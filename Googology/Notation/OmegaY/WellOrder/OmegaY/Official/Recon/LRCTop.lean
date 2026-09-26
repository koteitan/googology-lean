/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/LRCTop.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.LRCX

set_option backward.do.legacy false

/-!
# The top child of a copy of a root row emits at most one node

Fix a root row `C` copied by the column `x` with `g ≥ 1` generations. Along the tree, an item
copying `C` has offset `< g`, or offset `g` and no node of the boundary column in its target
region (`off_inv`). An item copying `C` with offset `g` and no boundary node in its target emits
at most one node (`single`). So the last child of an item copying `C` emits at most one node
(`top_single`).
-/

namespace OmegaY.Official.Recon.LRC

open Canonical Expansion Dimension RowLaw JumpLaw JumpLawLower
open Classification Classification.Proofs.ChainCorr Reserve

section
variable {ctx : Context} {Rm : Mountain} {Bc : Nat}

/-- The invariant of the offsets. -/
def OffInv (ctx : Context) (C : Row) (g : Nat) (d : Nat) (K : Item) : Prop :=
  K.clean = some C → K.offset < g ∨ (K.offset = g ∧ topIn ctx.result ctx.boundary d K.target = none)

theorem gen_unique {ctx : Context} {C : Row} {csRef csRef' : Ref} {cs cs' : Cell} {g g' : Nat}
    (hn : nodeAt ctx.source ctx.x C = some (csRef, cs))
    (hn' : nodeAt ctx.source ctx.x C = some (csRef', cs'))
    (hg : generations ctx.source ctx.rootColumn C (ctx.x + 1) csRef cs 0 = .ok g)
    (hg' : generations ctx.source ctx.rootColumn C (ctx.x + 1) csRef' cs' 0 = .ok g') : g = g' := by
  rw [hn] at hn'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hn')
  rw [hg] at hg'
  exact Except.ok.inj hg'

/-- A slot above the boundary top, or inside a region without boundary node, has no boundary
node. -/
theorem bfree_slot (hVR : MountainValid Rm) {d : Nat} {T : Row} {j : Nat}
    (h : j > heightOf (d + 2) (topIn Rm Bc (d + 2) T) ∨ topIn Rm Bc (d + 2) T = none) :
    topIn Rm Bc (d + 1) (slot (d + 2) T j) = none := by
  cases hq : topIn Rm Bc (d + 2) T with
  | none => exact Proofs.CopyShape.MHProof.topIn_slot_none hq
  | some q =>
    obtain ⟨qr, qc⟩ := q
    rw [hq] at h
    rcases h with h | h
    · exact Proofs.CopyShape.MHProof.topIn_slot_above hVR hq h
    · cases h

/-- **One step of the offset invariant.** -/
theorem off_step (hblk : ctx.block ≠ 0) (hVR : MountainValid Rm)
    (hbnd : ∀ d T, topIn ctx.result ctx.boundary d T = topIn Rm Bc d T)
    {C : Row} {g : Nat} (hg1 : 1 ≤ g) {csRef0 : Ref} {cs0 : Cell}
    (hn0 : nodeAt ctx.source ctx.x C = some (csRef0, cs0))
    (hg0 : generations ctx.source ctx.rootColumn C (ctx.x + 1) csRef0 cs0 0 = .ok g)
    {d : Nat} {A : Item} (hA : OffInv ctx C g (d + 2) A) {cs : List Item}
    (hcs : childItems ctx (d + 2) A = .ok cs) : ∀ c ∈ cs, OffInv ctx C g (d + 1) c := by
  intro c hc hcC
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc
  cases hax : topIn ctx.source ctx.x (d + 2) A.source with
  | none =>
    have := childItems_none hcs hax
    subst this; simp at hj
  | some ax =>
    obtain ⟨b, hb⟩ := childItems_asc hcs hax
    cases b with
    | false =>
      obtain ⟨_, _, _, hg⟩ := kids1 hcs hax hb
      rw [hg j hj] at hcC; cases hcC
    | true =>
      cases hρ : topIn ctx.source ctx.rootColumn (d + 2) A.source with
      | none => rw [hρ] at hb; cases hb
      | some ρ =>
        obtain ⟨r, cl⟩ := ρ
        rw [hρ] at hb
        cases hAcl : A.clean with
        | none =>
          cases hAcb : A.cutBottom with
          | false =>
            obtain ⟨_, hg⟩ := kids2 hcs hAcl hAcb hax hρ hb
            left
            rw [hg j hj] at hcC ⊢
            rcases c2_cases (d := d + 2) (S := A.source) (T := A.target) (i := ctx.block)
              (hR := height (d + 2) (official cl.row))
              (lift := (((heightOf (d + 2) (topIn ctx.source ctx.lastColumn (d + 2) A.source) :
                Nat) : Int) - ((height (d + 2) (official cl.row) : Nat) : Int)) * (ctx.block : Int))
              (C := official cl.row) j with ⟨_, h2⟩ | ⟨_, _, h3⟩ | ⟨_, _, h3⟩
            · rw [h2] at hcC; cases hcC
            · rw [h3]; show 0 < g; omega
            · rw [h3.2.1] at hcC; cases hcC
          | true =>
            obtain ⟨_, hg⟩ := kids3 hcs hAcl hAcb hblk hax hρ hb
            left
            rw [hg j hj] at hcC ⊢
            rcases c3_cases (d := d + 2) (S := A.source) (T := A.target)
              (hR := height (d + 2) (official cl.row))
              (hB := heightOf (d + 2) (topIn ctx.result ctx.boundary (d + 2) A.target))
              (C := official cl.row) (j + height (d + 2) (official cl.row)) with ⟨_, h2⟩ | ⟨_, h2⟩
            · rw [h2]; show 0 < g; omega
            · rw [h2] at hcC; cases hcC
        | some CA =>
          obtain ⟨xr, xc, gA, hxn, hxg, _, hl, hg⟩ := kids4 hcs hAcl hblk hax hρ hb
          have hCA : CA = C := by
            rw [hg j hj] at hcC
            unfold c4 at hcC
            split_ifs at hcC <;> simp at hcC <;> exact hcC
          subst hCA
          have hgg := gen_unique hxn hn0 hxg hg0
          subst hgg
          have hlo : height (d + 2) (official cl.row) ≤ j ∨ A.cutBottom = true := by
            have hcC' := hcC
            rw [hg j hj] at hcC'
            exact c4_clean_lo (by rw [hcC']; simp)
          have hoff : (cs[j]).offset = ((j : Int) -
              heightOf (d + 2) (topIn ctx.result ctx.boundary (d + 2) A.target) + A.offset).toNat := by
            rw [hg j hj]; unfold c4
            rcases hlo with hlo | hlo
            · split_ifs <;> first | rfl | omega
            · simp [hlo]
          have hjl : (j : Int) ≤ heightOf (d + 2) (topIn ctx.result ctx.boundary (d + 2) A.target) +
              gA - A.offset := by
            rw [hl] at hj; omega
          rw [hoff]
          have htg : (cs[j]).target = slot (d + 2) A.target j := by
            rw [hg j hj]; unfold c4; split_ifs <;> rfl
          by_cases hlt : ((j : Int) - heightOf (d + 2) (topIn ctx.result ctx.boundary (d + 2)
              A.target) + A.offset).toNat < gA
          · exact Or.inl hlt
          · right
            refine ⟨by omega, ?_⟩
            rw [htg, hbnd]
            apply bfree_slot hVR
            rcases hA hAcl with ho | ⟨ho, hfree⟩
            · left
              rw [← hbnd]; omega
            · right
              rw [← hbnd]; exact hfree

end

section
variable {ctx : Context} {Rm : Mountain} {Bc : Nat}

theorem off_desc (hblk : ctx.block ≠ 0) (hVR : MountainValid Rm)
    (hbnd : ∀ d T, topIn ctx.result ctx.boundary d T = topIn Rm Bc d T)
    {C : Row} {g : Nat} (hg1 : 1 ≤ g) {csRef0 : Ref} {cs0 : Cell}
    (hn0 : nodeAt ctx.source ctx.x C = some (csRef0, cs0))
    (hg0 : generations ctx.source ctx.rootColumn C (ctx.x + 1) csRef0 cs0 0 = .ok g)
    {d : Nat} {A : Item} {d' : Nat} {B : Item} (hD : Desc ctx d A d' B) :
    OffInv ctx C g d A → OffInv ctx C g d' B := by
  induction hD with
  | refl => exact id
  | @step d A cs c d' B hcs hc _ ih =>
    intro hA
    exact ih (off_step hblk hVR hbnd hg1 hn0 hg0 hA hcs c hc)

theorem off_tree (hblk : ctx.block ≠ 0) (hVR : MountainValid Rm)
    (hbnd : ∀ d T, topIn ctx.result ctx.boundary d T = topIn Rm Bc d T)
    {C : Row} {g : Nat} (hg1 : 1 ≤ g) {csRef0 : Ref} {cs0 : Cell}
    (hn0 : nodeAt ctx.source ctx.x C = some (csRef0, cs0))
    (hg0 : generations ctx.source ctx.rootColumn C (ctx.x + 1) csRef0 cs0 0 = .ok g)
    {τ : Row} {d : Nat} {K : Item} (hK : InTree ctx τ d K) : OffInv ctx C g d K := by
  obtain ⟨F, hF, hD⟩ := hK
  apply off_desc hblk hVR hbnd hg1 hn0 hg0 hD
  intro hcl
  rw [Inner.lowerItems_clean τ F hF] at hcl
  cases hcl

theorem levelOne_len (ctx : Context) (it : Item) {L : List Emit} (h : levelOne ctx it = .ok L) :
    L.length ≤ 1 := by
  unfold levelOne at h
  split at h
  · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; simp
  · split at h
    · split at h
      · cases h
      · obtain ⟨v, _, h⟩ := Reconstruction.bind_ok h
        simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; simp
    · split at h
      · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; simp
      · obtain ⟨v, _, h⟩ := Reconstruction.bind_ok h
        simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; simp

set_option maxHeartbeats 800000 in
/-- **An item copying `C` with offset `g` and no boundary node in its target emits at most one
node.** -/
theorem single (hblk : ctx.block ≠ 0) (hVR : MountainValid Rm)
    (hbnd : ∀ d T, topIn ctx.result ctx.boundary d T = topIn Rm Bc d T)
    {C : Row} {g : Nat} (hg1 : 1 ≤ g) {csRef0 : Ref} {cs0 : Cell}
    (hn0 : nodeAt ctx.source ctx.x C = some (csRef0, cs0))
    (hg0 : generations ctx.source ctx.rootColumn C (ctx.x + 1) csRef0 cs0 0 = .ok g) :
    ∀ d (K : Item) (L : List Emit), runItem ctx d K = .ok L → K.clean = some C → K.offset = g →
      topIn ctx.result ctx.boundary d K.target = none → L.length ≤ 1 := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro K L h hcl hoff hfree
  match d, ih, h, hfree with
  | 0, _, h, _ =>
    simp [runItem, pure, Except.pure] at h; subst h; simp
  | 1, _, h, _ => exact levelOne_len ctx K (by simpa [runItem] using h)
  | d + 2, ih, h, hfree =>
    obtain ⟨cs, outs, hcs, hF, rfl⟩ := runItem_children h
    obtain ⟨hlen, hget⟩ := forall₂_getElem hF
    cases hax : topIn ctx.source ctx.x (d + 2) K.source with
    | none =>
      have := childItems_none hcs hax
      subst this
      have : outs = [] := by
        cases outs with
        | nil => rfl
        | cons _ _ => simp at hlen
      subst this; simp
    | some ax =>
      have hb := asc_true_of_kind hcs hax (Or.inl (by rw [hcl]; simp))
      cases hρ : topIn ctx.source ctx.rootColumn (d + 2) K.source with
      | none => rw [hρ] at hb; cases hb
      | some ρ =>
        obtain ⟨r, cl⟩ := ρ
        rw [hρ] at hb
        obtain ⟨xr, xc, gK, hxn, hxg, hcbK, hl, hg⟩ := kids4 hcs hcl hblk hax hρ hb
        have hgg := gen_unique hxn hn0 hxg hg0
        subst hgg
        have hcbt : K.cutBottom = true := by
          cases hc : K.cutBottom with
          | true => rfl
          | false => have := (hcbK hc).2; omega
        have hB0 : heightOf (d + 2) (topIn ctx.result ctx.boundary (d + 2) K.target) = 0 := by
          rw [hfree]; rfl
        rw [hB0, hoff] at hl
        have hl1 : cs.length = 1 := by rw [hl]; omega
        have hout1 : outs.length = 1 := by omega
        have h0 : 0 < cs.length := by omega
        have hc0 := hg 0 h0
        rw [hcbt, hB0, hoff] at hc0
        have hrun0 := hget 0 h0 (by omega)
        have hIH := ih (d + 1) (by omega) cs[0] outs[0] hrun0
          (by rw [hc0]; unfold c4; simp) (by rw [hc0]; unfold c4; simp)
          (by
            rw [hc0]; unfold c4; simp only [if_true]
            rw [hbnd]; apply bfree_slot hVR; right; rw [← hbnd]; exact hfree)
        obtain ⟨o, rfl⟩ := List.length_eq_one_iff.mp hout1
        simpa using hIH

/-- **The last child of an item copying `C` emits at most one node.** -/
theorem top_single (hblk : ctx.block ≠ 0) (hVR : MountainValid Rm)
    (hbnd : ∀ d T, topIn ctx.result ctx.boundary d T = topIn Rm Bc d T)
    {C : Row} {g : Nat} (hg1 : 1 ≤ g) {csRef0 : Ref} {cs0 : Cell}
    (hn0 : nodeAt ctx.source ctx.x C = some (csRef0, cs0))
    (hg0 : generations ctx.source ctx.rootColumn C (ctx.x + 1) csRef0 cs0 0 = .ok g)
    {τ : Row} {d : Nat} {A : Item} (hA : InTree ctx τ (d + 2) A) (hcl : A.clean = some C)
    {cs : List Item} (hcs : childItems ctx (d + 2) A = .ok cs) {ax : Ref × Cell}
    (hax : topIn ctx.source ctx.x (d + 2) A.source = some ax)
    (hMH : A.cutBottom = false →
      heightOf (d + 2) (topIn ctx.source ctx.rootColumn (d + 2) A.source) ≤
        heightOf (d + 2) (topIn ctx.result ctx.boundary (d + 2) A.target) + g)
    {j : Nat} (hj : j + 1 = cs.length) {L : List Emit}
    (hL : runItem ctx (d + 1) (cs[j]'(by omega)) = .ok L) : L.length ≤ 1 := by
  have hj' : j < cs.length := by omega
  have hb := asc_true_of_kind hcs hax (Or.inl (by rw [hcl]; simp))
  cases hρ : topIn ctx.source ctx.rootColumn (d + 2) A.source with
  | none => rw [hρ] at hb; cases hb
  | some ρ =>
    obtain ⟨r, cl⟩ := ρ
    rw [hρ] at hb
    obtain ⟨xr, xc, gA, hxn, hxg, hcbA, hl, hg⟩ := kids4 hcs hcl hblk hax hρ hb
    have hgg := gen_unique hxn hn0 hxg hg0
    subst hgg
    have hc := hg j hj'
    have hcT : InTree ctx τ (d + 1) cs[j] := LowerLeftProof.inTree_snoc hA hcs (List.getElem_mem hj')
    have hinv := off_tree hblk hVR hbnd hg1 hn0 hg0 hcT
    -- the last child copies `C` with offset `g`
    have hlo : height (d + 2) (official cl.row) ≤ j ∨ A.cutBottom = true := by
      cases hcb : A.cutBottom with
      | true => exact Or.inr rfl
      | false =>
        left
        have h1 := hMH hcb
        rw [hρ] at h1
        have h2 := (hcbA hcb).2
        rw [hl, h2] at hj
        change height (d + 2) (official cl.row) ≤ _ at h1
        omega
    have hcC : cs[j].clean = some C := by
      rw [hc]; unfold c4
      rcases hlo with hlo | hlo
      · split_ifs <;> first | rfl | omega
      · simp [hlo]
    have hoff : cs[j].offset = gA := by
      rw [hc]; unfold c4
      rw [hl] at hj
      rcases hlo with hlo | hlo
      · split_ifs <;> first | (simp; omega) | omega
      · simp [hlo]; omega
    rcases hinv hcC with h | ⟨_, hfree⟩
    · omega
    · exact single hblk hVR hbnd hg1 hn0 hg0 (d + 1) cs[j] L hL hcC hoff hfree

end

end OmegaY.Official.Recon.LRC
