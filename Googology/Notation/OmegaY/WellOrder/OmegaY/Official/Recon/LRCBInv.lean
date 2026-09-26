/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/LRCBInv.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.LRCBSF

set_option backward.do.legacy false

/-!
# The boundary column has nodes in the targets of the gap copies of `X`

`qb_tree`: in the tree of `X = x + w·(i+1)`, every plain item with a cut bottom and every item
copying a root row with offset `0` has, in its target region, a node of the lower part of the
boundary column `B = c_r + w·(i+1)` (the copy of `x₀` in block `i`).

The children of a lifting item lie in slots at most `h_ρ + Δ`, and `B` reaches that slot there
(`bnd_lift`, `sf_tree`); the children of a cut-bottom item or of a copy item lie in slots at
most the top of `B` in the target region (`sf_tree`).
-/

namespace OmegaY.Official.Recon.LRC

open Canonical Expansion Dimension RowLaw JumpLaw JumpLawLower
open Classification Classification.Proofs.ChainCorr Reserve

/-- The property of the items. -/
def QB (R : Mountain) (Bc : Nat) (vsB : List (List Emit)) (d : Nat) (K : Item) : Prop :=
  (K.clean = none ∧ K.cutBottom = true) ∨ (K.clean ≠ none ∧ K.offset = 0) →
    ∃ em ∈ vsB.flatten, inRegion d K.target em.row = true

section
variable {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref} {i x : Nat}

/-- A node of `B` in a region below `τ` is a node of its lower part. -/
theorem bnd_lower (hNCb : NewColumn s n R M t root i (M.size - 1)) {vsB : List (List Emit)}
    (hvsB : LowerRun (colCtx M R root i (M.size - 1)) (official t.row) vsB) {d : Nat} {T : Row}
    (hbelow : ∀ r, inRegion d T r = true → r < official t.row) {q : Ref × Cell}
    (hq : topIn R (root.column + (M.size - 1 - root.column) * (i + 1)) d T = some q) :
    ∃ em ∈ vsB.flatten, em.row = official q.2.row ∧ inRegion d T em.row = true := by
  obtain ⟨vsB', usB, _, hvsB', husB, _, hrowsB⟩ := hNCb.emits
  have hvv : vsB' = vsB := Except.ok.inj (hvsB'.symm.trans hvsB)
  subst hvv
  obtain ⟨hqm, hqreg, _⟩ := RowLaw.topIn_spec hq
  have e : root.column + (M.size - 1 - root.column) * (i + 1) =
      M.size - 1 + (M.size - 1 - root.column) * i := by
    have := hNCb.top.lt
    rw [Nat.mul_succ]; omega
  have hqR : official q.2.row ∈ rowsOf R (M.size - 1 + (M.size - 1 - root.column) * i) := by
    rw [← e]; exact List.mem_map.mpr ⟨q, hqm, rfl⟩
  rw [hrowsB] at hqR
  obtain ⟨emq, hemq, hemqr⟩ := List.mem_map.mp hqR
  rcases List.mem_append.mp hemq with hl | hu
  · exact ⟨emq, hl, hemqr, by rw [hemqr]; exact hqreg⟩
  · exfalso
    obtain ⟨hU1, _⟩ := upper_facts husB
    obtain ⟨_, _, _, hτ, _⟩ := hU1 emq hu
    rw [hemqr] at hτ
    exact absurd (lt_of_le_of_lt hτ (hbelow _ hqreg)) (lt_irrefl _)

end

section
variable {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref} {i x : Nat}

/-- **A slot below the top of `B` in the target of an item of `X` holds a node of `B`.** -/
theorem slot_of_top (hNCx : NewColumn s n R M t root (i + 1) x)
    (hNCb : NewColumn s n R M t root i (M.size - 1)) {vsB : List (List Emit)}
    (hvsB : LowerRun (colCtx M R root i (M.size - 1)) (official t.row) vsB)
    {F : Nat × Item} (hF : F ∈ lowerItems (official t.row)) {d : Nat} {A : Item}
    (hD : Desc (colCtx M R root (i + 1) x) F.1 F.2 (d + 2) A) {q : Ref × Cell}
    (hq : topIn R (root.column + (M.size - 1 - root.column) * (i + 1)) (d + 2) A.target = some q)
    {j : Nat} (hj : j ≤ (official q.2.row).coeff d) :
    ∃ em ∈ vsB.flatten, inRegion (d + 1) (slot (d + 2) A.target j) em.row = true := by
  have rX := hNCx.runCtx
  have hAt : InTree (colCtx M R root (i + 1) x) (official t.row) (d + 2) A := ⟨F, hF, hD⟩
  obtain ⟨_, hAOK⟩ := LowerLeftProof.inTree_itemOK rX hAt
  obtain ⟨hFOK, hFst, hF1, _⟩ := lower_itemOK (ctx := colCtx M R root (i + 1) x) hF
  obtain ⟨_, hlev, _, htgt, _⟩ := desc_facts rX hD hF1 hFOK
  have hbelow : ∀ r, inRegion (d + 2) A.target r = true → r < official t.row := by
    intro r hr
    have := htgt r hr
    rw [← hFst] at this
    exact hFOK.below r this
  obtain ⟨em, hem, hemr, hemreg⟩ := bnd_lower hNCb hvsB hbelow hq
  have hemF : inRegion F.1 F.2.source em.row = true := by rw [hFst]; exact htgt _ hemreg
  exact sf_tree hNCb.runCtx hvsB hF (by omega) (by simpa using hAOK.target) hem hemF hemreg
    (by rw [hemr]; exact hj)

end

section
variable {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref} {i x : Nat}

/-- A lower node of `B` in a region makes a top of `B` there. -/
theorem top_of_lower (hNCb : NewColumn s n R M t root i (M.size - 1)) {vsB : List (List Emit)}
    (hvsB : LowerRun (colCtx M R root i (M.size - 1)) (official t.row) vsB) {d : Nat} {T : Row}
    {em : Emit} (hem : em ∈ vsB.flatten) (hin : inRegion d T em.row = true) :
    ∃ q, topIn R (root.column + (M.size - 1 - root.column) * (i + 1)) d T = some q := by
  obtain ⟨vsB', usB, _, hvsB', _, _, hrowsB⟩ := hNCb.emits
  have hvv : vsB' = vsB := Except.ok.inj (hvsB'.symm.trans hvsB)
  subst hvv
  have e : root.column + (M.size - 1 - root.column) * (i + 1) =
      M.size - 1 + (M.size - 1 - root.column) * i := by
    have := hNCb.top.lt
    rw [Nat.mul_succ]; omega
  have hR : em.row ∈ rowsOf R (root.column + (M.size - 1 - root.column) * (i + 1)) := by
    rw [e, hrowsB]; exact List.mem_map.mpr ⟨em, List.mem_append_left _ hem, rfl⟩
  obtain ⟨p, hp, hpr⟩ := List.mem_map.mp hR
  cases hq : topIn R (root.column + (M.size - 1 - root.column) * (i + 1)) d T with
  | none =>
    have := RowLaw.topIn_none hq p hp
    rw [hpr, hin] at this; cases this
  | some q => exact ⟨q, rfl⟩

theorem c4_offset {d : Nat} {S T : Row} {hR hB off : Nat} {cb : Bool} {C : Row} {j : Nat}
    (h : (c4 d S T hR hB off cb C j).clean ≠ none) :
    (c4 d S T hR hB off cb C j).offset = ((j : Int) - hB + off).toNat := by
  unfold c4 at h ⊢
  split_ifs at h ⊢ <;> first | rfl | simp at h

/-- **One step of the invariant.** -/
theorem qb_step (hNCx : NewColumn s n R M t root (i + 1) x)
    (hNCb : NewColumn s n R M t root i (M.size - 1)) {vsB : List (List Emit)}
    (hvsB : LowerRun (colCtx M R root i (M.size - 1)) (official t.row) vsB)
    {F : Nat × Item} (hF : F ∈ lowerItems (official t.row)) {d : Nat} {A : Item}
    (hD : Desc (colCtx M R root (i + 1) x) F.1 F.2 (d + 2) A)
    (hA : QB R (root.column + (M.size - 1 - root.column) * (i + 1)) vsB (d + 2) A)
    {cs : List Item} (hcs : childItems (colCtx M R root (i + 1) x) (d + 2) A = .ok cs)
    {j : Nat} (hj : j < cs.length) :
    QB R (root.column + (M.size - 1 - root.column) * (i + 1)) vsB (d + 1) cs[j] := by
  intro hkind
  have hAt : InTree (colCtx M R root (i + 1) x) (official t.row) (d + 2) A := ⟨F, hF, hD⟩
  have hbnd := colCtx_bnd hNCx
  obtain ⟨ax, hax⟩ : ∃ ax, topIn M x (d + 2) A.source = some ax := by
    cases h : topIn M x (d + 2) A.source with
    | none =>
      have := childItems_none hcs h
      rw [this] at hj; simp at hj
    | some ax => exact ⟨ax, rfl⟩
  have hax' : topIn (colCtx M R root (i + 1) x).source (colCtx M R root (i + 1) x).x (d + 2)
      A.source = some ax := hax
  have hblk : (colCtx M R root (i + 1) x).block ≠ 0 := by show i + 1 ≠ 0; omega
  have hee := e_val' d
  -- the target of the child is the slot `j`
  have hsl : ∀ q, topIn R (root.column + (M.size - 1 - root.column) * (i + 1)) (d + 2) A.target =
      some q → j ≤ (official q.2.row).coeff d → cs[j].target = slot (d + 2) A.target j →
      ∃ em ∈ vsB.flatten, inRegion (d + 1) cs[j].target em.row = true := by
    intro q hq hjq htg
    rw [htg]
    exact slot_of_top hNCx hNCb hvsB hF hD hq hjq
  obtain ⟨b, hb⟩ := childItems_asc hcs hax'
  cases b with
  | false =>
    obtain ⟨_, _, _, hg⟩ := kids1 hcs hax' hb
    rw [hg j hj] at hkind
    simp [k1] at hkind
  | true =>
    cases hρ : topIn M root.column (d + 2) A.source with
    | none =>
      have : topIn (colCtx M R root (i + 1) x).source (colCtx M R root (i + 1) x).rootColumn
        (d + 2) A.source = none := hρ
      rw [this] at hb; cases hb
    | some ρ =>
      obtain ⟨r, cl⟩ := ρ
      have hρ' : topIn (colCtx M R root (i + 1) x).source (colCtx M R root (i + 1) x).rootColumn
        (d + 2) A.source = some (r, cl) := hρ
      rw [hρ'] at hb
      cases hcl : A.clean with
      | none =>
        cases hcb : A.cutBottom with
        | false =>
          obtain ⟨_, hg⟩ := kids2 hcs hcl hcb hax' hρ' hb
          obtain ⟨_, hMD, q, hq, hqc⟩ := bnd_lift hNCx hNCb hAt hcl hcb hax hρ hb
          have hHR : height (d + 2) (official cl.row) = (official cl.row).coeff d := rfl
          have hlift : (((heightOf (d + 2) (topIn (colCtx M R root (i + 1) x).source
              (colCtx M R root (i + 1) x).lastColumn (d + 2) A.source) : Nat) : Int) -
              ((height (d + 2) (official cl.row) : Nat) : Int)) *
                ((colCtx M R root (i + 1) x).block : Int) =
              (((heightOf (d + 2) (topIn M (M.size - 1) (d + 2) A.source) -
                height (d + 2) (official cl.row)) * (i + 1) : Nat) : Int) := by
            have hb1 : ((colCtx M R root (i + 1) x).block : Int) = ((i + 1 : Nat) : Int) := rfl
            rw [hb1]
            have e2 : heightOf (d + 2) (topIn (colCtx M R root (i + 1) x).source
              (colCtx M R root (i + 1) x).lastColumn (d + 2) A.source) =
              heightOf (d + 2) (topIn M (M.size - 1) (d + 2) A.source) := rfl
            rw [e2]
            push_cast
            rw [Nat.cast_sub hMD.le]
          have hcj := hg j hj
          have hsl' := hsl q hq
          rw [hqc] at hsl'
          have hMD' : height (d + 2) (official cl.row) <
              heightOf (d + 2) (topIn M (M.size - 1) (d + 2) A.source) := hMD
          generalize hK : heightOf (d + 2) (topIn M (M.size - 1) (d + 2) A.source) = K at hMD' hlift hsl'
          generalize hH : height (d + 2) (official cl.row) = H at hMD' hlift hsl' hcj
          rw [hlift] at hcj
          rw [Nat.mul_succ] at hcj
          generalize hP : (K - H) * i = P at hsl' hcj
          rcases c2_cases (d := d + 2) (S := A.source) (T := A.target)
            (i := (colCtx M R root (i + 1) x).block) (hR := H)
            (lift := (((P + (K - H) : Nat)) : Int)) (C := official cl.row) j with
            ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
          · rw [hcj, h2] at hkind; simp [k1] at hkind
          · refine hsl' ?_ (by rw [hcj]; exact c2_target _ _ _ _ _ _ _ _)
            rcases hee with ⟨he1, _⟩ | ⟨he1, _⟩ <;> rw [he1] at h2 <;> push_cast at h2 <;> omega
          · obtain ⟨_, hc3, hcb3⟩ := h3
            rw [hcj, hc3, hcb3] at hkind
            have hq' : (j : Int) = H + ((P + (K - H) : Nat) : Int) := by
              rcases hkind with ⟨_, h⟩ | ⟨h, _⟩
              · simp at h; exact h.2
              · exact absurd rfl h
            refine hsl' ?_ (by rw [hcj]; exact c2_target _ _ _ _ _ _ _ _)
            push_cast at hq'
            omega
        | true =>
          obtain ⟨_, hg⟩ := kids3 hcs hcl hcb hblk hax' hρ' hb
          have hcj := hg j hj
          obtain ⟨em, hem, hemin⟩ := hA (Or.inl ⟨hcl, hcb⟩)
          obtain ⟨q, hq⟩ := top_of_lower hNCb hvsB hem hemin
          have hhB : heightOf (d + 2) (topIn (colCtx M R root (i + 1) x).result
              (colCtx M R root (i + 1) x).boundary (d + 2) A.target) = (official q.2.row).coeff d := by
            rw [hbnd, hq]; rfl
          rw [hhB] at hcj
          have htg : cs[j].target = slot (d + 2) A.target j := by
            rw [hcj]; unfold c3; split_ifs <;> simp
          rcases c3_cases (d := d + 2) (S := A.source) (T := A.target)
            (hR := height (d + 2) (official cl.row)) (hB := (official q.2.row).coeff d)
            (C := official cl.row) (j + height (d + 2) (official cl.row)) with ⟨h1, _⟩ | ⟨h1, h2⟩
          · refine hsl q hq ?_ htg
            rcases hee with ⟨he1, _⟩ | ⟨he1, _⟩ <;> rw [he1] at h1 <;> push_cast at h1 <;> omega
          · rw [hcj, h2] at hkind
            rcases hkind with ⟨_, h⟩ | ⟨h, _⟩
            · simp at h
              exact hsl q hq (by omega) htg
            · exact absurd rfl h
      | some C =>
        obtain ⟨xr, xc, g, hxn, hxg, hxb, hlX, hgX⟩ := kids4 hcs hcl hblk hax' hρ' hb
        have hcj := hgX j hj
        have htg : cs[j].target = slot (d + 2) A.target j := by rw [hcj]; exact c4_target _ _ _ _ _ _ _ _ _
        rcases hkind with ⟨h1, h2⟩ | ⟨hcln, hoff⟩
        · -- a plain child of a copy has no cut bottom
          rw [hcj] at h1 h2
          exfalso
          unfold c4 at h1 h2
          split_ifs at h1 h2 <;> simp_all
        · have hoff' := c4_offset (by rw [← hcj]; exact hcln)
          rw [← hcj, hoff] at hoff'
          by_cases hB0 : heightOf (d + 2) (topIn (colCtx M R root (i + 1) x).result
              (colCtx M R root (i + 1) x).boundary (d + 2) A.target) = 0
          · have hj0 : j = 0 := by rw [hB0] at hoff'; omega
            have hA0 : A.offset = 0 := by rw [hB0] at hoff'; omega
            obtain ⟨em, hem, hemin⟩ := hA (Or.inr ⟨by rw [hcl]; simp, hA0⟩)
            obtain ⟨q, hq⟩ := top_of_lower hNCb hvsB hem hemin
            exact hsl q hq (by omega) htg
          · cases hq : topIn R (root.column + (M.size - 1 - root.column) * (i + 1)) (d + 2) A.target with
            | none =>
              exfalso; apply hB0
              rw [hbnd, hq]; rfl
            | some q =>
              refine hsl q hq ?_ htg
              have : heightOf (d + 2) (topIn (colCtx M R root (i + 1) x).result
                (colCtx M R root (i + 1) x).boundary (d + 2) A.target) =
                  (official q.2.row).coeff d := by rw [hbnd, hq]; rfl
              rw [this] at hoff'
              omega

end

section
variable {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref} {i x : Nat}

theorem desc_pos {ctx : Context} {d : Nat} {A : Item} {d' : Nat} {B : Item}
    (hD : Desc ctx d A d' B) (hd : 1 ≤ d) : 1 ≤ d' := by
  induction hD with
  | refl => exact hd
  | step _ _ _ ih => exact ih (by omega)

/-- **The invariant along the tree of `X`.** -/
theorem qb_tree (hNCx : NewColumn s n R M t root (i + 1) x)
    (hNCb : NewColumn s n R M t root i (M.size - 1)) {vsB : List (List Emit)}
    (hvsB : LowerRun (colCtx M R root i (M.size - 1)) (official t.row) vsB)
    {F : Nat × Item} (hF : F ∈ lowerItems (official t.row)) :
    ∀ m d A, d + m = F.1 → Desc (colCtx M R root (i + 1) x) F.1 F.2 d A →
      QB R (root.column + (M.size - 1 - root.column) * (i + 1)) vsB d A := by
  intro m
  induction m with
  | zero =>
    intro d A hd hD
    subst hd
    have := desc_eq hD
    subst this
    intro hk
    obtain ⟨k, j, _, _, hkj⟩ := mem_lowerItems hF
    rw [hkj] at hk
    simp at hk
  | succ m ih =>
    intro d A hd hD
    obtain ⟨K, cs, hDK, hcs, hAm⟩ := desc_parent hD (by omega)
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hAm
    have hF1 : 1 ≤ F.1 := (lower_itemOK (ctx := colCtx M R root (i + 1) x) hF).2.2.1
    have hd1 := desc_pos hD hF1
    obtain ⟨d'', rfl⟩ : ∃ d'', d = d'' + 1 := ⟨d - 1, by omega⟩
    exact qb_step hNCx hNCb hvsB hF hDK (ih (d'' + 2) K (by omega) hDK) hcs hj

end

end OmegaY.Official.Recon.LRC
