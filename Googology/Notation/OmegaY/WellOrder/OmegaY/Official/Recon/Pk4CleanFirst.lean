/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/Pk4CleanFirst.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.CrossPlainPosColumn

set_option backward.do.legacy false
/-
(Package 4 copy.) This file is a copy of the untracked file `CrossPlainPosCleanFirst.lean` of an
earlier agent, in the namespace `CrossPlainPos.Pk4CF`, so that the package-4 results do not
depend on an untracked file that another agent may change. The proof is unchanged.
-/

/-!
# `CleanFirst`: a copy of the root row without the cut flag is the first emit of its origin

`CleanFirst` (`CrossPlainPosColumn.lean`) is one of the open statements of the reduction of
`CrossLexPos IsClean`. This file proves it, for every column of every splice run
(`emitsT_first`, for any context; `cleanFirst_holds`), by an induction over the items
(notes/03 §2.3, §2.4) next to `ChainCorr.Inner.runItemT_order`.

For the list `ps` of emits of an item `it` of level `d` the induction carries

* `FirstClean ps`: no emit of `ps` before an emit `.clean r false` has the source `r`;
* `CutInv`: (B) if `it` copies a root row and has the cut flag, every emit of `ps` is
  `.clean _ true`; (C) if `it` copies no root row, has the cut flag and `d ≥ 2`, and `ρ` is the
  top of the root column in the region of `it`, no emit `.clean r' false` of `ps` has the row of
  `ρ`.

The step: the children of an item are pairwise separated (`ChildSep`, from
`childItems_order`) in one of three ways, and in each the later child has no `.clean r false`
emit whose source is a source of the earlier child (`sep_first`):

* by slots: the rows of the two children differ;
* the later child copies the same root row with the cut flag: all its emits are cut (B);
* the later child is a cut item without a root row above the root row `C` of the earlier one:
  its emits are at or above `C` (`EmitOK`), those at `C` are not `.clean _ false` (C), and the
  emits of the earlier one are at or below `C`.

(B) and (C) pass from the children to the item by the shape of the children
(`childItems_cut`): a cut copy of a root row has only cut copies of the same root row as
children (case 4), and a cut item without a root row (case 3) has cut copies of the root row,
items above the slot of `ρ`, and (for `d ≥ 1`) one cut item without a root row in the slot of
`ρ`, whose region has the same top `ρ` of the root column (`topIn_slot`).
-/

namespace OmegaY.Official.Recon.CrossPlainPos.Pk4CF

open Canonical Reserve Official Classification
open OmegaY.Official.Classification.Proofs.ChainCorr.Inner (EmitOK ItemInvC ChildSep
  runItemT_order childItems_order slot_rows_lt topIn_slot emitOK_lower lowerItems_sep
  lowerItems_clean)

/-- No emit before an emit `.clean r false` has the source `r`. -/
def FirstClean (l : List (Emit × Origin)) : Prop :=
  ∀ a b (ha : a < l.length) (hb : b < l.length), a < b → ∀ r, l[b].2 = .clean r false →
    l[a].2.src ≠ r

/-- The cut invariants of the emits `ps` of an item `it` of level `d`. -/
def CutInv (M : Mountain) (cr d : Nat) (it : Item) (ps : List (Emit × Origin)) : Prop :=
  (∀ C, it.clean = some C → it.cutBottom = true → ∀ p ∈ ps, ∃ r, p.2 = .clean r true) ∧
  (it.clean = none → it.cutBottom = true → 2 ≤ d → ∀ r ρc, topIn M cr d it.source = some (r, ρc) →
    ∀ p ∈ ps, ∀ r', p.2 = .clean r' false → ∀ c, cell? M r' = some c →
      official c.row ≠ official ρc.row)

/-! ## The shape of the children of a cut item -/

/-- **The children of a cut item.** -/
theorem childItems_cut {ctx : Context} {d : Nat} {it : Item} {cs : List Item}
    (h : childItems ctx (d + 2) it = .ok cs) :
    (∀ C, it.clean = some C → it.cutBottom = true → ∀ c ∈ cs,
      c.clean = some C ∧ c.cutBottom = true) ∧
    (it.clean = none → it.cutBottom = true → ∀ r ρc,
      topIn ctx.source ctx.rootColumn (d + 2) it.source = some (r, ρc) → ∀ c ∈ cs,
        (∃ C, c.clean = some C ∧ c.cutBottom = true) ∨
        (∃ j, c.source = slot (d + 2) it.source j ∧ (official ρc.row).coeff d < j) ∨
        (c.clean = none ∧ c.cutBottom = true ∧ 1 ≤ d ∧
          c.source = slot (d + 2) it.source ((official ρc.row).coeff d))) := by
  unfold childItems at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  generalize hrho : topIn ctx.source ctx.rootColumn (d + 2) it.source = rho at h
  split at h
  · obtain rfl := Except.ok.inj h
    simp
  · split at h
    · cases h
    · rename_i v hv
      split at h
      · -- case 1: no cut flag
        rename_i hnv
        split at h
        · simp [throw, throwThe, MonadExceptOf.throw] at h
        · rename_i hcond
          have hcb : it.cutBottom = false := by
            cases hb : it.cutBottom
            · rfl
            · exact absurd (Or.inr (Or.inr hb)) hcond
          refine ⟨?_, ?_⟩
          · intro _ _ hb
            rw [hcb] at hb
            cases hb
          · intro _ hb
            rw [hcb] at hb
            cases hb
      · rename_i hvt
        have hvt' : v = true := by simpa using hvt
        subst hvt'
        obtain ⟨ρr, ρc, rfl⟩ : ∃ a b, rho = some (a, b) := by
          cases rho with
          | none => simp [ascends, pure, Except.pure] at hv
          | some q => exact ⟨q.1, q.2, rfl⟩
        have hhR : heightOf (d + 2) (some (ρr, ρc)) = (official ρc.row).coeff d := by
          simp [heightOf, Recon.RowLaw.height_eq]
        simp only at h
        generalize heightOf (d + 2) (some (ρr, ρc)) = hR at h hhR
        split at h
        · -- clean = none
          rename_i hcl
          split at h
          · -- case 2: no cut flag
            rename_i hcb'
            have hcb : it.cutBottom = false := by simpa using hcb'
            refine ⟨?_, ?_⟩
            · intro _ _ hb
              rw [hcb] at hb
              cases hb
            · intro _ hb
              rw [hcb] at hb
              cases hb
          · -- case 3
            rename_i hcb'
            have hcb : it.cutBottom = true := by simpa using hcb'
            have he : ((if d + 2 = 2 then (1 : Int) else 0) = 1 ∧ d = 0) ∨
                ((if d + 2 = 2 then (1 : Int) else 0) = 0 ∧ 1 ≤ d) := by
              by_cases hd : d = 0
              · left; simp [hd]
              · right; simp [hd]; omega
            generalize (if d + 2 = 2 then (1 : Int) else 0) = e at h he
            generalize heightOf (d + 2) (topIn ctx.result ctx.boundary (d + 2) it.target) = hB at h
            obtain rfl := Except.ok.inj h
            refine ⟨?_, ?_⟩
            · intro C hC
              rw [hcl] at hC
              cases hC
            intro _ _ r ρ hρ c hc
            injection hρ with hρ'
            injection hρ' with _ hρρ
            subst hρρ
            simp only [List.mem_map, List.mem_filter] at hc
            obtain ⟨j, ⟨_, hjR⟩, rfl⟩ := hc
            have hjR' : hR ≤ j := by simpa using hjR
            by_cases a1 : (j : Int) < (hB : Int) + hR + e
            · rw [if_pos a1]
              exact Or.inl ⟨_, rfl, rfl⟩
            · rw [if_neg a1]
              by_cases hs : hR < j - hB
              · exact Or.inr (Or.inl ⟨j - hB, rfl, by rw [← hhR]; exact hs⟩)
              · have hs' : j - hB = hR := by omega
                have he0 : e = 0 ∧ 1 ≤ d := by
                  rcases he with ⟨he1, hd0⟩ | ⟨he0, hd⟩
                  · exfalso; omega
                  · exact ⟨he0, hd⟩
                refine Or.inr (Or.inr ⟨rfl, by simp; omega, he0.2, ?_⟩)
                show slot (d + 2) it.source (j - hB) = _
                rw [hs', hhR]
        · -- case 4: a copy of the root row
          rename_i C hclC
          split at h
          · simp [throw, throwThe, MonadExceptOf.throw] at h
          · split at h
            · cases h
            · split at h
              · simp [throw, throwThe, MonadExceptOf.throw] at h
              · obtain rfl := Except.ok.inj h
                refine ⟨?_, ?_⟩
                swap
                · intro hn
                  rw [hclC] at hn
                  cases hn
                intro C' hC' hb c hc
                rw [hclC] at hC'
                obtain rfl := Option.some.inj hC'
                simp only [List.mem_map] at hc
                obtain ⟨j, _, rfl⟩ := hc
                rw [if_pos hb]
                exact ⟨rfl, rfl⟩

/-! ## Two separated children -/

/-- **Separated children.** If the child `a` comes before the child `b`, no emit of `a` has
the source of an emit `.clean r false` of `b`. -/
theorem sep_first {M : Mountain} {cr d : Nat} {S : Row} {a b : Item}
    (hs : ChildSep M cr d S a b) {p q : Emit × Origin} {qs : List (Emit × Origin)}
    (hp : EmitOK M cr (d + 1) a p) (hq : EmitOK M cr (d + 1) b q)
    (hb : CutInv M cr (d + 1) b qs) (hqm : q ∈ qs) {r : Ref} (hqr : q.2 = .clean r false) :
    p.2.src ≠ r := by
  intro heq
  have hqs : q.2.src = r := by rw [hqr]; rfl
  have hp' := hp
  obtain ⟨_, c, hc, hreg, _⟩ := hp'
  obtain ⟨_, c', hc', hreg', _, _, hq3⟩ := hq
  have hc0 := hc
  rw [heq] at hc
  rw [hqs] at hc'
  rw [hc] at hc'
  obtain rfl := Option.some.inj hc'
  rcases hs with ⟨j, j', hja, hjb, hjj⟩ | ⟨C, haC, hbC⟩
  · rw [hja] at hreg
    rw [hjb] at hreg'
    exact lt_irrefl _ (slot_rows_lt hreg hreg' hjj)
  · rcases hbC with ⟨hbC, hbb⟩ | ⟨hbn, hbb, hd, r0, ρc, hρ, hρC⟩
    · obtain ⟨r1, h1⟩ := hb.1 C hbC hbb q hqm
      rw [hqr] at h1
      injection h1 with _ h2
      cases h2
    · have hne := hb.2 hbn hbb (by omega) r0 ρc hρ q hqm r hqr c hc
      have hlo := emitOK_lower haC hc0 hp
      have hhi := (hq3 hbn hbb (by omega) r0 ρc hρ).1
      rw [hρC] at hne hhi
      exact hne (le_antisymm hlo.1 hhi)

/-! ## The induction over the items -/

theorem levelOneT_first {ctx : Context} {it : Item} {ps : List (Emit × Origin)}
    (h : levelOneT ctx it = .ok ps) :
    FirstClean ps ∧ CutInv ctx.source ctx.rootColumn 1 it ps := by
  have hlen : ps.length ≤ 1 ∧ (∀ C, it.clean = some C → it.cutBottom = true →
      ∀ p ∈ ps, ∃ r, p.2 = .clean r true) := by
    unfold levelOneT at h
    cases hsrc : nodeAt ctx.source ctx.x it.source with
    | none =>
      simp [hsrc, pure, Except.pure] at h
      subst h
      simp
    | some q =>
      simp only [hsrc] at h
      cases hC : it.clean with
      | some C =>
        simp only [hC] at h
        cases hcs : nodeAt ctx.source ctx.x C with
        | none => simp [hcs, throw, throwThe, MonadExceptOf.throw] at h
        | some q' =>
          simp only [hcs, bind, Except.bind, pure, Except.pure] at h
          split at h
          · cases h
          · cases h
            refine ⟨by simp, ?_⟩
            intro C' _ hb p hp
            simp only [List.mem_singleton] at hp
            subst hp
            exact ⟨_, by rw [hb]⟩
      | none =>
        simp only [hC] at h
        refine ⟨?_, fun C' hC' => by cases hC'⟩
        split at h
        · simp only [pure, Except.pure, Except.ok.injEq] at h
          subst h
          simp
        · simp only [bind, Except.bind, pure, Except.pure] at h
          split at h
          · cases h
          · cases h
            simp
  refine ⟨?_, hlen.2, fun _ _ h2 => absurd h2 (by decide)⟩
  intro a b ha hb hab
  omega

/-- **The induction over the items.** -/
theorem runItemT_first (ctx : Context) :
    ∀ (d : Nat) (it : Item) (ps : List (Emit × Origin)), runItemT ctx d it = .ok ps →
      ItemInvC ctx.source ctx.rootColumn d it →
      FirstClean ps ∧ CutInv ctx.source ctx.rootColumn d it ps
  | 0, _, ps, h, _ => by
      simp [runItemT, pure, Except.pure] at h
      subst h
      refine ⟨fun a b ha => by simp at ha, fun _ _ _ p hp => by simp at hp,
        fun _ _ _ _ _ _ p hp => by simp at hp⟩
  | 1, it, ps, h, _ => levelOneT_first (by simpa [runItemT] using h)
  | d + 2, it, ps, h, hinv => by
      have h0 := h
      simp only [runItemT, bind, Except.bind, pure, Except.pure] at h
      split at h
      · cases h
      · rename_i children hch
        split at h
        · cases h
        · rename_i outs houts
          cases h
          obtain ⟨hinvc, hsep, _⟩ := childItems_order hch hinv
          obtain ⟨hcut1, hcut2⟩ := childItems_cut hch
          obtain ⟨hlen, hall⟩ := mapM_except_spec _ _ _ houts
          have hIH : ∀ a (ha : a < outs.length), FirstClean outs[a] ∧
              CutInv ctx.source ctx.rootColumn (d + 1) (children[a]'(by omega)) outs[a] :=
            fun a ha => runItemT_first ctx (d + 1) _ _ (hall a (by omega) ha)
              (hinvc _ (List.getElem_mem _))
          have hOK : ∀ a (ha : a < outs.length), ∀ p ∈ outs[a],
              EmitOK ctx.source ctx.rootColumn (d + 1) (children[a]'(by omega)) p :=
            fun a ha => (runItemT_order ctx (d + 1) _ _ (hall a (by omega) ha)
              (hinvc _ (List.getElem_mem _))).2
          -- a member of the flattened list
          have hmem : ∀ p ∈ outs.flatten, ∃ a, ∃ ha : a < outs.length, p ∈ outs[a] := by
            intro p hp
            obtain ⟨l, hl, hpl⟩ := List.mem_flatten.mp hp
            obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hl
            exact ⟨a, ha, hpl⟩
          refine ⟨?_, ?_, ?_⟩
          · -- `FirstClean` of the flattened list
            have hpw : outs.flatten.Pairwise (fun p q => ∀ r, q.2 = .clean r false →
                p.2.src ≠ r) := by
              rw [List.pairwise_flatten]
              constructor
              · intro l hl
                obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hl
                rw [List.pairwise_iff_getElem]
                intro i j hi hj hij r hr
                exact (hIH a ha).1 i j hi hj hij r hr
              · rw [List.pairwise_iff_getElem]
                intro a b ha hb hab p hp q hq r hqr
                have hs := List.pairwise_iff_getElem.mp hsep a b (by omega) (by omega) hab
                exact sep_first hs (hOK a ha p hp) (hOK b hb q hq) (hIH b hb).2 hq hqr
            intro a b ha hb hab r hr
            exact List.pairwise_iff_getElem.mp hpw a b ha hb hab r hr
          · -- (B)
            intro C hC hb p hp
            obtain ⟨a, ha, hpa⟩ := hmem p hp
            have hca : (children[a]'(by omega)) ∈ children := List.getElem_mem _
            obtain ⟨hcC, hcb⟩ := hcut1 C hC hb _ hca
            exact (hIH a ha).2.1 C hcC hcb p hpa
          · -- (C)
            intro hcl hcb _ r ρc hρ p hp r' hpr c hc
            obtain ⟨a, ha, hpa⟩ := hmem p hp
            have hca : (children[a]'(by omega)) ∈ children := List.getElem_mem _
            have hρreg := topIn_inRegion hρ
            have hρslot : inRegion (d + 1) (slot (d + 2) it.source ((official ρc.row).coeff d))
                (official ρc.row) = true :=
              Recon.RowLaw.inRegion_slot_iff.mpr ⟨hρreg, rfl⟩
            rcases hcut2 hcl hcb r ρc hρ _ hca with ⟨C, hcC, hcb'⟩ | ⟨j, hjs, hjgt⟩ |
                ⟨hcn, hcb', hd, hcs⟩
            · obtain ⟨r1, h1⟩ := (hIH a ha).2.1 C hcC hcb' p hpa
              rw [hpr] at h1
              injection h1 with _ h2
              cases h2
            · obtain ⟨_, c1, hc1, hreg1, _⟩ := hOK a ha p hpa
              have hsrc : p.2.src = r' := by rw [hpr]; rfl
              rw [hsrc, hc] at hc1
              obtain rfl := Option.some.inj hc1
              rw [hjs] at hreg1
              exact ne_of_gt (slot_rows_lt hρslot hreg1 hjgt)
            · have hsub := topIn_slot hρ
              rw [← hcs] at hsub
              exact (hIH a ha).2.2 hcn hcb' (by omega) r ρc hsub p hpa r' hpr c hc

/-! ## The lower part and the column -/

/-- **The lower part.** -/
theorem lowerT_first {ctx : Context} {τ : Row} {lower : List (Emit × Origin)}
    (h : lowerT ctx τ = .ok lower) : FirstClean lower := by
  unfold lowerT at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i outs houts
    cases h
    obtain ⟨hlen, hall⟩ := mapM_except_spec _ _ _ houts
    have hinv : ∀ a (ha : a < outs.length), ItemInvC ctx.source ctx.rootColumn
        ((lowerItems τ)[a]'(by omega)).1 ((lowerItems τ)[a]'(by omega)).2 := by
      intro a ha C hC
      rw [lowerItems_clean τ _ (List.getElem_mem _)] at hC
      cases hC
    have hIH : ∀ a (ha : a < outs.length), FirstClean outs[a] ∧
        ∀ p ∈ outs[a], EmitOK ctx.source ctx.rootColumn ((lowerItems τ)[a]'(by omega)).1
          ((lowerItems τ)[a]'(by omega)).2 p :=
      fun a ha => ⟨(runItemT_first ctx _ _ _ (hall a (by omega) ha) (hinv a ha)).1,
        (runItemT_order ctx _ _ _ (hall a (by omega) ha) (hinv a ha)).2⟩
    have hpw : outs.flatten.Pairwise (fun p q => ∀ r, q.2 = .clean r false → p.2.src ≠ r) := by
      rw [List.pairwise_flatten]
      constructor
      · intro l hl
        obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hl
        rw [List.pairwise_iff_getElem]
        intro i j hi hj hij r hr
        exact (hIH a ha).1 i j hi hj hij r hr
      · rw [List.pairwise_iff_getElem]
        intro a b ha hb hab p hp q hq r hqr heq
        obtain ⟨_, c, hc, hreg, _⟩ := (hIH a ha).2 p hp
        obtain ⟨_, c', hc', hreg', _⟩ := (hIH b hb).2 q hq
        have hqs : q.2.src = r := by rw [hqr]; rfl
        rw [heq] at hc
        rw [hqs, hc] at hc'
        obtain rfl := Option.some.inj hc'
        exact lt_irrefl _ (List.pairwise_iff_getElem.mp (lowerItems_sep τ) a b (by omega)
          (by omega) hab _ _ hreg hreg')
    intro a b ha hb hab r hr
    exact List.pairwise_iff_getElem.mp hpw a b ha hb hab r hr

/-- **`FirstClean` for every column.** -/
theorem emitsT_first {ctx : Context} {τ : Row} {es : List (Emit × Origin)}
    (h : emitsT ctx τ = .ok es) : FirstClean es := by
  obtain ⟨lo, us, hlo, hus, rfl⟩ := CrossPlain.emitsT_parts h
  have hL := lowerT_first hlo
  intro a b ha hb hab r hr
  have hbl : b < lo.length := by
    by_contra hn
    have hmem : (lo ++ us)[b] ∈ us := by
      rw [List.getElem_append_right (by omega)]
      exact List.getElem_mem _
    have hup := CrossPlain.upperT_isUpper hus _ hmem
    rw [hr] at hup
    cases hup
  rw [List.getElem_append_left (by omega)]
  rw [List.getElem_append_left hbl] at hr
  exact hL a b (by omega) hbl hab r hr

/-- **`CleanFirst` holds.** -/
theorem cleanFirst_holds : CleanFirst := by
  intro s n R hrun M t root hTop i x hi hxb es hes k hk r hr j hj
  exact emitsT_first hes j k (by omega) hk hj r hr

end OmegaY.Official.Recon.CrossPlainPos.Pk4CF

#print axioms OmegaY.Official.Recon.CrossPlainPos.Pk4CF.emitsT_first
#print axioms OmegaY.Official.Recon.CrossPlainPos.Pk4CF.cleanFirst_holds
