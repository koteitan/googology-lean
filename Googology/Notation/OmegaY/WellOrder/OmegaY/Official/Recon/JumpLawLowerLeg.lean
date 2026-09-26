/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/JumpLawLowerLeg.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.JumpLawLower
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.ChainCorrStartLegJump

set_option backward.do.legacy false

/-!
# The legs of the lower part are at least `c_r`

`LowerLegGe` (`JumpLawLower.lean`) asks that every node of the lower part of a column of
block `i ≥ 1` has a leg `l ≥ c_r`. This file derives it from `LegBelowTop`
(`ChainCorrStartLegJump.lean`, a statement about the source mountain only: the leg of every
node of a column `c_r < c ≤ x₀` below the row of the top `t` is at least `c_r`).

Every lower node is emitted by a level-1 item of the tree of the column (`descend_to`). Its
leg is the leg of the source node `(x, σ)` (plain item) or of the node `(x, C)` of the copied
root row (clean item). Both rows are below `τ`: `σ` because the source region of an item is
below `τ` (`ItemOK.below`), and `C` because every copied root row is the row of the top of the
root column in the source region of an ancestor, or `0` (`childItems_clean`, `CleanBelow`).
-/

namespace OmegaY.Official.Recon.JumpLawLower

open Canonical Expansion Dimension RowLaw JumpLaw

/-! ## Copied root rows are below `τ` -/

/-- The row `row(ρ)` copied by the clean children of an item (`0` if the root column has no
node in the source region). -/
def rhoRowOf (ctx : Context) (d : Nat) (it : Item) : Row :=
  match topIn ctx.source ctx.rootColumn d it.source with
  | none => 0
  | some (_, c) => official c.row

/-- The copied root row of a child comes from its parent or is `row(ρ)`. -/
def CleanFrom (ctx : Context) (d : Nat) (it c : Item) : Prop :=
  c.clean = none ∨ c.clean = it.clean ∨ c.clean = some (rhoRowOf ctx d it)

theorem childItems_clean (ctx : Context) (d : Nat) (it : Item) :
    Ok (childItems ctx (d + 2) it) (fun cs => ∀ c ∈ cs, CleanFrom ctx (d + 2) it c) := by
  unfold childItems
  dsimp only
  split
  · exact ok_pure (by simp)
  · refine ok_bind (ok_true _) (fun asc _ => ?_)
    split
    · split
      · exact ok_throw_bind _ _
      · refine ok_pure ?_
        intro c hc
        obtain ⟨j, _, rfl⟩ := List.mem_map.mp hc
        exact Or.inl rfl
    · split
      · rename_i hcl
        split
        · refine ok_pure ?_
          intro c hc
          obtain ⟨j, _, rfl⟩ := List.mem_map.mp hc
          unfold CleanFrom rhoRowOf
          split_ifs <;> simp <;> right <;> rfl
        · refine ok_pure ?_
          intro c hc
          obtain ⟨j, _, rfl⟩ := List.mem_map.mp hc
          unfold CleanFrom rhoRowOf
          split_ifs <;> simp <;> right <;> rfl
      · rename_i C hC
        split
        · exact ok_throw_bind _ _
        · rename_i q hq
          obtain ⟨csRef, cs⟩ := q
          simp only [pure, Except.pure, bind, Except.bind]
          cases hg : generations ctx.source ctx.rootColumn C (ctx.x + 1) csRef cs 0 with
          | error _ => intro _ h; cases h
          | ok g =>
            simp only
            split
            · intro _ h; cases h
            · intro children hch
              simp only [Except.ok.injEq] at hch
              subst hch
              intro c hc
              obtain ⟨j, _, rfl⟩ := List.mem_map.mp hc
              unfold CleanFrom
              split_ifs <;> simp [hC]

/-- Every copied root row of an item is below `τ`. -/
def CleanBelow (τ : Row) (it : Item) : Prop := ∀ C, it.clean = some C → C < τ

theorem rhoRow_lt {s : List Nat} {ctx : Context} {t : Cell} {root : Ref}
    (hctx : RunCtx s ctx t root) {d : Nat} {it : Item}
    (hit : ItemOK ctx (official t.row) d it) : rhoRowOf ctx d it < official t.row := by
  unfold rhoRowOf
  split
  · exact lt_of_le_of_ne (Row.zero_le _) (fun h => hctx.top.real h.symm)
  · rename_i r c hrc
    exact hit.below _ (topIn_spec hrc).2.1

/-- **Copied root rows stay below `τ` down the tree.** -/
theorem desc_cleanBelow {s : List Nat} {ctx : Context} {t : Cell} {root : Ref}
    (hctx : RunCtx s ctx t root) {d : Nat} {A : Item} {d' : Nat} {B : Item}
    (hD : Desc ctx d A d' B) :
    1 ≤ d → ItemOK ctx (official t.row) d A → CleanBelow (official t.row) A →
      CleanBelow (official t.row) B := by
  induction hD with
  | refl => intro _ _ h; exact h
  | @step d A cs c d' B hcs hc hD ih =>
    intro _ hA hAc
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc
    obtain ⟨hcOK, _⟩ := child_itemOK hctx hA hcs j hj
    refine ih (by omega) hcOK ?_
    intro C hC
    rcases childItems_clean ctx d A cs hcs _ hc with h | h | h
    · rw [h] at hC; cases hC
    · rw [h] at hC; exact hAc C hC
    · rw [h] at hC
      obtain rfl := Option.some.inj hC
      exact rhoRow_lt hctx hA

theorem leftColumn_ok {cell : Cell} {l : Nat} (h : leftColumn cell = .ok l) :
    ∃ r, cell.left = some r ∧ r.column = l := by
  cases hc : cell.left with
  | none =>
    simp [leftColumn, Expansion.leftOf, hc, liftE, Except.mapError, bind, Except.bind] at h
  | some r =>
    rw [leftColumn_of hc] at h
    exact ⟨r, rfl, Except.ok.inj h⟩

/-- **The leg of a lower node is the leg of a source node below `τ`.** -/
theorem lower_leg_node {s : List Nat} {ctx : Context} {t : Cell} {root : Ref}
    (hctx : RunCtx s ctx t root) {vs : List (List Emit)}
    (hvs : LowerRun ctx (official t.row) vs) {em : Emit} (hem : em ∈ vs.flatten) {l : Nat}
    (hl : em.leftColumn = some l) :
    ∃ u ∈ realNodes ctx.source ctx.x, official u.2.row < official t.row ∧
      leftColumn u.2 = .ok l := by
  obtain ⟨F, hF, hin⟩ := lowerItems_cover (official t.row) (lower_lt hctx hvs em hem)
  obtain ⟨LF, hLF, hemF, _⟩ := mem_first_output hctx hvs hF hem hin
  obtain ⟨hFOK, _, hF1, _⟩ := lower_itemOK (ctx := ctx) hF
  obtain ⟨m, hm⟩ : ∃ m, F.1 = 0 + 1 + m := ⟨F.1 - 1, by omega⟩
  have hFOK' := hFOK
  rw [hm] at hFOK' hLF
  obtain ⟨J, LJ, hD, hLJ, hemJ⟩ := descend_to hctx 0 m F.2 LF em hFOK' hLF hemF
  obtain ⟨_, _, hJOK, _, _⟩ := desc_facts hctx hD (by omega) hFOK'
  have hFc : CleanBelow (official t.row) F.2 := by
    obtain ⟨k, j, _, _, hFeq⟩ := mem_lowerItems hF
    rw [hFeq]
    intro C hC
    cases hC
  have hJc := desc_cleanBelow hctx hD (by omega) hFOK' hFc
  have hsrc : J.source < official t.row := hJOK.below _ (self_inRegion _ _)
  change levelOne ctx J = .ok LJ at hLJ
  unfold levelOne at hLJ
  split at hLJ
  · simp [pure, Except.pure] at hLJ
    subst hLJ
    cases hemJ
  · rename_i srcRef src hsrcn
    obtain ⟨hsrcmem, hsrcrow⟩ := nodeAt_spec hsrcn
    split at hLJ
    · rename_i C hC
      split at hLJ
      · cases hLJ
      · rename_i csRef cs hcsn
        obtain ⟨hcsmem, hcsrow⟩ := nodeAt_spec hcsn
        obtain ⟨v, hv, hLJ⟩ := Reconstruction.bind_ok hLJ
        simp only [pure, Except.pure, Except.ok.injEq] at hLJ
        subst hLJ
        rw [List.mem_singleton.mp hemJ] at hl
        obtain rfl := Option.some.inj hl
        refine ⟨(csRef, cs), hcsmem, ?_, hv⟩
        rw [hcsrow]
        exact hJc C hC
    · rename_i hC
      split at hLJ
      · simp only [pure, Except.pure, Except.ok.injEq] at hLJ
        subst hLJ
        rw [List.mem_singleton.mp hemJ] at hl
        cases hl
      · obtain ⟨v, hv, hLJ⟩ := Reconstruction.bind_ok hLJ
        simp only [pure, Except.pure, Except.ok.injEq] at hLJ
        subst hLJ
        rw [List.mem_singleton.mp hemJ] at hl
        obtain rfl := Option.some.inj hl
        refine ⟨(srcRef, src), hsrcmem, ?_, hv⟩
        rw [hsrcrow]
        exact hsrc

/-- **`LowerLegGe` from `LegBelowTop`.** -/
theorem lowerLegGe_of_legBelowTop
    (hT : Classification.Proofs.ChainCorr.LegJump.LegBelowTop) : LowerLegGe := by
  intro s n R M t root i x hNC hi vs hvs em hem l hl
  have hctx := hNC.runCtx
  obtain ⟨u, hu, hurow, hul⟩ := lower_leg_node hctx hvs hem hl
  obtain ⟨r, hr, rfl⟩ := leftColumn_ok hul
  have hb := hNC.top.build
  have hV := build_valid_of_success hb
  obtain ⟨hucol, _⟩ := realNodes_column hu
  have hxgt := hctx.xgt
  have hxle := hctx.xle
  rw [hctx.rootc] at hxgt
  rw [hctx.last] at hxle
  change u.1.column = x at hucol
  change root.column < x at hxgt
  change x ≤ M.size - 1 at hxle
  have ht1 : (1 : Row) ≤ t.row := by
    obtain ⟨q, hq, rfl⟩ := top_mem hNC.top
    exact realNodes_row_one_le hV hq
  have hlt : u.2.row < t.row := by
    by_contra hn
    exact absurd hurow (not_lt.mpr (official_mono ht1 (not_lt.mp hn)))
  exact hT s M t root hNC.top u.1 u.2 r (by omega) (by omega)
    (Classification.Proofs.ChainCorr.LegJump.cell?_of_mem_realNodes hu) hr hlt

/-- **The jump law from `LegBelowTop` and the rows form of the lower pairs.** -/
theorem jumpLawHolds_of_legBelowTop_lowerRows
    (hT : Classification.Proofs.ChainCorr.LegJump.LegBelowTop) (hR : LowerRowsHolds) :
    RowLaw.JumpLawHolds :=
  jumpLawHolds_of_lowerRows (lowerLegGe_of_legBelowTop hT) hR

end OmegaY.Official.Recon.JumpLawLower

#print axioms OmegaY.Official.Recon.JumpLawLower.lowerLegGe_of_legBelowTop
#print axioms OmegaY.Official.Recon.JumpLawLower.jumpLawHolds_of_legBelowTop_lowerRows
