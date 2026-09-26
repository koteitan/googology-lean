/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/JumpLawLowerSplit.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.JumpLawLowerLeg

set_option backward.do.legacy false

/-!
# The two kinds of parent column of a lower pair

For a lower pair (`LowerPair`) of the column `X = x + w·i` with leg `l`, the parent column
`Y = φ_i(l)` is a new column. Since `c_r ≤ l < x` (the leg of a node is left of it), it is

* the copy of `l` in the same block `i` when `c_r < l` (`LowerRowsCopy`), or
* the boundary column `c_r + w·i`, the copy of `x₀` in block `i - 1`, when `l = c_r`
  (`LowerRowsBoundary`).

`lowerRows_of_split` proves `LowerRowsHolds` from the two cases.
-/

namespace OmegaY.Official.Recon.JumpLawLower

open Canonical Expansion Dimension RowLaw JumpLaw

/-- The conclusion of `LowerRowsHolds` for a column `Y` with lower part `vsY`. -/
def RowsConclusion (J : Item) (lam : Row) (e : Nat) (vsY : List (List Emit)) : Prop :=
  (∃ em ∈ vsY.flatten, inRegion (e + 1) J.target em.row = true) ∧
  ∀ em ∈ vsY.flatten, inRegion (e + 1) J.target em.row = true →
    ∀ d, e = d + 1 → em.row.coeff d < lam.coeff d

/-- **Open (copy case).** `LowerRowsHolds` when the leg is right of the root column: `Y` is the
copy of the column `l` in the same block. -/
def LowerRowsCopy : Prop :=
  ∀ (s : List Nat) (n : Nat) (R M : Mountain) (t : Cell) (root : Ref) (i x : Nat)
    (lam θ : Row) (l e : Nat) (J : Item), LowerPair s n R M t root i x lam θ l e J →
    root.column < l → l < x → NewColumn s n R M t root i l →
    ∀ vsY, LowerRun (colCtx M R root i l) (official t.row) vsY → RowsConclusion J lam e vsY

/-- **Open (boundary case).** `LowerRowsHolds` when the leg is the root column: `Y` is the
boundary column, the copy of `x₀` in block `i - 1`. -/
def LowerRowsBoundary : Prop :=
  ∀ (s : List Nat) (n : Nat) (R M : Mountain) (t : Cell) (root : Ref) (i x : Nat)
    (lam θ : Row) (e : Nat) (J : Item), LowerPair s n R M t root (i + 1) x lam θ root.column e J →
    NewColumn s n R M t root i (M.size - 1) →
    ∀ vsY, LowerRun (colCtx M R root i (M.size - 1)) (official t.row) vsY →
      RowsConclusion J lam e vsY

/-- The leg of a lower node is left of its column. -/
theorem lower_leg_lt {s : List Nat} {ctx : Context} {t : Cell} {root : Ref}
    (hctx : RunCtx s ctx t root) {vs : List (List Emit)}
    (hvs : LowerRun ctx (official t.row) vs) {em : Emit} (hem : em ∈ vs.flatten) {l : Nat}
    (hl : em.leftColumn = some l) : l < ctx.x := by
  obtain ⟨u, hu, _, hul⟩ := lower_leg_node hctx hvs hem hl
  obtain ⟨r, hr, rfl⟩ := leftColumn_ok hul
  have hV := build_valid_of_success hctx.top.build
  obtain ⟨col, k, hc, hcell, _⟩ := mem_realNodes_iff.mp hu
  obtain ⟨hcs, hcolEq⟩ := Array.getElem?_eq_some_iff.mp hc
  have hCV : ColumnValid ctx.source ctx.x col := hcolEq ▸ hV ctx.x hcs
  exact (hCV.stored_valid _ _ _ hcell hr).1

/-- **`LowerRowsHolds` from the copy case and the boundary case.** -/
theorem lowerRows_of_split (hC : LowerRowsCopy) (hB : LowerRowsBoundary) : LowerRowsHolds := by
  intro s n R M t root i x lam θ l e J hP i' x' hNC' hY vsY hvsY
  have hNC := hP.nc
  have hi := hP.pos
  have hctx := hNC.runCtx
  set w := M.size - 1 - root.column with hw
  have hcr := hNC.top.lt
  obtain ⟨hxgt, hxle⟩ := mem_blockColumns hcr hNC.mem
  obtain ⟨hx'gt, hx'le⟩ := mem_blockColumns hcr hNC'.mem
  -- the leg is left of `x`
  obtain ⟨vs, us, col, hvs, _, _, k, hk, hkL, _, _, hleft, _, _⟩ := hP.run
  have hlx : l < x := lower_leg_lt hctx hvs (getElem_mem_left hk hkL) hleft
  -- the leg is at least `c_r`
  have hcl : root.column ≤ l := by
    by_contra hn
    have hleg : legCol (colCtx M R root i x) l = l := by
      unfold legCol
      rw [if_neg (show ¬ (colCtx M R root i x).rootColumn ≤ l from hn)]
    rw [hleg] at hY
    have : x' ≤ x' + w * i' := Nat.le_add_right _ _
    omega
  have hleg : legCol (colCtx M R root i x) l = l + w * i := by
    unfold legCol
    rw [if_pos (show (colCtx M R root i x).rootColumn ≤ l from hcl)]
    rfl
  rw [hleg] at hY
  rcases Nat.eq_or_lt_of_le hcl with heq | hlt
  · -- the boundary column
    obtain ⟨i0, rfl⟩ : ∃ i0, i = i0 + 1 := ⟨i - 1, by omega⟩
    have hdec := decomp_unique (w := w) (a := w - 1) (b := x' - root.column - 1)
      (i := i0) (j := i') (by omega) (by omega) (by
        have e1 : w * (i0 + 1) = w * i0 + w := Nat.mul_succ w i0
        rw [e1] at hY
        generalize w * i0 = P at hY ⊢
        generalize w * i' = Q at hY ⊢
        omega)
    obtain ⟨hx', rfl⟩ : x' = M.size - 1 ∧ i0 = i' := ⟨by omega, hdec.2⟩
    subst hx'
    rw [← heq] at hP
    exact hB s n R M t root i0 x lam θ e J hP hNC' vsY hvsY
  · -- a copy in the same block
    have hdec := decomp_unique (w := w) (a := l - root.column - 1) (b := x' - root.column - 1)
      (i := i) (j := i') (by omega) (by omega) (by
        generalize w * i = P at hY ⊢
        generalize w * i' = Q at hY ⊢
        omega)
    obtain ⟨hx', rfl⟩ : x' = l ∧ i = i' := ⟨by omega, hdec.2⟩
    subst hx'
    exact hC s n R M t root i x lam θ x' e J hP hlt hlx hNC' vsY hvsY

/-- **The jump law from `LegBelowTop` and the two cases of the lower pairs.** -/
theorem jumpLawHolds_of_lowerCases
    (hT : Classification.Proofs.ChainCorr.LegJump.LegBelowTop) (hC : LowerRowsCopy)
    (hB : LowerRowsBoundary) : RowLaw.JumpLawHolds :=
  jumpLawHolds_of_legBelowTop_lowerRows hT (lowerRows_of_split hC hB)

end OmegaY.Official.Recon.JumpLawLower

#print axioms OmegaY.Official.Recon.JumpLawLower.lowerRows_of_split
#print axioms OmegaY.Official.Recon.JumpLawLower.jumpLawHolds_of_lowerCases
