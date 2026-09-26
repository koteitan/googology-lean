/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/TSQBiTopRows.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.TSQRootTop
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.RowLawRows

set_option backward.do.legacy false

set_option autoImplicit false

/-!
# The first item of the root row (`TSQ`, `BiTopLow`)

A statement about rows only. Let `τ = B(a, b)` (the row law of the top `t` of the last column,
`a = row t⁻`, `b = row r`), and let a first item `F = (k + 1, S)` (`S = slot (k + 2) τ j`,
`j < τ_k`) contain a row `C` with `b ≤ C < τ`. Then

* `b` is in `F` (`root_mem_first`);
* every row `r < τ` outside `F` is below every row of `F` (`below_first`).

With `J = jump(a, b)`: `τ_m = a_m = b_m` for `m > J`, `τ_J = a_J + 1 = b_J + 1`, `τ_m = 0` for
`m < J`. So `k ≥ J` (`τ_k > 0`), and `k > J` would put `b` above `C`. Hence `k = J` and
`j = b_J`: `F` is the region of `b` of level `J + 1`, and it reaches up to `τ`.
-/

namespace OmegaY.Official.Recon.TSQ.BTL

open Canonical Classification

theorem coeff_B_high {a b : Row} {m : Nat} (h : Row.jump a b < m) :
    (Row.B a b).coeff m = a.coeff m := Row.coeff_bump_high h

theorem coeff_B_at (a b : Row) : (Row.B a b).coeff (Row.jump a b) = a.coeff (Row.jump a b) + 1 :=
  Row.coeff_bump_at a _

theorem coeff_B_low {a b : Row} {m : Nat} (h : m < Row.jump a b) : (Row.B a b).coeff m = 0 :=
  Row.coeff_bump_low h

theorem agree_of_jump (a b : Row) {m : Nat} (h : Row.jump a b ≤ m) : a.coeff m = b.coeff m :=
  Row.jump_le_iff.mp le_rfl m h

/-- The region of level `k + 1` with base `slot (k + 2) τ j`, by coefficients. -/
theorem mem_first_iff {τ r : Row} {k j : Nat} :
    inRegion (k + 1) (slot (k + 2) τ j) r = true ↔
      (∀ m, k < m → r.coeff m = τ.coeff m) ∧ r.coeff k = j := by
  rw [Recon.RowLaw.inRegion_iff']
  constructor
  · intro h
    refine ⟨fun m hm => ?_, ?_⟩
    · rw [h m (by omega), Recon.RowLaw.slot_coeff_high hm]
    · rw [h k (by omega), Recon.RowLaw.slot_coeff_at]
  · rintro ⟨h1, h2⟩ m hm
    rcases Nat.lt_or_eq_of_le (show k ≤ m by omega) with hlt | heq
    · rw [h1 m hlt, Recon.RowLaw.slot_coeff_high hlt]
    · subst heq; rw [h2, Recon.RowLaw.slot_coeff_at]

/-- In the setting, the level index of the first item is the jump `J = jump(a, b)`. -/
theorem first_index {a b C : Row} {k j : Nat} (hbC : b ≤ C)
    (hj : j < (Row.B a b).coeff k)
    (hC : inRegion (k + 1) (slot (k + 2) (Row.B a b) j) C = true) :
    k = Row.jump a b ∧ j = b.coeff k := by
  obtain ⟨hC1, hC2⟩ := mem_first_iff.mp hC
  have hkJ : Row.jump a b ≤ k := by
    by_contra hn
    rw [coeff_B_low (by omega)] at hj
    omega
  have hbhigh : ∀ m, Row.jump a b ≤ m → b.coeff m = a.coeff m :=
    fun m hm => (agree_of_jump a b hm).symm
  -- `k > J` puts `b` above `C`
  have hk : k = Row.jump a b := by
    by_contra hne
    have hlt : Row.jump a b < k := lt_of_le_of_ne hkJ (Ne.symm hne)
    have hCb : C < b := by
      apply Row.lt_iff.mpr
      refine ⟨k, fun m hm => ?_, ?_⟩
      · rw [hC1 m hm, coeff_B_high (by omega), hbhigh m (by omega)]
      · rw [hC2, hbhigh k (by omega)]
        rw [coeff_B_high hlt] at hj
        exact hj
    exact absurd (lt_of_lt_of_le hCb hbC) (lt_irrefl _)
  subst hk
  refine ⟨rfl, ?_⟩
  -- `j = b_J`
  rw [coeff_B_at] at hj
  have hbJ : b.coeff (Row.jump a b) = a.coeff (Row.jump a b) := hbhigh _ le_rfl
  have hle : b.coeff (Row.jump a b) ≤ j := by
    by_contra hn
    have hCb : C < b := by
      apply Row.lt_iff.mpr
      refine ⟨Row.jump a b, fun m hm => ?_, ?_⟩
      · rw [hC1 m hm, coeff_B_high hm, hbhigh m (by omega)]
      · rw [hC2]; omega
    exact absurd (lt_of_lt_of_le hCb hbC) (lt_irrefl _)
  omega

/-- **The root row lies in the first item of `C`.** -/
theorem root_mem_first {a b C : Row} {k j : Nat} (hbC : b ≤ C)
    (hj : j < (Row.B a b).coeff k)
    (hC : inRegion (k + 1) (slot (k + 2) (Row.B a b) j) C = true) :
    inRegion (k + 1) (slot (k + 2) (Row.B a b) j) b = true := by
  obtain ⟨hk, hjb⟩ := first_index hbC hj hC
  apply mem_first_iff.mpr
  refine ⟨fun m hm => ?_, hjb.symm⟩
  rw [coeff_B_high (by omega)]
  exact (agree_of_jump a b (by omega)).symm

/-- **The first item of `C` reaches up to `τ`.** A row below `τ` outside it is below each of
its rows. -/
theorem below_first {a b C : Row} {k j : Nat} (hbC : b ≤ C)
    (hj : j < (Row.B a b).coeff k)
    (hC : inRegion (k + 1) (slot (k + 2) (Row.B a b) j) C = true)
    {r r' : Row} (hr : r < Row.B a b)
    (hr' : inRegion (k + 1) (slot (k + 2) (Row.B a b) j) r' = true)
    (hnot : inRegion (k + 1) (slot (k + 2) (Row.B a b) j) r = false) : r < r' := by
  obtain ⟨hk, hjb⟩ := first_index hbC hj hC
  subst hk
  obtain ⟨hr'1, hr'2⟩ := mem_first_iff.mp hr'
  by_contra hn
  have hle : r' ≤ r := le_of_not_gt hn
  -- `r` agrees with `τ` above `J`
  have hjump : Row.jump r' (Row.B a b) ≤ Row.jump a b + 1 := by
    apply Row.jump_le_iff.mpr
    intro m hm
    exact hr'1 m (by omega)
  obtain ⟨_, hj2⟩ := Row.jump_le_between hle hr.le hjump
  have hrhigh : ∀ m, Row.jump a b < m → r.coeff m = (Row.B a b).coeff m :=
    fun m hm => Row.jump_le_iff.mp hj2 m (by omega)
  -- `r_J = j`
  have hrJ1 : r'.coeff (Row.jump a b) ≤ r.coeff (Row.jump a b) := by
    by_contra hn'
    have : r < r' := by
      apply Row.lt_iff.mpr
      refine ⟨Row.jump a b, fun m hm => ?_, by omega⟩
      rw [hrhigh m hm, hr'1 m hm]
    exact absurd (lt_of_lt_of_le this hle) (lt_irrefl _)
  have hrJ2 : r.coeff (Row.jump a b) < (Row.B a b).coeff (Row.jump a b) := by
    obtain ⟨i, hi1, hi2⟩ := Row.lt_iff.mp hr
    rcases Nat.lt_trichotomy i (Row.jump a b) with h | h | h
    · rw [coeff_B_low h] at hi2; omega
    · subst h; exact hi2
    · rw [hrhigh i h] at hi2; omega
  rw [coeff_B_at] at hrJ2
  have hbJ : b.coeff (Row.jump a b) = a.coeff (Row.jump a b) :=
    (agree_of_jump a b le_rfl).symm
  have hrin : inRegion (Row.jump a b + 1) (slot (Row.jump a b + 2) (Row.B a b) j) r = true := by
    apply mem_first_iff.mpr
    refine ⟨fun m hm => hrhigh m hm, ?_⟩
    omega
  rw [hrin] at hnot
  cases hnot

end OmegaY.Official.Recon.TSQ.BTL

#print axioms OmegaY.Official.Recon.TSQ.BTL.root_mem_first
#print axioms OmegaY.Official.Recon.TSQ.BTL.below_first
