/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Rows/Truncate.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Rows/Truncate.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Rows

set_option backward.do.legacy false

/-! High-coefficient prefixes, with the ordinary Cantor row order. -/

namespace OmegaY.Row

def cut (a : Row) (k : Nat) : Row := ⟨a.coeffs.filter (fun i => k ≤ i)⟩

@[simp] theorem coeff_cut (a : Row) (k i : Nat) :
    coeff (cut a k) i = if k ≤ i then coeff a i else 0 := by
  simp [cut, coeff, Finsupp.filter_apply]

@[simp] theorem cut_zero (a : Row) : cut a 0 = a := by
  ext i
  simp

theorem cut_cut (a : Row) (k l : Nat) : cut (cut a k) l = cut a (max k l) := by
  ext i
  simp only [coeff_cut, max_le_iff]
  by_cases hk : k ≤ i <;> by_cases hl : l ≤ i <;> simp [hk, hl]

theorem cut_monotone (k : Nat) : Monotone (fun a : Row => cut a k) := by
  intro a b hab
  rcases lt_or_eq_of_le hab with hlt | rfl
  · obtain ⟨i, hHigher, hAt⟩ := lt_iff.mp hlt
    by_cases hi : k ≤ i
    · apply le_of_lt
      apply lt_iff.mpr
      refine ⟨i, ?_, ?_⟩
      · intro j hj
        simp only [coeff_cut, if_pos (hi.trans hj.le), hHigher j hj]
      · simpa only [coeff_cut, if_pos hi] using hAt
    · apply le_of_eq
      ext j
      by_cases hj : k ≤ j
      · simp only [coeff_cut, if_pos hj, hHigher j (by omega)]
      · simp only [coeff_cut, if_neg hj]
  · exact le_rfl

/-- A strict high-prefix difference remains strict when lower coordinates
are restored; no equality of those lower coordinates is required. -/
theorem cut_strict_finer {a b : Row} {fine coarse : Nat} (hScale : fine ≤ coarse)
    (h : cut a coarse < cut b coarse) : cut a fine < cut b fine := by
  by_contra hn
  have hReverse := cut_monotone coarse (le_of_not_gt hn)
  dsimp only at hReverse
  rw [cut_cut, cut_cut, max_eq_right hScale] at hReverse
  exact not_lt_of_ge hReverse h

theorem cut_le_of_cut_le {a b : Row} {fine coarse : Nat} (hScale : fine ≤ coarse)
    (h : cut a fine ≤ cut b fine) : cut a coarse ≤ cut b coarse := by
  have ht := cut_monotone coarse h
  simpa only [cut_cut, max_eq_right hScale] using ht

end OmegaY.Row

#print axioms OmegaY.Row.cut_monotone
#print axioms OmegaY.Row.cut_strict_finer
