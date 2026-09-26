/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Rows/FillLadder.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Rows/FillLadder.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Rows.Intervals
import Mathlib.Data.List.Nodup

set_option backward.do.legacy false

/-!
# The exact reference-fill ladder

The list below uses the same descending exponents as `Expansion.fill`:
`differenceDegree, ..., 0`. Every inserted row lies in its own half-open
parent interval. This supplies the local non-overlap and upper-bound facts
without assuming numerical canonicality of the copied column.
-/

namespace OmegaY.Row

def fillLadder (lower upper : Row) : List Row :=
  ((List.range (jump lower upper)).reverse).map (bump lower)

theorem mem_fillLadder {lower upper row : Row} :
    row ∈ fillLadder lower upper ↔ ∃ d, d < jump lower upper ∧ bump lower d = row := by
  simp only [fillLadder, List.mem_map, List.mem_reverse, List.mem_range]

theorem fillLadder_length (lower upper : Row) :
    (fillLadder lower upper).length = jump lower upper := by
  simp [fillLadder]

theorem fillLadder_nodup (lower upper : Row) : (fillLadder lower upper).Nodup := by
  exact List.Nodup.map (bump_strictMono_exponent lower).injective
    (List.nodup_reverse.mpr (List.nodup_range (n := jump lower upper)))

theorem fillLadder_bounds {lower upper row : Row} (hlu : lower < upper)
    (hrow : row ∈ fillLadder lower upper) : lower < row ∧ row ≤ upper := by
  obtain ⟨d, hd, rfl⟩ := mem_fillLadder.mp hrow
  exact ⟨lt_bump lower d,
    (bump_mono_exponent lower (show d ≤ jump lower upper - 1 by omega)).trans
      (bump_last_le hlu)⟩

/-- A higher scale absorbs the preceding lower-scale step. -/
theorem bump_bump_of_lt (row : Row) {d e : Nat} (hde : d < e) :
    bump (bump row d) e = bump row e := by
  apply bump_eq_of_jump_le
  rw [jump_comm, jump_bump]
  omega

theorem fillLadder_adjacent (lower : Row) (d : Nat) :
    bump (bump lower d) (d + 1) = bump lower (d + 1) :=
  bump_bump_of_lt lower (Nat.lt_succ_self d)

theorem fillLadder_contains_upper (lower : Row) (d : Nat) :
    bump lower d ∈ fillLadder lower (bump lower d) := by
  apply mem_fillLadder.mpr
  exact ⟨d, by simp, rfl⟩

/-- The finite ladder's lower-to-upper order is strict, including all limit
scales; its generated list is the reverse of this order. -/
theorem fillLadder_strictMono (lower upper : Row) :
    StrictMono (fun d : Fin (jump lower upper) => bump lower d.val) := by
  intro a b hab
  exact bump_strictMono_exponent lower hab

/-- Ladders belonging to successive parent intervals cannot collide. -/
theorem fillLadders_separated {a b c d x y : Row}
    (hab : a < b) (hbc : b ≤ c) (hcd : c < d)
    (hx : x ∈ fillLadder a b) (hy : y ∈ fillLadder c d) : x < y :=
  lt_of_le_of_lt ((fillLadder_bounds hab hx).2.trans hbc)
    (fillLadder_bounds hcd hy).1

theorem fillLadders_disjoint {a b c d : Row}
    (hab : a < b) (hbc : b ≤ c) (hcd : c < d) :
    ∀ row, row ∈ fillLadder a b → row ∉ fillLadder c d := by
  intro row hx hy
  exact (lt_irrefl row) (fillLadders_separated hab hbc hcd hx hy)

end OmegaY.Row

#print axioms OmegaY.Row.fillLadder_bounds
#print axioms OmegaY.Row.fillLadder_nodup
#print axioms OmegaY.Row.fillLadders_disjoint
