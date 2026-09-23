import Googology.Trans.BMS.ZeroRow

/-!
# BMS: the zero-row embedding is not onto

`Trans/BMS/ZeroRow.lean` puts BMS with `r + 1` rows inside BMS with `r + 2`
rows, by writing a row of zeros underneath (`bmsL_homSucc`).  Every column of
an image therefore ends in `0`.  The two-row generator `(0,0)(1,1)` has a
column ending in `1`, so it is not an image, and the map is not onto.
-/

namespace Googology.Trans.BMS

/-- **It is not onto**: the generator `(0,0)(1,1)` of two-row BMS has `1` in
its bottom row, and every column of an image ends in `0`. -/
theorem bmsToSucc_not_surjective :
    ¬ ∀ (i : Nat) (c : (bmsL (i + 1)).State), ∃ a : (bmsL i).State,
      True ∧ (bmsL_homSucc i).map a = c := by
  intro h
  obtain ⟨a, -, ha⟩ := h 0 ((bmsLStd 1).gen 1)
  have hv : zeroRow a.1 = [[0, 0], [1, 1]] := congrArg Subtype.val ha
  have hm : [1, 1] ∈ zeroRow a.1 := by rw [hv]; decide
  obtain ⟨d, -, hd⟩ := List.mem_map.mp hm
  have := congrArg List.getLast? hd
  simp at this

end Googology.Trans.BMS
