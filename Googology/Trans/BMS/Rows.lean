import Googology.Notation.BMS

/-!
# Expansion, once the parent is known

`BM4.expand` is `noncomputable`: it reads its bad root off `Classical.choose`.
The choice is inert, though, because a column has at most one parent in a
given row.  So naming a parent pins the bad root down, and the rest of the
definition can be read off.

Nothing here depends on the number of rows.  `BMS/OneRow.lean` and
`BMS/TwoRow.lean` put `m₀` in and read the column map out.
-/

namespace Googology.Trans.BMS

open BM4

variable {r : ℕ} {A : Arr r}

/-- **A column has at most one parent in a row.**  Two candidates cannot both
be below the target and both be last. -/
theorem parent_unique {k j j' i : Nat} (h : parent A k j i) (h' : parent A k j' i) :
    j = j' := by
  obtain ⟨h1, hc1, h3, h4, _, _⟩ := h
  obtain ⟨h1', hc1', h3', h4', _, _⟩ := h'
  rcases Nat.lt_trichotomy j j' with hlt | heq | hgt
  · exact absurd h3' (Nat.not_lt.mpr (h4 j' hlt h1' hc1'))
  · exact heq
  · exact absurd h3 (Nat.not_lt.mpr (h4' j hgt h1 hc1))

/-- A parent at the maximal parent row makes the last column have one. -/
theorem lastHasParent_of_parent (hr : 0 < r) {p : Nat} (h : parent A (m₀ A) p (A.len - 1)) :
    LastHasParent A :=
  ⟨by have := h.2.2.2.2.2; omega, m₀ A, m₀_lt hr, ⟨p, h⟩⟩

/-- **The bad root is *the* parent.**  The choice in its definition picks
nothing that the array does not already name. -/
theorem badRoot_of_parent (hr : 0 < r) {p : Nat} (h : parent A (m₀ A) p (A.len - 1)) :
    badRoot A = p :=
  parent_unique (badRoot_parent (lastHasParent_of_parent hr h)) h

/-- **How long an expansion is**: the good part, then `N + 1` copies of the
bad part. -/
theorem expand_len_of_parent (hr : 0 < r) {p : Nat} (h : parent A (m₀ A) p (A.len - 1))
    (N : Nat) : (expand A N).len = p + (N + 1) * (A.len - 1 - p) := by
  rw [expand_len (lastHasParent_of_parent hr h) N]
  simp only [BadRoot.s, toBadRoot_p, badRoot_of_parent hr h]

/-- **What an expansion holds**: Definition 5.1's column map, with the bad
root named. -/
theorem expand_col_of_parent (hr : 0 < r) {p : Nat} (h : parent A (m₀ A) p (A.len - 1))
    (N i k : Nat) :
    (expand A N).col i k = tildeCol A p (m₀ A) (A.len - 1 - p) i k := by
  have h0 : A.len ≠ 0 := by have := h.2.2.2.2.2; omega
  simp only [expand, h0, if_false, lastHasParent_of_parent hr h, if_true]
  rw [badRoot_of_parent hr h]

/-- The column map below the bad root is a copy. -/
@[simp] theorem tildeCol_lt (A : Arr r) (p m s i k : Nat) (h : i < p) :
    tildeCol A p m s i k = A.col i k := by
  unfold tildeCol; simp [h]

open Classical in
/-- The column map at or above the bad root, written out. -/
theorem tildeCol_ge (A : Arr r) (p m s i k : Nat) (h : ¬ i < p) :
    tildeCol A p m s i k =
      if k < m ∧ ancEq A k p (p + (i - p) % s) then
        A.col (p + (i - p) % s) k + ((i - p) / s) * (A.col (A.len - 1) k - A.col p k)
      else A.col (p + (i - p) % s) k := by
  unfold tildeCol; simp [h]

/-- When the maximal parent row is `0` the column map only copies: there is no
row below it to carry the increment. -/
theorem tildeCol_zero (A : Arr r) (p s i k : Nat) :
    tildeCol A p 0 s i k = if i < p then A.col i k else A.col (p + (i - p) % s) k := by
  unfold tildeCol
  by_cases h : i < p <;> simp [h]

open Classical in
/-- When it is `1` the increment lands on row `0` alone. -/
theorem tildeCol_one_row (A : Arr r) (p s i k : Nat) :
    tildeCol A p 1 s i k =
      if i < p then A.col i k
      else if k = 0 ∧ ancEq A k p (p + (i - p) % s) then
        A.col (p + (i - p) % s) k + ((i - p) / s) * (A.col (A.len - 1) k - A.col p k)
      else A.col (p + (i - p) % s) k := by
  by_cases h : i < p
  · rw [tildeCol_lt A p 1 s i k h, if_pos h]
  · rw [tildeCol_ge A p 1 s i k h, if_neg h]
    simp only [Nat.lt_one_iff]

end Googology.Trans.BMS
