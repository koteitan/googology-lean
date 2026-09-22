import Googology.Trans.BMS.Rows

/-!
# Two-row Bashicu matrices

`BMS/OneRow.lean` reads `BM4.expand` off for one row, where the column map
only copies.  Two rows is the first case where it does not.

There are two rows, so `m₀` is `0` or `1`, and `m₀_two` says which: `1`
exactly when the last column has a parent in row `1`.  When it is `0` nothing
is below it and expansion copies, as with one row — `expand_two_col_zero`.
When it is `1`, row `0` receives an increment on the columns whose position in
the bad part is a row-`0` ancestor of the bad root — `expand_two_col_one`.
That increment is what one row never sees, and it is why the pair sequences
reach `ψ_0(Ω_ω)` rather than `ε₀` — passing the Bachmann–Howard ordinal
`ψ_0(Ω_2)`, which is `(0,0)(1,1)(2,2)`, on the way.

The two rows also differ in what counts as a candidate.  Row `0` sees every
earlier column (`parent_zero_iff`); row `1` sees only the strict row-`0`
ancestors (`parent_one_iff`).

This is the ground for a two-row translation.  The reading itself is not here:
it would have to use `ψ_1` as well as `ψ_0`, and the commutation would meet
the clause of `[ ]` that one row never reaches.
-/

namespace Googology.Trans.BMS

open BM4

variable {A : Arr 2}

open Classical in
/-- With two rows the maximal parent row is `1` when the last column has a
parent there, and `0` otherwise. -/
theorem m₀_two (A : Arr 2) :
    m₀ A = if HasParent A 1 (A.len - 1) then 1 else 0 := by
  unfold m₀
  rw [show (2 : Nat) - 1 = 1 from rfl, Nat.findGreatest]
  split
  · rfl
  · rfl

/-- Row `0` sees every earlier column, so being its parent is a condition on
the row-`0` entries alone. -/
theorem parent_zero_iff {j i : Nat} :
    parent A 0 j i ↔ j < i ∧ A.col j 0 < A.col i 0 ∧
      (∀ j', j < j' → j' < i → A.col i 0 ≤ A.col j' 0) ∧ i < A.len :=
  parent_row0_iff (by omega)

/-- Row `1` sees only the strict row-`0` ancestors. -/
theorem parent_one_iff {j i : Nat} :
    parent A 1 j i ↔ j < i ∧ anc A 0 j i ∧ A.col j 1 < A.col i 1 ∧
      (∀ j', j < j' → j' < i → anc A 0 j' i → A.col i 1 ≤ A.col j' 1) ∧ i < A.len := by
  constructor
  · rintro ⟨h1, h2, h3, h4, _, h6⟩
    exact ⟨h1, h2, h3, h4, h6⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨h1, h2, h3, h4, by omega, h5⟩

/-- **Two-row expansion, when the last column has no parent in row `1`.**  The
column map only copies, exactly as with one row. -/
theorem expand_two_col_zero {p : Nat} (hm : ¬ HasParent A 1 (A.len - 1))
    (h : parent A 0 p (A.len - 1)) (N i k : Nat) :
    (expand A N).col i k =
      if i < p then A.col i k else A.col (p + (i - p) % (A.len - 1 - p)) k := by
  have hm0 : m₀ A = 0 := by rw [m₀_two, if_neg hm]
  rw [expand_col_of_parent (by omega) (by rw [hm0]; exact h) N i k, hm0]
  exact tildeCol_zero A p _ i k

open Classical in
/-- **Two-row expansion, when it does.**  Row `0` gets the increment on the
columns whose bad-root position is a row-`0` ancestor of the bad root. -/
theorem expand_two_col_one {p : Nat} (hm : HasParent A 1 (A.len - 1))
    (h : parent A 1 p (A.len - 1)) (N i k : Nat) :
    (expand A N).col i k =
      if i < p then A.col i k
      else if k = 0 ∧ ancEq A k p (p + (i - p) % (A.len - 1 - p)) then
        A.col (p + (i - p) % (A.len - 1 - p)) k
          + ((i - p) / (A.len - 1 - p)) * (A.col (A.len - 1) k - A.col p k)
      else A.col (p + (i - p) % (A.len - 1 - p)) k := by
  have hm1 : m₀ A = 1 := by rw [m₀_two, if_pos hm]
  rw [expand_col_of_parent (by omega) (by rw [hm1]; exact h) N i k, hm1]
  exact tildeCol_one_row A p _ i k

theorem expand_two_len_zero {p : Nat} (hm : ¬ HasParent A 1 (A.len - 1))
    (h : parent A 0 p (A.len - 1)) (N : Nat) :
    (expand A N).len = p + (N + 1) * (A.len - 1 - p) :=
  expand_len_of_parent (by omega) (by rw [m₀_two, if_neg hm]; exact h) N

theorem expand_two_len_one {p : Nat} (hm : HasParent A 1 (A.len - 1))
    (h : parent A 1 p (A.len - 1)) (N : Nat) :
    (expand A N).len = p + (N + 1) * (A.len - 1 - p) :=
  expand_len_of_parent (by omega) (by rw [m₀_two, if_pos hm]; exact h) N

end Googology.Trans.BMS
