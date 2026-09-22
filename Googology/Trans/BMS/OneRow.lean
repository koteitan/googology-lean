import Googology.Notation.BMS

/-!
# One-row Bashicu matrices

`BM4.expand` is stated for any number of rows, and it is `noncomputable`: the
bad root is `Classical.choose` of "the last column has a parent", and the
column map adds an increment on the rows below the maximal parent row.  Neither
is something one can match against a fundamental sequence by rewriting.

For **one row** both disappear.  There is only row `0`, so the maximal parent
row `m₀` is `0` and no row is below it — `tildeCol_one` says the column map
only copies.  And the parent is unique, so the chosen bad root is the one
index the entries already name: `p` is the last index before the last column
whose entry is smaller.  `badRoot_one` pins it down.  The choice stays in the
definition — `badRoot_one` still uses `Classical.choice` to get at
`badRoot_parent` — but it is inert, and nothing downstream has to look inside
it.

What is left is the rule itself, `expand_one_len` and `expand_one_col`: with
`s = len - 1 - p`, expansion keeps the first `p` entries and writes `N + 1`
copies of the next `s`.  That is the primitive sequence system.  When no
earlier entry is smaller than the last, `expand_one_drop` says the last column
is dropped instead.

This is what the translation in `BMS/ExBuchholz.lean` has to commute with.
-/

namespace Googology.Trans.BMS

open BM4

variable {A : Arr 1}

/-- For one row, being the parent is a plain condition on the entries: `j` is
the last index before `i` whose entry is smaller. -/
theorem parent_one {j i : Nat} :
    parent A 0 j i ↔ j < i ∧ A.col j 0 < A.col i 0 ∧
      (∀ j', j < j' → j' < i → A.col i 0 ≤ A.col j' 0) ∧ i < A.len := by
  constructor
  · rintro ⟨h1, _, h3, h4, _, h6⟩
    exact ⟨h1, h3, fun j' a b => h4 j' a b b, h6⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h1, h2, fun j' a b _ => h3 j' a b, Nat.zero_lt_one, h4⟩

/-- There is at most one parent. -/
theorem parent_one_unique {j j' i : Nat} (h : parent A 0 j i) (h' : parent A 0 j' i) :
    j = j' := by
  rw [parent_one] at h h'
  rcases Nat.lt_trichotomy j j' with hlt | heq | hgt
  · exact absurd h'.2.1 (Nat.not_lt.mpr (h.2.2.1 j' hlt h'.1))
  · exact heq
  · exact absurd h.2.1 (Nat.not_lt.mpr (h'.2.2.1 j hgt h.1))

/-- With one row there is only row `0`, so the maximal parent row is `0`. -/
theorem m₀_one (A : Arr 1) : m₀ A = 0 := rfl

/-- For one row, the last column has a parent exactly when some earlier entry
is smaller than the last. -/
theorem lastHasParent_one : LastHasParent A ↔ ∃ j, parent A 0 j (A.len - 1) := by
  constructor
  · rintro ⟨_, k, hk, hp⟩
    rw [show k = 0 by omega] at hp
    exact hp
  · rintro ⟨j, hj⟩
    exact ⟨by have := (parent_one.mp hj).2.2.2; omega, 0, Nat.zero_lt_one, ⟨j, hj⟩⟩

/-- The bad root is *the* parent: the entries pin it down, so the choice in
its definition picks nothing. -/
theorem badRoot_one {p : Nat} (h : parent A 0 p (A.len - 1)) : badRoot A = p :=
  parent_one_unique (m₀_one A ▸ badRoot_parent (lastHasParent_one.mpr ⟨p, h⟩)) h

/-- With one row the column map of an expansion copies entries and adds
nothing: the row `k < m₀` that would receive the increment does not exist. -/
theorem tildeCol_one (A : Arr 1) (p s i k : Nat) :
    tildeCol A p 0 s i k = if i < p then A.col i k else A.col (p + (i - p) % s) k := by
  unfold tildeCol
  by_cases h : i < p <;> simp [h]

/-- **One-row expansion is the primitive sequence rule**: with `p` the last
index whose entry is below the last entry and `s = len - 1 - p`, expansion
keeps the first `p` entries and repeats the next `s` of them `N + 1` times. -/
theorem expand_one_len {p : Nat} (h : parent A 0 p (A.len - 1)) (N : Nat) :
    (expand A N).len = p + (N + 1) * (A.len - 1 - p) := by
  have hl : LastHasParent A := lastHasParent_one.mpr ⟨p, h⟩
  rw [expand_len hl N]
  simp only [BadRoot.s, toBadRoot_p, badRoot_one h]

theorem expand_one_col {p : Nat} (h : parent A 0 p (A.len - 1)) (N i k : Nat) :
    (expand A N).col i k =
      if i < p then A.col i k else A.col (p + (i - p) % (A.len - 1 - p)) k := by
  have hl : LastHasParent A := lastHasParent_one.mpr ⟨p, h⟩
  have h0 : A.len ≠ 0 := by have := (parent_one.mp h).2.2.2; omega
  simp only [expand, h0, if_false, hl, if_true]
  rw [show badRoot A = p from badRoot_one h, m₀_one]
  exact tildeCol_one A p _ i k

/-- When no earlier entry is smaller than the last, expansion drops the last
column. -/
theorem expand_one_drop (h0 : A.len ≠ 0) (h : ∀ j, ¬ parent A 0 j (A.len - 1)) (N : Nat) :
    expand A N = dropLast A :=
  expand_of_not_lastHasParent h0 (fun hl => (h _ (lastHasParent_one.mp hl).choose_spec)) N

end Googology.Trans.BMS
