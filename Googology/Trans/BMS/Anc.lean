import Googology.Trans.BMS.Entries

/-!
# The row-0 ancestor relation, on the entries

With one row the column map of an expansion only copies.  With two or more it
does not: when the maximal parent row is `1`, row `0` takes an increment on
the columns whose position in the bad part is a row-`0` ancestor of the bad
root (`BMS/TwoRow.lean`).  So any treatment of two rows has to say what
`ancEq A 0` is in terms of the array's entries.

That is this file.  `ParL` is being the row-`0` parent — the last index before
`i` whose entry is smaller — written on a list, and `AncL` is its transitive
closure.  `ParL_iff_parent` and `AncL_iff_anc` say these are `BM4.parent A 0`
and `BM4.anc A 0`, for any number of rows, because row `0`'s candidates are
all the earlier columns and nothing else in the array is consulted.

`parAt` computes the parent and `ancAtB` chases the chain, so the relation is
decidable and runs.  The chase terminates because a parent is a smaller index,
and it is correct because a column has at most one parent in a row —
`parAt_unique`, which is `parent_unique` read on the entries.
-/

namespace Googology.Trans.BMS

open BM4

variable {r : Nat} {A : Arr r}

theorem entries_getElem (A : Arr r) (i : Nat) (h : i < A.len) :
    (entries A)[i]! = A.col i 0 := by
  rw [entries, getElem!_pos _ _ (by simpa using h), List.getElem_map, List.getElem_range]

theorem entries_getElem_of_ge (A : Arr r) (i : Nat) (h : ¬ i < A.len) :
    (entries A)[i]! = 0 :=
  getElem!_neg _ _ (by simpa using h)

/-! ### The row-0 parent, on the entries -/

/-- `j` is the row-`0` parent of `i`: the last index before `i` whose entry is
smaller. -/
def ParL (l : List Nat) (j i : Nat) : Prop :=
  j < i ∧ l[j]! < l[i]! ∧ ∀ j', j < j' → j' < i → l[i]! ≤ l[j']!

/-- `j` is a strict row-`0` ancestor of `i`. -/
def AncL (l : List Nat) : Nat → Nat → Prop := Relation.TransGen (ParL l)

theorem anc_zero_eq (A : Arr r) : anc A 0 = Relation.TransGen (parent A 0) := rfl

/-- **Being the row-`0` parent is a condition on the entries.** -/
theorem ParL_iff_parent (hr : 0 < r) (A : Arr r) (j i : Nat) :
    ParL (entries A) j i ↔ parent A 0 j i := by
  rw [parent_row0_iff hr]
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hi : i < A.len := by
      by_contra hc
      rw [entries_getElem_of_ge A i hc] at h2
      omega
    have hj : j < A.len := by omega
    rw [entries_getElem A j hj, entries_getElem A i hi] at h2
    refine ⟨h1, h2, ?_, hi⟩
    intro j' a b
    have := h3 j' a b
    rwa [entries_getElem A i hi, entries_getElem A j' (by omega)] at this
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, ?_, ?_⟩
    · rw [entries_getElem A j (by omega), entries_getElem A i h4]; exact h2
    · intro j' a b
      rw [entries_getElem A i h4, entries_getElem A j' (by omega)]
      exact h3 j' a b

/-- **Being a strict row-`0` ancestor is too.** -/
theorem AncL_iff_anc (hr : 0 < r) (A : Arr r) (j i : Nat) :
    AncL (entries A) j i ↔ anc A 0 j i := by
  rw [anc_zero_eq, AncL]
  constructor
  · intro h
    induction h with
    | single hp => exact Relation.TransGen.single ((ParL_iff_parent hr A _ _).mp hp)
    | tail _ hp ih => exact Relation.TransGen.tail ih ((ParL_iff_parent hr A _ _).mp hp)
  · intro h
    induction h with
    | single hp => exact Relation.TransGen.single ((ParL_iff_parent hr A _ _).mpr hp)
    | tail _ hp ih => exact Relation.TransGen.tail ih ((ParL_iff_parent hr A _ _).mpr hp)

/-- And so is the non-strict one, which is what the column map asks for. -/
theorem AncEqL_iff (hr : 0 < r) (A : Arr r) (j i : Nat) :
    (j = i ∨ AncL (entries A) j i) ↔ ancEq A 0 j i := by
  rw [ancEq]
  exact or_congr Iff.rfl (AncL_iff_anc hr A j i)

/-! ### Computing it -/

/-- The last index below `k` whose entry is below `x`. -/
def parAux (l : List Nat) (x : Nat) : Nat → Option Nat
  | 0 => none
  | j + 1 => if l[j]! < x then some j else parAux l x j

/-- The row-`0` parent of `i`, computed from the entries. -/
def parAt (l : List Nat) (i : Nat) : Option Nat := parAux l l[i]! i

theorem parAux_eq_some (l : List Nat) (x : Nat) : ∀ (k j : Nat),
    parAux l x k = some j ↔ j < k ∧ l[j]! < x ∧ ∀ j', j < j' → j' < k → x ≤ l[j']! := by
  intro k
  induction k with
  | zero => intro j; constructor
            · intro h; rw [parAux] at h; exact absurd h (by simp)
            · rintro ⟨h, _, _⟩; omega
  | succ m ih =>
    intro j
    rw [parAux]
    by_cases hm : l[m]! < x
    · rw [if_pos hm]
      constructor
      · intro h
        rw [← Option.some.inj h]
        exact ⟨by omega, hm, fun j' a b => by omega⟩
      · rintro ⟨h1, h2, h3⟩
        by_cases hj : j = m
        · rw [hj]
        · exfalso
          have := h3 m (by omega) (by omega)
          omega
    · rw [if_neg hm]
      rw [ih j]
      constructor
      · rintro ⟨h1, h2, h3⟩
        refine ⟨by omega, h2, fun j' a b => ?_⟩
        by_cases hb : j' < m
        · exact h3 j' a hb
        · rw [show j' = m by omega]; omega
      · rintro ⟨h1, h2, h3⟩
        have hjm : j ≠ m := by intro he; rw [he] at h2; omega
        exact ⟨by omega, h2, fun j' a b => h3 j' a (by omega)⟩

theorem parAt_eq_some (l : List Nat) (i j : Nat) : parAt l i = some j ↔ ParL l j i :=
  parAux_eq_some l l[i]! i j

instance (l : List Nat) (j i : Nat) : Decidable (ParL l j i) :=
  decidable_of_iff (parAt l i = some j) (parAt_eq_some l i j)

theorem ParL_lt {l : List Nat} {j i : Nat} (h : ParL l j i) : j < i := h.1

theorem parAt_unique {l : List Nat} {i j j' : Nat} (h : parAt l i = some j)
    (h' : ParL l j' i) : j' = j :=
  Option.some.inj (((parAt_eq_some l i j').mpr h').symm.trans h)

set_option linter.unusedVariables false in
/-- Whether `p` is on the row-`0` parent chain of `i`. -/
def ancAtB (l : List Nat) (p : Nat) (i : Nat) : Bool :=
  match h : parAt l i with
  | none => false
  | some j => (j == p) || ancAtB l p j
  termination_by i
  decreasing_by exact ParL_lt ((parAt_eq_some l i j).mp h)

/-- **The computed chain is the ancestor relation.** -/
theorem ancAtB_iff (l : List Nat) (p : Nat) : ∀ i : Nat, ancAtB l p i = true ↔ AncL l p i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    rw [ancAtB]
    cases h : parAt l i with
    | none =>
      simp only [Bool.false_eq_true, false_iff]
      intro hA
      obtain ⟨j, _, hj⟩ := Relation.TransGen.tail'_iff.mp hA
      rw [← parAt_eq_some l i j] at hj
      rw [hj] at h
      exact absurd h (by simp)
    | some j =>
      simp only [Bool.or_eq_true, beq_iff_eq]
      rw [ih j (ParL_lt ((parAt_eq_some l i j).mp h))]
      constructor
      · rintro (he | hA)
        · exact Relation.TransGen.single (he ▸ (parAt_eq_some l i j).mp h)
        · exact Relation.TransGen.tail hA ((parAt_eq_some l i j).mp h)
      · intro hA
        obtain ⟨j', hr, hj'⟩ := Relation.TransGen.tail'_iff.mp hA
        rw [parAt_unique h hj'] at hr
        rcases Relation.reflTransGen_iff_eq_or_transGen.mp hr with he | ht
        · exact Or.inl he
        · exact Or.inr ht


end Googology.Trans.BMS
