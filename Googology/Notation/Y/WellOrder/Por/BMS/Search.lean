/-
Por.BMS.Search: the specification of `greatestBelow?`, the parent as a search, the
characterizations of `entry?`, `entryLt` and `expansionPivot?`, and the head decomposition
of `Relation.TransGen`.

Written independently. The statements (names, binders, binder names) are fixed by how the
imported 0-Y / 1-Y core (Phyrion1343/1Y-Well-Ordering-Lean, `formalization/{ZeroY,OneY}`,
Apache-2.0) calls them. Lean core only; no Mathlib.
Taken from koteitan, 1y-wo-por, `Por/BMS/Search.lean` (https://github.com/koteitan/1y-wo-por,
revision db86f2d13c2e18a8e2c2fae5e083d00fc4d48a78, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.Y.WellOrder.`.
-/
import Googology.Notation.Y.WellOrder.Por.BMS.Defs

namespace Por.BMS

/-! ## Equations of the downward scan -/

@[simp] theorem greatestBelow?_zero (predicate : Nat → Bool) :
    greatestBelow? 0 predicate = none := rfl

/-- One step of the scan: test `bound` first, then continue below it. -/
theorem greatestBelow?_succ (bound : Nat) (predicate : Nat → Bool) :
    greatestBelow? (bound + 1) predicate =
      (if predicate bound = true then some bound else greatestBelow? bound predicate) := by
  unfold greatestBelow?
  rw [List.range_succ, List.reverse_append]
  cases hTop : predicate bound <;> simp [hTop]

/-! ## Specification -/

/-- `greatestBelow? bound predicate = some found` iff `found` is the largest
`m < bound` with `predicate m = true`. -/
theorem greatestBelow?_eq_some_iff {bound found : Nat} {predicate : Nat → Bool} :
    greatestBelow? bound predicate = some found ↔
      found < bound ∧ predicate found = true ∧
        ∀ candidate, candidate < bound → predicate candidate = true → candidate ≤ found := by
  induction bound with
  | zero => simp
  | succ bound ih =>
      rw [greatestBelow?_succ]
      rcases Bool.eq_false_or_eq_true (predicate bound) with hTop | hTop
      · rw [if_pos hTop, Option.some.injEq]
        refine ⟨fun hEq => ?_, fun hSpec => ?_⟩
        · subst hEq
          exact ⟨by omega, hTop, fun other hOther _ => by omega⟩
        · have hLe := hSpec.2.2 bound (by omega) hTop
          have hLt := hSpec.1
          omega
      · rw [if_neg (by rw [hTop]; decide), ih]
        refine ⟨fun ⟨hLt, hSat, hMax⟩ => ⟨by omega, hSat, ?_⟩,
          fun ⟨hLt, hSat, hMax⟩ => ?_⟩
        · intro other hOther hOtherSat
          have hNe : other ≠ bound := fun hEq => by rw [← hEq, hOtherSat] at hTop; cases hTop
          exact hMax other (by omega) hOtherSat
        · have hNe : found ≠ bound := fun hEq => by rw [← hEq, hSat] at hTop; cases hTop
          exact ⟨by omega, hSat, fun other hOther => hMax other (by omega)⟩

/-- A found value is below the bound. -/
theorem greatestBelow?_some_lt {bound : Nat} {predicate : Nat → Bool} {found : Nat}
    (hFound : greatestBelow? bound predicate = some found) :
    found < bound :=
  (greatestBelow?_eq_some_iff.mp hFound).1

/-- A found value satisfies the predicate. -/
theorem greatestBelow?_some_satisfies {bound : Nat} {predicate : Nat → Bool} {found : Nat}
    (hFound : greatestBelow? bound predicate = some found) :
    predicate found = true :=
  (greatestBelow?_eq_some_iff.mp hFound).2.1

/-- A found value is the largest one below the bound that satisfies the predicate. -/
theorem greatestBelow?_some_isGreatest {bound : Nat} {predicate : Nat → Bool} {found : Nat}
    (hFound : greatestBelow? bound predicate = some found) :
    ∀ candidate, candidate < bound → predicate candidate = true → candidate ≤ found :=
  (greatestBelow?_eq_some_iff.mp hFound).2.2

/-- `greatestBelow? bound predicate = none` iff no `m < bound` satisfies the predicate. -/
theorem greatestBelow?_eq_none_iff {bound : Nat} {predicate : Nat → Bool} :
    greatestBelow? bound predicate = none ↔
      ∀ candidate, candidate < bound → predicate candidate = false := by
  simp only [greatestBelow?, List.find?_eq_none, List.mem_reverse, List.mem_range,
    Bool.not_eq_true]

/-! ## Booleans and entries -/

/-- Two booleans are equal when each is `true` exactly when the other is. -/
theorem bool_eq_of_true_iff {left right : Bool} (hSame : left = true ↔ right = true) :
    left = right := by
  cases left <;> cases right <;> simp_all

theorem entry?_eq_some_iff {array : BMSArray} {column row value : Nat} :
    entry? array column row = some value ↔
      ∃ found, array[column]? = some found ∧ found[row]? = some value :=
  Option.bind_eq_some_iff

theorem entryLt_eq_true_iff {array : BMSArray} {row candidate target : Nat} :
    entryLt array row candidate target = true ↔
      ∃ left right, entry? array candidate row = some left ∧
        entry? array target row = some right ∧ left < right := by
  unfold entryLt
  cases entry? array candidate row <;> cases entry? array target row <;> simp

/-! ## The parent as a search -/

theorem parent_eq_greatestBelow? (row : Nat) (array : BMSArray) (target : Nat) :
    parent row array target =
      (if target < array.length then greatestBelow? target (parentEligible row array target)
        else none) := by
  cases row <;> rfl

/-- What a found parent satisfies: the target is a column, the parent lies to its left and
passes the eligibility test. -/
theorem parent_eq_some_facts {row : Nat} {array : BMSArray} {target found : Nat}
    (hParent : parent row array target = some found) :
    target < array.length ∧ found < target ∧ parentEligible row array target found = true := by
  have hSearch := parent_eq_greatestBelow? row array target
  rw [hParent] at hSearch
  rcases Nat.lt_or_ge target array.length with hTarget | hTarget
  · rw [if_pos hTarget] at hSearch
    exact ⟨hTarget, greatestBelow?_some_lt hSearch.symm, greatestBelow?_some_satisfies hSearch.symm⟩
  · rw [if_neg (Nat.not_lt.mpr hTarget)] at hSearch
    cases hSearch

/-! ## The pivot of an expansion -/

theorem expansionPivot?_eq_some_iff {array : BMSArray} {m₀ root : Nat} :
    expansionPivot? array = some (m₀, root) ↔
      maximalParentRow array = some m₀ ∧ parent m₀ array (array.length - 1) = some root := by
  unfold expansionPivot?
  constructor
  · intro hPivot
    obtain ⟨row, hRow, hMap⟩ := Option.bind_eq_some_iff.mp hPivot
    obtain ⟨found, hFound, hPair⟩ := Option.map_eq_some_iff.mp hMap
    cases hPair
    exact ⟨hRow, hFound⟩
  · rintro ⟨hRow, hFound⟩
    simp [hRow, hFound]

theorem expandRaw_of_maximalParentRow_none {array : BMSArray}
    (hNone : maximalParentRow array = none) (index : Nat) :
    expandRaw array index = array.take (array.length - 1) := by
  simp [expandRaw, expansionPivot?, hNone]

/-- A `TransGen` path either is one step or starts with a step followed by a path. -/
theorem transGen_head
    {α : Type} {relation : α → α → Prop} {start finish : α}
    (path : Relation.TransGen relation start finish) :
    relation start finish ∨
      ∃ next, relation start next ∧ Relation.TransGen relation next finish := by
  induction path with
  | single hStep => exact Or.inl hStep
  | tail _ hLast ih =>
      cases ih with
      | inl hFirst => exact Or.inr ⟨_, hFirst, Relation.TransGen.single hLast⟩
      | inr hRest =>
          obtain ⟨next, hFirst, hPath⟩ := hRest
          exact Or.inr ⟨next, hFirst, Relation.TransGen.tail hPath hLast⟩

end Por.BMS
