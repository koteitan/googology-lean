/-
Por.BMS.ParentAncestor: the lemmas about the BM4 parent and the strict ancestor relation.

Written independently from the BM4 rule. The statements (names, binders, binder names) are
fixed by how the imported 0-Y / 1-Y core (Phyrion1343/1Y-Well-Ordering-Lean,
`formalization/{ZeroY,OneY}`, Apache-2.0) calls them. Lean core only; no Mathlib.

The two lemmas about the parent after deleting all-zero rows (`parent_trimZeroRows_of_lt`,
`parent_trimZeroRows_eq_none_of_le`) are in `Por.BMS.Array`.
Taken from koteitan, 1y-wo-por, `Por/BMS/ParentAncestor.lean` (https://github.com/koteitan/1y-wo-por,
revision db86f2d13c2e18a8e2c2fae5e083d00fc4d48a78, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.Y.WellOrder.`.
-/
import Googology.Notation.Y.WellOrder.Por.BMS.Array

namespace Por.BMS

/-! ## Strict ancestors as a transitive closure -/

/-- `smaller` is reached from `larger` by one or more row-`row` parent steps. -/
def StrictAncestor (row : Nat) (array : BMSArray) (larger smaller : Nat) : Prop :=
  Relation.TransGen (fun larger smaller => parent row array larger = some smaller)
    larger smaller

/-! ## The parent as a search

`parent_eq_greatestBelow?` and `parent_eq_some_facts` are in `Por.BMS.Search`. -/

theorem parent_some_lt {row : Nat} {array : BMSArray} {target found : Nat}
    (hParent : parent row array target = some found) :
    found < target :=
  (parent_eq_some_facts hParent).2.1

theorem parent_some_entry_lt {row : Nat} {array : BMSArray} {target found : Nat}
    (hParent : parent row array target = some found) :
    ∃ left right,
      entry? array found row = some left ∧
      entry? array target row = some right ∧
      left < right := by
  have hEligible := (parent_eq_some_facts hParent).2.2
  cases row
  case zero => exact entryLt_eq_true_iff.mp hEligible
  case succ row =>
    rw [parentEligible, Bool.and_eq_true] at hEligible
    exact entryLt_eq_true_iff.mp hEligible.2

theorem parent_eq_none_iff {row : Nat} {array : BMSArray} {target : Nat} :
    parent row array target = none ↔
      array.length ≤ target ∨
        ∀ candidate, candidate < target →
          parentEligible row array target candidate = false := by
  rw [parent_eq_greatestBelow? row array target]
  rcases Nat.lt_or_ge target array.length with hTarget | hTarget
  · rw [if_pos hTarget, greatestBelow?_eq_none_iff]
    exact ⟨Or.inr, fun hCases => hCases.resolve_left (Nat.not_le.mpr hTarget)⟩
  · rw [if_neg (Nat.not_lt.mpr hTarget)]
    exact ⟨fun _ => Or.inl hTarget, fun _ => rfl⟩

/-- A row-`row+1` parent is a row-`row` ancestor. -/
theorem isAncestor_of_parent_succ {row : Nat} {array : BMSArray} {target found : Nat}
    (hParent : parent (row + 1) array target = some found) :
    isAncestor array row found target = true := by
  have hEligible := (parent_eq_some_facts hParent).2.2
  rw [parentEligible, Bool.and_eq_true] at hEligible
  exact hEligible.1

/-! ## Parent chains of a decreasing parent function -/

theorem ancestorChain_succ_of_none {parentFunction : Nat → Option Nat} {current fuel : Nat}
    (hNone : parentFunction current = none) :
    ancestorChain parentFunction current (fuel + 1) = [] := by
  simp [ancestorChain, hNone]

theorem ancestorChain_succ_of_some {parentFunction : Nat → Option Nat}
    {current fuel next : Nat} (hSome : parentFunction current = some next) :
    ancestorChain parentFunction current (fuel + 1) =
      next :: ancestorChain parentFunction next fuel := by
  simp [ancestorChain, hSome]

/-- Along a path of a decreasing parent function, the end is smaller than the start. -/
theorem transGen_lt_of_decrease
    {parentFunction : Nat → Option Nat}
    (hDecrease : ∀ {larger smaller},
      parentFunction larger = some smaller → smaller < larger)
    {larger smaller : Nat}
    (hPath : Relation.TransGen
      (fun larger smaller => parentFunction larger = some smaller) larger smaller) :
    smaller < larger := by
  induction hPath with
  | single hStep => exact hDecrease hStep
  | tail _ hStep ih => exact Nat.lt_trans (hDecrease hStep) ih

/-- A path starts with a parent step. -/
theorem transGen_parent_head_iff
    {parentFunction : Nat → Option Nat} {start finish : Nat} :
    Relation.TransGen (fun larger smaller => parentFunction larger = some smaller)
        start finish ↔
      ∃ next, parentFunction start = some next ∧
        (finish = next ∨
          Relation.TransGen (fun larger smaller => parentFunction larger = some smaller)
            next finish) := by
  constructor
  · intro hPath
    rcases transGen_head hPath with hStep | ⟨next, hStep, hRest⟩
    · exact ⟨finish, hStep, Or.inl rfl⟩
    · exact ⟨next, hStep, Or.inr hRest⟩
  · rintro ⟨next, hStep, hFinish | hRest⟩
    · subst hFinish
      exact Relation.TransGen.single hStep
    · exact Relation.TransGen.trans (Relation.TransGen.single hStep) hRest

theorem ancestorChain_mem_strictAncestor
    {parentFunction : Nat → Option Nat}
    {current fuel ancestor : Nat}
    (hMember : ancestor ∈ ancestorChain parentFunction current fuel) :
    Relation.TransGen
      (fun larger smaller => parentFunction larger = some smaller)
      current ancestor := by
  induction fuel generalizing current
  case zero => simp [ancestorChain] at hMember
  case succ fuel ih =>
    cases hFound : parentFunction current
    case none =>
      rw [ancestorChain_succ_of_none hFound] at hMember
      cases hMember
    case some found =>
      rw [ancestorChain_succ_of_some hFound, List.mem_cons] at hMember
      rcases hMember with hEq | hRest
      · rw [hEq]
        exact .single hFound
      · exact Relation.TransGen.trans (.single hFound) (ih hRest)

theorem strictAncestor_mem_ancestorChain
    {parentFunction : Nat → Option Nat}
    (hDecrease : ∀ {larger smaller},
      parentFunction larger = some smaller → smaller < larger)
    {current fuel ancestor : Nat}
    (hFuel : current ≤ fuel)
    (hAncestor : Relation.TransGen
      (fun larger smaller => parentFunction larger = some smaller)
      current ancestor) :
    ancestor ∈ ancestorChain parentFunction current fuel := by
  induction fuel generalizing current
  case zero =>
    exact absurd (transGen_lt_of_decrease hDecrease hAncestor) (by omega)
  case succ fuel ih =>
    obtain ⟨next, hNext, hRest⟩ := transGen_parent_head_iff.mp hAncestor
    have hNextLt := hDecrease hNext
    rw [ancestorChain_succ_of_some hNext, List.mem_cons]
    exact hRest.imp id (ih (by omega))

theorem ancestorChain_congr_below
    {leftParent rightParent : Nat → Option Nat} {target current fuel : Nat}
    (hLeftDecrease : ∀ {larger smaller},
      leftParent larger = some smaller → smaller < larger)
    (hParent : ∀ column, column ≤ target → leftParent column = rightParent column)
    (hCurrent : current ≤ target) :
    ancestorChain leftParent current fuel =
      ancestorChain rightParent current fuel := by
  induction fuel generalizing current
  case zero => rfl
  case succ fuel ih =>
    have hRightEq := hParent current hCurrent
    cases hFound : leftParent current
    case none =>
      rw [ancestorChain_succ_of_none hFound,
        ancestorChain_succ_of_none (hRightEq.symm.trans hFound)]
    case some found =>
      have hFoundLe : found ≤ target :=
        Nat.le_trans (Nat.le_of_lt (hLeftDecrease hFound)) hCurrent
      rw [ancestorChain_succ_of_some hFound,
        ancestorChain_succ_of_some (hRightEq.symm.trans hFound), ih hFoundLe]

theorem parentTransGen_comparable
    {parentFunction : Nat → Option Nat}
    (hDecrease : ∀ {larger smaller},
      parentFunction larger = some smaller → smaller < larger)
    {target left right : Nat}
    (hLeft : Relation.TransGen
      (fun larger smaller => parentFunction larger = some smaller) target left)
    (hRight : Relation.TransGen
      (fun larger smaller => parentFunction larger = some smaller) target right) :
    left = right ∨
      Relation.TransGen
        (fun larger smaller => parentFunction larger = some smaller) left right ∨
      Relation.TransGen
        (fun larger smaller => parentFunction larger = some smaller) right left := by
  have key : ∀ bound start, start < bound →
      ∀ {first second : Nat},
        Relation.TransGen
          (fun larger smaller => parentFunction larger = some smaller) start first →
        Relation.TransGen
          (fun larger smaller => parentFunction larger = some smaller) start second →
        first = second ∨
          Relation.TransGen
            (fun larger smaller => parentFunction larger = some smaller) first second ∨
          Relation.TransGen
            (fun larger smaller => parentFunction larger = some smaller) second first := by
    intro bound
    induction bound with
    | zero => intro start hStart; omega
    | succ bound ih =>
        intro start hStart first second hFirst hSecond
        obtain ⟨next, hNext, hFirstRest⟩ := transGen_parent_head_iff.mp hFirst
        obtain ⟨next', hNext', hSecondRest⟩ := transGen_parent_head_iff.mp hSecond
        rw [hNext] at hNext'
        cases hNext'
        rcases hFirstRest with hFirstEq | hFirstPath <;>
          rcases hSecondRest with hSecondEq | hSecondPath
        · exact Or.inl (hFirstEq.trans hSecondEq.symm)
        · subst hFirstEq
          exact Or.inr (Or.inl hSecondPath)
        · subst hSecondEq
          exact Or.inr (Or.inr hFirstPath)
        · have hLt := hDecrease hNext
          exact ih next (by omega) hFirstPath hSecondPath
  exact key (target + 1) target (Nat.lt_succ_self _) hLeft hRight

/-! ## `isAncestor` and `StrictAncestor` -/

theorem isAncestor_iff_strictAncestor
    {array : BMSArray} {row ancestor target : Nat} :
    isAncestor array row ancestor target = true ↔
      StrictAncestor row array target ancestor := by
  unfold isAncestor StrictAncestor
  rw [List.contains_iff_mem]
  exact ⟨ancestorChain_mem_strictAncestor,
    strictAncestor_mem_ancestorChain (fun hFound => parent_some_lt hFound) (Nat.le_refl _)⟩

theorem isAncestor_lt {array : BMSArray} {row ancestor target : Nat}
    (hAncestor : isAncestor array row ancestor target = true) :
    ancestor < target :=
  transGen_lt_of_decrease (fun hFound => parent_some_lt hFound)
    (isAncestor_iff_strictAncestor.mp hAncestor)

theorem direct_parent_isAncestor {array : BMSArray} {row ancestor target : Nat}
    (hParent : parent row array target = some ancestor) :
    isAncestor array row ancestor target = true :=
  isAncestor_iff_strictAncestor.mpr (Relation.TransGen.single hParent)

theorem isAncestor_trans {array : BMSArray} {row earlier middle later : Nat}
    (hEarlier : isAncestor array row earlier middle = true)
    (hMiddle : isAncestor array row middle later = true) :
    isAncestor array row earlier later = true :=
  isAncestor_iff_strictAncestor.mpr
    (Relation.TransGen.trans (isAncestor_iff_strictAncestor.mp hMiddle)
      (isAncestor_iff_strictAncestor.mp hEarlier))

/-- `ancestor` is a strict ancestor of `target` iff it is the parent of `target` or a strict
ancestor of that parent. -/
theorem isAncestor_eq_true_iff_parent {array : BMSArray} {row ancestor target : Nat} :
    isAncestor array row ancestor target = true ↔
      ∃ found, parent row array target = some found ∧
        (ancestor = found ∨ isAncestor array row ancestor found = true) := by
  rw [isAncestor_iff_strictAncestor]
  unfold StrictAncestor
  rw [transGen_parent_head_iff]
  constructor
  · rintro ⟨found, hFound, hRest⟩
    refine ⟨found, hFound, ?_⟩
    rcases hRest with hEq | hPath
    · exact Or.inl hEq
    · exact Or.inr (isAncestor_iff_strictAncestor.mpr hPath)
  · rintro ⟨found, hFound, hRest⟩
    refine ⟨found, hFound, ?_⟩
    rcases hRest with hEq | hAncestor
    · exact Or.inl hEq
    · exact Or.inr (isAncestor_iff_strictAncestor.mp hAncestor)

theorem isAncestor_congr_of_parent_eq {array : BMSArray}
    {row leftTarget rightTarget : Nat}
    (hParent : parent row array leftTarget = parent row array rightTarget) :
    ∀ ancestor,
      isAncestor array row ancestor leftTarget =
        isAncestor array row ancestor rightTarget := by
  intro ancestor
  refine bool_eq_of_true_iff ?_
  rw [isAncestor_eq_true_iff_parent, isAncestor_eq_true_iff_parent, hParent]

theorem isAncestor_eq_false_of_parent_none {array : BMSArray}
    {row ancestor target : Nat}
    (hParent : parent row array target = none) :
    isAncestor array row ancestor target = false := by
  rw [← Bool.not_eq_true]
  intro hAncestor
  obtain ⟨found, hFound, _⟩ := isAncestor_eq_true_iff_parent.mp hAncestor
  rw [hParent] at hFound
  cases hFound

theorem ancestor_le_parent {array : BMSArray}
    {row ancestor target found : Nat}
    (hParent : parent row array target = some found)
    (hAncestor : isAncestor array row ancestor target = true) :
    ancestor ≤ found := by
  obtain ⟨found', hFound', hRest⟩ := isAncestor_eq_true_iff_parent.mp hAncestor
  rw [hParent] at hFound'
  cases hFound'
  rcases hRest with hEq | hAncestorFound
  · exact Nat.le_of_eq hEq
  · exact Nat.le_of_lt (isAncestor_lt hAncestorFound)

/-- A row-`row+1` ancestor is a row-`row` ancestor. -/
theorem isAncestor_of_succ_row {array : BMSArray} {row ancestor target : Nat}
    (hAncestor : isAncestor array (row + 1) ancestor target = true) :
    isAncestor array row ancestor target = true := by
  have hChain : StrictAncestor (row + 1) array target ancestor :=
    isAncestor_iff_strictAncestor.mp hAncestor
  clear hAncestor
  unfold StrictAncestor at hChain
  induction hChain with
  | single hStep => exact isAncestor_of_parent_succ hStep
  | tail _ hStep ih => exact isAncestor_trans (isAncestor_of_parent_succ hStep) ih

theorem isAncestor_of_lt_row {array : BMSArray}
    {lowerRow row ancestor target : Nat} (hLower : lowerRow < row)
    (hAncestor : isAncestor array row ancestor target = true) :
    isAncestor array lowerRow ancestor target = true := by
  induction row with
  | zero => exact absurd hLower (Nat.not_lt_zero _)
  | succ row ih =>
      have hRow := isAncestor_of_succ_row hAncestor
      by_cases hEq : lowerRow = row
      · subst hEq
        exact hRow
      · exact ih (by omega) hRow

theorem ancestor_entries_lt {array : BMSArray} {row target ancestor : Nat}
    (hAncestor : isAncestor array row ancestor target = true) :
    ∃ ancestorValue targetValue,
      entry? array ancestor row = some ancestorValue ∧
      entry? array target row = some targetValue ∧
      ancestorValue < targetValue := by
  have hChain : StrictAncestor row array target ancestor :=
    isAncestor_iff_strictAncestor.mp hAncestor
  clear hAncestor
  unfold StrictAncestor at hChain
  induction hChain with
  | single hStep => exact parent_some_entry_lt hStep
  | tail _ hStep ih =>
      obtain ⟨middleValue, targetValue, hMiddle, hTarget, hLt⟩ := ih
      obtain ⟨ancestorValue, middleValue', hAncestorEntry, hMiddle', hLt'⟩ :=
        parent_some_entry_lt hStep
      rw [hMiddle] at hMiddle'
      cases hMiddle'
      exact ⟨ancestorValue, targetValue, hAncestorEntry, hTarget, Nat.lt_trans hLt' hLt⟩

/-! ## Locality: the parent depends only on the columns up to the target -/

/-- `greatestBelow?` depends only on the predicate below the bound. -/
theorem greatestBelow?_congr {bound : Nat} {left right : Nat → Bool}
    (hSame : ∀ candidate, candidate < bound → left candidate = right candidate) :
    greatestBelow? bound left = greatestBelow? bound right := by
  induction bound with
  | zero => rfl
  | succ bound ih =>
      rw [greatestBelow?_succ, greatestBelow?_succ, hSame bound (Nat.lt_succ_self _),
        ih fun candidate hCandidate => hSame candidate (Nat.lt_succ_of_lt hCandidate)]

theorem isAncestor_congr_below {left right : BMSArray} {row ancestor target : Nat}
    (hParent : ∀ column, column ≤ target →
      parent row left column = parent row right column) :
    isAncestor left row ancestor target = isAncestor right row ancestor target := by
  unfold isAncestor
  rw [ancestorChain_congr_below (fun hFound => parent_some_lt hFound) hParent
    (Nat.le_refl _)]

theorem parent_eq_of_entry?_eq_below {left right : BMSArray} {target : Nat}
    (hLeftTarget : target < left.length)
    (hRightTarget : target < right.length)
    (hEntry : ∀ column, column ≤ target → ∀ row,
      entry? left column row = entry? right column row) :
    ∀ row, parent row left target = parent row right target := by
  have key : ∀ row column, column ≤ target →
      parent row left column = parent row right column := by
    intro row
    induction row with
    | zero =>
        intro column hColumn
        have hLeftColumn : column < left.length := by omega
        have hRightColumn : column < right.length := by omega
        rw [parent_eq_greatestBelow? 0 left column, parent_eq_greatestBelow? 0 right column,
          if_pos hLeftColumn, if_pos hRightColumn]
        refine greatestBelow?_congr fun candidate hCandidate => ?_
        simp only [parentEligible, entryLt, hEntry candidate (by omega) 0, hEntry column hColumn 0]
    | succ row ih =>
        intro column hColumn
        have hLeftColumn : column < left.length := by omega
        have hRightColumn : column < right.length := by omega
        rw [parent_eq_greatestBelow? (row + 1) left column,
          parent_eq_greatestBelow? (row + 1) right column, if_pos hLeftColumn, if_pos hRightColumn]
        refine greatestBelow?_congr fun candidate hCandidate => ?_
        have hAncestorSame := isAncestor_congr_below (ancestor := candidate) (target := column)
          (right := right) (fun other hOther => ih other (by omega))
        simp only [parentEligible, entryLt, hAncestorSame, hEntry candidate (by omega) (row + 1),
          hEntry column hColumn (row + 1)]
  intro row
  exact key row target (Nat.le_refl _)

end Por.BMS
