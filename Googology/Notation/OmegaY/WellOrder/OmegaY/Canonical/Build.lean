/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Canonical/Build.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Canonical/Build.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Rows

set_option backward.do.legacy false

/-!
# Executable canonical omega-Y mountains

This is the mathematical, exact-natural-number version of `makeMountain` in
`omega-y/engine.js`.  Columns run from the row-0 phantom to the top, so a stored
reference is `(column, indexFromBottom)`.  Zero values denote phantoms only.

Every failure is explicit.  The search allowance is the current column index;
the column allowance is its starting value minus one.  There is no fixed global
resource cap and exhaustion is never treated as a legitimate top.  In particular,
this definition alone does not assert that every legal input succeeds.
-/

namespace OmegaY.Canonical

structure Ref where
  column : Nat
  index : Nat
  deriving DecidableEq, Repr

structure Cell where
  row : Row
  value : Nat
  left : Option Ref
  deriving DecidableEq

abbrev Column := Array Cell
abbrev Mountain := Array Column

inductive BuildError where
  | invalidInput
  | invalidReference
  | missingLeft
  | nonLeftward
  | searchExhausted
  | emptyColumn
  | nonpositiveCurrent
  | columnExhausted
  deriving DecidableEq, Repr

def cellAt (mountain : Mountain) (ref : Ref) : Except BuildError Cell :=
  match mountain[ref.column]? with
  | none => .error .invalidReference
  | some column =>
      match column[ref.index]? with
      | none => .error .invalidReference
      | some cell => .ok cell

/-- Starting at a stored left endpoint, climb consecutively while the next
row is at most the CURRENT candidate's row.  Stop at the first higher row. -/
def climb (ceiling : Row) (index : Nat) : List Cell → Nat
  | [] => index
  | next :: rest =>
      if next.row ≤ ceiling then climb ceiling (index + 1) rest else index

/-- The structural Q step.  The leftward guard is a consistency check on graph
references, not an alternative parent rule.  Canonical construction is intended
to satisfy it; a malformed graph gets an explicit error. -/
def nextCandidate (mountain : Mountain) (current : Ref) : Except BuildError Ref := do
  let cell ← cellAt mountain current
  let left ← match cell.left with
    | none => .error .missingLeft
    | some left => .ok left
  if ¬ left.column < current.column then throw .nonLeftward
  let _ ← cellAt mountain left
  match mountain[left.column]? with
  | none => throw .invalidReference
  | some column =>
      return ⟨left.column,
        climb cell.row left.index (column.toList.drop (left.index + 1))⟩

/-- Each recursive call recomputes Q using the newly reached candidate's own
row.  The original target value is the only threshold held fixed. -/
def findParentAux (mountain : Mountain) (targetValue : Nat) :
    Nat → Ref → Except BuildError Ref
  | 0, _ => .error .searchExhausted
  | fuel + 1, current => do
      let candidate ← nextCandidate mountain current
      let cell ← cellAt mountain candidate
      if 0 < cell.value ∧ cell.value < targetValue then
        return candidate
      else
        findParentAux mountain targetValue fuel candidate

def findParent (mountain : Mountain) (current : Ref) : Except BuildError Ref := do
  let cell ← cellAt mountain current
  findParentAux mountain cell.value current.column current

def phantom : Cell := ⟨0, 0, none⟩

def initialColumn (column value : Nat) : Column :=
  #[phantom, ⟨1, value, if column = 0 then none else some ⟨column - 1, 0⟩⟩]

/-- Append genuine difference nodes.  The top test precedes the allowance
test, so a value-1 top reached on the last permitted step is accepted. -/
def growColumn (leftColumns : Mountain) :
    Nat → Column → Except BuildError Column
  | fuel, column =>
      match column.back? with
      | none => .error .emptyColumn
      | some child =>
          if child.value = 1 then .ok column
          else if child.value = 0 then .error .nonpositiveCurrent
          else match fuel with
          | 0 => .error .columnExhausted
          | fuel + 1 => do
              let mountain := leftColumns.push column
              let parentRef ← findParent mountain ⟨leftColumns.size, column.size - 1⟩
              let parent ← cellAt mountain parentRef
              let next : Cell := {
                row := Row.B child.row parent.row
                value := child.value - parent.value
                left := some parentRef }
              growColumn leftColumns fuel (column.push next)

def buildColumn (leftColumns : Mountain) (value : Nat) : Except BuildError Column :=
  if value = 0 then .error .invalidInput
  else growColumn leftColumns (value - 1) (initialColumn leftColumns.size value)

def buildFrom : Mountain → List Nat → Except BuildError Mountain
  | mountain, [] => .ok mountain
  | mountain, value :: rest => do
      let column ← buildColumn mountain value
      buildFrom (mountain.push column) rest

/-- Empty sequences, or positive sequences beginning with 1, are accepted.
Other inputs get an explicit input error, as in the engine's validation. -/
def build (values : List Nat) : Except BuildError Mountain :=
  match values with
  | [] => .ok #[]
  | 1 :: rest =>
      if rest.all (fun n => 0 < n) then buildFrom #[] (1 :: rest)
      else .error .invalidInput
  | _ => .error .invalidInput

/-- All internal rows and values, including each row-0 phantom.  Coefficients
are listed in ascending exponent order, matching the engine's representation. -/
def rowValues (mountain : Mountain) : List (List (List Nat × Nat)) :=
  mountain.toList.map fun column =>
    column.toList.map fun cell => (Row.toList cell.row, cell.value)

/-- Also expose every stored left reference for direct semantic inspection. -/
def fullSummary (mountain : Mountain) :
    List (List (List Nat × Nat × Option (Nat × Nat))) :=
  mountain.toList.map fun column =>
    column.toList.map fun cell =>
      (Row.toList cell.row, cell.value, cell.left.map fun ref => (ref.column, ref.index))

def buildRowValues (values : List Nat) : Except BuildError (List (List (List Nat × Nat))) :=
  (build values).map rowValues

#eval buildRowValues [1, 4]
#eval buildRowValues [1, 4, 6, 4]
#eval (build [1, 4, 6, 4]).map fullSummary

end OmegaY.Canonical
