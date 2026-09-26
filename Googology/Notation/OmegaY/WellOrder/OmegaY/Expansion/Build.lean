/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/Build.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/Build.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.Build

set_option backward.do.legacy false

/-!
# Executable weak-magma copying

This definition works on the actual sparse mountain, with ordinal rows and
stored left endpoints.  It follows the supplied engine's decrease/copy/fill/cut
convention.  It has no fixed machine resource limits.  All structural failures
are explicit errors; totality and canonical reconstruction are separate proof
obligations.  In particular, this file does not prove well-foundedness.

Weak descendants are computed backwards along their unique incoming weak edge.
Each backward step strictly decreases the column.  The equivalence to the
engine's forward breadth-first enumeration still needs a general proof.
-/

namespace OmegaY.Expansion

open Canonical

inductive Error where
  | canonical (error : BuildError)
  | missingColumn
  | missingNode
  | missingLeft
  | missingUpper
  | nonLeftward
  | weakSearchExhausted
  | missingReference
  | invalidRoot
  | nonIncreasingRows
  | overlappingRows
  | missingPhantom
  | misplacedFill
  | unfinishedParent
  deriving DecidableEq, Repr

abbrev Result := Except Error

def lookup (mountain : Mountain) (ref : Ref) : Result Cell :=
  (cellAt mountain ref).mapError Error.canonical

def columnAt (mountain : Mountain) (column : Nat) : Result Column :=
  match mountain[column]? with
  | some result => .ok result
  | none => .error .missingColumn

def top (column : Column) : Result Cell :=
  match column.back? with
  | some result => .ok result
  | none => .error .missingNode

def leftOf (cell : Cell) : Result Ref :=
  match cell.left with
  | some result => .ok result
  | none => .error .missingLeft

/-- Highest node strictly below a ceiling, in bottom-to-top storage. -/
def below (mountain : Mountain) (column : Nat) (ceiling : Row) : Result Ref := do
  let nodes ← columnAt mountain column
  let mut chosen : Option Ref := none
  for index in List.range nodes.size do
    let cell ← lookup mountain ⟨column, index⟩
    if cell.row < ceiling then chosen := some ⟨column, index⟩
  match chosen with
  | some ref => return ref
  | none => throw .missingReference

/-- The last applicable reference in the descending boundary list. -/
def referenceAt (mountain : Mountain) (references : List Ref) (row : Row) : Result Row := do
  let mut chosen : Option Row := none
  for ref in references do
    let cell ← lookup mountain ref
    if row ≤ cell.row then chosen := some cell.row
  match chosen with
  | some result => return result
  | none => throw .missingReference

/-- Reverse one weak edge: `current.above.left`, provided its height is
unchanged. A top or a height mismatch has no incoming weak edge. -/
def weakParent (mountain : Mountain) (current : Ref) : Result (Option Ref) := do
  let column ← columnAt mountain current.column
  let cell ← lookup mountain current
  match column[current.index + 1]? with
  | none => return none
  | some upper =>
      let parent ← leftOf upper
      if ¬ parent.column < current.column then throw .nonLeftward
      let parentCell ← lookup mountain parent
      if parentCell.row ≠ cell.row then return none
      return some parent

/-- The column allowance is a structural bound, not a fixed implementation cap. -/
def weakReaches (mountain : Mountain) (root : Ref) : Nat → Ref → Result Bool
  | 0, current => if current = root then .ok true else .error .weakSearchExhausted
  | fuel + 1, current => do
      if current = root then return true
      if current.column ≤ root.column then return false
      match ← weakParent mountain current with
      | none => return false
      | some parent => weakReaches mountain root fuel parent

/-- Markers are grouped by source column, and ordered from high root rows down
to the phantom row.  Within a fixed row, a column has at most one node in a
canonical mountain. -/
def markers (mountain : Mountain) (root : Ref) : Result (Array (List Ref)) := do
  let mut result := Array.replicate mountain.size []
  for rootIndex in (List.range (root.index + 1)).reverse do
    let rootRef : Ref := ⟨root.column, rootIndex⟩
    let rootCell ← lookup mountain rootRef
    for column in List.range mountain.size do
      if root.column < column then
        let nodes ← columnAt mountain column
        for index in List.range nodes.size do
          let ref : Ref := ⟨column, index⟩
          let cell ← lookup mountain ref
          if cell.row = rootCell.row then
            if ← weakReaches mountain rootRef (column + 1) ref then
              result := result.modify column (fun refs => refs ++ [ref])
  return result

/-- Translate an actual edge.  Endpoints strictly left of the root are fixed;
other left endpoints use the highest shifted node strictly below the new row. -/
def copyEdge (mountain : Mountain) (source : Ref) (shift rootColumn : Nat)
    (row : Row) : Result Cell := do
  let cell ← lookup mountain source
  if cell.row = 0 then return ⟨row, 0, none⟩
  let oldParent ← leftOf cell
  let parent ← if oldParent.column < rootColumn then pure oldParent
    else below mountain (oldParent.column + shift) row
  if ¬ parent.column < source.column + shift then throw .nonLeftward
  return ⟨row, 0, some parent⟩

/-- Copy the segment above one marker, stopping before the next marker or at
the original value-1 top.  The finite list is the actual remaining source path. -/
def contour (mountain : Mountain) (sourceColumn : Nat) (markerIndices : List Nat)
    (shift rootColumn : Nat) : Nat → Row → Cell → List Cell → Result (List Cell)
  | _, _, current, [] => if current.value = 1 then .ok [] else .error .missingUpper
  | index, target, current, upper :: rest => do
      if current.value = 1 ∨ (index + 1) ∈ markerIndices then return []
      if ¬ current.row < upper.row then throw .nonIncreasingRows
      let nextTarget := Row.bump target (Row.jump current.row upper.row - 1)
      let copied ← copyEdge mountain ⟨sourceColumn, index + 1⟩ shift rootColumn nextTarget
      let remaining ← contour mountain sourceColumn markerIndices shift rootColumn
        (index + 1) nextTarget upper rest
      return copied :: remaining

/-- Insert every successor scale crossed by a reference edge.  The resulting
left endpoints are references into already finished columns. -/
def fill (mountain : Mountain) (source : Ref) (shift : Nat) (low high : Row) :
    Result (List Cell) := do
  let sourceCell ← lookup mountain source
  let sourceParent ← leftOf sourceCell
  let parentColumn := sourceParent.column + shift
  let nodes ← columnAt mountain parentColumn
  let mut result := []
  for index in List.range nodes.size do
    let parentRef : Ref := ⟨parentColumn, index⟩
    let parent ← lookup mountain parentRef
    if low ≤ parent.row ∧ parent.row < high then
      if ¬ parentColumn < source.column + shift then throw .nonLeftward
      let upper ← lookup mountain ⟨parentColumn, index + 1⟩
      if ¬ parent.row < upper.row then throw .nonIncreasingRows
      for d in (List.range (Row.jump parent.row upper.row)).reverse do
        result := result ++ [⟨Row.bump parent.row d, 0, some parentRef⟩]
  return result

/-- Backfill bottom-to-top cells by traversing them from their value-1 top.
The unique phantom is retained with value zero. -/
def backfill (mountain : Mountain) (upper : Cell) : List Cell → Result (List Cell)
  | [] => .ok []
  | lower :: rest => do
      if lower.row = 0 then
        if rest.isEmpty then return [⟨lower.row, 0, lower.left⟩]
        else throw .missingPhantom
      let parentRef ← leftOf upper
      let parent ← lookup mountain parentRef
      if parent.value = 0 then throw .unfinishedParent
      let next : Cell := ⟨lower.row, upper.value + parent.value, lower.left⟩
      let remaining ← backfill mountain next rest
      return next :: remaining

/-- The structural checks before numerical backfill, kept separate so their
geometric success obligation can be proved independently. -/
def validateColumnRows (sorted : List Cell) : Result Unit := do
  match sorted with
  | [] => throw .missingPhantom
  | first :: _ => if first.row ≠ 0 then throw .missingPhantom
  for pair in sorted.zip sorted.tail do
    if pair.1.row = pair.2.row then throw .overlappingRows
  return ()

/-- Numerically finish a specified bottom-to-top list after row validation. -/
def finishSorted (mountain : Mountain) (sorted : List Cell) : Result Column := do
  match sorted.reverse with
  | [] => throw .missingNode
  | last :: rest =>
      if last.row = 0 then throw .missingNode
      let topCell : Cell := ⟨last.row, 1, last.left⟩
      let lower ← backfill mountain topCell rest
      return (topCell :: lower).reverse.toArray

def finish (mountain : Mountain) (cells : List Cell) : Result Column := do
  let sorted := cells.mergeSort (fun a b => decide (a.row ≤ b.row))
  validateColumnRows sorted
  finishSorted mountain sorted

def copyColumn (mountain : Mountain) (marked : Array (List Ref)) (references : List Ref)
    (sourceColumn shift rootColumn : Nat) : Result Column := do
  let sources ← columnAt mountain sourceColumn
  let sourceMarkers := marked[sourceColumn]?.getD []
  let markerIndices := sourceMarkers.map Ref.index
  let mut cells := []
  for marker in sourceMarkers do
    let cell ← lookup mountain marker
    let copied ← copyEdge mountain marker shift rootColumn cell.row
    let target ← referenceAt mountain references cell.row
    let upperPath ← contour mountain sourceColumn markerIndices shift rootColumn
      marker.index target cell (sources.toList.drop (marker.index + 1))
    let gapCells ← fill mountain ⟨sourceColumn, marker.index + 1⟩ shift cell.row target
    cells := cells ++ [copied] ++ upperPath ++ gapCells
  finish mountain cells

def copyBlock (mountain : Mountain) (marked : Array (List Ref)) (boundaries : List Row)
    (rootColumn width block : Nat) : Result Mountain := do
  let references ← boundaries.mapM (below mountain (mountain.size - 1))
  let mut result := mountain
  for offset in List.range width do
    let sourceColumn := rootColumn + offset + 1
    let shift := block * width
    if result.size ≠ sourceColumn + shift then throw .misplacedFill
    let column ← copyColumn result marked references sourceColumn shift rootColumn
    result := result.push column
  return result

/-- The complete algorithmic graph, including every real row and left leg.
The temporary final boundary column is cut after all requested blocks. -/
def expandDiagram (values : List Nat) (copies : Nat) : Result Mountain := do
  let initial ← (Canonical.build values).mapError Error.canonical
  if values.isEmpty ∨ values.getLast? = some 1 ∨ copies = 0 then
    return initial.pop
  let lastColumn ← columnAt initial (initial.size - 1)
  let lastTop ← top lastColumn
  let root ← leftOf lastTop
  if ¬ root.column < initial.size - 1 then throw .invalidRoot
  let rootColumn ← columnAt initial root.column
  let rootCell ← lookup initial root
  let boundaries := lastTop.row ::
    ((rootColumn.toList.take (root.index + 1)).reverse.filterMap fun cell =>
      if cell.row = 0 then none else some cell.row)
  let width := initial.size - 1 - root.column
  let reduced := values.take (values.length - 1) ++ [values.getLast?.getD 1 - 1]
  let mountain ← (Canonical.build reduced).mapError Error.canonical
  let restored ← lookup mountain root
  if restored.row ≠ rootCell.row then throw .invalidRoot
  let marked ← markers mountain root
  let mut result := mountain
  for block in List.range copies do
    result ← copyBlock result marked boundaries root.column width (block + 1)
  return result.pop

def valuesOf (mountain : Mountain) : Result (List Nat) :=
  mountain.toList.mapM fun column =>
    match column[1]? with
    | some bottom => .ok bottom.value
    | none => .error .missingNode

def expand (values : List Nat) (copies : Nat) : Result (List Nat) := do
  valuesOf (← expandDiagram values copies)

#eval expand [1, 4] 5
#eval expand [1, 4, 6, 4] 2
#eval expand [1, 3, 4, 3] 2

end OmegaY.Expansion
