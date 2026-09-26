/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/CopySegment.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/CopySegment.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.Contour
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.FillGeometry

set_option backward.do.legacy false

/-!
# One actual marker segment

The helper below is the body of one marker iteration in `copyColumn`, before
appending to the previously accumulated cells. It leaves executable order
unchanged: marker, contour, then filling. Its rows need not be sorted, but the
three pieces occupy disjoint ranges and have no duplicate rows.

The selected reference row must occur in the shifted parent column used by
`fill`. This is an explicit local input, not a claim about all reference
choices. This module does not establish separation of different markers.
-/

namespace OmegaY.Expansion

open Canonical

/-- The actual loop body for the marker `⟨sourceColumn, index⟩`. -/
def copySegment (mountain : Mountain) (sources : Column) (references : List Ref)
    (sourceColumn : Nat) (markerIndices : List Nat) (shift rootColumn index : Nat) :
    Result (List Cell) := do
  let cell ← lookup mountain ⟨sourceColumn, index⟩
  let copied ← copyEdge mountain ⟨sourceColumn, index⟩ shift rootColumn cell.row
  let target ← referenceAt mountain references cell.row
  let upperPath ← contour mountain sourceColumn markerIndices shift rootColumn
    index target cell (sources.toList.drop (index + 1))
  let gap ← fill mountain ⟨sourceColumn, index + 1⟩ shift cell.row target
  return [copied] ++ upperPath ++ gap

@[simp] private theorem segment_bind_ok {α β : Type} (a : α) (f : α → Result β) :
    (Except.ok a >>= f) = f a := rfl
@[simp] private theorem segment_pure_ok {α : Type} (a : α) :
    (pure a : Result α) = .ok a := rfl

/-- A marker lies below its gap, and the entire gap lies strictly below the
contour. The statement concerns list order only through contour strictness. -/
theorem segment_rows_nodup {low target : Row} {upper gap : List Row}
    (hLow : low ≤ target) (hUpper : (target :: upper).Pairwise (· < ·))
    (hGap : gap.Nodup) (hGapBounds : ∀ row ∈ gap, low < row ∧ row ≤ target) :
    (low :: (upper ++ gap)).Nodup := by
  obtain ⟨hAbove, hStrict⟩ := List.pairwise_cons.mp hUpper
  have hUpperNodup : upper.Nodup := hStrict.imp (fun h => ne_of_lt h)
  have hDisjoint : List.Disjoint upper gap := by
    apply List.disjoint_left.mpr
    intro row hU hG
    exact (not_lt_of_ge (hGapBounds row hG).2) (hAbove row hU)
  apply List.nodup_cons.mpr
  refine ⟨?_, List.nodup_append.mpr ⟨hUpperNodup, hGap, ?_⟩⟩
  swap
  · intro a ha b hb he
    subst b
    exact List.disjoint_left.mp hDisjoint ha hb
  intro hMem
  rcases List.mem_append.mp hMem with hU | hG
  · exact (not_lt_of_ge hLow) (hAbove low hU)
  · exact (lt_irrefl low) (hGapBounds low hG).1

/-- Local success and non-overlap of one marker iteration. Ambient columns
are already finished; neither this segment nor a future copied column is
assumed valid. In particular, readable parents here need not have positive
values, which is a separate obligation for numerical backfilling. -/
theorem copySegment_total_nodup {mountain : Mountain} (hValid : MountainValid mountain)
    {sourceColumn shift rootColumn index : Nat} {sources : Column}
    (hSources : mountain[sourceColumn]? = some sources)
    (hSourcePositive : 0 < sourceColumn)
    (hDestination : sourceColumn + shift ≤ mountain.size) (hTop : TopOne sources)
    (references : List Ref) (markerIndices : List Nat)
    {current upper : Cell} (hCurrent : sources[index]? = some current)
    (hUpper : sources[index + 1]? = some upper) {sourceParent : Ref}
    (hLeft : upper.left = some sourceParent) {parentNodes : Column}
    (hParentNodes : mountain[sourceParent.column + shift]? = some parentNodes)
    {targetIndex : Nat} {targetCell : Cell}
    (hTarget : parentNodes[targetIndex]? = some targetCell)
    (hReference : referenceAt mountain references current.row = .ok targetCell.row)
    (hLow : current.row ≤ targetCell.row) :
    ∃ copied upperPath gap,
      copyEdge mountain ⟨sourceColumn, index⟩ shift rootColumn current.row = .ok copied ∧
      copied.row = current.row ∧ copied.value = 0 ∧
      contour mountain sourceColumn markerIndices shift rootColumn index targetCell.row
        current (sources.toList.drop (index + 1)) = .ok upperPath ∧
      fill mountain ⟨sourceColumn, index + 1⟩ shift current.row targetCell.row = .ok gap ∧
      copySegment mountain sources references sourceColumn markerIndices shift rootColumn index =
        .ok ([copied] ++ upperPath ++ gap) ∧
      (([copied] ++ upperPath ++ gap).map Cell.row).Nodup ∧
      (targetCell.row :: upperPath.map Cell.row).Pairwise (· < ·) ∧
      ContourParents mountain (sourceColumn + shift) upperPath ∧
      (gap.map Cell.row).Nodup ∧
      ∀ cell ∈ gap, current.row < cell.row ∧ cell.row ≤ targetCell.row ∧ cell.value = 0 ∧
        ∃ parentRef parent, cell.left = some parentRef ∧
          lookup mountain parentRef = .ok parent ∧
          parentRef.column < sourceColumn + shift ∧ parent.row < cell.row := by
  obtain ⟨hc, hSourcesEq⟩ := Array.getElem?_eq_some_iff.mp hSources
  have hSourceValid : ColumnValid mountain sourceColumn sources := by
    rw [← hSourcesEq]
    exact hValid sourceColumn hc
  have hParentLeft : sourceParent.column < sourceColumn :=
    (hSourceValid.stored_valid _ _ _ hUpper hLeft).1
  obtain ⟨hp, hParentEq⟩ := Array.getElem?_eq_some_iff.mp hParentNodes
  have hParentValid : ColumnValid mountain (sourceParent.column + shift) parentNodes := by
    rw [← hParentEq]
    exact hValid _ hp
  have hCurrentRead : lookup mountain ⟨sourceColumn, index⟩ = .ok current :=
    lookup_ok_iff.mpr ⟨sources, hSources, hCurrent⟩
  have hUpperRead : lookup mountain ⟨sourceColumn, index + 1⟩ = .ok upper :=
    lookup_ok_iff.mpr ⟨sources, hSources, hUpper⟩
  obtain ⟨copied, hCopied, hCopiedRow, hCopiedZero⟩ :=
    copyEdge_total hValid hCurrentRead hSourcePositive hDestination
      (fun hn => lt_of_le_of_ne (Row.zero_le current.row) (Ne.symm hn))
      (rootColumn := rootColumn)
  obtain ⟨upperPath, hContour, hContourStrict, hContourParents⟩ :=
    contour_total_strict hValid hSources hSourcePositive hDestination hTop
      markerIndices targetCell.row hCurrent rfl (rootColumn := rootColumn)
  obtain ⟨gap, hFill, _, hGapNodup, hGapSpec⟩ :=
    fill_spec_of_valid_column hUpperRead hLeft hParentNodes hParentValid hTarget hParentLeft
      (low := current.row)
  refine ⟨copied, upperPath, gap, hCopied, hCopiedRow, hCopiedZero, hContour, hFill,
    ?_, ?_, hContourStrict, hContourParents, hGapNodup, hGapSpec⟩
  · simp [copySegment, hCurrentRead, hCopied, hReference, hContour, hFill]
  · simp only [List.map_append, List.map_cons, List.cons_append,
      List.nil_append, hCopiedRow]
    apply segment_rows_nodup hLow hContourStrict hGapNodup
    intro row hRow
    obtain ⟨cell, hCell, rfl⟩ := List.mem_map.mp hRow
    exact ⟨(hGapSpec cell hCell).1, (hGapSpec cell hCell).2.1⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.segment_rows_nodup
#print axioms OmegaY.Expansion.copySegment_total_nodup
