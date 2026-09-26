/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ColumnSegments.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/ColumnSegments.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.CopySegment
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.LoopProjection

set_option backward.do.legacy false

/-!
# Connecting marker segments to the frozen executable column loop

This module identifies the exact input passed by `copyColumn` to `finish`.
It preserves the marker bucket's order and each segment's internal order.
It does not assume or prove that `finish` succeeds.
-/

namespace OmegaY.Expansion

open Canonical

private def columnSegmentBody (mountain : Mountain) (sources : Column)
    (references : List Ref) (sourceColumn : Nat) (markerIndices : List Nat)
    (shift rootColumn : Nat) (marker : Ref) (cells : List Cell) :
    Result (ForInStep (List Cell)) := do
  let cell ← lookup mountain marker
  let copied ← copyEdge mountain marker shift rootColumn cell.row
  let target ← referenceAt mountain references cell.row
  let upperPath ← contour mountain sourceColumn markerIndices shift rootColumn
    marker.index target cell (sources.toList.drop (marker.index + 1))
  let gapCells ← fill mountain ⟨sourceColumn, marker.index + 1⟩ shift cell.row target
  return .yield (cells ++ [copied] ++ upperPath ++ gapCells)

@[simp] private theorem column_bind_ok {α β : Type} (a : α) (f : α → Result β) :
    (Except.ok a >>= f) = f a := rfl
@[simp] private theorem column_pure_ok {α : Type} (a : α) :
    (pure a : Result α) = .ok a := rfl

private theorem columnSegmentBody_eq (mountain : Mountain) (sources : Column)
    (references : List Ref) (sourceColumn : Nat) (markerIndices : List Nat)
    (shift rootColumn : Nat) (marker : Ref) (cells : List Cell)
    (hColumn : marker.column = sourceColumn) :
    columnSegmentBody mountain sources references sourceColumn markerIndices shift rootColumn
      marker cells =
      (do
        let segment ← copySegment mountain sources references sourceColumn markerIndices
          shift rootColumn marker.index
        pure (.yield (cells ++ segment))) := by
  cases marker with
  | mk column index =>
    dsimp only at hColumn
    subst column
    simp only [columnSegmentBody, copySegment, bind_assoc, pure_bind, List.append_assoc]

/-- If every actual marker segment succeeds, the original executable loop
passes exactly their ordered concatenation to `finish`. Marker-column
agreement is explicit; no validity, disjointness, or finish success is hidden
in the assumptions. -/
theorem copyColumn_eq_finish_segments {mountain : Mountain} {marked : Array (List Ref)}
    {references : List Ref} {sourceColumn shift rootColumn : Nat} {sources : Column}
    (hSources : mountain[sourceColumn]? = some sources)
    (segments : Ref → List Cell)
    (hColumns : ∀ marker ∈ marked[sourceColumn]?.getD [], marker.column = sourceColumn)
    (hSegments : ∀ marker ∈ marked[sourceColumn]?.getD [],
      copySegment mountain sources references sourceColumn
        ((marked[sourceColumn]?.getD []).map Ref.index) shift rootColumn marker.index =
          .ok (segments marker)) :
    copyColumn mountain marked references sourceColumn shift rootColumn =
      finish mountain ((marked[sourceColumn]?.getD []).flatMap segments) := by
  let bucket := marked[sourceColumn]?.getD []
  let body := columnSegmentBody mountain sources references sourceColumn
    (bucket.map Ref.index) shift rootColumn
  have hBody : ∀ marker ∈ bucket, ∀ cells : List Cell, True →
      ∃ next, body marker cells = .ok (.yield next) ∧ True ∧
        next = cells ++ segments marker := by
    intro marker hMarker cells _
    refine ⟨cells ++ segments marker, ?_, trivial, rfl⟩
    rw [show body marker cells = _ from
      columnSegmentBody_eq mountain sources references sourceColumn
        (bucket.map Ref.index) shift rootColumn marker cells (hColumns marker hMarker)]
    rw [hSegments marker hMarker]
    rfl
  obtain ⟨result, hRun, _, hResult⟩ :=
    forIn_append_projection bucket ([] : List Cell) body (fun _ => True) id segments trivial hBody
  have hResult' : result = bucket.flatMap segments := by
    simpa only [id_eq, List.nil_append] using hResult
  subst result
  unfold copyColumn
  have hRead : columnAt mountain sourceColumn = .ok sources := by
    simp only [columnAt, hSources]
  rw [hRead]
  simp only [column_bind_ok]
  change ((forIn bucket ([] : List Cell) body : Result (List Cell)) >>= finish mountain) = _
  rw [hRun]
  rfl

end OmegaY.Expansion

#print axioms OmegaY.Expansion.copyColumn_eq_finish_segments
