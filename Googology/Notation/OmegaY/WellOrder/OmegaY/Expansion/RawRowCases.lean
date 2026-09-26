/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/RawRowCases.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/RawRowCases.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.MarkerFillGeometry
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.MarkerContourGeometry

set_option backward.do.legacy false

/-! Raw row and stored-parent geometry for the actual adjacent output
pairs. This is deliberately weaker than numerical parent recovery: it
does not claim that the stored parent is the first smaller ancestor. -/

namespace OmegaY.Expansion

open Canonical Geometry

/-- The actual upper node names an existing left parent at or below the
lower node, and its row is exactly the prescribed ordinal row operation. -/
def CopiedRawAt (mountain : Mountain) (column : Column) (lower upper : Cell) : Prop :=
  ∃ parentRef parent, upper.left = some parentRef ∧
    Canonical.cellAt (mountain.push column) parentRef = .ok parent ∧
    parentRef.column < mountain.size ∧ parent.row ≤ lower.row ∧
    upper.row = Row.B lower.row parent.row

theorem CopiedCanonicalAt.raw_geometry {mountain : Mountain} {column : Column}
    {index : Nat} {lower upper : Cell}
    (hValid : MountainValid (mountain.push column))
    (h : CopiedCanonicalAt mountain column index lower upper) :
    CopiedRawAt mountain column lower upper := by
  obtain ⟨parentRef, parent, step, hPosition, hLower, hUpper⟩ := h
  have hRead : Canonical.cellAt (mountain.push column)
      ⟨mountain.size, step.position⟩ = .ok step.lower :=
    cellAt_ok_iff.mpr ⟨column, by simp, step.lower_at⟩
  obtain ⟨u, hURef, hUCell⟩ := Canonical.frame_node_of_cellAt hRead
  obtain ⟨p, hPRef, hPCell⟩ := Canonical.frame_node_of_cellAt step.parent_at
  have hFound : Canonical.findParent (mountain.push column) (Frame.ref u) = .ok (Frame.ref p) := by
    rw [hURef, hPRef]
    exact step.parent_found
  have hParent := (Executable.findParent_ref_iff hValid.toOrdered u p).mp hFound
  have hBelow : parent.row ≤ step.lower.row := by
    simpa only [Frame.height, hUCell, hPCell] using Frame.P_height_le hValid.toOrdered hParent
  exact ⟨parentRef, parent, by simpa only [hUpper] using step.upper_left,
    step.parent_at, step.parent_left, by simpa only [hLower] using hBelow,
    by simpa only [hLower, hUpper] using step.upper_row⟩

/-- Only contour interiors and joins between distinct marker segments
remain after the already proved raw geometries are removed. -/
inductive RemainingRawOrigin {mountain : Mountain} {marked : Array (List Ref)}
    {references : List Ref} {sourceColumn shift rootColumn : Nat}
    (d : ColumnCopyData mountain marked references sourceColumn shift rootColumn)
    (index : Nat) (lower upper : Cell) : Prop where
  | contour_inside (pair : ExecutedSegmentPair d index lower upper) (pathIndex : Nat)
      (position : pair.localIndex = 1 + pair.fill.length + pathIndex)
      (lower_read : pair.path[pathIndex]? = some pair.originalLower)
      (upper_read : pair.path[pathIndex + 1]? = some pair.originalUpper) :
      RemainingRawOrigin d index lower upper
  | cross_segment (seam : ExecutedSegmentSeam d index lower upper) :
      RemainingRawOrigin d index lower upper

/-- An exhaustive statement about the actual executable output, not an
assumed classification of an abstract candidate diagram. -/
theorem ColumnCopyData.prepared_adjacent_raw_cases {front : List Nat} {last : Nat}
    {p : Preparation front last} {mountain : Mountain} {references : List Ref}
    {sourceColumn shift : Nat}
    (d : ColumnCopyData mountain p.marked references sourceColumn shift p.root.column)
    (hSource : p.reduced[sourceColumn]? = some d.sources)
    (hParentPower : ∀ marker (hm : marker ∈ d.bucket),
      ColumnPowerSteps (d.marker_data marker hm).parentNodes)
    (hParentLow : ∀ marker (hm : marker ∈ d.bucket), ∃ (i : Nat) (cell : Cell),
      (d.marker_data marker hm).parentNodes[i]? = some cell ∧
        cell.row = (d.marker_data marker hm).current.row)
    (hNoPremature : NoPrematureOne d.sources) {column : Column}
    (hRun : copyColumn mountain p.marked references sourceColumn shift p.root.column = .ok column)
    {index : Nat} {lower upper : Cell}
    (hLower : column[index]? = some lower) (hUpper : column[index + 1]? = some upper)
    (hReal : lower.row ≠ 0) :
    CopiedRawAt mountain column lower upper ∨ RemainingRawOrigin d index lower upper := by
  obtain ⟨actual, hActual, _, _, _, hValid⟩ := d.copyColumn_valid
  have hEq : actual = column := Except.ok.inj (hActual.symm.trans hRun)
  subst actual
  rcases d.prepared_adjacent_canonical_cases hSource hParentPower hParentLow hNoPremature
      hRun hLower hUpper with hCanonical | hOrigin
  · exact Or.inl (hCanonical.raw_geometry hValid)
  cases hOrigin with
  | marker_fill pair _ hEq hHead =>
    obtain ⟨parentRef, parent, hLeft, hRead, hCol, hRow, hB⟩ :=
      pair.marker_fill_geometry hParentLow hRun hLower hUpper hEq hHead
    exact Or.inl ⟨parentRef, parent, hLeft, hRead, hCol, hRow.le, hB⟩
  | marker_contour pair _ hEq hEmpty hHead =>
    obtain ⟨parentRef, parent, hLeft, hRead, hCol, hRow, hB⟩ :=
      pair.marker_contour_geometry hSource hParentLow hReal hEq hEmpty hHead
    exact Or.inl ⟨parentRef, parent, hLeft, (cellAt_push_left hCol).trans hRead,
      hCol, hRow.le, hB⟩
  | contour_inside pair pathIndex hPosition hLow hUp =>
    exact Or.inr (.contour_inside pair pathIndex hPosition hLow hUp)
  | cross_segment seam => exact Or.inr (.cross_segment seam)

end OmegaY.Expansion

#print axioms OmegaY.Expansion.CopiedCanonicalAt.raw_geometry
#print axioms OmegaY.Expansion.ColumnCopyData.prepared_adjacent_raw_cases
