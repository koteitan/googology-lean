/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/PreparedExtension.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/PreparedExtension.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.FrozenSource
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.RootReferenceAt
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.PreparedPhantom

set_option backward.do.legacy false

/-! The initial block reference intervals remain exact after any sequence
of column appends. Only complete-column preservation is used. These results
do not identify a newly selected reference map in a later block. -/

namespace OmegaY.Expansion

open Canonical

theorem PreservesColumns.cellAt {before after : Mountain}
    (hPreserve : PreservesColumns before after) {ref : Ref}
    (hc : ref.column < before.size) :
    Canonical.cellAt after ref = Canonical.cellAt before ref :=
  cellAt_eq_of_column_eq (hPreserve ref.column hc)

theorem Preparation.initial_referenceAt_preserved {front : List Nat} {last : Nat}
    (p : Preparation front last) {ambient : Mountain}
    (hPreserve : PreservesColumns p.reduced ambient) {references : List Ref}
    (hMap : p.boundaries.mapM (below p.reduced (p.reduced.size - 1)) = .ok references)
    (row : Row) : referenceAt ambient references row = referenceAt p.reduced references row :=
  hPreserve.referenceAt (p.initial_references_valid hMap) row

theorem Preparation.cell_read_preserved {front : List Nat} {last : Nat}
    (p : Preparation front last) {ambient : Mountain}
    (hPreserve : PreservesColumns p.reduced ambient) {ref : Ref} {cell : Cell}
    (hRead : Canonical.cellAt p.reduced ref = .ok cell) :
    Canonical.cellAt ambient ref = .ok cell := by
  obtain ⟨nodes, hColumn, hIndex⟩ := cellAt_ok_iff.mp hRead
  exact cellAt_ok_iff.mpr ⟨nodes, hPreserve.column_read hColumn, hIndex⟩

theorem Preparation.initial_referenceAt_zero_extended {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) {ambient : Mountain}
    (hPreserve : PreservesColumns p.reduced ambient) {references : List Ref}
    (hMap : p.boundaries.mapM (below p.reduced (p.reduced.size - 1)) = .ok references) :
    referenceAt ambient references 0 = .ok 0 := by
  rw [p.initial_referenceAt_preserved hPreserve hMap]
  exact p.initial_referenceAt_zero hLast hMap

/-- The source and target inequalities are derived from preparation in the
original graph, then applied to the same actual reads in the extension. -/
theorem Preparation.initial_marker_reference_interval_extended {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) {ambient : Mountain}
    (hPreserve : PreservesColumns p.reduced ambient) {references : List Ref}
    (hMap : p.boundaries.mapM (below p.reduced (p.reduced.size - 1)) = .ok references)
    {bucket : Nat} {marker : Ref} (hMarker : BucketMem p.marked bucket marker)
    {source : Cell} (hSource : Canonical.cellAt ambient marker = .ok source) :
    ∃ target ceiling degree,
      referenceAt ambient references source.row = .ok target ∧
      source.row ≤ target ∧ target < ceiling ∧
      ceiling = Row.bump source.row degree ∧ ceiling ≤ p.lastTop.row := by
  obtain ⟨oldSource, target, ceiling, degree, hOldSource, hReference, hLow, hHigh, hPower, hTop⟩ :=
    p.initial_marker_reference_interval hLast hMap hMarker
  have he : oldSource = source := Except.ok.inj
    ((p.cell_read_preserved hPreserve hOldSource).symm.trans hSource)
  subst oldSource
  exact ⟨target, ceiling, degree,
    (p.initial_referenceAt_preserved hPreserve hMap source.row).trans hReference,
    hLow, hHigh, hPower, hTop⟩

/-- Cross-marker ceilings, including markers in different source columns,
are unchanged throughout the first block. No copied-column normality or
power-step certificate is required for these frozen-reference bounds. -/
theorem Preparation.initial_marker_reference_below_extended {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) {ambient : Mountain}
    (hPreserve : PreservesColumns p.reduced ambient) {references : List Ref}
    (hMap : p.boundaries.mapM (below p.reduced (p.reduced.size - 1)) = .ok references)
    {bucket nextBucket : Nat} {marker nextMarker : Ref} {source next : Cell}
    (hMarker : BucketMem p.marked bucket marker)
    (hSource : Canonical.cellAt ambient marker = .ok source)
    (hNextMarker : BucketMem p.marked nextBucket nextMarker)
    (hNext : Canonical.cellAt ambient nextMarker = .ok next)
    (hStrict : source.row < next.row) :
    ∃ target ceiling degree,
      referenceAt ambient references source.row = .ok target ∧
      source.row ≤ target ∧ target < ceiling ∧
      ceiling = Row.bump source.row degree ∧ ceiling ≤ next.row := by
  obtain ⟨oldSource, hOldSource, _⟩ := p.marker_cell_row_bound hMarker
  obtain ⟨oldNext, hOldNext, _⟩ := p.marker_cell_row_bound hNextMarker
  have hs : oldSource = source := Except.ok.inj
    ((p.cell_read_preserved hPreserve hOldSource).symm.trans hSource)
  have hn : oldNext = next := Except.ok.inj
    ((p.cell_read_preserved hPreserve hOldNext).symm.trans hNext)
  subst oldSource
  subst oldNext
  obtain ⟨target, ceiling, degree, hReference, hLow, hHigh, hPower, hCap⟩ :=
    p.initial_marker_reference_below hLast hMap hMarker hOldSource hNextMarker hOldNext hStrict
  exact ⟨target, ceiling, degree,
    (p.initial_referenceAt_preserved hPreserve hMap source.row).trans hReference,
    hLow, hHigh, hPower, hCap⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.Preparation.initial_referenceAt_zero_extended
#print axioms OmegaY.Expansion.Preparation.initial_marker_reference_below_extended
