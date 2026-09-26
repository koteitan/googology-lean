/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/PreparedReferenceAt.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/PreparedReferenceAt.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.PreparedBoundaries
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.MarkerOrder

set_option backward.do.legacy false

/-!
# Reference lookup for the first copied block

The actual prepared markers lie at or below the root row. The first selected
reference is at or above that row; every reference in the actual mapM output
is readable. These facts establish success of the real referenceAt loop on
the initial reduced mountain, before any copied column is appended.
-/

namespace OmegaY.Expansion

open Canonical Geometry

theorem MarkerSpec.row_le_root {mountain : Mountain}
    (hOrdered : (Frame.ofMountain mountain).Ordered)
    {root ref : Ref} {bucket : Nat} {rootCell cell : Cell}
    (hSpec : MarkerSpec mountain root bucket ref)
    (hRoot : CellAt mountain root rootCell) (hCell : CellAt mountain ref cell) :
    cell.row ≤ rootCell.row := by
  obtain ⟨_, _, _, index, hIndex, hPath⟩ := hSpec
  obtain ⟨prefixCell, hPrefixRead⟩ :=
    (show ValidRef mountain root from ⟨rootCell, hRoot⟩).lookup_below_index hIndex
  have hPrefix := lookup_ok_iff.mp hPrefixRead
  rw [hPath.row_eq hPrefix hCell]
  apply le_of_not_gt
  intro hRow
  have hImpossible := (cellAt_row_lt_iff hOrdered hRoot hPrefix rfl).mp hRow
  exact Nat.not_lt_of_ge hIndex hImpossible

theorem Preparation.marker_row_le_root {front : List Nat} {last : Nat}
    (p : Preparation front last) {bucket : Nat} {ref : Ref} {cell : Cell}
    (hMarker : BucketMem p.marked bucket ref)
    (hCell : Canonical.cellAt p.reduced ref = .ok cell) : cell.row ≤ p.rootCell.row := by
  have hRoot : CellAt p.reduced p.root p.rootCell := cellAt_ok_iff.mp p.restored_root
  have hSpec := markers_member_sound
    (weakLocal_of_ordered p.reduced_valid.toOrdered p.reduced_valid.left_sources)
    ⟨p.rootCell, hRoot⟩ p.markers_built hMarker
  exact hSpec.row_le_root p.reduced_valid.toOrdered hRoot (cellAt_ok_iff.mp hCell)

theorem Preparation.marker_cell_row_bound {front : List Nat} {last : Nat}
    (p : Preparation front last) {bucket : Nat} {ref : Ref}
    (hMarker : BucketMem p.marked bucket ref) :
    ∃ cell, Canonical.cellAt p.reduced ref = .ok cell ∧ cell.row ≤ p.rootCell.row := by
  have hRoot : CellAt p.reduced p.root p.rootCell := cellAt_ok_iff.mp p.restored_root
  have hSpec := markers_member_sound
    (weakLocal_of_ordered p.reduced_valid.toOrdered p.reduced_valid.left_sources)
    ⟨p.rootCell, hRoot⟩ p.markers_built hMarker
  obtain ⟨cell, hCell⟩ := hSpec.2.2.1
  have hRead := cellAt_ok_iff.mpr hCell
  exact ⟨cell, hRead, p.marker_row_le_root hMarker hRead⟩

/-- A successful actual mapM pairs every output with the corresponding
successful below call. No positivity or validity certificate is assumed. -/
theorem below_mapM_pairing {mountain : Mountain} {column : Nat}
    {boundaries : List Row} {references : List Ref}
    (hRun : boundaries.mapM (below mountain column) = .ok references) :
    List.Forall₂ (fun ceiling ref => below mountain column ceiling = .ok ref)
      boundaries references := by
  induction boundaries generalizing references with
  | nil =>
    have he : references = [] := by simpa using hRun.symm
    subst references
    exact .nil
  | cons ceiling rest ih =>
    cases hFirst : below mountain column ceiling with
    | error error => simp [List.mapM_cons, hFirst] at hRun
    | ok first =>
      cases hRest : rest.mapM (below mountain column) with
      | error error => simp [List.mapM_cons, hFirst, hRest] at hRun
      | ok tail =>
        have he : first :: tail = references := by
          simpa [List.mapM_cons, hFirst, hRest] using hRun
        subst references
        exact .cons hFirst (ih hRest)

theorem below_references_valid {mountain : Mountain} {column : Nat} {nodes : Column}
    (hColumn : mountain[column]? = some nodes)
    {boundaries : List Row} {references : List Ref}
    (hPaired : List.Forall₂
      (fun ceiling ref => below mountain column ceiling = .ok ref) boundaries references) :
    ∀ ref ∈ references, ValidRef mountain ref := by
  induction hPaired with
  | nil => simp
  | @cons ceiling ref boundaries references hBelow hPaired ih =>
    intro entry hEntry
    rcases List.mem_cons.mp hEntry with rfl | hEntry
    · exact below_validRef hColumn hBelow
    · exact ih entry hEntry

theorem below_mapM_head {mountain : Mountain} {column : Nat}
    {ceiling : Row} {boundaries : List Row} {references : List Ref}
    (hRun : (ceiling :: boundaries).mapM (below mountain column) = .ok references) :
    ∃ first tail, references = first :: tail ∧ below mountain column ceiling = .ok first := by
  have hPaired := below_mapM_pairing hRun
  cases hPaired with
  | cons hFirst hRest => exact ⟨_, _, rfl, hFirst⟩

/-- One readable reference above the requested row suffices; validity of all
other references ensures the actual loop cannot fail on a later read. -/
theorem referenceAt_from_floor {mountain : Mountain} {references : List Ref}
    (hValid : ∀ ref ∈ references, ValidRef mountain ref)
    {floor : Ref} {floorCell : Cell} {row : Row}
    (hMem : floor ∈ references)
    (hRead : Canonical.cellAt mountain floor = .ok floorCell)
    (hBound : row ≤ floorCell.row) :
    ∃ target, referenceAt mountain references row = .ok target ∧ row ≤ target := by
  obtain ⟨target, hTarget⟩ := (referenceAt_succeeds_iff hValid row).mpr
    ⟨floor, hMem, floorCell, lookup_ok_iff.mpr (cellAt_ok_iff.mp hRead), hBound⟩
  exact ⟨target, hTarget, referenceAt_lower_bound hValid hTarget⟩

theorem Preparation.initial_references_valid {front : List Nat} {last : Nat}
    (p : Preparation front last) {references : List Ref}
    (hRun : p.boundaries.mapM (below p.reduced (p.reduced.size - 1)) = .ok references) :
    ∀ ref ∈ references, ValidRef p.reduced ref :=
  below_references_valid (Array.getElem?_eq_getElem p.reduced_last_exists)
    (below_mapM_pairing hRun)

/-- The first reference in the actual output is a genuine cell between the
root row and the old final-top row. -/
theorem Preparation.initial_references_head_floor {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) {references : List Ref}
    (hRun : p.boundaries.mapM (below p.reduced (p.reduced.size - 1)) = .ok references) :
    ∃ first tail cell, references = first :: tail ∧
      Canonical.cellAt p.reduced first = .ok cell ∧
      p.rootCell.row ≤ cell.row ∧ cell.row < p.lastTop.row := by
  obtain ⟨first, tail, hList, hFirst⟩ := below_mapM_head hRun
  obtain ⟨found, cell, hFound, hCell, hRoot, hTop⟩ := p.initial_reference_floor hLast
  have he : found = first := Except.ok.inj (hFound.symm.trans hFirst)
  subst found
  exact ⟨first, tail, cell, hList, hCell, hRoot, hTop⟩

/-- Only the initial reduced mountain is covered. No success hypothesis is
made for referenceAt, nor any preservation claim for later copied blocks. -/
theorem Preparation.initial_referenceAt {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) {references : List Ref}
    (hRun : p.boundaries.mapM (below p.reduced (p.reduced.size - 1)) = .ok references)
    {bucket : Nat} {marker : Ref} {cell : Cell}
    (hMarker : BucketMem p.marked bucket marker)
    (hCell : Canonical.cellAt p.reduced marker = .ok cell) :
    ∃ target, referenceAt p.reduced references cell.row = .ok target ∧ cell.row ≤ target := by
  obtain ⟨first, tail, floorCell, hList, hFloor, hAbove, _⟩ :=
    p.initial_references_head_floor hLast hRun
  exact referenceAt_from_floor (p.initial_references_valid hRun)
    (by simp [hList]) hFloor ((p.marker_row_le_root hMarker hCell).trans hAbove)

/-- Both the marker read and its subsequent target selection succeed. -/
theorem Preparation.initial_marker_referenceAt {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) {references : List Ref}
    (hRun : p.boundaries.mapM (below p.reduced (p.reduced.size - 1)) = .ok references)
    {bucket : Nat} {marker : Ref} (hMarker : BucketMem p.marked bucket marker) :
    ∃ cell target, Canonical.cellAt p.reduced marker = .ok cell ∧
      referenceAt p.reduced references cell.row = .ok target ∧ cell.row ≤ target := by
  obtain ⟨cell, hCell, _⟩ := p.marker_cell_row_bound hMarker
  obtain ⟨target, hTarget, hBound⟩ := p.initial_referenceAt hLast hRun hMarker hCell
  exact ⟨cell, target, hCell, hTarget, hBound⟩

theorem Preparation.initial_references_and_targets {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) :
    ∃ references,
      p.boundaries.mapM (below p.reduced (p.reduced.size - 1)) = .ok references ∧
      (∀ ref ∈ references, ValidRef p.reduced ref) ∧
      ∀ bucket marker cell, BucketMem p.marked bucket marker →
        Canonical.cellAt p.reduced marker = .ok cell →
        ∃ target, referenceAt p.reduced references cell.row = .ok target ∧ cell.row ≤ target := by
  obtain ⟨references, hRun, _⟩ := p.initial_references hLast
  exact ⟨references, hRun, p.initial_references_valid hRun,
    fun _ _ _ hMarker hCell => p.initial_referenceAt hLast hRun hMarker hCell⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.Preparation.marker_row_le_root
#print axioms OmegaY.Expansion.below_mapM_pairing
#print axioms OmegaY.Expansion.Preparation.initial_referenceAt
#print axioms OmegaY.Expansion.Preparation.initial_references_and_targets
