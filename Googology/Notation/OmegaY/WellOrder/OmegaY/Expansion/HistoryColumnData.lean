/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/HistoryColumnData.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/HistoryColumnData.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.CopyRunHistory

set_option backward.do.legacy false

/-!
# Recovering usable prior-copy data from an actual block history

An earlier copied parent column comes with its real original ambient state,
copy execution and input-side power/support facts. The current reference
query is proved equal to that earlier query because both use the same fresh
block map. No copy certificate is recovered from row patterns alone.
-/

namespace OmegaY.Expansion

open Canonical

theorem DynamicBlockState.prior_column_data {front : List Nat} {last : Nat}
    {p : Preparation front last} {block : Nat} {start : Mountain} {references : List Ref}
    {next : Nat} {ambient : Mountain} (state : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    {sourceColumn : Nat} (hLower : p.root.column < sourceColumn) (hUpper : sourceColumn < next) :
    ∃ before column,
      ∃ d : ColumnCopyData before p.marked references sourceColumn
          (block * (p.reduced.size - 1 - p.root.column)) p.root.column,
        copyColumn before p.marked references sourceColumn
          (block * (p.reduced.size - 1 - p.root.column)) p.root.column = .ok column ∧
        PreservesColumns (before.push column) ambient ∧
        p.reduced[sourceColumn]? = some d.sources ∧
        NoPrematureOne d.sources ∧
        (∀ marker (hm : marker ∈ d.bucket), ColumnPowerSteps (d.marker_data marker hm).parentNodes) ∧
        (∀ marker (hm : marker ∈ d.bucket), ∃ (index : Nat) (cell : Cell),
          (d.marker_data marker hm).parentNodes[index]? = some cell ∧
            cell.row = (d.marker_data marker hm).current.row) ∧
        (∀ row, referenceAt before references row = referenceAt ambient references row) ∧
        ambient[sourceColumn + block * (p.reduced.size - 1 - p.root.column)]? = some column := by
  obtain ⟨before, column, oldState, hRun, hPreserve, hColumn⟩ :=
    CopyRunHistory.column_read history hLower hUpper
  have hSourceBound : sourceColumn < p.reduced.size := hUpper.trans_le state.next_upper
  obtain ⟨d, hNoPremature, hParentPower, hParentLow⟩ := oldState.column_data hLast hSourceBound
  have hSource : p.reduced[sourceColumn]? = some d.sources :=
    (oldState.base_ambient sourceColumn hSourceBound).symm.trans d.source_column
  refine ⟨before, column, d, hRun, hPreserve, hSource, hNoPremature,
    hParentPower, hParentLow, ?_, hColumn⟩
  intro row
  exact (oldState.referenceAt_preserved row).trans (state.referenceAt_preserved row).symm

#print axioms DynamicBlockState.prior_column_data

end OmegaY.Expansion
