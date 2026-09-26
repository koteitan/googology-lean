/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/FillGeometry.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/FillGeometry.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.Fill
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.Invariant

set_option backward.do.legacy false

/-!
# Local geometry of actual reference filling

Different parent intervals produce disjoint rows. A real cap bounds every
inserted row, and every stored parent is an actual node strictly to the left.
The output list uses the executable order, not a subsequently sorted order.
-/

namespace OmegaY.Expansion

open Canonical

theorem fillChunk_rows (nodes : Column) (column : Nat) (low high : Row) (i : Nat) :
    (fillChunk nodes column low high i).map Cell.row =
      if low ≤ (nodes[i]?.getD phantom).row ∧ (nodes[i]?.getD phantom).row < high then
        Row.fillLadder (nodes[i]?.getD phantom).row (nodes[i + 1]?.getD phantom).row
      else [] := by
  unfold fillChunk
  split <;> simp_all [List.map_map, Function.comp_def]

theorem fillChunk_rows_nodup (nodes : Column) (column : Nat) (low high : Row) (i : Nat) :
    ((fillChunk nodes column low high i).map Cell.row).Nodup := by
  rw [fillChunk_rows]
  split
  · exact Row.fillLadder_nodup _ _
  · exact List.nodup_nil

/-- Membership exposes actual parent and upper-neighbor reads; the default
array values used in the list definition disappear from the result. -/
theorem mem_fillChunk {nodes : Column} (hstrict : FillRowsStrict nodes)
    {capIndex column i : Nat} {cap : Cell} {low high : Row} {cell : Cell}
    (hcap : nodes[capIndex]? = some cap) (hhigh : high ≤ cap.row)
    (hi : i < nodes.size) (hmem : cell ∈ fillChunk nodes column low high i) :
    ∃ parent upper, nodes[i]? = some parent ∧ nodes[i + 1]? = some upper ∧
      low ≤ parent.row ∧ parent.row < high ∧ parent.row < upper.row ∧
      upper.row ≤ cap.row ∧ cell.row ∈ Row.fillLadder parent.row upper.row ∧
      cell.value = 0 ∧ cell.left = some ⟨column, i⟩ := by
  have hread : nodes[i]? = some nodes[i] := Array.getElem?_eq_getElem hi
  simp only [fillChunk, hread, Option.getD_some] at hmem
  split at hmem
  next heligible =>
    obtain ⟨upper, hupper, hrow, hbound⟩ :=
      fill_successor hstrict hcap hhigh hread heligible.2
    rw [hupper] at hmem
    simp only [Option.getD_some] at hmem
    obtain ⟨row, hrowMem, rfl⟩ := List.mem_map.mp hmem
    exact ⟨nodes[i], upper, hread, hupper, heligible.1, heligible.2,
      hrow, hbound, hrowMem, rfl, rfl⟩
  next h => simp at hmem

theorem mem_fillCells {nodes : Column} (hstrict : FillRowsStrict nodes)
    {capIndex column : Nat} {cap : Cell} {low high : Row} {cell : Cell}
    (hcap : nodes[capIndex]? = some cap) (hhigh : high ≤ cap.row)
    (hmem : cell ∈ fillCells nodes column low high) :
    ∃ i parent upper, nodes[i]? = some parent ∧ nodes[i + 1]? = some upper ∧
      low ≤ parent.row ∧ parent.row < high ∧ parent.row < upper.row ∧
      upper.row ≤ cap.row ∧ cell.row ∈ Row.fillLadder parent.row upper.row ∧
      cell.value = 0 ∧ cell.left = some ⟨column, i⟩ := by
  obtain ⟨i, hi, hcell⟩ := List.mem_flatMap.mp hmem
  exact ⟨i, mem_fillChunk hstrict hcap hhigh (List.mem_range.mp hi) hcell⟩

theorem fillCells_row_bounds {nodes : Column} (hstrict : FillRowsStrict nodes)
    {capIndex column : Nat} {cap : Cell} {low high : Row} {cell : Cell}
    (hcap : nodes[capIndex]? = some cap) (hhigh : high ≤ cap.row)
    (hmem : cell ∈ fillCells nodes column low high) : low < cell.row ∧ cell.row ≤ cap.row := by
  obtain ⟨i, parent, upper, _, _, hlo, _, hpu, hcaprow, hrow, _, _⟩ :=
    mem_fillCells hstrict hcap hhigh hmem
  obtain ⟨hbottom, htop⟩ := Row.fillLadder_bounds hpu hrow
  exact ⟨lt_of_le_of_lt hlo hbottom, htop.trans hcaprow⟩

/-- Successive source intervals cannot produce a common output row. -/
theorem fillChunk_rows_disjoint {nodes : Column} (hstrict : FillRowsStrict nodes)
    {capIndex column i j : Nat} {cap : Cell} {low high : Row}
    (hcap : nodes[capIndex]? = some cap) (hhigh : high ≤ cap.row)
    (hi : i < nodes.size) (hj : j < nodes.size) (hij : i < j) :
    List.Disjoint ((fillChunk nodes column low high i).map Cell.row)
      ((fillChunk nodes column low high j).map Cell.row) := by
  apply List.disjoint_left.mpr
  intro row hri hrj
  obtain ⟨a, ha, harow⟩ := List.mem_map.mp hri
  obtain ⟨b, hb, hbrow⟩ := List.mem_map.mp hrj
  obtain ⟨pa, ua, hpa, hua, _, _, hpua, _, hla, _, _⟩ :=
    mem_fillChunk hstrict hcap hhigh hi ha
  obtain ⟨pb, ub, hpb, hub, _, _, hpub, _, hlb, _, _⟩ :=
    mem_fillChunk hstrict hcap hhigh hj hb
  have hmiddle : ua.row ≤ pb.row := by
    rcases eq_or_lt_of_le (show i + 1 ≤ j by omega) with he | hl
    · have heq : ua = pb := Option.some.inj (hua.symm.trans (he ▸ hpb))
      exact le_of_eq (congrArg Cell.row heq)
    · exact le_of_lt (hstrict _ _ _ _ hua hpb hl)
  have hab := Row.fillLadders_separated hpua hmiddle hpub hla hlb
  rw [harow, hbrow] at hab
  exact (lt_irrefl _) hab

theorem fillCells_rows_nodup {nodes : Column} (hstrict : FillRowsStrict nodes)
    {capIndex column : Nat} {cap : Cell} {low high : Row}
    (hcap : nodes[capIndex]? = some cap) (hhigh : high ≤ cap.row) :
    ((fillCells nodes column low high).map Cell.row).Nodup := by
  rw [fillCells, List.map_flatMap]
  apply List.nodup_flatMap.mpr
  refine ⟨fun i _ => fillChunk_rows_nodup _ _ _ _ _, ?_⟩
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij
  simp only [List.length_range, List.getElem_range] at hi hj ⊢
  exact fillChunk_rows_disjoint hstrict hcap hhigh hi hj hij

/-- Output references point at existing parents, independent of whether
numerical values have subsequently been filled in. -/
theorem fillCells_parent_valid {mountain : Mountain} {nodes : Column} {column dest : Nat}
    (hnodes : mountain[column]? = some nodes) (hstrict : FillRowsStrict nodes)
    {capIndex : Nat} {cap : Cell} {low high : Row} {cell : Cell}
    (hcap : nodes[capIndex]? = some cap) (hhigh : high ≤ cap.row)
    (hleft : column < dest) (hmem : cell ∈ fillCells nodes column low high) :
    cell.value = 0 ∧ ∃ parentRef parent, cell.left = some parentRef ∧
      lookup mountain parentRef = .ok parent ∧ parentRef.column < dest ∧ parent.row < cell.row := by
  obtain ⟨i, parent, upper, hp, _, _, _, hpu, _, hrow, hv, hl⟩ :=
    mem_fillCells hstrict hcap hhigh hmem
  exact ⟨hv, ⟨column, i⟩, parent, hl, lookup_ok_iff.mpr ⟨nodes, hnodes, hp⟩,
    hleft, (Row.fillLadder_bounds hpu hrow).1⟩

/-- A valid actual parent column supplies the strict-row hypothesis directly. -/
theorem fillRowsStrict_of_columnValid {mountain : Mountain} {column : Nat}
    {nodes : Column} (h : Canonical.ColumnValid mountain column nodes) : FillRowsStrict nodes :=
  h.rows_strict

/-- Executable filling succeeds with exact content, distinct rows, and valid
strict-left parent references. Its upper bound is the actual cap row. -/
theorem fill_spec {mountain : Mountain} {source : Ref} {sourceCell : Cell}
    {sourceParent : Ref} {shift : Nat} {nodes : Column} {low high : Row}
    {capIndex : Nat} {cap : Cell}
    (hsource : lookup mountain source = .ok sourceCell)
    (hleft : sourceCell.left = some sourceParent)
    (hnodes : mountain[sourceParent.column + shift]? = some nodes)
    (hstrict : FillRowsStrict nodes)
    (hcap : nodes[capIndex]? = some cap) (hhigh : high ≤ cap.row)
    (hleftward : sourceParent.column + shift < source.column + shift) :
    ∃ result, fill mountain source shift low high = .ok result ∧
      result = fillCells nodes (sourceParent.column + shift) low high ∧
      (result.map Cell.row).Nodup ∧
      ∀ cell ∈ result, low < cell.row ∧ cell.row ≤ cap.row ∧ cell.value = 0 ∧
        ∃ parentRef parent, cell.left = some parentRef ∧
          lookup mountain parentRef = .ok parent ∧
          parentRef.column < source.column + shift ∧ parent.row < cell.row := by
  refine ⟨fillCells nodes (sourceParent.column + shift) low high,
    fill_eq_cells hsource hleft hnodes hstrict hcap hhigh hleftward, rfl,
    fillCells_rows_nodup hstrict hcap hhigh, ?_⟩
  intro cell hcell
  obtain ⟨hlo, hhi⟩ := fillCells_row_bounds hstrict hcap hhigh hcell
  obtain ⟨hv, hp⟩ := fillCells_parent_valid hnodes hstrict hcap hhigh hleftward hcell
  exact ⟨hlo, hhi, hv, hp⟩

/-- In the paper's reference-gap case, `high` is a real node of the shifted
parent column, so the exact upper bound is `high` itself. -/
theorem fill_spec_of_valid_column {mountain : Mountain} {source : Ref} {sourceCell : Cell}
    {sourceParent : Ref} {shift : Nat} {nodes : Column} {low : Row}
    {highIndex : Nat} {highCell : Cell}
    (hsource : lookup mountain source = .ok sourceCell)
    (hleft : sourceCell.left = some sourceParent)
    (hnodes : mountain[sourceParent.column + shift]? = some nodes)
    (hvalid : Canonical.ColumnValid mountain (sourceParent.column + shift) nodes)
    (hhigh : nodes[highIndex]? = some highCell)
    (hleftward : sourceParent.column < source.column) :
    ∃ result, fill mountain source shift low highCell.row = .ok result ∧
      result = fillCells nodes (sourceParent.column + shift) low highCell.row ∧
      (result.map Cell.row).Nodup ∧
      ∀ cell ∈ result, low < cell.row ∧ cell.row ≤ highCell.row ∧ cell.value = 0 ∧
        ∃ parentRef parent, cell.left = some parentRef ∧
          lookup mountain parentRef = .ok parent ∧
          parentRef.column < source.column + shift ∧ parent.row < cell.row :=
  fill_spec hsource hleft hnodes (fillRowsStrict_of_columnValid hvalid) hhigh le_rfl
    (Nat.add_lt_add_right hleftward shift)

end OmegaY.Expansion

#print axioms OmegaY.Expansion.fillCells_rows_nodup
#print axioms OmegaY.Expansion.fillCells_parent_valid
#print axioms OmegaY.Expansion.fill_spec_of_valid_column
