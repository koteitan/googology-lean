/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/FillEndpoints.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/FillEndpoints.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.FillGeometry
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.PowerSteps

set_option backward.do.legacy false

/-!
# Reference-fill endpoints and positive parents

Adjacent power steps are a row-only condition, usable as a recursive copying
invariant. No canonical numerical-parent rule is assumed for a copied column.
-/

namespace OmegaY.Expansion

open Canonical

private theorem index_lt_of_row_lt {nodes : Column} (hstrict : FillRowsStrict nodes)
    {i j : Nat} {a b : Cell} (ha : nodes[i]? = some a) (hb : nodes[j]? = some b)
    (hrow : a.row < b.row) : i < j := by
  by_contra h
  rcases eq_or_lt_of_le (show j ≤ i by omega) with he | hl
  · subst i
    have hab : a = b := Option.some.inj (ha.symm.trans hb)
    exact (lt_irrefl _) (hab ▸ hrow)
  · exact (lt_asymm hrow) (hstrict _ _ _ _ hb ha hl)

/-- The last eligible parent is the immediate predecessor of the actual
high node. Its power-step ladder includes the high endpoint itself. -/
theorem fillCells_contains_high {nodes : Column} (hstrict : FillRowsStrict nodes)
    (hpower : ColumnPowerSteps nodes) {column lowIndex highIndex : Nat}
    {lowCell highCell : Cell}
    (hlow : nodes[lowIndex]? = some lowCell) (hhigh : nodes[highIndex]? = some highCell)
    (hrow : lowCell.row < highCell.row) :
    ∃ parentIndex parent, parentIndex + 1 = highIndex ∧ nodes[parentIndex]? = some parent ∧
      lowCell.row ≤ parent.row ∧
      (⟨highCell.row, 0, some ⟨column, parentIndex⟩⟩ : Cell) ∈
        fillCells nodes column lowCell.row highCell.row := by
  have hij := index_lt_of_row_lt hstrict hlow hhigh hrow
  obtain ⟨hhi, _⟩ := Array.getElem?_eq_some_iff.mp hhigh
  have hp : highIndex - 1 < nodes.size := by omega
  have hnext : highIndex - 1 + 1 = highIndex := by omega
  have hparent : nodes[highIndex - 1]? = some nodes[highIndex - 1] :=
    Array.getElem?_eq_getElem hp
  have hupper : nodes[highIndex - 1 + 1]? = some highCell := hnext ▸ hhigh
  have hlowParent : lowCell.row ≤ nodes[highIndex - 1].row := by
    rcases eq_or_lt_of_le (show lowIndex ≤ highIndex - 1 by omega) with he | hl
    · have heq : lowCell = nodes[highIndex - 1] :=
        Option.some.inj (hlow.symm.trans (he ▸ hparent))
      exact le_of_eq (congrArg Cell.row heq)
    · exact le_of_lt (hstrict _ _ _ _ hlow hparent hl)
  have hparentHigh : nodes[highIndex - 1].row < highCell.row :=
    hstrict _ _ _ _ hparent hhigh (by omega)
  have hstep := hpower _ _ _ hparent hupper
  have hendpoint : highCell.row ∈ Row.fillLadder nodes[highIndex - 1].row highCell.row := by
    rw [hstep]
    exact Row.fillLadder_contains_upper _ _
  refine ⟨highIndex - 1, nodes[highIndex - 1], hnext, hparent, hlowParent, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨highIndex - 1, List.mem_range.mpr hp, ?_⟩
  simp only [fillChunk, hparent, hupper, Option.getD_some,
    hlowParent, hparentHigh, and_self, ↓reduceIte]
  exact List.mem_map.mpr ⟨highCell.row, hendpoint, rfl⟩

/-- At a positive lower boundary every fill parent is a real, positive-value
node. This uses only validity of the already available parent column. -/
theorem fillCells_positive_parents {mountain : Mountain} {nodes : Column} {column : Nat}
    (hnodes : mountain[column]? = some nodes)
    (hvalid : Canonical.ColumnValid mountain column nodes)
    {capIndex : Nat} {cap : Cell} {low high : Row} {cell : Cell}
    (hcap : nodes[capIndex]? = some cap) (hhigh : high ≤ cap.row)
    (hlow : (1 : Row) ≤ low) (hcell : cell ∈ fillCells nodes column low high) :
    ∃ parentRef parent, cell.left = some parentRef ∧ lookup mountain parentRef = .ok parent ∧
      0 < parentRef.index ∧ 0 < parent.value := by
  obtain ⟨i, parent, upper, hp, _, hlo, _, _, _, _, _, hleft⟩ :=
    mem_fillCells (fillRowsStrict_of_columnValid hvalid) hcap hhigh hcell
  have hi : 0 < i := by
    by_contra h
    have he : i = 0 := by omega
    subst i
    have hphantom : parent = phantom := Option.some.inj (hp.symm.trans hvalid.phantom)
    have hzero : (1 : Row) ≤ 0 := by
      simpa only [hphantom, phantom] using hlow.trans hlo
    exact (not_le_of_gt Row.zero_lt_one) hzero
  exact ⟨⟨column, i⟩, parent, hleft, lookup_ok_iff.mpr ⟨nodes, hnodes, hp⟩,
    hi, hvalid.real_positive i parent hp hi⟩

/-- Full actual success with the high endpoint included. The exact output,
row uniqueness, bounds, and strict-left references are retained. -/
theorem fill_spec_with_high {mountain : Mountain} {source : Ref} {sourceCell : Cell}
    {sourceParent : Ref} {shift : Nat} {nodes : Column}
    {lowIndex highIndex : Nat} {lowCell highCell : Cell}
    (hsource : lookup mountain source = .ok sourceCell)
    (hleft : sourceCell.left = some sourceParent)
    (hnodes : mountain[sourceParent.column + shift]? = some nodes)
    (hvalid : Canonical.ColumnValid mountain (sourceParent.column + shift) nodes)
    (hpower : ColumnPowerSteps nodes)
    (hlow : nodes[lowIndex]? = some lowCell) (hhigh : nodes[highIndex]? = some highCell)
    (hrow : lowCell.row < highCell.row) (hleftward : sourceParent.column < source.column) :
    ∃ result, fill mountain source shift lowCell.row highCell.row = .ok result ∧
      result = fillCells nodes (sourceParent.column + shift) lowCell.row highCell.row ∧
      (result.map Cell.row).Nodup ∧ highCell.row ∈ result.map Cell.row ∧
      ∀ cell ∈ result, lowCell.row < cell.row ∧ cell.row ≤ highCell.row ∧ cell.value = 0 ∧
        ∃ parentRef parent, cell.left = some parentRef ∧ lookup mountain parentRef = .ok parent ∧
          parentRef.column < source.column + shift ∧ parent.row < cell.row := by
  obtain ⟨result, hfill, heq, hnodup, hcells⟩ :=
    fill_spec_of_valid_column hsource hleft hnodes hvalid hhigh hleftward
  refine ⟨result, hfill, heq, hnodup, ?_, hcells⟩
  obtain ⟨parentIndex, parent, _, _, _, hmem⟩ :=
    fillCells_contains_high (fillRowsStrict_of_columnValid hvalid) hpower hlow hhigh hrow
      (column := sourceParent.column + shift)
  rw [heq]
  exact List.mem_map.mpr ⟨_, hmem, rfl⟩

/-- The executable result has positive actual parents whenever `low ≥ 1`.
The cap may be any actual row at or above `high`. -/
theorem fill_with_positive_parents {mountain : Mountain} {source : Ref} {sourceCell : Cell}
    {sourceParent : Ref} {shift : Nat} {nodes : Column} {low high : Row}
    {capIndex : Nat} {cap : Cell}
    (hsource : lookup mountain source = .ok sourceCell)
    (hleft : sourceCell.left = some sourceParent)
    (hnodes : mountain[sourceParent.column + shift]? = some nodes)
    (hvalid : Canonical.ColumnValid mountain (sourceParent.column + shift) nodes)
    (hcap : nodes[capIndex]? = some cap) (hhigh : high ≤ cap.row)
    (hlow : (1 : Row) ≤ low) (hleftward : sourceParent.column < source.column) :
    ∃ result, fill mountain source shift low high = .ok result ∧
      ∀ cell ∈ result, ∃ parentRef parent,
        cell.left = some parentRef ∧ lookup mountain parentRef = .ok parent ∧
        0 < parentRef.index ∧ 0 < parent.value := by
  refine ⟨fillCells nodes (sourceParent.column + shift) low high,
    fill_eq_cells hsource hleft hnodes (fillRowsStrict_of_columnValid hvalid) hcap hhigh
      (Nat.add_lt_add_right hleftward shift), ?_⟩
  intro cell hcell
  exact fillCells_positive_parents hnodes hvalid hcap hhigh hlow hcell

end OmegaY.Expansion

#print axioms OmegaY.Expansion.fill_spec_with_high
#print axioms OmegaY.Expansion.fill_with_positive_parents
