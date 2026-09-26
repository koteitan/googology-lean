/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ReducedRootSupport.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/ReducedRootSupport.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.RootGeometry
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.DecrementRows

set_option backward.do.legacy false

/-!
# Root rows in the actual decremented boundary column

The old P-support witnesses lie strictly below the old last top. Exact
decrement synchronization retains each such cell at its original index.
Thus the needed root-row support holds in the actual reduced build, not just
in the original mountain. The auxiliary zero row is handled separately.
-/

namespace OmegaY.Expansion

open Canonical Geometry

private theorem index_lt_of_same_column_height {F : Frame} (hF : F.Ordered)
    {v top : F.Node} (hc : v.1 = top.1) (hh : F.height v < F.height top) :
    v.2.val < top.2.val := by
  cases v with
  | mk c i =>
    dsimp only at hc
    subst c
    by_contra hn
    have hi : top.2 ≤ i := Nat.le_of_not_gt hn
    exact not_lt_of_ge ((hF.rows_strict top.1).monotone hi) hh

/-- A strict old last-top height bound places the node before the actual
last array index, rather than merely below an unattained ordinal bound. -/
theorem Preparation.initial_below_top_index {front : List Nat} {last : Nat}
    (p : Preparation front last) (hlast : 1 < last)
    (v : (Frame.ofMountain p.initial).Node) (hvColumn : v.1.val = front.length)
    (hvRow : (Frame.ofMountain p.initial).height v < p.lastTop.row) :
    v.2.val + 1 < (Frame.ofMountain p.initial).length v.1 := by
  obtain ⟨g⟩ := p.root_geometry hlast
  have hc : v.1 = g.topNode.1 := Fin.ext (hvColumn.trans g.top_column.symm)
  have hTopRow : (Frame.ofMountain p.initial).height g.topNode = p.lastTop.row :=
    congrArg Cell.row g.top_cell
  have hIndex := index_lt_of_same_column_height p.initial_valid.toOrdered hc
    (hvRow.trans_eq hTopRow.symm)
  have hLength : (Frame.ofMountain p.initial).length v.1 = g.topNode.2.val + 1 := by
    exact (congrArg (Frame.ofMountain p.initial).length hc).trans g.top_last.symm
  omega

/-- An actual old final-column cell below the top is read at the same Ref
after decrement, with exactly its old row and leg and one subtracted value. -/
theorem Preparation.reduced_below_top_cell {front : List Nat} {last : Nat}
    (p : Preparation front last) (hlast : 1 < last)
    (v : (Frame.ofMountain p.initial).Node) (hvColumn : v.1.val = front.length)
    (hvRow : (Frame.ofMountain p.initial).height v < p.lastTop.row) :
    cellAt p.reduced (Frame.ref v) = .ok (decCell ((Frame.ofMountain p.initial).cell v)) := by
  have hColumn : p.initial[front.length]? = some p.initial[v.1.val] := by
    rw [← hvColumn]
    exact Array.getElem?_eq_getElem v.1.isLt
  have hCell : p.initial[v.1.val][v.2.val]? = some ((Frame.ofMountain p.initial).cell v) :=
    Array.getElem?_eq_getElem v.2.isLt
  have hRead := build_decrement_prefix_cell p.initial_build p.reduced_build hlast hColumn
    (p.initial_below_top_index hlast v hvColumn hvRow) hCell
  have hRef : Frame.ref v = ⟨front.length, v.2.val⟩ := by
    simp only [Frame.ref, Ref.mk.injEq]
    exact ⟨hvColumn, True.intro⟩
  simpa only [hRef] using hRead

/-- The stronger version keeps the old witness, its exact reference, and the
complete decremented cell read in the new mountain. -/
theorem Preparation.reduced_root_cell_support {front : List Nat} {last : Nat}
    (p : Preparation front last) (hlast : 1 < last)
    (w : (Frame.ofMountain p.initial).Node) (hwReal : Frame.Real w)
    (hwColumn : w.1.val = p.root.column)
    (hwRow : (Frame.ofMountain p.initial).height w ≤ p.rootCell.row) :
    ∃ (oldV : (Frame.ofMountain p.initial).Node) (newV : (Frame.ofMountain p.reduced).Node),
      Frame.Real oldV ∧ oldV.1.val = front.length ∧
      (Frame.ofMountain p.initial).height oldV < p.lastTop.row ∧
      (Frame.ofMountain p.initial).height oldV = (Frame.ofMountain p.initial).height w ∧
      Frame.ref newV = Frame.ref oldV ∧
      (Frame.ofMountain p.reduced).cell newV = decCell ((Frame.ofMountain p.initial).cell oldV) ∧
      Frame.Real newV := by
  obtain ⟨oldV, hReal, hColumn, hBelow, hRow⟩ := p.root_row_support hlast w hwReal hwColumn hwRow
  obtain ⟨newV, hRef, hCell⟩ := Canonical.frame_node_of_cellAt
    (p.reduced_below_top_cell hlast oldV hColumn hBelow)
  have hIndex : newV.2.val = oldV.2.val := congrArg Ref.index hRef
  exact ⟨oldV, newV, hReal, hColumn, hBelow, hRow, hRef, hCell, by
    unfold Frame.Real
    rw [hIndex]
    exact hReal⟩

/-- Every real root-prefix row is present in the actual initial reduced
boundary column. No support condition on that new column is assumed. -/
theorem Preparation.reduced_root_row_support {front : List Nat} {last : Nat}
    (p : Preparation front last) (hlast : 1 < last)
    (w : (Frame.ofMountain p.initial).Node) (hwReal : Frame.Real w)
    (hwColumn : w.1.val = p.root.column)
    (hwRow : (Frame.ofMountain p.initial).height w ≤ p.rootCell.row) :
    ∃ v : (Frame.ofMountain p.reduced).Node,
      Frame.Real v ∧ v.1.val = front.length ∧
      (Frame.ofMountain p.reduced).height v = (Frame.ofMountain p.initial).height w := by
  obtain ⟨oldV, newV, _, hColumn, _, hRow, hRef, hCell, hReal⟩ :=
    p.reduced_root_cell_support hlast w hwReal hwColumn hwRow
  have hNewColumn : newV.1.val = oldV.1.val := congrArg Ref.column hRef
  have hNewRow : (Frame.ofMountain p.reduced).height newV =
      (Frame.ofMountain p.initial).height oldV := by
    simpa only [decCell_row, Frame.height] using congrArg Cell.row hCell
  exact ⟨newV, hReal, hNewColumn.trans hColumn, hNewRow.trans hRow⟩

/-- The auxiliary zero row is an actual phantom read in the reduced last
column. It is deliberately not asserted to be a real node. -/
theorem Preparation.reduced_last_phantom_read {front : List Nat} {last : Nat}
    (p : Preparation front last) : cellAt p.reduced ⟨front.length, 0⟩ = .ok phantom := by
  have hSize := build_size p.reduced_build
  have hc : front.length < p.reduced.size := by
    simp only [List.length_append, List.length_singleton] at hSize
    omega
  exact cellAt_ok_iff.mpr ⟨p.reduced[front.length], Array.getElem?_eq_getElem hc,
    (p.reduced_valid front.length hc).phantom⟩

theorem Preparation.reduced_last_zero_row {front : List Nat} {last : Nat}
    (p : Preparation front last) :
    ∃ v : (Frame.ofMountain p.reduced).Node,
      v.1.val = front.length ∧ v.2.val = 0 ∧ (Frame.ofMountain p.reduced).height v = 0 := by
  obtain ⟨v, hRef, hCell⟩ := Canonical.frame_node_of_cellAt p.reduced_last_phantom_read
  exact ⟨v, congrArg Ref.column hRef, congrArg Ref.index hRef, congrArg Cell.row hCell⟩

#print axioms Preparation.reduced_below_top_cell
#print axioms Preparation.reduced_root_row_support
#print axioms Preparation.reduced_last_zero_row

end OmegaY.Expansion
