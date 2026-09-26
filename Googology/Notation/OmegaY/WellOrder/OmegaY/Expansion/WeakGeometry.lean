/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/WeakGeometry.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/WeakGeometry.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.WeakTotality

set_option backward.do.legacy false

/-!
# Local geometry of weak descendants

Actual two-leg paths give upper-neighbor and parent closure.  The auxiliary
row-zero path is constructed from stored bottom left legs, rather than
postulated as marker reachability.
-/

namespace OmegaY.Expansion

open Canonical

theorem CellAt.unique {mountain : Mountain} {ref : Ref} {a b : Cell}
    (ha : CellAt mountain ref a) (hb : CellAt mountain ref b) : a = b := by
  exact Except.ok.inj ((lookup_ok_iff.mpr ha).symm.trans (lookup_ok_iff.mpr hb))

theorem TwoLeg.column_lt {mountain : Mountain} {parent current : Ref}
    (edge : TwoLeg mountain parent current) : parent.column < current.column :=
  weakParent_column_lt (weakParent_iff_twoLeg.mpr edge)

theorem ForwardWeakPath.column_le {mountain : Mountain} {root current : Ref}
    (path : ForwardWeakPath mountain root current) : root.column ≤ current.column :=
  (forwardWeakPath_iff.mp path).column_le

theorem ForwardWeakPath.eq_or_column_lt {mountain : Mountain} {root current : Ref}
    (path : ForwardWeakPath mountain root current) :
    current = root ∨ root.column < current.column := by
  cases path with
  | root => exact Or.inl rfl
  | step previous edge => exact Or.inr (lt_of_le_of_lt previous.column_le edge.column_lt)

theorem ForwardWeakPath.row_eq {mountain : Mountain} {root current : Ref}
    (path : ForwardWeakPath mountain root current) {rootCell currentCell : Cell}
    (hroot : CellAt mountain root rootCell) (hcurrent : CellAt mountain current currentCell) :
    currentCell.row = rootCell.row := by
  induction path generalizing currentCell with
  | root => rw [CellAt.unique hcurrent hroot]
  | step _ edge ih =>
    obtain ⟨column, cell, upper, parentCell, hc, hi, _, _, _, hp, heq⟩ := edge
    have he := CellAt.unique hcurrent ⟨column, hc, hi⟩
    rw [he, ← heq]
    exact ih hp

/-- Strict descendants, with the root itself excluded exactly by column order. -/
def WeakDescendant (mountain : Mountain) (root current : Ref) : Prop :=
  ForwardWeakPath mountain root current ∧ root.column < current.column

theorem WeakDescendant.last_edge {mountain : Mountain} {root current : Ref}
    (descendant : WeakDescendant mountain root current) :
    ∃ parent, ForwardWeakPath mountain root parent ∧ TwoLeg mountain parent current ∧
      (parent = root ∨ WeakDescendant mountain root parent) := by
  obtain ⟨path, hstrict⟩ := descendant
  cases path with
  | root => exact False.elim (Nat.lt_irrefl _ hstrict)
  | @step parent current previous edge =>
    refine ⟨parent, previous, edge, ?_⟩
    rcases previous.eq_or_column_lt with he | hl
    · exact Or.inl he
    · exact Or.inr ⟨previous, hl⟩

/-- A marker has an actual upper neighbor.  Its upper neighbor's stored left
endpoint is the root or an earlier marker, at exactly the marker's row. -/
theorem WeakDescendant.upper_parent {mountain : Mountain} {root current : Ref}
    (descendant : WeakDescendant mountain root current) :
    ∃ parent currentCell upper parentCell,
      CellAt mountain current currentCell ∧
      CellAt mountain ⟨current.column, current.index + 1⟩ upper ∧
      upper.left = some parent ∧ parent.column < current.column ∧
      CellAt mountain parent parentCell ∧ parentCell.row = currentCell.row ∧
      (parent = root ∨ WeakDescendant mountain root parent) := by
  obtain ⟨parent, _, edge, hparent⟩ := descendant.last_edge
  obtain ⟨column, cell, upper, parentCell, hc, hi, hu, hl, hlt, hp, heq⟩ := edge
  exact ⟨parent, cell, upper, parentCell, ⟨column, hc, hi⟩,
    ⟨column, hc, hu⟩, hl, hlt, hp, heq, hparent⟩

/-- The common row can also be read at the root, independently of values. -/
theorem WeakDescendant.upper_parent_at_root_row {mountain : Mountain} {root current : Ref}
    (descendant : WeakDescendant mountain root current) {rootCell : Cell}
    (hroot : CellAt mountain root rootCell) :
    ∃ parent currentCell upper parentCell,
      CellAt mountain current currentCell ∧
      CellAt mountain ⟨current.column, current.index + 1⟩ upper ∧
      upper.left = some parent ∧ parent.column < current.column ∧
      CellAt mountain parent parentCell ∧
      currentCell.row = rootCell.row ∧ parentCell.row = rootCell.row ∧
      (parent = root ∨ WeakDescendant mountain root parent) := by
  obtain ⟨parent, cell, upper, parentCell, hc, hu, hl, hlt, hp, heq, hparent⟩ :=
    descendant.upper_parent
  have hrow := descendant.1.row_eq hroot hc
  exact ⟨parent, cell, upper, parentCell, hc, hu, hl, hlt, hp, hrow,
    heq.trans hrow, hparent⟩

/-- Only concrete auxiliary/bottom cells and stored references are required.
No descendant or weak-search condition occurs in these premises. -/
structure PhantomChain (mountain : Mountain) : Prop where
  phantom_at : ∀ c, c < mountain.size → CellAt mountain ⟨c, 0⟩ phantom
  bottom_left : ∀ c, 0 < c → c < mountain.size →
    ∃ bottom, CellAt mountain ⟨c, 1⟩ bottom ∧ bottom.left = some ⟨c - 1, 0⟩

theorem PhantomChain.step {mountain : Mountain} (hchain : PhantomChain mountain)
    {c : Nat} (hpos : 0 < c) (hc : c < mountain.size) :
    TwoLeg mountain ⟨c - 1, 0⟩ ⟨c, 0⟩ := by
  obtain ⟨column, hcol, hphantom⟩ := hchain.phantom_at c hc
  obtain ⟨bottom, ⟨column', hcol', hbottom⟩, hleft⟩ := hchain.bottom_left c hpos hc
  have he : column' = column := Option.some.inj (hcol'.symm.trans hcol)
  subst column'
  exact ⟨column, phantom, bottom, phantom, hcol, hphantom, hbottom, hleft,
    by dsimp; omega, hchain.phantom_at (c - 1) (by omega), rfl⟩

/-- The actual bottom legs construct the complete row-zero chain. -/
theorem PhantomChain.reachable {mountain : Mountain} (hchain : PhantomChain mountain)
    {rootColumn currentColumn : Nat} (hle : rootColumn ≤ currentColumn)
    (hc : currentColumn < mountain.size) :
    ForwardWeakPath mountain ⟨rootColumn, 0⟩ ⟨currentColumn, 0⟩ := by
  induction currentColumn generalizing rootColumn with
  | zero =>
    have he : rootColumn = 0 := by omega
    subst rootColumn
    exact .root
  | succ c ih =>
    by_cases he : rootColumn = c + 1
    · subst rootColumn
      exact .root
    · have previous := ih (rootColumn := rootColumn) (by omega) (by omega)
      have edge := hchain.step (c := c + 1) (by omega) hc
      simpa only [Nat.add_sub_cancel] using ForwardWeakPath.step previous edge

theorem PhantomChain.descendant {mountain : Mountain} (hchain : PhantomChain mountain)
    {rootColumn currentColumn : Nat} (hlt : rootColumn < currentColumn)
    (hc : currentColumn < mountain.size) :
    WeakDescendant mountain ⟨rootColumn, 0⟩ ⟨currentColumn, 0⟩ :=
  ⟨hchain.reachable (Nat.le_of_lt hlt) hc, hlt⟩

/-- The executable predicate recognizes every auxiliary marker with its actual
column-derived allowance. This conclusion is not assumed in `PhantomChain`. -/
theorem PhantomChain.weakReaches {mountain : Mountain} (hchain : PhantomChain mountain)
    {rootColumn currentColumn : Nat} (hle : rootColumn ≤ currentColumn)
    (hc : currentColumn < mountain.size) :
    weakReaches mountain ⟨rootColumn, 0⟩ (currentColumn + 1) ⟨currentColumn, 0⟩ = .ok true :=
  (weakReaches_forward_iff (by dsimp; omega)).mpr (hchain.reachable hle hc)

/-- The standard frame hypotheses yield the concrete row-zero chain. -/
theorem phantomChain_of_ordered {mountain : Mountain}
    (hF : (Geometry.Frame.ofMountain mountain).Ordered)
    (hbottom : ∀ (c : Fin mountain.size)
      (h : 1 < (Geometry.Frame.ofMountain mountain).length c), 0 < c.val →
      ((Geometry.Frame.ofMountain mountain).cells c ⟨1, h⟩).left =
        some ⟨c.val - 1, 0⟩) : PhantomChain mountain := by
  constructor
  · intro c hc
    let col : Fin mountain.size := ⟨c, hc⟩
    have hn : 0 < (Geometry.Frame.ofMountain mountain).length col :=
      lt_of_lt_of_le (by decide : 0 < 2) (hF.length_ge_two col)
    let u : (Geometry.Frame.ofMountain mountain).Node := ⟨col, ⟨0, hn⟩⟩
    have hu := frame_ref_cellAt mountain u
    have hcell : (Geometry.Frame.ofMountain mountain).cell u = phantom := hF.phantom col hn
    rw [hcell] at hu
    exact hu
  · intro c hpos hc
    let col : Fin mountain.size := ⟨c, hc⟩
    have hn : 1 < (Geometry.Frame.ofMountain mountain).length col :=
      lt_of_lt_of_le (by decide : 1 < 2) (hF.length_ge_two col)
    let u : (Geometry.Frame.ofMountain mountain).Node := ⟨col, ⟨1, hn⟩⟩
    exact ⟨(Geometry.Frame.ofMountain mountain).cell u, frame_ref_cellAt mountain u,
      hbottom col hn hpos⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.WeakDescendant.upper_parent_at_root_row
#print axioms OmegaY.Expansion.PhantomChain.reachable
#print axioms OmegaY.Expansion.PhantomChain.weakReaches
#print axioms OmegaY.Expansion.phantomChain_of_ordered
