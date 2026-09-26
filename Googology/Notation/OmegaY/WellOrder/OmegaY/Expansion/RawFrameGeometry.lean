/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/RawFrameGeometry.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/RawFrameGeometry.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.RawForest
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.RawRowCases

set_option backward.do.legacy false

/-!
# Stored-edge row geometry of actual array mountains

The array certificate records actual reads and ordinal row equations, without
asserting that the stored edge is the numerical first-smaller parent. It is
preserved when complete later columns are appended. The typed bridge uses the
actual vertical successor and `Frame.rawParent`, not `Frame.P`.

The row certificate alone permits a phantom parent. Real-parent positivity is
supplied separately by the already proved backfill sums.
-/

namespace OmegaY.Expansion

open Canonical Geometry

/-- Actual stored edges on the real adjacent pairs of one column. -/
def ColumnRawGeometry (mountain : Mountain) (c : Nat) (column : Column) : Prop :=
  ∀ index lower upper, column[index]? = some lower →
    column[index + 1]? = some upper → 0 < index →
    ∃ parentRef parent, upper.left = some parentRef ∧
      Canonical.cellAt mountain parentRef = .ok parent ∧ parentRef.column < c ∧
      parent.row ≤ lower.row ∧ upper.row = Row.B lower.row parent.row

def MountainRawGeometry (mountain : Mountain) : Prop :=
  ∀ c (hc : c < mountain.size), ColumnRawGeometry mountain c mountain[c]

theorem ColumnRawGeometry.transport {before after : Mountain} {c : Nat} {column : Column}
    (h : ColumnRawGeometry before c column)
    (hRead : ∀ ref, ref.column < c →
      Canonical.cellAt before ref = Canonical.cellAt after ref) :
    ColumnRawGeometry after c column := by
  intro index lower upper hLower hUpper hReal
  obtain ⟨ref, parent, hLeft, hParent, hColumn, hRow, hB⟩ :=
    h index lower upper hLower hUpper hReal
  exact ⟨ref, parent, hLeft, (hRead ref hColumn).symm.trans hParent,
    hColumn, hRow, hB⟩

theorem columnRawGeometry_iff_copiedRawAt {mountain : Mountain} {column : Column} :
    ColumnRawGeometry (mountain.push column) mountain.size column ↔
      ∀ index lower upper, column[index]? = some lower →
        column[index + 1]? = some upper → 0 < index →
        CopiedRawAt mountain column lower upper := Iff.rfl

/-- An appended column does not change any old stored-edge lookup. -/
theorem MountainRawGeometry.push {mountain : Mountain} {column : Column}
    (hMountain : MountainRawGeometry mountain)
    (hColumn : ∀ index lower upper, column[index]? = some lower →
      column[index + 1]? = some upper → 0 < index →
      CopiedRawAt mountain column lower upper) :
    MountainRawGeometry (mountain.push column) := by
  intro c hc
  by_cases he : c = mountain.size
  · subst c
    simpa only [Array.getElem_push_eq] using
      (columnRawGeometry_iff_copiedRawAt.mpr hColumn)
  · have hOld : c < mountain.size := by simp only [Array.size_push] at hc; omega
    rw [Array.getElem_push_lt hOld]
    exact (hMountain c hOld).transport
      (fun ref hr => (cellAt_push_left (hr.trans hOld)).symm)

/-- Restricting to complete initial columns retains every referenced parent,
since every raw edge is strictly leftward. -/
theorem MountainRawGeometry.prefix {before after : Mountain}
    (h : MountainRawGeometry after) (hPrefix : PreservesColumns before after) :
    MountainRawGeometry before := by
  intro c hc
  have hcAfter : c < after.size := hc.trans_le hPrefix.size_le
  have hColumn : after[c] = before[c] := Option.some.inj
    ((Array.getElem?_eq_getElem hcAfter).symm.trans
      ((hPrefix c hc).trans (Array.getElem?_eq_getElem hc)))
  rw [← hColumn]
  apply (h c hcAfter).transport
  intro ref hr
  exact cellAt_eq_of_column_eq (hPrefix ref.column (hr.trans hc))

theorem MountainRawGeometry.pop {mountain : Mountain}
    (h : MountainRawGeometry mountain) : MountainRawGeometry mountain.pop := by
  apply h.prefix
  intro c hc
  have hBeforeCut : c < mountain.size - 1 := by simpa only [Array.size_pop] using hc
  simp only [Array.getElem?_pop, hBeforeCut, ↓reduceIte]

end OmegaY.Expansion

namespace OmegaY.Geometry.Frame

/-- The ordinal row law for actual upper-stored parents. No numerical search
or real-parent assertion is part of this geometric predicate. -/
def RawRowGeometry (F : Frame) : Prop :=
  ∀ u upper, Real u → F.upper u = some upper →
    ∃ parent, F.rawParent u = some parent ∧ parent.1.val < u.1.val ∧
      F.height parent ≤ F.height u ∧
      F.height upper = Row.B (F.height u) (F.height parent)

theorem Normal.rawRowGeometry {F : Frame} (h : F.Normal) : F.RawRowGeometry := by
  intro u upper hReal hUpper
  obtain ⟨parent, hParent, hB, _, hLeft⟩ := h.upper_step u upper hReal hUpper
  exact ⟨parent, rawParent_eq_of_upper_left hUpper hLeft,
    P_column_lt h.toOrdered hParent, P_height_le h.toOrdered hParent, hB⟩

end OmegaY.Geometry.Frame

namespace OmegaY.Expansion

open Canonical Geometry

/-- A successful actual parent-cell read and the actual upper stored reference
produce a typed raw edge. The parent may be phantom; no numerical search is
asserted. The leftward bound is obtained from `MountainValid`. -/
theorem rawParent_geometry_of_reads {mountain : Mountain}
    (hValid : MountainValid mountain)
    {u upper : (Frame.ofMountain mountain).Node} {parentRef : Ref} {parent : Cell}
    (hUpper : (Frame.ofMountain mountain).upper u = some upper)
    (hLeft : ((Frame.ofMountain mountain).cell upper).left = some parentRef)
    (hRead : Canonical.cellAt mountain parentRef = .ok parent)
    (hRow : parent.row ≤ (Frame.ofMountain mountain).height u)
    (hB : (Frame.ofMountain mountain).height upper =
      Row.B ((Frame.ofMountain mountain).height u) parent.row) :
    ∃ p, Frame.ref p = parentRef ∧ (Frame.ofMountain mountain).cell p = parent ∧
      (Frame.ofMountain mountain).rawParent u = some p ∧ p.1.val < u.1.val ∧
      (Frame.ofMountain mountain).height p ≤ (Frame.ofMountain mountain).height u ∧
      (Frame.ofMountain mountain).height upper =
        Row.B ((Frame.ofMountain mountain).height u) ((Frame.ofMountain mountain).height p) := by
  obtain ⟨p, hRef, hCell⟩ := Canonical.frame_node_of_cellAt hRead
  have hRaw : (Frame.ofMountain mountain).rawParent u = some p := by
    apply Frame.rawParent_eq_of_upper_left hUpper
    simpa only [hRef] using hLeft
  exact ⟨p, hRef, hCell, hRaw, Frame.rawParent_column_lt hValid.toOrdered hRaw,
    by simpa only [Frame.height, hCell] using hRow,
    by simpa only [Frame.height, hCell] using hB⟩

theorem MountainRawGeometry.rawRowGeometry {mountain : Mountain}
    (h : MountainRawGeometry mountain) : (Frame.ofMountain mountain).RawRowGeometry := by
  intro u upper hReal hUpper
  rcases u with ⟨c, i⟩
  unfold Frame.upper at hUpper
  split at hUpper
  · obtain rfl := Option.some.inj hUpper
    rename_i hNext
    obtain ⟨ref, parent, hLeft, hRead, hColumn, hRow, hB⟩ :=
      h c.val c.isLt i.val _ _ (Array.getElem?_eq_getElem i.isLt)
        (Array.getElem?_eq_getElem hNext) hReal
    obtain ⟨p, hRef, hCell⟩ := Canonical.frame_node_of_cellAt hRead
    refine ⟨p, ?_, ?_, ?_, ?_⟩
    · apply Frame.rawParent_eq_of_upper_left
        (upper := ⟨c, ⟨i.val + 1, hNext⟩⟩)
      · simp [Frame.upper, hNext]
      · rw [hRef]
        exact hLeft
    · simpa only [← hRef, Frame.ref] using hColumn
    · simp only [Frame.height]
      rw [hCell]
      exact hRow
    · simp only [Frame.height]
      rw [hCell]
      exact hB
  · cases hUpper

theorem mountainRawGeometry_of_rawRowGeometry {mountain : Mountain}
    (h : (Frame.ofMountain mountain).RawRowGeometry) : MountainRawGeometry mountain := by
  intro c hc index lower upper hLower hUpper hReal
  obtain ⟨hi, hLowerEq⟩ := Array.getElem?_eq_some_iff.mp hLower
  obtain ⟨hj, hUpperEq⟩ := Array.getElem?_eq_some_iff.mp hUpper
  let u : (Frame.ofMountain mountain).Node := ⟨⟨c, hc⟩, ⟨index, hi⟩⟩
  let v : (Frame.ofMountain mountain).Node := ⟨⟨c, hc⟩, ⟨index + 1, hj⟩⟩
  have hUV : (Frame.ofMountain mountain).upper u = some v := by
    simp [Frame.upper, u, v, Frame.ofMountain, hj]
  obtain ⟨parent, hParent, hColumn, hRow, hB⟩ := h u v hReal hUV
  obtain ⟨actualUpper, hActualUpper, hLeft⟩ := Frame.rawParent_spec hParent
  have hEq : actualUpper = v := Option.some.inj (hActualUpper.symm.trans hUV)
  subst actualUpper
  have hUCell : (Frame.ofMountain mountain).cell u = lower := hLowerEq
  have hVCell : (Frame.ofMountain mountain).cell v = upper := hUpperEq
  refine ⟨Frame.ref parent, (Frame.ofMountain mountain).cell parent, ?_,
    Canonical.cellAt_of_frame_node mountain parent, hColumn, ?_, ?_⟩
  · simpa only [hVCell] using hLeft
  · simpa only [Frame.height, hUCell] using hRow
  · simpa only [Frame.height, hUCell, hVCell] using hB

theorem mountainRawGeometry_iff_rawRowGeometry {mountain : Mountain} :
    MountainRawGeometry mountain ↔ (Frame.ofMountain mountain).RawRowGeometry :=
  ⟨MountainRawGeometry.rawRowGeometry, mountainRawGeometry_of_rawRowGeometry⟩

theorem mountainRawGeometry_of_normal {mountain : Mountain}
    (hNormal : (Frame.ofMountain mountain).Normal) : MountainRawGeometry mountain :=
  mountainRawGeometry_of_rawRowGeometry hNormal.rawRowGeometry

/-- Backfill sums, separately from the raw row law, make the raw parent real.
This still does not identify it with a numerical first-smaller parent. -/
theorem MountainRawGeometry.real_raw_parent {mountain : Mountain}
    (h : MountainRawGeometry mountain) (hValid : MountainValid mountain)
    (hSums : MountainSums mountain)
    {u upper : (Frame.ofMountain mountain).Node} (hReal : Frame.Real u)
    (hUpper : (Frame.ofMountain mountain).upper u = some upper) :
    ∃ parent, (Frame.ofMountain mountain).rawParent u = some parent ∧
      Frame.Real parent ∧ parent.1.val < u.1.val ∧
      (Frame.ofMountain mountain).height parent ≤ (Frame.ofMountain mountain).height u ∧
      (Frame.ofMountain mountain).height upper =
        Row.B ((Frame.ofMountain mountain).height u) ((Frame.ofMountain mountain).height parent) ∧
      (Frame.ofMountain mountain).value parent < (Frame.ofMountain mountain).value u := by
  obtain ⟨parent, hParent, hColumn, hRow, hB⟩ := h.rawRowGeometry u upper hReal hUpper
  obtain ⟨hParentReal, hValue⟩ := hSums.rawParent_value_lt hValid hReal hParent
  exact ⟨parent, hParent, hParentReal, hColumn, hRow, hB, hValue⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.MountainRawGeometry.push
#print axioms OmegaY.Expansion.MountainRawGeometry.prefix
#print axioms OmegaY.Expansion.MountainRawGeometry.pop
#print axioms OmegaY.Expansion.rawParent_geometry_of_reads
#print axioms OmegaY.Expansion.MountainRawGeometry.rawRowGeometry
#print axioms OmegaY.Expansion.mountainRawGeometry_iff_rawRowGeometry
#print axioms OmegaY.Expansion.mountainRawGeometry_of_normal
#print axioms OmegaY.Expansion.MountainRawGeometry.real_raw_parent
