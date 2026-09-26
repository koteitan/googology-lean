/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Canonical/Reconstruction.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Canonical/Reconstruction.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.GraftTransfer
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.BottomLegs
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.BuildSplit
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.TruncateValues

set_option backward.do.legacy false

/-! Reconstruction from local certificates. The input diagram is arbitrary:
its successful canonical build is a conclusion, never an assumption.
Normality determines its genuine difference steps, while BottomLegs fixes
the otherwise independent initial stored references at row one. -/

namespace OmegaY.Canonical

open Geometry

private theorem reconstruction_cell_eq {a b : Cell}
    (hRow : a.row = b.row) (hValue : a.value = b.value) (hLeft : a.left = b.left) : a = b := by
  cases a
  cases b
  simp_all

private theorem reconstruction_first_two {α : Type} {xs : List α} {a b : α}
    (hZero : xs[0]? = some a) (hOne : xs[1]? = some b) :
    ∃ rest, xs = a :: b :: rest := by
  cases xs with
  | nil => simp at hZero
  | cons first rest =>
    have he : first = a := by simpa using hZero
    subst first
    cases rest with
    | nil => simp at hOne
    | cons second tail =>
      have he : second = b := by simpa using hOne
      subst second
      exact ⟨tail, rfl⟩

/-- Rebuilding a source column over its exact strict left prefix recovers
all its rows, values, and stored references. The source is supplied by local
certificates and need not be assumed to have been built previously. -/
theorem buildColumn_reconstruct {mountain left : Mountain}
    (hValid : MountainValid mountain) (hNormal : (Frame.ofMountain mountain).Normal)
    (hLegs : BottomLegs mountain) {c : Nat} {sources : Column}
    (hSources : mountain[c]? = some sources) (hLeftSize : left.size = c)
    (hPrefix : ∀ index, index < c → mountain[index]? = left[index]?) :
    buildColumn left (sources[1]?.getD phantom).value = .ok sources := by
  obtain ⟨hc, hSourcesEq⟩ := Array.getElem?_eq_some_iff.mp hSources
  have hSourceValid : ColumnValid mountain c sources := hSourcesEq ▸ hValid c hc
  obtain ⟨bottom, hBottom, hBottomLeft⟩ := hLegs c hc
  have hBottomRead : sources[1]? = some bottom := by simpa only [hSourcesEq] using hBottom
  have hBottomRow : bottom.row = 1 := hSourceValid.bottom_row bottom hBottomRead
  have hBottomPositive : 0 < bottom.value := hSourceValid.real_positive 1 bottom hBottomRead (by omega)
  have hInitialBottom : initialBottom c bottom.value = bottom :=
    reconstruction_cell_eq hBottomRow.symm rfl hBottomLeft.symm
  have hInitial : initialColumn left.size bottom.value = #[phantom, bottom] := by
    change #[phantom, initialBottom left.size bottom.value] = _
    rw [hLeftSize, hInitialBottom]
  obtain ⟨tail, hList⟩ := reconstruction_first_two
    (show sources.toList[0]? = some phantom by
      simpa only [Array.getElem?_toList] using hSourceValid.phantom)
    (show sources.toList[1]? = some bottom by
      simpa only [Array.getElem?_toList] using hBottomRead)
  have hTake : (initialColumn left.size bottom.value).toList = sources.toList.take 2 := by
    rw [hInitial, hList]
    rfl
  have hRead : cellAt mountain ⟨c, 1⟩ = .ok bottom :=
    cellAt_ok_iff.mpr ⟨sources, hSources, hBottomRead⟩
  obtain ⟨u, hRef, hCell⟩ := frame_node_of_cellAt hRead
  have hUColumn : u.1.val = c := congrArg Ref.column hRef
  have hUIndex : u.2.val = 1 := congrArg Ref.index hRef
  have hReal : Frame.Real u := by unfold Frame.Real; omega
  have hTop : (initialColumn left.size bottom.value).back? = some ((Frame.ofMountain mountain).cell u) := by
    rw [hInitial, hCell]
    rfl
  have hRight : u.1.val ≤ left.size := by omega
  have hColumns : ∀ index, index < u.1.val → mountain[index]? = left[index]? := by
    intro index hi
    exact hPrefix index (by simpa only [hUColumn] using hi)
  have hValue : (Frame.ofMountain mountain).value u = bottom.value := congrArg Cell.value hCell
  obtain ⟨result, hGrow, hResultList, _hTopOne⟩ :=
    growColumn_graft_transfer hNormal hReal hTop hRight hColumns
      (fuel := bottom.value - 1) (by rw [hValue])
  have hSuffix : upperSuffix mountain u = sources.toList.drop 2 := by
    simp only [upperSuffix, hUColumn, hUIndex, hSourcesEq]
  rw [hTake, hSuffix, List.take_append_drop] at hResultList
  have hResultEq : result = sources := Array.ext' hResultList
  rw [hResultEq] at hGrow
  simp only [hBottomRead, Option.getD_some, buildColumn, Nat.ne_of_gt hBottomPositive, ↓reduceIte]
  exact hGrow

/-- Reconstruct the remaining actual columns after an already identical
left prefix. The recursion follows the finite column list, with no successful
whole-build assumption or alternative construction algorithm. -/
theorem buildFrom_reconstruct_suffix {mountain left : Mountain}
    (hValid : MountainValid mountain) (hNormal : (Frame.ofMountain mountain).Normal)
    (hLegs : BottomLegs mountain) (remaining : List Column)
    (hSplit : mountain.toList = left.toList ++ remaining) :
    buildFrom left (remaining.map (fun column => (column[1]?.getD phantom).value)) = .ok mountain := by
  induction remaining generalizing left with
  | nil =>
    have he : left = mountain := Array.ext' (by simpa only [List.append_nil] using hSplit.symm)
    subst left
    rfl
  | cons column rest ih =>
    have hColumn : mountain[left.size]? = some column := by
      have hListRead : mountain.toList[left.size]? = some column := by
        rw [hSplit, List.getElem?_append_right (by simp)]
        simp
      simpa only [Array.getElem?_toList] using hListRead
    have hPrefix : ∀ index, index < left.size → mountain[index]? = left[index]? := by
      intro index hIndex
      have hListRead : mountain.toList[index]? = left.toList[index]? := by
        rw [hSplit, List.getElem?_append_left (by simpa using hIndex)]
      simpa only [Array.getElem?_toList] using hListRead
    have hColumnBuild := buildColumn_reconstruct hValid hNormal hLegs hColumn rfl hPrefix
    have hNextSplit : mountain.toList = (left.push column).toList ++ rest := by
      simpa only [Array.toList_push, List.append_assoc, List.singleton_append] using hSplit
    simp only [List.map_cons, buildFrom, hColumnBuild, except_bind_ok]
    exact ih hNextSplit

/-- The actual unvalidated builder reproduces the complete supplied diagram
from its exact bottom values, including every stored reference. -/
theorem buildFrom_reconstruct {mountain : Mountain} (hValid : MountainValid mountain)
    (hNormal : (Frame.ofMountain mountain).Normal) (hLegs : BottomLegs mountain) :
    buildFrom #[] (Expansion.bottomValues mountain) = .ok mountain :=
  buildFrom_reconstruct_suffix hValid hNormal hLegs mountain.toList (by simp)

/-- Local validity, normality, and exact bottom legs suffice for complete
canonical reconstruction. This is equality of full mountains, rather than
only equal row summaries or equal bottom sequences. -/
theorem build_reconstruct {mountain : Mountain} (hValid : MountainValid mountain)
    (hNormal : (Frame.ofMountain mountain).Normal) (hLegs : BottomLegs mountain) :
    build (Expansion.bottomValues mountain) = .ok mountain := by
  rw [build_eq_buildFrom_of_legal (Expansion.bottomValues_legal hValid)]
  exact buildFrom_reconstruct hValid hNormal hLegs

/-- Any successful execution of the existing value extractor has the same
reconstruction. No separate claim identifying extracted values is required. -/
theorem build_reconstruct_of_valuesOf {mountain : Mountain} (hValid : MountainValid mountain)
    (hNormal : (Frame.ofMountain mountain).Normal) (hLegs : BottomLegs mountain)
    {values : List Nat} (hValues : Expansion.valuesOf mountain = .ok values) :
    build values = .ok mountain := by
  have he : values = Expansion.bottomValues mountain :=
    Except.ok.inj (hValues.symm.trans (Expansion.valuesOf_eq_bottomValues hValid))
  rw [he]
  exact build_reconstruct hValid hNormal hLegs

end OmegaY.Canonical

#print axioms OmegaY.Canonical.buildColumn_reconstruct
#print axioms OmegaY.Canonical.buildFrom_reconstruct_suffix
#print axioms OmegaY.Canonical.build_reconstruct
#print axioms OmegaY.Canonical.build_reconstruct_of_valuesOf
