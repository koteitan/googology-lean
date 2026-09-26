/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Canonical/Totality.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Canonical/Totality.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.Invariant
import Googology.Notation.OmegaY.WellOrder.OmegaY.Geometry.Executable

set_option backward.do.legacy false

/-!
# Actual canonical construction succeeds on every legal input

The search-existence input is derived from concrete column invariants, actual
Q/P equivalence, leftward real candidates, and the value-1 first column.
Neither well-foundedness of expansion nor numerical normality of a completed
mountain is assumed.  Partial columns are permitted until their top reaches 1.
-/

namespace OmegaY.Canonical

open Geometry

def TopOne (column : Column) : Prop :=
  ∃ (cell : Cell), column.back? = some cell ∧ cell.value = 1

def MountainTops (mountain : Mountain) : Prop :=
  ∀ c (hc : c < mountain.size), TopOne mountain[c]

theorem mountainTops_empty : MountainTops #[] := by
  intro c hc
  simp at hc

theorem MountainTops.push {mountain : Mountain} {column : Column}
    (hMountain : MountainTops mountain) (hColumn : TopOne column) :
    MountainTops (mountain.push column) := by
  intro c hc
  by_cases he : c = mountain.size
  · subst c
    simpa only [Array.getElem_push_eq] using hColumn
  · have hOld : c < mountain.size := by
      simp only [Array.size_push] at hc
      omega
    simpa only [Array.getElem_push_lt hOld] using hMountain c hOld

theorem ColumnValid.top_positive {mountain : Mountain} {c : Nat}
    {column : Column} {child : Cell} (hColumn : ColumnValid mountain c column)
    (hTop : column.back? = some child) : 0 < child.value := by
  have hRead : column[column.size - 1]? = some child := by
    simpa only [Array.back?_eq_getElem?] using hTop
  exact hColumn.real_positive _ _ hRead (by have := hColumn.size_ge_two; omega)

/-- The actual executable search has an answer with all bounds needed to add
the next difference cell.  Search success is a conclusion, not a premise. -/
theorem MountainValid.parent_exists_bounds {mountain : Mountain}
    (hMountain : MountainValid mountain) {current : Ref} {child : Cell}
    (hCurrent : cellAt mountain current = .ok child) (hLarge : 1 < child.value) :
    ∃ (parentRef : Ref) (parent : Cell),
      findParent mountain current = .ok parentRef ∧
      cellAt mountain parentRef = .ok parent ∧
      0 < parent.value ∧ parent.value < child.value ∧ parent.row ≤ child.row ∧
      parentRef.column < current.column := by
  obtain ⟨u, hRef, hCell⟩ := frame_node_of_cellAt hCurrent
  have hValue : 1 < (Frame.ofMountain mountain).value u := by
    simpa only [Frame.value, hCell] using hLarge
  obtain ⟨p, hParent⟩ := Frame.parent_exists_of_left_sources hMountain.toOrdered
    hMountain.left_sources hMountain.first_values hValue
  refine ⟨Frame.ref p, (Frame.ofMountain mountain).cell p, ?_,
    cellAt_of_frame_node mountain p, ?_, ?_, ?_, ?_⟩
  · rw [← hRef]
    exact (Executable.findParent_ref_iff hMountain.toOrdered u p).mpr hParent
  · exact (Frame.P_value hMountain.toOrdered hParent).1
  · simpa only [Frame.value, hCell] using
      (Frame.P_value hMountain.toOrdered hParent).2
  · simpa only [Frame.height, hCell] using Frame.P_height_le hMountain.toOrdered hParent
  · have hc := congrArg Ref.column hRef
    change u.1.val = current.column at hc
    change p.1.val < current.column
    rw [← hc]
    exact Frame.P_column_lt hMountain.toOrdered hParent

/-- A partial valid column always reaches a value-1 top within the actual
value-derived allowance, while preserving every concrete column condition. -/
theorem growColumn_total {leftColumns : Mountain}
    (hMountain : MountainValid leftColumns) {fuel : Nat} {column : Column} {child : Cell}
    (hColumn : ColumnValid leftColumns leftColumns.size column)
    (hTop : column.back? = some child) (hEnough : child.value - 1 ≤ fuel) :
    ∃ result, growColumn leftColumns fuel column = .ok result ∧
      ColumnValid leftColumns leftColumns.size result ∧ TopOne result := by
  induction fuel generalizing column child with
  | zero =>
      have hPositive := hColumn.top_positive hTop
      have hOne : child.value = 1 := by omega
      exact ⟨column, growColumn_top _ hTop hOne, hColumn, child, hTop, hOne⟩
  | succ fuel ih =>
      by_cases hOne : child.value = 1
      · exact ⟨column, growColumn_top _ hTop hOne, hColumn, child, hTop, hOne⟩
      · have hPositive := hColumn.top_positive hTop
        have hLarge : 1 < child.value := by omega
        have hZero : child.value ≠ 0 := by omega
        obtain ⟨parentRef, parent, hFind, hParent, hPPositive, hPSmall, hPRow, hPColumn⟩ :=
          (hMountain.push hColumn).parent_exists_bounds (cellAt_current_top hTop) hLarge
        have hParentLeft : cellAt leftColumns parentRef = .ok parent :=
          (cellAt_push_left (column := column) hPColumn).symm.trans hParent
        let next : Cell := {
          row := Row.B child.row parent.row
          value := child.value - parent.value
          left := some parentRef }
        have hNextPositive : 0 < next.value := by dsimp [next]; omega
        have hNextValid : ColumnValid leftColumns leftColumns.size (column.push next) :=
          hColumn.push hTop (Row.lt_B child.row parent.row) hNextPositive rfl hPColumn
            hParentLeft (hPRow.trans (Row.lt_B child.row parent.row).le)
        obtain ⟨result, hRun, hValid, hFinalTop⟩ :=
          ih hNextValid (Array.back?_push) (show next.value - 1 ≤ fuel by dsimp [next]; omega)
        refine ⟨result, ?_, hValid, hFinalTop⟩
        rw [growColumn_step fuel hTop hOne hZero]
        simpa [hFind, hParent, next] using hRun

theorem buildColumn_total {mountain : Mountain} {value : Nat}
    (hMountain : MountainValid mountain) (hPositive : 0 < value)
    (hFirst : mountain.size = 0 → value = 1) :
    ∃ column, buildColumn mountain value = .ok column ∧
      ColumnValid mountain mountain.size column ∧ TopOne column := by
  have hInitial := initialColumn_valid hMountain hPositive hFirst
  have hTop : (initialColumn mountain.size value).back? =
      some (initialBottom mountain.size value) := by simp [initialColumn, initialBottom]
  obtain ⟨column, hRun, hValid, hTopOne⟩ := growColumn_total hMountain hInitial hTop
    (show (initialBottom mountain.size value).value - 1 ≤ value - 1 by rfl)
  refine ⟨column, ?_, hValid, hTopOne⟩
  simpa [buildColumn, Nat.ne_of_gt hPositive] using hRun

/-- Once the first column exists, every finite list of positive next values
is constructible, preserving concrete validity and the value-1 stopping rule. -/
theorem buildFrom_total {mountain : Mountain} {values : List Nat}
    (hMountain : MountainValid mountain) (hTops : MountainTops mountain)
    (hNonempty : 0 < mountain.size) (hPositive : ∀ value ∈ values, 0 < value) :
    ∃ result, buildFrom mountain values = .ok result ∧
      MountainValid result ∧ MountainTops result := by
  induction values generalizing mountain with
  | nil => exact ⟨mountain, rfl, hMountain, hTops⟩
  | cons value rest ih =>
      have hValue : 0 < value := hPositive value (by simp)
      obtain ⟨column, hBuild, hValid, hTop⟩ := buildColumn_total hMountain hValue (by omega)
      obtain ⟨result, hRest, hFinal, hFinalTops⟩ := ih
        (hMountain.push hValid) (hTops.push hTop)
        (by simp [Array.size_push]) (fun v hv => hPositive v (by simp [hv]))
      refine ⟨result, ?_, hFinal, hFinalTops⟩
      simpa [buildFrom, hBuild] using hRest

/-- Exactly the engine's mathematical input domain: empty, or positive and
beginning with 1.  There is no bound on length, entry magnitude, or row degree. -/
def Legal (values : List Nat) : Prop :=
  values = [] ∨ ∃ rest, values = 1 :: rest ∧ ∀ value ∈ rest, 0 < value

/-- Actual canonical build totality, with concrete output certificates. -/
theorem build_total {values : List Nat} (hLegal : Legal values) :
    ∃ mountain, build values = .ok mountain ∧
      MountainValid mountain ∧ MountainTops mountain := by
  rcases hLegal with rfl | ⟨rest, rfl, hPositive⟩
  · exact ⟨#[], rfl, mountainValid_empty, mountainTops_empty⟩
  · obtain ⟨column, hBuild, hValid, hTop⟩ := buildColumn_total
      mountainValid_empty (show 0 < (1 : Nat) by decide) (fun _ => rfl)
    obtain ⟨result, hRest, hFinal, hFinalTops⟩ := buildFrom_total
      (mountainValid_empty.push hValid) (mountainTops_empty.push hTop)
      (by simp) hPositive
    have hAll : rest.all (fun n => 0 < n) = true := by
      simpa only [List.all_eq_true, decide_eq_true_eq] using hPositive
    refine ⟨result, ?_, hFinal, hFinalTops⟩
    simpa [build, hAll, buildFrom, hBuild] using hRest

theorem build_total_with_size {values : List Nat} (hLegal : Legal values) :
    ∃ mountain, build values = .ok mountain ∧ MountainValid mountain ∧
      MountainTops mountain ∧ mountain.size = values.length := by
  obtain ⟨mountain, hBuild, hValid, hTop⟩ := build_total hLegal
  exact ⟨mountain, hBuild, hValid, hTop, build_size hBuild⟩

#print axioms MountainValid.parent_exists_bounds
#print axioms growColumn_total
#print axioms build_total
#print axioms build_total_with_size

end OmegaY.Canonical
