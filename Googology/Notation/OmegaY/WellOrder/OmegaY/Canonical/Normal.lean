/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Canonical/Normal.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Canonical/Normal.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.Totality
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.Locality
import Googology.Notation.OmegaY.WellOrder.OmegaY.Geometry.FatherUpperBound

set_option backward.do.legacy false

/-!
# The actual canonical builder satisfies the local geometric rules

Adjacent difference steps are recorded without requiring a partial column's
top to equal one.  Executable search locality preserves those records when
more cells or columns are appended.  Only after construction finishes do we
combine the records with the proved value-one stopping property.
-/

namespace OmegaY.Canonical

open Geometry

/-- A certificate of actual executed adjacent steps, including the actual
numerical search, not an independently supplied parent map. -/
def ColumnSteps (mountain : Mountain) (c : Nat) (column : Column) : Prop :=
  ∀ (i : Nat) (child upper : Cell), column[i]? = some child →
    column[i + 1]? = some upper → 0 < i →
    1 < child.value ∧ ∃ (parentRef : Ref) (parent : Cell),
      parentRef.column < c ∧ findParent mountain ⟨c, i⟩ = .ok parentRef ∧
      cellAt mountain parentRef = .ok parent ∧
      upper.row = Row.B child.row parent.row ∧
      upper.value = child.value - parent.value ∧ upper.left = some parentRef

def MountainSteps (mountain : Mountain) : Prop :=
  ∀ c (hc : c < mountain.size), ColumnSteps mountain c mountain[c]

theorem initialColumn_steps (mountain : Mountain) (c value : Nat) :
    ColumnSteps mountain c (initialColumn c value) := by
  intro i child upper hChild hUpper hi
  rcases initialColumn_cases hUpper with ⟨h, _⟩ | ⟨h, _⟩ <;> omega

theorem ColumnSteps.transport {before after : Mountain} {c : Nat} {column : Column}
    (h : ColumnSteps before c column)
    (hSearch : ∀ i, i < column.size →
      findParent before ⟨c, i⟩ = findParent after ⟨c, i⟩)
    (hRead : ∀ ref, ref.column < c → cellAt before ref = cellAt after ref) :
    ColumnSteps after c column := by
  intro i child upper hChild hUpper hi
  obtain ⟨hLarge, p, parent, hp, hFind, hParent, hRow, hValue, hLeft⟩ :=
    h i child upper hChild hUpper hi
  have hiSize := (Array.getElem?_eq_some_iff.mp hChild).1
  exact ⟨hLarge, p, parent, hp, (hSearch i hiSize).symm.trans hFind,
    (hRead p hp).symm.trans hParent, hRow, hValue, hLeft⟩

theorem MountainSteps.push {mountain : Mountain} {column : Column}
    (hMountain : MountainSteps mountain)
    (hColumn : ColumnSteps (mountain.push column) mountain.size column) :
    MountainSteps (mountain.push column) := by
  intro c hc
  by_cases he : c = mountain.size
  · subst c
    simpa only [Array.getElem_push_eq] using hColumn
  · have hOld : c < mountain.size := by simp only [Array.size_push] at hc; omega
    rw [Array.getElem_push_lt hOld]
    exact (hMountain c hOld).transport
      (fun _ _ => (findParent_push hOld).symm)
      (fun ref hr => (cellAt_push_left (hr.trans hOld)).symm)

/-- Appending the next genuine difference cell preserves every previous
record and records precisely the successful search used for the new cell. -/
theorem ColumnSteps.push {left : Mountain} {column : Column} {child parent : Cell}
    {p : Ref} (h : ColumnSteps (left.push column) left.size column)
    (hTop : column.back? = some child) (hLarge : 1 < child.value)
    (hFind : findParent (left.push column) ⟨left.size, column.size - 1⟩ = .ok p)
    (hParent : cellAt (left.push column) p = .ok parent) :
    let next : Cell := ⟨Row.B child.row parent.row, child.value - parent.value, some p⟩
    ColumnSteps (left.push (column.push next)) left.size (column.push next) := by
  dsimp only
  let next : Cell := ⟨Row.B child.row parent.row, child.value - parent.value, some p⟩
  have hCurrent := cellAt_current_top (leftColumns := left) hTop
  have hp : p.column < left.size :=
    ((findParent_iff hCurrent).mp hFind).column_lt
  intro i a b ha hb hi
  have hiBound := (Array.getElem?_eq_some_iff.mp ha).1
  have hjBound := (Array.getElem?_eq_some_iff.mp hb).1
  simp only [Array.size_push] at hiBound hjBound
  have hiOld : i < column.size := by omega
  have haOld : column[i]? = some a := by
    simpa only [Array.getElem?_push, if_neg (Nat.ne_of_lt hiOld)] using ha
  by_cases hNew : i + 1 = column.size
  · have hiTop : i = column.size - 1 := by omega
    have haTop : a = child := by
      have ht : column[column.size - 1]? = some child := by
        simpa only [Array.back?_eq_getElem?] using hTop
      rw [hiTop, ht] at haOld
      exact Option.some.inj haOld.symm
    have hbNext : b = next := by
      simpa only [Array.getElem?_push, hNew, if_true, Option.some.injEq] using hb.symm
    subst a
    subst b
    refine ⟨hLarge, p, parent, hp, ?_, ?_, rfl, rfl, rfl⟩
    · rw [findParent_push_cell hiOld, hiTop]
      exact hFind
    · rw [cellAt_push_left hp, ← cellAt_push_left (column := column) hp]
      exact hParent
  · have hjOld : i + 1 < column.size := by omega
    have hbOld : column[i + 1]? = some b := by
      simpa only [Array.getElem?_push, if_neg hNew] using hb
    obtain ⟨hA, q, qCell, hq, hSearch, hRead, hRow, hValue, hLeft⟩ :=
      h i a b haOld hbOld hi
    refine ⟨hA, q, qCell, hq, ?_, ?_, hRow, hValue, hLeft⟩
    · rw [findParent_push_cell hiOld]
      exact hSearch
    · rw [cellAt_push_left hq, ← cellAt_push_left (column := column) hq]
      exact hRead

theorem growColumn_steps {left : Mountain} {fuel : Nat} {column result : Column}
    (hSteps : ColumnSteps (left.push column) left.size column)
    (hRun : growColumn left fuel column = .ok result) :
    ColumnSteps (left.push result) left.size result := by
  induction fuel generalizing column with
  | zero =>
      rw [growColumn] at hRun
      cases ht : column.back? with
      | none => simp [ht] at hRun
      | some child =>
          by_cases ho : child.value = 1
          · have he : column = result := by simpa [ht, ho] using hRun
            subst result
            exact hSteps
          · by_cases hz : child.value = 0 <;> simp [ht, ho, hz] at hRun
  | succ fuel ih =>
      cases ht : column.back? with
      | none => rw [growColumn] at hRun; simp [ht] at hRun
      | some child =>
          by_cases ho : child.value = 1
          · have he : column = result := by
              simpa only [growColumn_top _ ht ho, Except.ok.injEq] using hRun
            subst result
            exact hSteps
          · by_cases hz : child.value = 0
            · rw [growColumn] at hRun; simp [ht, hz] at hRun
            · rw [growColumn_step fuel ht ho hz] at hRun
              cases hp : findParent (left.push column) ⟨left.size, column.size - 1⟩ with
              | error e => simp [hp] at hRun
              | ok p =>
                  cases hr : cellAt (left.push column) p with
                  | error e => simp [hp, hr] at hRun
                  | ok parent =>
                      have hNext := hSteps.push ht (by omega) hp hr
                      apply ih hNext
                      simpa only [hp, hr, except_bind_ok] using hRun

theorem buildColumn_steps {mountain : Mountain} {value : Nat} {column : Column}
    (hRun : buildColumn mountain value = .ok column) :
    ColumnSteps (mountain.push column) mountain.size column := by
  unfold buildColumn at hRun
  split at hRun
  · cases hRun
  · exact growColumn_steps (initialColumn_steps _ _ _) hRun

theorem buildFrom_steps {mountain result : Mountain} {values : List Nat}
    (hSteps : MountainSteps mountain) (hRun : buildFrom mountain values = .ok result) :
    MountainSteps result := by
  induction values generalizing mountain with
  | nil =>
      have he : mountain = result := by simpa only [buildFrom, Except.ok.injEq] using hRun
      exact he ▸ hSteps
  | cons value rest ih =>
      cases hb : buildColumn mountain value with
      | error e => simp [buildFrom, hb] at hRun
      | ok column =>
          apply ih (hSteps.push (buildColumn_steps hb))
          simpa only [buildFrom, hb, except_bind_ok] using hRun

theorem build_steps {values : List Nat} {mountain : Mountain}
    (hRun : build values = .ok mountain) : MountainSteps mountain := by
  apply buildFrom_steps (mountain := #[]) (values := values) ?_ (buildFrom_of_build hRun)
  intro c hc
  simp at hc

/-- Executable records give the actual geometric numerical parent, using
the separately proved equivalence of the two candidate-search procedures. -/
theorem MountainSteps.upper_step {mountain : Mountain}
    (hValid : MountainValid mountain) (hSteps : MountainSteps mountain)
    {u v : (Frame.ofMountain mountain).Node} (hReal : Frame.Real u)
    (hUpper : (Frame.ofMountain mountain).upper u = some v) :
    1 < (Frame.ofMountain mountain).value u ∧
    ∃ p, (Frame.ofMountain mountain).P u = some p ∧
      (Frame.ofMountain mountain).height v =
        Row.B ((Frame.ofMountain mountain).height u) ((Frame.ofMountain mountain).height p) ∧
      (Frame.ofMountain mountain).value v =
        (Frame.ofMountain mountain).value u - (Frame.ofMountain mountain).value p ∧
      ((Frame.ofMountain mountain).cell v).left = some (Frame.ref p) := by
  rcases u with ⟨c, i⟩
  unfold Frame.upper at hUpper
  split at hUpper
  · obtain rfl := Option.some.inj hUpper
    rename_i hNext
    have hi : i.val < mountain[c.val].size := i.isLt
    have hj : i.val + 1 < mountain[c.val].size := hNext
    obtain ⟨hLarge, p, parent, hp, hFind, hRead, hRow, hValue, hLeft⟩ :=
      hSteps c.val c.isLt i.val mountain[c.val][i.val] mountain[c.val][i.val + 1]
        (Array.getElem?_eq_getElem hi) (Array.getElem?_eq_getElem hj) hReal
    obtain ⟨pNode, hRef, hCell⟩ := frame_node_of_cellAt hRead
    refine ⟨hLarge, pNode, ?_, ?_, ?_, ?_⟩
    · apply (Executable.findParent_ref_iff hValid.toOrdered ⟨c, i⟩ pNode).mp
      rw [hRef]
      exact hFind
    · simp only [Frame.height, hCell]
      simpa only [Frame.cell, Frame.ofMountain] using hRow
    · simp only [Frame.value, hCell]
      simpa only [Frame.cell, Frame.ofMountain] using hValue
    · rw [hRef]
      simpa only [Frame.cell, Frame.ofMountain] using hLeft
  · cases hUpper

/-- The completed finite array has the exact local certificate required by
the geometric theorems.  This statement does not assume that certificate. -/
theorem normal_of_certificates {mountain : Mountain}
    (hValid : MountainValid mountain) (hTops : MountainTops mountain)
    (hSteps : MountainSteps mountain) : (Frame.ofMountain mountain).Normal := by
  refine {
    toOrdered := hValid.toOrdered
    upper_exists := ?_
    upper_nontrivial := fun _ _ hr hu => (hSteps.upper_step hValid hr hu).1
    upper_step := fun _ _ hr hu => (hSteps.upper_step hValid hr hu).2 }
  intro u hReal hLarge
  rcases u with ⟨c, i⟩
  have hi : i.val < mountain[c.val].size := i.isLt
  have hNext : i.val + 1 < mountain[c.val].size := by
    by_contra hn
    have hLast : i.val = mountain[c.val].size - 1 := by omega
    obtain ⟨top, hTop, hOne⟩ := hTops c.val c.isLt
    change mountain[c.val].back? = some top at hTop
    have hRead : mountain[c.val][i.val]? = some top := by
      rw [hLast]
      rw [Array.back?_eq_getElem?] at hTop
      exact hTop
    have hCell : mountain[c.val][i.val] = top := by
      simpa only [Array.getElem?_eq_getElem hi, Option.some.injEq] using hRead
    have hValue : (Frame.ofMountain mountain).value ⟨c, i⟩ = 1 := by
      change mountain[c.val][i.val].value = 1
      rw [hCell, hOne]
    omega
  refine ⟨⟨c, ⟨i.val + 1, hNext⟩⟩, ?_⟩
  unfold Frame.upper
  split
  · rfl
  · rename_i hn
    exact False.elim (hn hNext)

theorem build_normal_of_legal {values : List Nat} {mountain : Mountain}
    (hLegal : Legal values) (hBuild : build values = .ok mountain) :
    (Frame.ofMountain mountain).Normal := by
  obtain ⟨result, hResult, hValid, hTops⟩ := build_total hLegal
  have he : result = mountain := by rw [hBuild] at hResult; exact Except.ok.inj hResult.symm
  subst result
  exact normal_of_certificates hValid hTops (build_steps hBuild)

/-- Totality and the actual local geometric rules, with no assumed search
success, normality, or well-foundedness of expansion. -/
theorem build_total_normal {values : List Nat} (hLegal : Legal values) :
    ∃ mountain, build values = .ok mountain ∧ MountainValid mountain ∧
      MountainTops mountain ∧ (Frame.ofMountain mountain).Normal := by
  obtain ⟨mountain, hBuild, hValid, hTops⟩ := build_total hLegal
  exact ⟨mountain, hBuild, hValid, hTops,
    normal_of_certificates hValid hTops (build_steps hBuild)⟩

#print axioms growColumn_steps
#print axioms build_steps
#print axioms normal_of_certificates
#print axioms build_normal_of_legal
#print axioms build_total_normal

end OmegaY.Canonical
