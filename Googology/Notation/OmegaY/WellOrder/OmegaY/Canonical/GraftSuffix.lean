/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Canonical/GraftSuffix.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Canonical/GraftSuffix.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.Normal
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.CellLocality

set_option backward.do.legacy false

/-!
# Actual construction reproduces an old upper suffix

Copy a real cell from a completed canonical mountain to the top of a new
column, retaining that cell's row, value, and stored left endpoint. Continuing
the actual builder appends exactly the old cells above it, including their
full stored references, and reaches the old value-one top. No condition is
imposed on the portion of the new column below the copied cell.
-/

namespace OmegaY.Canonical

open Geometry

def upperSuffix (mountain : Mountain) (u : (Frame.ofMountain mountain).Node) : List Cell :=
  mountain[u.1.val].toList.drop (u.2.val + 1)

theorem upperSuffix_of_upper {mountain : Mountain}
    {u v : (Frame.ofMountain mountain).Node}
    (hUpper : (Frame.ofMountain mountain).upper u = some v) :
    upperSuffix mountain u = (Frame.ofMountain mountain).cell v :: upperSuffix mountain v := by
  rcases u with ⟨c, i⟩
  unfold Frame.upper at hUpper
  split at hUpper
  · obtain rfl := Option.some.inj hUpper
    rename_i hNext
    exact List.drop_eq_getElem_cons (l := mountain[c.val].toList)
      (i := i.val + 1) (by simpa only [Array.length_toList, Frame.ofMountain] using hNext)
  · cases hUpper

theorem upperSuffix_of_value_one {mountain : Mountain}
    (hNormal : (Frame.ofMountain mountain).Normal)
    {u : (Frame.ofMountain mountain).Node} (hReal : Frame.Real u)
    (hOne : (Frame.ofMountain mountain).value u = 1) : upperSuffix mountain u = [] := by
  have hBound : (Frame.ofMountain mountain).length u.1 ≤ u.2.val + 1 := by
    by_contra hn
    have hNext : u.2.val + 1 < (Frame.ofMountain mountain).length u.1 := by omega
    let v : (Frame.ofMountain mountain).Node := ⟨u.1, ⟨u.2.val + 1, hNext⟩⟩
    have hv : (Frame.ofMountain mountain).upper u = some v := by
      simp only [Frame.upper, dif_pos hNext, v]
    have hLarge := hNormal.upper_nontrivial u v hReal hv
    omega
  apply List.drop_eq_nil_of_le
  simpa only [Array.length_toList, Frame.ofMountain] using hBound

private theorem cell_eq_of_fields {a b : Cell}
    (hRow : a.row = b.row) (hValue : a.value = b.value) (hLeft : a.left = b.left) : a = b := by
  cases a
  cases b
  simp_all

/-- A genuine source step transfers to the new column, with exactly the same
actual parent and exactly the same complete next cell. -/
theorem graft_next_cell {mountain : Mountain}
    (hNormal : (Frame.ofMountain mountain).Normal)
    {u v : (Frame.ofMountain mountain).Node} (hReal : Frame.Real u)
    (hUpper : (Frame.ofMountain mountain).upper u = some v)
    {target : Column} (hTop : target.back? = some ((Frame.ofMountain mountain).cell u)) :
    ∃ p : (Frame.ofMountain mountain).Node,
      findParent (mountain.push target) ⟨mountain.size, target.size - 1⟩ = .ok (Frame.ref p) ∧
      cellAt (mountain.push target) (Frame.ref p) = .ok ((Frame.ofMountain mountain).cell p) ∧
      (⟨Row.B ((Frame.ofMountain mountain).height u) ((Frame.ofMountain mountain).height p),
        (Frame.ofMountain mountain).value u - (Frame.ofMountain mountain).value p,
        some (Frame.ref p)⟩ : Cell) = (Frame.ofMountain mountain).cell v := by
  obtain ⟨p, hParent, hRow, hValue, hLeft⟩ := hNormal.upper_step u v hReal hUpper
  have hOld : findParent mountain (Frame.ref u) = .ok (Frame.ref p) :=
    (Executable.findParent_ref_iff hNormal.toOrdered u p).mpr hParent
  have hMoved := findParent_success_of_same_cell (cellAt_of_frame_node mountain u)
    (cellAt_current_top hTop) (show (Frame.ref u).column ≤ mountain.size from u.1.isLt.le)
    (fun c hc => by
      have hcm : c < mountain.size := lt_trans hc u.1.isLt
      simp [Array.getElem?_push, Nat.ne_of_lt hcm]) hOld
  refine ⟨p, hMoved, ?_, ?_⟩
  · rw [cellAt_push_left p.1.isLt]
    exact cellAt_of_frame_node mountain p
  · exact cell_eq_of_fields hRow.symm hValue.symm hLeft.symm

/-- Suffix reproduction from the independently established local certificate.
The target column below its top may be arbitrary and need not be ordered. -/
theorem growColumn_graft_of_normal {mountain : Mountain}
    (hNormal : (Frame.ofMountain mountain).Normal) {fuel : Nat}
    {u : (Frame.ofMountain mountain).Node} (hReal : Frame.Real u) {target : Column}
    (hTop : target.back? = some ((Frame.ofMountain mountain).cell u))
    (hEnough : (Frame.ofMountain mountain).value u - 1 ≤ fuel) :
    ∃ result, growColumn mountain fuel target = .ok result ∧
      result.toList = target.toList ++ upperSuffix mountain u ∧ TopOne result := by
  induction fuel generalizing u target with
  | zero =>
      have hPositive := hNormal.real_positive u hReal
      have hOne : (Frame.ofMountain mountain).value u = 1 := by omega
      refine ⟨target, growColumn_top _ hTop hOne, ?_, _, hTop, hOne⟩
      simp only [upperSuffix_of_value_one hNormal hReal hOne, List.append_nil]
  | succ fuel ih =>
      by_cases hOne : (Frame.ofMountain mountain).value u = 1
      · refine ⟨target, growColumn_top _ hTop hOne, ?_, _, hTop, hOne⟩
        simp only [upperSuffix_of_value_one hNormal hReal hOne, List.append_nil]
      · have hPositive := hNormal.real_positive u hReal
        have hLarge : 1 < (Frame.ofMountain mountain).value u := by omega
        have hZero : (Frame.ofMountain mountain).value u ≠ 0 := by omega
        obtain ⟨v, hUpper⟩ := hNormal.upper_exists u hReal hLarge
        obtain ⟨p, hFind, hRead, hNext⟩ := graft_next_cell hNormal hReal hUpper hTop
        have hBounds := difference_value_bounds hTop hFind hRead
        have hV : (Frame.ofMountain mountain).value v =
            (Frame.ofMountain mountain).value u - (Frame.ofMountain mountain).value p := by
          exact (congrArg Cell.value hNext).symm
        have hDecrease : (Frame.ofMountain mountain).value v <
            (Frame.ofMountain mountain).value u := by
          rw [hV]
          exact hBounds.2
        have hVReal : Frame.Real v := by
          unfold Frame.Real
          rw [(Frame.upper_spec hUpper).2]
          omega
        obtain ⟨result, hRun, hList, hFinalTop⟩ := ih hVReal
          (target := target.push ((Frame.ofMountain mountain).cell v))
          Array.back?_push (by omega)
        refine ⟨result, ?_, ?_, hFinalTop⟩
        · rw [growColumn_step fuel hTop hOne hZero]
          simp only [hFind, hRead, except_bind_ok]
          simp only [Frame.height, Frame.value] at hNext
          rw [hNext]
          exact hRun
        · rw [upperSuffix_of_upper hUpper]
          simpa only [Array.toList_push, List.append_assoc, List.singleton_append] using hList

/-- The actual old mountain supplies the normality certificate: no success
oracle for the new continuation is an assumption. -/
theorem growColumn_graft {values : List Nat} {mountain : Mountain}
    (hLegal : Legal values) (hBuild : build values = .ok mountain)
    {u : (Frame.ofMountain mountain).Node} (hReal : Frame.Real u)
    {target : Column} (hTop : target.back? = some ((Frame.ofMountain mountain).cell u))
    (fuel : Nat) (hEnough : (Frame.ofMountain mountain).value u - 1 ≤ fuel) :
    ∃ result, growColumn mountain fuel target = .ok result ∧
      result.toList = target.toList ++
        mountain[u.1.val].toList.drop (u.2.val + 1) ∧ TopOne result :=
  growColumn_graft_of_normal (build_normal_of_legal hLegal hBuild) hReal hTop hEnough

end OmegaY.Canonical

#print axioms OmegaY.Canonical.graft_next_cell
#print axioms OmegaY.Canonical.growColumn_graft_of_normal
#print axioms OmegaY.Canonical.growColumn_graft
