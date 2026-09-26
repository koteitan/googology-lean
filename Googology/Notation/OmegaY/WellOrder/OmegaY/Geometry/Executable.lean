/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Geometry/Executable.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Geometry/Executable.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Geometry.Frame
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.Search

set_option backward.do.legacy false

/-!
# Actual array search and finite frame search

This module connects the executable searches to their finite geometric
definitions. The column climb is proved to compute its maximum directly from
the array recursion; no search correspondence is included in an input record.
-/

namespace OmegaY.Geometry.Executable

open Canonical

/-- The consecutive executable climb computes the last eligible array index. -/
theorem climb_spec (column : Column)
    (hmono : StrictMono (fun i : Fin column.size => column[i.val].row))
    (ceiling : Row) (start : Fin column.size)
    (hstart : column[start.val].row ≤ ceiling) :
    ∃ out : Fin column.size,
      climb ceiling start.val (column.toList.drop (start.val + 1)) = out.val ∧
      start ≤ out ∧ column[out.val].row ≤ ceiling ∧
      ∀ j : Fin column.size, start ≤ j → column[j.val].row ≤ ceiling → j ≤ out := by
  by_cases hn : start.val + 1 < column.size
  · let next : Fin column.size := ⟨start.val + 1, hn⟩
    have hd : column.toList.drop (start.val + 1) =
        column[next.val] :: column.toList.drop (next.val + 1) := by
      exact (List.drop_eq_getElem_cons (l := column.toList)
        (i := start.val + 1) (by simpa using hn))
    by_cases hnext : column[next.val].row ≤ ceiling
    · obtain ⟨out, heq, hle, hout, hmax⟩ := climb_spec column hmono ceiling next hnext
      refine ⟨out, ?_, le_trans (by exact Nat.le_succ start.val) hle, hout, ?_⟩
      · rw [hd, climb, if_pos hnext]
        exact heq
      · intro j hj hjrow
        by_cases hnj : next ≤ j
        · exact hmax j hnj hjrow
        · have hjs : j = start := by
            apply Fin.ext
            change ¬ start.val + 1 ≤ j.val at hnj
            change start.val ≤ j.val at hj
            omega
          simpa [hjs] using (le_trans (show start ≤ next from Nat.le_succ _) hle)
    · refine ⟨start, ?_, le_rfl, hstart, ?_⟩
      · rw [hd, climb, if_neg hnext]
      · intro j hj hjrow
        by_contra hnot
        have hnj : next ≤ j := by change start.val + 1 ≤ j.val; omega
        exact hnext ((hmono.monotone hnj).trans hjrow)
  · have hd : column.toList.drop (start.val + 1) = [] := by
      apply List.drop_eq_nil_of_le
      simpa using Nat.le_of_not_gt hn
    refine ⟨start, by simp [hd, climb], le_rfl, hstart, ?_⟩
    intro j _ _
    have hj := j.isLt
    change j.val ≤ start.val
    omega
termination_by column.size - start.val
decreasing_by omega

private theorem read_node (mountain : Mountain) (u : (Frame.ofMountain mountain).Node) :
    cellAt mountain (Frame.ref u) = .ok ((Frame.ofMountain mountain).cell u) := by
  have hread (c i : Nat) (hc : c < mountain.size) (hi : i < mountain[c].size) :
      cellAt mountain ⟨c, i⟩ = .ok mountain[c][i] := by
    simp [cellAt, Array.getElem?_eq_getElem hc, Array.getElem?_eq_getElem hi]
  exact hread u.1.val u.2.val u.1.isLt u.2.isLt

theorem ref_injective (F : Frame) : Function.Injective (@Frame.ref F) := by
  intro u v h
  apply Option.some.inj
  rw [← F.lookup_ref u, ← F.lookup_ref v, h]

/-- A stored endpoint's executable climb is exactly the finite maximum Q. -/
theorem candidate_of_stored {mountain : Mountain}
    (hF : (Frame.ofMountain mountain).Ordered)
    {u left : (Frame.ofMountain mountain).Node}
    (hleft : ((Frame.ofMountain mountain).cell u).left = some (Frame.ref left)) :
    ∃ q : (Frame.ofMountain mountain).Node,
      (Frame.ofMountain mountain).Q u = some q ∧
      nextCandidate mountain (Frame.ref u) = .ok (Frame.ref q) := by
  let F := Frame.ofMountain mountain
  obtain ⟨stored, hs, hcol, hrow⟩ := hF.stored_valid u (Frame.ref left) hleft
  have he : stored = left := by simpa using hs.symm
  subst stored
  obtain ⟨i, hclimb, hle, hheight, hmax⟩ :=
    climb_spec mountain[left.1.val] (hF.rows_strict left.1)
      (F.height u) left.2 hrow
  let q : F.Node := ⟨left.1, i⟩
  refine ⟨q, ?_, ?_⟩
  · apply Frame.Q_eq_of_maximal hleft i (Frame.mem_eligible.mpr ⟨hle, hheight⟩)
    intro j hj
    obtain ⟨hji, hjheight⟩ := Frame.mem_eligible.mp hj
    exact hmax j hji hjheight
  · simp only [nextCandidate, read_node, except_bind_ok, hleft]
    simp only [Frame.ref, hcol, not_true_eq_false, ↓reduceIte, except_pure,
      Array.getElem?_eq_getElem left.1.isLt]
    change Except.ok ⟨left.1.val, climb (F.height u) left.2.val
      (mountain[left.1.val].toList.drop (left.2.val + 1))⟩ = .ok (Frame.ref q)
    rw [hclimb]
    rfl

/-- Success is equivalent for the actual array Q step and the geometric Q. -/
theorem nextCandidate_iff {mountain : Mountain}
    (hF : (Frame.ofMountain mountain).Ordered)
    (u : (Frame.ofMountain mountain).Node) (r : Ref) :
    nextCandidate mountain (Frame.ref u) = .ok r ↔
      ∃ q : (Frame.ofMountain mountain).Node,
        (Frame.ofMountain mountain).Q u = some q ∧ Frame.ref q = r := by
  cases hs : ((Frame.ofMountain mountain).cell u).left with
  | none => simp [Frame.Q, hs, nextCandidate, read_node]
  | some stored =>
    obtain ⟨left, hl, _, _⟩ := hF.stored_valid u stored hs
    have hstored := Frame.lookup_spec hl
    have hleft : ((Frame.ofMountain mountain).cell u).left = some (Frame.ref left) :=
      hs.trans (congrArg some hstored.symm)
    obtain ⟨q, hq, ha⟩ := candidate_of_stored hF hleft
    simp [ha, hq]

theorem nextCandidate_ref_iff {mountain : Mountain}
    (hF : (Frame.ofMountain mountain).Ordered)
    (u q : (Frame.ofMountain mountain).Node) :
    nextCandidate mountain (Frame.ref u) = .ok (Frame.ref q) ↔
      (Frame.ofMountain mountain).Q u = some q := by
  rw [nextCandidate_iff hF]
  constructor
  · rintro ⟨q', hq', he⟩
    obtain rfl := ref_injective _ he
    exact hq'
  · exact fun h => ⟨q, h, rfl⟩

/-- Every amount of operational fuel agrees with the corresponding finite
geometric search; failures are forgotten only on the two sides of this equality. -/
theorem findParentAux_toOption {mountain : Mountain}
    (hF : (Frame.ofMountain mountain).Ordered) (threshold fuel : Nat)
    (u : (Frame.ofMountain mountain).Node) :
    (findParentAux mountain threshold fuel (Frame.ref u)).toOption =
      (((Frame.ofMountain mountain).Q u).bind
        ((Frame.ofMountain mountain).seek threshold fuel)).map Frame.ref := by
  induction fuel generalizing u with
  | zero =>
    cases (Frame.ofMountain mountain).Q u <;>
      simp [findParentAux, Frame.seek, Except.toOption]
  | succ fuel ih =>
    cases hq : (Frame.ofMountain mountain).Q u with
    | none =>
      have he : ∃ e, nextCandidate mountain (Frame.ref u) = .error e := by
        cases hn : nextCandidate mountain (Frame.ref u) with
        | error e => exact ⟨e, rfl⟩
        | ok r =>
          obtain ⟨q, hq', _⟩ := (nextCandidate_iff hF u r).mp hn
          simp [hq] at hq'
      obtain ⟨e, he⟩ := he
      simp [findParentAux, he, Except.toOption]
    | some q =>
      have hn := (nextCandidate_ref_iff hF u q).mpr hq
      simp only [findParentAux, hn, except_bind_ok, read_node,
        Option.bind_some, Frame.seek]
      change (if 0 < (Frame.ofMountain mountain).value q ∧
          (Frame.ofMountain mountain).value q < threshold then
          pure (Frame.ref q) else findParentAux mountain threshold fuel (Frame.ref q)).toOption =
        (if 0 < (Frame.ofMountain mountain).value q ∧
          (Frame.ofMountain mountain).value q < threshold then some q else
          ((Frame.ofMountain mountain).Q q).bind
            ((Frame.ofMountain mountain).seek threshold fuel)).map Frame.ref
      by_cases ht : 0 < (Frame.ofMountain mountain).value q ∧
          (Frame.ofMountain mountain).value q < threshold
      · simp [ht, Except.toOption]
      · simpa only [ht, if_false] using ih q

/-- The actual numerical parent is exactly Frame.P, including its column fuel. -/
theorem findParent_toOption {mountain : Mountain}
    (hF : (Frame.ofMountain mountain).Ordered)
    (u : (Frame.ofMountain mountain).Node) :
    (findParent mountain (Frame.ref u)).toOption =
      ((Frame.ofMountain mountain).P u).map Frame.ref := by
  simp only [findParent, read_node, except_bind_ok]
  exact findParentAux_toOption hF ((Frame.ofMountain mountain).value u) u.1.val u

theorem findParent_iff {mountain : Mountain}
    (hF : (Frame.ofMountain mountain).Ordered)
    (u : (Frame.ofMountain mountain).Node) (r : Ref) :
    findParent mountain (Frame.ref u) = .ok r ↔
      ∃ p : (Frame.ofMountain mountain).Node,
        (Frame.ofMountain mountain).P u = some p ∧ Frame.ref p = r := by
  have h := findParent_toOption hF u
  cases ha : findParent mountain (Frame.ref u) <;>
    cases hp : (Frame.ofMountain mountain).P u <;>
    simp [ha, hp, Except.toOption] at h ⊢
  simp only [h]

theorem findParent_ref_iff {mountain : Mountain}
    (hF : (Frame.ofMountain mountain).Ordered)
    (u p : (Frame.ofMountain mountain).Node) :
    findParent mountain (Frame.ref u) = .ok (Frame.ref p) ↔
      (Frame.ofMountain mountain).P u = some p := by
  rw [findParent_iff hF]
  constructor
  · rintro ⟨p', hp', he⟩
    obtain rfl := ref_injective _ he
    exact hp'
  · exact fun h => ⟨p, h, rfl⟩

#print axioms climb_spec
#print axioms nextCandidate_ref_iff
#print axioms findParent_ref_iff

end OmegaY.Geometry.Executable
