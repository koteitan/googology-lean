/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/ChainsCanonParent.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.ControlDominates
import Googology.Notation.OmegaY.WellOrder.OmegaY.Geometry.FatherUpperBound
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.BottomLegs

set_option backward.do.legacy false

/-!
# The parent of an edge of a canonical mountain

Let `M = Canonical.build s` with `s` legal. For an edge of a column, from the node `u`
at index `i` to the node `v` at index `i + 1`, the parent `p` is the left endpoint stored
on `v` (`Reserve.rawParent M u = some p`). Then

  `p` is the highest node of its column whose row is strictly below the row of `v`:
  `row p < row v`, and every node `(p.column, j)` with `row < row v` has `j ≤ p.index`.

Equivalently, the node above `p` (if any) has row `≥ row v`.

For a real node `u`, `p` is the numerical parent `P(u)` (`Normal.rawParent_eq_P`), so
`row p ≤ row u < row v`, and Phyrion's father upper bound (`father_upper_bound_nodes`)
gives `row v ≤ row p⁺` for the upper neighbour `p⁺` of `p`. For the phantom `u`
(index `0`), `v` is the bottom node (row `1`) and `p` is the phantom of the previous
column (`build_bottom_legs`).

Numerical check before the proof: the canonical mountain of every sequence `1 :: rest`
with (length ≤ 7, entries ≤ 6), (length ≤ 9, entries ≤ 4) or (length ≤ 6, entries ≤ 12),
built with the mountain builder of `reference/official/omegay-trace.cjs`; 414,821
sequences, 6,368,584 edges with a real lower node, no exception.
-/

namespace OmegaY.Official.Classification.Proofs

open Canonical Reserve Geometry

/-! ## In a normal frame -/

section FrameVersion

variable {F : Frame}

/-- **Frame version.** In a normal frame, the raw parent `p` of a real node `u` with upper
neighbour `v` has row `< row v`, and every node of the column of `p` with row `< row v`
is at or below `p`. -/
theorem Normal.rawParent_highest_below (hF : F.Normal) {u v p : F.Node}
    (hReal : Frame.Real u) (hv : F.upper u = some v) (hraw : F.rawParent u = some p) :
    F.height p < F.height v ∧
      ∀ w : F.Node, w.1 = p.1 → F.height w < F.height v → w.2.val ≤ p.2.val := by
  have hP : F.P u = some p := (hF.rawParent_eq_P hReal).symm.trans hraw
  have huv : F.height u < F.height v := by
    obtain ⟨hc, hi⟩ := Frame.upper_spec hv
    exact ControlProof.height_lt_of_index hF.toOrdered hc.symm (by omega)
  refine ⟨lt_of_le_of_lt (Frame.P_height_le hF.toOrdered hP) huv, ?_⟩
  intro w hw hwv
  by_contra hn
  have hlen : p.2.val + 1 < F.length p.1 := by
    have := w.2.isLt
    have hl : F.length w.1 = F.length p.1 := by rw [hw]
    omega
  let pplus : F.Node := ⟨p.1, ⟨p.2.val + 1, hlen⟩⟩
  have hpp : F.upper p = some pplus := ControlProof.upper_eq_of_index rfl rfl
  have hD := Frame.father_upper_bound_nodes hF hP hv hpp
  have hmono : F.height pplus ≤ F.height w :=
    ControlProof.height_le_of_index hF.toOrdered (by simp [pplus, hw]) (by
      show p.2.val + 1 ≤ w.2.val
      omega)
  exact absurd (lt_of_lt_of_le hwv (hD.trans hmono)) (lt_irrefl _)

/-- The same statement through the upper neighbour of the parent: its row is at least the
row of `v`. -/
theorem Normal.rawParent_upper_ge (hF : F.Normal) {u v p pplus : F.Node}
    (hReal : Frame.Real u) (hv : F.upper u = some v) (hraw : F.rawParent u = some p)
    (hpp : F.upper p = some pplus) : F.height v ≤ F.height pplus :=
  Frame.father_upper_bound_nodes hF ((hF.rawParent_eq_P hReal).symm.trans hraw) hv hpp

end FrameVersion

/-! ## In the executable canonical mountain -/

section Canonical

variable {M : Mountain}

theorem canon_cell?_some_iff {r : Ref} {c : Cell} :
    cell? M r = some c ↔ ∃ (hc : r.column < M.size) (hi : r.index < M[r.column].size),
      M[r.column][r.index] = c := by
  unfold cell?
  constructor
  · intro h
    cases hcol : M[r.column]? with
    | none => simp [hcol] at h
    | some col =>
        rw [hcol] at h
        simp only [Option.bind_eq_bind, Option.bind_some] at h
        obtain ⟨hc, rfl⟩ := Array.getElem?_eq_some_iff.mp hcol
        obtain ⟨hi, rfl⟩ := Array.getElem?_eq_some_iff.mp h
        exact ⟨hc, hi, rfl⟩
  · rintro ⟨hc, hi, rfl⟩
    simp [Array.getElem?_eq_getElem hc, Array.getElem?_eq_getElem hi]

/-- The frame node of a reference with a cell. -/
def canonNodeOf (r : Ref) (hc : r.column < M.size) (hi : r.index < M[r.column].size) :
    (Frame.ofMountain M).Node :=
  ⟨⟨r.column, hc⟩, ⟨r.index, hi⟩⟩

theorem ref_canonNodeOf {r : Ref} (hc : r.column < M.size) (hi : r.index < M[r.column].size) :
    Frame.ref (canonNodeOf r hc hi) = r := rfl

theorem cell_canonNodeOf {r : Ref} (hc : r.column < M.size) (hi : r.index < M[r.column].size) :
    (Frame.ofMountain M).cell (canonNodeOf r hc hi) = M[r.column][r.index] := rfl

/-- **The parent of an edge of a canonical mountain is the highest node of its column
whose row is strictly below the row of the upper node.**

For the edge from `u` to `v = (u.column, u.index + 1)` with parent
`p = rawParent M u` (the left endpoint stored on `v`): `p` has a cell `cp` with
`cp.row < cv.row`, and every node `(p.column, j)` of row `< cv.row` has `j ≤ p.index`. -/
theorem canonical_rawParent_highest_below {s : List Nat} (hLegal : Legal s)
    (hBuild : build s = .ok M) {u p : Ref} {cv : Cell}
    (hv : cell? M ⟨u.column, u.index + 1⟩ = some cv) (hraw : rawParent M u = some p) :
    ∃ cp, cell? M p = some cp ∧ cp.row < cv.row ∧
      ∀ j c, cell? M ⟨p.column, j⟩ = some c → c.row < cv.row → j ≤ p.index := by
  have hN := build_normal_of_legal hLegal hBuild
  have hO := hN.toOrdered
  obtain ⟨hc, hvi, hvc⟩ := canon_cell?_some_iff.mp hv
  have hvi' : u.index + 1 < M[u.column].size := hvi
  have hui : u.index < M[u.column].size := by omega
  let nu := canonNodeOf u hc hui
  let nv := canonNodeOf ⟨u.column, u.index + 1⟩ hc hvi
  have hup : (Frame.ofMountain M).upper nu = some nv := ControlProof.upper_eq_of_index rfl rfl
  have hleft : ((Frame.ofMountain M).cell nv).left = some p := by
    have h := ControlProof.rawParent_ref (M := M) nu
    rw [ref_canonNodeOf, hup] at h
    simpa only [Option.bind_some] using h.symm.trans hraw
  obtain ⟨np, hlk, _, _⟩ := hO.stored_valid nv p hleft
  have hnp : Frame.ref np = p := Frame.lookup_spec hlk
  have hleft' : ((Frame.ofMountain M).cell nv).left = some (Frame.ref np) := by
    rw [hnp]
    exact hleft
  have hrawF : (Frame.ofMountain M).rawParent nu = some np :=
    Frame.rawParent_eq_of_upper_left hup hleft'
  have hcvF : (Frame.ofMountain M).cell nv = cv := hvc
  subst hnp
  refine ⟨(Frame.ofMountain M).cell np, ControlProof.cell?_ref np, ?_⟩
  -- the reading of a cell of the parent column as a frame node
  have hread : ∀ j c, cell? M ⟨np.1.val, j⟩ = some c →
      ∃ w : (Frame.ofMountain M).Node, w.1 = np.1 ∧ w.2.val = j ∧
        (Frame.ofMountain M).cell w = c := by
    intro j c hjc
    obtain ⟨hc', hj', hcell⟩ := canon_cell?_some_iff.mp hjc
    exact ⟨canonNodeOf ⟨np.1.val, j⟩ hc' hj', rfl, rfl, hcell⟩
  by_cases hReal : 0 < u.index
  · obtain ⟨hlt, hmax⟩ := Normal.rawParent_highest_below hN
      (show Frame.Real nu from hReal) hup hrawF
    refine ⟨by rw [← hcvF]; exact hlt, ?_⟩
    intro j c hjc hjr
    obtain ⟨w, hw1, hw2, hwc⟩ := hread j c hjc
    have := hmax w hw1 (by
      show ((Frame.ofMountain M).cell w).row < ((Frame.ofMountain M).cell nv).row
      rw [hwc, hcvF]
      exact hjr)
    simp only [Frame.ref]
    omega
  · -- the phantom edge: `v` is the bottom node and `p` the phantom of the previous column
    have hu0 : u.index = 0 := by omega
    have hvlen : 1 < (Frame.ofMountain M).length nv.1 := by
      show 1 < M[u.column].size
      rw [hu0] at hvi'
      exact hvi'
    have hbot := build_bottom_left hBuild nv.1 hvlen
    have hnv1 : nv.2 = ⟨1, hvlen⟩ := Fin.ext (by simp [nv, canonNodeOf, hu0])
    have hvrow : cv.row = 1 := by
      rw [← hcvF]
      show ((Frame.ofMountain M).cells nv.1 nv.2).row = 1
      rw [hnv1]
      exact hO.bottom_row nv.1 hvlen
    have hleft1 : ((Frame.ofMountain M).cells nv.1 ⟨1, hvlen⟩).left =
        some (Frame.ref np) := by
      rw [← hnv1]
      exact hleft'
    rw [hbot] at hleft1
    have hcol0 : nv.1.val ≠ 0 := by
      intro h0
      rw [if_pos h0] at hleft1
      cases hleft1
    rw [if_neg hcol0] at hleft1
    have hpref : Frame.ref np = ⟨nv.1.val - 1, 0⟩ := (Option.some.inj hleft1).symm
    have hnp0 : np.2.val = 0 := by
      have := congrArg Canonical.Ref.index hpref
      simpa [Frame.ref] using this
    have hnpphantom : (Frame.ofMountain M).cell np = Canonical.phantom := by
      have hlen0 : 0 < (Frame.ofMountain M).length np.1 := by
        have := hO.length_ge_two np.1
        omega
      have hnp2 : np.2 = ⟨0, hlen0⟩ := Fin.ext hnp0
      show (Frame.ofMountain M).cells np.1 np.2 = _
      rw [hnp2]
      exact hO.phantom np.1 hlen0
    refine ⟨?_, ?_⟩
    · rw [hnpphantom, hvrow]
      exact Row.zero_lt_one
    · intro j c hjc hjr
      obtain ⟨w, hw1, hw2, hwc⟩ := hread j c hjc
      by_contra hn
      have hwReal : Frame.Real w := by
        show 0 < w.2.val
        simp only [Frame.ref] at hn
        omega
      have h1 := Frame.one_le_height hO hwReal
      have : (Frame.ofMountain M).height w < 1 := by
        show ((Frame.ofMountain M).cell w).row < 1
        rw [hwc, ← hvrow]
        exact hjr
      exact absurd (lt_of_le_of_lt h1 this) (lt_irrefl _)

/-- **Upper-neighbour form.** The node above the parent of an edge has row at least the
row of the upper node of the edge. -/
theorem canonical_rawParent_upper_ge {s : List Nat} (hLegal : Legal s)
    (hBuild : build s = .ok M) {u p : Ref} {cv cpp : Cell}
    (hv : cell? M ⟨u.column, u.index + 1⟩ = some cv) (hraw : rawParent M u = some p)
    (hpp : cell? M ⟨p.column, p.index + 1⟩ = some cpp) : cv.row ≤ cpp.row := by
  obtain ⟨_, _, _, hmax⟩ := canonical_rawParent_highest_below hLegal hBuild hv hraw
  by_contra hn
  have := hmax (p.index + 1) cpp hpp (lt_of_not_ge hn)
  omega

/-- **Iff form.** A node `(p.column, j)` of the parent column is strictly below the row of
the upper node of the edge exactly when `j ≤ p.index`. -/
theorem canonical_rawParent_below_iff {s : List Nat} (hLegal : Legal s)
    (hBuild : build s = .ok M) {u p : Ref} {cv c : Cell} {j : Nat}
    (hv : cell? M ⟨u.column, u.index + 1⟩ = some cv) (hraw : rawParent M u = some p)
    (hc : cell? M ⟨p.column, j⟩ = some c) : c.row < cv.row ↔ j ≤ p.index := by
  obtain ⟨cp, hcp, hlt, hmax⟩ := canonical_rawParent_highest_below hLegal hBuild hv hraw
  refine ⟨hmax j c hc, fun hj => ?_⟩
  have hV : MountainValid M := by
    obtain ⟨R, hR, hVR, _⟩ := build_total hLegal
    rw [hBuild] at hR
    cases hR
    exact hVR
  obtain ⟨hcc, hjs, hjc⟩ := canon_cell?_some_iff.mp hc
  obtain ⟨_, hps, hpc⟩ := canon_cell?_some_iff.mp hcp
  have hcol := hV p.column hcc
  rcases Nat.lt_or_eq_of_le hj with hj | hj
  · exact lt_trans (hcol.rows_strict j p.index c cp
      (by rw [Array.getElem?_eq_getElem hjs, hjc]) (by
        rw [Array.getElem?_eq_getElem hps, hpc]) hj) hlt
  · subst hj
    have : c = cp := hjc.symm.trans hpc
    rw [this]
    exact hlt

end Canonical

#print axioms Normal.rawParent_highest_below
#print axioms canonical_rawParent_highest_below
#print axioms canonical_rawParent_upper_ge
#print axioms canonical_rawParent_below_iff

end OmegaY.Official.Classification.Proofs
