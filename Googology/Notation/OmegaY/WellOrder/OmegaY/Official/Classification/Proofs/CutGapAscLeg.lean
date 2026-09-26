/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/CutGapAscLeg.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CutPartsTop
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CopyShapeItems

set_option backward.do.legacy false

/-!
# The leg of a node passes the ascension test of its row (`CutGap`)

`ascLeg`: in a canonical mountain, let `C` be a row, `x > cr`, `(x, C)` a node whose leg `l`
(the left end of the edge into `(x, C)`) is right of `cr`, and let `x` pass the ascension test of
`C` (the in-row parents from `(x, Z)`, `Z` the reference row of `C`, reach the column `cr`
exactly). Then `l` passes the same test.

* If the finite coefficient of `C` is positive, `Z = C - 1`, `(x, C)` is the node above
  `(x, Z)` and its leg is the in-row parent `q = P(x, Z)` (the row law), so the test from `l` is
  the rest of the test from `x`.
* Otherwise `Z = C` and `q = P(x, C)` is the raw parent of `(x, C)`, at the row `C`. The parent
  search for the node above `(x, C)` starts at the node `Q` of the leg column at or below `C`
  and reaches `q` by numerical parents (`Frame.Hit.parentPath`). The rows along this path lie
  between `row q = C` and `row Q ≤ C`, so all are `C`: `Q` is the node `(l, C)` and every step is
  an in-row parent. The test from `l` follows the path to `q` and then the test from `x`.
-/

namespace OmegaY.Official.Classification.Proofs.CutGap

open Canonical Reserve Official Descent Classification Proofs Geometry
open ChainCorr ChainCorr.CutParts

/-! ## The ascension test does not depend on the fuel -/

theorem reachesRoot_fuel {M : Mountain} {cr : Nat} :
    ∀ (f f' : Nat) (a : Ref), a.column < f → a.column < f' →
      reachesRoot M cr f a = reachesRoot M cr f' a
  | 0, _, a, h, _ => absurd h (Nat.not_lt_zero _)
  | _ + 1, 0, a, _, h => absurd h (Nat.not_lt_zero _)
  | f + 1, f' + 1, a, h, h' => by
      unfold reachesRoot
      by_cases hc : a.column ≤ cr
      · rw [if_pos hc, if_pos hc]
      · rw [if_neg hc, if_neg hc]
        cases hw : Expansion.weakParent M a with
        | error e => simp [liftE, hw, Except.mapError, bind, Except.bind]
        | ok wp =>
          cases wp with
          | none => simp [liftE, hw, Except.mapError, bind, Except.bind]
          | some p =>
            have hp := Expansion.weakParent_column_lt hw
            simp only [liftE, hw, Except.mapError, bind, Except.bind]
            exact reachesRoot_fuel f f' p (by omega) (by omega)

theorem reachesRoot_step {M : Mountain} {cr f : Nat} {a p : Ref} (ha : cr < a.column)
    (hw : Expansion.weakParent M a = .ok (some p)) :
    reachesRoot M cr (f + 1) a = reachesRoot M cr f p := by
  conv_lhs => unfold reachesRoot
  rw [if_neg (by omega)]
  simp [liftE, hw, Except.mapError, bind, Except.bind]

/-! ## Numerical parents at the same row are in-row parents -/

theorem weakParent_of_P {s : List Nat} {M : Mountain} (hb : Canonical.build s = .ok M)
    {u p : (Frame.ofMountain M).Node} (hP : (Frame.ofMountain M).P u = some p)
    (hh : (Frame.ofMountain M).height p = (Frame.ofMountain M).height u) :
    Expansion.weakParent M (Frame.ref u) = .ok (some (Frame.ref p)) := by
  have hO := (build_normal_of_success hb).toOrdered
  have hraw := rawParent_of_P hb hP
  have hlt := Frame.P_column_lt hO hP
  have hcu := ControlProof.cell?_ref (M := M) u
  have hcp := ControlProof.cell?_ref (M := M) p
  apply Expansion.weakParent_iff_twoLeg.mpr
  simp only [Reserve.rawParent, Option.bind_eq_bind, Option.bind_eq_some_iff] at hraw
  obtain ⟨col, hcol, up, hup, hleft⟩ := hraw
  obtain ⟨colu, hcolu, hcellu⟩ := cell?_spec hcu
  have hcc : colu = col := Option.some.inj (hcolu.symm.trans hcol)
  subst hcc
  obtain ⟨colp, hcolp, hcellp⟩ := cell?_spec hcp
  refine ⟨colu, _, up, _, hcolu, hcellu, hup, hleft, hlt, ⟨colp, hcolp, hcellp⟩, ?_⟩
  simpa [Frame.height] using hh

/-! ## Paths of numerical parents at one row -/

theorem parentPath_column_le {F : Frame} (hF : F.Ordered) {u p : F.Node}
    (h : Frame.ParentPath F u p) : p.1.val ≤ u.1.val := by
  induction h with
  | refl _ => exact le_rfl
  | cons hp _ ih => exact le_trans ih (Frame.P_column_lt hF hp).le

/-- **Along a path of numerical parents at one row, the ascension test is the test from the
end.** -/
theorem reachesRoot_path {s : List Nat} {M : Mountain} (hb : Canonical.build s = .ok M)
    {cr : Nat} {u p : (Frame.ofMountain M).Node} (h : Frame.ParentPath (Frame.ofMountain M) u p) :
    (Frame.ofMountain M).height p = (Frame.ofMountain M).height u → cr ≤ p.1.val →
      reachesRoot M cr ((Frame.ref u).column + 1) (Frame.ref u) =
        reachesRoot M cr ((Frame.ref p).column + 1) (Frame.ref p) := by
  have hO := (build_normal_of_success hb).toOrdered
  induction h with
  | refl u => intro _ _; rfl
  | @cons u q p hP rest ih =>
      intro hh hcr
      have h1 := Frame.P_height_le hO hP
      have h2 := parentPath_height_le hO rest
      have hq : (Frame.ofMountain M).height q = (Frame.ofMountain M).height u :=
        le_antisymm h1 (by rw [← hh]; exact h2)
      have hw := weakParent_of_P hb hP hq
      have hlt := Frame.P_column_lt hO hP
      have hle := parentPath_column_le hO rest
      have hcu : (Frame.ref u).column = u.1.val := rfl
      have hcq : (Frame.ref q).column = q.1.val := rfl
      rw [reachesRoot_step (by rw [hcu]; omega) hw,
        reachesRoot_fuel _ ((Frame.ref q).column + 1) _ (by rw [hcq, hcu]; omega) (by omega)]
      exact ih (by rw [hh, hq]) hcr

/-! ## The statement -/

/-- A real node of a column is the node found at its official row. -/
theorem nodeAt_of_cell {M : Mountain} (hV : MountainValid M) {p : Ref} {c : Cell}
    (hc : cell? M p = some c) (h1 : 1 ≤ p.index) :
    nodeAt M p.column (official c.row) = some (p, c) := by
  have hmem := CopyShape.mem_realNodes_of_cell' hc h1
  obtain ⟨p', hp'⟩ := Recon.RowLaw.nodeAt_of_mem hmem
  obtain ⟨hmem', hrow'⟩ := Recon.RowLaw.nodeAt_spec hp'
  simp only at hp' hrow'
  have := realNodes_eq_of_official hV hmem' hmem hrow'
  rw [this] at hp'
  exact hp'

/-- **The leg of a node passes the ascension test of its row.** -/
theorem ascLeg {s : List Nat} {M : Mountain} (hb : Canonical.build s = .ok M) {cr x : Nat}
    (hx : cr < x) {C : Row} {ref : Ref} {cl : Cell}
    (hn : nodeAt M x (referenceRow C) = some (ref, cl))
    (hr : reachesRoot M cr (x + 1) ref = .ok true)
    {csRef : Ref} {cs : Cell} (hcs : nodeAt M x C = some (csRef, cs)) {l : Ref}
    (hl : cs.left = some l) (hlcr : cr < l.column) :
    ∃ ref' cl', nodeAt M l.column (referenceRow C) = some (ref', cl') ∧
      reachesRoot M cr (l.column + 1) ref' = .ok true := by
  have hV := build_valid_of_success hb
  obtain ⟨hmem, hrow⟩ := Recon.RowLaw.nodeAt_spec hn
  obtain ⟨hcolx, hidx⟩ := Recon.RowLaw.realNodes_column hmem
  simp only at hcolx hidx hrow
  have hax : cr < ref.column := by rw [hcolx]; exact hx
  obtain ⟨q, hw, hrq⟩ := reachesRoot_next hax hr
  obtain ⟨col, cell', upper, parentCell, hcol, hcell, hup, hleft, hpc, hprow⟩ :=
    Recon.RowLaw.weakParent_some hw
  have hc0 : cell? M ref = some cell' := by simp [cell?, hcol, hcell]
  have hcl0 : cl = cell' := by
    have := (mem_realNodes (M := M) hmem).2.2
    exact Option.some.inj (this.symm.trans hc0)
  subst hcl0
  obtain ⟨colq, hcolq, hcq⟩ := cellAt_ok_iff.mp hpc
  have hcellq : cell? M q = some parentCell := by simp [cell?, hcolq, hcq]
  have hc'1 : (1 : Row) ≤ cl.row := one_le_row hV hc0 hidx
  have hq1 : (1 : Row) ≤ parentCell.row := by rw [hprow]; exact hc'1
  have hqidx := index_pos_of_one_le hV hcellq hq1
  have hqlt : q.column < ref.column := Expansion.weakParent_column_lt hw
  have hcrq : cr ≤ q.column := reachesRoot_column hrq
  obtain ⟨hrx, hr1, hcscell, hcsrow⟩ := Classification.nodeAt_spec hcs
  simp only at hrx hr1 hcscell hcsrow
  by_cases h0 : 0 < C.coeff 0
  · -- `(x, C)` is the node above `(x, Z)`, and its leg is `q`
    have hcup : cell? M (Inner.up ref) = some upper := by simp [cell?, Inner.up, hcol, hup]
    have hraw : Reserve.rawParent M ref = some q := by
      simp only [Reserve.rawParent, hcol, Option.bind_eq_bind, Option.bind_some, hup, hleft]
    have hB := Inner.canon_rowLaw hb (by omega) hc0 hcup hleft hcellq
    rw [hprow, Row.B_self] at hB
    have hupRow : official upper.row = C := by
      rw [hB, Recon.RowLaw.official_bump hc'1 0, hrow]
      exact Recon.RowLaw.referenceRow_bump h0
    have hup1 : (1 : Row) ≤ upper.row := one_le_row hV hcup (by simp [Inner.up])
    have hcs1 : (1 : Row) ≤ cs.row := one_le_row hV hcscell hr1
    have hupcs : upper.row = cs.row :=
      official_inj' hup1 hcs1 (by rw [hupRow, hcsrow])
    have hupr : Inner.up ref = csRef := by
      have hcol' : (Inner.up ref).column = csRef.column := by simp [Inner.up, hcolx, hrx]
      exact Inner.cell?_eq_of_index hV hcol' hcup hcscell hupcs
    have hlq : l = q := by
      rw [← hupr] at hcscell
      have hcu' : cs = upper := Option.some.inj (hcscell.symm.trans hcup)
      subst hcu'
      exact Option.some.inj (hl.symm.trans hleft)
    subst hlq
    refine ⟨l, parentCell, ?_, ?_⟩
    · have := nodeAt_of_cell hV hcellq (by omega)
      rw [← hrow, ← hprow]
      exact this
    · rw [reachesRoot_fuel _ x _ (by omega) (by omega)]
      exact hrq
  · -- `Z = C`: `q` is the raw parent of `(x, C)`, at the row `C`
    have hZ : referenceRow C = C := by
      unfold referenceRow
      rw [if_neg h0]
    rw [hZ] at hn
    rw [hn] at hcs
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hcs)
    have hraw : Reserve.rawParent M ref = some q := by
      simp only [Reserve.rawParent, hcol, Option.bind_eq_bind, Option.bind_some, hup, hleft]
    -- the frame
    have hF := build_normal_of_success hb
    have hO := hF.toOrdered
    obtain ⟨nu, hnu, hcellnu⟩ := ControlProof.node_of_cell? hc0
    have h1 := ControlProof.rawParent_ref (M := M) nu
    rw [hnu, hraw] at h1
    cases hupF : (Frame.ofMountain M).upper nu with
    | none => rw [hupF] at h1; cases h1
    | some v =>
      rw [hupF, Option.bind_some] at h1
      obtain ⟨np, hlk, _, _⟩ := hO.stored_valid v q h1.symm
      have hnp : Frame.ref np = q := Frame.lookup_spec hlk
      have hleft' : ((Frame.ofMountain M).cell v).left = some (Frame.ref np) := by
        rw [hnp]
        exact h1.symm
      have hrawF := Frame.rawParent_eq_of_upper_left hupF hleft'
      have hReal : Frame.Real nu := by
        show 0 < nu.2.val
        have : ref.index = nu.2.val := by rw [← hnu]; rfl
        omega
      have hP : (Frame.ofMountain M).P nu = some np :=
        (hF.rawParent_eq_P hReal).symm.trans hrawF
      obtain ⟨qq, hQ, hit⟩ := (Frame.P_iff hO).mp hP
      obtain ⟨left, hls, _, _, hqc, _, hqh, _⟩ := Frame.Q_spec hO hQ
      have hl' : ((Frame.ofMountain M).cell nu).left = some l := by rw [hcellnu]; exact hl
      have hlref : Frame.ref left = l := Option.some.inj (hls.symm.trans hl')
      -- the heights along the search
      have hhnp : (Frame.ofMountain M).height np = cl.row := by
        have := ControlProof.cell?_ref (M := M) np
        rw [hnp, hcellq] at this
        simp only [Frame.height]
        rw [← Option.some.inj this, hprow]
      have hhnu : (Frame.ofMountain M).height nu = cl.row := by
        simp only [Frame.height, hcellnu]
      -- the start of the search is at the row `C`
      have hh := hit.height_le hO
      have hqqh : (Frame.ofMountain M).height qq = cl.row :=
        le_antisymm (hqh.trans hhnu.le) (by rw [← hhnp]; exact hh)
      have hcqq := ControlProof.cell?_ref (M := M) qq
      have hqq1 : (1 : Row) ≤ ((Frame.ofMountain M).cell qq).row := by
        have : ((Frame.ofMountain M).cell qq).row = cl.row := hqqh
        rw [this]; exact hc'1
      have hqqidx := index_pos_of_one_le hV hcqq hqq1
      have hqqR : Frame.Real qq := hqqidx
      have hpath := Frame.Hit.parentPath hO (hO.real_positive qq hqqR) hit
      have hqqcol : (Frame.ref qq).column = l.column := by
        rw [← hlref]
        show qq.1.val = left.1.val
        rw [hqc]
      have hcrnp : cr ≤ np.1.val := by
        have : (Frame.ref np).column = np.1.val := rfl
        rw [← this, hnp]; exact hcrq
      have hreach := reachesRoot_path hb hpath (by rw [hhnp, hqqh]) hcrnp
      refine ⟨Frame.ref qq, (Frame.ofMountain M).cell qq, ?_, ?_⟩
      · have hq := nodeAt_of_cell hV hcqq hqqidx
        rw [hqqcol] at hq
        have hrowqq : official ((Frame.ofMountain M).cell qq).row = referenceRow C := by
          rw [← hrow]
          exact congrArg official hqqh
        rw [← hrowqq]
        exact hq
      · rw [← hqqcol, hreach, hnp, reachesRoot_fuel _ x _ (by omega) (by omega)]
        exact hrq

end OmegaY.Official.Classification.Proofs.CutGap
