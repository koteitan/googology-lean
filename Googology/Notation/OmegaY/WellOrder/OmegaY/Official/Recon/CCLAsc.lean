/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/CCLAsc.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.CCLBase
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CutGapAscLeg
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CutPartsPaRow
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.StepInnerCleanParent
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.RowLawSource
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.RowLawRows

set_option backward.do.legacy false

set_option autoImplicit false

/-!
# `AscCarry` (`CCL`, part (b))

`v = (x, a)`, `v' = (y, b)` of row `C` with the same stored left end `L`, and the column `x`
ascends at a root top `ρ` of row `C`: the node `w` of `x` at the reference row `Z` of `C` passes
its in-row parents to the root column. Two cases.

* `w ≠ v` (then `Z < C`, the finite coefficient of `C` is positive): the row law of the node
  above `w` (`upper_step`: `row w⁺ = B(row w, row P(w))`, and `row P(w) = row w`) gives
  `row w⁺ = Z + 1 = C`, so `w⁺ = v` and `P(w) = L`. For `v'`, the node `v'⁻` below it has
  `P(v'⁻) = L`; if `row v'⁻ ≠ row L`, the row law would give `v'` a zero finite coefficient. So
  `v'⁻` is the node of `y` at `Z`, its in-row parent is `L`, and `y` ascends.
* `w = v` (`Z = C`): `v` is not the top of `x`, so by the condition the nodes above `v`, `v'` have
  left ends `l = P(v)` (of row `C`), `l' = P(v')` with `col l ≤ col l'`. Both are found from the
  same candidate `Q(v) = Q(v')` (same left end, same row) along the numerical parents
  (`Hit.parentPath`), so `l'` lies on the path of numerical parents to `l`; its row is between
  `row l = C` and `row Q(v) ≤ C`, so `l'` is the in-row parent of `v'`, and the test from `v'`
  is the test from `l` (`reachesRoot_path`).

## Result

* `ascCarry : AscCarry`.
-/

namespace OmegaY.Official.Recon.CCL

open Canonical Expansion Geometry Frame Classification
open Reserve (cell?)
open Classification.Proofs.CopyShape.ProfileLeg (AscRow)

/-! ## Tools -/

theorem ascends_of_clean {ctx : Context} {r : Ref} {cl : Cell} {ref : Ref} {cw : Cell}
    (hn : nodeAt ctx.source ctx.x (referenceRow (official cl.row)) = some (ref, cw))
    (hr : reachesRoot ctx.source ctx.rootColumn (ctx.x + 1) ref = .ok true) :
    ascends ctx (some (r, cl)) = .ok true := by
  unfold ascends
  simp only [hn]
  exact hr

/-- `Q` depends only on the stored left end and the height. -/
theorem Q_congr {F : Frame} {u u' : F.Node} (hl : (F.cell u).left = (F.cell u').left)
    (hh : F.height u = F.height u') : F.Q u = F.Q u' := by
  have he : ∀ left, F.eligible u left = F.eligible u' left := by
    intro left
    unfold Frame.eligible
    rw [hh]
  unfold Frame.Q
  rw [hl]
  simp only [he]

/-- **Paths of numerical parents from one node are nested.** -/
theorem parentPath_tail {F : Frame} (hF : F.Ordered) {a b c : F.Node}
    (hab : Frame.ParentPath F a b) (hac : Frame.ParentPath F a c) (hcb : c.1.val ≤ b.1.val) :
    Frame.ParentPath F b c := by
  induction hab with
  | refl _ => exact hac
  | @cons a a' b hP rest ih =>
    cases hac with
    | refl _ =>
      exfalso
      have h1 := rest.column_le hF
      have h2 := Frame.P_column_lt hF hP
      omega
    | cons hP' rest' =>
      rw [hP] at hP'
      obtain rfl := Option.some.inj hP'
      exact ih rest' hcb

section Mnt

variable {M : Mountain}

theorem node_col {u : (Frame.ofMountain M).Node} {r : Ref} (h : Frame.ref u = r) :
    u.1.val = r.column := by
  rw [← h]; rfl

theorem node_idx {u : (Frame.ofMountain M).Node} {r : Ref} (h : Frame.ref u = r) :
    u.2.val = r.index := by
  rw [← h]; rfl

/-- The node above a node, from the cell above it. -/
theorem upper_node {u : (Frame.ofMountain M).Node} {c : Cell}
    (h : cell? M ⟨u.1.val, u.2.val + 1⟩ = some c) :
    ∃ v, (Frame.ofMountain M).upper u = some v ∧ Frame.ref v = ⟨u.1.val, u.2.val + 1⟩ ∧
      (Frame.ofMountain M).cell v = c := by
  obtain ⟨v, hv, hvc⟩ := ControlProof.node_of_cell? h
  have hc : v.1 = u.1 := Fin.ext (node_col hv)
  have hi : v.2.val = u.2.val + 1 := node_idx hv
  exact ⟨v, ControlProof.upper_eq_of_index hc.symm hi, hv, hvc⟩

theorem cell_of_col {r : Ref} {col : Column} {c : Cell} (hcol : M[r.column]? = some col)
    (hc : col[r.index]? = some c) : cell? M r = some c := by
  simp [cell?, hcol, hc]

theorem cell_of_cellAt {r : Ref} {c : Cell} (h : cellAt M r = .ok c) : cell? M r = some c := by
  obtain ⟨col, hcol, hc⟩ := cellAt_ok_iff.mp h
  exact cell_of_col hcol hc

end Mnt

/-! ## The theorem -/

theorem ascCarry : AscCarry := by
  intro s n R hrun M t root hTop i x y hi0 hin hxb hyb a b cv cv' ha hb hcv hcv' hrow hτ hleft
    habove hA
  obtain ⟨d, S, ρ, hρ, hρrow, hasc⟩ := hA
  refine ⟨d, S, ρ, hρ, hρrow, ?_⟩
  have hcr := hTop.lt
  obtain ⟨hxg, hxl⟩ := mem_blockColumns hcr hxb
  obtain ⟨hyg, hyl⟩ := mem_blockColumns hcr hyb
  have hbld := hTop.build
  have hN := build_normal_of_success hbld
  have hO := hN.toOrdered
  have hV := build_valid_of_success hbld
  obtain ⟨wr, cw, hnw, hrw⟩ := Classification.Proofs.ChainCorr.ascClean_of_ascends hasc
  change nodeAt M x (referenceRow (official ρ.2.row)) = some (wr, cw) at hnw
  change reachesRoot M root.column (x + 1) wr = .ok true at hrw
  obtain ⟨hwc, hw1, hcw, hwrow⟩ := Classification.nodeAt_spec hnw
  simp only at hwc hw1 hcw hwrow
  obtain ⟨q, hwq, hrq⟩ := Classification.Proofs.ChainCorr.CutParts.reachesRoot_next
    (by rw [hwc]; exact hxg) hrw
  have hqcr := Classification.Proofs.ChainCorr.reachesRoot_column hrq
  obtain ⟨col, cell, up, pc, hcol, hcell, hup, hupl, hpc, hpcrow⟩ := RowLaw.weakParent_some hwq
  have hcw' : cell = cw := by
    have := cell_of_col hcol hcell
    exact Option.some.inj (this.symm.trans hcw)
  subst cell
  have hcup : cell? M ⟨wr.column, wr.index + 1⟩ = some up := cell_of_col hcol hup
  have hcq : cell? M q = some pc := cell_of_cellAt hpc
  -- the frame nodes
  obtain ⟨nw, hnwr, hnwc⟩ := ControlProof.node_of_cell? hcw
  have hnwcol : nw.1.val = x := by rw [node_col hnwr, hwc]
  have hnwidx : nw.2.val = wr.index := node_idx hnwr
  have hnwR : Frame.Real nw := by show 0 < nw.2.val; omega
  obtain ⟨nwu, hnwu, hnwur, hnwuc⟩ := upper_node (u := nw) (by rw [hnwcol, hnwidx, ← hwc]; exact hcup)
  obtain ⟨pw, hPw, hBw, _, hleftw⟩ := hN.upper_step nw nwu hnwR hnwu
  have hpwq : Frame.ref pw = q := by
    have : ((Frame.ofMountain M).cell nwu).left = some q := by rw [hnwuc]; exact hupl
    exact Option.some.inj (hleftw.symm.trans this)
  have hpwh : (Frame.ofMountain M).height pw = (Frame.ofMountain M).height nw := by
    have e1 : (Frame.ofMountain M).cell pw = pc := by
      have := ControlProof.cell?_ref (M := M) pw
      rw [hpwq, hcq] at this
      exact (Option.some.inj this).symm
    show ((Frame.ofMountain M).cell pw).row = ((Frame.ofMountain M).cell nw).row
    rw [e1, hnwc]; exact hpcrow
  obtain ⟨nv, hnvr, hnvc⟩ := ControlProof.node_of_cell? hcv
  obtain ⟨nv', hnvr', hnvc'⟩ := ControlProof.node_of_cell? hcv'
  have hnvcol : nv.1.val = x := node_col hnvr
  have hnvidx : nv.2.val = a := node_idx hnvr
  have hnvcol' : nv'.1.val = y := node_col hnvr'
  have hnvidx' : nv'.2.val = b := node_idx hnvr'
  have hnvR : Frame.Real nv := by show 0 < nv.2.val; omega
  have hnvR' : Frame.Real nv' := by show 0 < nv'.2.val; omega
  have hcv1 : (1 : Row) ≤ cv.row := Classification.one_le_row hV hcv ha
  have hcv1' : (1 : Row) ≤ cv'.row := Classification.one_le_row hV hcv' hb
  have hcw1 : (1 : Row) ≤ cw.row := Classification.one_le_row hV hcw hw1
  -- `v'` is the node of `y` at its official row
  have hnv'at : nodeAt M y (official cv'.row) = some (⟨y, b⟩, cv') :=
    Classification.Proofs.CutGap.nodeAt_of_cell hV hcv' hb
  by_cases hwv : wr.index = a
  · ------------------------------------------------------------------
    -- `w = v`: the reference row is the row of `v`
    have hwr : wr = ⟨x, a⟩ := by cases wr; simp only at hwc hwv; subst hwc hwv; rfl
    subst hwr
    have hcc : cw = cv := Option.some.inj (hcw.symm.trans hcv)
    subst hcc
    have hnn : nw = nv := ControlProof.node_eq_of_index (Fin.ext (by rw [hnwcol, hnvcol]))
      (by rw [hnwidx, hnvidx])
    subst hnn
    -- the nodes above
    rcases habove with hnone | ⟨cu, cu', l, l', hcu, hcu', hl, hl', hll⟩
    · simp only at hcup; rw [hcup] at hnone; cases hnone
    have hcuu : cu = up := Option.some.inj (hcu.symm.trans hcup)
    subst hcuu
    have hlq : l = q := Option.some.inj (hl.symm.trans hupl)
    subst l
    -- `P(v') = l'`
    have hraw' : Reserve.rawParent M (Frame.ref nv') = some l' := by
      rw [hnvr', RPLLex.rawParent_eq_cell, hcu']; exact hl'
    obtain ⟨pv', hPv', hpv'r⟩ := Classification.Proofs.ChainCorr.Inner.Clean.P_of_rawParent hN hnvR'
      hraw'
    -- the common candidate
    have hQeq : (Frame.ofMountain M).Q nw = (Frame.ofMountain M).Q nv' := by
      apply Q_congr
      · rw [hnwc, hnvc']; exact hleft
      · show ((Frame.ofMountain M).cell nw).row = ((Frame.ofMountain M).cell nv').row
        rw [hnwc, hnvc']; exact hrow
    obtain ⟨q0, hQ0, hit0⟩ := (P_iff hO).mp hPw
    obtain ⟨q0', hQ0', hit0'⟩ := (P_iff hO).mp hPv'
    rw [hQeq, hQ0'] at hQ0
    obtain rfl := Option.some.inj hQ0
    have hq0R : Frame.Real q0' := Q_real hO hnvR' hQ0'
    have hq0pos := hO.real_positive q0' hq0R
    have hpath := hit0.parentPath hO hq0pos
    have hpath' := hit0'.parentPath hO hq0pos
    have hcolle : pw.1.val ≤ pv'.1.val := by
      rw [node_col hpwq, node_col hpv'r]; exact hll
    have hpp := parentPath_tail hO hpath' hpath hcolle
    -- heights
    have hh1 : (Frame.ofMountain M).height pw ≤ (Frame.ofMountain M).height pv' :=
      Classification.Proofs.ChainCorr.CutParts.parentPath_height_le hO hpp
    have hh2 : (Frame.ofMountain M).height pv' ≤ (Frame.ofMountain M).height q0' :=
      hit0'.height_le hO
    have hh3 : (Frame.ofMountain M).height q0' ≤ (Frame.ofMountain M).height nv' :=
      Q_height_le hO hQ0'
    have hvv' : (Frame.ofMountain M).height nw = (Frame.ofMountain M).height nv' := by
      show ((Frame.ofMountain M).cell nw).row = ((Frame.ofMountain M).cell nv').row
      rw [hnwc, hnvc']; exact hrow
    have hpv'h : (Frame.ofMountain M).height pv' = (Frame.ofMountain M).height nv' := by
      apply le_antisymm (hh2.trans hh3)
      rw [← hvv', ← hpwh]; exact hh1
    have hwp' := Classification.Proofs.CutGap.weakParent_of_P hbld hPv' hpv'h
    rw [hnvr', hpv'r] at hwp'
    -- the test from `v'`
    have hpcr : root.column ≤ pw.1.val := by rw [node_col hpwq]; exact hqcr
    have hpath_eq := Classification.Proofs.CutGap.reachesRoot_path hbld (cr := root.column) hpp
      (hpv'h.trans hvv'.symm |>.trans hpwh.symm |>.symm) hpcr
    rw [hpv'r, hpwq] at hpath_eq
    have hpl' : l'.column < y := by
      rw [← hpv'r, ← hnvcol']; exact Frame.P_column_lt hO hPv'
    have hql : q.column < x := by
      rw [← hpwq, ← hnvcol]; exact Frame.P_column_lt hO hPw
    apply ascends_of_clean (ref := ⟨y, b⟩) (cw := cv')
    · change nodeAt M y (referenceRow (official ρ.2.row)) = some (⟨y, b⟩, cv')
      rw [← hwrow, hrow]; exact hnv'at
    · change reachesRoot M root.column (y + 1) ⟨y, b⟩ = .ok true
      rw [Classification.Proofs.CutGap.reachesRoot_step (show root.column < (⟨y, b⟩ : Ref).column
        from hyg) hwp']
      rw [Classification.Proofs.CutGap.reachesRoot_fuel y (l'.column + 1) l' hpl' (by omega),
        hpath_eq, Classification.Proofs.CutGap.reachesRoot_fuel (q.column + 1) x q (by omega) hql]
      exact hrq
  · ------------------------------------------------------------------
    -- `w ≠ v`: the reference row is below the row of `v`
    have hnwuh : (Frame.ofMountain M).height nwu = Row.bump cw.row 0 := by
      rw [hBw, hpwh]
      show Row.B ((Frame.ofMountain M).cell nw).row ((Frame.ofMountain M).cell nw).row = _
      rw [hnwc, Row.B_self]
    -- the reference row differs from `C`
    have hZC : referenceRow (official ρ.2.row) ≠ official ρ.2.row := by
      intro heq
      apply hwv
      have h1 : nodeAt M x (official cv.row) = some (⟨x, a⟩, cv) :=
        Classification.Proofs.CutGap.nodeAt_of_cell hV hcv ha
      rw [heq, hρrow] at hnw
      rw [hnw] at h1
      have := congrArg (fun p => p.1.index) (Option.some.inj h1)
      simpa using this
    have hpos : 0 < (official ρ.2.row).coeff 0 := by
      by_contra hn
      apply hZC
      unfold referenceRow
      rw [if_neg hn]
    have hbumpZ : Row.bump (referenceRow (official ρ.2.row)) 0 = official ρ.2.row :=
      RowLaw.referenceRow_bump hpos
    -- `w⁺ = v`
    have hoff : official ((Frame.ofMountain M).height nwu) = official cv.row := by
      rw [hnwuh, RowLaw.official_bump hcw1, hwrow, hbumpZ, hρrow]
    have hnwuv : Frame.ref nwu = ⟨x, a⟩ := by
      have hc1 : cell? M (Frame.ref nwu) = some ((Frame.ofMountain M).cell nwu) :=
        ControlProof.cell?_ref nwu
      have hidx : 1 ≤ (Frame.ref nwu).index := by rw [hnwur]; simp
      have h1 := Classification.Proofs.CutGap.nodeAt_of_cell hV hc1 hidx
      have h2 : nodeAt M x (official cv.row) = some (⟨x, a⟩, cv) :=
        Classification.Proofs.CutGap.nodeAt_of_cell hV hcv ha
      have hcol1 : (Frame.ref nwu).column = x := by rw [hnwur]; exact hnwcol
      rw [hcol1] at h1
      change nodeAt M x (official ((Frame.ofMountain M).height nwu)) = _ at h1
      rw [hoff, h2] at h1
      exact (congrArg Prod.fst (Option.some.inj h1)).symm
    have hnwuc' : (Frame.ofMountain M).cell nwu = cv := by
      have := ControlProof.cell?_ref (M := M) nwu
      rw [hnwuv, hcv] at this
      exact (Option.some.inj this).symm
    have hLq : cv.left = some q := by rw [← hnwuc', hleftw, hpwq]
    -- the node below `v'`
    have hL' : cv'.left = some q := by rw [← hleft]; exact hLq
    have hb2 : 2 ≤ b := by
      by_contra hn
      have hb1 : (⟨y, b⟩ : Ref).index = 1 := by show b = 1; omega
      have := Classification.bottom_left hbld hcv' hb1 (by show y ≠ 0; omega)
      rw [hL'] at this
      have hqi : q.index = 0 := by rw [Option.some.inj this]
      have hpwR : Frame.Real pw := real_of_value_pos hO (P_value hO hPw).1
      have : pw.2.val = q.index := node_idx hpwq
      unfold Frame.Real at hpwR
      omega
    have hcb : ∃ cb, cell? M ⟨y, b - 1⟩ = some cb := by
      obtain ⟨colv, hcolv, hcv2⟩ := cell?_spec hcv'
      have hlt : b < colv.size := by
        rcases Array.getElem?_eq_some_iff.mp hcv2 with ⟨h, _⟩
        exact h
      exact ⟨colv[b - 1], cell_of_col hcolv (Array.getElem?_eq_getElem (by show b - 1 < colv.size; omega))⟩
    obtain ⟨cb, hcb⟩ := hcb
    obtain ⟨nb, hnbr, hnbc⟩ := ControlProof.node_of_cell? hcb
    have hnbcol : nb.1.val = y := node_col hnbr
    have hnbidx : nb.2.val = b - 1 := node_idx hnbr
    have hnbR : Frame.Real nb := by show 0 < nb.2.val; omega
    have hnbu : (Frame.ofMountain M).upper nb = some nv' :=
      ControlProof.upper_eq_of_index (Fin.ext (by rw [hnbcol, hnvcol'])) (by rw [hnvidx', hnbidx]; omega)
    obtain ⟨p2, hP2, hB2, _, hleft2⟩ := hN.upper_step nb nv' hnbR hnbu
    have hp2q : Frame.ref p2 = q := by
      have : ((Frame.ofMountain M).cell nv').left = some q := by rw [hnvc']; exact hL'
      exact Option.some.inj (hleft2.symm.trans this)
    have hp2pw : p2 = pw := by
      have := hp2q.trans hpwq.symm
      exact ControlProof.node_eq_of_index (Fin.ext (by
        have h1 := congrArg Canonical.Ref.column this; simpa [Frame.ref] using h1))
        (by have h1 := congrArg Canonical.Ref.index this; simpa [Frame.ref] using h1)
    subst hp2pw
    -- the height of `v'⁻` is the height of `L`
    have hnbh : (Frame.ofMountain M).height nb = (Frame.ofMountain M).height p2 := by
      by_contra hne
      have hj : Row.jump ((Frame.ofMountain M).height nb) ((Frame.ofMountain M).height p2) ≠ 0 := by
        intro h0
        exact hne (Row.jump_eq_zero.mp h0)
      have h0 : ((Frame.ofMountain M).height nv').coeff 0 = 0 := by
        rw [hB2]
        unfold Row.B
        exact Row.coeff_bump_low (by omega)
      have h1 : ((Frame.ofMountain M).height nv').coeff 0 = cw.row.coeff 0 + 1 := by
        have : (Frame.ofMountain M).height nv' = (Frame.ofMountain M).height nwu := by
          show ((Frame.ofMountain M).cell nv').row = ((Frame.ofMountain M).cell nwu).row
          rw [hnvc', hnwuc']; exact hrow.symm
        rw [this, hnwuh, Row.coeff_bump_at]
      omega
    have hwp2 := Classification.Proofs.CutGap.weakParent_of_P hbld hP2 hnbh.symm
    rw [hnbr, hp2q] at hwp2
    have hnbrow : official cb.row = official cw.row := by
      have : cb.row = cw.row := by
        have e1 : (Frame.ofMountain M).height nb = cb.row := by
          show ((Frame.ofMountain M).cell nb).row = cb.row; rw [hnbc]
        rw [← e1, hnbh, hpwh]
        show ((Frame.ofMountain M).cell nw).row = cw.row; rw [hnwc]
      rw [this]
    have hnbat : nodeAt M y (official cb.row) = some (⟨y, b - 1⟩, cb) :=
      Classification.Proofs.CutGap.nodeAt_of_cell hV hcb (by show 1 ≤ b - 1; omega)
    have hql : q.column < x := by
      rw [← hpwq]; have := Frame.P_column_lt hO hPw; rw [hnwcol] at this; exact this
    have hqy : q.column < y := by
      rw [← hpwq]; have := Frame.P_column_lt hO hP2; rw [hnbcol] at this; exact this
    apply ascends_of_clean (ref := ⟨y, b - 1⟩) (cw := cb)
    · change nodeAt M y (referenceRow (official ρ.2.row)) = some (⟨y, b - 1⟩, cb)
      rw [← hwrow, ← hnbrow]; exact hnbat
    · change reachesRoot M root.column (y + 1) ⟨y, b - 1⟩ = .ok true
      rw [Classification.Proofs.CutGap.reachesRoot_step (show root.column < (⟨y, b - 1⟩ : Ref).column
        from hyg) hwp2]
      rw [Classification.Proofs.CutGap.reachesRoot_fuel y x q hqy hql]
      exact hrq

end OmegaY.Official.Recon.CCL

#print axioms OmegaY.Official.Recon.CCL.ascCarry
