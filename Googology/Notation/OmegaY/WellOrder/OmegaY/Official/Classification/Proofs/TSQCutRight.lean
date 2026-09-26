/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/TSQCutRight.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
Port change: in `topNode_cutRight` the rewrites `[hgq, hlj] at hgapq` and `[hgq, hqo]` use `erw` instead of `rw` (the list indices `(lo' ++ us')[gi]` and `(lo ++ us)[j]` are elaborated with bound proofs that `rw` does not identify).
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.TopStartFixParts
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CutPartsPaRow
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.P3TRunTop
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CopyShapeFinal

set_option backward.do.legacy false

set_option autoImplicit false

/-!
# `TopStartCutRight` from one statement about gap copies (`TSQ`)

`TopStartCutRight` (`TopStartFixParts.lean`): `u = (X, j + 1)` (`X = x + w·i`, block `i ≥ 1`) is
the top copy of its origin `o = (x, C)` and a gap copy, the leg `l` of `o` is right of `c_r`, and
`row o < row t`. With `pa = hAM_M(l, C)` and `pe = hAM_R(l + w·i, row u)`: `Rel pe pa`, and
`TopNode pe pa` when `o` has a node above it below `row t`. Here `TopNode pe pa` is proved
outright (so also `Rel pe pa`), from one open statement:

* `CutTopGap` (**open**, numerically checked): every gap copy of `pa` in the copied column `l`
  (block `i`) is at or below the row of `u`.

## The argument

* `pa` is at the row `C` (`paRow_diag`: the argument of `CutParts.paRow_of_clean`, for the
  diagram of a run; the origin of a copy of the root row passed its ascension test).
* The column `l` has a gap copy `q` of `pa` at a row `≥ row u` (`P3T.run_top_core`, proved).
  With `CutTopGap`, `row q = row u`, so the node `G` of `q` in `L = l + w·i` is at the row of
  `u` and `pe = G`.
* No copy of `pa` lies above `G` in `L`: a gap copy is at or below `row u` (`CutTopGap`), a
  non-gap copy strictly below (`CopyShape.Final.cutBetweenLeg`, proved: the origin rows of `u`
  and of the copy are both `C`), and an upper copy would have its origin at or above `τ`.
* The last clause of `TopNode` is empty: `row pa = C < row t`.

Results: `topNode_cutRight`, `topStartCutRight_of_gap : CutTopGap → TopStartCutRight`.
-/

namespace OmegaY.Official.Classification.Proofs.ChainCorr.CutParts.TSQ

open Canonical Reserve Official Descent Classification Proofs

/-- **The node `pa` of a copy of the root row is at the row of the origin**, in the diagram of
a run (`CutParts.paRow_of_clean` without the canonicity of the output). -/
theorem paRow_diag {s : List Nat} {M R : Mountain} (hb : Canonical.build s = .ok M)
    {cr x i w x0 X : Nat} (hcx : cr < x) {τ : Row} {es : List (Emit × Origin)}
    (hes : emitsT (ctxAt M R x i cr w x0 X) τ = .ok es) {j : Nat} (hj : j < es.length)
    {r : Ref} {b : Bool} (ho : es[j].2 = .clean r b) {cv : Cell} {l pa : Ref} {cpa : Cell}
    (hcv0 : cell? M es[j].2.src = some cv) (hl : cv.left = some l)
    (hpa : highestAtMost M l.column cv.row = some pa) (hcpa : cell? M pa = some cpa) :
    cpa.row = cv.row := by
  have hV := build_valid_of_success hb
  obtain ⟨C, cs, hcs, ref0, cl0, hn, hr⟩ :=
    emitsT_cleanAsc hes es[j] (List.getElem_mem hj) r b ho
  obtain ⟨ρ0, hρ0, C', cs', hcs', hρrow⟩ :=
    emitsT_cleanRow hes es[j] (List.getElem_mem hj) r b ho
  simp only [ctxAt] at hcs hn hr hρ0 hcs'
  obtain ⟨hrx, hr1, hcscell, hcsrow⟩ := Classification.nodeAt_spec hcs
  obtain ⟨_, _, hcscell', hcsrow'⟩ := Classification.nodeAt_spec hcs'
  simp only at hrx hr1 hcscell hcsrow hcscell' hcsrow'
  have hccs : cs' = cs := Option.some.inj (hcscell'.symm.trans hcscell)
  subst cs'
  have hCC : C' = C := hcsrow'.symm.trans hcsrow
  subst C'
  have hsrc : es[j].2.src = r := by rw [ho]; rfl
  have hcv := hcv0
  rw [hsrc] at hcv
  have hcvs : cv = cs := Option.some.inj (hcv.symm.trans hcscell)
  subst cv
  have hcs1 : (1 : Row) ≤ cs.row := one_le_row hV hcscell hr1
  obtain ⟨hmem, hrow⟩ := Recon.RowLaw.nodeAt_spec hn
  obtain ⟨hcolx, hidx⟩ := Recon.RowLaw.realNodes_column hmem
  simp only at hcolx hidx hrow
  have hax : cr < ref0.column := by rw [hcolx]; exact hcx
  obtain ⟨q, hw, hq⟩ := weakParent_of_reachesRoot hax hr
  obtain ⟨col, cell', upper, parentCell, hcol, hcell, hup, hleft, hpc, hprow⟩ :=
    Recon.RowLaw.weakParent_some hw
  have hc0 : cell? M ref0 = some cell' := by simp [cell?, hcol, hcell]
  have hcl0 : cl0 = cell' := by
    have := (mem_realNodes (M := M) hmem).2.2
    exact Option.some.inj (this.symm.trans hc0)
  subst cl0
  have hcup : cell? M (Inner.up ref0) = some upper := by simp [cell?, Inner.up, hcol, hup]
  obtain ⟨colq, hcolq, hcq⟩ := cellAt_ok_iff.mp hpc
  have hcellq : cell? M q = some parentCell := by simp [cell?, hcolq, hcq]
  have hraw : Reserve.rawParent M ref0 = some q := by
    simp only [Reserve.rawParent, hcol, Option.bind_eq_bind, Option.bind_some, hup, hleft]
  have hc'1 : (1 : Row) ≤ cell'.row := one_le_row hV hc0 hidx
  by_cases h0 : 0 < C.coeff 0
  · suffices hw : ∃ w cw, w.column = l.column ∧ 0 < w.index ∧ cell? M w = some cw ∧
        cw.row = cs.row by
      obtain ⟨w, cw, hwc, hw0, hcw, hrow⟩ := hw
      exact hAM_row_of_node hV hpa hcpa hwc hw0 hcw hrow
    have hB := Inner.canon_rowLaw hb (by omega) hc0 hcup hleft hcellq
    rw [hprow, Row.B_self] at hB
    have hupRow : official upper.row = C := by
      rw [hB, Recon.RowLaw.official_bump hc'1 0, hrow]
      exact Recon.RowLaw.referenceRow_bump h0
    have hup1 : (1 : Row) ≤ upper.row := one_le_row hV hcup (by simp [Inner.up])
    have hupcs : upper.row = cs.row :=
      official_inj' hup1 hcs1 (by rw [hupRow, hcsrow])
    have hupr : Inner.up ref0 = r := by
      have hcol' : (Inner.up ref0).column = r.column := by simp [Inner.up, hcolx, hrx]
      exact Inner.cell?_eq_of_index hV hcol' hcup hcscell hupcs
    have hlq : l = q := by
      rw [← hupr] at hcscell
      have hcu' : cs = upper := Option.some.inj (hcscell.symm.trans hcup)
      subst hcu'
      exact Option.some.inj (hl.symm.trans hleft)
    subst l
    rcases Nat.lt_or_eq_of_le hq with hqlt | hqeq
    · obtain ⟨q', hw', hr'⟩ := reachesRoot_next hax hr
      have hqq : q' = q := by
        rw [hw] at hw'
        exact (Option.some.inj (Except.ok.inj hw')).symm
      subst q'
      obtain ⟨p2, hw2, _⟩ := weakParent_of_reachesRoot hqlt hr'
      obtain ⟨col2, cell2, upper2, par2, hcol2, hcell2, hup2, hleft2, hpc2, hprow2⟩ :=
        Recon.RowLaw.weakParent_some hw2
      have hc2 : cell? M q = some cell2 := by simp [cell?, hcol2, hcell2]
      have hc2e : cell2 = parentCell := Option.some.inj (hc2.symm.trans hcellq)
      subst cell2
      have hcup2 : cell? M (Inner.up q) = some upper2 := by simp [cell?, Inner.up, hcol2, hup2]
      obtain ⟨colp, hcolp, hcp⟩ := cellAt_ok_iff.mp hpc2
      have hcellp : cell? M p2 = some par2 := by simp [cell?, hcolp, hcp]
      have hq1 : (1 : Row) ≤ parentCell.row := by rw [hprow]; exact hc'1
      have hq0 := index_pos_of_one_le hV hcellq hq1
      have hB2 := Inner.canon_rowLaw hb hq0 hcellq hcup2 hleft2 hcellp
      rw [hprow2, Row.B_self] at hB2
      have hup2Row : official upper2.row = C := by
        rw [hB2, Recon.RowLaw.official_bump hq1 0, hprow, hrow]
        exact Recon.RowLaw.referenceRow_bump h0
      have hup21 : (1 : Row) ≤ upper2.row := one_le_row hV hcup2 (by simp [Inner.up])
      exact ⟨Inner.up q, upper2, rfl, by simp [Inner.up], hcup2,
        official_inj' hup21 hcs1 (by rw [hup2Row, hcsrow])⟩
    · obtain ⟨hρc, hρi⟩ := Recon.RowLaw.realNodes_column hρ0
      have hρcell := (mem_realNodes (M := M) hρ0).2.2
      have hρ1 : (1 : Row) ≤ ρ0.2.row := Recon.realNodes_row_one_le hV hρ0
      exact ⟨ρ0.1, ρ0.2, by rw [hρc, hqeq], by omega, hρcell,
        official_inj' hρ1 hcs1 (by rw [hCC, hcsrow])⟩
  · have hZ : referenceRow C = C := by
      unfold referenceRow
      rw [if_neg h0]
    rw [hZ] at hn
    rw [hn] at hcs
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hcs)
    have hle := rawParent_row_le_hAM hb hc0 (by omega) hl hpa hcpa hraw hcellq
    rw [hprow] at hle
    exact le_antisymm (hAM_row_le hpa hcpa) hle

end OmegaY.Official.Classification.Proofs.ChainCorr.CutParts.TSQ

namespace OmegaY.Official.Recon.TSQ

open Canonical Expansion Geometry Frame Classification
open CrossUpperSim CrossUpper
open Classification.Proofs.ChainCorr (MStep cutOrigin CopyNode)
open Classification.Proofs.ChainCorr.LowerChain (CopyOf TopNode Stand Rel above IsTopAt)
open Classification.Proofs.ChainCorr.TopStartFix (HasAboveLow)
open TopChain
open LowerChainRecon (node_of_cell)
open Classification.ControlProof (height_le_of_index height_lt_of_index node_eq_of_index
  upper_eq_of_index)

/-! ## The open statement -/

/-- **Open.** In the setting of `TopStartCutRight` (the top copy `u` of `o` is a gap copy, the leg
`l` of `o` is right of `c_r`, `row o < row t`), every gap copy of `pa` in the copied column `l`
of the block is at or below the row of `u`. -/
def CutTopGap : Prop :=
  ∀ (s : List Nat) (n : Nat) (R M : Mountain) (t : Cell) (root : Ref) (i x : Nat),
    Official.expandDiagram s n = .ok R → Recon.Top s M t root → 0 < i → i ≤ n →
    x ∈ blockColumns root.column (M.size - 1) n i →
    ∀ es, emitsT (ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1)
        (x + (M.size - 1 - root.column) * i)) (official t.row) = .ok es →
    ∀ j (hj : j < es.length), IsTopAt es j →
    ∀ cv l pa,
      Reserve.cell? M es[j].2.src = some cv → cv.left = some l →
      Reserve.highestAtMost M l.column cv.row = some pa →
      cv.row < t.row → root.column < l.column → cutOrigin es[j].2 = true →
      ∀ es', emitsT (ctxAt M R l.column i root.column (M.size - 1 - root.column) (M.size - 1)
          (l.column + (M.size - 1 - root.column) * i)) (official t.row) = .ok es' →
        ∀ j' (hj' : j' < es'.length), es'[j'].2 = .clean pa true → es'[j'].1.row ≤ es[j].1.row

/-! ## Tools -/

/-- A new column from its column data (as `SRT.nc_of_colData`). -/
theorem nc_of_colData' {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}
    (E : Env s n R M t root) {i x : Nat} {lo us : List (Emit × Origin)} (hi1 : 1 ≤ i)
    (hD : LowerPB.ColData s n R M t root (x + (M.size - 1 - root.column) * i) i x lo us) :
    JumpLaw.NewColumn s n R M t root i x := by
  have hcr := E.top.lt
  obtain ⟨hxg, hxl⟩ := mem_blockColumns hcr hD.xb
  have hwi : M.size - 1 - root.column ≤ (M.size - 1 - root.column) * i :=
    Nat.le_mul_of_pos_right _ hi1
  have hXR := hD.XR
  obtain ⟨i', x', hi', hx', hXeq, hcopy⟩ := E.CI.2.2 (x + (M.size - 1 - root.column) * i) hXR
    (by omega)
  obtain ⟨hii, hxx⟩ := Classification.Proofs.ChainCorr.NonTop.blockX_unique hcr hxg hxl hx'
    hXeq (by omega)
  subst hii hxx
  have hn0 : n ≠ 0 := by have := hD.iln; omega
  exact ⟨E.run, E.top, hn0, E.CI, hi', hD.xb, hXR, ⟨_, Array.getElem?_eq_getElem hXR, hcopy⟩⟩

/-- The origin of a gap copy. -/
theorem origin_of_cut {o : Origin} (h : cutOrigin o = true) : o = .clean o.src true := by
  cases o with
  | clean r b => cases b <;> simp_all [cutOrigin, Origin.src]
  | plain r => simp [cutOrigin] at h
  | upper r => simp [cutOrigin] at h

/-- An emit of the lower part of a copied column whose source is below `row t`. -/
theorem lower_index {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}
    {X i x : Nat} {lo us : List (Emit × Origin)}
    (hD : LowerPB.ColData s n R M t root X i x lo us) {j : Nat} (hj : j < (lo ++ us).length)
    {c : Cell} (hc : Reserve.cell? M (lo ++ us)[j].2.src = some c) (hlo : c.row < t.row) :
    j < lo.length := by
  have hVM := build_valid_of_success hD.top.build
  by_contra hn
  have hmemu : (lo ++ us)[j] ∈ us := by
    rw [List.getElem_append_right (by omega)]
    exact List.getElem_mem _
  obtain ⟨k, c', hk1, hc', hup, _, hτc, _⟩ := (LowerPB.upperT_spec hD.hus).1 _ hmemu
  have hs2 : (lo ++ us)[j].2.src =
      ⟨upperColumn (ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1) X), k⟩ := by
    rw [hup]; rfl
  rw [hs2] at hc
  have hcc : c' = c := Option.some.inj (hc'.symm.trans hc)
  subst hcc
  have := le_of_official_le (LowerPB.cell_row_one_le hVM hc hk1) hτc
  exact absurd (lt_of_le_of_lt this hlo) (lt_irrefl _)

/-! ## The theorem -/

/-- **`pe` is the top copy of `pa`** in the setting of `TopStartCutRight`, given `CutTopGap`. -/
theorem topNode_cutRight (hG : CutTopGap) {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell}
    {root : Ref} {i x : Nat} (hrun : Official.expandDiagram s n = .ok R) (hTop : Top s M t root)
    (hi0 : 0 < i) (hin : i ≤ n) (hx : x ∈ blockColumns root.column (M.size - 1) n i)
    {es : List (Emit × Origin)}
    (hes : emitsT (ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1)
      (x + (M.size - 1 - root.column) * i)) (official t.row) = .ok es)
    {j : Nat} (hj : j < es.length) (htop : IsTopAt es j) {cu cv : Cell} {l pe pa : Ref}
    (hcu : Reserve.cell? R ⟨x + (M.size - 1 - root.column) * i, j + 1⟩ = some cu)
    (hcv : Reserve.cell? M es[j].2.src = some cv) (hl : cv.left = some l)
    (hpa : Reserve.highestAtMost M l.column cv.row = some pa)
    (hpe : Reserve.highestAtMost R (Reserve.mapColumn root.column
      ((M.size - 1 - root.column) * i) l.column) cu.row = some pe)
    (hlo : cv.row < t.row) (hlr : root.column < l.column) (hcut : cutOrigin es[j].2 = true) :
    TopNode M R n root.column (M.size - 1) (official t.row) t.row i pe pa := by
  have hi1 : 1 ≤ i := hi0
  have hcr := hTop.lt
  have hb := hTop.build
  have hVM := build_valid_of_success hb
  obtain ⟨hxg, hxl⟩ := mem_blockColumns hcr hx
  have hwi : M.size - 1 - root.column ≤ (M.size - 1 - root.column) * i :=
    Nat.le_mul_of_pos_right _ hi1
  have hXR : x + (M.size - 1 - root.column) * i < R.size := by
    unfold Reserve.cell? at hcu
    cases hc : R[x + (M.size - 1 - root.column) * i]? with
    | none => rw [hc] at hcu; cases hcu
    | some _ => exact (Array.getElem?_eq_some_iff.mp hc).1
  have E := env_of hrun hTop hXR (by omega)
  have hG0 := E.G
  have hF := E.FR
  obtain ⟨lo, us, hD⟩ := colData_block E hi1 hin hx hXR
  have hee : es = lo ++ us := Except.ok.inj (hes.symm.trans hD.emitsT)
  subst hee
  set ctx := ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1)
    (x + (M.size - 1 - root.column) * i) with hctx
  -- the gap copy
  have ho := origin_of_cut hcut
  -- `pa` is at the row of `o`
  obtain ⟨paN, hpaN, hpac, hpar, hpaH⟩ := highestIn_of_highestAtMost hpa
  obtain ⟨peN, hpeN, hpec, _, hpeH⟩ := highestIn_of_highestAtMost hpe
  subst hpaN hpeN
  have hrowpa : ((Frame.ofMountain M).cell paN).row = cv.row :=
    Classification.Proofs.ChainCorr.CutParts.TSQ.paRow_diag hb hxg hes hj ho hcv hl hpa
      (LowerChainRecon.cell?_ref paN)
  -- the emit is in the lower part
  have hjlo : j < lo.length := lower_index hD hj hcv hlo
  have hlj : (lo ++ us)[j] = lo[j] := List.getElem_append_left hjlo
  have hmemlo : lo[j] ∈ lo := List.getElem_mem _
  obtain ⟨k, cv', hsk, hk1, hcvk, _⟩ := LowerPB.lowerT_src hD.hlo hmemlo
  have hcv2 : Reserve.cell? M lo[j].2.src = some cv := by rw [← hlj]; exact hcv
  rw [hsk] at hcv2
  have hcvv : cv = cv' := Option.some.inj (hcv2.symm.trans hcvk)
  subst hcvv
  -- the row of `u`
  have hk : j + 1 < (R[x + (M.size - 1 - root.column) * i]'hXR).size := by
    have := hD.size; rw [this, List.length_append]; omega
  obtain ⟨_, hrow, _⟩ := hD.node hk (by omega)
  have hcuR : cu = (R[x + (M.size - 1 - root.column) * i]'hXR)[j + 1] := by
    unfold Reserve.cell? at hcu
    simp only [Array.getElem?_eq_getElem hXR, Option.bind_eq_bind, Option.bind_some,
      Array.getElem?_eq_getElem hk] at hcu
    exact (Option.some.inj hcu).symm
  have hcurow : cu.row = stored lo[j].1.row := by
    rw [hcuR, hrow]; simp only [Nat.add_sub_cancel, hlj]
  -- the leg column
  have hlx : l.column < x := LowerPB.left_lt hVM hcvk hl
  have hax : paN.1.val < M.size - 1 := by omega
  have hag : root.column < paN.1.val := by omega
  have hpeC : peN.1.val = paN.1.val + (M.size - 1 - root.column) * i := by
    rw [hpec, hpac, Classification.Proofs.ChainCorr.mapColumn_of_ge hlr.le]
  have hLR : paN.1.val + (M.size - 1 - root.column) * i < R.size := by
    rw [← hpeC]; exact peN.1.isLt
  obtain ⟨lo', us', hD'⟩ := colData_inner E hi1 hin hag hax hLR
  set ctx' := ctxAt M R paN.1.val i root.column (M.size - 1 - root.column) (M.size - 1)
    (paN.1.val + (M.size - 1 - root.column) * i) with hctx'
  have hes' : emitsT (ctxAt M R l.column i root.column (M.size - 1 - root.column) (M.size - 1)
      (l.column + (M.size - 1 - root.column) * i)) (official t.row) = .ok (lo' ++ us') := by
    rw [← hpac]; exact hD'.emitsT
  -- a gap copy `q` of `pa` at a row `≥ row u` (`run_top_core`)
  have hNCx := nc_of_colData' E hi1 hD
  have hNCl := nc_of_colData' E hi1 hD'
  have hCS : Recon.LRC.CS s n R M t root i x paN.1.val := ⟨hNCx, hNCl, hi1, hag, by omega⟩
  obtain ⟨outsX, usX, hoX, hesXe, hupX⟩ := Classification.Proofs.P3T.lower_of_emits hD.emitsT
  obtain ⟨outsY, usY, hoY, hesYe, _⟩ := Classification.Proofs.P3T.lower_of_emits hD'.emitsT
  have hpX : lo[j] ∈ outsX.flatten := by
    have hmem : lo[j] ∈ outsX.flatten ++ usX := by
      rw [← hesXe]; exact List.mem_append_left _ hmemlo
    rcases List.mem_append.mp hmem with h | h
    · exact h
    · have := hupX _ h
      rw [← hlj, ho] at this
      simp [Origin.isUpper] at this
  have hpo : lo[j].2 = .clean ⟨ctx.x, k⟩ true := by
    rw [← hlj, ho]; congr 1; rw [hlj]; exact hsk
  have hmx : ((⟨ctx.x, k⟩ : Ref), cv) ∈ realNodes M x :=
    Classification.Proofs.CopyShape.mem_realNodes_of_cell' hcvk hk1
  have hpamem : (Frame.ref paN, (Frame.ofMountain M).cell paN) ∈ realNodes M paN.1.val :=
    Classification.Proofs.CopyShape.mem_realNodes_of_cell' (LowerChainRecon.cell?_ref paN) hpar
  obtain ⟨q, hq, hqo, hqrow⟩ := Classification.Proofs.P3T.run_top_core hCS hoX hoY hpX hpo hmx
    (by rw [hpac]; exact Classification.Proofs.P3T.leftColumn_of_left hl) hpamem
    (by rw [hrowpa])
  have hqm : q ∈ lo' ++ us' := by rw [hesYe]; exact List.mem_append_left _ hq
  obtain ⟨gi, hgi, hgq⟩ := List.getElem_of_mem hqm
  -- `CutTopGap`: `q` is at the row of `u`
  have hGap := hG s n R M t root i x hrun hTop hi0 hin hx (lo ++ us) hes j hj htop cv l
    (Frame.ref paN) hcv hl hpa hlo hlr hcut (lo' ++ us') hes'
  have hgapq : (lo' ++ us')[gi].1.row ≤ (lo ++ us)[j].1.row :=
    hGap gi hgi (by rw [hgq]; exact hqo)
  erw [hgq, hlj] at hgapq
  have hqeq : q.1.row = lo[j].1.row := le_antisymm hgapq hqrow
  -- the node `G` of `q`
  have hGlen : gi + 1 < (Frame.ofMountain R).length peN.1 := by
    change gi + 1 < R[peN.1.val].size
    simp only [hpeC]
    have := hD'.size
    rw [this]; omega
  let G : (Frame.ofMountain R).Node := ⟨peN.1, ⟨gi + 1, hGlen⟩⟩
  obtain ⟨hGk, hGrow⟩ := node_row hD' (N := G) hpeC (by simp [G])
  have hGe : (lo' ++ us')[G.2.val - 1] = q := by
    simp only [G, Nat.add_sub_cancel]
    exact hgq
  rw [hGe] at hGrow
  have hGu : (Frame.ofMountain R).height G = cu.row := by
    rw [hGrow, hcurow, hqeq]
  -- `pe` is `G`
  have hGpe : G.2.val ≤ peN.2.val := hpeH.2 G rfl (le_of_eq hGu)
  have hpeG : peN = G := by
    rcases lt_or_eq_of_le hGpe with hlt | heq
    · exfalso
      have h1 := height_lt_of_index hF (a := G) (b := peN) rfl hlt
      have h2 := hpeH.1
      rw [hGu] at h1
      exact absurd (lt_of_lt_of_le h1 h2) (lt_irrefl _)
    · exact node_eq_of_index rfl heq.symm
  rw [hpeG]
  have hsrcG : (lo' ++ us')[gi].2.src = Frame.ref paN := by
    erw [hgq, hqo]; rfl
  -- the ingredients of the non-gap comparison
  have hco : Reserve.cell? M ⟨ctx.x, k⟩ = some cv := hcvk
  have hleftc : l.column = ctx'.x := hpac.symm
  have CBL := Proofs.CopyShape.Final.cutBetweenLeg s n R hrun M t root hTop i hi1 hin ctx ctx'
    hD.bctx hD'.bctx hxg k cv l hk1 hco hl hleftc lo lo' hD.hlo hD'.hlo
  have hecut : LowerPB.cutO lo[j].2 = true := by
    rw [Proofs.CopyShape.Found.cutO_eq, ← hlj]; exact hcut
  have hec : Reserve.cell? M lo[j].2.src = some cv := by rw [hsk]; exact hcvk
  have hpaτ : (Frame.ofMountain M).height paN < t.row := by
    show ((Frame.ofMountain M).cell paN).row < t.row
    rw [hrowpa]; exact hlo
  refine ⟨⟨paN.1.val, lo' ++ us', gi, hag, hax,
    mem_blockColumns_of_inner (by omega) (by omega) hag hax, hpeC, by simp [Frame.ref, G], ?_,
    hgi, hsrcG⟩, ?_, ?_⟩
  · rw [show (Frame.ref G).column = paN.1.val + (M.size - 1 - root.column) * i from hpeC]
    exact hD'.emitsT
  · rintro v' hv'c hv'i ⟨c', hc'⟩ ⟨y', es2, j', hcy', hyx', _, hv', hidx', hes2, hj', hsrc'⟩
    obtain ⟨V', hV', _⟩ := node_of_cell hc'
    subst hV'
    have hV'c : V'.1 = G.1 := Fin.ext hv'c
    have hy' : y' = paN.1.val := by
      have h1 : V'.1.val = y' + (M.size - 1 - root.column) * i := hv'
      have h2 : V'.1.val = paN.1.val + (M.size - 1 - root.column) * i := by
        rw [hV'c]; exact hpeC
      omega
    subst hy'
    have hV'c2 : V'.1.val = paN.1.val + (M.size - 1 - root.column) * i := by
      rw [hV'c]; exact hpeC
    rw [show (Frame.ref V').column = paN.1.val + (M.size - 1 - root.column) * i from hV'c2]
      at hes2
    have hee : es2 = lo' ++ us' := Except.ok.inj (hes2.symm.trans hD'.emitsT)
    subst hee
    have hj'e : V'.2.val - 1 = j' := by
      have : (Frame.ref V').index = j' + 1 := hidx'
      simp [Frame.ref] at this; omega
    -- the rows of `G` and `V'`
    obtain ⟨_, hV'row⟩ := node_row hD' (N := V') hV'c2 (by simp [Frame.ref] at hidx'; omega)
    have hrowV : (Frame.ofMountain R).height V' = stored (lo' ++ us')[j'].1.row := by
      rw [hV'row]; simp only [hj'e]
    have hlt : G.2.val < V'.2.val := by simpa [Frame.ref] using hv'i
    have hGV := height_lt_of_index hF (a := G) (b := V') hV'c.symm hlt
    rw [hGu, hrowV, hcurow] at hGV
    have hGV' : lo[j].1.row < (lo' ++ us')[j'].1.row :=
      Recon.LowerPB.lt_of_stored_lt hGV
    cases hcut' : cutOrigin (lo' ++ us')[j'].2
    · -- a non-gap copy: strictly below `u`
      have hj'lo : j' < lo'.length := by
        refine lower_index hD' hj' (c := (Frame.ofMountain M).cell paN) ?_ hpaτ
        rw [hsrc']; exact LowerChainRecon.cell?_ref paN
      have hle' : (lo' ++ us')[j'] = lo'[j'] := List.getElem_append_left hj'lo
      have hmem' : lo'[j'] ∈ lo' := List.getElem_mem _
      have hc'src : Reserve.cell? M lo'[j'].2.src = some ((Frame.ofMountain M).cell paN) := by
        rw [← hle', hsrc']; exact LowerChainRecon.cell?_ref paN
      have hcut'' : LowerPB.cutO lo'[j'].2 = false := by
        rw [Proofs.CopyShape.Found.cutO_eq, ← hle']; exact hcut'
      have hC := (CBL lo[j] hmemlo lo'[j'] hmem' cv _ hec hc'src le_rfl).1 hecut hcut''
      have hlt2 := hC.1 (le_of_eq hrowpa)
      rw [← hle'] at hlt2
      exact absurd (lt_trans hGV' hlt2) (lt_irrefl _)
    · -- a gap copy: at or below `u`
      have ho' := origin_of_cut hcut'
      rw [hsrc'] at ho'
      have := hGap j' hj' ho'
      rw [hlj] at this
      exact absurd (lt_of_le_of_lt this hGV') (lt_irrefl _)
  · intro cm cv'' hcm _ hθ
    rw [LowerChainRecon.cell?_ref] at hcm
    rw [← Option.some.inj hcm] at hθ
    exact absurd (lt_of_le_of_lt hθ hpaτ) (lt_irrefl _)

/-- **`TopStartCutRight` from `CutTopGap`.** -/
theorem topStartCutRight_of_gap (hG : CutTopGap) : TopStartFixParts.TopStartCutRight := by
  intro s n R M t root i x hrun hTop hi0 hin hx es hes j hj htop cu cv l pe pa hcu hcv hl hpa hpe
    hlo hlr hcut
  have hT := topNode_cutRight hG hrun hTop hi0 hin hx hes hj htop hcu hcv hl hpa hpe hlo hlr hcut
  exact ⟨Or.inr hT, fun _ => hT⟩

end OmegaY.Official.Recon.TSQ

#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.CutParts.TSQ.paRow_diag
#print axioms OmegaY.Official.Recon.TSQ.topNode_cutRight
#print axioms OmegaY.Official.Recon.TSQ.topStartCutRight_of_gap
