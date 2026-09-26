/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/CCLMain.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.CCLCount
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.RPLFix
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.SeamPassMain
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.JumpLawBlock0
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.P3TRunTop
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.NonTopBase

set_option backward.do.legacy false

set_option autoImplicit false

/-!
# `CountAsc`, `CopyCountLe`, and the plain and clean parent chains (`CCL`)

`countAsc : CountAsc` (part (c) of `CCLBase.lean`). The columns `x`, `y` of block `i` and nodes
`v = (x, a)`, `v' = (y, b)` of row `C` with the same stored left end `L`, both columns ascending at
`C`:

* `L` is at or right of `c_r` (`left_ge_of_asc`, from the ascension of `x`);
* the anchor facts `AnchE` for the row `C`: below `C` the columns `x`, `y` ascend together (both
  with `L`, `ascLeg`), at `C` the column `y` ascends, and the generations of `v`, `v'` are equal
  (their chains of generations continue from the same node `(col L, C)`, `gen_eq`);
* the lower emits are the flattened runs of the first items; `count_sim` compares them item by
  item; the upper part has no emit of `v` (its origins are at or above `τ`).

With `copyCountLe_of` (`CCLBase.lean`) and `ascCarry` (`CCLAsc.lean`): **`copyCountLe :
CopyCountLe`**. With the seam reduction `seamStep_of_cutParent`, `seamStart_of_cutParent`
(`SeamPassMain.lean`, from the open stage-D statement `CutParentNT`):

* `rootPass_plain_of : TopStep → TopStart' → CutParentNT → RootPass IsPlain`;
* `lexImg_plain_final : LexImg IsPlain`, `lexImg_clean_final : LexImg IsClean`;
* `crossLexFor_plain_final : TopStep → TopStart' → CutParentNT → CrossLexFor IsPlain`;
* `crossLexFor_clean_final : TopStep → TopStart' → CrossLexFor IsClean`.
-/

namespace OmegaY.Official.Recon.CCL

open Canonical Expansion Geometry Frame Classification
open Reserve (cell?)
open Classification.Proofs.ChainCorr (cutOrigin)
open Classification.Proofs.CopyShape.ProfileLeg (AscRow)
open RPLLex (cnt CopyCountLe)
open JumpLaw JumpLawLower LRC

/-! ## The left end of an ascending node -/

/-- **The stored left end of `v` is at or right of `c_r`** when the column of `v` ascends at a
root top of the row of `v`. -/
theorem left_ge_of_asc {s : List Nat} {M R : Mountain} {t : Cell} {root : Ref}
    (hTop : Top s M t root) {i x a : Nat} {cv : Cell} (hxg : root.column < x) (ha : 1 ≤ a)
    (hcv : cell? M ⟨x, a⟩ = some cv) (hA : AscRow (bctx M R root i x) (official cv.row)) :
    ∃ L, cv.left = some L ∧ root.column ≤ L.column := by
  obtain ⟨d, S, ρ, hρ, hρrow, hasc⟩ := hA
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
  obtain ⟨nw, hnwr, hnwc⟩ := ControlProof.node_of_cell? hcw
  have hnwcol : nw.1.val = x := by rw [node_col hnwr, hwc]
  have hnwidx : nw.2.val = wr.index := node_idx hnwr
  have hnwR : Frame.Real nw := by show 0 < nw.2.val; omega
  obtain ⟨nwu, hnwu, hnwur, hnwuc⟩ :=
    upper_node (u := nw) (by rw [hnwcol, hnwidx, ← hwc]; exact hcup)
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
  have hcw1 : (1 : Row) ≤ cw.row := Classification.one_le_row hV hcw hw1
  by_cases hwv : wr.index = a
  · -- `w = v`: the left end is the column of the candidate `Q(v)`
    have hwr : wr = ⟨x, a⟩ := by cases wr; simp only at hwc hwv; subst hwc hwv; rfl
    subst hwr
    have hcc : cw = cv := Option.some.inj (hcw.symm.trans hcv)
    subst hcc
    obtain ⟨q0, hQ0, hit0⟩ := (P_iff hO).mp hPw
    obtain ⟨left, hleft, _, _, hq0c, _, _, _⟩ := Q_spec hO hQ0
    have hq0R : Frame.Real q0 := Q_real hO hnwR hQ0
    have hpath := hit0.parentPath hO (hO.real_positive q0 hq0R)
    have hle := hpath.column_le hO
    refine ⟨Frame.ref left, by rw [← hnwc]; exact hleft, ?_⟩
    show root.column ≤ left.1.val
    rw [← hq0c]
    have : pw.1.val = q.column := node_col hpwq
    omega
  · -- `w ≠ v`: the node above `w` is `v`, and its left end is `q`
    have hnwuh : (Frame.ofMountain M).height nwu = Row.bump cw.row 0 := by
      rw [hBw, hpwh]
      show Row.B ((Frame.ofMountain M).cell nw).row ((Frame.ofMountain M).cell nw).row = _
      rw [hnwc, Row.B_self]
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
    exact ⟨q, by rw [← hnwuc', hleftw, hpwq], hqcr⟩

/-! ## Generations -/

/-- **Two nodes with the same left column have the same number of generations.** -/
theorem gen_eq {M : Mountain} {cr : Nat} {C : Row} {fx fy : Nat} {rx ry : Ref} {cx cy : Cell}
    {gx gy p : Nat} (hx : generations M cr C fx rx cx 0 = .ok gx)
    (hy : generations M cr C fy ry cy 0 = .ok gy) (hcx : cr < rx.column) (hcy : cr < ry.column)
    (hlx : leftColumn cx = .ok p) (hly : leftColumn cy = .ok p) (hpx : p < rx.column)
    (hpy : p < ry.column) : gx = gy := by
  cases fx with
  | zero => simp [generations, throw, throwThe, MonadExceptOf.throw] at hx
  | succ fx =>
  cases fy with
  | zero => simp [generations, throw, throwThe, MonadExceptOf.throw] at hy
  | succ fy =>
    unfold generations at hx hy
    rw [if_neg (by omega)] at hx hy
    simp only [bind, Except.bind, hlx] at hx
    simp only [bind, Except.bind, hly] at hy
    rw [if_neg (by omega)] at hx hy
    cases hn : nodeAt M p C with
    | none => rw [hn] at hx; simp [throw, throwThe, MonadExceptOf.throw] at hx
    | some q =>
      obtain ⟨r2, c2⟩ := q
      rw [hn] at hx hy
      simp only at hx hy
      have := gen_shift M cr C fx r2 c2 1 gx hx fy 1 gy hy
      omega

/-! ## Tools -/

theorem left_lt {s : List Nat} {M : Mountain} (hb : Canonical.build s = .ok M) {r L : Ref}
    {c : Cell} (hc : cell? M r = some c) (hl : c.left = some L) : L.column < r.column := by
  have hO := (build_normal_of_success hb).toOrdered
  obtain ⟨u, hu, huc⟩ := ControlProof.node_of_cell? hc
  have hl' : ((Frame.ofMountain M).cell u).left = some L := by rw [huc]; exact hl
  obtain ⟨left, hlk, hlt, _⟩ := hO.stored_valid u L hl'
  have h1 : Frame.ref left = L := Frame.lookup_spec hlk
  have h2 : left.1.val = L.column := node_col h1
  have h3 : u.1.val = r.column := node_col hu
  omega

theorem lowerT_flat' {ctx : Context} {τ : Row} {lo : List (Emit × Origin)}
    (h : lowerT ctx τ = .ok lo) :
    ∃ outs, (lowerItems τ).mapM (fun p => runItemT ctx p.1 p.2) = .ok outs ∧
      lo = outs.flatten := by
  unfold lowerT at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i outs houts
    exact ⟨outs, houts, (Except.ok.inj h).symm⟩

/-- The columns of the blocks `1 ≤ i ≤ n` exist in the output. -/
theorem col_lt_size {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}
    (hrun : Official.expandDiagram s n = .ok R) (hTop : Top s M t root) {i x : Nat} (hi0 : 0 < i)
    (hin : i ≤ n) (hxb : x ∈ blockColumns root.column (M.size - 1) n i) :
    x + (M.size - 1 - root.column) * i < R.size := by
  have hcr := hTop.lt
  obtain ⟨hxg, hxl⟩ := mem_blockColumns hcr hxb
  have hsz := Classification.Proofs.CopyShape.Found.run_size hrun hTop (by omega)
  set W := M.size - 1 - root.column with hW
  have hWpos : 0 < W := by omega
  rw [hsz, Nat.mul_comm n W]
  rcases Nat.lt_or_eq_of_le hin with hlt | heq
  · have : W * i < W * n := (Nat.mul_lt_mul_left hWpos).mpr hlt
    have : W * i + W ≤ W * n := by
      have h2 : W * (i + 1) ≤ W * n := Nat.mul_le_mul_left W hlt
      rw [Nat.mul_succ] at h2; exact h2
    omega
  · subst heq
    have hx0 : x < M.size - 1 := by
      unfold blockColumns at hxb
      rw [if_neg (by omega), if_neg (by omega)] at hxb
      rw [List.mem_range'_1] at hxb
      omega
    omega

/-- **A column of a block `1 ≤ i ≤ n` is a new column.** -/
theorem nc_of_block {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}
    (hrun : Official.expandDiagram s n = .ok R) (hTop : Top s M t root) {i x : Nat} (hi0 : 0 < i)
    (hin : i ≤ n) (hxb : x ∈ blockColumns root.column (M.size - 1) n i) :
    NewColumn s n R M t root i x := by
  have hcr := hTop.lt
  obtain ⟨hxg, hxl⟩ := mem_blockColumns hcr hxb
  have hwi : M.size - 1 - root.column ≤ (M.size - 1 - root.column) * i :=
    Nat.le_mul_of_pos_right _ hi0
  have hXR := col_lt_size hrun hTop hi0 hin hxb
  have E := CrossUpperSim.env_of hrun hTop hXR (by omega)
  obtain ⟨i', x', hi', hx', hXeq, hcopy⟩ := E.CI.2.2 (x + (M.size - 1 - root.column) * i) hXR
    (by omega)
  obtain ⟨hii, hxx⟩ := Classification.Proofs.ChainCorr.NonTop.blockX_unique hcr hxg hxl hx'
    hXeq hi0
  subst hii hxx
  exact ⟨E.run, E.top, by omega, E.CI, hi', hxb, hXR, ⟨_, Array.getElem?_eq_getElem hXR, hcopy⟩⟩

/-! ## `CountAsc` -/

theorem countAsc : CountAsc := by
  intro s n R hrun M t root hTop i x y hi0 hin hxb hyb es esY hes hesY a b cv cv' ha hb hcv hcv'
    hrow hτ hleft hAx hAy
  have hcr := hTop.lt
  obtain ⟨hxg, hxl⟩ := mem_blockColumns hcr hxb
  obtain ⟨hyg, hyl⟩ := mem_blockColumns hcr hyb
  have hbld := hTop.build
  have hV := build_valid_of_success hbld
  have hoff : official cv.row = official cv'.row := by rw [hrow]
  -- the same column
  by_cases hxy : x = y
  · subst hxy
    have h1 := Classification.Proofs.CutGap.nodeAt_of_cell hV hcv ha
    have h2 := Classification.Proofs.CutGap.nodeAt_of_cell hV hcv' hb
    rw [hoff, h2] at h1
    have hba : b = a := by
      have := congrArg (fun p => p.1.index) (Option.some.inj h1)
      simpa using this
    subst hba
    have : es = esY := Except.ok.inj (hes.symm.trans hesY)
    subst this
    exact le_rfl
  -- the left end
  obtain ⟨L, hL, hLcr⟩ := left_ge_of_asc hTop hxg ha hcv hAx
  have hL' : cv'.left = some L := by rw [← hleft]; exact hL
  have hLx : L.column < x := left_lt hbld hcv hL
  have hLy : L.column < y := left_lt hbld hcv' hL'
  -- the new columns and the pair
  have hNCx := nc_of_block hrun hTop hi0 hin hxb
  have hNCy := nc_of_block hrun hTop hi0 hin hyb
  have rX := hNCx.runCtx
  have rY := hNCy.runCtx
  have P : Pair (colCtx M R root i x) (colCtx M R root i y) :=
    ⟨rfl, rfl, rfl, rfl, fun d T => by rw [colCtx_bnd hNCy, colCtx_bnd hNCx],
      by show i ≠ 0; omega⟩
  -- the anchor facts
  have hnvx : nodeAt M x (official cv.row) = some (⟨x, a⟩, cv) :=
    Classification.Proofs.CutGap.nodeAt_of_cell hV hcv ha
  have hnvy : nodeAt M y (official cv.row) = some (⟨y, b⟩, cv') := by
    rw [hoff]; exact Classification.Proofs.CutGap.nodeAt_of_cell hV hcv' hb
  have hlt' : ∀ {r : Row}, r < official cv.row → r < official cv'.row := by
    intro r h; rw [← hoff]; exact h
  have H : AnchE (colCtx M R root i x) (colCtx M R root i y) (official cv.row) := by
    refine ⟨?_, ?_, ?_⟩
    · intro d S ρr ρc hρ hlt
      have h1 := Classification.Proofs.CopyShape.AscLeg.ascLeg hbld hxg ha hcv hL hLcr hρ hlt
        (colCtx M R root i x) (colCtx M R root i L.column) rfl rfl rfl rfl rfl rfl
      have h2 := Classification.Proofs.CopyShape.AscLeg.ascLeg hbld hyg hb hcv' hL' hLcr hρ
        (hlt' hlt) (colCtx M R root i y) (colCtx M R root i L.column) rfl rfl rfl rfl rfl rfl
      exact h1.trans h2.symm
    · intro d S ρr ρc hρ hle hasc
      rcases lt_or_eq_of_le hle with hlt | heq
      · have h1 := Classification.Proofs.CopyShape.AscLeg.ascLeg hbld hxg ha hcv hL hLcr hρ hlt
          (colCtx M R root i x) (colCtx M R root i L.column) rfl rfl rfl rfl rfl rfl
        have h2 := Classification.Proofs.CopyShape.AscLeg.ascLeg hbld hyg hb hcv' hL' hLcr hρ
          (hlt' hlt) (colCtx M R root i y) (colCtx M R root i L.column) rfl rfl rfl rfl rfl rfl
        exact h2.mpr (h1.mp hasc)
      · obtain ⟨d', S', ⟨r', cl'⟩, _, hrow', hasc'⟩ := hAy
        rw [Classification.Proofs.P3T.ascends_row (r' := r') (cl' := cl')
          (by rw [heq]; exact hrow'.symm)]
        exact hasc'
    · intro refx cx gx refy cy gy hnx hgx hny hgy
      change nodeAt M x (official cv.row) = some (refx, cx) at hnx
      change nodeAt M y (official cv.row) = some (refy, cy) at hny
      rw [hnvx] at hnx
      rw [hnvy] at hny
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hnx)
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hny)
      exact gen_eq hgx hgy hxg hyg (Classification.Proofs.P3T.leftColumn_of_left hL)
        (Classification.Proofs.P3T.leftColumn_of_left hL') hLx hLy
  -- the facts MD and MH
  have hFMDX := Classification.Proofs.CopyShape.Found.factMD_of_bctx hTop (colCtx_bctx hNCx)
  have hFMDY := Classification.Proofs.CopyShape.Found.factMD_of_bctx hTop (colCtx_bctx hNCy)
  have hFMHY := Classification.Proofs.CopyShape.Found.factMH_of_bctx hrun hTop hi0 hin
    (colCtx_bctx hNCy)
  -- the lower and upper parts
  obtain ⟨lo, us, hlo, hus, rfl⟩ := LowerPB.emitsT_split hes
  obtain ⟨loY, usY, hloY, husY, rfl⟩ := LowerPB.emitsT_split hesY
  obtain ⟨outsX, houtsX, rfl⟩ := lowerT_flat' hlo
  obtain ⟨outsY, houtsY, rfl⟩ := lowerT_flat' hloY
  rw [cnt_append, cnt_append]
  have hus0 : cnt us ⟨x, a⟩ = 0 := by
    apply RPLLex.cnt_zero
    intro k hk hsrc
    obtain ⟨c, hc, hle⟩ :=
      (Classification.Proofs.ChainCorr.CopyMonoProof.upperT_mono hV hus).2 _ (List.getElem_mem hk)
    change cell? M us[k].2.src = some c at hc
    rw [hsrc, hcv] at hc
    obtain rfl := Option.some.inj hc
    have h1 : (1 : Row) ≤ cv.row := Classification.one_le_row hV hcv ha
    exact absurd (Recon.official_strictMono h1 hτ) (not_lt.mpr hle)
  have hmain : cnt outsX.flatten ⟨x, a⟩ ≤ cnt outsY.flatten ⟨y, b⟩ := by
    obtain ⟨hlX, hallX⟩ := Classification.mapM_except_spec _ _ _ houtsX
    obtain ⟨hlY, hallY⟩ := Classification.mapM_except_spec _ _ _ houtsY
    apply count_le_sum
    intro k hk _
    have hkF : k < (lowerItems (official t.row)).length := by omega
    have hkY : k < outsY.length := by omega
    refine ⟨hkY, ?_⟩
    have hFmem := List.getElem_mem hkF
    have hAt : InTree (colCtx M R root i x) (official t.row) (lowerItems (official t.row))[k].1
        (lowerItems (official t.row))[k].2 := ⟨_, hFmem, .refl _ _⟩
    have hBt : InTree (colCtx M R root i y) (official t.row) (lowerItems (official t.row))[k].1
        (lowerItems (official t.row))[k].2 := ⟨_, hFmem, .refl _ _⟩
    exact count_sim P rX rY hbld H houtsX houtsY hcv rfl
      (Classification.Proofs.CopyShape.mem_realNodes_of_cell' hcv' hb) hoff.symm hnvy
      (fun d A r cl hA hρ hasc => hFMDX d A (reach_of_inTree hA) r cl hρ hasc)
      (fun d B r cl hB hρ hasc => hFMDY d B (reach_of_inTree hB) r cl hρ hasc)
      (fun d B hB C' r cl csRef csc g hC hcb hρ hn hg => by
        have := hFMHY d B C' (reach_of_inTree hB) hC hcb csRef csc g hn hg
        have hρ' : topIn (colCtx M R root i y).source (colCtx M R root i y).rootColumn (d + 2)
            B.source = some (r, cl) := hρ
        rw [hρ', P.bnd] at this
        exact this)
      _ _ _ hAt hBt (Or.inl rfl) _ _ (hallX k hkF hk) (hallY k hkF hkY)
  omega

/-! ## `CopyCountLe` and the plain and clean parent chains -/

/-- **`CopyCountLe` holds.** -/
theorem copyCountLe : CopyCountLe := copyCountLe_of ascCarry countAsc

open Classification.Proofs.ChainCorr.LowerChain (TopStep)
open Classification.Proofs.ChainCorr.TopStartFix (TopStart')
open TopChain.Seam (CutParentNT)

/-- **`RootPass IsPlain`** from `TopStep`, `TopStart'` and `CutParentNT`. -/
theorem rootPass_plain_of (hTS : TopStep) (hTSt : TopStart') (hCP : CutParentNT) :
    CrossPlainPos.RootPass IsPlain :=
  RPLLex.rootPass_plain_fix hTS hTSt (TopChain.Seam.Pass.seamStep_of_cutParent hCP)
    (TopChain.Seam.Pass.seamStart_of_cutParent hCP)

/-- **`LexImg IsPlain`.** -/
theorem lexImg_plain_final : CrossPlainPos.LexImg IsPlain := RPLLex.lexImg_plain copyCountLe

/-- **`LexImg IsClean`.** -/
theorem lexImg_clean_final : CrossPlainPos.LexImg IsClean := RPLLex.lexImg_clean copyCountLe

/-- **`CrossLexFor IsPlain`** from `TopStep`, `TopStart'` and `CutParentNT`. -/
theorem crossLexFor_plain_final (hTS : TopStep) (hTSt : TopStart') (hCP : CutParentNT) :
    CrossLexFor IsPlain :=
  RPLLex.crossLexFor_plain_fix hTS hTSt (TopChain.Seam.Pass.seamStep_of_cutParent hCP)
    (TopChain.Seam.Pass.seamStart_of_cutParent hCP) copyCountLe

/-- **`CrossLexFor IsClean`** from `TopStep` and `TopStart'`. -/
theorem crossLexFor_clean_final (hTS : TopStep) (hTSt : TopStart') : CrossLexFor IsClean :=
  RPLLex.crossLexFor_clean_fix hTS hTSt copyCountLe

end OmegaY.Official.Recon.CCL

#print axioms OmegaY.Official.Recon.CCL.countAsc
#print axioms OmegaY.Official.Recon.CCL.copyCountLe
#print axioms OmegaY.Official.Recon.CCL.rootPass_plain_of
#print axioms OmegaY.Official.Recon.CCL.lexImg_plain_final
#print axioms OmegaY.Official.Recon.CCL.lexImg_clean_final
#print axioms OmegaY.Official.Recon.CCL.crossLexFor_plain_final
#print axioms OmegaY.Official.Recon.CCL.crossLexFor_clean_final
