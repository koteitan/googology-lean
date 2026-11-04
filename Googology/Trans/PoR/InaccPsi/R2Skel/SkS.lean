import Googology.Trans.PoR.InaccPsi.R2.WdRoad
import Googology.Trans.PoR.InaccPsi.R2.WcSupLo
import Googology.Trans.PoR.InaccPsi.R2.VrRoad
import Googology.Trans.PoR.InaccPsi.R2.TyRng
import Googology.Trans.PoR.InaccPsi.R2Skel.SkF
import Googology.Trans.PoR.InaccPsi.R2.WfRoad
import Googology.Trans.PoR.InaccPsi.R2.WfWin
import Googology.Trans.PoR.InaccPsi.R2.WfRefute
import Googology.Trans.PoR.InaccPsi.R2.WkRead
import Googology.Trans.PoR.InaccPsi.R2.WkCarry
import Googology.Trans.PoR.InaccPsi.R2.WqImgRef
import Googology.Trans.PoR.InaccPsi.R2.WqCarry
import Googology.Trans.PoR.InaccPsi.R2.WuSup
import Googology.Trans.PoR.InaccPsi.R2.WuWin
import Googology.Trans.PoR.InaccPsi.R2.WuImg
import Googology.Trans.PoR.InaccPsi.R2.WwGap
import Googology.Trans.PoR.InaccPsi.R2.WwForm
import Googology.Trans.PoR.InaccPsi.R2.WwRoad
import Googology.Trans.PoR.InaccPsi.R2.XbImg
import Googology.Trans.PoR.InaccPsi.R2.XbReal
import Googology.Trans.PoR.InaccPsi.R2.XbRoad
import Googology.Trans.PoR.InaccPsi.R2.XaRep
import Googology.Trans.PoR.InaccPsi.R2.CitedXe
import Googology.Trans.PoR.InaccPsi.R2.XeFix
import Googology.Trans.PoR.InaccPsi.R2.XeShift
import Googology.Trans.PoR.InaccPsi.R2.XjShift
import Googology.Trans.PoR.InaccPsi.R2.XjGap
import Googology.Trans.PoR.InaccPsi.R2.XoRoad
import Googology.Trans.PoR.InaccPsi.R2.XoNode
import Googology.Trans.PoR.InaccPsi.R2.XoSub
import Googology.Trans.PoR.InaccPsi.R2.XoRef
import Googology.Trans.PoR.InaccPsi.R2.YbCov
import Googology.Trans.PoR.InaccPsi.R2.YbLev
import Googology.Trans.PoR.InaccPsi.R2.YbSup
import Googology.Trans.PoR.InaccPsi.R2.YgIF
import Googology.Trans.PoR.InaccPsi.R2.YgK
import Googology.Trans.PoR.InaccPsi.R2.YgUc
import Googology.Trans.PoR.InaccPsi.R2.YgWw
import Googology.Trans.PoR.InaccPsi.R2.YqIF
import Googology.Trans.PoR.InaccPsi.R2.YqCov
import Googology.Trans.PoR.InaccPsi.R2.YqReal
import Googology.Trans.PoR.InaccPsi.R2.YqShift
import Googology.Trans.PoR.InaccPsi.R2.YqRoad
import Googology.Trans.PoR.InaccPsi.R2.YvSub
import Googology.Trans.PoR.InaccPsi.R2.YvPi
import Googology.Trans.PoR.InaccPsi.R2.YvDat
import Googology.Trans.PoR.InaccPsi.R2.YvComp
import Googology.Trans.PoR.InaccPsi.R2.YvUp
import Googology.Trans.PoR.InaccPsi.R2.YvLev
import Googology.Trans.PoR.InaccPsi.R2.YvWit

/-!
# Skeleton of the part "supply": the hypotheses `h0` / `hn` of `Wd.wdRoadL`

`L(ξ) = Nc.ncL S ξ`, `a = υ_λ = L(k)`, `u₁ = υ_{λ+1}`, `g = ω^{ω^{u₁+1}}` (the offset of the `Vo.voNoGo` witness),
`β(ν) = (ν − λ) + ω²` (the window chosen at the isolated uncovered Range restart `ν`), `u' = υ_{μ+1}`,
`X = ω^{ω^{u'+1}+1}` (`Wc.wcX`), `m(z) = cdOff(cdExp z)`, `π = π_{υ_μ, υ_λ}`.

Round 116 (leaf "repair the supply road"): the road is replaced.  `Wf.wfRoad` has the conclusion of `Wd.wdRoadL`
with `h0` / `hn` in the RESTRICTED form `Wf.WfVisGen` (the image clause of the carry only for decompositions with
`Wf.WfR`: lo-leaves in `T^{υ_λ}[υ_μ]`, i.e. below `υ_μ` when below `υ_λ`); `Wf.wfVisGen_of_vr` shows the old
statement implies the new one.  NEW top node `skSup`: `h0' ∧ ∀ n, hn' n` of `Wf.wfRoad`; `Root.skNuC` must apply
`Wf.wfRoad` (same arguments) in place of `Wd.wdRoadL`.  The map data `SkMapP` has the restricted exponent clause.
RESTATED nodes: `SkMapP`, `skOffMapW` (now PROVED by `Wf.wfOffMap`), `skImgF`, `skCarryWit`, `skCarryOther`,
`skSupK`, `skGen`, `skVisK`, `skSup`.  NEW nodes: `skPiLo` (PROVED), `skSideRef` (PROVED negation).
The SUSPECT reasons of the refuter (`SkSX.skSX_offMap_free`, `skSX_img_pi`, `skSX_sup_pi`) do not apply to the
restated nodes (`Wf.wfR_skSX_excl`, `Wf.wfSup_lo`, `R2Skel.SkSX.skSX_notTB`).  This file imports the new `Wf`
modules, so it can be checked only after the merge.  Every node is tagged STATUS / SIZE in its docstring.

Round 117 (leaf "WcRead0, then the witness-window leaves", sup39): `skRead0` PROVED (`Wk.wkRead0`: the level-wise
lift with atoms `ψ_{Ω₂}(Ω_{n+1} + κ ζ)` below `θ`), so `skMu` is PROVED.  `skLowerF` RESTATED (a window hypothesis
`∃ w, Ty.TyWin S k w ∧ w < υ_μ`; the old `∀ μ` form asked LOWER at `μ + f z` with no Range / `RzRest` known when
`υ_μ` lies below the window, e.g. at an index `L(j)`, code `P′`) and REDUCED (`Wk.wkLowerF` + the new shared leaf
`skLowRR`); `skCarryWit`, `skCarryOther` carry the window hypothesis, `skSupK` picks `μ` above the window
(`Wk.wkWin_ex`).  `skBigF` REDUCED (`Wk.wkBigF`: vacuous at every offset with `λ + z < ν` since `ν` is not covered)
to the NEW leaf `skBigTop` (the single offset `z = ν − λ`).  This file imports the new `Wk` modules, so it can be
checked only after the merge.

Round 118 (leaf "the supply leaves skBigTop, skImgF, skFormOther, skCarryOther", sup40).  `u₁ = υ_{λ+1}`,
`ε_{u₁+1} = eN u₁`.  In the low region (`0 < z < υ_{λ+2}`) every inner reach is `r(λ+z) = υ_{λ+(z+ω+1)} + m_{λ+z}`,
`m_{λ+z} ≤ z` (`Vr.vrR_inner`).
* `skBigTop` REDUCED to the shared `skNu` only (VACUOUS: `r(ν) < υ_{ν+ω²}`, `Wq.wqBigTop`, `Wq.wqBigLow`).
* `skImgF` REFUTED (`Wq.wqImgF_ref`; nodes `skImgF_ref`, `skImgF_false`): the map data `SkMapP` leave `f z` free
  at every offset with `m z ≥ u₁`; the map with `f(ω^{u₁}) = ω²` breaks the image clause.  REPLACED by the NEW leaf
  `skImgEps` (an `∃ f B` with the image clause, at every window with `ν − λ < ε_{u₁+1}`).
* What separates the windows is not "witness / non-witness" but the size of `ν − λ`: below `ε_{u₁+1}` the forms
  hold (`Wq.wqForms_eps`; NEW node `skFormEps`) and the carry needs only the image clause (`Wq.wqCarry_low`: LOWER by
  `Wk.wkLowerF`, the big reach vacuous; NEW node `skCarryEps`).  The witness window is one of them
  (`Wq.wqWit_eps`; NEW node `skWitEps`).  `skFormOther` and `skCarryOther` are REDUCED to the NEW leaves
  `skFormHigh` / `skCarryHigh` (windows with `ν − λ ≥ ε_{u₁+1}`).
* Non-vacuity: the witness context exists with `ν` explicit (`Wq.wqWitCtx`, used in `skImgF_ref`).
* `skOffMapW`, `skLowerF`, `skBigF` stay as they are but are OFF THE ROAD (`skCarryEps` uses `Wq.wqCarry_low`).
This file imports the new `Wq` modules, so it can be checked only after the merge.

Round 119 (leaf "skImgEps, skFormHigh, skCarryHigh", sup41).  `X` an `ε`-number with `u₁ < X < u₂ = υ_{λ+2}`.
* REFUTE FIRST, "is the image of a decomposition a function of its value?": NO EVIDENCE against.  On the value
  `τ + u₁` of `Wq.wqImgF_ref` three different decompositions have one image for every `f` (`Wu.wuImg_test`; NEW node
  `skImgVal`); in a realizer configuration every two decompositions of one value have one image (`Vr.vrImg_agree`).
* `skImgEps` stays OPEN; its piece (i) "a supply past `Wc.wcX`" is PROVED: `υ_{μ+φ(1,u'+1)} ≤ r(μ)`, `φ(1,u'+1) ≥
  ε_{u'+1}` (`Wu.wuSup`; NEW node `skSupEps`).
* `skFormHigh` SUSPECT.  The code of `λ + X` is `X` and `r(λ+X) = υ_{λ+(X+ω+1)} + X` (`Wu.wuR_X`); `ν_X = λ + X + ω²`
  is a window (`Wu.wuWin`; at `X = ε_{u₁+1}` a high window, NEW node `skHighWin`: the hypotheses of `skFormHigh` /
  `skCarryHigh` are satisfiable).  A repaired form of a value ending in `X` ends in an `sg`-node with parameters below
  `υ_λ` or in `X = ϑ^{u₁}(ξ)`, `ξ ∈ T^{u₁}`, `ξ < B₂` (`Wu.wuLast`, `Wu.wuForm_X`: the term languages stop at the
  level `B₂`).  So `Wu.WuGap S k` (an `X` that is neither) REFUTES `skFormHigh` (NEW node `skFormHigh_ref`) and the
  supply hypothesis of `Wf.wfRoad` at `L(k)` (`Wu.wuVis_ref`; at `k = 0` the road is vacuous: NEW node `skRoadRef`).
  NEW leaf `skGap` (`WuGap`, OFF THE ROAD: a refutation target; expected witness `X = ϑ^{u₁}(B₂ + υ_λ)`).
* `skCarryHigh` stays OPEN (moot if `skGap` holds).
This file imports the new `Wu` modules, so it can be checked only after the merge.

Round 120 (leaf "decide WuGap: is the supply road vacuous?", sup42).  `X = ϑ^{u₁}(B₂ + υ_λ)` (`Ww.wwX`).
* The gap HOLDS at every `L(k)`: `Ww.wwGap` (`WuGap` with the segment clause asked where `υ_{λ+h} < Ω₁`, the only
  bases over which `Par` is cited; NEW node `skGapW`, PROVED; the old leaf `skGap` is REPLACED by it).
* So `Wf.WfVisGen` fails at every `L(k)` under `L(k+1) ≤ ν_C` (`Ww.wwVis_ref`), the hypotheses of `Wf.wfRoad` and of
  `Ws.wsRoadZ` are jointly FALSE (`Ww.wwRoad_false`, `Ww.wwRoadZ_false`): the old top `skSup` is REFUTED (NEW node
  `skSup_false`, from the shared leaf `skNu`), and with it `skVisK`, `skGen`, `skForm`, `skFormOther`, `skFormHigh`
  (NEW node `skFormHigh_false`, by `Ww.wwFormHigh_fail`); these nodes are removed.
* REPAIR: forms with `ϑ`-nodes of every level (`Ww.WwE`: `th h M e`, value `ϑ^{υ_{λ+h}}(Ω₁·M + val e)`, image
  `ϑ^{υ_{μ+f(h)}}(Ω₁·M + img e)`; `Ww.WwForm`, `Ww.WwCarry`, `Ww.WwSup`, `Ww.WwGen`, `Ww.WwVisGen`); the gap witness
  has a repaired form at every window (`Ww.wwForm_X`, `Ww.wwForm_gap`); old forms are repaired forms
  (`Ww.wwForm_of_vr`); the repaired carry contains `Wf.WfCarry` (`Ww.wwSup_wf`).  NEW road `Ww.wwRoad` (conclusion of
  `Wf.wfRoad`) with `WwVisGen` and the realizer bridge `Ww.WwRealB`.  NEW TOP `skSupW`; `Root.skNuC` must apply
  `Ww.wwRoad` with `SkS.skRealB S` and `skSupW.1`, `skSupW.2` in place of `Wf.wfRoad` with `skSup.1`, `skSup.2`.
  NEW nodes: `skFormW` (REDUCED), `skFormHighW` (OPEN), `skSupKW` (OPEN), `skGenW`, `skVisKW` (REDUCED), `skRealB`
  (OPEN).  `skSupK` (and its subtree `skCarryWit`, `skCarryOther`, `skCarryHigh`, `skImgEps`) is now OFF THE ROAD: its
  statement `Wf.WfSup` follows from `skSupKW` (`Ww.wwSup_wf`).
This file imports the new `Ww` modules, so it can be checked only after the merge.

Round 122 (leaf "skShiftTh, following the paper", sup44).
* NEW cited axiom `R2.xeVt_trL` (`R2.CitedXe`): [W07a] Def 6.2 + Lemma 6.3, subcase `Γ > 0`, `Γ^* < α`, at every
  level `Γ = Ω₁·M`, `B₂ ≤ M < θ`, data `d_S(M) < q ≤ α` (`q` strongly critical); the twin of `R2.uvVt_trL` (ranges
  disjoint: `Xe.xe_twin_disj`).  REFUTE FIRST: NO EVIDENCE (consistent with `uvVt_trL` below `B₂`; no no-go result
  mentions translations).
* The node lemmas of `R2.UyFix` below `θ` (`R2.XeFix`, NEW node `skNodeTh`, PROVED): the code `π`-fix
  `Xe.xe_pi_fix_th` (every `z < θ` with `d_S(z) < q ≤ σ` is in `Tᵗ[σ]` and fixed by `π`: one induction along
  `Vs.vsMu`, no axiom beyond `CitedVd`, `CitedVp`), `Xe.xe_Om1_mul_TB`, `Xe.xe_arg_T`, `Xe.xeLt_vt_self`,
  `Xe.xeVt_tr` (both translations at every constant level `Ω₁·M < θ`), `Xe.xeDown`, `Xe.xeMv`.
* `skShiftTh` REDUCED (`Xe.xbShift_of_xe`) to the NEW leaf `skShiftThHi` (`Xe.XeShift S`: the clause only for `η ∈ Y`
  at levels `M ≥ B₂`).  The other cases are theorems: `η ∈ X` at every level `Ω₁·M < θ` (`Xe.xe_thCl_low`, from the
  move clause of `Vl.vlShiftCore` and `Xe.xeMv`), every `η` at levels `Ω₁·M < B₂` (`Xe.xe_thCl_lowLev`, the term
  clause of `vlShiftCore` at `thc M (par η)`).  `Root.skNuC` is unchanged.
This file imports the new `Xe` modules, so it can be checked only after the merge.

Round 123 (leaf "the FRAG term language with the level as a parameter up to θ: skShiftThHi", sup45).
* FRAG with a top `ϑ`-node of a constant level as a parameter (`Xj.XjNodeSys L`, `Xj.XjCl L`, `Xj.xjFragV`): the
  node cases of `Vl.vlFrag_step` with the node lemmas `hL.down`, `hL.trA`, `hL.trB`, `hL.nodeUp`, `hL.nodeMv`; the
  instances `L = Uy.UyLev` (bound `B₂`, from `R2.uvVt_trL` only: `Xj.xjNodeUy`, `Xj.xjLv_B_iff`) and `L = Xe.XeLev`
  (bound `θ`: `Xj.xjNodeXe`, with `R2.xeVt_trL`).  REFUTE FIRST at `M = B₂`: NO EVIDENCE (`B₂` is a level of the new
  instance, `Xj.xjLv_th_B`; `vmap` keeps it, `vtr` takes the branch `Γ^* < α`); the step is now a theorem.
* `skShiftThHi` PROVED (`Xj.xeShift_holds`, from the shift `Xj.xjShiftCore` built with `Xj.xjFragV`), so
  `skShiftTh` (`Xb.XbShift S`) and `skRealBX` (`Xb.XbRealB S`) are PROVED.  NEW node `skFragTh` (PROVED).
* NEW REFUTATION: `skFormHighX` is REFUTED (`Xj.xjFormHighX_fail`; NEW node `skFormHighX_false`).  The witness
  `X′ = ϑ^{u₁}(Ω₁·(B₂ + λ) + λ)` (`Xj.xjX`) is an `ε`-number in `(u₁, u₂)` whose only `ϑ`-reading has the level
  `B₂ + λ`, whose data never lie below `λ` (`Xj.xj_M0_noLt`); a form with constant `ϑ`-levels cannot end in it
  (`Xj.xjLast`, `Xj.xjVt_ne_lev`, `Xj.xjVt_ne_low`, `Xj.xj_par_X`).  So `Xb.XbVisGen` fails at every `L(k)` under
  `L(k+1) ≤ ν_C` (`Xj.xjVis_ref`): the top `skSupX` is REFUTED (NEW node `skSupX_false`, from the shared node
  `skNu`), and the hypotheses of `Xb.xbRoad` (and of `Xj.xjRoad`) are jointly FALSE (`Xj.xbRoad_false`,
  `Xj.xjRoad_false`).  `Root.skNuC` still applies `Xb.xbRoad`, now through a REFUTED leaf: the supply road must be
  replaced (forms whose `ϑ`-levels may have data in `[υ_λ, υ_{λ+h})`, i.e. the shift at moving levels `≥ B₂`).
This file imports the new `Xj` modules, so it can be checked only after the merge.

Round 125 (leaf "repair Xo.XoR and the supply road with moving leaves (skeleton SkS)", sup47; sup46 was not merged,
its `Xo` modules enter here, fixed).
* REPAIR of `Xo.XoR` (the BLOCKING finding of round 124: the level constructors gave fixed spellings, image = value,
  of countable points `≥ υ_μ`, e.g. `F_k = ψ_{Ω₁}(Ω_ω·2 + P′·k) = λ`): every closed sub-term (no `old` leaf, no
  `ϑ`-node, `Xo.XoCl`) has a low value (`Xo.XoLow`: below `θ` a data reading below `υ_μ`), and every collapse with a
  countable value is closed and below `υ_μ`.  `Xo.xoR_fixed`: every closed spelling of a countable point `≥ υ_μ`
  violates it; `Xo.xoFk_notR` (`F_k`), `Xo.xoE2_notR` (the audit's `E″`).
* REFUTE FIRST of the repair as first asked (closed sub-terms only): REFUTED, `Xo.xoNaive_ref`.  The absorbed spelling
  `F′_k = ψ_{Ω₁}(λ + Ω_ω + Ω_ω + P′·k)` carries the moving leaf `λ` (absorbed by `Ω_ω`), has value `λ` and image `λ`;
  `E‴ = (F′_k + sg h₁) + th 1 (lc B₂ + lo λ) (lo λ)` is well formed with value `r(λ+X′)` and passes the syntactic
  repair `Xo.XoRn`, its image is `≥ λ` (`Xo.xoE3_img_ge`), and under the reach formula at `μ + f(X′)` the carry asks
  `λ ≤ r(μ+f(X′)) < λ`.  The collapse clause excludes it (`Xo.xoE3_notR`, `Xo.xoFkA_notR`).
* REFUTE FIRST of the repaired road: NO EVIDENCE.  Forms clause: unchanged, always holds (`Xo.xoForms_all`; it does not
  read `XoR`).  Under the repaired `XoR`: `λ` (`lo λ`, `Xo.xo_lo_R`), `X′` (`E′`, `Xo.xoXj_R`), the level with `u₁`
  (`Xo.xoU1_R`) and the nested level (`Xo.xoNest_R`) keep their terms; a point of `[υ_μ, υ_λ)` has neither a moving
  leaf (`Xo.xo_gap_noLeaf`) nor a fixed spelling, as before (`π` is free there); the obligation at `X′` stays
  `X′_μ ≤ f(X′)` (`Xo.xoXj_obl`) and is consistent with `Sl.SlOff` (`Xo.xoOff_wit`).
* Left on the supply: `skSupKXo` (OPEN, `Xo.XoSup` with the repaired `XoR`), `skRealBXo` (OPEN).  `Root.skNuC` must
  apply `Xo.xoRoadH` as in round 124 (same statement, the repaired `XoR` inside `Xo.XoCarry`).
This file imports the new `Xo` modules, so it can be checked only after the merge.

Round 124 (leaf "a supply road whose ϑ-levels may carry moving leaves (skeleton SkS)", sup46).
* REFUTE FIRST, the new supply: NO EVIDENCE.  Forms `Xo.XoE`: a `ϑ`-node `th h L e` whose level `L` is a term (leaves
  are old nodes or nested `ϑ`-nodes and move; fixed constants `lc M` with data below `υ_μ`; `+`, `φ`, `Ω_·`, `ψ`);
  image `Xo.xoImg` = the leaf substitution.  At the witness `X′ = Xj.xjX` the moving-leaf decomposition `E′ = sg h₁
  υ_{λ+h₁} + th 1 (lc B₂ + lo λ) (lo λ)` is well formed and passes the restriction (`Xo.xoXj_WF`, `Xo.xoXj_R`; its
  constant-level version was excluded, `Xo.xoXj_notWwR`); its image is `υ_{μ+f(h₁)} + X′_μ`, `X′_μ =
  ϑ^{υ_{μ+f(1)}}(Ω₁·(B₂ + υ_μ) + υ_μ)` (`Xo.xoXj_img`), and the carry there asks exactly `X′_μ ≤ f(X′)`
  (`Xo.xoCarry_xj`, `Xo.xoXj_obl`, given the reach formula at `μ`).  Next candidates (a level with the leaf `u₁`, a
  level with the nested node `X′`): `u₁ ↦ υ_{μ+f(1)}`, `X′ ↦ X′_μ` (`Xo.xoNext_img`).  On one-segment levels the leaf
  substitution is the base change (`Xo.xoImg_pi`; `π(B₂ + λ) = B₂ + υ_μ`, `Xo.xoXj_lev_pi`), so the image does not
  depend on the term of the level.  Covering: every level with data below `υ_{λ+β}` is a term (`Xo.xoCover_lev`), every
  `Ww.WwE` decomposition is rewritten with term levels (`Xo.xoRewrite`), the forms clause always holds
  (`Xo.xoForms_all`).
* NEW cited axiom `R2.xoVt_trH` (`R2.CitedXo`): [W07a] Def 6.2 + Lemma 6.3, subcase `Γ^* ≥ α`, at every level `B₂ ≤ M
  < θ` with a strongly critical `q`, `α ≤ q ≤ d_S(M)` (twin of `R2.uvVt_trH`); `Xo.xoVt_up` / `Xo.xoVt_down` (both
  subcases), `Xo.xoCase_disj` (the cases of `xeVt_trL` and `xoVt_trH` exclude each other), `Xo.xoH_wit`
  (non-vacuity).
* NEW ROAD `Xo.xoRoadH` / `Xo.xoRoad` (conclusion of `Xb.xbRoad` / `Xl.xlwRoad`) with the bridge `Xo.XoRealB` and the
  supply `Xo.XoVisGen`; not touched by `Xj.xjVis_ref` (`Xo.xoVis_gap`).  NEW TOP `skSupXo` (REDUCED to the OPEN leaf
  `skSupKXo`, `Xo.XoSup`) and NEW leaf `skRealBXo` (OPEN, `Xo.XoRealB`: FRAG with moving-leaf levels `≥ B₂` and the
  carry).  The old top `skSupX` stays (REFUTED as a whole) and is OFF THE ROAD.  `Root.skNuC` must apply
  `Xo.xoRoadH (SkF.skFrontU S) (SkF.skFrontL S) (SkF.skFrontV S) (SkF.skFrontVt S) hE.1 hE.2 (SkS.skRealBXo S)
  SkS.skSupXo.1 SkS.skSupXo.2` in place of `Xb.xbRoad … (SkS.skShiftTh S) skSupX.1 skSupX.2`.
This file imports the new `Xo` modules, so it can be checked only after the merge.

Round 121 (leaf "the realizer bridge for ϑ-nodes: skRealB", real1).
* REFUTE FIRST at the gap witness: NO EVIDENCE.  The image of the `ϑ`-node `th 1 B₂ (lo λ)` under an offset map with
  `f(1) = 1` is `ϑ^{υ_{μ+1}}(B₂ + υ_μ)` (`Xb.xb_img_gap`), an `ε`-number of `T^{υ_{μ+1}}` in `(υ_{μ+1}, υ_{μ+2})` with
  the parameter `υ_μ` (`Xb.xbIX_spec`): the shape of the gap witness one segment down (NEW node `skImgGap`, PROVED).
* The gap of `skRealB`, in Lean names: (G1) `Vl.vlShiftCore` has the term clause only for nodes `thz (Ω₁·q) r` with
  `Ω₁·q < B₂` (`Vi.Nz.qB`); the `ϑ`-node clause `Xb.XbThCl` is missing; (G2) `R2.uvVt_trL` / `uvVt_trH` (the
  translations of [W07a] Def 6.2 / Lemma 6.3 used by every FRAG step) stop at `B₂`; `CitedVd` gives membership,
  order, data and `π` below `θ` but no translation.  (G3) `Ww.WwCarry` bounds images only under `Ww.WwR` (data of
  every `ϑ`-level below `υ_μ`), while `Ww.WwWF` allows `ϑ`-levels with data in `[υ_λ, υ_{λ+h})`: the bridge
  `Ww.WwRealB` as stated asks an image bound that the carry does not give.  `skRealB` is SUSPECT as stated and OFF THE
  ROAD.
* REDUCTION (`Xb.xbRealB`): `Xb.XbShift S` (`vlShiftCore` + `XbThCl` at constant levels: `1 ≤ M`, data below the
  bottom `γ`) gives `Xb.XbRealB S` (the bridge for `Xb.XbGen`: forms with constant `ϑ`-levels, `Xb.XbForm`).  NEW leaf
  `skShiftTh` (OPEN), NEW node `skRealBX` (REDUCED).
* NEW ROAD `Xb.xbRoad`: `Ww.wwRoad` with `hB` replaced by `XbShift S` and the supply by `Xb.XbVisGen`
  (`Xb.xbVisGen_ww`: `XbVisGen ⇒ WwVisGen`).  NEW TOP `skSupX` (XbVisGen at `m*` and every `L(n+1)`); the old top
  `skSupW` is kept with its exact statement and is REDUCED from `skSupX`.  `Root.skNuC` must apply
  `Xb.xbRoad (SkF.skFrontU S) (skFrontL S) (skFrontV S) (skFrontVt S) hE.1 hE.2 (SkS.skShiftTh S) skSupX.1 skSupX.2`.
  NEW nodes: `skFormHighX` (OPEN; `skFormHighW` with constant `ϑ`-levels; the gap witness satisfies it,
  `Xb.xbForm_gap`), `skFormX`, `skGenX`, `skVisKX` (REDUCED).  `skFormHighW`, `skFormW`, `skGenW`, `skVisKW` are OFF
  THE ROAD (they feed only `skSupW`, which now follows from `skSupX`).  `skSupKW` stays on the road (`XbGen` uses
  `Ww.WwSup`).
This file imports the new `Xb` modules, so it can be checked only after the merge.

Round 121 (leaf "skFormHighW, skSupKW", sup43; joined with real1 at the merge).
* REFUTE FIRST `skFormHighW`: NO countable ordinal below `υ_{λ+β}` escapes the repaired forms.  Every `x < υ_{λ+β}`,
  `x < Ω₁`, is `wwVal l E` of a well-formed `E` (`Xa.xaRep`, by induction on `x`: `lo` below `υ_{λ+1}`, sums at
  decomposable `x`, `sg h x` at `x = υ_{λ+h}`, otherwise `x = ϑ^{υ_{λ+h}}(Ω₁·M + η)` by `vt_rep` with `η ∈ T`, `η < x`,
  `Xa.xa_arg`).  So the forms clause holds at EVERY offset and window (`Xa.xaForm_all`, given only `0 < λ`,
  `υ_{λ+β} ≤ Ω₁`): `skFormHighW` and `skFormW` are PROVED, and `Ww.WwGen` is the UPPER clause plus `Ww.WwSup`
  (`Xa.xaGen_iff`).  After the join both are OFF THE ROAD (the road `Xb.xbRoad` needs forms with constant `ϑ`-levels,
  `skFormHighX`, still OPEN; `Xa.xaRep` may use levels with data in `[υ_λ, υ_{λ+h})`).
* `skSupKW` stays OPEN (on the road through `skGenX`).  REFUTE FIRST: NO EVIDENCE (see its docstring).
This file imports `Xa.XaRep`, so it can be checked only after the merge.

Round 126 (leaf "the supply carry and the bridge of Xo.xoRoadH", sup48).  Top node `skSupXo` and its statement kept;
`Root.skNuC` unchanged (it applies `Xo.xoRoadH`).
* REFUTE FIRST, the risk "a `ϑ`-node image argument outside `T^{υ_{μ+f h}}`": NO EVIDENCE.  The leaves of a level
  of a well-formed node of segment `h` are in segments `≤ h` unless absorbed (a level datum in `T^{υ_{λ+h}}` is below
  `υ_{λ+h+1}`); absorption by `+`, `φ` or `ψ_{Ω_k}` (`k ≥ 2`) of a countable leaf does not depend on its value, and
  a countable collapse is closed (`Xo.XoR`); the image moves each leaf inside its own target segment, so the image
  level has its data below `υ_{μ+f h+1}`.  Not a Lean theorem (needs the hull isomorphism of `skRealBXo`).
* COVERING LEMMA (`Yb`): every countable `x < υ_{λ+β}` has ONE well-formed, non-closed moving-leaf decomposition with
  a finite offset set, restricted at every `μ` in a tail `γ < υ_μ < υ_λ` (`Yb.ybCover`), under the level statement
  `Yb.YbLevK`, which follows from the notation-only statement `Yb.YbIF` (`Yb.ybLevK_of_IF`): every level
  `Ω₁ ≤ M < θ` lies in the inacc-free closure `Yb.YbK S q` (fixed atoms with data below `Γ₀` allowed) at every
  strongly critical `q ≤ Ω₁` above its datum.  NEW leaf `skYbIF` (OPEN, OFF THE ROAD: a tool for `skRealBXo`).
  Reason it is needed: an inaccessible `I_n` has no restricted term (`lc (I n)` fails the `lc` clause, `I_n ≥ θ`),
  so a high-data level whose every spelling needs `I_n` would have no restricted decomposition.
* At the witnesses no hypothesis is needed (`Yb.ybCov_wit`, `Yb.ybTail_wwX`): `λ`, `r(λ+X′)`, `wwX`; the audit's
  `F_k`, `F′_k`, `E″`, `E‴` have the values `λ`, `r(λ+X′)`.
* NON-SILENCE (`Yb.ybSup_bound`): under `YbLevK`, `Xo.XoSup` gives for every `γ` and every finite offset set a
  configuration whose carry bounds the image of a restricted decomposition of EVERY inner reach below `υ_{λ+β}` (the
  audit's MINOR 2: the carry is not silent where the realizer needs it).
* `skSupKXo`, `skRealBXo` stay OPEN (exact gaps in their docstrings).
NEW nodes: `skYbIF` (OPEN), `skYbIFWit` (PROVED), `skLevOfIF` (PROVED), `skCoverLev` (PROVED), `skCoverXo` (REDUCED),
`skCoverWit` (PROVED), `skSupNonSilent` (REDUCED).  This file imports the new `Yb` modules, so it can be checked only
after the merge.

Round 129 (leaf "YbIF above B₂, the bridge skRealBXo and the carry skSupKXo of Xo.xoRoadH", sup51).
* `YbIF` ON THE NOTATION (`Yq.yqNotK`, no axiom): on the normal form of an ordinal below `θ` every collapse argument
  is below `Ω_ω` (`Ui.ui_args_th`), so no `I_n` occurs in an uncountable subterm with value below `Ω_ω`
  (`Yq.yqTermK`), and the countable leaves are below `q` (`Vd.vd_dat_ui`).  So `YgIFTh` holds at every level whose
  datum is below some `ψ_{Ω₁}(A)` (`Yq.yqIF_dat`), `YbIF` at every threshold `q ≤ ψ_{Ω₁}(A)` (`Yq.yqIFN`), and the
  covering lemma and the non-silent supply hold on every window `υ_{λ+β} ≤ ψ_{Ω₁}(A)`, e.g. `≤ L(ω+1)`, with no
  hypothesis (`Yq.yqCover`, `Yq.yqSupBound`; NEW nodes `skYbIFNot`, `skLevKNot`, `skCoverXoL`, `skSupNonSilentL`).
  `skYbIFTh` REDUCED to the NEW leaf `skYbIFHuge` (`Yq.YqIFHuge`: the levels whose datum is above every value of
  `ψ_{Ω₁}`; `Yq.yqHuge_iff`: equivalent to `skYbIFTh`).
* THE BRIDGE REDUCED TO A SHIFT CLAUSE: `Yq.yqReal_gen` (the proof of `Xb.xbReal_gen` with the decompositions taken
  from the covering lemma instead of the forms clause) gives the realizer from the clause `Yq.XoDCl` (`D(value) =
  image` on restricted decompositions with an `old` / `th` / `add` skeleton, the shape of the covering lemma
  `Yq.yqCoverT`) of the shift `Yq.XoShift`; `Yq.yqShift_of2` reduces `XoDCl` to ONE node clause on top of
  `Xb.XbShift`: `Yq.XoThCl` (the `ϑ`-node clause with a level term, moving leaves included).  NEW leaf `skShift2` (`Yq.XoShift2 S`, OPEN L, ON THE ROAD);
  `skRealBXo` REDUCED (`Yq.yqRealB_huge`, off the road); NEW node `skRealBXoL` (`Yq.XoRealBL`: the bridge on the
  windows `υ_{λ+β} ≤ L(ω+1)`, the only ones the road uses; from `skShift2` alone).
* THE ROAD: `Yq.yqRoadS` is `Xo.xoRoadH` with the bridge replaced by `Yq.XoShift S` (through `Yq.XoRealBL`).
  `Root.skNuC` must apply `Yq.yqRoadS (SkF.skFrontU S) (SkF.skFrontL S) (SkF.skFrontV S) (SkF.skFrontVt S) hE.1 hE.2
  (SkS.skShiftXo S) hS.1 hS.2` in place of `Xo.xoRoadH … (SkS.skRealBXo S) …`.
* REFUTE FIRST: `YbIF` at levels just above `B₂` and with an `Ω₂^λ·D` part: PROVED on the notation (no refutation
  possible there); the carry at `wwX`, `xjX` and at a large-code supply point: NO EVIDENCE (unchanged); `XoShift2`:
  NO EVIDENCE (no known no-go result speaks of the shift; it extends `Xb.XbShift`, PROVED by `Xj.xbShift_holds`).
This file imports the new `Yq` modules, so it can be checked only after the merge.

Round 127 (leaf "YbIF, the bridge skRealBXo and the carry skSupKXo of Xo.xoRoadH: is the root non-vacuous?", sup49).
Top node `skSupXo` and its statement kept; `Root.skNuC` unchanged (it applies `Xo.xoRoadH`).
* REFUTE FIRST, `YbIF`: NO EVIDENCE.  The naive route (copy a `Vd.VdK`-derivation, drop the inaccessibles) is
  REFUTED: `Y = ψ_{Ω₃}(I₀)` is in `Vd.VdK S 0 q` at every `q` but in no `Yb.YbK S q`, `q ≤ Ω₁` (`Yg.ygY_notK`,
  `Yg.ygVdK_notYb`; NEW node `skYbNaiveRef`).  But below `Ω₂` the inaccessible washes out on the test level
  `M₀ = ψ_{Ω₂}(ψ_{Ω₃}(I₀)) ∈ [B₂, θ)`: `M₀ = ψ_{Ω₂}(Ω₃)` (`Yg.ygTwin`, `Yg.ygTwin_lev`; NEW node `skYbTwin`).  `YbIF`
  holds at every level with datum `< Γ₀` (`Yg.ygIF_low`) and at `B₂ + c`, `c < q` (`Yg.ygIF_B_add`).
* `YbIF` BELOW `B₂` PROVED (`Yg.ygIF_lowB`, NEW node `skYbIFLowB`): `UcCl q ⊆ YgK S q ⊆ YbK S q` (`Yg.ygUcK`, the
  inacc-free closure without fixed atoms `Yg.YgK`; the inversion `Uo.uoArg` is replaced by carrying the own argument
  of every atom along the induction, `Yg.YgOwnK`).  `skYbIF` is REDUCED to the NEW leaf `skYbIFTh` (`Yg.YgIFTh`:
  the levels `B₂ ≤ M < θ`), by `Yg.ygIF_of_th`.
* REFUTE FIRST, the carry at the gap witness `wwX = ϑ^{u₁}(Ω₁·B₂ + λ)`: NO EVIDENCE.  `E_W = sg h_W + th 1 (lc B₂)
  (lo λ)` is a well-formed restricted form of `r(λ+wwX)` (`Yg.ygWw_WF`, `Yg.ygWw_R`), its image is `υ_{μ+f(h_W)} +
  W_μ` (`Yg.ygWw_img`), and under the reach formula at `μ` the carry asks exactly `W_μ ≤ f(wwX)` (`Yg.ygWw_obl`), the
  same shape as at `X′` (`Xo.xoXj_obl`); NEW nodes `skXoCarryWw`, `skXoOblWw`.
* REFUTE FIRST, the carry at a supply point with a large code (the Range restarts `μ` with code `G_{k+1}+1` of
  `Wk.wkRead0`): NO EVIDENCE; Lean has no value of `r(μ + f g)` there (only `υ_{μ+B} ≤ r(μ)`, `Wu.wuSup`).
* `skSupKXo`, `skRealBXo` stay OPEN.  NON-VACUITY of `Xo.xoRoadH`: not shown, not refuted; the exact gap is the
  open leaves on the road (18, all L).
NEW nodes: `skYbIFTh` (OPEN, off the road), `skYbIFLowB`, `skYbIFLow`, `skYbIFBAdd`, `skYbTwin`, `skXoCarryWw`,
`skXoOblWw` (PROVED), `skYbNaiveRef` (PROVED NEGATION); `skYbIF` OPEN → REDUCED.  This file imports the new `Yg`
modules, so it can be checked only after the merge.

Round 130 (leaf "the shift clause XoThCl and the carry skSupKXo: is the root non-vacuous?", sup52).  Top node `skSupXo`
and its statement kept; `Root.skNuC` unchanged (it applies `Yq.yqRoadS`).
* THE LEVEL SORT BELOW `θ` (the tool `skShift2` needs: a leaf substitution on the levels `[B₂, θ)` whose leaves move):
  `Yv.YvLv` / `Yv.YvR` / `Yv.yvSub` (the canonical decomposition of every code below `θ`, through every cardinal level
  of the dictionary `D(s)`, `Vs.vsShape`; below `B₂` it is `Vc.vcSub`), and for every base change: `π z = yvSub π z`
  (`Yv.yv_pi`, `Yv.yv_pi_TB`), membership decided by the leaves (`Yv.yv_TB_iff`), the clause of `π z` is the
  `π`-image of the clause of `z` (`Yv.yv_comp`), the inverse base change `π⁻¹ G = yvSub π⁻¹ G` (`Yv.yv_up`), the image
  of a level is a level (`Yv.yv_level_img`), the node `π(ϑᵗ(Ω₁·M + ρ)) = ϑ^σ(yvSub π (Ω₁·M) + π ρ)` (`Yv.yv_node_img`),
  the datum is decided by the leaves (`Yv.yv_dat_iff`, no axiom) and so is the subcase of [W07a] Def 6.2
  (`Yv.yv_node_tr`).  NEW nodes `skYvPi`, `skYvComp`, `skYvUp`, `skYvNode`, `skYvDat`, `skYvTr` (PROVED).
* REFUTE FIRST, `XoThCl` at a node whose level has one moving leaf (the base itself, `ϑ^{b}(Ω₁·(B₂ + b) + r)`): NO
  EVIDENCE.  The compression gives `ϑ^σ(Ω₁·(B₂ + σ) + π r)` (`Yv.yv_wit_pi`: the leaf substitution `b ↦ σ`), the
  translation keeps the argument (`Yv.yv_wit_hi`: subcase `Γ^* ≥ α`), the expansion is `yvSub π⁻¹` (`Yv.yv_up`): every
  step of FRAG agrees with the leaf substitution there.  NEW node `skYvWit` (PROVED).  The carry `skSupKXo` at `wwX`,
  `xjX` and at a supply restart with code `G_{k+1}+1`: NO EVIDENCE (unchanged; Lean has no value of `r(μ + f g)`).
* `skShift2` stays OPEN.  The moving-level hull clause is stated (`Yv.YvCl`: `Ψ(ϑ^{b_k}(Ω₁·q + r[b_k])) =
  ϑ^{c_k}(yvSub Ψ (Ω₁·q) + (vmap Ψ r)[c_k])` for levels `Ω₁·q < θ` with leaves in the configuration); at constant
  levels it is the proved `Xj.XjCl` (`Yv.yv_cl_const`, `Yv.yv_cl_frag`: the FRAG map of `Xj.xjFragXe`).  NEW node
  `skYvClConst` (PROVED), NEW leaf `skYvCl` (OPEN L, off the road: the next statement for `skShift2`).
This file imports the new `Yv` modules, so it can be checked only after the merge.
-/

set_option autoImplicit false

namespace R2Skel.SkS

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-! ## Statement abbreviations -/

/-- The context of `Vr.VrVisGen` at `L(k) = υ_λ` on the window `[υ_{L(k)+W(L(k))}, L(k+1))` at the Range restart
`ν`: uncovered, isolated from below. -/
def SkCtx (S : InaccSeq.{0}) (k : ℕ) (l ν : Ordinal.{0}) : Prop :=
  IsRestartIdx l ∧ Nc.ncL S (k : Ordinal.{0}) = upsilon l ∧ CdRange S ν ∧
    upsilon (Nc.ncL S (k : Ordinal.{0}) + Te.teW (Nc.ncL S (k : Ordinal.{0}))) ≤ upsilon ν ∧
    upsilon ν < Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ∧ upsilon l < upsilon ν ∧
    ¬ Tk.TkCov S (upsilon l) ν ∧ Tk.TkIso S (upsilon l) ν

/-- The supply restarts `μ`: Range, code `G₂+1`, below `L(ω)`, with the first reading `Wc.WcRead0`. -/
def SkMu (S : InaccSeq.{0}) (μ : Ordinal.{0}) : Prop :=
  CdRange S μ ∧ cdCode S μ = Ls.lsG S (0 + 1 + 1) + 1 ∧ upsilon μ < Nc.ncL S ω ∧ Wc.WcRead0 S μ

/-- The witness window: `ν = λ + g + ω²`. -/
def SkWit (l ν : Ordinal.{0}) : Prop := ν = l + ω ^ ω ^ (upsilon (l + 1) + 1) + ω ^ 2

/-- The map data at the witness window: bound, supply, `Sl.SlOff`, `f g = g'`, and the exponent condition
`π(m z) ≤ m(f z)` at every low offset with `m z ∈ T^{υ_λ}[υ_μ]` (RESTATED round 116: the restricted exponent
clause; `Vy.vyEQ_lo`). -/
def SkMapP (S : InaccSeq.{0}) (l μ : Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}) (B : Ordinal.{0})
    (Os : Finset Ordinal.{0}) : Prop :=
  μ + B ≤ l ∧ ω ^ 2 ∣ B ∧ upsilon (μ + B) ≤ cdR S μ ∧ Sl.SlOff f Os B ∧
    (ω ^ ω ^ (upsilon (l + 1) + 1) ∈ Os → f (ω ^ ω ^ (upsilon (l + 1) + 1)) = ω ^ ω ^ (upsilon (μ + 1) + 1)) ∧
    ∀ z ∈ Os, 0 < z → ω ^ 2 ∣ z → cdOff (cdExp z) < upsilon (l + 1) →
      cdOff (cdExp z) ∈ TB (upsilon l) (upsilon μ) →
      pi (upsilon μ) (upsilon l) (cdOff (cdExp z)) ≤ cdOff (cdExp (f z))

/-! ## Shared leaves (content of the other parts of the road) -/

/-- STATUS: REDUCED (R2Skel.SkF.skFrontU, Hl.hlU_enum; integration round 115)
SIZE: L
UPPER at every Range restart with `RzRest` (shared with part hUH: below the frontier by `Hl.hlU_enum`, above it
by the frontier part `SkF.skFrontU`).
∀ λ, Range(λ) ∧ RzRest(λ) ⇒ UPPER(λ) -/
theorem skUpRR : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l := by
  intro l hr _
  by_cases h : Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l
  · exact _root_.R2Skel.SkF.skFrontU S l hr h
  · exact (Hl.hlU_enum S hr (lt_of_not_ge h)).1

/-- STATUS: REDUCED (R2Skel.SkF.skFrontL, Hl.hlU_enum; NEW round 117)
SIZE: L
LOWER at every Range restart with `RzRest` (shared with part hLH: below the frontier by `Hl.hlU_enum`, above it
by the frontier part `SkF.skFrontL`).
∀ λ, Range(λ) ∧ RzRest(λ) ⇒ LOWER(λ) -/
theorem skLowRR : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l := by
  intro l hr _
  by_cases h : Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l
  · exact _root_.R2Skel.SkF.skFrontL S l hr h
  · exact (Hl.hlU_enum S hr (lt_of_not_ge h)).2

/-- STATUS: REDUCED (R2Skel.SkF.skFrontU/L/V/Vt, Wd.wdNu; integration round 115)
SIZE: L
`L(ω+1) ≤ ν_C` (shared: `Wd.wdNu` from hUH, hLH, hVH, hVt of the frontier part `SkF`).
L(ω+1) ≤ ν_C -/
theorem skNu : Nc.ncL S (ω + 1) ≤ nuC :=
  Wd.wdNu (_root_.R2Skel.SkF.skFrontU S) (_root_.R2Skel.SkF.skFrontL S) (_root_.R2Skel.SkF.skFrontV S)
    (_root_.R2Skel.SkF.skFrontVt S)

/-! ## The window -/

/-- STATUS: PROVED (by `Pp.ppL_succ_restart`, `Vr.vr_dvd_step`, `upsilon_normal`)
SIZE: S
υ_ν < υ_{λ+β(ν)} ≤ L(k+1) -/
theorem skWin {k : ℕ} {l ν : Ordinal.{0}} (h : SkCtx S k l ν) :
    upsilon ν < upsilon (l + (ν - l + ω ^ 2)) ∧
      upsilon (l + (ν - l + ω ^ 2)) ≤ Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) := by
  obtain ⟨-, -, hR, -, h3, h4, -, -⟩ := h
  have hm := upsilon_normal.strictMono
  have hlν : l < ν := hm.lt_iff_lt.1 h4
  have he : l + (ν - l + ω ^ 2) = ν + ω ^ 2 := by
    rw [← add_assoc, Ordinal.add_sub_cancel_of_le hlν.le]
  rw [he]
  obtain ⟨l', hl', e'⟩ := Pp.ppL_succ_restart (S := S) k
  rw [e'] at h3 ⊢
  refine ⟨hm (lt_add_of_pos_right ν (pow_pos omega0_pos 2)), hm.monotone ?_⟩
  exact Vr.vr_dvd_step hR.1.2 hl'.2 (hm.lt_iff_lt.1 h3)

/-! ## The three clauses of `Vr.VrGen` at `β(ν)` -/

/-- STATUS: REDUCED (from `skUpRR`, `skWin`, `Ty.tyInner_rng`)
SIZE: S
∀ g, 0 < g < β(ν), ω² | g ⇒ UPPER(λ+g) -/
theorem skUp {k : ℕ} {l ν : Ordinal.{0}} (h : SkCtx S k l ν) :
    ∀ g, 0 < g → g < ν - l + ω ^ 2 → ω ^ 2 ∣ g → CdUpper S (l + g) := by
  intro g hg0 hgβ hgd
  have hm := upsilon_normal.strictMono
  have hl := h.1
  have hr : IsRestartIdx (l + g) :=
    ⟨(lt_of_lt_of_le (pos_iff_ne_zero.2 hl.1) le_self_add).ne', dvd_add hl.2 hgd⟩
  have h1 : Nc.ncL S (k : Ordinal.{0}) < upsilon (l + g) := by
    rw [h.2.1]; exact hm (lt_add_of_pos_right l hg0)
  have h2 : upsilon (l + g) < Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) :=
    (hm ((add_lt_add_iff_left l).2 hgβ)).trans_le (skWin h).2
  obtain ⟨hR, hz⟩ := Ty.tyInner_rng (S := S) (k := k) hr h1 h2
  exact skUpRR _ hR hz

/-- STATUS: REDUCED, OFF THE ROAD since round 120 (`skFormW` uses `skFormEps`; witness windows are `ε`-windows, `skWitEps`); (from the shared leaf `skNu` and `Vr.vrForms_win`, `Te.teUps_L`, `Pp.ppL_lt_omega`, `Qq.qqL_lt_succ`;
no other child)
SIZE: S
ν = λ+g+ω² ⇒ ∀ z < β(ν) = g+ω²·2, ω² | z ⇒ VrForm(λ, β, z) -/
theorem skFormWit {k : ℕ} {l ν : Ordinal.{0}} (h : SkCtx S k l ν) (hw : SkWit l ν) :
    ∀ g, 0 < g → g < ν - l + ω ^ 2 → ω ^ 2 ∣ g →
      upsilon (l + (ν - l + ω ^ 2)) ≤ cdR S (l + g) ∨ Vr.VrForm S l (ν - l + ω ^ 2) g := by
  have hm := upsilon_normal.strictMono
  have hlk : l = Nc.ncL S (k : Ordinal.{0}) :=
    hm.injective (h.2.1.symm.trans (Te.teUps_L (S := S) k).symm)
  have hβ : ν - l + ω ^ 2 = ω ^ ω ^ (upsilon (l + 1) + 1) + ω ^ 2 * 2 := by
    have e2 : ∀ x : Ordinal.{0}, x * 2 = x + x := fun x => by
      rw [show (2 : Ordinal.{0}) = 1 + 1 by norm_num, mul_add, mul_one]
    rw [hw, add_assoc, Ordinal.add_sub_cancel, add_assoc, e2]
  rw [hβ]
  have hν : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC :=
    ((Pp.ppL_lt_omega k).trans (Qq.qqL_lt_succ S)).le.trans skNu
  obtain ⟨-, -, hF⟩ := Vr.vrForms_win (S := S) k hν
  intro z hz0 hzβ hzd
  rw [hlk] at hzβ ⊢
  exact Or.inr (hF z hz0 hzβ hzd)

/-- STATUS: PROVED (by `Wq.wqEps_u2`; NEW round 118)
SIZE: S
a window below `ε_{u₁+1}` is in the low region: ν − λ < ε_{u₁+1} ⇒ ν − λ < υ_{λ+2} -/
theorem skEpsU2 {k : ℕ} {l ν : Ordinal.{0}} (h : SkCtx S k l ν) (hE : ν - l < eN (upsilon (l + 1))) :
    ν - l < upsilon (l + 2) := by
  have hll : l = Nc.ncL S (k : Ordinal.{0}) :=
    upsilon_normal.strictMono.injective (h.2.1.symm.trans (Te.teUps_L (S := S) k).symm)
  subst hll
  exact hE.trans_le (Wq.wqEps_u2 k)

/-- STATUS: PROVED (by `Wq.wqWit_eps`; NEW round 118)
SIZE: S
the witness window lies below `ε_{u₁+1}`: ν = λ+g+ω² ⇒ ν − λ < ε_{u₁+1} -/
theorem skWitEps {l ν : Ordinal.{0}} (hw : SkWit l ν) : ν - l < eN (upsilon (l + 1)) := by
  have e : ν - l = ω ^ ω ^ (upsilon (l + 1) + 1) + ω ^ 2 := by rw [hw, add_assoc, Ordinal.add_sub_cancel]
  rw [e]; exact Wq.wqWit_eps _

/-- STATUS: REDUCED (from the shared leaf `skNu` only, by `Wq.wqForms_eps`, `Wq.wqEps_beta`; NEW round 118)
SIZE: M
the forms clause at every window below `ε_{u₁+1}` (the codes `m ≤ z < ε_{u₁+1}` have no `ε`-number in `(u₁, m]`)
ν − λ < ε_{u₁+1} ⇒ ∀ z < β(ν), ω² | z ⇒ υ_{λ+β} ≤ r(λ+z) ∨ VrForm(λ, β, z) -/
theorem skFormEps {k : ℕ} {l ν : Ordinal.{0}} (h : SkCtx S k l ν) (hE : ν - l < eN (upsilon (l + 1))) :
    ∀ g, 0 < g → g < ν - l + ω ^ 2 → ω ^ 2 ∣ g →
      upsilon (l + (ν - l + ω ^ 2)) ≤ cdR S (l + g) ∨ Vr.VrForm S l (ν - l + ω ^ 2) g := by
  have hm := upsilon_normal.strictMono
  have hlν : l < ν := hm.lt_iff_lt.1 h.2.2.2.2.2.1
  have e : l + (ν - l) = ν := Ordinal.add_sub_cancel_of_le hlν.le
  have hd : ω ^ 2 ∣ ν - l := (Ordinal.dvd_add_iff h.1.2).1 (by rw [e]; exact h.2.2.1.1.2)
  obtain ⟨hβd, hβ⟩ := Wq.wqEps_beta hd hE
  have hν : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC :=
    ((Pp.ppL_lt_omega k).trans (Qq.qqL_lt_succ S)).le.trans skNu
  have hll : l = Nc.ncL S (k : Ordinal.{0}) := hm.injective (h.2.1.symm.trans (Te.teUps_L (S := S) k).symm)
  subst hll
  intro g hg0 hgβ hgd
  exact Or.inr (Wq.wqForms_eps (S := S) k hν hβd hβ g hg0 hgβ hgd)

/-- STATUS: PROVED (a REFUTATION recorded as a node, by `Ww.wwFormHigh_fail`, `Wu.wuWin`, `Wq.wqWit_eps` and the shared
leaf `skNu`; NEW round 120.  The old node `skFormHigh` (SUSPECT in round 119) is REFUTED and removed, and with it
`skFormOther` and `skForm`, which contain it)
SIZE: M
at every `L(k)` the old forms clause fails at a high window: ¬ skFormHigh -/
theorem skFormHigh_false (k : ℕ) : ¬ (∀ l ν, SkCtx S k l ν → ¬ SkWit l ν →
    ¬ ν - l < eN (upsilon (l + 1)) → ∀ g, 0 < g → g < ν - l + ω ^ 2 → ω ^ 2 ∣ g →
      upsilon (l + (ν - l + ω ^ 2)) ≤ cdR S (l + g) ∨ Vr.VrForm S l (ν - l + ω ^ 2) g) := by
  intro H
  have hν : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC :=
    ((Pp.ppL_lt_omega k).trans (Qq.qqL_lt_succ S)).le.trans skNu
  obtain ⟨X, hXE, hX1, hX2, heN, -, hfail⟩ := Ww.wwFormHigh_fail k hν
  set l := Nc.ncL S (k : Ordinal.{0}) with hldef
  have hC : SkCtx S k l (l + X + ω ^ 2) := Wu.wuWin k hν hXE hX1 hX2
  have e : l + X + ω ^ 2 - l = X + ω ^ 2 := by rw [add_assoc, Ordinal.add_sub_cancel]
  have hE : ¬ l + X + ω ^ 2 - l < eN (upsilon (l + 1)) := by rw [e]; exact not_lt.2 (heN.trans le_self_add)
  have hW : ¬ SkWit l (l + X + ω ^ 2) := fun hw => hE (skWitEps hw)
  have hωX : ω ≤ X := Vo.vo_omega_le hXE (InE.pos hXE)
  have hω2g : ω ^ 2 ∣ X := by
    have h := Vo.vo_e2 ▸ opow_dvd_opow ω ((natCast_lt_omega0 2).trans_le hωX).le
    rwa [hXE] at h
  have hXβ : X < l + X + ω ^ 2 - l + ω ^ 2 := by
    rw [e]
    exact (lt_add_of_pos_right X (pow_pos omega0_pos 2)).trans_le le_self_add
  exact hfail (H l (l + X + ω ^ 2) hC hW hE X (InE.pos hXE) hXβ hω2g)

/-- STATUS: PROVED (round 121, by `Xa.xaForm_all`, `skWin`, `Vr.vr_facts`), OFF THE ROAD since round 121 (feeds only
`skSupW`, now REDUCED from `skSupX`; replaced on the road by `skFormHighX`) (NEW round 120; REPLACES the refuted
`skFormHigh`).  Round 121: the hypothesis `hE` is not used; every countable ordinal below `υ_{λ+β}` is the value of a
repaired decomposition (`Xa.xaRep`).
SIZE: L (was)
the REPAIRED forms clause at the windows with `ν − λ ≥ ε_{u₁+1}`: every inner reach `r(λ+z)`, `z < β(ν)`, is a big
reach or the value of a repaired decomposition (`Ww.WwForm`: old nodes and `ϑ`-nodes `ϑ^{υ_{λ+h}}(Ω₁·M + val e)` of
any level `M`).  REFUTE FIRST (round 120): NO EVIDENCE.  The refutation of the old node does not apply: at the gap
witness `X = ϑ^{u₁}(B₂ + υ_λ)` the repaired form exists at every admissible `β` (`Ww.wwForm_X`, `Ww.wwForm_gap`).
Expected proof: every point of `T^{υ_{λ+h}}` is a sum of components, each `< υ_{λ+1}` (`lo`), `υ_{λ+h}` (`sg`), or
`ϑ^{υ_{λ+h}}(Ω₁·M + η)` with `η` below it (`CitedVd.vdLevel_lt`, `CitedLu.luLt_vt_self`, `CitedLv.lvLevel_lt_vt`), by
induction on the point; plus the long region `z ≥ υ_{λ+2}` (reaches not known in Lean).
¬(ν − λ < ε_{u₁+1}) ⇒ ∀ z < β(ν), ω² | z ⇒ υ_{λ+β} ≤ r(λ+z) ∨ WwForm(λ, β, z) -/
theorem skFormHighW {k : ℕ} {l ν : Ordinal.{0}} (h : SkCtx S k l ν) (_hE : ¬ ν - l < eN (upsilon (l + 1))) :
    ∀ g, 0 < g → g < ν - l + ω ^ 2 → ω ^ 2 ∣ g →
      upsilon (l + (ν - l + ω ^ 2)) ≤ cdR S (l + g) ∨ Ww.WwForm S l (ν - l + ω ^ 2) g := by
  intro g _ _ _
  obtain ⟨-, -, -, -, -, -, hL1O, -, -⟩ := Vr.vr_facts (S := S) k
  exact Xa.xaForm_all S (pos_iff_ne_zero.2 h.1.1) ((skWin h).2.trans hL1O.le) g

/-- STATUS: PROVED (round 121, by `Xa.xaForm_all`, `skWin`, `Vr.vr_facts`; was REDUCED from `skFormEps`, `skFormHighW`),
OFF THE ROAD since round 121 (NEW round 120, REPLACES `skForm`)
SIZE: L (was)
∀ z < β(ν), ω² | z ⇒ υ_{λ+β} ≤ r(λ+z) ∨ WwForm(λ, β, z) -/
theorem skFormW {k : ℕ} {l ν : Ordinal.{0}} (h : SkCtx S k l ν) :
    ∀ g, 0 < g → g < ν - l + ω ^ 2 → ω ^ 2 ∣ g →
      upsilon (l + (ν - l + ω ^ 2)) ≤ cdR S (l + g) ∨ Ww.WwForm S l (ν - l + ω ^ 2) g := by
  intro g _ _ _
  obtain ⟨-, -, -, -, -, -, hL1O, -, -⟩ := Vr.vr_facts (S := S) k
  exact Xa.xaForm_all S (pos_iff_ne_zero.2 h.1.1) ((skWin h).2.trans hL1O.le) g

/-! ## The supply clause `Vr.VrSup` at `β(ν)` -/

/-- STATUS: PROVED (by `Ls.lsNames_M`, `Ls.lsNames_L`, `Qq.qqL_lt_omega`)
SIZE: S
∀ γ < L(k) ∃ μ: Range(μ), γ < υ_μ < L(k) < L(ω), code(μ) = G₂+1 -/
theorem skCodeCof (k : ℕ) : ∀ γ < Nc.ncL S (k : Ordinal.{0}), ∃ μ, CdRange S μ ∧ γ < upsilon μ ∧
    upsilon μ < Nc.ncL S (k : Ordinal.{0}) ∧ cdCode S μ = Ls.lsG S (0 + 1 + 1) + 1 ∧
    upsilon μ < Nc.ncL S ω := by
  intro γ hγ
  rcases k with _ | n
  · have hγ' : γ < Nc.ncL S 0 := by simpa using hγ
    obtain ⟨μ, hR, h1, h2, hc⟩ := Ls.lsNames_M (S := S) 1 γ hγ'
    refine ⟨μ, hR, h1, by simpa using h2, hc, ?_⟩
    exact h2.trans (by simpa using Qq.qqL_lt_omega S 0)
  · obtain ⟨μ, hR, h1, h2, hc⟩ := Ls.lsNames_L (S := S) n 1 γ hγ
    exact ⟨μ, hR, h1, h2, hc, h2.trans (Qq.qqL_lt_omega S (n + 1))⟩

/-- STATUS: PROVED (by `Wk.wkRead0`; round 117.  The lift of `Rx.rxLift` one level at a time: for members
`ζ < ψ_{Ω₂}(Ω_n)` the atoms `ψ_{Ω₂}(Ω_{n+1} + κ ζ) < θ` of `At_C`, closure condition by `Wk.wkL_memN_lt`; `θ = sup_n
ψ_{Ω₂}(Ω_n)` (`Wk.wkTh_cof`); continuity of `ψ_{Ω₁}` at `A + θ`.  Consequences: `Θ_C(θ) = Θ_μ(θ) = υ_{μ+1}`
(`Wk.wkRead0_eq`, `Wk.wkTheta_th`))
SIZE: L
Range(μ), code(μ) = G₂+1, υ_μ < L(ω) ⇒ υ_{μ+1} ≤ Θ_C(θ) -/
theorem skRead0 : ∀ μ, CdRange S μ → cdCode S μ = Ls.lsG S (0 + 1 + 1) + 1 → upsilon μ < Nc.ncL S ω →
    Wc.WcRead0 S μ := fun _ hR hc hω => Wk.wkRead0 hR hc hω

/-- STATUS: PROVED (from `skCodeCof`, `skRead0`, both PROVED; round 117)
SIZE: L
∀ γ < υ_λ ∃ μ: γ < υ_μ < υ_λ, SkMu(μ) -/
theorem skMu {k : ℕ} {l ν : Ordinal.{0}} (h : SkCtx S k l ν) :
    ∀ γ < upsilon l, ∃ μ, γ < upsilon μ ∧ upsilon μ < upsilon l ∧ SkMu S μ := by
  intro γ hγ
  rw [← h.2.1] at hγ ⊢
  obtain ⟨μ, hR, h1, h2, hc, hω⟩ := skCodeCof (S := S) k γ hγ
  exact ⟨μ, h1, h2, hR, hc, hω, skRead0 μ hR hc hω⟩

/-- STATUS: REDUCED, OFF THE ROAD since round 118 (`skCarryEps` asks the map with its image clause, `skImgEps`)
(by `Wf.wfOffMap` and the shared leaf `skNu` only; round 116.  Was SUSPECT: the restricted exponent clause asks nothing
at `z = ω^{υ_μ}` since `υ_μ ∉ T^{υ_λ}[υ_μ]`; `WcPiLo` restricted is the theorem `Wf.wfPiLo`; the side hypothesis
`hside` of `Wc.wcSupLo` is REFUTED (`Wf.wfSide_false`) and not used: `Wf.wfOffMap` builds the block map on the blocks
of every `Os` and derives the side conditions for that map)
SIZE: M
ν witness, SkMu(μ), υ_μ < υ_λ, Os ⊂ β ⇒ ∃ f B, SkMapP (restricted) -/
theorem skOffMapW {k : ℕ} {l ν : Ordinal.{0}} (h : SkCtx S k l ν) (_hw : SkWit l ν) :
    ∀ μ, upsilon μ < upsilon l → SkMu S μ → ∀ Os : Finset Ordinal.{0}, (∀ d ∈ Os, d < ν - l + ω ^ 2) →
      ∃ f B, SkMapP S l μ f B Os := by
  intro μ hμl hM Os _
  have hlν : upsilon l < nuC := by
    have h3 := h.2.2.2.2.1
    have hk : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC :=
      ((Pp.ppL_lt_omega k).trans (Qq.qqL_lt_succ S)).le.trans skNu
    exact (h.2.2.2.2.2.1.trans h3).trans_le hk
  obtain ⟨f, B, h1, h2, h3, h4, h5, h6, -, -⟩ :=
    Wf.wfOffMap (S := S) k h.2.1 hM.1 hM.2.1 hM.2.2.1 hM.2.2.2 hμl hlν Os
  exact ⟨f, B, h1, h2, h3, h4, h5, h6⟩

/-- STATUS: REDUCED, OFF THE ROAD since round 118 (used inside `Wq.wqCarry_low`)
(by `Wk.wkLowerF` and the shared leaf `skLowRR`; RESTATED round 117: the window hypothesis
`hwin`.  No code of `μ + f z` is needed: `υ_μ < υ_{μ+f z} < υ_λ = L(k)` lies above a window `w` of `L(k)`, so
`Ty.tyWin_rng` gives Range and `RzRest`.  The old statement (all `μ` below `υ_λ`) is REPLACED: below the window
`μ + f z` may hit an index `L(j)` (code `P′`, not Range))
SIZE: M
w window of L(k), w < υ_μ, SkMapP ⇒ ∀ z ∈ Os, 0 < z, ω² | z ⇒ LOWER(μ + f z) -/
theorem skLowerF {k : ℕ} {l ν : Ordinal.{0}} (h : SkCtx S k l ν) (_hw : SkWit l ν) :
    ∀ μ, upsilon μ < upsilon l → SkMu S μ → (∃ w, Ty.TyWin S k w ∧ w < upsilon μ) →
      ∀ (Os : Finset Ordinal.{0}) f B, (∀ d ∈ Os, d < ν - l + ω ^ 2) →
      SkMapP S l μ f B Os → ∀ g ∈ Os, 0 < g → ω ^ 2 ∣ g → CdLower S (μ + f g) := by
  intro μ _ hM hwin Os f B _ hP
  obtain ⟨w, hw, hwμ⟩ := hwin
  exact Wk.wkLowerF skLowRR h.2.1 hw hwμ hM.1.1 hP.1 hP.2.2.2.1

/-- STATUS: REDUCED (from the shared leaf `skNu` only, by `Wq.wqBigLow`; round 118, was OPEN)
SIZE: M
the big-reach clause at the offset `z = ν − λ` of `ν` itself.  VACUOUS: the witness window is low (`skWitEps`,
`skEpsU2`), and there `r(ν) = υ_{ν+ω+1} + m_ν < υ_{ν+ω²}` (`Wq.wqBigTop`).
ν − λ ∈ Os, υ_{ν+ω²} ≤ r(ν) ⇒ υ_{μ+B} ≤ r(μ + f(ν − λ)) -/
theorem skBigTop {k : ℕ} {l ν : Ordinal.{0}} (h : SkCtx S k l ν) (hw : SkWit l ν) :
    ∀ μ, upsilon μ < upsilon l → SkMu S μ → ∀ (Os : Finset Ordinal.{0}) f B, (∀ d ∈ Os, d < ν - l + ω ^ 2) →
      SkMapP S l μ f B Os → ν - l ∈ Os →
        (upsilon (l + (ν - l + ω ^ 2)) ≤ cdR S ν → upsilon (μ + B) ≤ cdR S (μ + f (ν - l))) := by
  intro μ _ _ Os f B _ _ hm hbig
  have hlν : l < ν := upsilon_normal.strictMono.lt_iff_lt.1 h.2.2.2.2.2.1
  have e : l + (ν - l) = ν := Ordinal.add_sub_cancel_of_le hlν.le
  have hd : ω ^ 2 ∣ ν - l := (Ordinal.dvd_add_iff h.1.2).1 (by rw [e]; exact h.2.2.1.1.2)
  have hd0 : 0 < ν - l := by
    rcases eq_or_lt_of_le (zero_le : (0 : Ordinal.{0}) ≤ ν - l) with h0 | h0
    · rw [← h0, add_zero] at e; exact absurd e hlν.ne
    · exact h0
  have hν : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC :=
    ((Pp.ppL_lt_omega k).trans (Qq.qqL_lt_succ S)).le.trans skNu
  exact Wq.wqBigLow (μ := μ) (B := B) (f := f) (Os := Os) hν h.1 h.2.2.1.1 h.2.2.2.2.2.1 h.2.1 h.2.2.2.2.1
    h.2.2.2.2.2.2.1 (skEpsU2 h (skWitEps hw)) (ν - l) hm hd0 hd
    (lt_add_of_pos_right _ (pow_pos omega0_pos 2)) (by rw [e]; exact hbig)

/-- STATUS: REDUCED, OFF THE ROAD since round 118 (the same clause is `Wq.wqBigLow` inside `Wq.wqCarry_low`)
(by `Wk.wkBigF` from `skBigTop`; round 117: every offset `z` with `λ + z < ν` is vacuous since `ν`
is not covered (`Wk.wkBig_vac`), and the only other offset `z < β` with `ω² | z` is `z = ν − λ` (`Wk.wkTop_eq`))
SIZE: M
the big-reach clause of `Wf.WfCarry`
υ_{λ+β} ≤ r(λ+z) ⇒ υ_{μ+B} ≤ r(μ+f z) -/
theorem skBigF {k : ℕ} {l ν : Ordinal.{0}} (h : SkCtx S k l ν) (hw : SkWit l ν) :
    ∀ μ, upsilon μ < upsilon l → SkMu S μ → ∀ (Os : Finset Ordinal.{0}) f B, (∀ d ∈ Os, d < ν - l + ω ^ 2) →
      SkMapP S l μ f B Os → ∀ g ∈ Os, 0 < g → ω ^ 2 ∣ g →
        (upsilon (l + (ν - l + ω ^ 2)) ≤ cdR S (l + g) → upsilon (μ + B) ≤ cdR S (μ + f g)) := by
  intro μ hμ hM Os f B hOs hP g hg hg0 hgd
  exact Wk.wkBigF h.1 h.2.2.1.1 h.2.2.2.2.2.1 h.2.1 h.2.2.2.2.1 h.2.2.2.2.2.2.1
    (fun hm => skBigTop h hw μ hμ hM Os f B hOs hP hm) g hg hg0 hgd (hOs g hg)

/-- STATUS: PROVED (refuter round: `exists_next` gives `c ∈ T^{υ_λ}`, `Par_sub` gives `Par ⊆ υ_λ`; the suspicion
below is void; same proof as `R2Skel.SkSX.skSX_piT`)
SIZE: M
(old note) `π` is an axiom constant fixed only on `TB(υ_λ, υ_μ)` (`Cited.pi_lt`, `pi_add`, …): every leaf `c < u₁` moved by
`π` in `Vr.vrImg` must lie in `TB(υ_λ, σ)` for all large `σ < υ_λ`, else the carry (and `WcPiLo`) is independent of
the axioms (neither provable nor refutable).  No Lean lemma gives `Tset(υ_λ)`-membership on `[υ_λ, u₁)`.
∀ c, υ_λ ≤ c < u₁ ⇒ ∃ σ₀ < υ_λ, ∀ σ ∈ [σ₀, υ_λ), Bases(σ, υ_λ) ⇒ c ∈ TB(υ_λ, σ) -/
theorem skPiT {k : ℕ} {l ν : Ordinal.{0}} (h : SkCtx S k l ν) :
    ∀ c, upsilon l ≤ c → c < upsilon (l + 1) → ∃ σ₀ < upsilon l, ∀ σ, σ₀ ≤ σ → Bases σ (upsilon l) →
      c ∈ TB (upsilon l) σ := by
  have hτ : UpsPt (upsilon l) := upsPt_upsilon (pos_iff_ne_zero.2 h.1.1)
  have hn : IsNext (upsilon l) (upsilon (l + 1)) := by
    have := upsilon_isNext l; rwa [Order.succ_eq_add_one] at this
  intro c _ hcu
  by_cases h1 : upsilon l < Om1
  · obtain ⟨m, hm, hT⟩ := exists_next hτ h1
    have hmu : m = upsilon (l + 1) := hm.unique hn
    have hu1 : upsilon (l + 1) < Om1 := next_lt_Om1 hn (Or.inr hτ) h1
    have hcT : c ∈ Tset (upsilon l) := (hT c (hcu.trans hu1)).2 (hmu ▸ hcu)
    have hP : ↑(Par (upsilon l) c) ⊆ Set.Iio (upsilon l) := Par_sub (upsPt_inE hτ) h1 hcT
    set s := (Par (upsilon l) c).sup id with hs
    have hsl : s < upsilon l := by
      rcases (Par (upsilon l) c).eq_empty_or_nonempty with he | hne
      · have : s = ⊥ := by rw [hs, he]; rfl
        rw [this]; exact hτ.1
      · obtain ⟨p, hp, hpe⟩ := Finset.exists_mem_eq_sup (Par (upsilon l) c) hne id
        rw [hs, hpe]; exact hP hp
    have hτl : IsSuccLimit (upsilon l) := by
      have hE : InE (upsilon l) := upsPt_inE hτ
      have : IsSuccLimit (ω ^ upsilon l) := isSuccLimit_opow_left isSuccLimit_omega0 hτ.1.ne'
      unfold InE at hE; rwa [hE] at this
    refine ⟨s + 1, hτl.add_one_lt hsl, fun σ hσ _ => ⟨hcT, fun p hp => ?_⟩⟩
    have : p ≤ s := Finset.le_sup (f := id) hp
    exact lt_of_lt_of_le (Order.lt_add_one_iff.2 this) hσ
  · exact ⟨0, hτ.1, fun σ _ hB => absurd hB.2.2.2 h1⟩

/-- STATUS: PROVED (a REFUTATION recorded as a node, by `Wq.wqWitCtx`, `Wq.wqMu_ex`, `Wq.wqImgF_ref` and the shared
leaf `skNu`; round 118.  The old node `skImgF` is REFUTED, see `skImgF_false`)
SIZE: L
at every `L(k)` the witness context exists, and for a supply restart `μ` there are `Os ⊂ β(ν)`, `f`, `B` with
`SkMapP` and a decomposition `E` with every hypothesis of the image clause and `r(μ + f z) < img E`
(`z = ω^{u₁}`, `f z = ω²`, `E = ub(z+ω+1) base + ub 1 base`) -/
theorem skImgF_ref (k : ℕ) : ∃ l ν, SkCtx S k l ν ∧ SkWit l ν ∧ ∃ μ, upsilon μ < upsilon l ∧ SkMu S μ ∧
    ∃ (Os : Finset Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}) (B : Ordinal.{0}),
      (∀ d ∈ Os, d < ν - l + ω ^ 2) ∧ SkMapP S l μ f B Os ∧ ∃ g ∈ Os, 0 < g ∧ ω ^ 2 ∣ g ∧
        ∃ E : Vr.VrE, Vr.VrWF l (ν - l + ω ^ 2) E ∧ Vr.vrVal l E = cdR S (l + g) ∧ Vr.VrOs l Os E ∧
          Wf.WfR l μ E ∧ cdR S (μ + f g) < Vr.vrImg l μ f E := by
  have hν : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC :=
    ((Pp.ppL_lt_omega k).trans (Qq.qqL_lt_succ S)).le.trans skNu
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := Wq.wqWitCtx (S := S) k hν
  have hl0 : 0 < Nc.ncL S (k : Ordinal.{0}) := pos_iff_ne_zero.2 h1.1
  obtain ⟨μ, hR, -, hμk, hc, hω, hr⟩ := Wq.wqMu_ex (S := S) k 0 hl0
  have hμl : upsilon μ < upsilon (Nc.ncL S (k : Ordinal.{0})) := hμk.trans_eq h2
  have e : Nc.ncL S (k : Ordinal.{0}) + ω ^ ω ^ (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1) + 1) + ω ^ 2 -
      Nc.ncL S (k : Ordinal.{0}) = ω ^ ω ^ (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1) + 1) + ω ^ 2 := by
    rw [add_assoc, Ordinal.add_sub_cancel]
  have hgβ : ω ^ ω ^ (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1) + 1) ≤
      Nc.ncL S (k : Ordinal.{0}) + ω ^ ω ^ (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1) + 1) + ω ^ 2 -
        Nc.ncL S (k : Ordinal.{0}) + ω ^ 2 := by
    rw [e]; exact le_self_add.trans le_self_add
  obtain ⟨Os, f, B, z, E, hOs, hB1, hB2, hB3, hO, hwit, hexp, hzO, hz0, hzd, hWF, hval, hOsE, hWR, hlt⟩ :=
    Wq.wqImgF_ref (S := S) k hν hR hc hω hr hμl hgβ
  exact ⟨_, _, ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩, rfl, μ, hμl, ⟨hR, hc, hω, hr⟩, Os, f, B, hOs,
    ⟨hB1, hB2, hB3, hO, hwit, hexp⟩, z, hzO, hz0, hzd, E, hWF, hval, hOsE, hWR, hlt⟩

/-- STATUS: PROVED (REFUTATION of the old node `skImgF`, from `skImgF_ref`; round 118)
SIZE: S
the old `skImgF` (the image clause for EVERY offset map with `SkMapP`) is false; it is REPLACED by `skImgEps`
(`∃ f B`) -/
theorem skImgF_false : ¬ (∀ {k : ℕ} {l ν : Ordinal.{0}}, SkCtx S k l ν → SkWit l ν →
    ∀ μ, upsilon μ < upsilon l → SkMu S μ → ∀ (Os : Finset Ordinal.{0}) f B, (∀ d ∈ Os, d < ν - l + ω ^ 2) →
      SkMapP S l μ f B Os → ∀ g ∈ Os, 0 < g → ω ^ 2 ∣ g →
        ∀ E : Vr.VrE, Vr.VrWF l (ν - l + ω ^ 2) E → Vr.vrVal l E = cdR S (l + g) → Vr.VrOs l Os E →
          Wf.WfR l μ E → Vr.vrImg l μ f E ≤ cdR S (μ + f g)) := by
  intro H
  obtain ⟨l, ν, h, hw, μ, hμ, hM, Os, f, B, hOs, hP, g, hg, hg0, hgd, E, h1, h2, h3, h4, hlt⟩ :=
    skImgF_ref (S := S) 0
  exact absurd (H h hw μ hμ hM Os f B hOs hP g hg hg0 hgd E h1 h2 h3 h4) (not_le.2 hlt)

/-- STATUS: OPEN, OFF THE ROAD since round 120 (feeds only Wf.WfSup, implied by skSupKW via Ww.wwSup_wf); (NEW round 118; REPLACES the refuted `skImgF`)
SIZE: L
the image clause for ONE map: at every window below `ε_{u₁+1}` (all codes `≤ z < ε_{u₁+1}`), for every supply
restart `μ` above a window of `L(k)` and every `Os ⊂ β(ν)`, a map `f` with bound `B` (`μ + B ≤ λ`, `ω² | B`,
`υ_{μ+B} ≤ r(μ)`, `Sl.SlOff f Os B`) whose image clause holds for every decomposition with `Wf.WfR`.
REFUTE FIRST: NO EVIDENCE (`Wq.wqImgF_ref` refutes only the `∀ f` form; `Wf.wfOffMap` gives a map with EQ at the
witness decomposition and at the low decompositions `ub(z+ω+1) + lo(m z)`).  Left: (i) the code move at offsets with
`u₁ ≤ m z < ε_{u₁+1}` (`f z` with `m(f z) ≥` the image of the code over `u' = υ_{μ+1}`; for `m z > ω^{u₁+1}` this
needs `B > Wc.wcX`, i.e. a supply `υ_{μ+B} ≤ r(μ)` past `WcRead0`), (ii) the image of a decomposition depends only on
its value (`ub` / `sg` / `tm` nodes over `u₁` and over `υ_{λ+(z+ω+1)}`).
Round 119: REFUTE FIRST on (ii): NO EVIDENCE (`skImgVal`, `Vr.vrImg_agree`).  (i): the supply `υ_{μ+B} ≤ r(μ)` for every
`B ≤ φ(1, u'+1)` (so every `B < ε_{u'+1}`) is PROVED (`skSupEps`, `Wu.wuSup_lt`); left: the code move itself (an `f`
with `m(f z) ≥` the image of `m z` over `u'`) and (ii) as a Lean statement over all decompositions. -/
theorem skImgEps {k : ℕ} {l ν : Ordinal.{0}} (h : SkCtx S k l ν) (hE : ν - l < eN (upsilon (l + 1))) :
    ∀ μ, upsilon μ < upsilon l → SkMu S μ → (∃ w, Ty.TyWin S k w ∧ w < upsilon μ) →
      ∀ Os : Finset Ordinal.{0}, (∀ d ∈ Os, d < ν - l + ω ^ 2) →
      ∃ f B, μ + B ≤ l ∧ ω ^ 2 ∣ B ∧ upsilon (μ + B) ≤ cdR S μ ∧ Sl.SlOff f Os B ∧
        ∀ g ∈ Os, 0 < g → ω ^ 2 ∣ g →
          ∀ E : Vr.VrE, Vr.VrWF l (ν - l + ω ^ 2) E → Vr.vrVal l E = cdR S (l + g) → Vr.VrOs l Os E →
            Wf.WfR l μ E → Vr.vrImg l μ f E ≤ cdR S (μ + f g) := by sorry

/-- STATUS: REDUCED, OFF THE ROAD since round 120 (feeds only Wf.WfSup, implied by skSupKW via Ww.wwSup_wf); (from `skImgEps`, `skEpsU2`, the shared leaves `skLowRR`, `skNu`, by `Wq.wqCarry_low`; NEW
round 118)
SIZE: L
the supply data and `WfCarry` at every window below `ε_{u₁+1}` (LOWER by `Wk.wkLowerF`, big reach vacuous by
`Wq.wqBigLow`, image clause by `skImgEps`) -/
theorem skCarryEps {k : ℕ} {l ν : Ordinal.{0}} (h : SkCtx S k l ν) (hE : ν - l < eN (upsilon (l + 1))) :
    ∀ μ, upsilon μ < upsilon l → SkMu S μ → (∃ w, Ty.TyWin S k w ∧ w < upsilon μ) →
      ∀ Os : Finset Ordinal.{0}, (∀ d ∈ Os, d < ν - l + ω ^ 2) →
      ∃ f B, μ + B ≤ l ∧ ω ^ 2 ∣ B ∧ upsilon (μ + B) ≤ cdR S μ ∧ Sl.SlOff f Os B ∧
        Wf.WfCarry S l (ν - l + ω ^ 2) μ f B Os := by
  intro μ hμ hM hwin Os hOs
  obtain ⟨f, B, h1, h2, h3, h4, hI⟩ := skImgEps h hE μ hμ hM hwin Os hOs
  obtain ⟨w, hw, hwμ⟩ := hwin
  have hν : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC :=
    ((Pp.ppL_lt_omega k).trans (Qq.qqL_lt_succ S)).le.trans skNu
  exact ⟨f, B, h1, h2, h3, h4, Wq.wqCarry_low skLowRR hν h.1 h.2.2.1.1 h.2.2.2.2.2.1 h.2.1 h.2.2.2.2.1
    h.2.2.2.2.2.2.1 (skEpsU2 h hE) hw hwμ hM.1.1 h1 h4 hOs hI⟩

/-- STATUS: REDUCED, OFF THE ROAD since round 120 (feeds only Wf.WfSup, implied by skSupKW via Ww.wwSup_wf); (from `skCarryEps`, `skWitEps`; round 118: was from `skOffMapW`, `skLowerF`, `skBigF`, `skImgF`,
the last one REFUTED)
SIZE: L
ν witness, μ above a window of L(k) ⇒ the supply data and `WfCarry` at every `μ` of `skMu` -/
theorem skCarryWit {k : ℕ} {l ν : Ordinal.{0}} (h : SkCtx S k l ν) (hw : SkWit l ν) :
    ∀ μ, upsilon μ < upsilon l → SkMu S μ → (∃ w, Ty.TyWin S k w ∧ w < upsilon μ) →
      ∀ Os : Finset Ordinal.{0}, (∀ d ∈ Os, d < ν - l + ω ^ 2) →
      ∃ f B, μ + B ≤ l ∧ ω ^ 2 ∣ B ∧ upsilon (μ + B) ≤ cdR S μ ∧ Sl.SlOff f Os B ∧
        Wf.WfCarry S l (ν - l + ω ^ 2) μ f B Os :=
  skCarryEps h (skWitEps hw)

/-- STATUS: OPEN, OFF THE ROAD since round 120 (feeds only Wf.WfSup, implied by skSupKW via Ww.wwSup_wf); (NEW round 118; the part of the old `skCarryOther` left; round 119: moot if `skGap` holds, since then
the forms clause already fails at these windows)
SIZE: L
the supply and carry at the windows with `ν − λ ≥ ε_{u₁+1}`: offsets with codes `≥ ε_{u₁+1}` (`z < υ_{λ+2}`) and the
long region (`z ≥ υ_{λ+2}`, reaches not known in Lean), a supply past `X` (readings at the code levels `θ_{k+2}`
beyond `WcRead0`).  REFUTE FIRST: NO EVIDENCE (`Wq.wqImgF_ref` is about the `∀ f` form only).
¬(ν − λ < ε_{u₁+1}) ⇒ the same as `skCarryWit` -/
theorem skCarryHigh {k : ℕ} {l ν : Ordinal.{0}} (h : SkCtx S k l ν) (hw : ¬ SkWit l ν)
    (hE : ¬ ν - l < eN (upsilon (l + 1))) :
    ∀ μ, upsilon μ < upsilon l → SkMu S μ → (∃ w, Ty.TyWin S k w ∧ w < upsilon μ) →
      ∀ Os : Finset Ordinal.{0}, (∀ d ∈ Os, d < ν - l + ω ^ 2) →
      ∃ f B, μ + B ≤ l ∧ ω ^ 2 ∣ B ∧ upsilon (μ + B) ≤ cdR S μ ∧ Sl.SlOff f Os B ∧
        Wf.WfCarry S l (ν - l + ω ^ 2) μ f B Os := by sorry

/-- STATUS: REDUCED, OFF THE ROAD since round 120 (feeds only Wf.WfSup, implied by skSupKW via Ww.wwSup_wf); (from `skCarryEps`, `skCarryHigh`; round 118, was OPEN)
SIZE: L
¬ witness ⇒ the same as `skCarryWit` -/
theorem skCarryOther {k : ℕ} {l ν : Ordinal.{0}} (h : SkCtx S k l ν) (hw : ¬ SkWit l ν) :
    ∀ μ, upsilon μ < upsilon l → SkMu S μ → (∃ w, Ty.TyWin S k w ∧ w < upsilon μ) →
      ∀ Os : Finset Ordinal.{0}, (∀ d ∈ Os, d < ν - l + ω ^ 2) →
      ∃ f B, μ + B ≤ l ∧ ω ^ 2 ∣ B ∧ upsilon (μ + B) ≤ cdR S μ ∧ Sl.SlOff f Os B ∧
        Wf.WfCarry S l (ν - l + ω ^ 2) μ f B Os := by
  by_cases hE : ν - l < eN (upsilon (l + 1))
  · exact skCarryEps h hE
  · exact skCarryHigh h hw hE

/-- STATUS: REDUCED, OFF THE ROAD since round 120 (feeds only Wf.WfSup, implied by skSupKW via Ww.wwSup_wf); (from `skMu`, `skCarryWit`, `skCarryOther`; RESTATED round 116; round 117: `μ` is taken above
`max(γ, w)` for a window `w` of `L(k)`, `Wk.wkWin_ex`)
SIZE: L
WfSup(λ, β(ν)) -/
theorem skSupK {k : ℕ} {l ν : Ordinal.{0}} (h : SkCtx S k l ν) : Wf.WfSup S l (ν - l + ω ^ 2) := by
  intro γ hγ Os hOs
  obtain ⟨w, hw⟩ := Wk.wkWin_ex (S := S) k
  have hwl : w < upsilon l := hw.2.1.trans_eq h.2.1
  obtain ⟨μ, h1, h2, hM⟩ := skMu h (max γ w) (max_lt hγ hwl)
  have hwin : ∃ w, Ty.TyWin S k w ∧ w < upsilon μ := ⟨w, hw, (le_max_right γ w).trans_lt h1⟩
  have hc : ∃ f B, μ + B ≤ l ∧ ω ^ 2 ∣ B ∧ upsilon (μ + B) ≤ cdR S μ ∧ Sl.SlOff f Os B ∧
      Wf.WfCarry S l (ν - l + ω ^ 2) μ f B Os := by
    by_cases hw : SkWit l ν
    · exact skCarryWit h hw μ h2 hM hwin Os hOs
    · exact skCarryOther h hw μ h2 hM hwin Os hOs
  obtain ⟨f, B, hB, hd, hs, ho, hC⟩ := hc
  exact ⟨μ, f, B, hM.1, (le_max_left γ w).trans_lt h1, h2, hB, hd, hs, ho, hC⟩

/-- STATUS: PROVED (by `Wf.wfPiLo`; round 116)
SIZE: S
the exponent clause `WcPiLo` restricted to `T^{υ_λ}[υ_μ]` is a theorem:
Bases(υ_μ, υ_λ), c ∈ T^{υ_λ}[υ_μ], c < Ω₁ ⇒ π(c) < ω^{υ_{μ+1}+1} -/
theorem skPiLo {l μ c : Ordinal.{0}} (hB : Bases (upsilon μ) (upsilon l))
    (hc : c ∈ TB (upsilon l) (upsilon μ)) (hc1 : c < Om1) :
    pi (upsilon μ) (upsilon l) c < ω ^ (upsilon (μ + 1) + 1) :=
  Wf.wfPiLo hB hc hc1

/-- STATUS: PROVED (by `Wf.wfSide_false`; round 116; a REFUTATION recorded as a node)
SIZE: S
the side hypothesis `hside` of `Wc.wcQ_carry` / `Wc.wcSupLo` (bounds for EVERY block map `Q`) is false as soon as
`Os` has an element `z ≠ g`; the old route `skOffMapW ← Wc.wcSupLo` was vacuous there -/
theorem skSideRef {μ g : Ordinal.{0}} {Os : Finset Ordinal.{0}} (hz : ∃ z ∈ Os, z ≠ g) :
    ¬ ∀ Q : Ordinal.{0} → Ordinal.{0}, ∀ z ∈ Os, z ≠ g →
      ω ≤ Vy.vyMap Q z ∧ Vy.vyMap Q z < upsilon (μ + 2) ∧ upsilon (μ + Vy.vyMap Q z + ω + 1) < nuC :=
  Wf.wfSide_false hz

/-! ## Round 119: the supply past `Wc.wcX`, the image test, the high windows and the refutation of `skFormHigh` -/

/-- STATUS: PROVED (by `Wu.wuSup`, `Wu.wuEN_le`; NEW round 119)
SIZE: M
the supply past `Wc.wcX` at every supply restart: SkMu(μ) ⇒ υ_{μ+φ(1,u'+1)} ≤ r(μ), ε_{u'+1} ≤ φ(1,u'+1) -/
theorem skSupEps : ∀ μ, SkMu S μ →
    upsilon (μ + Wu.wuX (upsilon (μ + 1))) ≤ cdR S μ ∧ eN (upsilon (μ + 1)) ≤ Wu.wuX (upsilon (μ + 1)) :=
  fun _ hM => ⟨(Wu.wuSup (k := 0) hM.1 hM.2.1 hM.2.2.1 hM.2.2.2).2.2.2, Wu.wuEN_le _⟩

/-- STATUS: PROVED (by `Wu.wuImg_test`; NEW round 119; REFUTE-FIRST test of "the image is a function of the value")
SIZE: S
the three decompositions `ub h base + ub 1 base`, `ub h (base + u₁)`, `ub h base + tm 1 base` of `υ_{λ+h} + u₁` (the value
of `Wq.wqImgF_ref`) have one image for every `f` -/
theorem skImgVal (l μ h δ : Ordinal.{0}) (Lf : Finset Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}) :
    Vr.vrImg l μ f (.add (.ub h .base) (.ub 1 .base)) =
        Vr.vrImg l μ f (.ub h (.add .base (.par (upsilon (l + 1))))) ∧
      Vr.vrImg l μ f (.add (.ub h .base) (.ub 1 .base)) = Vr.vrImg l μ f (.add (.ub h .base) (.tm 1 .base Lf δ)) := by
  obtain ⟨-, h1, h2, h3⟩ := Wu.wuImg_test l μ h δ Lf f
  exact ⟨h1.trans h2.symm, h1.trans h3.symm⟩

/-- STATUS: REDUCED (from the shared leaf `skNu` only, by `Wu.wuWin`, `Wu.wuWin_high`; NEW round 119; NON-VACUITY of
`skFormHigh` / `skCarryHigh`)
SIZE: S
a high window exists at every `L(k)`: ν = λ + ε_{u₁+1} + ω², SkCtx, ¬ SkWit, ¬(ν − λ < ε_{u₁+1}) -/
theorem skHighWin (k : ℕ) :
    SkCtx S k (Nc.ncL S (k : Ordinal.{0}))
        (Nc.ncL S (k : Ordinal.{0}) + eN (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1)) + ω ^ 2) ∧
      ¬ SkWit (Nc.ncL S (k : Ordinal.{0}))
        (Nc.ncL S (k : Ordinal.{0}) + eN (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1)) + ω ^ 2) ∧
      ¬ (Nc.ncL S (k : Ordinal.{0}) + eN (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1)) + ω ^ 2 -
          Nc.ncL S (k : Ordinal.{0}) < eN (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1))) := by
  have hν : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC :=
    ((Pp.ppL_lt_omega k).trans (Qq.qqL_lt_succ S)).le.trans skNu
  obtain ⟨h1, h2, h3⟩ := Wu.wuWin_high (S := S) k
  have hu : upsilon (Nc.ncL S (k : Ordinal.{0}) + 1) < eN (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1)) :=
    lt_of_lt_of_le (lt_add_one _) (le_nfp _ _)
  exact ⟨Wu.wuWin k hν (eN_E _) hu h1, h3, h2⟩

/-- STATUS: PROVED, SUPERSEDED round 120 by the unconditional `skFormHigh_false` / `skSup_false` (a CONDITIONAL REFUTATION recorded as a node, by `Wu.wuFormHigh_fail`, `Wu.wuWin`, `Wq.wqWit_eps` and
the shared leaf `skNu`; NEW round 119)
SIZE: M
`WuGap S k` refutes `skFormHigh` at `L(k)`: at the window `ν_X = λ + X + ω²` the forms clause fails at the offset `X` -/
theorem skFormHigh_ref (k : ℕ) (hG : Wu.WuGap S k) : ¬ (∀ l ν, SkCtx S k l ν → ¬ SkWit l ν →
    ¬ ν - l < eN (upsilon (l + 1)) → ∀ g, 0 < g → g < ν - l + ω ^ 2 → ω ^ 2 ∣ g →
      upsilon (l + (ν - l + ω ^ 2)) ≤ cdR S (l + g) ∨ Vr.VrForm S l (ν - l + ω ^ 2) g) := by
  intro H
  have hν : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC :=
    ((Pp.ppL_lt_omega k).trans (Qq.qqL_lt_succ S)).le.trans skNu
  obtain ⟨X, hXE, hX1, hX2, heN, -, hfail⟩ := Wu.wuFormHigh_fail k hν hG
  set l := Nc.ncL S (k : Ordinal.{0}) with hldef
  have hC : SkCtx S k l (l + X + ω ^ 2) := Wu.wuWin k hν hXE hX1 hX2
  have e : l + X + ω ^ 2 - l = X + ω ^ 2 := by rw [add_assoc, Ordinal.add_sub_cancel]
  have hE : ¬ l + X + ω ^ 2 - l < eN (upsilon (l + 1)) := by rw [e]; exact not_lt.2 (heN.trans le_self_add)
  have hW : ¬ SkWit l (l + X + ω ^ 2) := fun hw => hE (skWitEps hw)
  have hωX : ω ≤ X := Vo.vo_omega_le hXE (InE.pos hXE)
  have hω2g : ω ^ 2 ∣ X := by
    have h := Vo.vo_e2 ▸ opow_dvd_opow ω ((natCast_lt_omega0 2).trans_le hωX).le
    rwa [hXE] at h
  have hXβ : X < l + X + ω ^ 2 - l + ω ^ 2 := by
    rw [e]
    exact (lt_add_of_pos_right X (pow_pos omega0_pos 2)).trans_le le_self_add
  exact hfail (H l (l + X + ω ^ 2) hC hW hE X (InE.pos hXE) hXβ hω2g)

/-- STATUS: PROVED, SUPERSEDED round 120 by the unconditional `skFormHigh_false` / `skSup_false` (by `Wu.wuRoad_vac`; NEW round 119; a CONDITIONAL REFUTATION of the road)
SIZE: S
`WuGap S 0` makes the supply hypothesis `h0'` of `Wf.wfRoad` (the first half of the top `skSup`) incompatible with
`L(1) ≤ ν_C` (a consequence of the road's own conclusion): the road would be vacuous -/
theorem skRoadRef (hG : Wu.WuGap S 0) :
    ¬ ((∀ l, IsRestartIdx l → Nc.ncL S 0 = upsilon l →
        Wf.WfVisGen S l (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Te.teW (Nc.ncL S 0)))) ∧
      Nc.ncL S 1 ≤ nuC) :=
  Wu.wuRoad_vac hG

/-- STATUS: PROVED (by `Ww.wwGap`; NEW round 120; REPLACES the leaf `skGap` of round 119, whose statement `Wu.WuGap`
also asks the segment clause over bases `υ_{λ+h} ≥ Ω₁`, where `Par` is not cited; `Ww.wuGap_ww`: `WuGap ⇒ WwGap`,
and `WwGap` is all that the refutations use)
SIZE: M
`WwGap S k` with the witness `X = ϑ^{u₁}(B₂ + υ_λ)` (`Ww.wwX_spec`, `Ww.wwVt_ne`, `Ww.ww_par_X`) -/
theorem skGapW (k : ℕ) : Ww.WwGap S k := Ww.wwGap k

/-! ## Assembly -/

/-- STATUS: PROVED (a REFUTATION recorded as a node, by `Ww.wwRoad_vac` and the shared leaf `skNu`; NEW round 120.
The old top `skSup` (the supply hypotheses `h0'`, `hn'` of `Wf.wfRoad`) is REFUTED and removed, and with it `skVisK`
and `skGen`, from which it was assembled)
SIZE: S
¬ (h0' ∧ ∀ n, hn' n) -/
theorem skSup_false :
    ¬ ((∀ l, IsRestartIdx l → Nc.ncL S 0 = upsilon l →
        Wf.WfVisGen S l (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Te.teW (Nc.ncL S 0)))) ∧
      (∀ n : ℕ, ∀ l, IsRestartIdx l → Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) = upsilon l →
        Wf.WfVisGen S l (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
          (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Te.teW (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})))))) := by
  rintro ⟨h0, -⟩
  have h1 : Nc.ncL S ((0 + 1 : ℕ) : Ordinal.{0}) ≤ nuC :=
    ((Pp.ppL_lt_omega 0).trans (Qq.qqL_lt_succ S)).le.trans skNu
  exact Ww.wwRoad_vac ⟨h0, by simpa using h1⟩

/-- STATUS: OPEN, OFF THE ROAD since round 124 (it follows from `skSupKXo` by `Xo.xoSup_ww`, node `skSupKW_of_Xo`) (NEW round 120; REPLACES `skSupK` on the road; `skSupK` follows from it by `Ww.wwSup_wf`)
SIZE: L
the REPAIRED supply clause `Ww.WwSup` at `β(ν)`: supply restarts `μ` (`skMu`, `skSupEps`) with a map `(f, B)` whose
carry `Ww.WwCarry` bounds the image of every repaired decomposition, `ϑ`-nodes included (at the gap witness the image
is `ϑ^{υ_{μ+f(1)}}(B₂ + υ_μ)`).  REFUTE FIRST (round 120): NO EVIDENCE (not touched by `Vo.voNoGo`, `Vn.vnTop_Om3`,
`Wf.wfSide_false`; the image of a `ϑ`-node depends only on its level and the image of its countable argument, and
`ϑ^{υ_λ}` is injective on `T ∩ Ω₂` by [W07a] Lemma 3.30).
Round 121: REFUTE FIRST again, NO EVIDENCE.  (a) Since `Xa.xaRep` every reach has repaired decompositions, so the
carry is a statement about every inner reach; two decompositions of one value differ only in (i) the split into
sums (images are additive), (ii) `sg h x` against `th h M e` at the same `x` (the `sg` node asks `Par ⊆ υ_λ` and its
`WfR` asks the parameters below `υ_μ`; then the level data and the leaves of `e` are below `υ_μ` and both images are
the base change of `x`: `mv` = `π` / `up` at `ϑ`, `pi_vt_two`), (iii) the decomposition `e` of the countable
argument (handled recursively).  (b) At the gap witness the image of the form of `Ww.wwForm_X` is
`mv υ_{λ+h} υ_{μ+f h} υ_{λ+h} + ϑ^{υ_{μ+f(1)}}(Ω₁·B₂ + υ_μ)` (`Xa.xaImg_X`), `h = X+ω+1`; with `f(X) = X_μ :=
ϑ^{υ_{μ+1}}(B₂ + υ_μ)` (and `f(X+ω+1) = f(X)+ω+1` by `Sl.SlOff`) the carry there asks `υ_{μ+X_μ+ω+1} + X_μ ≤
r(μ+X_μ)`, which is the equality `Wu.wuR_X` transported to `μ` (proved in Lean only at `L(k)`).  Not touched by
`Vo.voNoGo`, `Vn.vnTop_Om3`, `Wf.wfSide_false` (no old form language, no top law). -/
theorem skSupKW {k : ℕ} {l ν : Ordinal.{0}} (h : SkCtx S k l ν) : Ww.WwSup S l (ν - l + ω ^ 2) := by sorry

/-- STATUS: REDUCED, OFF THE ROAD since round 121 (from `skUp`, `skFormW` (PROVED round 121), `skSupKW`; NEW round 120, REPLACES `skGen`)
SIZE: L
WwGen(λ, β(ν)) -/
theorem skGenW {k : ℕ} {l ν : Ordinal.{0}} (h : SkCtx S k l ν) : Ww.WwGen S l (ν - l + ω ^ 2) :=
  ⟨skUp h, skFormW h, skSupKW h⟩

/-- STATUS: REDUCED, OFF THE ROAD since round 121 (from `skWin`, `skGenW`; NEW round 120, REPLACES `skVisK`)
SIZE: L
∀ k, υ_λ = L(k) ⇒ WwVisGen(λ, L(k+1), υ_{L(k)+W(L(k))}) -/
theorem skVisKW (k : ℕ) : ∀ l, IsRestartIdx l → Nc.ncL S (k : Ordinal.{0}) = upsilon l →
    Ww.WwVisGen S l (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}))
      (upsilon (Nc.ncL S (k : Ordinal.{0}) + Te.teW (Nc.ncL S (k : Ordinal.{0})))) := by
  intro l hl e ν h1 h2 h3 h4 h5 h6
  have hC : SkCtx S k l ν := ⟨hl, e, h1, h2, h3, h4, h5, h6⟩
  exact ⟨_, (skWin hC).1, (skWin hC).2, skGenW hC⟩

/-- STATUS: SUSPECT, OFF THE ROAD since round 121 (`Xb.xbRoad` uses `skShiftTh` / `skRealBX`; reason: `Ww.WwCarry` bounds
the image only of decompositions with `Ww.WwR`, data of every `ϑ`-level below `υ_μ`, but `Ww.WwWF` allows `ϑ`-levels
with a datum in `[υ_λ, υ_{λ+h})`; for such a form the realizer must bound `D(r(λ+g))` and the carry gives nothing.
REFUTE FIRST round 121: NO EVIDENCE against the realizer itself, `skImgGap`) (NEW round 120)
SIZE: L
the realizer bridge `Ww.WwRealB`: `Ww.WwGen` at `(λ, β)` gives `Lr.LrReal (υ_λ) (υ_{λ+β})` (as `Wf.wfReal_gen`; on old
decompositions it IS `Wf.wfReal_gen`, `Ww.wwRealB_of`).  The new part: the realizer map must send a `ϑ`-node value
`ϑ^{υ_{λ+h}}(Ω₁·M + η)` to `ϑ^{υ_{μ+f(h)}}(Ω₁·M + img η)` and keep `≤₁`; this needs [W07a] Def 6.2 / Lemma 6.3 (the
translations) at levels `M ≥ B₂`, cited so far only below `B₂` (`CitedUv`).  REFUTE FIRST: NO EVIDENCE. -/
theorem skRealB (S : InaccSeq.{0}) : Ww.WwRealB S := by sorry

/-- STATUS: PROVED (by `Xb.xb_img_gap_k`; NEW round 121; REFUTE-FIRST test of the bridge at the gap witness)
SIZE: S
at `L(k)`: the `ϑ`-node `th 1 B₂ (lo λ)` has the value `Ww.wwX S k`; for every `υ_μ < υ_λ`, `0 < μ`, and `f(1) = 1`
its image is `ϑ^{υ_{μ+1}}(B₂ + υ_μ)`, an `ε`-number of `T^{υ_{μ+1}}` in `(υ_{μ+1}, υ_{μ+2})` with the parameter
`υ_μ`. -/
theorem skImgGap (k : ℕ) {μ : Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} (hμ : 0 < μ)
    (hμl : upsilon μ < upsilon (Nc.ncL S (k : Ordinal.{0}))) (hf : f 1 = 1) :
    Ww.wwVal (Nc.ncL S (k : Ordinal.{0})) (.th 1 Uc.ucB (.old (.lo (Nc.ncL S (k : Ordinal.{0}))))) = Ww.wwX S k ∧
    Ww.wwImg (Nc.ncL S (k : Ordinal.{0})) μ f (.th 1 Uc.ucB (.old (.lo (Nc.ncL S (k : Ordinal.{0}))))) =
      Xb.xbIX μ ∧
    Xb.xbIX μ ∈ Tset (upsilon (μ + 1)) ∧ InE (Xb.xbIX μ) ∧ upsilon (μ + 1) < Xb.xbIX μ ∧
    Xb.xbIX μ < upsilon (μ + 2) ∧ upsilon μ ∈ Par (upsilon (μ + 1)) (Xb.xbIX μ) :=
  Xb.xb_img_gap_k k hμ hμl hf

/-- STATUS: PROVED (by `Xe.xe_pi_fix_th`, `Xe.xe_Om1_mul_TB`, `Xe.xeVt_tr`; NEW round 122; the node lemmas of
`R2.UyFix` at every constant level `Ω₁·M < θ`)
SIZE: M
for bases `σ < τ`, a strongly critical `q ≤ σ`: every `z < θ` with `d_S(z) < q` is in `Tᵗ[σ]` and `π z = z`; for a
level `M` over `κ < τ` (`Xe.XeLev`): both translations of [W07a] Def 6.2 (subcase `Γ^* < α`). -/
theorem skNodeTh (S : InaccSeq.{0}) :
    (∀ σ τ q z, Bases σ τ → SC q → q ≤ σ → z < ConjT.th S → Vd.vdD S 0 z < q → Xe.XeFx σ τ z) ∧
    (∀ κ τ (n : ℕ) M ρ, Bases κ τ → 1 ≤ n → Xe.XeLev κ M → ρ < Om1 →
      (Om1 * M + ρ ∈ Tset (Dl τ n) → vt (Dl τ n) (Om1 * M + ρ) < Dp τ n →
        Om1 * M + (Dl τ n + ρ) ∈ Tset τ ∧ vt (Dl τ n) (Om1 * M + ρ) = vt τ (Om1 * M + (Dl τ n + ρ)))) :=
  ⟨fun _ _ _ _ h hq hqσ hz hd => Xe.xe_pi_fix_th (S := S) h hq hqσ hz hd,
    fun _ _ _ _ _ hB hn hM hρ => (Xe.xeVt_tr hB hn hM hρ).1⟩

/-- STATUS: PROVED (by `Xj.xeShift_holds`; round 123: FRAG with a top `ϑ`-node of a constant level, `Xj.xjFragV`, in
the shift `Xj.xjShiftCore`; was OPEN, NEW round 122; the part of `skShiftTh` left by `Xe.xbShift_of_xe`)
SIZE: L
`Xe.XeShift S`: the shift `Vl.vlShiftCore` with the `ϑ`-node clause `Xe.XeThHi` for a point `η ∈ Y` and a level `M ≥
B₂` (data below the bottom `γ`): `D(ϑ^{υ_{λ+h}}(Ω₁·M + η)) = ϑ^{υ_{μ+f(h)}}(Ω₁·M + D(η))`.  Needs FRAG
(`Vl.vlFrag`) on a term type with a node of constant level `Ω₁·M ∈ [B₂, θ)` (`Un.UnC` has only `thc` with `Ω₁·q <
B₂`, `Vi.Nz.qB`); its node cases are the theorems `Xe.xeDown` (`viDown`), `Xe.xeMv` (`viMv`), `Xe.xeVt_tr`
(`viTrA` / `viTrB`), `Xe.xeLt_vt_self`, `Xe.xe_arg_T`, with order from `R2.vdVt_lt`, `R2.vdLt_of_vt_lt`.
REFUTE FIRST round 122: NO EVIDENCE (at the gap witness the clause asks `D(X*) = ϑ^{υ_{μ+1}}(B₂ + υ_μ)`, the point of
`skImgGap`; not touched by `Vo.voNoGo`, `Vn.vnTop_Om3`, `Wf.wfSide_false`, `Ww.wwRoad_false`). -/
theorem skShiftThHi (S : InaccSeq.{0}) : Xe.XeShift S := Xj.xeShift_holds

/-- STATUS: PROVED (from `skShiftThHi` by `Xe.xbShift_of_xe`; round 123; = `Xj.xbShift_holds`; was REDUCED round 122,
OPEN round 121)
SIZE: L
`Xb.XbShift S`: the shift `Vl.vlShiftCore` with the `ϑ`-node clause `Xb.XbThCl`: for `y ∈ Y` in the segment of
`υ_{λ+h}`, `y = ϑ^{υ_{λ+h}}(Ω₁·M + η)` with `1 ≤ M`, the data of `M` below the bottom `γ` (`Vd.VdLtIn M γ`), `η < Ω₁`
in `X ∪ Y`: `D(y) = ϑ^{υ_{μ+f(h)}}(Ω₁·M + D(η))`.  The cases `η ∈ X` (`Xe.xe_thCl_low`) and `Ω₁·M < B₂`
(`Xe.xe_thCl_lowLev`) are theorems. -/
theorem skShiftTh (S : InaccSeq.{0}) : Xb.XbShift S := Xe.xbShift_of_xe (skShiftThHi S)

/-- STATUS: PROVED (from `skShiftTh` by `Xb.xbRealB`; round 123; NEW round 121, REPLACES `skRealB` on the road)
SIZE: L
the bridge for forms with constant `ϑ`-levels, `Xb.XbRealB S` -/
theorem skRealBX (S : InaccSeq.{0}) : Xb.XbRealB S := Xb.xbRealB (skShiftTh S)

/-- STATUS: PROVED (by `Xj.xjFragXe`; NEW round 123)
SIZE: L
FRAG with the hull isomorphism on `thz`-terms (`Vl.VlFragConcl`) and the clause at a top `ϑ`-node of every constant
level `Ω₁·q < θ` (`Xj.XjCl Xe.XeLev`). -/
theorem skFragTh {m : ℕ} {κ : Ordinal.{0}} {b c : ℕ → Ordinal.{0}} (hb : Chain κ b m) (hc : Chain κ c m)
    (F : Finset Ordinal.{0}) (hF : ↑F ⊆ DD κ b m) : ∃ Ψ, Xj.XjFragConcl Xe.XeLev κ b c m F Ψ :=
  Xj.xjFragXe hb hc F hF

/-- STATUS: REFUTED (round 123, by `Xj.xjFormHighX_fail` and the shared node `skNu`; node `skFormHighX_false`)
(NEW round 121; `skFormHighW` with constant `ϑ`-levels; REPLACES it on the road)
SIZE: L
the forms clause at the windows with `ν − λ ≥ ε_{u₁+1}` with forms `Xb.XbForm` (every `ϑ`-level `M` with `1 ≤ M` and
its data below some `c < υ_λ`).  REFUTE FIRST round 121: NO EVIDENCE; at the gap witness the form exists with `M = B₂`,
data below `Γ₀` (`Xb.xbForm_X`, `Xb.xbForm_gap`).  Round 123: REFUTED at the witness `Xj.xjX` (level `B₂ + λ` with
the leaf `λ`).  Old expected proof: as `skFormHighW`, with the induction on the point
of `T^{υ_{λ+h}}` writing `ϑ^{υ_{λ+h}}(Ω₁·M + η)` with `M`'s data below `υ_λ` as a `ϑ`-node and every other point as a
`sg`-node or a sum (a level with a datum in `[υ_λ, υ_{λ+h})` must be unfolded further).
¬(ν − λ < ε_{u₁+1}) ⇒ ∀ z < β(ν), ω² | z ⇒ υ_{λ+β} ≤ r(λ+z) ∨ XbForm(λ, β, z) -/
theorem skFormHighX {k : ℕ} {l ν : Ordinal.{0}} (h : SkCtx S k l ν) (hE : ¬ ν - l < eN (upsilon (l + 1))) :
    ∀ g, 0 < g → g < ν - l + ω ^ 2 → ω ^ 2 ∣ g →
      upsilon (l + (ν - l + ω ^ 2)) ≤ cdR S (l + g) ∨ Xb.XbForm S l (ν - l + ω ^ 2) g := by sorry

/-- STATUS: PROVED (a REFUTATION recorded as a node, by `Xj.xjFormHighX_fail`, `Wu.wuWin`, `skWitEps` and the shared
node `skNu`; NEW round 123: `skFormHighX` is REFUTED)
SIZE: M
at every `L(k)` the forms clause with constant `ϑ`-levels fails at a high window: ¬ skFormHighX -/
theorem skFormHighX_false (k : ℕ) : ¬ (∀ l ν, SkCtx S k l ν →
    ¬ ν - l < eN (upsilon (l + 1)) → ∀ g, 0 < g → g < ν - l + ω ^ 2 → ω ^ 2 ∣ g →
      upsilon (l + (ν - l + ω ^ 2)) ≤ cdR S (l + g) ∨ Xb.XbForm S l (ν - l + ω ^ 2) g) := by
  intro H
  have hν : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC :=
    ((Pp.ppL_lt_omega k).trans (Qq.qqL_lt_succ S)).le.trans skNu
  obtain ⟨X, hXE, hX1, hX2, heN, -, hfail⟩ := Xj.xjFormHighX_fail k hν
  set l := Nc.ncL S (k : Ordinal.{0}) with hldef
  have hC : SkCtx S k l (l + X + ω ^ 2) := Wu.wuWin k hν hXE hX1 hX2
  have e : l + X + ω ^ 2 - l = X + ω ^ 2 := by rw [add_assoc, Ordinal.add_sub_cancel]
  have hE : ¬ l + X + ω ^ 2 - l < eN (upsilon (l + 1)) := by rw [e]; exact not_lt.2 (heN.trans le_self_add)
  have hωX : ω ≤ X := Vo.vo_omega_le hXE (InE.pos hXE)
  have hω2g : ω ^ 2 ∣ X := by
    have h := Vo.vo_e2 ▸ opow_dvd_opow ω ((natCast_lt_omega0 2).trans_le hωX).le
    rwa [hXE] at h
  have hXβ : X < l + X + ω ^ 2 - l + ω ^ 2 := by
    rw [e]
    exact (lt_add_of_pos_right X (pow_pos omega0_pos 2)).trans_le le_self_add
  exact hfail (H l (l + X + ω ^ 2) hC hE X (InE.pos hXE) hXβ hω2g)

/-- STATUS: REDUCED (from `skFormEps` with `Xb.xbForm_of_vr`, and `skFormHighX`; NEW round 121)
SIZE: L
∀ z < β(ν), ω² | z ⇒ υ_{λ+β} ≤ r(λ+z) ∨ XbForm(λ, β, z) -/
theorem skFormX {k : ℕ} {l ν : Ordinal.{0}} (h : SkCtx S k l ν) :
    ∀ g, 0 < g → g < ν - l + ω ^ 2 → ω ^ 2 ∣ g →
      upsilon (l + (ν - l + ω ^ 2)) ≤ cdR S (l + g) ∨ Xb.XbForm S l (ν - l + ω ^ 2) g := by
  have hl : 0 < upsilon l := InE.pos (upsPt_inE (upsPt_upsilon (pos_iff_ne_zero.2 h.1.1)))
  intro g hg0 hgβ hgd
  by_cases hE : ν - l < eN (upsilon (l + 1))
  · exact (skFormEps h hE g hg0 hgβ hgd).imp_right (Xb.xbForm_of_vr hl)
  · exact skFormHighX h hE g hg0 hgβ hgd

/-- STATUS: REDUCED (from `skUp`, `skFormX`, `skSupKW`; NEW round 121)
SIZE: L
XbGen(λ, β(ν)) -/
theorem skGenX {k : ℕ} {l ν : Ordinal.{0}} (h : SkCtx S k l ν) : Xb.XbGen S l (ν - l + ω ^ 2) :=
  ⟨skUp h, skFormX h, skSupKW h⟩

/-- STATUS: REDUCED (from `skWin`, `skGenX`; NEW round 121)
SIZE: L
∀ k, υ_λ = L(k) ⇒ XbVisGen(λ, L(k+1), υ_{L(k)+W(L(k))}) -/
theorem skVisKX (k : ℕ) : ∀ l, IsRestartIdx l → Nc.ncL S (k : Ordinal.{0}) = upsilon l →
    Xb.XbVisGen S l (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}))
      (upsilon (Nc.ncL S (k : Ordinal.{0}) + Te.teW (Nc.ncL S (k : Ordinal.{0})))) := by
  intro l hl e ν h1 h2 h3 h4 h5 h6
  have hC : SkCtx S k l ν := ⟨hl, e, h1, h2, h3, h4, h5, h6⟩
  exact ⟨_, (skWin hC).1, (skWin hC).2, skGenX hC⟩

/-- STATUS: REDUCED (from `skVisKX`); REFUTED as a whole (round 123: `skSupX_false`; it rests on the REFUTED leaf
`skFormHighX`); REPLACED on the road by `skSupXo` (round 124), OFF THE ROAD
SIZE: L
NEW TOP (round 121; the supply hypotheses of `Xb.xbRoad`): `Xb.XbVisGen` at `m*` and every `L(n+1)`; with
`skShiftTh` they feed `Xb.xbRoad`.  `Root.skNuC` must apply `Xb.xbRoad` (arguments: the four frontier tops, `hE.1`,
`hE.2`, `SkS.skShiftTh S`, `skSupX.1`, `skSupX.2`) in place of `Ww.wwRoad`. -/
theorem skSupX :
    (∀ l, IsRestartIdx l → Nc.ncL S 0 = upsilon l →
      Xb.XbVisGen S l (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Te.teW (Nc.ncL S 0)))) ∧
    (∀ n : ℕ, ∀ l, IsRestartIdx l → Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) = upsilon l →
      Xb.XbVisGen S l (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
        (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Te.teW (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))) := by
  refine ⟨fun l hl e => ?_, fun n l hl e => skVisKX (n + 1) l hl e⟩
  have h := skVisKX (S := S) 0 l hl (by simpa using e)
  simpa using h

/-- STATUS: PROVED (a REFUTATION recorded as a node, by `Xj.xjRoad_vac` and the shared node `skNu`; NEW round 123.
The top `skSupX` (the supply hypotheses `h0`, `hn` of `Xb.xbRoad`) is REFUTED; so the road `Xb.xbRoad` used by
`Root.skNuC` is VACUOUS (`Xj.xbRoad_false`), and so is `Xj.xjRoad` (`Xj.xjRoad_false`))
SIZE: S
¬ (h0 ∧ ∀ n, hn n) of `Xb.xbRoad` -/
theorem skSupX_false :
    ¬ ((∀ l, IsRestartIdx l → Nc.ncL S 0 = upsilon l →
        Xb.XbVisGen S l (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Te.teW (Nc.ncL S 0)))) ∧
      (∀ n : ℕ, ∀ l, IsRestartIdx l → Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) = upsilon l →
        Xb.XbVisGen S l (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
          (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Te.teW (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})))))) := by
  rintro ⟨h0, -⟩
  have h1 : Nc.ncL S ((0 + 1 : ℕ) : Ordinal.{0}) ≤ nuC :=
    ((Pp.ppL_lt_omega 0).trans (Qq.qqL_lt_succ S)).le.trans skNu
  exact Xj.xjRoad_vac ⟨h0, by simpa using h1⟩

/-- STATUS: REDUCED (round 121: from `skSupX` by `Xb.xbVisGen_ww`; round 120: from `skVisKW`)
SIZE: L
THE ROUND-120 TOP, kept with its exact statement (round 121: no longer the top; `Xb.xbRoad` uses `skSupX`):
h0'' ∧ ∀ n, hn'' n, the supply hypotheses of `Ww.wwRoad` (`Ww.WwVisGen`). -/
theorem skSupW :
    (∀ l, IsRestartIdx l → Nc.ncL S 0 = upsilon l →
      Ww.WwVisGen S l (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Te.teW (Nc.ncL S 0)))) ∧
    (∀ n : ℕ, ∀ l, IsRestartIdx l → Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) = upsilon l →
      Ww.WwVisGen S l (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
        (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Te.teW (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))) := by
  exact ⟨fun l hl e => Xb.xbVisGen_ww (skSupX.1 l hl e), fun n l hl e => Xb.xbVisGen_ww (skSupX.2 n l hl e)⟩


/-! ## Round 124: the supply with moving-leaf levels (`Xo`) -/

/-- STATUS: PROVED (by `Xo.xoForms_all`, `skWin`, `Vr.vr_facts`; NEW round 124)
SIZE: S
∀ z < β(ν), ω² | z ⇒ υ_{λ+β} ≤ r(λ+z) ∨ XoForm(λ, β, z) -/
theorem skFormXo {k : ℕ} {l ν : Ordinal.{0}} (h : SkCtx S k l ν) :
    ∀ g, 0 < g → g < ν - l + ω ^ 2 → ω ^ 2 ∣ g →
      upsilon (l + (ν - l + ω ^ 2)) ≤ cdR S (l + g) ∨ Xo.XoForm S l (ν - l + ω ^ 2) g := by
  intro g _ _ _
  obtain ⟨-, -, -, -, -, -, hL1O, -, -⟩ := Vr.vr_facts (S := S) k
  exact Xo.xoForms_all S (pos_iff_ne_zero.2 h.1.1) ((skWin h).2.trans hL1O.le) g

/-- STATUS: OPEN (NEW round 124; RESTATED round 125: `Xo.XoCarry` reads the repaired `Xo.XoR`; REPLACES `skSupKW` on
the road; `skSupKW` follows from it by `Xo.xoSup_ww`)
SIZE: L
the supply clause with the moving-leaf carry `Xo.XoCarry` at `β(ν)`: supply restarts `μ` with a map `(f, B)` whose
carry bounds the image (`Xo.xoImg`, the leaf substitution) of every restricted moving-leaf decomposition.
REFUTE FIRST (round 125, repaired `Xo.XoR`): NO EVIDENCE; the audit's `F_k` and the absorbed `F′_k` are excluded
(`Xo.xoE2_notR`, `Xo.xoE3_notR`, nodes `skXoFixed`, `skXoFkEx`, `skXoAbsEx`); the syntactic repair is REFUTED (node
`skXoNaiveRef`); the offset obligation at `X′` is consistent (node `skXoOffWit`).
REFUTE FIRST (round 124, old `XoR`, REPLACED): NO EVIDENCE claimed there, BLOCKING in the audit.  At the witness `X′ = Xj.xjX` the decomposition `Xo.xoXjE` is well formed and
restricted at every `μ` (`Xo.xoXj_WF`, `Xo.xoXj_R`), its image is `υ_{μ+f(h₁)} + X′_μ` (`Xo.xoXj_img`), and the carry
asks exactly `X′_μ ≤ f(X′)` (`Xo.xoXj_obl`, under the reach formula at `μ`, the twin of `Wu.wuR_X`): an offset map
sending `X′` to its twin `X′_μ` satisfies it with equality.  The next candidates (leaf `u₁`, nested node `X′`) move to
their twins (`Xo.xoNext_img`).  The image is a function of the value on one-segment levels (`Xo.xoImg_pi`: it is the
base change `π`), so different terms of one level give one image there.  Not touched by `Vo.voNoGo`, `Vn.vnTop_Om3`,
`Wf.wfSide_false`, `Xj.xjVis_ref` (no old form language, no top law; the forms clause always holds,
`Xo.xoForms_all`).  Left: the reach formula `r(μ + f(g)) = υ_{μ+(f(g)+ω+1)} + f(g)` at the supply restarts (proved in
Lean only at `L(k)`, `Wu.wuR_X`), and EQ under `η_λ ↦ η_μ` above `υ_{λ+2}`.
REFUTE FIRST (round 126): NO EVIDENCE.  The carry is not silent where it matters: with the covering lemma every small
reach has a restricted decomposition on a tail, and any `XoSup` configuration can be chosen to bound its image
(`Yb.ybSup_bound`, nodes `skCoverXo`, `skSupNonSilent`); so `XoSup` really constrains `r(μ + f g)` at every small
reach (it is not trivially satisfiable), and still no decomposition with two different images of one value was found
(the image is the leaf substitution; leaves move order-preservingly inside their segments, absorption is structural).
Exact gap: the reach formula `r(μ + f(g))` at the supply restarts for every `g` of the window (Lean has it only at
`L(k)`, `Wu.wuR_X`), the supply `υ_{μ+B} ≤ r(μ)` with `B` above every `f(g)`, and EQ under `η_λ ↦ η_μ` above
`υ_{λ+2}`.
XoSup(λ, β(ν)) -/
theorem skSupKXo {k : ℕ} {l ν : Ordinal.{0}} (h : SkCtx S k l ν) : Xo.XoSup S l (ν - l + ω ^ 2) := by sorry

/-- STATUS: REDUCED (from `skUp`, `skFormXo` (PROVED), `skSupKXo`; NEW round 124)
SIZE: S
XoGen(λ, β(ν)) -/
theorem skGenXo {k : ℕ} {l ν : Ordinal.{0}} (h : SkCtx S k l ν) : Xo.XoGen S l (ν - l + ω ^ 2) :=
  ⟨skUp h, skFormXo h, skSupKXo h⟩

/-- STATUS: REDUCED (from `skWin`, `skGenXo`; NEW round 124)
SIZE: S
∀ k, υ_λ = L(k) ⇒ XoVisGen(λ, L(k+1), υ_{L(k)+W(L(k))}) -/
theorem skVisKXo (k : ℕ) : ∀ l, IsRestartIdx l → Nc.ncL S (k : Ordinal.{0}) = upsilon l →
    Xo.XoVisGen S l (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}))
      (upsilon (Nc.ncL S (k : Ordinal.{0}) + Te.teW (Nc.ncL S (k : Ordinal.{0})))) := by
  intro l hl e ν h1 h2 h3 h4 h5 h6
  have hC : SkCtx S k l ν := ⟨hl, e, h1, h2, h3, h4, h5, h6⟩
  exact ⟨_, (skWin hC).1, (skWin hC).2, skGenXo hC⟩

/-- STATUS: REDUCED (from `skVisKXo`; NEW round 124)
SIZE: L
NEW TOP (round 124; the supply hypotheses of `Xo.xoRoadH`): `Xo.XoVisGen` at `m*` and every `L(n+1)`; with
`skRealBXo` they feed `Xo.xoRoadH`.  `Root.skNuC` must apply `Xo.xoRoadH (SkF.skFrontU S) (SkF.skFrontL S)
(SkF.skFrontV S) (SkF.skFrontVt S) hE.1 hE.2 (SkS.skRealBXo S) skSupXo.1 skSupXo.2` in place of `Xb.xbRoad`.
NON-VACUITY: the refutation of the four earlier supply tops (`Xj.xjVis_ref` and its predecessors) goes through the
forms clause, which now always holds (`Xo.xoForms_all`, `Xo.xoVis_gap`). -/
theorem skSupXo :
    (∀ l, IsRestartIdx l → Nc.ncL S 0 = upsilon l →
      Xo.XoVisGen S l (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Te.teW (Nc.ncL S 0)))) ∧
    (∀ n : ℕ, ∀ l, IsRestartIdx l → Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) = upsilon l →
      Xo.XoVisGen S l (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
        (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Te.teW (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))) := by
  refine ⟨fun l hl e => ?_, fun n l hl e => skVisKXo (n + 1) l hl e⟩
  have h := skVisKXo (S := S) 0 l hl (by simpa using e)
  simpa using h

/-- STATUS: OPEN (NEW round 129; REPLACES `skRealBXo` on the road)
SIZE: L
the shift with the `ϑ`-node clause `Yq.XoShift2 S`: `Xb.XbShift` (PROVED: `Xj.xbShift_holds`) with `Yq.XoThCl` in
place of `Xb.XbThCl`, for one realizer map `D`.  `XoThCl`: `D(ϑ^{υ_{λ+h}}(Ω₁·L + e)) = ϑ^{υ_{μ+f h}}(Ω₁·L′ + e′)` for a
level TERM `L` with moving leaves (`L′`, `e′` the leaf substitutions `Xo.xoImg`), at restricted well-formed nodes
whose points lie in the configuration; at a constant level it is the clause `Xb.XbThCl` of `Xb.XbShift`.
REFUTE FIRST (round 129): NO EVIDENCE; the clause asks the image to be a function of the value on restricted
decompositions, which no test has broken (`Wu.wuImg_test`, `Vr.vrImg_agree`, `Xo.xoImg_pi`); no no-go result
(`Vo.voNoGo`, `Vn.vnTop_Om3`, `Wf.wfSide_false`, `Xj.xjVis_ref`) speaks of the shift.
Needed: FRAG (`Xj.xjFragV`) with nodes whose levels are terms with moving leaves (the two subcases `R2.xeVt_trL`,
`R2.xoVt_trH`, through `Xo.xoVt_up` / `xoVt_down`); on one segment the leaf substitution of a level is `π`
(`Xo.xoImg_pi`).
Round 130: the level sort below `θ` is built (`Yv.yvSub`; nodes `skYvPi`, `skYvComp`, `skYvUp`, `skYvNode`, `skYvDat`,
`skYvTr`, PROVED); REFUTE FIRST at the one-moving-leaf node `ϑ^{b}(Ω₁·(B₂ + b) + r)`: NO EVIDENCE, every FRAG step
agrees with the leaf substitution there (`skYvWit`).  Next: `skYvCl` (FRAG with the moving-level clause), then
`Xo.xoImg` of a restricted level term `= yvSub D` of its value. -/
theorem skShift2 (S : InaccSeq.{0}) : Yq.XoShift2 S := by sorry

/-- STATUS: REDUCED (from `skShift2` by `Yq.yqShift_of2`; NEW round 129)
SIZE: M
the shift with the moving-leaf clause `Yq.XoShift S` (`D(value) = image` on restricted decompositions) -/
theorem skShiftXo (S : InaccSeq.{0}) : Yq.XoShift S := Yq.yqShift_of2 (skShift2 S)

/-- STATUS: REDUCED (from `skShiftXo` by `Yq.yqRealBL`; NEW round 129; ON THE ROAD through `Yq.yqRoadS`)
SIZE: L
the bridge on the windows `υ_{λ+β} ≤ L(ω+1)` (`Yq.XoRealBL`, all the road uses) -/
theorem skRealBXoL (S : InaccSeq.{0}) : Yq.XoRealBL S := Yq.yqRealBL (skShiftXo S)

/-- STATUS: OPEN (NEW round 129; OFF THE ROAD: the part of `skYbIFTh` left)
SIZE: L
`Yq.YqIFHuge`: `YgIFTh` at the levels `B₂ ≤ M < θ` whose `K⁽⁰⁾`-datum is above every value of `ψ_{Ω₁}` (above the
countable part of the notation).  Equivalent to `skYbIFTh` (`Yq.yqHuge_iff`).  REFUTE FIRST: NO EVIDENCE.
Needed: the code test `Ui.ui_code_th` relative to a countable base (normal forms with countable constants), or the
port of `Yg.ygUcK` to `[B₂, θ)` through `Vd.vd_nf_ex` with an induction on own arguments. -/
theorem skYbIFHuge (S : InaccSeq.{0}) : Yq.YqIFHuge S := by sorry

/-- STATUS: PROVED (by `Yq.yqIFN`; NEW round 129)
SIZE: M
`YbIF` at every threshold `q ≤ ψ_{Ω₁}(A)` -/
theorem skYbIFNot (S : InaccSeq.{0}) (A : Ordinal.{0}) : Yq.YqIFN S A := Yq.yqIFN A

/-- STATUS: PROVED (by `Yq.yqLevK`; NEW round 129)
SIZE: S
the level statement of the covering lemma on every window `υ_{λ+β} ≤ ψ_{Ω₁}(A)` -/
theorem skLevKNot {l β A : Ordinal.{0}} (hl0 : 0 < l) (hb1 : upsilon (l + β) ≤ Om1)
    (hA : upsilon (l + β) ≤ S.psi A (Om 1)) : Yb.YbLevK S l β :=
  Yq.yqLevK hl0 hb1 hA

/-- STATUS: PROVED (by `Yq.yqCover_L`; NEW round 129)
SIZE: S
THE COVERING LEMMA on every window `υ_{λ+β} ≤ L(ω+1)`, with no hypothesis -/
theorem skCoverXoL {l β : Ordinal.{0}} (hl0 : 0 < l) (hb1 : upsilon (l + β) ≤ Om1)
    (hL : upsilon (l + β) ≤ Nc.ncL S (ω + 1)) :
    ∀ x, x < upsilon (l + β) → x < Om1 → Yb.YbCov S l β x :=
  Yq.yqCover_L hl0 hb1 hL

/-- STATUS: PROVED (by `Yq.yqSupBound_L`; NEW round 129)
SIZE: S
THE NON-SILENT SUPPLY on every window `υ_{λ+β} ≤ L(ω+1)`: from `Xo.XoSup S λ β` alone -/
theorem skSupNonSilentL {l β : Ordinal.{0}} (hl0 : 0 < l) (hb1 : upsilon (l + β) ≤ Om1) (hl1 : upsilon l < Om1)
    (hL : upsilon (l + β) ≤ Nc.ncL S (ω + 1)) (hS : Xo.XoSup S l β) :
    ∀ γ < upsilon l, ∀ G : Finset Ordinal.{0}, (∀ d ∈ G, d < β) →
      ∃ μ f B, ∃ Os : Finset Ordinal.{0}, G ⊆ Os ∧ CdRange S μ ∧ γ < upsilon μ ∧ upsilon μ < upsilon l ∧
        μ + B ≤ l ∧ ω ^ 2 ∣ B ∧ upsilon (μ + B) ≤ cdR S μ ∧ Sl.SlOff f Os B ∧ Xo.XoCarry S l β μ f B Os ∧
        ∀ g ∈ G, 0 < g → ω ^ 2 ∣ g → cdR S (l + g) < upsilon (l + β) →
          ∃ E : Xo.XoE, Xo.XoWF S l β E ∧ Xo.xoVal S l E = cdR S (l + g) ∧ Xo.XoR S l μ E ∧
            Xo.xoImg S l μ f E ≤ cdR S (μ + f g) :=
  Yq.yqSupBound_L hl0 hb1 hl1 hL hS

/-- STATUS: REDUCED (round 129: from `skShiftXo` and `skYbIFHuge` by `Yq.yqRealB_huge`; OFF THE ROAD since round 129:
the road `Yq.yqRoadS` asks the bridge only on the windows `υ_{λ+β} ≤ L(ω+1)`, node `skRealBXoL`) (NEW round 124;
REPLACES `skShiftTh` / `skRealBX` on the road)
SIZE: L
the realizer bridge for moving-leaf levels `Xo.XoRealB`: `Xo.XoGen` at `(λ, β)` gives `Lr.LrReal (υ_λ) (υ_{λ+β})`.
Needed: FRAG (`Xj.xjFragV`) with a `ϑ`-node whose level is a term with moving leaves, the node lemmas at such levels
(`Xo.xoVt_up` / `Xo.xoVt_down`: both subcases of [W07a] Def 6.2, now cited on `[B₂, θ)`), the hull clause
`Ψ(ϑ^{b_k}(Ω₁·L[b_k] + r)) = ϑ^{c_k}(Ω₁·L[Ψ] + vmap Ψ r)` and the carry.  It holds where the forms are constant-level
forms (`Xo.xoReal_of_xb`, from `Xj.xbRealB_holds`).  REFUTE FIRST: NO EVIDENCE (the moving-leaf image of the witness
is a valid point of the target segment, `Xo.xoXj_img`, `Xb.xbIX_spec`; on one segment the image is `π`, `Xo.xoImg_pi`).
REFUTE FIRST (round 126): the risk "image argument outside `T^{υ_{μ+f h}}`": NO EVIDENCE (see the round-126 note in
the header); the audit's worry that the carry is silent at reaches with no restricted decomposition is answered by
the covering lemma (`skCoverXo`, `skSupNonSilent`) up to `skYbIF`.  Exact gap: the FRAG step with a `ϑ`-node whose
level is a term with moving leaves (`Ψ(ϑ^{b_k}(Ω₁·L[b_k] + r)) = ϑ^{c_k}(Ω₁·L[Ψ] + vmap Ψ r)`), the proof that the
image argument lies in `T^{υ_{μ+f h}}` (data of `L[Ψ]` below `υ_{μ+f h+1}`), and the use of `skSupNonSilent` to
place the image below the target reach. -/
theorem skRealBXo (S : InaccSeq.{0}) : Xo.XoRealB S := Yq.yqRealB_huge (skShiftXo S) (skYbIFHuge S)

/-- STATUS: PROVED (by `Xo.xoReal_of_xb`; NEW round 124)
SIZE: S
the bridge where every form is a constant-level form -/
theorem skRealBXoOld {l β : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : upsilon l < Om1) (hν : upsilon l < nuC)
    (hνβ : upsilon (l + β) ≤ nuC) (hstd : Cx.CxStdPairTop S) (hlL : upsilon l ≤ Nc.ncL S (ω + 1))
    (h : Xo.XoGen S l β)
    (hold : ∀ g, 0 < g → g < β → ω ^ 2 ∣ g → upsilon (l + β) ≤ cdR S (l + g) ∨ Xb.XbForm S l β g) :
    Lr.LrReal S (upsilon l) (upsilon (l + β)) :=
  Xo.xoReal_of_xb hl hl1 hν hνβ hstd hlL h hold

/-- STATUS: PROVED (by `Xo.xoCarry_xj`; NEW round 124; REFUTE-FIRST test of the moving-leaf carry at the witness)
SIZE: M
the carry at `X′` asks `υ_{μ+f(h₁)} + X′_μ ≤ r(μ+f(X′))` -/
theorem skXoCarryWit (k : ℕ) (hν : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC) {β μ B : Ordinal.{0}}
    {f : Ordinal.{0} → Ordinal.{0}} {Os : Finset Ordinal.{0}}
    (hC : Xo.XoCarry S (Nc.ncL S (k : Ordinal.{0})) β μ f B Os) (hX : Xj.xjX S k ∈ Os)
    (h1 : Xj.xjX S k + ω + 1 ∈ Os) (hone : (1 : Ordinal.{0}) ∈ Os)
    (hβ : Xj.xjX S k + ω + 1 < β) (hb1 : upsilon (Nc.ncL S (k : Ordinal.{0}) + β) ≤ Om1)
    (hμ0 : 0 < μ) (hμl : upsilon μ < upsilon (Nc.ncL S (k : Ordinal.{0})))
    (hτ'O : upsilon (μ + f (Xj.xjX S k + ω + 1)) < Om1) :
    upsilon (μ + f (Xj.xjX S k + ω + 1)) + Xo.xoXjMu μ f ≤ cdR S (μ + f (Xj.xjX S k)) :=
  Xo.xoCarry_xj k hν hC hX h1 hone hβ hb1 hμ0 hμl hτ'O

/-- STATUS: PROVED (by `Xo.xoXj_obl`; NEW round 124)
SIZE: S
under the reach formula at `μ`, the carry at `X′` ⇔ `X′_μ ≤ f(X′)` -/
theorem skXoObl (k : ℕ) {μ B : Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} {Os : Finset Ordinal.{0}}
    (hO : Sl.SlOff f Os B)
    (hr : cdR S (μ + f (Xj.xjX S k)) = upsilon (μ + (f (Xj.xjX S k) + ω + 1)) + f (Xj.xjX S k)) :
    upsilon (μ + f (Xj.xjX S k + ω + 1)) + Xo.xoXjMu μ f ≤ cdR S (μ + f (Xj.xjX S k)) ↔
      Xo.xoXjMu μ f ≤ f (Xj.xjX S k) :=
  Xo.xoXj_obl k hO hr

/-- STATUS: PROVED (by `Xo.xoRewrite`; NEW round 124; the covering argument)
SIZE: M
every `Ww.WwE` decomposition whose levels have data below `υ_{λ+β}` is a moving-leaf decomposition with term levels -/
theorem skXoCover {l β : Ordinal.{0}} (hl0 : 0 < l) (hb1 : upsilon (l + β) ≤ Om1) :
    ∀ E : Ww.WwE, Ww.WwWF l β E → Xo.XoLevLt S (upsilon (l + β)) E →
      ∃ E' : Xo.XoE, Xo.XoWF S l β E' ∧ Xo.xoVal S l E' = Ww.wwVal l E :=
  Xo.xoRewrite S hl0 hb1

/-- STATUS: PROVED (by `Xo.xoXj_lev_pi`; NEW round 124)
SIZE: S
the leaf substitution at the witness level is the base change: `π(B₂ + λ) = B₂ + υ_μ` -/
theorem skXoLevPi (k : ℕ) {μ : Ordinal.{0}} (f : Ordinal.{0} → Ordinal.{0}) (hμ0 : 0 < μ)
    (hμl : upsilon μ < upsilon (Nc.ncL S (k : Ordinal.{0}))) :
    pi (upsilon μ) (upsilon (Nc.ncL S (k : Ordinal.{0}))) (Uc.ucB + Nc.ncL S (k : Ordinal.{0})) =
      Uc.ucB + upsilon μ :=
  Xo.xoXj_lev_pi k f hμ0 hμl

/-- STATUS: PROVED (by `Xo.xoVt_up`, from the NEW cited axiom `R2.xoVt_trH` and `R2.xeVt_trL`; NEW round 124)
SIZE: M
`t^α_τ` at every level `B₂ ≤ M < θ` in either subcase of [W07a] Def 6.2 -/
theorem skXoTrUp {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) {n : ℕ} (hn : 1 ≤ n) {M ρ : Ordinal.{0}}
    (hMB : Uc.ucB ≤ M) (hMθ : M < ConjT.th S) (hc : Xo.XoCase S (Dl τ n) M) (hρ1 : ρ < Om1)
    (hT : Om1 * M + ρ ∈ Tset (Dl τ n)) (hlt : vt (Dl τ n) (Om1 * M + ρ) < Dp τ n) :
    ∃ ρ', (ρ' = Dl τ n + ρ ∨ ρ' = ρ) ∧ Om1 * M + ρ' ∈ Tset τ ∧
      vt (Dl τ n) (Om1 * M + ρ) = vt τ (Om1 * M + ρ') :=
  Xo.xoVt_up hτ hτ1 hn hMB hMθ hc hρ1 hT hlt

/-- STATUS: PROVED (by `Xo.xoSup_ww`; NEW round 124)
SIZE: S
the old supply clause `Ww.WwSup` (leaf `skSupKW`, now OFF THE ROAD) follows from the new one -/
theorem skSupKW_of_Xo {k : ℕ} {l ν : Ordinal.{0}} (h : SkCtx S k l ν) : Ww.WwSup S l (ν - l + ω ^ 2) :=
  Xo.xoSup_ww (skSupKXo h)

/-! ## Round 125: the repaired restriction -/

/-- STATUS: PROVED (by `Xo.xoR_fixed`; NEW round 125)
SIZE: S
every closed spelling of a countable point `≥ υ_μ` violates the repaired `XoR` -/
theorem skXoFixed {l μ : Ordinal.{0}} (E : Xo.XoE) (hc : Xo.XoCl E) (h1 : upsilon μ ≤ Xo.xoVal S l E)
    (h2 : Xo.xoVal S l E < Om1) : ¬ Xo.XoR S l μ E :=
  Xo.xoR_fixed E hc h1 h2

/-- STATUS: PROVED (by `Xo.xoE2_notR`, `Xo.xoE2_WF`, `Xo.xoE2_val`; NEW round 125; the audit's BLOCKING witness)
SIZE: S
`E″ = sg h₁ + th 1 (lc B₂ + F_k) (lo λ)` is well formed with value `r(λ+X′)` and excluded at every `μ` with `υ_μ ≤ λ` -/
theorem skXoFkEx (k : ℕ) (hν : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC) {β μ : Ordinal.{0}}
    (hβ : Xj.xjX S k + ω + 1 < β) (hb1 : upsilon (Nc.ncL S (k : Ordinal.{0}) + β) ≤ Om1)
    (hμ : upsilon μ ≤ Nc.ncL S (k : Ordinal.{0})) :
    Xo.XoWF S (Nc.ncL S (k : Ordinal.{0})) β (Xo.xoE2 S k) ∧
      Xo.xoVal S (Nc.ncL S (k : Ordinal.{0})) (Xo.xoE2 S k) = cdR S (Nc.ncL S (k : Ordinal.{0}) + Xj.xjX S k) ∧
      ¬ Xo.XoR S (Nc.ncL S (k : Ordinal.{0})) μ (Xo.xoE2 S k) :=
  ⟨Xo.xoE2_WF k hβ hb1, (Xo.xoE2_val k).trans (Xo.xoXj_val k hν), Xo.xoE2_notR k hμ⟩

/-- STATUS: PROVED (by `Xo.xoE3_notR`, `Xo.xoE3_WF`, `Xo.xoE3_val`; NEW round 125)
SIZE: S
the absorbed `E‴ = (F′_k + sg h₁) + th 1 (lc B₂ + lo λ) (lo λ)` is well formed with value `r(λ+X′)` and excluded -/
theorem skXoAbsEx (k : ℕ) (hν : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC) {β μ : Ordinal.{0}}
    (hβ : Xj.xjX S k + ω + 1 < β) (hb1 : upsilon (Nc.ncL S (k : Ordinal.{0}) + β) ≤ Om1)
    (hμ : upsilon μ ≤ Nc.ncL S (k : Ordinal.{0})) :
    Xo.XoWF S (Nc.ncL S (k : Ordinal.{0})) β (Xo.xoE3 S k) ∧
      Xo.xoVal S (Nc.ncL S (k : Ordinal.{0})) (Xo.xoE3 S k) = cdR S (Nc.ncL S (k : Ordinal.{0}) + Xj.xjX S k) ∧
      ¬ Xo.XoR S (Nc.ncL S (k : Ordinal.{0})) μ (Xo.xoE3 S k) :=
  ⟨Xo.xoE3_WF k hβ hb1, (Xo.xoE3_val k).trans (Xo.xoXj_val k hν), Xo.xoE3_notR k hμ⟩

/-- STATUS: PROVED NEGATION (by `Xo.xoNaive_ref`; NEW round 125): the syntactic repair `Xo.XoRn` (closed sub-terms
only) is REFUTED wherever the reach formula holds at `μ + f(X′)`
SIZE: M -/
theorem skXoNaiveRef (k : ℕ) (hν : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC) {β μ B : Ordinal.{0}}
    {f : Ordinal.{0} → Ordinal.{0}} {Os : Finset Ordinal.{0}}
    (hβ : Xj.xjX S k + ω + 1 < β) (hb1 : upsilon (Nc.ncL S (k : Ordinal.{0}) + β) ≤ Om1)
    (hμ0 : 0 < μ) (hμl : upsilon μ < upsilon (Nc.ncL S (k : Ordinal.{0})))
    (hO : Sl.SlOff f Os B) (hμB : μ + B ≤ Nc.ncL S (k : Ordinal.{0}))
    (hX : Xj.xjX S k ∈ Os) (h1 : Xj.xjX S k + ω + 1 ∈ Os) (hone : (1 : Ordinal.{0}) ∈ Os)
    (hr : cdR S (μ + f (Xj.xjX S k)) = upsilon (μ + (f (Xj.xjX S k) + ω + 1)) + f (Xj.xjX S k)) :
    ¬ Xo.XoCarryN S (Nc.ncL S (k : Ordinal.{0})) β μ f B Os :=
  Xo.xoNaive_ref k hν hβ hb1 hμ0 hμl hO hμB hX h1 hone hr

/-- STATUS: PROVED (by `Xo.xoXj_R`, `Xo.xoU1_R`, `Xo.xoNest_R`, `Xo.xo_lo_R`; NEW round 125)
SIZE: S
`λ`, `X′` and the next candidates keep restricted terms -/
theorem skXoKeep (k : ℕ) {μ : Ordinal.{0}} (hμ0 : 0 < μ) (hμl : upsilon μ < upsilon (Nc.ncL S (k : Ordinal.{0})))
    (hτO : upsilon (Nc.ncL S (k : Ordinal.{0}) + (Xj.xjX S k + ω + 1)) < Om1) :
    Xo.XoR S (Nc.ncL S (k : Ordinal.{0})) μ (.old (.lo (Nc.ncL S (k : Ordinal.{0})))) ∧
      Xo.XoR S (Nc.ncL S (k : Ordinal.{0})) μ (Xo.xoXjE S k) ∧
      Xo.XoR S (Nc.ncL S (k : Ordinal.{0})) μ (Xo.xoU1E S k) ∧
      Xo.XoR S (Nc.ncL S (k : Ordinal.{0})) μ (Xo.xoNestE S k) :=
  ⟨Xo.xo_lo_R k hμ0 hμl, Xo.xoXj_R k hμ0 hμl hτO, Xo.xoU1_R k hμ0 hμl, Xo.xoNest_R k hμ0 hμl⟩

/-- STATUS: PROVED (by `Xo.xoOff_wit`; NEW round 125)
SIZE: S
for all `ε`-numbers `X, Y > 1` an offset map on `{1, X, X+ω+1}` with `f(X) = Y` (the obligation `X′_μ ≤ f(X′)`
is consistent with `Sl.SlOff`) -/
theorem skXoOffWit {X Y : Ordinal.{0}} (hX : InE X) (hY : InE Y) (hX1 : 1 < X) (hY1 : 1 < Y) :
    ∃ f : Ordinal.{0} → Ordinal.{0}, Sl.SlOff f {1, X, X + ω + 1} (Y + ω ^ 2) ∧ f X = Y ∧ f 1 = 1 :=
  ⟨Xo.xoOffF X Y, Xo.xoOff_wit hX hY hX1 hY1⟩

/-! ## Round 126: the covering lemma for the repaired `Xo.XoR` (`Yb`) -/

/-- STATUS: REDUCED (round 129: from `skYbIFHuge` by `Yq.yqIF_of_huge`; PROVED at every level whose datum is below
some `ψ_{Ω₁}(A)`, `Yq.yqIF_dat`) (NEW round 127; OFF THE ROAD: the part of `skYbIF` left)
SIZE: L
`Yg.YgIFTh`: every level `B₂ ≤ M < θ` with `d_S(M) < q` (`q` strongly critical, `q ≤ Ω₁`) is in `Yb.YbK S q`.
REFUTE FIRST (round 127): NO EVIDENCE.  The naive route is refuted (`skYbNaiveRef`); at the test level
`ψ_{Ω₂}(ψ_{Ω₃}(I₀))` the inaccessible washes out (`skYbTwin`); levels with datum `< Γ₀` hold (`skYbIFLow`).
Expected route: the port of `Yg.ygUcK` to `[B₂, θ)` with the normal form `Hˡ_λ(y) = ψ_{Ω₂}(B + Ω₂^λ·D)`
(`Vd.vd_nf_ex`): the own argument `B + Ω₂^λ·D < Ω_ω`, the level `λ < Ω₃` at the threshold `Ω₂` (`Vd.VdK S 1`),
and the lemma that every collapse inside an own argument below `Ω_ω` has an argument below `Ω_ω` (no `I_n`, unlike
`Y`); `Uf.ufRun` / `Uf.ufRun_eq` at `θ` are not in the repo. -/
theorem skYbIFTh (S : InaccSeq.{0}) : Yg.YgIFTh S := Yq.yqIF_of_huge (skYbIFHuge S)

/-- STATUS: REDUCED (round 127: from `skYbIFTh` by `Yg.ygIF_of_th`; below `B₂` PROVED, node `skYbIFLowB`) (NEW round 126; OFF THE ROAD: a tool for `skRealBXo` through `skCoverXo`, not a hypothesis of
`Xo.xoRoadH`)
SIZE: L
the notation statement `Yb.YbIF`: every level `Ω₁ ≤ M < θ` lies in the inacc-free closure `Yb.YbK S q` (small
members below `q`, fixed atoms with data below `Γ₀`, `+`, `φ`, `Ω_·`, `ψ_π` with `π ≠ Ω₁`) at every strongly critical
`q ≤ Ω₁` above its datum (`ucDat M` below `B₂`, `d_S(M)` on `[B₂, θ)`).
REFUTE FIRST: NO EVIDENCE.  Holds at `Ω₁` and `B₂` (node `skYbIFWit`).  Expected route: below `B₂` the code test
`Uc.UcCl` (whose constructors use only `Ω₁`, `+`, `φ`, `ψ_{Ω₂}`-atoms `Uc.ucH`) ported from `Uo.uo_ucK` with `YbK` in
place of `Ul.UlK`; on `[B₂, θ)` the normal form `Hˡ_λ(y)` (`Vd.vd_nf_ex`) with `ψ_{Ω_k}` only.  A level that needs an
inaccessible in every spelling would have no restricted term at all (`lc (I n)` is not restricted, `I_n ≥ θ`). -/
theorem skYbIF (S : InaccSeq.{0}) : Yb.YbIF S := Yg.ygIF_of_th (skYbIFTh S)

/-- STATUS: PROVED (by `Yb.ybIF_wit`; NEW round 126)
SIZE: S
`Ω₁, B₂ ∈ YbK S q` for every strongly critical `q` (the hypotheses of `skYbIF` are satisfiable) -/
theorem skYbIFWit {q : Ordinal.{0}} (hq : SC q) : Yb.YbK S q Om1 ∧ Yb.YbK S q Uc.ucB := Yb.ybIF_wit hq

/-- STATUS: PROVED (by `Yb.ybLevK_of_IF`; NEW round 126)
SIZE: M
`YbIF ⇒ YbLevK S λ β` (`0 < λ`, `υ_{λ+β} ≤ Ω₁`) -/
theorem skLevOfIF {l β : Ordinal.{0}} (hl0 : 0 < l) (hb1 : upsilon (l + β) ≤ Om1) (hIF : Yb.YbIF S) :
    Yb.YbLevK S l β :=
  Yb.ybLevK_of_IF hl0 hb1 hIF

/-- STATUS: PROVED (by `Yb.ybCover`; NEW round 126)
SIZE: M
the covering lemma from the level statement -/
theorem skCoverLev {l β : Ordinal.{0}} (hl0 : 0 < l) (hK : Yb.YbLevK S l β) :
    ∀ x, x < upsilon (l + β) → x < Om1 → Yb.YbCov S l β x :=
  Yb.ybCover hl0 hK

/-- STATUS: REDUCED (from `skYbIF`, `skLevOfIF`, `skCoverLev`; NEW round 126)
SIZE: S
THE COVERING LEMMA: every countable `x < υ_{λ+β} ≤ Ω₁` (`0 < λ`) has a well-formed, non-closed moving-leaf
decomposition with a finite offset set below `β`, restricted (`Xo.XoR`) at every `μ` in a tail `γ < υ_μ < υ_λ` -/
theorem skCoverXo {l β : Ordinal.{0}} (hl0 : 0 < l) (hb1 : upsilon (l + β) ≤ Om1) :
    ∀ x, x < upsilon (l + β) → x < Om1 → Yb.YbCov S l β x :=
  skCoverLev hl0 (skLevOfIF hl0 hb1 (skYbIF S))

/-- STATUS: PROVED (by `Yb.ybCov_wit`, `Yb.ybTail_wwX`, `Yb.ybWwXE_val`; NEW round 126)
SIZE: S
the covering at the witnesses with no hypothesis: `λ`, `r(λ+X′)`, and `wwX` (restricted on a tail) -/
theorem skCoverWit (k : ℕ) (hν : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC) {β : Ordinal.{0}}
    (hβ : Xj.xjX S k + ω + 1 < β) (hb1 : upsilon (Nc.ncL S (k : Ordinal.{0}) + β) ≤ Om1) :
    Yb.YbCov S (Nc.ncL S (k : Ordinal.{0})) β (Nc.ncL S (k : Ordinal.{0})) ∧
      Yb.YbCov S (Nc.ncL S (k : Ordinal.{0})) β (cdR S (Nc.ncL S (k : Ordinal.{0}) + Xj.xjX S k)) ∧
      Yb.YbTail S (Nc.ncL S (k : Ordinal.{0})) (Yb.ybWwXE S k) ∧
      Xo.xoVal S (Nc.ncL S (k : Ordinal.{0})) (Yb.ybWwXE S k) = Ww.wwX S k :=
  ⟨(Yb.ybCov_wit k hν hβ hb1).1, (Yb.ybCov_wit k hν hβ hb1).2, Yb.ybTail_wwX k, Yb.ybWwXE_val k⟩

/-- STATUS: REDUCED (from `skYbIF`, by `Yb.ybSup_bound_IF`; NEW round 126)
SIZE: S
THE NON-SILENT SUPPLY: from `Xo.XoSup S λ β`, for every `γ < υ_λ` and finite offset set `G` below `β`, a supply
configuration `(μ, f, B, Os ⊇ G)` above `γ` whose carry bounds the image of a restricted decomposition of every inner
reach `r(λ+g) < υ_{λ+β}`, `g ∈ G` -/
theorem skSupNonSilent {l β : Ordinal.{0}} (hl0 : 0 < l) (hb1 : upsilon (l + β) ≤ Om1) (hl1 : upsilon l < Om1)
    (hS : Xo.XoSup S l β) :
    ∀ γ < upsilon l, ∀ G : Finset Ordinal.{0}, (∀ d ∈ G, d < β) →
      ∃ μ f B, ∃ Os : Finset Ordinal.{0}, G ⊆ Os ∧ CdRange S μ ∧ γ < upsilon μ ∧ upsilon μ < upsilon l ∧
        μ + B ≤ l ∧ ω ^ 2 ∣ B ∧ upsilon (μ + B) ≤ cdR S μ ∧ Sl.SlOff f Os B ∧ Xo.XoCarry S l β μ f B Os ∧
        ∀ g ∈ G, 0 < g → ω ^ 2 ∣ g → cdR S (l + g) < upsilon (l + β) →
          ∃ E : Xo.XoE, Xo.XoWF S l β E ∧ Xo.xoVal S l E = cdR S (l + g) ∧ Xo.XoR S l μ E ∧
            Xo.xoImg S l μ f E ≤ cdR S (μ + f g) :=
  Yb.ybSup_bound_IF hl0 hb1 hl1 (skYbIF S) hS

/-! ## Round 127: `YbIF` below `B₂`, the naive route refuted, the carry at `wwX` (`Yg`) -/

/-- STATUS: PROVED (by `Yg.ygIF_lowB`; NEW round 127)
SIZE: L
`YbIF` below `B₂`: `Ω₁ ≤ M < B₂`, `ucDat M < q` (`q` strongly critical, `q ≤ Ω₁`) ⇒ `M ∈ YbK S q` -/
theorem skYbIFLowB {M q : Ordinal.{0}} (hq : SC q) (hq1 : q ≤ Om1) (hMB : M < Uc.ucB) (hd : Uc.ucDat M < q) :
    Yb.YbK S q M :=
  Yg.ygIF_lowB hq hq1 hMB hd

/-- STATUS: PROVED (by `Yg.ygIF_low`; NEW round 127)
SIZE: S
`YbIF` at every level `M < θ` whose datum is below `Γ₀` -/
theorem skYbIFLow {M : Ordinal.{0}} (q : Ordinal.{0}) (hMθ : M < ConjT.th S)
    (h1 : M < Uc.ucB → Uc.ucDat M < gamma 0) (h2 : Uc.ucB ≤ M → Vd.vdD S 0 M < gamma 0) : Yb.YbK S q M :=
  Yg.ygIF_low q hMθ h1 h2

/-- STATUS: PROVED (by `Yg.ygIF_B_add`; NEW round 127; REFUTE-FIRST test just above `B₂`)
SIZE: S
`B₂ + c ∈ YbK S q` for `c < q` -/
theorem skYbIFBAdd {q c : Ordinal.{0}} (hq : SC q) (hc : c < q) : Yb.YbK S q (Uc.ucB + c) :=
  Yg.ygIF_B_add hq hc

/-- STATUS: PROVED NEGATION (by `Yg.ygVdK_notYb`, `Yg.ygY_notK`, `Yg.ygY_VdK`; NEW round 127): the naive route to
`skYbIF` (every `Vd.VdK`-derivation is inacc-free) is REFUTED: `ψ_{Ω₃}(I₀) ∈ Vd.VdK S 0 q \ Yb.YbK S q`
SIZE: M -/
theorem skYbNaiveRef {q : Ordinal.{0}} (hq : q ≤ Om1) :
    Vd.VdK S 0 q (Yg.ygY S) ∧ ¬ Yb.YbK S q (Yg.ygY S) ∧ ¬ ∀ x, Vd.VdK S 0 q x → Yb.YbK S q x :=
  ⟨Yg.ygY_VdK q, Yg.ygY_notK hq, Yg.ygVdK_notYb hq⟩

/-- STATUS: PROVED (by `Yg.ygTwin_lev`; NEW round 127; REFUTE-FIRST test of `skYbIFTh`)
SIZE: M
the level `M₀ = ψ_{Ω₂}(ψ_{Ω₃}(I₀))` lies in `[B₂, θ)`, has a spelling with `I₀` at every threshold, and is in
`YbK S q` (it equals `ψ_{Ω₂}(Ω₃)`) -/
theorem skYbTwin {q : Ordinal.{0}} (hq : SC q) :
    Uc.ucB ≤ S.psi (Yg.ygY S) (Om (1 + 1)) ∧ S.psi (Yg.ygY S) (Om (1 + 1)) < ConjT.th S ∧
      Vd.VdK S 0 q (S.psi (Yg.ygY S) (Om (1 + 1))) ∧ Yb.YbK S q (S.psi (Yg.ygY S) (Om (1 + 1))) :=
  Yg.ygTwin_lev hq

/-- STATUS: PROVED (by `Yg.ygCarry_ww`; NEW round 127; REFUTE-FIRST test of the carry at the gap witness)
SIZE: M
the carry at `wwX` asks `υ_{μ+f(h_W)} + W_μ ≤ r(μ+f(wwX))` -/
theorem skXoCarryWw (k : ℕ) (hν : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC) {β μ B : Ordinal.{0}}
    {f : Ordinal.{0} → Ordinal.{0}} {Os : Finset Ordinal.{0}}
    (hC : Xo.XoCarry S (Nc.ncL S (k : Ordinal.{0})) β μ f B Os) (hX : Ww.wwX S k ∈ Os)
    (h1 : Ww.wwX S k + ω + 1 ∈ Os) (hone : (1 : Ordinal.{0}) ∈ Os)
    (hβ : Ww.wwX S k + ω + 1 < β) (hb1 : upsilon (Nc.ncL S (k : Ordinal.{0}) + β) ≤ Om1)
    (hμ0 : 0 < μ) (hμl : upsilon μ < upsilon (Nc.ncL S (k : Ordinal.{0})))
    (hτ'O : upsilon (μ + f (Ww.wwX S k + ω + 1)) < Om1) :
    upsilon (μ + f (Ww.wwX S k + ω + 1)) + Yg.ygWwMu μ f ≤ cdR S (μ + f (Ww.wwX S k)) :=
  Yg.ygCarry_ww k hν hC hX h1 hone hβ hb1 hμ0 hμl hτ'O

/-- STATUS: PROVED (by `Yg.ygWw_obl`; NEW round 127)
SIZE: S
under the reach formula at `μ`, the carry at `wwX` ⇔ `W_μ ≤ f(wwX)` -/
theorem skXoOblWw (k : ℕ) {μ B : Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} {Os : Finset Ordinal.{0}}
    (hO : Sl.SlOff f Os B)
    (hr : cdR S (μ + f (Ww.wwX S k)) = upsilon (μ + (f (Ww.wwX S k) + ω + 1)) + f (Ww.wwX S k)) :
    upsilon (μ + f (Ww.wwX S k + ω + 1)) + Yg.ygWwMu μ f ≤ cdR S (μ + f (Ww.wwX S k)) ↔
      Yg.ygWwMu μ f ≤ f (Ww.wwX S k) :=
  Yg.ygWw_obl k hO hr


/-! ## Round 130: the level sort below `θ` (tools for `skShift2`) -/

/-- STATUS: PROVED (by `Yv.yv_pi_TB`; NEW round 130)
SIZE: L
`π_{σ,τ} = yvSub π_{σ,τ}` on `Tᵗ[σ] ∩ θ` (the base change on codes below `θ` is the leaf substitution) -/
theorem skYvPi {σ τ z : Ordinal.{0}} (h : Bases σ τ) (hz : z < ConjT.th S) (hT : z ∈ TB τ σ) :
    pi σ τ z = Yv.yvSub S (pi σ τ) z :=
  Yv.yv_pi_TB h hz hT

/-- STATUS: PROVED (by `Yv.yv_comp_sub`; NEW round 130)
SIZE: L
`yvSub g (π z) = yvSub (g ∘ π) z` (bases with `Γ₀ ≤ σ`, leaves of `z` in `Tᵗ[σ]`) -/
theorem skYvComp {σ τ z : Ordinal.{0}} (h : Bases σ τ) (hσ : gamma 0 ≤ σ) (g : Ordinal.{0} → Ordinal.{0})
    (hz : z < ConjT.th S) (hL : Yv.YvLv S (· ∈ TB τ σ) z) :
    Yv.yvSub S g (pi σ τ z) = Yv.yvSub S (g ∘ pi σ τ) z :=
  Yv.yv_comp_sub h hσ g hz hL (Yv.yvR_ex _ hL)

/-- STATUS: PROVED (by `Yv.yv_up`; NEW round 130)
SIZE: M
`π⁻¹ G = yvSub π⁻¹ G` for `G ∈ T^σ`, `π⁻¹ G < θ` (bases with `Γ₀ ≤ σ`) -/
theorem skYvUp {σ τ G : Ordinal.{0}} (h : Bases σ τ) (hσ : gamma 0 ≤ σ) (hG : G ∈ Tset σ)
    (hz : up σ τ G < ConjT.th S) : up σ τ G = Yv.yvSub S (up σ τ) G :=
  (Yv.yv_up h hσ hG hz).1

/-- STATUS: PROVED (by `Yv.yv_node_img`; NEW round 130)
SIZE: M
the base change of a `ϑ`-node whose level `Ω₁·M < θ` has moving leaves: `π(ϑᵗ(Ω₁·M + ρ)) = ϑ^σ(Ω₁·M' + π ρ)`,
`Ω₁·M' = yvSub π (Ω₁·M)` a level -/
theorem skYvNode {σ τ M ρ : Ordinal.{0}} (h : Bases σ τ) (hM1 : 1 ≤ M) (hθ : Om1 * M < ConjT.th S)
    (hT : Om1 * M ∈ TB τ σ) (hρ : ρ ∈ TB τ σ) (hρ1 : ρ < Om1) :
    ∃ M', Om1 * M' = Yv.yvSub S (pi σ τ) (Om1 * M) ∧ 1 ≤ M' ∧ Om1 * M' < ConjT.th S ∧
      Om1 * M + ρ ∈ TB τ σ ∧ pi σ τ (vt τ (Om1 * M + ρ)) = vt σ (Om1 * M' + pi σ τ ρ) :=
  Yv.yv_node_img h hM1 hθ hT hρ hρ1

/-- STATUS: PROVED (by `Yv.yv_dat_iff`, no project axiom; NEW round 130)
SIZE: M
`d_S(z) < q ⇔ every leaf of `z` is below `q`` (`q` strongly critical, `q ≤ Ω₁`, `z < θ`) -/
theorem skYvDat {q z : Ordinal.{0}} (hq : SC q) (hq1 : q ≤ Om1) (hz : z < ConjT.th S) :
    Vd.vdD S 0 z < q ↔ Yv.YvLv S (· < q) z :=
  Yv.yv_dat_iff hq hq1 hz

/-- STATUS: PROVED (by `Yv.yv_node_tr`; NEW round 130)
SIZE: S
the subcase of [W07a] Def 6.2 at a level `B₂ ≤ M < θ` with moving leaves is read off the leaves (`α = Dl τ n`
strongly critical): all below `α` ⇒ `R2.xeVt_trL`, else `R2.xoVt_trH` -/
theorem skYvTr {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) {n : ℕ} (hn : 1 ≤ n) {M ρ : Ordinal.{0}}
    (hMB : Uc.ucB ≤ M) (hMθ : M < ConjT.th S) (hα : SC (Dl τ n)) (hρ1 : ρ < Om1)
    (hL : ¬ Yv.YvLv S (· < Dl τ n) M) (hT : Om1 * M + ρ ∈ Tset (Dl τ n))
    (hlt : vt (Dl τ n) (Om1 * M + ρ) < Dp τ n) :
    Om1 * M + ρ ∈ Tset τ ∧ vt (Dl τ n) (Om1 * M + ρ) = vt τ (Om1 * M + ρ) :=
  ((Yv.yv_node_tr hτ hτ1 hn hMB hMθ hα hρ1).2 hL).1 hT hlt

/-- STATUS: PROVED (by `Yv.yv_wit_pi`, `Yv.yv_wit_hi`; NEW round 130; REFUTE-FIRST test of `XoThCl` at a node whose
level has one moving leaf, the base itself)
SIZE: S
`π(ϑᵗ(Ω₁·(B₂ + τ) + ρ)) = ϑ^σ(Ω₁·(B₂ + σ) + π ρ)`, and the leaf `α` of `B₂ + α` is not below `α` (subcase `Γ^* ≥ α`) -/
theorem skYvWit {σ τ ρ α : Ordinal.{0}} (h : Bases σ τ) (hσ : gamma 0 ≤ σ) (hρ : ρ ∈ TB τ σ) (hρ1 : ρ < Om1)
    (hα : SC α) (hα1 : α < Om1) :
    pi σ τ (vt τ (Om1 * (Uc.ucB + τ) + ρ)) = vt σ (Om1 * (Uc.ucB + σ) + pi σ τ ρ) ∧
      ¬ Yv.YvLv S (· < α) (Uc.ucB + α) :=
  ⟨(Yv.yv_wit_pi S h hσ hρ hρ1).2, Yv.yv_wit_hi hα hα1⟩

/-- STATUS: PROVED (by `Yv.yv_cl_frag`; NEW round 130; non-vacuity of `Yv.YvCl` on its constant part)
SIZE: S
the FRAG map of `Xj.xjFragXe` satisfies the moving-level clause at every constant level `B₂ ≤ q < θ` -/
theorem skYvClConst {m : ℕ} {κ : Ordinal.{0}} {b c : ℕ → Ordinal.{0}} (hb : Chain κ b m) (hc : Chain κ c m)
    (F : Finset Ordinal.{0}) (hF : ↑F ⊆ DD κ b m) :
    ∃ Ψ, Vl.VlFragConcl κ b c m F Ψ ∧ Xj.XjCl Xe.XeLev κ b c m F Ψ ∧
      ∀ k, k < m → ∀ (q q₀ : Ordinal.{0}) (r : Un.UnC), Uc.ucB ≤ q → q < ConjT.th S → SC q₀ → q₀ ≤ κ →
        Vd.vdD S 0 q < q₀ →
        Vi.ZW (b k) r → Ur.WFr (b k) r → Un.UnT.ev (b k) r < Om1 →
        Un.UnT.Lv (· ∈ F) r → Vi.ZL (fun p => p ∈ F ∨ p < κ) r → Un.UnT.Lv (· ∈ Tset (b k)) r →
        Vi.ZL (· ∈ Tset (b k)) r →
        vt (b k) (Om1 * q + Un.UnT.ev (b k) r) ∈ F → InSeg (b k) (vt (b k) (Om1 * q + Un.UnT.ev (b k) r)) →
          Ψ (vt (b k) (Om1 * q + Un.UnT.ev (b k) r)) =
              vt (c k) (Yv.yvSub S Ψ (Om1 * q) + Un.UnT.ev (c k) (Vi.vmap Ψ r)) ∧
            Ur.WFr (c k) (Vi.vmap Ψ r) ∧ Vi.ZW (c k) (Vi.vmap Ψ r) ∧ Un.UnT.ev (c k) (Vi.vmap Ψ r) < Om1 :=
  Yv.yv_cl_frag hb hc F hF

/-- STATUS: OPEN (NEW round 130; OFF THE ROAD: the next statement for `skShift2`, not yet a Lean reduction of it)
SIZE: L
FRAG with the moving-level hull clause below `θ`: for chains `b`, `c` over `κ` and a finite `F ⊆ D_m`, a FRAG map
`Ψ` (`Vl.VlFragConcl`) with `Yv.YvCl S κ b c m F Ψ`.  Proof plan: `Xj.xjFrag_step` with the node lemmas
`Yv.yv_node_img` (compression), `Yv.yv_node_tr` (translation, the subcase read off the leaves of the compressed
level; needs `α = Dl b_n M` strongly critical for `M ≥ 2`), `Yv.yv_up` (expansion), `Yv.yv_comp` (the substitutions
compose); missing tools: the leaves of `yvSub π z` are the `π`-images of the leaves of `z` (both directions; the
analogue of `Vi.vi_lv_pi`), the level clause `Vl.VlLC` with `yvSub` and bound `θ` (the analogue of `Vl.vl_lc_comp`),
membership of a level from its leaves in `T^g` (the analogue of `Vl.vl_lv_mem`, from `R2.vdArg_mem`).  For
`skShift2` itself one more step: the image `Xo.xoImg` of a restricted level term equals `yvSub D` of its value. -/
theorem skYvCl {m : ℕ} {κ : Ordinal.{0}} {b c : ℕ → Ordinal.{0}} (hb : Chain κ b m) (hc : Chain κ c m)
    (F : Finset Ordinal.{0}) (hF : ↑F ⊆ DD κ b m) :
    ∃ Ψ, Vl.VlFragConcl κ b c m F Ψ ∧ Yv.YvCl S κ b c m F Ψ := by sorry

end R2Skel.SkS
