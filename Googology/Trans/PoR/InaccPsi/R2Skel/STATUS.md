# R₂^C skeleton: status (round 220)
Root `R2Skel.Root.skNuC (S : InaccSeq)` = the conclusion of `Xo.xoRoadH` (ν_C = L(ω+1), …). Round 129: the root applies
`Yq.yqRoadS` = `Xo.xoRoadH` with the bridge replaced by the shift `SkS.skShiftXo`; supply `SkS.skSupXo` (repaired `Xo.XoR`);
frontier `SkF.skFront` → hUH/hLH/hVH/hVt; reading `SkR.skWall`, `SkR.skThHi` → `SkE.skEQ` → hT/hF. Round 130: Root unchanged.
Round 131: `SkE.skEQ hRead hUH hLH hVt`. Round 132: `SkE.skEQ hRead hW hUH hLH hVt`, `hW = SkR.skWallCF S` (the code-free
wall, used by `SkE.skTopK`). Round 133: Root unchanged; the bundle checks against the main build with only `declaration uses sorry` (68).
## Main progress number: OPEN / SUSPECT leaves on the road from `Root.skNuC`
**14 distinct OPEN leaves (all L); 0 SUSPECT; 0 REFUTED** (round 220: atom system below θ, Qt.qtU, with Zb.ZbAS.Ok; round 219: skLayPastXθ split, skLayPastXB2 PROVED (Qc.qc_past), skLayPastB2θ OPEN; round 215: skZbDirectX PROVED, Va.vsDirectX; round 182: skAtHi3 PROVED, Kz.kzAtHi3; 176: skPsi3OffRest2 PROVED, Ky.kyPsi3OffRest2; 174: skTopLawAll PROVED, Kx.kxTopLawAll; round 138: 17 after merges, then the road leaf skLayPastX was REFUTED and split; 137: 20; 135: 22 L; 134: 22; 133: 23; 132: 18 L; round 131: 18; round 130: 19 OPEN L; round 129: 19;
rounds 127, 128: 17). Counted by a Lean walk over the constants used by `skNuC`. On the road: SkF skLayPastB2θ, skLayPastTh,
skBC{BaseUL, InR, RsSH}, skFix{Cont, CapVF}, skWin/Top{InR, Big}, skTopLwNo2;
SkS skZlCfg, skLevImgHi4. Round 130: skWin/TopSpec → skWinIn, skTopIn, skTopLwNo2; skGapRng → skGapRngHi. Round 131:
skJumpNoRng, skGapRngHi PROVED (hVt); skLay{Lo,Hi}Fix → skZbDirect, skLay{Lo,Hi}FixX; skWin/TopIn, skWin/TopRsIn → skWin/TopInR,
skWin/TopRsT. Round 132: skWin/TopRsT, skWin/TopCapV → skWin/TopRsS, skWin/TopCapVL; skTopK → skTopG; skShift2 → skLevImgHi2.
Round 133 (narrower leaves, 18 → 23): skZbDirect → skZbDirectX; skLay{Lo,Hi}FixX → skLayPastX; skBhiAfar, skBhiL, skLongPre → 5
skBC* leaves; skWin/TopRsS, skWin/TopCapVL → skWin/Top{IsoCode, Cont, Big, CapVF}; skWallBase, skWallStep → skTopLawAll,
skPsi3OffRest2; skTopG → skAtHi3; skSupKXo → skZlCfg; skLevImgHi2 → skLevImgHi4. Round 134: skBCReach, skBCThPos PROVED from skBCBaseUL (Zr: l₀ = ι(Ω₂), Θ(π_{Ω₂}) < δ); skBCBaseUV → skBCBaseUL. Round 135: skBCBaseUL M → L (big reading, skBCBaseBig); skBCCapVH → codes > K_ω (skBCCapVK). Round 136: skWin/TopIsoCode PROVED (Zt.ztIsoCode, Fx.fxIso_theta). Round 137: skBCRsS → skBCRsSH; skBCCapVH far readings only. Round 138 (merges, no new proof): skFixCont, skFixCapVF.

**Vacuity of `Root.skNuC`: open.** No REFUTED or SUSPECT leaf on the road; `Zl.ZlCfg`, `Zk.ZkImgP4`, `Zq.ZqAtHi3` not shown satisfiable.
## Node tree (STATUS SIZE)
```
skNuC REDUCED L  (Yq.yqRoadS)
├ SkF.skFront REDUCED L ─ skAbove REDUCED L
│ ├ skRegA: REGION A CLOSED (skSysCof, skSysA3, skSysA3StepW PROVED L); off the road skA3T0Start OPEN L
│ ├ skRegB REDUCED L  (cells: base β ∈ {0, Ω₂·q, b_k, b_ω} + offset ζ < Ω₂)
│ │ ├ skRegBlo ─ skLay REDUCED L
│ │ │   skLayLo REDUCED L: skLayLoD (c+1 < ε₀) PROVED, skLayLoBig REDUCED L ─ skLayBelowBG, skLayLoFix REDUCED L
│ │ │   skLayHi REDUCED L: skLayDirect PROVED L, skLayHiBig REDUCED L ─ skLayBelowBG, skLayHiFix REDUCED L
│ │ │   round 131: ─ skZbDirect (B_Γ ≤ c < X), skLayLoFixX, skLayHiFixX (X ≤ c < Ω₂); skZbDirectE0 +3 PROVED
│ │ │   round 132: skZbDirect holds below B_Γ·B_Γ with no hypothesis (skZgDirectSq); skZgTl, skZgRef +3 PROVED
│ │ │   round 133: skZbDirect ─ skZbDirectX PROVED L (round 215, Va.vsDirectX; no hypothesis below B₂, the next fixed point of Γ: Va.vaDirectB2, skVaDirectB2, round 207; digit systems at every ε-number below X over gated segment bases: skVsGoodAll, round 213); skLay{Lo,Hi}FixX ─
│ │ │     skLayPastX REFUTED (138) → skLayPastXθ REDUCED (219: skLayPastXB2 PROVED, Qc.qc_past; skLayPastB2θ OPEN L), skLayPastTh OPEN L; 7 Zm PROVED; skLayBelowBG L (129), …
│ │ │   off the road: skLaySysY REDUCED L ─ skLaySysAll1, skLaySysYHi OPEN L; skLaySys_false, skFixReadX_false REFUTED S
│ │ ├ skRegBhi REDUCED L: skBhiA REDUCED L ─ skBhiAcell PROVED M, skBhiAfar;  skBhiL  (round 133: both PROVED from skBC)
│ │ ├ skWinA, skWinB ─ skWinL REDUCED L ─ skWinUL PROVED S, skWinSpec ─ skWinInR OPEN L
│ │ │   round 131 (Zc.zcWins2): skWinBase, skRsLongNoGo, skRsLongLower, skGivenOfUp, skWinInRVac PROVED
│ │ │   round 132 (Zh.zhWins6): skWinRsT, skWinCapV REPLACED by skWinRsS, skWinCapVL (υ-fixed restarts only)
│ │ │   round 133 (Zn.znWins): REPLACED by skWinRsF REDUCED L ─ skWinIsoCode PROVED (136), skWin{Cont, Big, CapVF} OPEN L; PROVED 12 Zn; 129 skWinStep M, …
│ │ └ skTopA, skTopB ─ skTopL REDUCED L ─ skTopUL, skTopPair, skTopNu, skTopNoBase PROVED S; skTopRsF REDUCED L (133, Zn.znTopAll)
│ │     ─ skTopIsoCode PROVED (136), skTop{Cont, Big, CapVF} OPEN L; skTopSpec REDUCED L (130 Yx.yxTopAll; 131 Zc.zcTopAll2) ─ skTopInR, skTopLwNo2 OPEN L
│ └ skRegC REDUCED L    skLongPre (round 133: PROVED from skBC); skLongMid, skLongTop PROVED S (vacuous); skBelowL0 REDUCED S
│     round 133: skBC REDUCED L (Zo.zoBC, one block induction on [l₀, ι(Ω_ω))) ─ skBC{BaseUV, Reach} OPEN M, skBC{InR, CapVH, RsS} OPEN L; round 134: skBCReach REDUCED, skBCThPos PROVED, skBCBaseUV REDUCED (CapV PROVED) ─ skBCBaseUL OPEN L (135: big reading, skBCBaseBig PROVED); 135: skBCCapVK PROVED, skBCCapVH narrowed
├ SkR.skWall REDUCED L ─ skWallCF ─ skWallLow REDUCED L   (round 132: skWallCF also feeds SkE.skEQ as hW)
│ │ skWallLevAll REDUCED L: skWallBase, skWallStep REDUCED L (round 133, Zp.zpWall, Zp.zpDecomp) ─ skTopLawAll PROVED L (round 174, Kx.kxTopLawAll)
│ │   (Θ(ψ₂ b) = ψ₁(A + 1 + ψ₂(T b)), normal Ω₃-divisible b ≥ Ω₃; b = β' + Ω₃ by Xi.xiTopUp0 and the first use Kx.kwFUG; a limit quotient b/Ω₃ by the bounded inverse transfer Kx.kxK and the normal hull Kx.kxNorm, Kx.kxLim), skPsi3OffRest2 PROVED L (round 176, Ky.kyPsi3OffRest2: the offset law Ky.kyOff Θ(ψ₂(a+δ)) = ψ₁(Â+Tδ), δ < Ω₃, at both ends; Ky.kyBase, Ky.kyMove); skTopUp PROVED L
│ │   off the road: skPsi3Off REDUCED L (round 130) ─ skPsi3OffLow PROVED, skPsi3OffHi OPEN L (bases a ≥ Ω₃);
│ │     round 131 skPsi3OffD REDUCED L (Ω₃-divisible bases) ─ skPsi3OffE0 PROVED M, skPsi3OffRest REDUCED L (round 132:
│ │     below W^{Y₃+Ω₂·Ω₂·K₃}, Zi.ziPsi3OffWK; law up to ξ < ψ₁(0), Zi.ziChain) ─ skPsi3OffRest2 PROVED (so skPsi3OffD, skWallBase, skWallStep are closed)
│ └ skWallTh PROVED M
├ SkR.skThHi REDUCED L: skThMid, skThFar REDUCED M (skWallCF, skTopK); off the road skMidAssemble SUSPECT M, skTopDyn …
├ SkE.skEQ REDUCED L  (round 131: takes hVt, passed through 12 nodes; round 132: takes hW, passed through 8 nodes)
│ ├ skThLow PROVED S;  └ skEQfar REDUCED L ─ skThFar ─ skTopK REDUCED S (round 132, Zj.zjTopK_ofG; shared with SkR)
│ │   ─ skTopG REDUCED L (round 133, Zq.zqTopG3; atoms move up to K_Y, Zq.zqAtK_Y) ─ skAtHi3 PROVED L (round 182, Kz.kzAtHi3); 8 PROVED
│     skKFar ─ skKCof ─ skKCofGap REDUCED S ─ skGapLh REDUCED S (round 130: takes hUH, hLH)
│       ├ skGapEps REDUCED S ─ skGapEpsIff PROVED S (+5 PROVED S), skGapEpsTop PROVED S (round 130, cites [W07b] Lemma 4.2)
│       ├ skGapRng REDUCED S (round 130, codes ≤ θ·ω done) ─ skGapRngHi PROVED S (round 131, Ze.zeGapRngHi, from hVt)
│       └ skGapBlk PROVED S (Yk.ykGapBlk, no hypothesis)
│     skKReachR ─ skEQTopR REDUCED L ─ skEQJump REDUCED S ─ skJumpOff PROVED S (vacuous),
│         skJumpNoRng PROVED S (round 131, Ze.zeJumpNoRng; short codes with no hypothesis, skJumpShortU; long from hVt)
├ SkS.skShiftXo REDUCED M ─ skShift2 REDUCED L (round 132, Zf.zfShift2) ─ skLevImg, skLevImgHi REDUCED L
│   ─ skLevImgHi2, skLevImgHi3 REDUCED L (133, Zk.zkImgP2_of_P4; segment sums, prefix levels are theorems) ─ skLevImgHi4 OPEN L
│   round 130 PROVED (leaf substitution below θ): 8 nodes skYv*; skYvCl PROVED L (round 132, was REDUCED, off the road)
│   round 131 off the road: skDlSC PROVED S (round 132, cited axiom R2.zfDl_vt, [W07a] L. 3.27) → skZaFrag, skZaShift3 PROVED
│     L; skShift4 REFUTED L (132) ─ skShift2_of4 PROVED S; skZaLevConst, skZaWitMv, skZaWitPhi PROVED S
└ SkS.skSupXo REDUCED L ─ skVisKXo REDUCED S ─ skGenXo REDUCED S
    ├ skUp REDUCED S ─ skUpRR REDUCED L (from SkF);  skFormXo PROVED S;  └ skSupKXo REDUCED L (133) ─ skZlCfg OPEN L (⇔ Xo.XoSup)
    off the road: skRealBXo REDUCED L; skYbIF REDUCED L ─ skYbIFTh REDUCED L ─ skYbIFNot PROVED M, skYbIFHuge OPEN L;
      skShiftTh PROVED L, skFormHighX REFUTED L, skSupKW, skImgEps, skCarryHigh OPEN L, skRealB SUSPECT L
```
## Counts (721 nodes)
| part | PROVED | REDUCED | OPEN | SUSPECT | REFUTED | REPLACED | S | M | L |
|---|---|---|---|---|---|---|---|---|---|
| SkF | 258 | 46 | 16 | 0 | 4 | 39 | 156 | 81 | 126 |
| SkR | 90 | 15 | 3 | 1 | 3 | 0 | 44 | 47 | 21 |
| SkE | 92 | 16 | 0 | 0 | 0 | 0 | 102 | 0 | 6 |
| SkS | 90 | 38 | 6 | 1 | 2 | 0 | 59 | 29 | 49 |
| Root | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 1 |
| all | 530 | 116 | 25 | 2 | 9 | 39 | 361 | 157 | 203 |

OPEN by size: L 23 (SkF 16, SkR 1, SkE 0, SkS 6), M 0, S 0. Off the road (8): skA3T0Start, skLaySysAll1,
skLaySysYHi, skPsi3OffHi, skYbIFHuge, skSupKW, skImgEps, skCarryHigh. SUSPECT: skMidAssemble M, skRealB L.
REFUTED: S 4, M 2, L 3. Sorry leaves (60): OPEN 23; SUSPECT 2; REFUTED skTopDyn, skTopFam, skX0Law, skFormHighX, skShift4
(record); REPLACED 30. Round 130 → 131: sorry 52 → 57, SUSPECT 2 → 3, nodes 549 → 588; road 19 → 18 OPEN L. Round 131 → 132:
sorry 57 → 60, OPEN 28 (27 L, 1 S) → 27 (all L), SUSPECT 3 → 2, REFUTED 7 → 8, nodes 588 → 640; road 18 → 18 OPEN L. Round
132 → 133: sorry 60 → 68, OPEN 27 (all L) → 31 (29 L, 2 M), nodes 640 → 712; road 18 L → 23 (21 L, 2 M). 133 → 134: nodes 714, sorry 67, OPEN 30, road 22. 134 → 135: nodes 716, OPEN 30 (all L), road 22 (all L). 135 → 136: sorry 65, OPEN 28, road 20 (all L). 136 → 137: nodes 717 (narrowings only). 137 → 138: skWin/TopCont → skFixCont, skWin/TopCapVF and skBCCapVH → skFixCapVF (same statements over one range): sorry 62, road 17; skLayPastX REFUTED (Zu.zuLayPastX_false) → skLayPastXθ, skLayPastTh: sorry 63, road 18. 170 → 174: skTopLawAll PROVED (Kx.kxTopLawAll): sorry 62, OPEN 25, road 17. 175 → 176: skPsi3OffRest2 PROVED (Ky.kyPsi3OffRest2): sorry 61, OPEN 24, road 16. 177 → 182: skAtHi3 PROVED (Kz.kzAtHi3): sorry 60, OPEN 23, road 15.
## REFUTED and SUSPECT
- **skLaySys_false REFUTED S** (`Yc.ycVD_empty`): `Xk.XkVD k` is empty for 1 ≤ k ≤ G. **skFixReadX_false REFUTED S** (130,
  `Yw.ywFirstFix_ref`): the least Γ-fixed point above x is ϑˣ(Ω₁·Ω₁+Ω₁). Both off road.
- **skFormHighX REFUTED L** (`Xj.xjFormHighX_fail`): no form with constant ϑ-levels ends in X′. **skTopFam, skTopDyn
  REFUTED M** (`Xi.xiTopFam_false`): no single image X̂ fits all cases. **skX0Law REFUTED L** (`Xd.xdX0Law_false`):
  outside D, T gives 0. **skShapeNat_false REFUTED S**. All off the road and replaced.
- **skShift4 REFUTED L** (132, `Zf.zfShift4_vac`): the level-0 node ϑ^{υ_{λ+1}}(Ω₁·0+1) is never good. Off road.
- **skRealB SUSPECT L**: `Ww.WwCarry` gives no bound for ϑ-levels in [υ_λ, υ_{λ+h}). **skMidAssemble SUSPECT M**: replaced by skMidCF. Off road.
- **skLayPastX_false REFUTED S** (round 138, `Zu.zuLayPastX_false`; was a ROAD leaf): no atom system `Zb.ZbAS` passes
  `θ = ψ_{Ω₂}(Ω_ω)` (`Zu.zuV_le_th`), so the layer `c = θ` has none. Replaced by skLayPastXθ (c < θ), skLayPastTh (c ≥ θ).
- PROVED negations: round 127 `Yi.yiWinShort_ref`, `Yi.yiMShort_ref`, `Yg.ygVdK_notYb`; round 129 `Ys.ysShortX_ref`; 130 `Yw.ywNoGo_GqSt`;
  131 `Zb.zbGsCS_lt_BG`, `Zc.zcRsTerm_long_false`; 132 `Zf.zfNodesAll_false`; 133 `Zn.znSupInB_false`, `Zn.znRsTerm_false`, `Zo.zoReach0_ref`; 135 `Zs.zsBaseRs_lower`, `Zs.zsSup_false`.
## Suggested order of the next rounds
1. Supply: skLevImgHi4 (nested ϑ-nodes: `Zf.zfDCl` by recursion on term size), skZlCfg (past the φ-ladder; EQ; υ-fixed carry).
2. Region B, (C): skLayPastB2θ (B₂ ≤ c < θ; X ≤ c < B₂ PROVED, Qc.qc_past), skLayPastTh (skZbDirectX PROVED, round 215); skFix{Cont, CapVF}, skWin/Top{Big, InR}, skTopLwNo2; skBCBaseUL (big reading: Lemma RS with values past υ_{l₀+1}), skBC{InR, CapVH, RsSH}.
3. Reading: skAtHi3 PROVED (rounds 177–182, Kz: T_K below K = Γ_{Ω_ω+1}, the top law Kz.kzTop, the offset law Kz.kzOff and the band moves Kz.kzMoveA on D_K).
