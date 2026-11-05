# R₂^C skeleton: status (round 134)
Root `R2Skel.Root.skNuC (S : InaccSeq)` = the conclusion of `Xo.xoRoadH` (ν_C = L(ω+1), …). Round 129: the root applies
`Yq.yqRoadS` = `Xo.xoRoadH` with the bridge replaced by the shift `SkS.skShiftXo`; supply `SkS.skSupXo` (repaired `Xo.XoR`);
frontier `SkF.skFront` → hUH/hLH/hVH/hVt; reading `SkR.skWall`, `SkR.skThHi` → `SkE.skEQ` → hT/hF. Round 130: Root unchanged.
Round 131: `SkE.skEQ hRead hUH hLH hVt`. Round 132: `SkE.skEQ hRead hW hUH hLH hVt`, `hW = SkR.skWallCF S` (the code-free
wall, used by `SkE.skTopK`). Round 133: Root unchanged; the bundle checks against the main build with only `declaration uses sorry` (68).
## Main progress number: OPEN / SUSPECT leaves on the road from `Root.skNuC`
**23 distinct OPEN leaves (L 21, M 2); 0 SUSPECT; 0 REFUTED** (round 133: 23; round 132: 18 L; round 131: 18; round 130: 19 OPEN L; round 129: 19;
rounds 127, 128: 17). Counted by a Lean walk over the constants used by `skNuC`. On the road: SkF skZbDirectX, skLayPastX,
skBC{BaseUV M, ThPos M, InR, CapVH, RsS}, skWin/Top{InR, IsoCode, Cont, Big, CapVF}, skTopLwNo2; SkR skTopLawAll, skPsi3OffRest2;
SkE skAtHi3; SkS skZlCfg, skLevImgHi4. Round 130: skWin/TopSpec → skWinIn, skTopIn, skTopLwNo2; skGapRng → skGapRngHi. Round 131:
skJumpNoRng, skGapRngHi PROVED (hVt); skLay{Lo,Hi}Fix → skZbDirect, skLay{Lo,Hi}FixX; skWin/TopIn, skWin/TopRsIn → skWin/TopInR,
skWin/TopRsT. Round 132: skWin/TopRsT, skWin/TopCapV → skWin/TopRsS, skWin/TopCapVL; skTopK → skTopG; skShift2 → skLevImgHi2.
Round 133 (narrower leaves, 18 → 23): skZbDirect → skZbDirectX; skLay{Lo,Hi}FixX → skLayPastX; skBhiAfar, skBhiL, skLongPre → 5
skBC* leaves; skWin/TopRsS, skWin/TopCapVL → skWin/Top{IsoCode, Cont, Big, CapVF}; skWallBase, skWallStep → skTopLawAll,
skPsi3OffRest2; skTopG → skAtHi3; skSupKXo → skZlCfg; skLevImgHi2 → skLevImgHi4. Round 134: skBCReach → skBCThPos (Zr).

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
│ │ │   round 133: skZbDirect ─ skZbDirectX OPEN L (no hypothesis below ζ_{B_Γ+1}, Zm.zmDirectZ); skLay{Lo,Hi}FixX ─
│ │ │     skLayPastX OPEN L (Zm.zmLay_of_past); 7 Zm PROVED. PROVED: skLayBelowBG L (129), skLayDirect0 M (127); 130 skFixImg …
│ │ │   off the road: skLaySysY REDUCED L ─ skLaySysAll1, skLaySysYHi OPEN L; skLaySys_false, skFixReadX_false REFUTED S
│ │ ├ skRegBhi REDUCED L: skBhiA REDUCED L ─ skBhiAcell PROVED M, skBhiAfar;  skBhiL  (round 133: both PROVED from skBC)
│ │ ├ skWinA, skWinB ─ skWinL REDUCED L ─ skWinUL PROVED S, skWinSpec ─ skWinInR OPEN L
│ │ │   round 131 (Zc.zcWins2): skWinBase, skRsLongNoGo, skRsLongLower, skGivenOfUp, skWinInRVac PROVED
│ │ │   round 132 (Zh.zhWins6): skWinRsT, skWinCapV REPLACED by skWinRsS, skWinCapVL (υ-fixed restarts only)
│ │ │   round 133 (Zn.znWins): REPLACED by skWinRsF REDUCED L ─ skWin{IsoCode, Cont, Big, CapVF} OPEN L; PROVED 12 Zn; 129 skWinStep M, …
│ │ └ skTopA, skTopB ─ skTopL REDUCED L ─ skTopUL, skTopPair, skTopNu, skTopNoBase PROVED S; skTopRsF REDUCED L (133, Zn.znTopAll)
│ │     ─ skTop{IsoCode, Cont, Big, CapVF} OPEN L; skTopSpec REDUCED L (130 Yx.yxTopAll; 131 Zc.zcTopAll2) ─ skTopInR, skTopLwNo2 OPEN L
│ └ skRegC REDUCED L    skLongPre (round 133: PROVED from skBC); skLongMid, skLongTop PROVED S (vacuous); skBelowL0 REDUCED S
│     round 133: skBC REDUCED L (Zo.zoBC, one block induction on [l₀, ι(Ω_ω))) ─ skBC{BaseUV, Reach} OPEN M, skBC{InR, CapVH, RsS} OPEN L; round 134: skBCReach REDUCED (Zr) ─ skBCThPos OPEN M
├ SkR.skWall REDUCED L ─ skWallCF ─ skWallLow REDUCED L   (round 132: skWallCF also feeds SkE.skEQ as hW)
│ │ skWallLevAll REDUCED L: skWallBase, skWallStep REDUCED L (round 133, Zp.zpWall, Zp.zpDecomp) ─ skTopLawAll OPEN L
│ │   (Θ(ψ₂ b) = ψ₁(A + 1 + ψ₂(T b)), normal Ω₃-divisible b ≥ Ω₃), skPsi3OffRest2 OPEN L (now on the road); skTopUp PROVED L
│ │   off the road: skPsi3Off REDUCED L (round 130) ─ skPsi3OffLow PROVED, skPsi3OffHi OPEN L (bases a ≥ Ω₃);
│ │     round 131 skPsi3OffD REDUCED L (Ω₃-divisible bases) ─ skPsi3OffE0 PROVED M, skPsi3OffRest REDUCED L (round 132:
│ │     below W^{Y₃+Ω₂·Ω₂·K₃}, Zi.ziPsi3OffWK; law up to ξ < ψ₁(0), Zi.ziChain) ─ skPsi3OffRest2
│ └ skWallTh PROVED M
├ SkR.skThHi REDUCED L: skThMid, skThFar REDUCED M (skWallCF, skTopK); off the road skMidAssemble SUSPECT M, skTopDyn …
├ SkE.skEQ REDUCED L  (round 131: takes hVt, passed through 12 nodes; round 132: takes hW, passed through 8 nodes)
│ ├ skThLow PROVED S;  └ skEQfar REDUCED L ─ skThFar ─ skTopK REDUCED S (round 132, Zj.zjTopK_ofG; shared with SkR)
│ │   ─ skTopG REDUCED L (round 133, Zq.zqTopG3; atoms move up to K_Y, Zq.zqAtK_Y) ─ skAtHi3 OPEN L (K_Y < s < P′); 8 PROVED
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
## Counts (713 nodes)
| part | PROVED | REDUCED | OPEN | SUSPECT | REFUTED | REPLACED | S | M | L |
|---|---|---|---|---|---|---|---|---|---|
| SkF | 248 | 44 | 21 | 0 | 3 | 39 | 153 | 81 | 121 |
| SkR | 90 | 15 | 3 | 1 | 3 | 0 | 44 | 47 | 21 |
| SkE | 91 | 16 | 1 | 0 | 0 | 0 | 102 | 0 | 6 |
| SkS | 90 | 38 | 6 | 1 | 2 | 0 | 59 | 29 | 49 |
| Root | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 1 |
| all | 519 | 114 | 31 | 2 | 8 | 39 | 358 | 157 | 198 |

OPEN by size: L 29 (SkF 19, SkR 3, SkE 1, SkS 6), M 2 (SkF skBCBaseUV, skBCThPos), S 0. Off the road (8): skA3T0Start, skLaySysAll1,
skLaySysYHi, skPsi3OffHi, skYbIFHuge, skSupKW, skImgEps, skCarryHigh. SUSPECT: skMidAssemble M, skRealB L.
REFUTED: S 3, M 2, L 3. Sorry leaves (68): OPEN 31; SUSPECT 2; REFUTED skTopDyn, skTopFam, skX0Law, skFormHighX, skShift4
(record); REPLACED 30. Round 130 → 131: sorry 52 → 57, SUSPECT 2 → 3, nodes 549 → 588; road 19 → 18 OPEN L. Round 131 → 132:
sorry 57 → 60, OPEN 28 (27 L, 1 S) → 27 (all L), SUSPECT 3 → 2, REFUTED 7 → 8, nodes 588 → 640; road 18 → 18 OPEN L. Round
132 → 133: sorry 60 → 68, OPEN 27 (all L) → 31 (29 L, 2 M), nodes 640 → 712; road 18 L → 23 (21 L, 2 M). 133 → 134: nodes 713, road 23.
## REFUTED and SUSPECT
- **skLaySys_false REFUTED S** (`Yc.ycVD_empty`): `Xk.XkVD k` is empty for 1 ≤ k ≤ G (hull fields ask Cl(1, b) < Γ(1)). Off road.
- **skFixReadX_false REFUTED S** (round 130, `Yw.ywFirstFix_ref`): the least Γ-fixed point above x is ϑˣ(Ω₁·Ω₁+Ω₁). Off road.
- **skFormHighX REFUTED L** (`Xj.xjFormHighX_fail`): no form with constant ϑ-levels ends in X′. **skTopFam, skTopDyn
  REFUTED M** (`Xi.xiTopFam_false`): no single image X̂ fits all cases. **skX0Law REFUTED L** (`Xd.xdX0Law_false`):
  outside D, T gives 0. **skShapeNat_false REFUTED S**. All off the road and replaced.
- **skShift4 REFUTED L** (round 132, `Zf.zfShift4_vac`; 131 SUSPECT): the level-0 node ϑ^{υ_{λ+1}}(Ω₁·0+1) is never good,
  so `Za.ZaShift4 S` contradicts the shift's hypotheses at every β ≥ 2 (a refutation if they are satisfiable). Off road.
- **skRealB SUSPECT L**: `Ww.WwCarry` gives no bound for ϑ-levels with data in [υ_λ, υ_{λ+h}). **skMidAssemble SUSPECT M**:
  its hypothesis covers only F_W ≤ m_λ < θ⁺; replaced by skMidCF. Both off the road.
- PROVED negations: round 127 `Yi.yiWinShort_ref`, `Yi.yiMShort_ref`, `Yg.ygVdK_notYb`; round 129 `Ys.ysShortX_ref`; 130 `Yw.ywNoGo_GqSt`;
  131 `Zb.zbGsCS_lt_BG`, `Zc.zcRsTerm_long_false`; 132 `Zf.zfNodesAll_false`; 133 `Zn.znSupInB_false`, `Zn.znRsTerm_false`, `Zo.zoReach0_ref`.
## Suggested order of the next rounds
1. Supply: skLevImgHi4 (nested ϑ-nodes: `Zf.zfDCl` by recursion on term size), skZlCfg (past the φ-ladder; EQ; υ-fixed carry).
2. Region B, (C): skZbDirectX (level-generic `Zm.ZmGood2`), skLayPastX; skWin/Top{IsoCode, Cont, Big, CapVF, InR}, skTopLwNo2; skBC*.
3. Reading: skAtHi3 (a level system over Ω_ω past Y₃), skTopLawAll (induction on the exponent E of b = β + W^E·γ), skPsi3OffRest2.
