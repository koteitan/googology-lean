# R₂^C skeleton: status (round 132)

Root `R2Skel.Root.skNuC (S : InaccSeq)` = the conclusion of `Xo.xoRoadH` (ν_C = L(ω+1), …). Round 129: the root applies
`Yq.yqRoadS` = `Xo.xoRoadH` with the bridge replaced by the shift `SkS.skShiftXo`; supply `SkS.skSupXo` (repaired `Xo.XoR`);
frontier `SkF.skFront` → hUH/hLH/hVH/hVt; reading `SkR.skWall`, `SkR.skThHi` → `SkE.skEQ` → hT/hF. Round 130: Root unchanged.
Round 131: `SkE.skEQ hRead hUH hLH hVt`. Round 132: `SkE.skEQ hRead hW hUH hLH hVt`, `hW = SkR.skWallCF S` (the code-free
wall, used by `SkE.skTopK`); the bundle checks against the main build with only `declaration uses sorry` (60).

## Main progress number: OPEN / SUSPECT leaves on the road from `Root.skNuC`
**18 distinct OPEN leaves, all L; 0 SUSPECT; 0 REFUTED** (round 131: 18; round 130: 19 OPEN L; round 129: 19; rounds 127,
128: 17). Counted by a Lean walk over the constants used by `skNuC`. On the road: SkF skZbDirect, skLayLoFixX, skLayHiFixX,
skBhiAfar, skBhiL, skWinInR, skWinRsS, skWinCapVL, skTopInR, skTopLwNo2, skTopRsS, skTopCapVL, skLongPre; SkR skWallBase,
skWallStep; SkE skTopG; SkS skSupKXo, skLevImgHi2. Round 130: skWin/TopSpec → skWinIn, skTopIn, skTopLwNo2; skGapRng →
skGapRngHi. Round 131: skJumpNoRng, skGapRngHi PROVED (hVt); skLay{Lo,Hi}Fix → skZbDirect, skLay{Lo,Hi}FixX; skWin/TopIn,
skWin/TopRsIn → skWin/TopInR, skWin/TopRsT. Round 132: skWin/TopRsT, skWin/TopCapV → skWin/TopRsS, skWin/TopCapVL (υ-fixed
window restarts only); skTopK → skTopG (with the wall hW); skShift2 → skLevImgHi2.

**Vacuity of `Root.skNuC`: open.** No REFUTED or SUSPECT leaf on the road; `Xo.XoSup` and `Zf.ZfImgP2` (skLevImgHi2) are
not shown satisfiable.
## Node tree (STATUS SIZE)
```
skNuC REDUCED L  (Yq.yqRoadS)
├ SkF.skFront REDUCED L ─ skAbove REDUCED L
│ ├ skRegA: REGION A CLOSED (skSysCof, skSysA3, skSysA3StepW PROVED L); off the road skA3T0Start OPEN L
│ ├ skRegB REDUCED L  (cells: base β ∈ {0, Ω₂·q, b_k, b_ω} + offset ζ < Ω₂)
│ │ ├ skRegBlo ─ skLay REDUCED L
│ │ │   skLayLo REDUCED L: skLayLoD (c+1 < ε₀) PROVED, skLayLoBig REDUCED L ─ skLayBelowBG, skLayLoFix REDUCED L
│ │ │   skLayHi REDUCED L: skLayDirect PROVED L, skLayHiBig REDUCED L ─ skLayBelowBG, skLayHiFix REDUCED L
│ │ │   round 131: ─ skZbDirect OPEN L (B_Γ ≤ c < X), skLayLoFixX, skLayHiFixX OPEN L (X ≤ c < Ω₂); skZbDirectE0 +3 PROVED
│ │ │   round 132: skZbDirect holds below B_Γ·B_Γ with no hypothesis (skZgDirectSq); skZgTl, skZgRef +3 PROVED
│ │ │   PROVED: skLayBelowBG L (round 129), skLayDirect0 M (round 127); round 130 skFixImg L, skFixKind, skFixLayBG M, skFixNoGo S
│ │ │   off the road: skLaySysY REDUCED L ─ skLaySysAll1, skLaySysYHi OPEN L; skLaySys_false, skFixReadX_false REFUTED S
│ │ ├ skRegBhi REDUCED L: skBhiA REDUCED L ─ skBhiAcell PROVED M, skBhiAfar OPEN L;  skBhiL OPEN L
│ │ ├ skWinA, skWinB ─ skWinL REDUCED L ─ skWinUL PROVED S, skWinSpec ─ skWinInR OPEN L; skWinRsS, skWinCapVL OPEN L
│ │ │   round 131 (Zc.zcWins2): skWinBase, skRsLongNoGo, skRsLongLower, skGivenOfUp, skWinInRVac PROVED
│ │ │   round 132 (Zh.zhWins6): skWinRsT, skWinCapV REPLACED by skWinRsS, skWinCapVL (υ-fixed restarts only)
│ │ │   PROVED: round 129 skWinStep M, skWinInd M, skWinSpecOld, skWinShortX, skRsInCongr S; round 127 skWinCross S, …
│ │ └ skTopA, skTopB ─ skTopL REDUCED L ─ skTopUL, skTopPair, skTopNu, skTopNoBase PROVED S; skTopRsS, skTopCapVL OPEN L
│ │     (round 132, Zh.zhTopAll6, replace skTopRsT, skTopCapV; 14 Zh nodes PROVED); skTopSpec REDUCED L (round 130,
│ │     Yx.yxTopAll; round 131 Zc.zcTopAll2) ─ skTopInR, skTopLwNo2 OPEN L
│ └ skRegC REDUCED L    skLongPre OPEN L; skLongMid, skLongTop PROVED S (vacuous); skBelowL0 REDUCED S (round 130)
├ SkR.skWall REDUCED L ─ skWallCF ─ skWallLow REDUCED L   (round 132: skWallCF also feeds SkE.skEQ as hW)
│ │ skWallLevAll REDUCED L: skWallBase OPEN L, skWallStep OPEN L; skTopUp PROVED L
│ │   PROVED: round 131 top law past Ω₂ (Zd.zdChain), top atoms move (Zd.zdTopMove), skPsi3OffE0, +4 M; round 130 Yy, …
│ │   off the road: skPsi3Off REDUCED L (round 130) ─ skPsi3OffLow PROVED, skPsi3OffHi OPEN L (bases a ≥ Ω₃);
│ │     round 131 skPsi3OffD REDUCED L (Ω₃-divisible bases) ─ skPsi3OffE0 PROVED M, skPsi3OffRest REDUCED L (round 132:
│ │     below W^{Y₃+Ω₂·Ω₂·K₃}, Zi.ziPsi3OffWK; law up to ξ < ψ₁(0), Zi.ziChain) ─ skPsi3OffRest2 OPEN L
│ └ skWallTh PROVED M
├ SkR.skThHi REDUCED L: skThMid, skThFar REDUCED M (skWallCF, skTopK); off the road skMidAssemble SUSPECT M, skTopDyn …
├ SkE.skEQ REDUCED L  (round 131: takes hVt, passed through 12 nodes; round 132: takes hW, passed through 8 nodes)
│ ├ skThLow PROVED S;  └ skEQfar REDUCED L ─ skThFar ─ skTopK REDUCED S (round 132, Zj.zjTopK_ofG; shared with SkR)
│ │   ─ skTopG OPEN L (codes ≥ ψ_{Ω₂}(Ω_ω + Ω₂^{Ω₂^{Ω₂}}); the only open leaf of SkE); 7 new nodes PROVED
│     skKFar ─ skKCof ─ skKCofGap REDUCED S ─ skGapLh REDUCED S (round 130: takes hUH, hLH)
│       ├ skGapEps REDUCED S ─ skGapEpsIff PROVED S (+5 PROVED S), skGapEpsTop PROVED S (round 130, cites [W07b] Lemma 4.2)
│       ├ skGapRng REDUCED S (round 130, codes ≤ θ·ω done) ─ skGapRngHi PROVED S (round 131, Ze.zeGapRngHi, from hVt)
│       └ skGapBlk PROVED S (Yk.ykGapBlk, no hypothesis)
│     skKReachR ─ skEQTopR REDUCED L ─ skEQJump REDUCED S ─ skJumpOff PROVED S (vacuous),
│         skJumpNoRng PROVED S (round 131, Ze.zeJumpNoRng; short codes with no hypothesis, skJumpShortU; long from hVt)
├ SkS.skShiftXo REDUCED M ─ skShift2 REDUCED L (round 132, Zf.zfShift2) ─ skLevImg, skLevImgHi REDUCED L
│   ─ skLevImgHi2 OPEN L (level image at levels mixing two segments, nested ϑ-nodes, Ω_· or ψ); 8 new Zf nodes PROVED
│   round 130 PROVED (leaf substitution below θ): 8 nodes skYv*; skYvCl PROVED L (round 132, was REDUCED, off the road)
│   round 131 off the road: skDlSC PROVED S (round 132, cited axiom R2.zfDl_vt, [W07a] L. 3.27) → skZaFrag, skZaShift3 PROVED
│     L; skShift4 REFUTED L (132) ─ skShift2_of4 PROVED S; skZaLevConst, skZaWitMv, skZaWitPhi PROVED S
└ SkS.skSupXo REDUCED L ─ skVisKXo REDUCED S ─ skGenXo REDUCED S
    ├ skUp REDUCED S ─ skUpRR REDUCED L (from SkF);  skFormXo PROVED S;  └ skSupKXo OPEN L (carry with the repaired XoR)
    off the road: skRealBXo REDUCED L; skYbIF REDUCED L ─ skYbIFTh REDUCED L ─ skYbIFNot PROVED M, skYbIFHuge OPEN L;
      skShiftTh PROVED L, skFormHighX REFUTED L, skSupKW, skImgEps, skCarryHigh OPEN L, skRealB SUSPECT L
```
## Counts (640 nodes)
| part | PROVED | REDUCED | OPEN | SUSPECT | REFUTED | REPLACED | S | M | L |
|---|---|---|---|---|---|---|---|---|---|
| SkF | 220 | 36 | 16 | 0 | 3 | 35 | 136 | 75 | 99 |
| SkR | 84 | 12 | 4 | 1 | 3 | 0 | 40 | 45 | 19 |
| SkE | 84 | 15 | 1 | 0 | 0 | 0 | 94 | 0 | 6 |
| SkS | 81 | 35 | 6 | 1 | 2 | 0 | 53 | 26 | 46 |
| Root | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 1 |
| all | 469 | 99 | 27 | 2 | 8 | 35 | 323 | 146 | 171 |

OPEN by size: L 27 (SkF 16, SkR 4, SkE 1, SkS 6), M 0, S 0. Off the road (9): skA3T0Start, skLaySysAll1, skLaySysYHi,
skPsi3OffHi, skPsi3OffRest2, skYbIFHuge, skSupKW, skImgEps, skCarryHigh. SUSPECT: skMidAssemble M, skRealB L.
REFUTED: S 3, M 2, L 3. Sorry leaves (60): OPEN 27; SUSPECT 2; REFUTED skTopDyn, skTopFam, skX0Law, skFormHighX, skShift4
(record); REPLACED 26. Round 130 → 131: sorry 52 → 57, SUSPECT 2 → 3, nodes 549 → 588; road 19 → 18 OPEN L. Round 131 → 132:
sorry 57 → 60, OPEN 28 (27 L, 1 S) → 27 (all L), SUSPECT 3 → 2, REFUTED 7 → 8, nodes 588 → 640; road 18 → 18 OPEN L.
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
- PROVED negations: round 127 `Yi.yiWinShort_ref`, `Yi.yiMShort_ref`, `Yg.ygVdK_notYb`; round 129 `Ys.ysShortX_ref`; 130
  `Yw.ywNoGo_GqSt`; 131 `Zb.zbGsCS_lt_BG`, `Zc.zcRsTerm_long_false`; 132 `Zf.zfNodesAll_false`.
## Suggested order of the next rounds
1. Supply: skLevImgHi2 (FRAG hull isomorphism on level terms, multi-base `Zf.zf_pi_mulG`; non-vacuity), skSupKXo.
2. Region B: skZbDirect (offsets B_Γ^k·q + r, codes up to ε_{B_Γ+1}, φ-codes below Γ_{B_Γ+1}, kinds β ≥ 1), skLay{Lo,Hi}FixX;
   skWin/TopRsS (supply `Zh.ZhSupB` at υ-fixed restarts), skWin/TopCapVL, skWin/TopInR, skTopLwNo2; skBhiAfar, skBhiL, skLongPre.
3. Reading: skTopG (`Sn.snCL_atom` for atoms θ ≤ s < P′ over Ω_ω), skWallBase, skWallStep (WallBelow); skPsi3OffRest2.
