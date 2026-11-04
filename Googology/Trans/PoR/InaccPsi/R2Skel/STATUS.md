# R₂^C skeleton: status (round 131)

Root `R2Skel.Root.skNuC (S : InaccSeq)` = the conclusion of `Xo.xoRoadH` (ν_C = L(ω+1), …). Round 129: the root applies
`Yq.yqRoadS` = `Xo.xoRoadH` with the bridge replaced by the shift `SkS.skShiftXo` (`Xo.XoShift S`); supply `SkS.skSupXo`
(repaired `Xo.XoR`); frontier `SkF.skFront` → hUH/hLH/hVH/hVt; reading `SkR.skWall`, `SkR.skThHi` → `SkE.skEQ hRead hUH hLH`
→ hT/hF. Round 130: Root unchanged. Round 131: `SkE.skEQ hRead hUH hLH hVt` (`SkF.skFrontVt`, already used by `Yq.yqRoadS`);
the bundle checks against the main build with only `declaration uses sorry` (57).

## Main progress number: OPEN / SUSPECT leaves on the road from `Root.skNuC`

**18 distinct OPEN leaves, all L; 0 SUSPECT; 0 REFUTED** (round 130: 19 OPEN L; round 129: 19; rounds 127, 128: 17). Counted
by a Lean walk over the constants used by `skNuC`. On the road: SkF skZbDirect, skLayLoFixX, skLayHiFixX, skBhiAfar, skBhiL,
skWinInR, skWinRsT, skWinCapV, skTopInR, skTopLwNo2, skTopRsT, skTopCapV, skLongPre; SkR skWallBase, skWallStep; SkE skTopK;
SkS skSupKXo, skShift2. Round 130: skWin/TopSpec → skWinIn, skTopIn, skTopLwNo2; skGapRng → skGapRngHi. Round 131: skJumpNoRng,
skGapRngHi PROVED (hVt); skLay{Lo,Hi}Fix → skZbDirect, skLay{Lo,Hi}FixX; skWin/TopIn, skWin/TopRsIn → skWin/TopInR, skWin/TopRsT.

**Vacuity: open.** No REFUTED or SUSPECT leaf on the road; `Xo.XoSup`, `Yq.XoThCl` (behind skShift2) not shown satisfiable.

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
│ │ │   PROVED: skLayBelowBG L (round 129), skLayDirect0 M (round 127); round 130 skFixImg L, skFixKind, skFixLayBG M, skFixNoGo S
│ │ │   off the road: skLaySysY REDUCED L ─ skLaySysAll1, skLaySysYHi OPEN L; skLaySys_false, skFixReadX_false REFUTED S
│ │ ├ skRegBhi REDUCED L: skBhiA REDUCED L ─ skBhiAcell PROVED M, skBhiAfar OPEN L;  skBhiL OPEN L
│ │ ├ skWinA, skWinB ─ skWinL REDUCED L ─ skWinUL PROVED S, skWinRsT, skWinCapV OPEN L, skWinSpec ─ skWinInR OPEN L
│ │ │   round 131 (Zc.zcWins2): skWinBase, skRsLongNoGo, skRsLongLower, skGivenOfUp, skWinInRVac PROVED
│ │ │   PROVED: round 129 skWinStep M, skWinInd M, skWinSpecOld, skWinShortX, skRsInCongr S; round 127 skWinCross S, …
│ │ └ skTopA, skTopB ─ skTopL REDUCED L ─ skTopUL, skTopPair, skTopNu, skTopNoBase PROVED S; skTopRsT, skTopCapV OPEN L,
│ │     skTopSpec REDUCED L (round 130, Yx.yxTopAll; round 131 Zc.zcTopAll2) ─ skTopInR, skTopLwNo2 OPEN L
│ └ skRegC REDUCED L    skLongPre OPEN L; skLongMid, skLongTop PROVED S (vacuous); skBelowL0 REDUCED S (round 130)
├ SkR.skWall REDUCED L ─ skWallCF ─ skWallLow REDUCED L
│ │ skWallLevAll REDUCED L: skWallBase OPEN L, skWallStep OPEN L; skTopUp PROVED L
│ │   PROVED: round 131 top law past Ω₂ (Zd.zdChain), top atoms move (Zd.zdTopMove), skPsi3OffE0, +4 M; round 130 Yy, …
│ │   off the road: skPsi3Off REDUCED L (round 130) ─ skPsi3OffLow PROVED, skPsi3OffHi OPEN L (bases a ≥ Ω₃);
│ │     round 131 skPsi3OffD REDUCED L (Ω₃-divisible bases) ─ skPsi3OffE0 PROVED M, skPsi3OffRest OPEN L
│ └ skWallTh PROVED M
├ SkR.skThHi REDUCED L: skThMid, skThFar REDUCED M (skWallCF, skTopK); off the road skMidAssemble SUSPECT M, skTopDyn …
├ SkE.skEQ REDUCED L  (round 131: takes hVt, passed through 12 nodes)
│ ├ skThLow PROVED S;  └ skEQfar REDUCED L ─ skThFar ─ skTopK OPEN L (shared with SkR; the only open leaf of SkE)
│     skKFar ─ skKCof ─ skKCofGap REDUCED S ─ skGapLh REDUCED S (round 130: takes hUH, hLH)
│       ├ skGapEps REDUCED S ─ skGapEpsIff PROVED S (+5 PROVED S), skGapEpsTop PROVED S (round 130, cites [W07b] Lemma 4.2)
│       ├ skGapRng REDUCED S (round 130, codes ≤ θ·ω done) ─ skGapRngHi PROVED S (round 131, Ze.zeGapRngHi, from hVt)
│       └ skGapBlk PROVED S (Yk.ykGapBlk, no hypothesis)
│     skKReachR ─ skEQTopR REDUCED L ─ skEQJump REDUCED S ─ skJumpOff PROVED S (vacuous),
│         skJumpNoRng PROVED S (round 131, Ze.zeJumpNoRng; short codes with no hypothesis, skJumpShortU; long from hVt)
├ SkS.skShiftXo REDUCED M ─ skShift2 OPEN L (ϑ-node clause Yq.XoThCl for the FRAG map, on top of Xb.XbShift)
│   round 130 PROVED (leaf substitution below θ): 8 nodes skYv*; skYvCl REDUCED L (round 131, Za.za_yvCl, off the road)
│   round 131 off the road: skDlSC OPEN S (Dl τ n strongly critical, cite [W07a]) ─ skZaFrag, skZaShift3 REDUCED L;
│     skShift4 SUSPECT L ─ skShift2_of4 PROVED S (ZaShift4 ⇒ XoShift2); skZaLevConst, skZaWitMv, skZaWitPhi PROVED S
└ SkS.skSupXo REDUCED L ─ skVisKXo REDUCED S ─ skGenXo REDUCED S
    ├ skUp REDUCED S ─ skUpRR REDUCED L (from SkF);  skFormXo PROVED S;  └ skSupKXo OPEN L (carry with the repaired XoR)
    off the road: skRealBXo REDUCED L; skYbIF REDUCED L ─ skYbIFTh REDUCED L ─ skYbIFNot PROVED M, skYbIFHuge OPEN L;
      skShiftTh PROVED L, skFormHighX REFUTED L, skSupKW, skImgEps, skCarryHigh OPEN L, skRealB SUSPECT L
```

## Counts (588 nodes)

| part | PROVED | REDUCED | OPEN | SUSPECT | REFUTED | REPLACED | S | M | L |
|---|---|---|---|---|---|---|---|---|---|
| SkF | 200 | 36 | 16 | 0 | 3 | 31 | 122 | 74 | 90 |
| SkR | 76 | 11 | 4 | 1 | 3 | 0 | 38 | 39 | 18 |
| SkE | 77 | 14 | 1 | 0 | 0 | 0 | 86 | 0 | 6 |
| SkS | 69 | 35 | 7 | 2 | 1 | 0 | 45 | 26 | 43 |
| Root | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 1 |
| all | 422 | 97 | 28 | 3 | 7 | 31 | 291 | 139 | 158 |

OPEN by size: L 27 (SkF 16, SkR 4, SkE 1, SkS 6), M 0, S 1 (skDlSC). Off the road (10): skA3T0Start, skLaySysAll1, skLaySysYHi,
skPsi3OffHi, skPsi3OffRest, skYbIFHuge, skSupKW, skImgEps, skCarryHigh, skDlSC. SUSPECT: skMidAssemble M, skRealB L, skShift4 L.
REFUTED: S 3, M 2, L 2. Sorry leaves (57): OPEN 28; SUSPECT 3; REFUTED skTopDyn, skTopFam, skX0Law, skFormHighX (record);
REPLACED 22. Round 129 → 130: sorry 51 → 52, OPEN 27 → 28 (L), REFUTED 6 → 7, nodes 511 → 549. Round 130 → 131: sorry
52 → 57, OPEN 28 (L) → 28 (27 L, 1 S), SUSPECT 2 → 3, REFUTED 7, nodes 549 → 588; road 19 → 18 OPEN L.

## REFUTED and SUSPECT

- **skLaySys_false REFUTED S** (`Yc.ycVD_empty`): `Xk.XkVD k` is empty for 1 ≤ k ≤ G (hull fields ask Cl(1, b) < Γ(1)). Off road.
- **skFixReadX_false REFUTED S** (round 130, `Yw.ywFirstFix_ref`): the least Γ-fixed point above x is ϑˣ(Ω₁·Ω₁+Ω₁). Off road.
- **skFormHighX REFUTED L** (`Xj.xjFormHighX_fail`): no form with constant ϑ-levels ends in X′. **skTopFam, skTopDyn
  REFUTED M** (`Xi.xiTopFam_false`): no single image X̂ fits all cases. **skX0Law REFUTED L** (`Xd.xdX0Law_false`):
  outside D, T gives 0. **skShapeNat_false REFUTED S**. All off the road and replaced.
- **skRealB SUSPECT L**: `Ww.WwCarry` gives no bound for ϑ-levels with data in [υ_λ, υ_{λ+h}). **skMidAssemble SUSPECT M**:
  its hypothesis covers only F_W ≤ m_λ < θ⁺; replaced by skMidCF. Both off the road.
- **skShift4 SUSPECT L** (round 131): `Za.ZaShift4` asks the leaves of a level value to be configuration points, but the
  level (Ω₁+a)+b has the leaf a+b, which a configuration need not contain. Off the road (skShift2 is not reduced to it).
- PROVED negations: round 127 `Yi.yiWinShort_ref`, `Yi.yiMShort_ref`, `Yg.ygVdK_notYb`; round 129 `Ys.ysShortX_ref`; 130
  `Yw.ywNoGo_GqSt`; 131 `Zb.zbGsCS_lt_BG` (no `Gs.GsCS` passes B_Γ), `Zc.zcRsTerm_long_false` (term input, supply restarts).

## Suggested order of the next rounds

1. Supply: skShift2 (finite leaf sets; leaves in T^{υ_{λ+h}}; level image Ω₁·img L via a φ ↔ ϑ link), skDlSC, skSupKXo.
2. Region B: skZbDirect (TlCl membership below B_Γ, offsets with the atom B_Γ, kinds β ≥ 1), skLayLoFixX / skLayHiFixX;
   skWin/TopRsT, skWin/TopInR, skWin/TopCapV, skTopLwNo2; skBhiAfar, skBhiL, skLongPre.
3. Reading: skPsi3OffRest (Y₃ + Ω₂·ξ, ξ ≥ ε₀; Y₃ + Ω₂²), top laws past Ω_{k+3} + Ω₂·ε₀, assembly into skWallBase, skWallStep; skTopK.
