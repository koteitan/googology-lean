# R₂^C skeleton: status (round 130)

Root `R2Skel.Root.skNuC (S : InaccSeq)` = the conclusion of `Xo.xoRoadH` (ν_C = L(ω+1), …). Round 129: the root applies
`Yq.yqRoadS` = `Xo.xoRoadH` with the bridge replaced by the shift `SkS.skShiftXo` (`Xo.XoShift S`); supply `SkS.skSupXo`
(repaired `Xo.XoR`); frontier `SkF.skFront` → hUH/hLH/hVH/hVt; reading `SkR.skWall`, `SkR.skThHi` → `SkE.skEQ hRead hUH hLH`
→ hT/hF. Round 130: Root unchanged; the bundle checks against the main build with only `declaration uses sorry` (52).

## Main progress number: OPEN / SUSPECT leaves on the road from `Root.skNuC`

**19 distinct OPEN leaves, all L; 0 SUSPECT; 0 REFUTED** (round 129: 19 OPEN L; rounds 127, 128: 17). Counted by a Lean
walk over the constants used by `skNuC`. On the road: SkF skLayLoFix, skLayHiFix, skBhiAfar, skBhiL, skWinIn, skWinRsIn,
skWinCapV, skTopIn, skTopLwNo2, skTopRsIn, skTopCapV, skLongPre; SkR skWallBase, skWallStep; SkE skTopK, skGapRngHi,
skJumpNoRng; SkS skSupKXo, skShift2. Round 130: skWin/TopSpec → skWinIn, skTopIn, skTopLwNo2; skGapRng → skGapRngHi.

**Vacuity: open.** No REFUTED or SUSPECT leaf on the road; `Xo.XoSup`, `Yq.XoThCl` (behind skShift2) not shown satisfiable.

## Node tree (STATUS SIZE)

```
skNuC REDUCED L  (Yq.yqRoadS)
├ SkF.skFront REDUCED L ─ skAbove REDUCED L
│ ├ skRegA: REGION A CLOSED (skSysCof, skSysA3, skSysA3StepW PROVED L); off the road skA3T0Start OPEN L
│ ├ skRegB REDUCED L  (cells: base β ∈ {0, Ω₂·q, b_k, b_ω} + offset ζ < Ω₂)
│ │ ├ skRegBlo ─ skLay REDUCED L
│ │ │   skLayLo REDUCED L: skLayLoD (c+1 < ε₀) PROVED, skLayLoBig REDUCED L ─ skLayBelowBG, skLayLoFix OPEN L
│ │ │   skLayHi REDUCED L: skLayDirect PROVED L, skLayHiBig REDUCED L ─ skLayBelowBG, skLayHiFix OPEN L
│ │ │   PROVED: skLayBelowBG L (round 129, every layer c < B_Γ), skLayDirect0 M (round 127); round 130 skFixImg L,
│ │ │     skFixKind M, skFixLayBG M (layers B_Γ, B_Γ+1), skFixNoGo S
│ │ │   off the road: skLaySysY REDUCED L ─ skLaySysAll1, skLaySysYHi OPEN L; skLaySys_false, skFixReadX_false REFUTED S
│ │ ├ skRegBhi REDUCED L: skBhiA REDUCED L ─ skBhiAcell PROVED M, skBhiAfar OPEN L;  skBhiL OPEN L
│ │ ├ skWinA, skWinB ─ skWinL REDUCED L ─ skWinUL PROVED S, skWinRsIn, skWinCapV OPEN L, skWinSpec ─ skWinIn OPEN L
│ │ │   PROVED: round 129 skWinStep M, skWinInd M, skWinSpecOld S, skWinShortX S, skRsInCongr S;
│ │ │     round 127 skWinShortRef, skMShortRef, skWinCross S;  skWinNoBase S
│ │ └ skTopA, skTopB ─ skTopL REDUCED L ─ skTopUL, skTopPair, skTopNu, skTopNoBase PROVED S; skTopRsIn, skTopCapV OPEN L,
│ │     skTopSpec REDUCED L (round 130, Yx.yxTopAll; skWinSpec: Yx.yxWins) ─ skTopIn, skTopLwNo2 OPEN L
│ └ skRegC REDUCED L    skLongPre OPEN L; skLongMid, skLongTop PROVED S (vacuous); skBelowL0 REDUCED S (round 130)
├ SkR.skWall REDUCED L ─ skWallCF ─ skWallLow REDUCED L
│ │ skWallLevAll REDUCED L: skWallBase OPEN L, skWallStep OPEN L; skTopUp PROVED L
│ │   PROVED: round 130 law at X + Ω₂ (Yy.yyLawOm2), skRefTests130; round 129 skTopMoveY, skSubLawLim, skSubBaseLim,
│ │     skSubMoveY M, skRefTests S; round 127 skBaseFactsB, …
│ │   off the road: skPsi3Off REDUCED L (round 130) ─ skPsi3OffLow PROVED, skPsi3OffHi OPEN L (bases a ≥ Ω₃)
│ └ skWallTh PROVED M
├ SkR.skThHi REDUCED L: skThMid REDUCED M, skThFar REDUCED M (skWallCF, skTopK)
│   (side: skMidAssemble SUSPECT M, skTopDyn / skTopFam REFUTED M, skX0Law REFUTED L, all off the road)
├ SkE.skEQ REDUCED L
│ ├ skThLow PROVED S;  └ skEQfar REDUCED L
│     skThFar ─ skTopK OPEN L (shared with SkR)
│     skKFar ─ skKCof ─ skKCofGap REDUCED S ─ skGapLh REDUCED S (round 130: takes hUH, hLH)
│       ├ skGapEps REDUCED S ─ skGapEpsIff PROVED S (+5 PROVED S), skGapEpsTop PROVED S (round 130, cites [W07b] Lemma 4.2)
│       ├ skGapRng REDUCED S (round 130, codes ≤ θ·ω done) ─ skGapRngHi OPEN L (gap restarts with code > θ·ω)
│       └ skGapBlk PROVED S (Yk.ykGapBlk, no hypothesis)
│     skKReachR ─ skEQTopR REDUCED L ─ skEQJump REDUCED S
│       ├ skJumpOff PROVED S (vacuous)
│       └ skJumpNoRng OPEN L (round 130: split by the code of κ); round 127 PROVED: skChainLe1, skJumpGapBot, …
├ SkS.skShiftXo REDUCED M ─ skShift2 OPEN L (ϑ-node clause Yq.XoThCl for the FRAG map, on top of Xb.XbShift)
│   round 130 PROVED (leaf substitution below θ): 8 nodes skYv*; off the road skYvCl OPEN L (next step for skShift2)
└ SkS.skSupXo REDUCED L ─ skVisKXo REDUCED S ─ skGenXo REDUCED S
    ├ skUp REDUCED S ─ skUpRR REDUCED L (from SkF);  skFormXo PROVED S
    └ skSupKXo OPEN L (carry with the repaired XoR)
    off the road: skRealBXo REDUCED L ─ skRealBXoL REDUCED L; skYbIF REDUCED L ─ skYbIFLowB PROVED,
      skYbIFTh REDUCED L ─ skYbIFNot PROVED M (notation range, Yq.yqIFN), skYbIFHuge OPEN L (data above every ψ_{Ω₁});
      skCoverXoL, skSupNonSilentL, skLevKNot PROVED S; skShiftTh PROVED L, skSupX REDUCED,
      skFormHighX REFUTED L, skSupKW OPEN L, skRealB SUSPECT L, skImgEps OPEN L, skCarryHigh OPEN L
```

## Counts (549 nodes)

| part | PROVED | REDUCED | OPEN | SUSPECT | REFUTED | REPLACED | S | M | L |
|---|---|---|---|---|---|---|---|---|---|
| SkF | 191 | 34 | 15 | 0 | 3 | 27 | 115 | 74 | 81 |
| SkR | 69 | 10 | 3 | 1 | 3 | 0 | 37 | 33 | 16 |
| SkE | 69 | 14 | 3 | 0 | 0 | 0 | 78 | 0 | 8 |
| SkS | 65 | 32 | 7 | 1 | 1 | 0 | 40 | 26 | 40 |
| Root | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 1 |
| all | 394 | 91 | 28 | 2 | 7 | 27 | 270 | 133 | 146 |

OPEN by size: L 28 (SkF 15, SkR 3, SkE 3, SkS 7), M 0, S 0. Off the road (9): skA3T0Start, skLaySysAll1, skLaySysYHi,
skPsi3OffHi, skYbIFHuge, skSupKW, skImgEps, skCarryHigh, skYvCl. SUSPECT: skMidAssemble M, skRealB L. REFUTED: S 3, M 2, L 2.
Sorry leaves (52): OPEN 28; SUSPECT 2; REFUTED skTopDyn, skTopFam, skX0Law, skFormHighX (record); REPLACED 18.
Round 129 → 130: sorry 51 → 52, OPEN 27 → 28 (L), SUSPECT 2, REFUTED 6 → 7, nodes 511 → 549; road 19 OPEN L → 19, 0 REFUTED.

## REFUTED and SUSPECT

- **skLaySys_false REFUTED S** (`Yc.ycVD_empty`): `Xk.XkVD k` is empty for 1 ≤ k ≤ G (hull fields ask Cl(1, b), which
  stays below Γ(1)). Repaired by `Yc.YcVD`. Off the road.
- **skFixReadX_false REFUTED S** (round 130, `Yw.ywFirstFix_ref`): the least Γ-fixed point above x is ϑˣ(Ω₁·Ω₁+Ω₁). Off road.
- **skFormHighX REFUTED L** (`Xj.xjFormHighX_fail`): no form with constant ϑ-levels ends in X′. Off the road.
- **skTopFam, skTopDyn REFUTED M** (`Xi.xiTopFam_false`, `R2.SkRXTop`): no single image X̂ fits all cases.
  **skX0Law REFUTED L** (`Xd.xdX0Law_false`): outside D, T gives 0. **skShapeNat_false REFUTED S**. All replaced.
- **skRealB SUSPECT L**: `Ww.WwCarry` gives no bound for ϑ-levels with data in [υ_λ, υ_{λ+h}). Off the road.
- **skMidAssemble SUSPECT M**: its hypothesis covers only F_W ≤ m_λ < θ⁺; replaced by skMidCF. Off the road.
- PROVED negations: round 127 `Yi.yiWinShort_ref`, `Yi.yiMShort_ref`, `Yg.ygVdK_notYb`; round 129 `Ys.ysShortX_ref`; 130 `Yw.ywNoGo_GqSt`.

## Suggested order of the next rounds

1. Supply: skYvCl (θ-versions of the level lemmas, FRAG with level bound θ), reduce skShift2 to it, then skSupKXo.
2. Region B: skLayLoFix, skLayHiFix (codes with atoms of every kind); skWinIn / skTopIn, skWinRsIn / skTopRsIn, skWinCapV /
   skTopCapV, skTopLwNo2 (≤₂-copy of [L(ω), ν_C)); skBhiAfar (via `Yx.yxSpec_capsG`), skBhiL, skLongPre.
3. Reading: skPsi3OffHi, top laws at X + Ω₂ + e and beyond, then skWallBase, skWallStep; skTopK.
4. EQ: skGapRngHi (reading Θ_l(m_l) at long codes), skJumpNoRng (short-bottom part first).
