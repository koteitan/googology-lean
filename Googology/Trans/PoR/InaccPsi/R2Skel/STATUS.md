# R₂^C skeleton: status (round 129)

Root `R2Skel.Root.skNuC (S : InaccSeq)` = the conclusion of `Xo.xoRoadH` (ν_C = L(ω+1), …). Round 129: the root applies
`Yq.yqRoadS` = `Xo.xoRoadH` with the bridge replaced by the shift `SkS.skShiftXo` (`Xo.XoShift S`; the old road used the
bridge only on windows up to L(ω+1)); supply `SkS.skSupXo` (repaired `Xo.XoR`); frontier `SkF.skFront` → hUH/hLH/hVH/hVt;
reading `SkR.skWall`, `SkR.skThHi` → `SkE.skEQ hRead hUH hLH` → hT/hF. No part changed its top statement.
The bundle SkF + SkE + SkR + SkS + Root checks against the main build with only `declaration uses sorry` warnings (51).

## Main progress number: OPEN / SUSPECT leaves on the road from `Root.skNuC`

**19 distinct OPEN leaves, all L; 0 SUSPECT; 0 REFUTED** (round 127 and 128: 17 OPEN L). Counted by a Lean walk over the
constants used by `skNuC`. On the road: SkF skLayLoFix, skLayHiFix, skBhiAfar, skBhiL, skWinSpec, skWinRsIn, skWinCapV,
skTopSpec, skTopRsIn, skTopCapV, skLongPre; SkR skWallBase, skWallStep; SkE skTopK, skGapEpsTop, skGapRng, skJumpNoRng;
SkS skSupKXo, skShift2. Round 129: skLayLoBig/HiBig → skLayLoFix/HiFix (layers B_Γ ≤ c < Ω₂ only); skWinA/L,
skTopA/L → six finer leaves; skGapEps → skGapEpsTop; skRealBXo → skShift2 (the bridge left the road).

**Vacuity: open.** No REFUTED or SUSPECT leaf is on the road. Non-vacuity is not proved: `Xo.XoSup` and the shift clause
`Yq.XoThCl` (behind skShift2) are not shown satisfiable.

## Node tree (STATUS SIZE)

```
skNuC REDUCED L  (Yq.yqRoadS)
├ SkF.skFront REDUCED L ─ skAbove REDUCED L
│ ├ skRegA: REGION A CLOSED (skSysCof, skSysA3, skSysA3StepW PROVED L); off the road skA3T0Start OPEN L
│ ├ skRegB REDUCED L  (cells: base β ∈ {0, Ω₂·q, b_k, b_ω} + offset ζ < Ω₂)
│ │ ├ skRegBlo ─ skLay REDUCED L
│ │ │   skLayLo REDUCED L: skLayLoD (c+1 < ε₀) PROVED, skLayLoBig REDUCED L ─ skLayBelowBG, skLayLoFix OPEN L
│ │ │   skLayHi REDUCED L: skLayDirect PROVED L, skLayHiBig REDUCED L ─ skLayBelowBG, skLayHiFix OPEN L
│ │ │   PROVED: skLayBelowBG L (round 129, Yr.yrLayAll: every layer c < B_Γ), skLayDirect0 M (round 127)
│ │ │   off the road: skLaySysY REDUCED L ─ skLaySysAll1 OPEN L, skLaySysYHi OPEN L; skLaySys_false REFUTED S
│ │ ├ skRegBhi REDUCED L: skBhiA REDUCED L ─ skBhiAcell PROVED M, skBhiAfar OPEN L;  skBhiL OPEN L
│ │ ├ skWinA REDUCED L, skWinB ─ skWinL REDUCED L ─ skWinUL PROVED S, skWinSpec, skWinRsIn, skWinCapV OPEN L
│ │ │   PROVED: round 129 skWinStep M, skWinInd M, skWinSpecOld S, skWinShortX S, skRsInCongr S;
│ │ │     round 127 skWinShortRef, skMShortRef, skWinCross S;  skWinNoBase S
│ │ └ skTopA REDUCED L, skTopB ─ skTopL REDUCED L ─ skTopUL, skTopPair, skTopNu PROVED S;
│ │     skTopSpec, skTopRsIn, skTopCapV OPEN L      (skTopNoBase PROVED S)
│ └ skRegC REDUCED L    skLongPre OPEN L; skLongMid, skLongTop PROVED S (vacuous)
├ SkR.skWall REDUCED L ─ skWallCF ─ skWallLow REDUCED L
│ │ skWallLevAll REDUCED L: skWallBase OPEN L, skWallStep OPEN L; skTopUp PROVED L
│ │   PROVED: round 129 skTopMoveY, skSubLawLim, skSubBaseLim, skSubMoveY M, skRefTests S; round 127 skBaseFactsB, …
│ │   off the road: skPsi3Off OPEN L (round 129; offsets Y₃ ≤ δ < Ω₃)
│ └ skWallTh PROVED M
├ SkR.skThHi REDUCED L: skThMid REDUCED M, skThFar REDUCED M (skWallCF, skTopK)
│   (side: skMidAssemble SUSPECT M, skTopDyn / skTopFam REFUTED M, skX0Law REFUTED L, all off the road)
├ SkE.skEQ REDUCED L
│ ├ skThLow PROVED S;  └ skEQfar REDUCED L
│     skThFar ─ skTopK OPEN L (shared with SkR)
│     skKFar ─ skKCof ─ skKCofGap REDUCED S ─ skGapLh REDUCED S
│       ├ skGapEps REDUCED S ─ skGapEpsIff PROVED S (+5 PROVED S), skGapEpsTop OPEN L (ξ' ≥ Ω₁·ε_{Ω₁+1})
│       ├ skGapRng OPEN L (υ-points in the gap when p is a restart)
│       └ skGapBlk PROVED S (Yk.ykGapBlk, no hypothesis)
│     skKReachR ─ skEQTopR REDUCED L ─ skEQJump REDUCED S
│       ├ skJumpOff PROVED S (vacuous)
│       └ skJumpNoRng OPEN L; round 127 PROVED: skChainLe1, skJumpGapBot, skJumpGapIff
├ SkS.skShiftXo REDUCED M ─ skShift2 OPEN L (ϑ-node clause Yq.XoThCl for the FRAG map, on top of Xb.XbShift)
└ SkS.skSupXo REDUCED L ─ skVisKXo REDUCED S ─ skGenXo REDUCED S
    ├ skUp REDUCED S ─ skUpRR REDUCED L (from SkF);  skFormXo PROVED S
    └ skSupKXo OPEN L (carry with the repaired XoR)
    off the road: skRealBXo REDUCED L ─ skRealBXoL REDUCED L; skYbIF REDUCED L ─ skYbIFLowB PROVED,
      skYbIFTh REDUCED L ─ skYbIFNot PROVED M (notation range, Yq.yqIFN), skYbIFHuge OPEN L (data above every ψ_{Ω₁});
      skCoverXoL, skSupNonSilentL, skLevKNot PROVED S; skShiftTh PROVED L, skSupX REDUCED,
      skFormHighX REFUTED L, skSupKW OPEN L, skRealB SUSPECT L, skImgEps OPEN L, skCarryHigh OPEN L
```

## Counts (511 nodes)

| part | PROVED | REDUCED | OPEN | SUSPECT | REFUTED | REPLACED | S | M | L |
|---|---|---|---|---|---|---|---|---|---|
| SkF | 184 | 29 | 14 | 0 | 2 | 27 | 109 | 72 | 75 |
| SkR | 62 | 9 | 3 | 1 | 3 | 0 | 34 | 29 | 15 |
| SkE | 62 | 13 | 4 | 0 | 0 | 0 | 70 | 0 | 9 |
| SkS | 57 | 32 | 6 | 1 | 1 | 0 | 37 | 23 | 37 |
| Root | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 1 |
| all | 365 | 84 | 27 | 2 | 6 | 27 | 250 | 124 | 137 |

OPEN by size: L 27 (SkF 14, SkR 3, SkE 4, SkS 6), M 0, S 0. Off the road: skA3T0Start, skLaySysAll1, skLaySysYHi,
skPsi3Off, skYbIFHuge, skSupKW, skImgEps, skCarryHigh. SUSPECT: skMidAssemble M, skRealB L. REFUTED: S 2, M 2, L 2.
Sorry leaves (51): OPEN 27; SUSPECT 2; REFUTED skTopDyn, skTopFam, skX0Law, skFormHighX (record); REPLACED 18.
Round 127/128 → 129: sorry leaves 48 → 51, OPEN 24 → 27 (all L), SUSPECT 2 → 2, REFUTED 6 → 6, nodes 472 → 511;
on the road 17 OPEN L → 19 OPEN L (four window leaves split into six finer ones), 0 REFUTED.

## REFUTED and SUSPECT

- **skLaySys_false REFUTED S** (`Yc.ycVD_empty`): `Xk.XkVD k` is empty for 1 ≤ k ≤ G (hull fields ask Cl(1, b), which
  stays below Γ(1)). Repaired by `Yc.YcVD`. Off the road.
- **skFormHighX REFUTED L** (`Xj.xjFormHighX_fail`): no form with constant ϑ-levels ends in X′. Off the road.
- **skTopFam, skTopDyn REFUTED M** (`Xi.xiTopFam_false`, `R2.SkRXTop`): no single image X̂ fits all cases.
  **skX0Law REFUTED L** (`Xd.xdX0Law_false`): outside D, T gives 0. **skShapeNat_false REFUTED S**. All replaced.
- **skRealB SUSPECT L**: `Ww.WwCarry` gives no bound for ϑ-levels with data in [υ_λ, υ_{λ+h}). Off the road.
- **skMidAssemble SUSPECT M**: its hypothesis covers only F_W ≤ m_λ < θ⁺; replaced by skMidCF. Off the road.
- PROVED negations: round 127 `Yi.yiWinShort_ref`, `Yi.yiMShort_ref`, `Yg.ygVdK_notYb`; round 129 `Ys.ysShortX_ref`.

## Suggested order of the next rounds

1. Supply: skShift2 (the ϑ-node clause `Yq.XoThCl`), then skSupKXo (reach r(μ + f g) at supply restarts); decides vacuity.
2. Region B: skLayLoFix, skLayHiFix (atoms ψ_{Ω₂}(Ω₂+ν)); skWinSpec at k = 0, every k, skTopSpec; skWinRsIn /
   skTopRsIn (FRAG-based RS step), skWinCapV / skTopCapV; skBhiAfar, skBhiL, skLongPre with the same induction.
3. Reading: skPsi3Off (offsets Y₃ ≤ δ < Ω₃), top laws at exponents X + E with E ≥ Ω₂, then skWallBase, skWallStep; skTopK.
4. EQ: skGapEpsTop (cite [W07b] Lemma 4.2, prove `YuGapPlus`), skJumpNoRng, skGapRng.
