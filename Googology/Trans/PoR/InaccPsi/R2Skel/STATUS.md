# R₂^C skeleton: status (round 127)

Root `R2Skel.Root.skNuC (S : InaccSeq)` = the conclusion of `Xo.xoRoadH` (ν_C = L(ω+1), …), unchanged since round 125:
bridge `SkS.skRealBXo` (`Xo.XoRealB`), supply `SkS.skSupXo` (repaired `Xo.XoR`); frontier `SkF.skFront` → hUH/hLH/hVH/hVt;
reading `SkR.skWall`, `SkR.skThHi` → `SkE.skEQ hRead hUH hLH` → hT/hF. No part changed its top statement; Root unchanged.
The bundle SkF + SkE + SkR + SkS + Root checks against the main build with only `declaration uses sorry` warnings (48).

## Main progress number: OPEN / SUSPECT leaves on the road from `Root.skNuC`

**17 distinct OPEN leaves, all L; 0 SUSPECT; 0 REFUTED** (round 126: 21 OPEN L). Counted by a Lean walk over the
constants used by `skNuC`. On the road: SkF skLayLoBig, skLayHiBig, skBhiAfar, skBhiL, skWinA, skWinL, skTopA, skTopL,
skLongPre; SkR skWallBase, skWallStep; SkE skTopK, skGapEps, skGapRng, skJumpNoRng; SkS skSupKXo, skRealBXo.
Left the road in round 127: skLayDirect, skGapBlk (PROVED); skLaySysAll1, skLaySysYHi (skLayLo now uses skLayDirect).

**Vacuity: open.** No REFUTED or SUSPECT leaf is on the road. Non-vacuity is not proved: `Xo.XoSup`, `Xo.XoRealB` are
not shown satisfiable (`skYbIF` would give the covering lemma; it is now reduced to `skYbIFTh`, OPEN).

## Node tree (STATUS SIZE)

```
skNuC REDUCED L  (Xo.xoRoadH)
├ SkF.skFront REDUCED L ─ skAbove REDUCED L
│ ├ skRegA: REGION A CLOSED (skSysCof, skSysA3, skSysA3StepW PROVED L); off the road skA3T0Start OPEN L
│ ├ skRegB REDUCED L  (cells: base β ∈ {0, Ω₂·q, b_k, b_ω} + offset ζ < Ω₂)
│ │ ├ skRegBlo ─ skLay REDUCED L
│ │ │   skLayLo REDUCED L: skLayLoD (c+1 < ε₀, through skLayDirect) PROVED, skLayLoBig OPEN L
│ │ │   skLayHi REDUCED L: skLayDirect PROVED L (Yh.yhDirect, every c with c+1 < ε₀), skLayHiBig OPEN L
│ │ │   round 127 PROVED: skLayDirect0 M (whole layer 0)
│ │ │   off the road: skLaySysY REDUCED L ─ skLaySysAll1 OPEN L, skLaySysYHi OPEN L; skLaySys_false REFUTED S
│ │ ├ skRegBhi REDUCED L: skBhiA REDUCED L ─ skBhiAcell PROVED M, skBhiAfar OPEN L;  skBhiL OPEN L
│ │ ├ skWinA OPEN L; skWinB REDUCED L ─ skWinL OPEN L      (skWinNoBase PROVED S: no base data in windows)
│ │ │   round 127 PROVED S: skWinShortRef, skMShortRef (the induction with short inner reaches fails),
│ │ │     skWinCross (the corrected crossing clause Yi.YiCross follows from UPPER)
│ │ └ skTopA OPEN L; skTopB REDUCED L ─ skTopL OPEN L      (skTopNoBase PROVED S)
│ └ skRegC REDUCED L    skLongPre OPEN L; skLongMid, skLongTop PROVED S (vacuous)
├ SkR.skWall REDUCED L ─ skWallCF ─ skWallLow REDUCED L
│ │ skWallLevAll REDUCED L: skWallBase OPEN L, skWallStep OPEN L; skTopUp PROVED L
│ │   round 127 PROVED: skBaseFactsB, skTopMoveAllB (every top atom ψ₂(β + W^{X+e}) moves), skBlkMove,
│ │     skTopBase, skTopBlk, skTopBlkFin (atoms ψ₂(t + Ω₂·m + c) above a top atom t move)
│ └ skWallTh PROVED M
├ SkR.skThHi REDUCED L: skThMid REDUCED M, skThFar REDUCED M (skWallCF, skTopK)
│   (side: skMidAssemble SUSPECT M, skTopDyn / skTopFam REFUTED M, skX0Law REFUTED L, all off the road)
├ SkE.skEQ REDUCED L
│ ├ skThLow PROVED S;  └ skEQfar REDUCED L
│     skThFar ─ skTopK OPEN L (shared with SkR)
│     skKFar ─ skKCof ─ skKCofGap REDUCED S ─ skGapLh REDUCED S
│       ├ skGapEps OPEN L (ε-numbers in the υ-interval of B_n p)
│       ├ skGapRng OPEN L (υ-points in the gap when p is a restart)
│       └ skGapBlk PROVED S (Yk.ykGapBlk, no hypothesis)
│     skKReachR ─ skEQTopR REDUCED L ─ skEQJump REDUCED S
│       ├ skJumpOff PROVED S (vacuous)
│       └ skJumpNoRng OPEN L; round 127 PROVED: skChainLe1, skJumpGapBot, skJumpGapIff
│           (skJumpNoRng ⇔ the gap bottom υ_κ has reach r(κ) = B_n R)
└ SkS.skSupXo REDUCED L ─ skVisKXo REDUCED S ─ skGenXo REDUCED S
    ├ skUp REDUCED S ─ skUpRR REDUCED L (from SkF);  skFormXo PROVED S
    ├ skSupKXo OPEN L (carry with the repaired XoR)
    └ skRealBXo OPEN L (bridge Xo.XoRealB)
    off the road: skYbIF REDUCED L ─ skYbIFLowB PROVED (levels below B₂), skYbIFTh OPEN L (levels B₂ ≤ M < θ);
      skCoverXo, skSupNonSilent REDUCED S (to skYbIF); skShiftTh PROVED L, skSupX REDUCED,
      skFormHighX REFUTED L, skSupKW OPEN L, skRealB SUSPECT L, skImgEps OPEN L, skCarryHigh OPEN L
```

## Counts (472 nodes)

| part | PROVED | REDUCED | OPEN | SUSPECT | REFUTED | REPLACED | S | M | L |
|---|---|---|---|---|---|---|---|---|---|
| SkF | 174 | 23 | 12 | 0 | 2 | 27 | 102 | 70 | 66 |
| SkR | 57 | 9 | 2 | 1 | 3 | 0 | 33 | 25 | 14 |
| SkE | 56 | 12 | 4 | 0 | 0 | 0 | 63 | 0 | 9 |
| SkS | 53 | 28 | 6 | 1 | 1 | 0 | 34 | 21 | 34 |
| Root | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 1 |
| all | 340 | 73 | 24 | 2 | 6 | 27 | 232 | 116 | 124 |

OPEN by size: L 24 (SkF 12, SkR 2, SkE 4, SkS 6), M 0, S 0. Off the road: skA3T0Start, skLaySysAll1, skLaySysYHi,
skYbIFTh, skSupKW, skImgEps, skCarryHigh. SUSPECT: skMidAssemble M, skRealB L. REFUTED: S 2, M 2, L 2.
Sorry leaves (48): OPEN 24; SUSPECT 2; REFUTED skTopDyn, skTopFam, skX0Law, skFormHighX (record); REPLACED 18.
Round 126 → 127: sorry leaves 51 → 48, OPEN 27 → 24 (M 1 → 0), SUSPECT 2 → 2, REFUTED 6 → 6, nodes 451 → 472;
on the road 21 OPEN L → 17 OPEN L, 0 REFUTED.

## REFUTED and SUSPECT

- **skLaySys_false REFUTED S** (`Yc.ycVD_empty`): `Xk.XkVD k` is empty for 1 ≤ k ≤ G (hull fields ask Cl(1, b), which
  stays below Γ(1)). Repaired by `Yc.YcVD`. Off the road.
- **skFormHighX REFUTED L** (`Xj.xjFormHighX_fail`): no form with constant ϑ-levels ends in X′. Off the road.
- **skTopFam REFUTED M** (`Xi.xiTopFam_false`), **skTopDyn REFUTED M** (`R2.SkRXTop`): no single image X̂ fits
  all cases. **skX0Law REFUTED L** (`Xd.xdX0Law_false`): outside D the map T gives 0. **skShapeNat_false REFUTED S**
  (`Wh.whShapeNat_false`). All replaced by proved nodes.
- **skRealB SUSPECT L**: `Ww.WwCarry` gives no bound for ϑ-levels with data in [υ_λ, υ_{λ+h}). Off the road.
- **skMidAssemble SUSPECT M**: its hypothesis covers only F_W ≤ m_λ < θ⁺; replaced by skMidCF. Off the road.
- PROVED negations (round 127): the window induction with only short inner reaches contradicts LOWER
  (`Yi.yiWinShort_ref`, `Yi.yiMShort_ref`); dropping I_n from a VdK derivation fails (`Yg.ygVdK_notYb`).

## Suggested order of the next rounds

1. Supply: skYbIFTh (port the B₂-part to levels B₂ ≤ M < θ), then skRealBXo and skSupKXo; this decides non-vacuity.
2. Region B: skLayHiBig, skLayLoBig (ε₀ ≤ c+1: atom indices, Xx.XxGq, hull lemma and IMG); window induction with
   `Yi.YiCross` (relative restart context, relative Good) for skWinA/L, skTopA/L; skBhiAfar, skBhiL, skLongPre.
3. Reading: skWallBase (bases t + Ω₂·γ with γ ≥ ω, offsets ≥ Ω₂², limit parts), skWallStep; skTopK.
4. EQ: skJumpNoRng (the gap bottom reach), then skGapRng, skGapEps.
