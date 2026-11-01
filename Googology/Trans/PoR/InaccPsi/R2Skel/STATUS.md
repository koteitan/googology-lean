# R₂^C skeleton: status (round 126)

Root `R2Skel.Root.skNuC (S : InaccSeq)` = the conclusion of `Xo.xoRoadH` (ν_C = L(ω+1), …), unchanged since round 125:
bridge `SkS.skRealBXo` (`Xo.XoRealB`), supply `SkS.skSupXo` (repaired `Xo.XoR`); frontier `SkF.skFront` → hUH/hLH/hVH/hVt;
reading `SkR.skWall`, `SkR.skThHi` → `SkE.skEQ hRead hUH hLH` → hT/hF. No part changed its top statement.
The bundle SkF + SkE + SkR + SkS + Root checks against the main build with only `declaration uses sorry` warnings (51).

## Main progress number: OPEN / SUSPECT leaves on the road from `Root.skNuC`

**21 distinct OPEN leaves, all L; 0 SUSPECT; 0 REFUTED** (round 125: 18 OPEN L). Counted by a Lean walk over the
constants used by `skNuC`. On the road: SkF skLaySysAll1, skLaySysYHi, skLayLoBig, skLayDirect, skLayHiBig, skBhiAfar,
skBhiL, skWinA, skWinL, skTopA, skTopL, skLongPre; SkR skWallBase, skWallStep; SkE skTopK, skGapEps, skGapRng, skGapBlk,
skJumpNoRng; SkS skSupKXo, skRealBXo. Left the road: skLaySys (REFUTED), skLayHi, skBhiA, skGapLh (REDUCED), skJumpOff (PROVED).

**Vacuity: open.** Round 125's road contained skLaySys, now REFUTED (so that road was vacuous); the road now uses the
repaired systems `Yc.YcVD` instead. No REFUTED or SUSPECT leaf is on the road. Non-vacuity is not proved:
`Xo.XoSup`, `Xo.XoRealB` are not shown satisfiable (`skYbIF` would give the covering lemma, but is OPEN).

## Node tree (STATUS SIZE)

```
skNuC REDUCED L  (Xo.xoRoadH)
├ SkF.skFront REDUCED L ─ skAbove REDUCED L
│ ├ skRegA: REGION A CLOSED (skSysCof, skSysA3, skSysA3StepW PROVED L); off the road skA3T0Start OPEN L
│ ├ skRegB REDUCED L  (cells: base β ∈ {0, Ω₂·q, b_k, b_ω} + offset ζ < Ω₂)
│ │ ├ skRegBlo ─ skLay REDUCED L
│ │ │   skLayLo REDUCED L: skLayFrontY PROVED L (repaired systems, k+1 < ε₀), skLayLoBig OPEN L,
│ │ │     skLaySysY REDUCED L ─ skLaySysAll1 OPEN L, skLaySysYHi OPEN L  (skLaySysAll0 PROVED S = Ws.wsSysAll)
│ │ │   skLayHi REDUCED L: skLayDirect OPEN L (direct readings Xx.XxRS c), skLayHiBig OPEN L
│ │ │   round 126 PROVED: skLayEmpty, skLayNoTransfer, skLayLoD, skLayDirectA2 (S); skLaySys_false REFUTED S
│ │ │   skLayFront PROVED L (old Xk.XkVD: vacuous for k ≥ 1)
│ │ ├ skRegBhi REDUCED L: skBhiA REDUCED L ─ skBhiAcell PROVED M, skBhiAfar OPEN L;  skBhiL OPEN L
│ │ │   round 126 PROVED: skCellUV L (cell transport from base data)
│ │ ├ skWinA OPEN L; skWinB REDUCED L ─ skWinL OPEN L      (skWinNoBase PROVED S: no base data in windows)
│ │ └ skTopA OPEN L; skTopB REDUCED L ─ skTopL OPEN L      (skTopNoBase PROVED S)
│ └ skRegC REDUCED L    skLongPre OPEN L; skLongMid, skLongTop PROVED S (vacuous)
├ SkR.skWall REDUCED L ─ skWallCF ─ skWallLow REDUCED L
│ │ skWallLevAll REDUCED L: skWallBase OPEN L, skWallStep OPEN L; skTopUp PROVED L
│ │   round 126: base-0 data and top atoms move for every top exponent (PROVED); skTopMoveAllB REDUCED M
│ │     ─ skBaseFactsB OPEN M (off the road: W^{X+B_n e} | B_n β, B_n β ∈ D_λ')
│ └ skWallTh PROVED M
├ SkR.skThHi REDUCED L: skThMid REDUCED M, skThFar REDUCED M (skWallCF, skTopK)
│   (side: skMidAssemble SUSPECT M, skTopDyn / skTopFam REFUTED M, skX0Law REFUTED L, all off the road)
├ SkE.skEQ REDUCED L
│ ├ skThLow PROVED S;  └ skEQfar REDUCED L
│     skThFar ─ skTopK OPEN L (shared with SkR)
│     skKFar ─ skKCof ─ skKCofGap REDUCED S ─ skGapLh REDUCED S
│       ├ skGapEps OPEN L (ε-numbers in the υ-interval of B_n p)
│       ├ skGapRng OPEN L, skGapBlk OPEN L (υ-points in the gap when p is a restart)
│     skKReachR ─ skEQTopR REDUCED L ─ skEQJump REDUCED S
│       ├ skJumpOff PROVED S (vacuous: the hypothesis "s not a range restart" never holds)
│       └ skJumpNoRng OPEN L (s a range restart: does not occur)
└ SkS.skSupXo REDUCED L ─ skVisKXo REDUCED S ─ skGenXo REDUCED S
    ├ skUp REDUCED S ─ skUpRR REDUCED L (from SkF);  skFormXo PROVED S
    ├ skSupKXo OPEN L (carry with the repaired XoR)
    └ skRealBXo OPEN L (bridge Xo.XoRealB)
    round 126 (off the road): skYbIF OPEN L (every level has a term without I_n); skYbIFWit, skLevOfIF,
      skCoverLev, skCoverWit PROVED; skCoverXo, skSupNonSilent REDUCED S (to skYbIF)
    off the road: skShiftTh PROVED L, skSupX REDUCED, skFormHighX REFUTED L, skSupKW OPEN L, skRealB SUSPECT L,
      skImgEps OPEN L, skCarryHigh OPEN L
```

## Counts (451 nodes)

| part | PROVED | REDUCED | OPEN | SUSPECT | REFUTED | REPLACED | S | M | L |
|---|---|---|---|---|---|---|---|---|---|
| SkF | 169 | 23 | 13 | 0 | 2 | 27 | 99 | 69 | 66 |
| SkR | 51 | 10 | 3 | 1 | 3 | 0 | 32 | 22 | 14 |
| SkE | 50 | 12 | 5 | 0 | 0 | 0 | 57 | 0 | 10 |
| SkS | 46 | 27 | 6 | 1 | 1 | 0 | 31 | 18 | 32 |
| Root | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 1 |
| all | 316 | 73 | 27 | 2 | 6 | 27 | 219 | 109 | 123 |

OPEN by size: L 26 (SkF 13, SkR 2, SkE 5, SkS 6), M 1 (skBaseFactsB). Off the road: skA3T0Start, skBaseFactsB, skYbIF,
skSupKW, skImgEps, skCarryHigh. SUSPECT: skMidAssemble M, skRealB L. REFUTED: S 2, M 2, L 2.
Sorry leaves (51): OPEN 27; SUSPECT 2; REFUTED skTopDyn, skTopFam, skX0Law, skFormHighX (record); REPLACED 18.
Round 125 → 126: sorry leaves 46 → 51, OPEN 22 → 27, SUSPECT 2 → 2, REFUTED 5 → 6, nodes 402 → 451;
on the road 18 OPEN L → 21 OPEN L, 0 REFUTED.

## REFUTED and SUSPECT

- **skLaySys_false REFUTED S** (`Yc.ycLaySys_false_eps`, `Yc.ycVD_empty`): `Xk.XkVD k` is empty for 1 ≤ k ≤ G: its
  hull fields ask membership in every Cl(a, b) with 0 < a, but Cl(1, b) ∩ Ω₂ ⊆ ψ_{Ω₂}(1) = Γ(1) while the bound is
  ≥ Γ(k). Repair: ask k < a (`Yc.YcVD`, `Yc.YcC`; same as before at k = 0). Was on the road in round 125.
- **skFormHighX REFUTED L** (`Xj.xjFormHighX_fail`): no form with constant ϑ-levels ends in X′. Off the road.
- **skTopFam REFUTED M** (`Xi.xiTopFam_false`), **skTopDyn REFUTED M** (`R2.SkRXTop`): no single image X̂ fits
  all cases. **skX0Law REFUTED L** (`Xd.xdX0Law_false`): outside D the map T gives 0. **skShapeNat_false REFUTED S**
  (`Wh.whShapeNat_false`). All replaced by proved nodes.
- **skRealB SUSPECT L**: `Ww.WwCarry` gives no bound for ϑ-levels with data in [υ_λ, υ_{λ+h}). Off the road.
- **skMidAssemble SUSPECT M**: its hypothesis covers only F_W ≤ m_λ < θ⁺; replaced by skMidCF. Off the road.
- PROVED negations: inverse map below B_n(ψ₂ t) (`Yd.ydInvRef`), relabelling G ↦ Γ(k) (`Yc.ycRelab_gap`), cells in windows.

## Suggested order of the next rounds

1. Supply: skYbIF (below B₂ port `Uo.uo_ucK` to YbK), then skRealBXo and skSupKXo; this decides non-vacuity.
2. Region B: skLayDirect (c = 1: add limit data to the Xu codes, then generalise to the atom Γ(1)), skLayHiBig,
   skLayLoBig (or skLaySysAll1 / skLaySysYHi); then ι(Ω₂) base data and skBhiAfar; window induction relative to the
   long reach of L(k) for skWinA/L, skTopA/L; skBhiL, skLongPre.
3. Reading: skBaseFactsB, then the non-top atoms of skWallBase / skWallStep; skTopK.
4. EQ: skJumpNoRng, then skGapRng / skGapBlk, skGapEps.
