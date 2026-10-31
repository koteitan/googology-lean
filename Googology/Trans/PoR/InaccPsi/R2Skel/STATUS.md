# R₂^C skeleton: status (round 115)

Root `R2Skel.Root.skNuC (S : InaccSeq)` = the conclusion of `Wd.wdRoadL` (ν_C = L(ω+1), L(ω) ≤₂ L(ω+1), …).
It applies `Wd.wdRoadL` to the four parts: frontier `SkF.skFront` → hUH/hLH/hVH/hVt; reading `SkR.skWall`,
`SkR.skThHi` → `hRead` of `SkE.skEQ`; `SkE.skEQ hRead` → hT/hF; supply `SkS.skSup` → h0/hn.
The bundle SkF + SkR + SkE + SkS + Root checks against the main build with only `declaration uses sorry`
warnings (32 leaves); `#print axioms R2Skel.Root.skNuC` = sorryAx + propext/choice/Quot.sound + repo axioms.
Integration change: `SkS.skUpRR` and `SkS.skNu` were OPEN; they are now REDUCED to `SkF.skFrontU/L/V/Vt`
(below the frontier `Hl.hlU_enum`; `Wd.wdNu`). Every node carries STATUS / SIZE in its docstring.

## Node tree (STATUS SIZE; leaves with `sorry` are OPEN / SUSPECT / REFUTED)

```
skNuC REDUCED L
├ SkF.skFront REDUCED L  (U/L/V/Vt projections REDUCED L; skRoad REDUCED L)
│ ├ skHypIff PROVED S
│ └ skAbove REDUCED L
│   ├ skRegA REDUCED L   region (A): l < ι(Γ(B)·ω), B < Γ(1)
│   │ ├ skLocOfSys PROVED S
│   │ └ skSysCof REDUCED L
│   │   ├ skSysA1 REDUCED M   ℓ < ε_{Ω₁+1}
│   │   │ ├ skCofLev OPEN S
│   │   │ └ skSysAll REDUCED M ─ skFam REDUCED M ─ skStep REDUCED M
│   │   │   ├ skShape OPEN S, skStepBase OPEN S
│   │   │   ├ skLvDatum REDUCED M: skDigitGate OPEN M, skReadExact PROVED S, skLvOfGate OPEN S
│   │   │   └ skStepSucc / skStepPow / skStepExpLim / skStepCoefLim OPEN M
│   │   ├ skSysA2 OPEN L   ε_{Ω₁+1} ≤ ℓ < G
│   │   └ skSysA3 OPEN L   G ≤ ℓ < Γ(1)
│   ├ skRegB SUSPECT L     region (B), atoms Γ(c)
│   └ skRegC REDUCED L     e(η) ≥ Ω₂: skLongPre / skLongMid / skLongTop OPEN L
│   (repo evidence: skLocHo, skSysHo, skSysHoSg PROVED S)
├ hRead from SkR
│ ├ SkR.skWall REDUCED L
│ │ ├ skWallLow REDUCED L
│ │ │ ├ skThCof PROVED S
│ │ │ └ skWallLevAll SUSPECT L
│ │ │   ├ skTopDyn REFUTED M
│ │ │   └ skWallBase SUSPECT L, skWallStep SUSPECT L
│ │ └ skWallTh REDUCED M: skThVal OPEN M, skThAtom PROVED S
│ └ SkR.skThHi REDUCED L
│   ├ skThMid REDUCED M: skBlkLaw REDUCED S (skThVal), skMidAssemble OPEN M
│   └ skThFar OPEN L   (FarLowMove)
│   (side nodes: skRead REDUCED L, skLowExp / skBelowThP / skRead_of_EQ / skNonVac PROVED S)
├ SkE.skEQ REDUCED L
│ ├ skThLow REDUCED L: skThLow_of PROVED S
│ └ skEQfar REDUCED L: skEQfar_of PROVED S, skThFar OPEN L (SkThFar)
│   └ skKFar REDUCED L: skKFar_of PROVED S, skKClosed / skKGap / skKLim OPEN L
│   (guards: skNoIdx, skThFar_of_top, skThHi_of_top, skThFar_of_EQ, skKTop_of_EQ PROVED S)
└ SkS.skSup REDUCED L ─ skVisK REDUCED L
  ├ skWin PROVED S
  └ skGen REDUCED L
    ├ skUp REDUCED S ─ skUpRR REDUCED L (from SkF)
    ├ skForm REDUCED L: skFormWit REDUCED S ─ skNu REDUCED L (from SkF); skFormOther OPEN L
    └ skSupK REDUCED L
      ├ skMu REDUCED L: skCodeCof PROVED S, skRead0 OPEN L
      ├ skCarryWit REDUCED L
      │ ├ skOffMapW SUSPECT M ─ skPiT PROVED M
      │ ├ skLowerF OPEN M, skBigF OPEN M
      │ └ skImgF SUSPECT L
      └ skCarryOther SUSPECT L
```

## Counts (94 nodes)

| part | PROVED | REDUCED | OPEN | SUSPECT | REFUTED | S | M | L |
|---|---|---|---|---|---|---|---|---|
| SkF | 6 | 15 | 14 | 1 | 0 | 10 | 10 | 16 |
| SkR | 6 | 7 | 3 | 3 | 1 | 7 | 5 | 8 |
| SkE | 8 | 4 | 4 | 0 | 0 | 8 | 0 | 8 |
| SkS | 3 | 11 | 4 | 3 | 0 | 4 | 4 | 13 |
| Root | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 1 |
| all | 23 | 38 | 25 | 7 | 1 | 29 | 19 | 46 |

Leaves left (32): OPEN 25 = S 4 + M 9 + L 12; SUSPECT leaves 6 = M 1 + L 5 (plus the inner node skWallLevAll);
REFUTED 1 (M).

## REFUTED and SUSPECT

- **skTopDyn REFUTED** (`R2.SkRXTop`, `skrxTopDynAll_false`): no single image X̂ fits both e = 0 and e = 1 at the
  restart of L(0); X̂ must depend on e.
- **skWallBase, skWallStep SUSPECT**: vacuous, their hypothesis is skTopDyn. **skWallLevAll SUSPECT**: its proof
  uses skTopDyn; its statement follows from UdAtMove25 and is not refuted.
- **skRegB SUSPECT** (`R2.SkFXRegB`): region (B) is not below ι(Ω₂); it holds every name with last exponent < Ω₂,
  e.g. a restart with L(0) < υ_λ < L(1). So it is as strong as the main target (false if ν_C < L(ω+1)).
- **skOffMapW, skImgF, skCarryOther SUSPECT** (`R2.SkSXPi`): they bound π_{υ_μ,υ_λ} at points of [υ_μ, υ_λ)
  outside T^{υ_λ}[υ_μ], where no axiom fixes π. So `Vr.VrSup`, hence `Vr.VrVisGen` (h0/hn of `wdRoadL`), is
  likely independent of the axioms as written. Not refuted; the road is not shown vacuous.

## Suggested order of the next rounds

1. Supply: weaken `Vr.VrCarry` / `SkMapP` / `WcPiLo` to lo-leaves p < υ_μ or p ∈ T^{υ_λ}[υ_μ]; new road over the
   weakened h0/hn; then skRead0, skLowerF, skBigF, skImgF, skFormOther, skCarryOther.
2. Reading: restate skTopDyn with X̂ depending on e; redo skWallBase / skWallStep; then skThVal, skMidAssemble.
3. Frontier, small: skShape, skCofLev, skDigitGate → skLvOfGate, the five step nodes (closes (A1)).
4. Frontier: re-split regions by name exponent (< Ω₂ vs ≥ Ω₂) and resize skRegB; then skSysA2, skSysA3.
5. The L leaves tied to the main target: skLong*, SkE skThFar / skKClosed / skKGap / skKLim, SkR skThFar.
