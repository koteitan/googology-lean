# R₂^C skeleton: status (round 116)

Root `R2Skel.Root.skNuC (S : InaccSeq)` = the conclusion of `Wf.wfRoad` (same as `Wd.wdRoadL`: ν_C = L(ω+1), …).
Round 116 moves the root from `Wd.wdRoadL` to `Wf.wfRoad`, whose supply hypotheses h0/hn are `Wf.WfVisGen`:
`Vr.VrVisGen` restricted to lo-leaves in T^{υ_λ}[υ_μ] (below υ_λ: p < υ_μ). `Wf.wfVisGen_of_vr`: the old form implies it.
Parts: frontier `SkF.skFront` → hUH/hLH/hVH/hVt; reading `SkR.skWall`, `SkR.skThHi` → `SkE.skEQ` → hT/hF; supply
`SkS.skSup` → h0/hn. The bundle SkF + SkR + SkE + SkS + Root checks against the main build with only
`declaration uses sorry` warnings (40); `#print axioms R2Skel.Root.skNuC` = sorryAx + propext/choice/Quot.sound + repo axioms.

## Node tree (STATUS SIZE)

```
skNuC REDUCED L
├ SkF.skFront REDUCED L  (U/L/V/Vt REDUCED L; skRoad REDUCED L; skHypIff PROVED S)
│ └ skAbove REDUCED L
│   ├ skRegA REDUCED L ─ skLocOfSys PROVED S, skSysCof REDUCED L
│   │ ├ skSysA1 REDUCED M   ℓ < ε_{Ω₁+1}: skCofLev PROVED S, skSysAll ─ skFam ─ skStep REDUCED M (on SkAtW)
│   │ │ ├ skShape PROVED S (e : Ordinal), skLvDatum PROVED M (skDigitGate PROVED M, skLvOfGate PROVED S)
│   │ │ ├ skStepBaseW PROVED S, skStepSuccW PROVED M
│   │ │ └ skStepPowW / skStepExpLimW / skStepCoefLimW OPEN M
│   │ ├ skSysA2 REDUCED L   [φ(E, G+1), φ(G, 1)): skSysA2Lev REDUCED M
│   │ │ ├ skSysAllG ─ skFamG ─ skStepG REDUCED M: skShapeG OPEN S, skLvDatumG REDUCED S (skLvOfGateG OPEN S)
│   │ │ │   skStepBaseG REDUCED S, skStepSuccG / skStepPowG / skStepCoefLimG / skStepExpLimG OPEN M
│   │ │ └ skLevG_Bn PROVED S, skGateBn OPEN S
│   │ └ skSysA3 REDUCED L ─ skSysA3All REDUCED L ─ skSysA3Lev: skSysA3Lev0 OPEN L, skSysA3Step SUSPECT M
│   ├ skRegB REDUCED L    (Wj.wjRegB_iff): skRegBlo OPEN L, skRegBhi OPEN L,
│   │   skWin: skWinA / skWinB OPEN L; skTop: skTopA / skTopB OPEN L
│   └ skRegC REDUCED L    skLongPre OPEN L; skLongMid, skLongTop PROVED S (vacuous)
│   (evidence: skLocHo, skSysHo, skSysHoSg, skReadExact, skAtG_iff, skSplit, skWinNonempty PROVED S)
├ SkR.skWall REDUCED L
│ ├ skWallLow REDUCED L: skThCof PROVED S, skWallLevAll REDUCED L
│ │   skTopFam OPEN M (skTopFam0, skTopSep PROVED S), skWallBase OPEN L, skWallStep OPEN L
│ └ skWallTh REDUCED M: skThVal REDUCED S (skThUp PROVED S, skThLow OPEN L), skThAtom PROVED S
├ SkR.skThHi REDUCED L: skThMid REDUCED M (skBlkLaw REDUCED S, skMidAssemble OPEN M), skThFar OPEN L
│   (side: skRead REDUCED L; skLowExp, skBelowThP, skRead_of_EQ, skNonVac PROVED S; skTopDyn REFUTED M)
├ SkE.skEQ REDUCED L
│ ├ skThLow REDUCED L: skThLow_of PROVED S
│ └ skEQfar REDUCED L: skEQfar_of PROVED S, skThFar OPEN L, skKFar REDUCED L
│     skKFar_of PROVED S, skKClosed / skKGap / skKLim OPEN L   (5 guard nodes PROVED S)
└ SkS.skSup REDUCED L ─ skVisK REDUCED L: skWin PROVED S, skGen REDUCED L
    ├ skUp REDUCED S ─ skUpRR REDUCED L (from SkF)
    ├ skForm REDUCED L: skFormWit REDUCED S ─ skNu REDUCED L (from SkF); skFormOther OPEN L
    └ skSupK REDUCED L
      ├ skMu REDUCED L: skCodeCof PROVED S, skRead0 OPEN L
      ├ skCarryWit REDUCED L: skOffMapW REDUCED M (Wf.wfOffMap, skNu), skLowerF OPEN M, skBigF OPEN M,
      │   skImgF OPEN L   (skPiT PROVED M, skPiLo PROVED S, skSideRef PROVED S)
      └ skCarryOther OPEN L
```

## Counts (138 nodes)

| part | PROVED | REDUCED | OPEN | SUSPECT | REFUTED | REPLACED | S | M | L |
|---|---|---|---|---|---|---|---|---|---|
| SkF | 22 | 27 | 18 | 1 | 1 | 4 | 25 | 23 | 25 |
| SkR | 9 | 9 | 6 | 0 | 1 | 0 | 11 | 5 | 9 |
| SkE | 8 | 4 | 4 | 0 | 0 | 0 | 8 | 0 | 8 |
| SkS | 5 | 12 | 6 | 0 | 0 | 0 | 6 | 4 | 13 |
| Root | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 1 |
| all | 44 | 53 | 34 | 1 | 2 | 4 | 50 | 32 | 56 |

Sorry leaves (40): OPEN 34 = S 3 + M 11 + L 20; SUSPECT 1 (M); REFUTED skTopDyn (M, kept for the record);
REPLACED 4 (M: SkF skStepSucc / skStepPow / skStepExpLim / skStepCoefLim, kept, not used).
Round 115 → 116: sorry leaves 32 → 40, OPEN 25 → 34, SUSPECT 6 → 1, because gam41 and reg1 split open nodes.

## REFUTED and SUSPECT

- **skTopDyn REFUTED** (`R2.SkRXTop`): no single image X̂ fits e = 0 and e = 1; replaced by the law
  `Wg.WgTopFamAll` (image X̂_e depending on e; `Wg.wgSep01` forces X̂₀(Ω₃) ≤ X̂₁(0)).
- **skShapeNat_false REFUTED S** (`Wh.whShapeNat_false`, proved): with `e : ℕ` in the shapes, Ω₁^ω has no shape;
  the shapes now use `e : Ordinal`.
- **`hside` of `Wc.wcSupLo` refuted** (`Wf.wfSide_false`, node skSideRef): false once Os ≠ {g}; not used any more.
- **skSysA3Step SUSPECT M**: its invariant `SkPk3` holds only the system, but the step t_n ↦ φ(t_n, 0) needs the
  full A3 level package; strengthen `SkPk3` once an A3 level datum exists.
- Cleared: skRegB (now REDUCED via the window split), skOffMapW / skImgF / skCarryOther (restricted carry `Wf.WfR`),
  skWallBase / skWallStep / skWallLevAll (hypothesis now the unrefuted family law).
- Risk notes (OPEN, not SUSPECT): skWallBase / skWallStep likely also need a B_n move of the images X̂;
  skWinA/B, skTopA/B are each as strong as "ν_C is not in that window"; the A2 G-steps run on `SkAtG`,
  which lacks the start condition that gam41 added in `SkAtW`.

## Suggested order of the next rounds

1. Supply: skRead0 (WcRead0, υ_{μ+1} ≤ Θ_C(θ)); then skLowerF, skBigF, skImgF, skFormOther, skCarryOther.
2. Reading: skThLow; the family law at every base for e = 0, then e = 1; the B_n move of X̂ for skWallBase /
   skWallStep; skMidAssemble; skThFar.
3. Frontier A1: an extension that lowers by the pseudo-base gate, then skStepCoefLimW, skStepExpLimW, skStepPowW.
4. Frontier A2: skShapeG, skLvOfGateG (ports of gam41), skGateBn; the four G-steps on a SkAtW-style predicate.
5. Frontier A3: a level datum with atoms {Ω₁, G}; skSysA3Lev0, skSysA3Step (strengthened).
6. The L leaves tied to the main target: skRegBlo, skRegBhi, skLongPre, skWin*/skTop*, SkE skThFar / skK*.
