# R₂^C skeleton: status (round 117)

Root `R2Skel.Root.skNuC (S : InaccSeq)` = the conclusion of `Wf.wfRoad` (same as `Wd.wdRoadL`: ν_C = L(ω+1), …),
whose supply hypotheses h0/hn are `Wf.WfVisGen`. Parts: frontier `SkF.skFront` → hUH/hLH/hVH/hVt; reading
`SkR.skWall`, `SkR.skThHi` → `SkE.skEQ` → hT/hF; supply `SkS.skSup` → h0/hn. Root and the top nodes are unchanged.
The bundle SkF + SkR + SkE + SkS + Root checks against the main build with only `declaration uses sorry` warnings (39).

## Node tree (STATUS SIZE)

```
skNuC REDUCED L
├ SkF.skFront REDUCED L  (U/L/V/Vt REDUCED L; skRoad REDUCED L; skHypIff PROVED S)
│ └ skAbove REDUCED L
│   ├ skRegA REDUCED L ─ skLocOfSys PROVED S, skSysCof REDUCED L
│   │ ├ skSysA1 REDUCED M   ℓ < ε_{Ω₁+1}: skCofLev PROVED S, skSysAll ─ skFam REDUCED M (on SkCohW2)
│   │ │ ├ skStepW2 REDUCED M: skStepBaseW2 PROVED S, skStepSuccW2 / skStepFsW2 PROVED M
│   │ │ │   (skStepCoefLimW2, skStepExpLimFsW2 PROVED M: every level with an ω-sequence)
│   │ │ ├ skStepOm1W2 OPEN L   (levels of cofinality Ω₁)
│   │ │ └ skShape, skLvOfGate, skOldVacuous, skExtW2_old, skCohW2_old PROVED S; skLvDatum, skFamSq PROVED M
│   │ ├ skSysA2 REDUCED L   [φ(E, G+1), φ(G, 1)): skSysA2Lev REDUCED M
│   │ │ ├ skSysAllG ─ skFamWG ─ skStepWG REDUCED M (on SkAtWG = Wn.WnAt)
│   │ │ │   skShapeG, skLvDatumG, skStepBaseWG PROVED S, skStepSuccWG PROVED M
│   │ │ │   skStepPowWG / skStepCoefLimWG / skStepExpLimWG OPEN M
│   │ │ └ skLevG_Bn, skGateBn PROVED S
│   │ └ skSysA3 REDUCED L ─ skSysA3All ─ skSysA3Lev ─ skSysA3LevW REDUCED L (on SkPk3W = Wn.WnEnt3)
│   │     skSysA3Lev0W OPEN L, skSysA3StepW OPEN L; skA3NoBand, skA3NoGBase, skA3Datum0, skPk3_of_W PROVED S
│   ├ skRegB REDUCED L    (Wj.wjRegB_iff): skRegBlo OPEN L, skRegBhi OPEN L,
│   │   skWin: skWinA / skWinB OPEN L; skTop: skTopA / skTopB OPEN L
│   └ skRegC REDUCED L    skLongPre OPEN L; skLongMid, skLongTop PROVED S (vacuous)
├ SkR.skWall REDUCED L
│ ├ skWallLow REDUCED L: skThCof PROVED S, skWallLevAll REDUCED L
│ │   skTopFam OPEN M (skTopFam0, skTopSep PROVED S), skWallBase OPEN L, skWallStep OPEN L
│ └ skWallTh PROVED M: skThVal PROVED S (skThUp PROVED S, skThLow PROVED L), skThAtom PROVED S
├ SkR.skThHi REDUCED L: skThMid REDUCED M (skBlkLaw PROVED S, skMidAssemble OPEN M), skThFar OPEN L
│   (side: skRead REDUCED L; skLowExp, skBelowThP, skRead_of_EQ, skNonVac PROVED S; skTopDyn REFUTED M)
├ SkE.skEQ REDUCED L
│ ├ skThLow REDUCED L: skThLow_of PROVED S
│ └ skEQfar REDUCED L: skEQfar_of PROVED S, skThFar OPEN L, skKFar REDUCED L
│     skKFar_of PROVED S, skKClosed / skKGap / skKLim OPEN L   (5 guard nodes PROVED S)
└ SkS.skSup REDUCED L ─ skVisK REDUCED L: skWin PROVED S, skGen REDUCED L
    ├ skUp REDUCED S ─ skUpRR REDUCED L (from SkF)
    ├ skForm REDUCED L: skFormWit REDUCED S ─ skNu REDUCED L (from SkF); skFormOther OPEN L
    └ skSupK REDUCED L
      ├ skMu PROVED L: skCodeCof PROVED S, skRead0 PROVED L (Wk.wkRead0)
      ├ skCarryWit REDUCED L: skOffMapW REDUCED M, skLowerF REDUCED M (skLowRR REDUCED L, from SkF),
      │   skBigF REDUCED M ─ skBigTop OPEN M, skImgF OPEN L   (skPiT PROVED M, skPiLo, skSideRef PROVED S)
      └ skCarryOther OPEN L
```

## Counts (166 nodes)

| part | PROVED | REDUCED | OPEN | SUSPECT | REFUTED | REPLACED | S | M | L |
|---|---|---|---|---|---|---|---|---|---|
| SkF | 42 | 28 | 13 | 0 | 1 | 15 | 35 | 35 | 29 |
| SkR | 13 | 6 | 5 | 0 | 1 | 0 | 11 | 5 | 9 |
| SkE | 8 | 4 | 4 | 0 | 0 | 0 | 8 | 0 | 8 |
| SkS | 7 | 14 | 4 | 0 | 0 | 0 | 6 | 5 | 14 |
| Root | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 1 |
| all | 70 | 53 | 26 | 0 | 2 | 15 | 60 | 45 | 61 |

OPEN by size: SkF M 3, L 10; SkR M 2, L 3; SkE L 4; SkS M 1, L 3; all S 0, M 6, L 20.
Sorry leaves (39): OPEN 26; REFUTED skTopDyn (M, kept for the record); REPLACED 12 with sorry (M; kept, not used:
skStepSucc / Pow / ExpLim / CoefLim, skStepPowW / ExpLimW / CoefLimW, skStepSuccG / PowG / CoefLimG / ExpLimG,
skSysA3Step). Three more REPLACED nodes (skStep, skStepG, skFamG) have no sorry of their own.
Round 116 → 117: sorry leaves 40 → 39, OPEN 34 → 26 (S 3 → 0, M 11 → 6, L 20 → 20), SUSPECT 1 → 0.

## REFUTED and SUSPECT

- **skTopDyn REFUTED M** (`R2.SkRXTop`): no single image X̂ fits e = 0 and e = 1; replaced by the law
  `Wg.WgTopFamAll` (image X̂_e depending on e).
- **skShapeNat_false REFUTED S** (`Wh.whShapeNat_false`, proved): with `e : ℕ` the shape leaf is false (Ω₁^ω).
- **skOldVacuous** (proved): the old package relation `Hn.HnkExt K' K` is vacuous when `K.g < K'.g`, and such a gate
  drop happens (gtc(Ω₁²) = 2 < ω = gtc(Ω₁·ω)); A1 now runs on `Wm.WmExt` (lowers by the pseudo-base gate).
- **skSysA3Step SUSPECT → confirmed, REPLACED** by skSysA3StepW: in A3, G is not a base (`skA3NoGBase`) and no
  `Hn.HnLv` holds an A3 level (`skA3NoBand`); the new invariant `SkPk3W` carries the full A3 package.
- **SkAtG REPLACED** by SkAtWG: same defect as SkAt (no start condition), and `Wh.WhAt` fails past ε_{Ω₁+1}.
- **skLowerF restated**: below the window of L(k) the old form (all μ) can fail (μ + f z may hit an index L(j),
  code P′); the new form asks for a window w < υ_μ.
- Risk notes (OPEN, not SUSPECT): skWallBase / skWallStep likely also need a B_n move of the images X̂;
  skWinA/B, skTopA/B are each as strong as "ν_C is not in that window"; skTopFam at e = 1 only reasoned, not in Lean.

## Suggested order of the next rounds

1. Frontier A1: skStepOm1W2 (first ℓ = Ω₁², then P + Ω₁^(e+1) and cf(e) = Ω₁); then A1 closes by `Wm.wmSysA1`.
2. Frontier A2: skStepPowWG, skStepCoefLimWG (ports of the A1 steps), skStepExpLimWG.
3. Supply: skBigTop (first decide r(ν) < υ_{ν+ω²}), skImgF, skFormOther, skCarryOther.
4. Reading: skTopFam (e = 0 at every base, then e = 1); skWallBase / skWallStep with the B_n move; skMidAssemble;
   skThFar.
5. Frontier A3: skSysA3Lev0W (port the Hn package stack to WnLv3), skSysA3StepW.
6. The L leaves tied to the main target: skRegBlo, skRegBhi, skLongPre, skWin*/skTop*, SkE skK*.
