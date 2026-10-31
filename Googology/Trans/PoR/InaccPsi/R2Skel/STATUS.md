# R₂^C skeleton: status (round 118)

Root `R2Skel.Root.skNuC (S : InaccSeq)` = the conclusion of `Wf.wfRoad` (same as `Wd.wdRoadL`: ν_C = L(ω+1), …),
whose supply hypotheses h0/hn are `Wf.WfVisGen`. Parts: frontier `SkF.skFront` → hUH/hLH/hVH/hVt; reading
`SkR.skWall`, `SkR.skThHi` → `SkE.skEQ` → hT/hF; supply `SkS.skSup` → h0/hn. Root and the top nodes are unchanged.
The bundle SkF + SkE + SkR + SkS + Root checks against the main build with only `declaration uses sorry` warnings (39).

## Node tree (STATUS SIZE)

```
skNuC REDUCED L
├ SkF.skFront REDUCED L  (U/L/V/Vt REDUCED L; skRoad REDUCED L; skHypIff PROVED S)
│ │   frontier moved: skSysE, skLocE, skHypIffE PROVED (ι(Γ(φ(ε_{Ω₁+1}, G+1))·ω), road `Wo.woRoad`)
│ └ skAbove REDUCED L
│   ├ skRegA REDUCED L ─ skLocOfSys PROVED S, skSysCof REDUCED L
│   │ ├ skSysA1 PROVED M   ℓ < ε_{Ω₁+1}: skSysAll, skFam PROVED M (region A1 CLOSED)
│   │ │   skStepAllWo PROVED M, skStepOm1Wo PROVED L (cofinality Ω₁), skFs1, skFamW2 PROVED M
│   │ │   (skStepBaseW2 … skStepExpLimFsW2 PROVED; skStepOm1W2, skStepW2 REPLACED)
│   │ ├ skSysA2 REDUCED L   [φ(E, G+1), φ(G, 1)): skSysA2Lev REDUCED M ─ skSysAllG REDUCED M
│   │ │ └ skFamWG2 ─ skStepWG2 REDUCED M (on SkCohWG2 = Wp.WpCoh: Wn.WnAt, Wm.WmExtE)
│   │ │     skStepBaseWG2, skStepExpLimFsWG2, skStepBnWG2 PROVED S; skStepSuccWG2, skStepFsWG2,
│   │ │     skStepCoefLimWG2 PROVED M; skFamSqG PROVED M; skStepOm1WG2 OPEN L (cofinality Ω₁)
│   │ │     (skGateDropG, skCohWG2_old, skLevG_Bn, skGateBn PROVED S; old A2 steps REPLACED)
│   │ └ skSysA3 REDUCED L ─ skSysA3All ─ skSysA3Lev ─ skSysA3LevW REDUCED L (on SkPk3W = Wn.WnEnt3)
│   │     skSysA3Lev0W OPEN L, skSysA3StepW OPEN L; skA3NoBand, skA3NoGBase, skA3Datum0, skPk3_of_W PROVED S
│   ├ skRegB REDUCED L    (Wj.wjRegB_iff): skRegBlo OPEN L, skRegBhi OPEN L,
│   │   skWin: skWinA / skWinB OPEN L; skTop: skTopA / skTopB OPEN L
│   └ skRegC REDUCED L    skLongPre OPEN L; skLongMid, skLongTop PROVED S (vacuous)
├ SkR.skWall REDUCED L
│ ├ skWallLow REDUCED L: skThCof PROVED S, skWallLevAll REDUCED L
│ │   skTopFam OPEN M (skTopFam0, skTopSep PROVED S), skWallBase OPEN L, skWallStep OPEN L (code-free)
│ ├ skWallCF REDUCED L (the wall with no code hypothesis)
│ └ skWallTh PROVED M: skThVal PROVED S (skThUp PROVED S, skThLow PROVED L), skThAtom PROVED S
├ SkR.skThHi REDUCED L: skThMid REDUCED M (skBlkLaw PROVED S, skMidCF PROVED M by Wr.wrMid), skThFar OPEN L
│   (side: skRead REDUCED L; skLowExp, skBelowThP, skRead_of_EQ, skNonVac PROVED S;
│    skMidAssemble SUSPECT M, off the road; skTopDyn REFUTED M)
├ SkE.skEQ REDUCED L
│ ├ skThLow REDUCED L: skThLow_of PROVED S
│ └ skEQfar REDUCED L: skEQfar_of PROVED S, skThFar OPEN L, skKFar REDUCED L
│     skKFar_of PROVED S, skKClosed / skKGap / skKLim OPEN L   (5 guard nodes PROVED S)
└ SkS.skSup REDUCED L ─ skVisK REDUCED L: skWin PROVED S, skGen REDUCED L
    ├ skUp REDUCED S ─ skUpRR REDUCED L (from SkF)
    ├ skForm REDUCED L: skFormWit REDUCED S ─ skNu REDUCED L (from SkF)
    │   skFormOther REDUCED L: skFormEps REDUCED M (below ε_{u₁+1}), skFormHigh OPEN L
    └ skSupK REDUCED L
      ├ skMu PROVED L: skCodeCof PROVED S, skRead0 PROVED L (Wk.wkRead0)
      ├ skCarryWit REDUCED L ─ skCarryEps REDUCED L: skImgEps OPEN L; skEpsU2, skWitEps PROVED S
      │   (skImgF_ref PROVED L, skImgF_false PROVED S; skOffMapW, skLowerF, skBigF, skBigTop off the road)
      └ skCarryOther REDUCED L: skCarryEps, skCarryHigh OPEN L
```

## Counts (195 nodes)

| part | PROVED | REDUCED | OPEN | SUSPECT | REFUTED | REPLACED | S | M | L |
|---|---|---|---|---|---|---|---|---|---|
| SkF | 61 | 24 | 10 | 0 | 1 | 22 | 42 | 45 | 31 |
| SkR | 14 | 7 | 4 | 1 | 1 | 0 | 11 | 6 | 10 |
| SkE | 8 | 4 | 4 | 0 | 0 | 0 | 8 | 0 | 8 |
| SkS | 11 | 19 | 3 | 0 | 0 | 0 | 9 | 6 | 18 |
| Root | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 1 |
| all | 94 | 55 | 21 | 1 | 2 | 22 | 70 | 57 | 68 |

OPEN by size: SkF L 10; SkR M 1, L 3; SkE L 4; SkS L 3; all S 0, M 1, L 20 (skThFar is counted in SkR and SkE).
Sorry leaves (39): OPEN 21; SUSPECT skMidAssemble (M); REFUTED skTopDyn (M, kept for the record); REPLACED 16 with
sorry (15 M, skStepOm1W2 L; kept, not used). The refuted `skImgF` was removed (its refutation is skImgF_false).
Round 117 → 118: sorry leaves 39 → 39, OPEN 26 → 21 (M 6 → 1, L 20 → 20), SUSPECT 0 → 1, REPLACED 12 → 16.

## REFUTED and SUSPECT

- **skImgF REFUTED L** (`Wq.wqImgF_ref`, node skImgF_false): `SkMapP` leaves f(z) free when m(z) ≥ u₁; with
  z = ω^{u₁}, f(z) = ω² the image exceeds r(μ+ω²). Replaced by skImgEps (one map f, ∃, instead of every map).
- **skMidAssemble SUSPECT M**: its hypothesis `Wd.WdAtWall` covers only F_W ≤ m_λ < θ⁺, but the move asks m_λ ≥ θ⁺.
  Replaced by skMidCF on the code-free wall `Wr.WrWallCF` (a stronger hypothesis, open in skWallBase / skWallStep).
- **skTopDyn REFUTED M** (`R2.SkRXTop`): no single image X̂ fits e = 0 and e = 1; replaced by `Wg.WgTopFamAll`.
- **skShapeNat_false REFUTED S** (`Wh.whShapeNat_false`, proved): with `e : ℕ` the shape leaf is false (Ω₁^ω).
- **Old A2 steps REPLACED** (skStepPowWG, skStepCoefLimWG, skStepExpLimWG): they sit on `Hn.HnkExt`, vacuous across a
  gate drop, and gate drops occur in A2 (glG(Ω₁·Ω₁) = 2 < ω = glG(Ω₁·ω), `Wp.wp_gate_drop`).
- **skStepOm1W2 REPLACED**: A1 is proved by families over all base data (`Wo.woFam`), no gate condition needed.
- Risk notes: adding the image move as a hypothesis to the wall steps is circular (`Wr.wrImgMove_iff`);
  skWinA/B, skTopA/B are each as strong as "ν_C is not in that window"; skTopFam at e = 1 only reasoned.

## Suggested order of the next rounds

1. Frontier A2: skStepOm1WG2 = `Wp.WpOm1Step G`: cut the A1 Ω₁-step (`Wo.woStep_om1`) into an interface over any
   entry predicate, instantiate with glR, glG, wnGW, WnAt, and add the Ω₁-sequences of Veblen exponents.
2. Supply: skImgEps (code move for u₁ ≤ m(z) < ε_{u₁+1}; image depends only on the value), then skFormHigh,
   skCarryHigh.
3. Reading: skWallBase / skWallStep (an intrinsic formula for the images X̂_e(β)); skTopFam; skThFar.
4. Frontier A3: skSysA3Lev0W (port the Hn package stack to WnLv3), skSysA3StepW.
5. The L leaves tied to the main target: skRegBlo, skRegBhi, skLongPre, skWin*/skTop*, SkE skK*.
