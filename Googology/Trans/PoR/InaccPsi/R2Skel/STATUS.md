# R₂^C skeleton: status (round 119)

Root `R2Skel.Root.skNuC (S : InaccSeq)` = the conclusion of `Wf.wfRoad` (same as `Wd.wdRoadL`: ν_C = L(ω+1), …),
whose supply hypotheses h0/hn are `Wf.WfVisGen`. Parts: frontier `SkF.skFront` → hUH/hLH/hVH/hVt; reading
`SkR.skWall`, `SkR.skThHi` → `SkE.skEQ` → hT/hF; supply `SkS.skSup` → h0/hn. Root and the top nodes are unchanged.
The bundle SkF + SkR + SkE + SkS + Root checks against the main build with only `declaration uses sorry` warnings (42).

## Node tree (STATUS SIZE)

```
skNuC REDUCED L
├ SkF.skFront REDUCED L  (U/L/V/Vt REDUCED L; skRoad REDUCED L; skHypIff PROVED S)
│ │   frontier moved: skLocZ, skHypIffZ, skSysZV PROVED (F_Z = ι(Γ(φ(ζ_{Ω₁+1}, G+1))·ω), road `Ws.wsRoadZ`)
│ └ skAbove REDUCED L
│   ├ skRegA REDUCED L ─ skLocOfSys PROVED S, skSysCof REDUCED L
│   │ ├ skSysA1 PROVED M   ℓ < ε_{Ω₁+1} (region A1 CLOSED; re-proved by the generic interface: skA1Check, skA1SysCheck)
│   │ ├ skSysA2 REDUCED L ─ skSysA2Lev REDUCED M ─ skBaseA2 REDUCED L (code interface `Ws.WsC`, instance `Ws.wsA2`)
│   │ │   skStepOm1Ws PROVED L (generic Ω₁-cofinal step); skClsA2, skSysAllG2 REDUCED M
│   │ │   levels ≤ ζ_{Ω₁+1}: skBaseZ, skClsZ, skSysZ PROVED M (also skBaseW, skClsW, skSysW at ε_{Ω₁+ω})
│   │ │   skBaseA2Hi OPEN L: ε-number codes e in (ζ_{Ω₁+1}, G), Veblen level ≥ 2
│   │ │   (skGlGNoFsE PROVED S; skStepOm1WG2, skStepWG2, skFamWG2, skSysAllG REPLACED)
│   │ └ skSysA3 REDUCED L ─ skSysA3All ─ skSysA3Lev ─ skSysA3LevW REDUCED L (on SkPk3W = Wn.WnEnt3)
│   │     skSysA3Lev0W OPEN L, skSysA3StepW OPEN L; skA3DatumAll, skA3Tow PROVED M; skA3StepLow PROVED S
│   │     (skA3NoBand, skA3NoGBase, skA3Datum0, skPk3_of_W PROVED S)
│   ├ skRegB REDUCED L    (Wj.wjRegB_iff): skRegBlo OPEN L, skRegBhi OPEN L,
│   │   skWin: skWinA / skWinB OPEN L; skTop: skTopA / skTopB OPEN L
│   └ skRegC REDUCED L    skLongPre OPEN L; skLongMid, skLongTop PROVED S (vacuous)
├ SkR.skWall REDUCED L
│ ├ skWallLow REDUCED L: skThCof PROVED S, skWallLevAll REDUCED L
│ │   skTopFam OPEN M (skTopFam0, skTopSep PROVED S), skWallBase OPEN L, skWallStep OPEN L (code-free)
│ │   images: skImgLtTh, skNaiveT, skImg1Gt, skX0Tests PROVED S; skX0Law OPEN L (candidate X̂⁰_k(β), not used yet)
│ ├ skWallCF REDUCED L (the wall with no code hypothesis)
│ └ skWallTh PROVED M: skThVal PROVED S (skThUp PROVED S, skThLow PROVED L), skThAtom PROVED S
├ SkR.skThHi REDUCED L: skThMid REDUCED M (skBlkLaw PROVED S, skMidCF PROVED M), skThFar OPEN L
│   (side: skRead REDUCED L; skMidAssemble SUSPECT M, off the road; skTopDyn REFUTED M)
├ SkE.skEQ REDUCED L
│ ├ skThLow REDUCED L: skThLow_of PROVED S
│ └ skEQfar REDUCED L: skEQfar_of PROVED S, skThFar OPEN L, skKFar REDUCED L
│     skKFar_of PROVED S, skKClosed / skKGap / skKLim OPEN L   (5 guard nodes PROVED S)
└ SkS.skSup REDUCED L ─ skVisK REDUCED L: skWin PROVED S, skGen REDUCED L
    ├ skUp REDUCED S ─ skUpRR REDUCED L (from SkF)
    ├ skForm REDUCED L: skFormWit REDUCED S ─ skNu REDUCED L (from SkF)
    │   skFormOther REDUCED L: skFormEps REDUCED M, skFormHigh SUSPECT L (skHighWin REDUCED)
    │   refutation side: skFormHigh_ref, skRoadRef PROVED (conditional on skGap); skGap OPEN M, off the road
    └ skSupK REDUCED L
      ├ skMu PROVED L: skCodeCof PROVED S, skRead0 PROVED L
      ├ skCarryWit REDUCED L ─ skCarryEps REDUCED L: skImgEps OPEN L (supply piece skSupEps PROVED,
      │   skImgVal PROVED); skEpsU2, skWitEps PROVED S; skImgF_ref, skImgF_false PROVED
      └ skCarryOther REDUCED L: skCarryEps, skCarryHigh OPEN L
```

## Counts (229 nodes)

| part | PROVED | REDUCED | OPEN | SUSPECT | REFUTED | REPLACED | S | M | L |
|---|---|---|---|---|---|---|---|---|---|
| SkF | 80 | 24 | 10 | 0 | 1 | 26 | 50 | 57 | 34 |
| SkR | 18 | 7 | 5 | 1 | 1 | 0 | 15 | 6 | 11 |
| SkE | 8 | 4 | 4 | 0 | 0 | 0 | 8 | 0 | 8 |
| SkS | 15 | 20 | 3 | 1 | 0 | 0 | 12 | 9 | 18 |
| Root | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 1 |
| all | 121 | 56 | 22 | 2 | 2 | 26 | 85 | 72 | 72 |

OPEN by size: SkF L 10; SkR M 1, L 4; SkE L 4; SkS M 1, L 2; all S 0, M 2, L 20 (skThFar is counted in SkR and SkE).
Sorry leaves (42): OPEN 22; SUSPECT skMidAssemble (M), skFormHigh (L); REFUTED skTopDyn (M, kept for the record);
REPLACED 17 with sorry (15 M; skStepOm1W2, skStepOm1WG2 L; kept, not used).
Round 118 → 119: sorry leaves 39 → 42, OPEN 21 → 22 (M 1 → 2, L 20 → 20), SUSPECT 1 → 2, REPLACED 22 → 26.

## REFUTED and SUSPECT

- **skStepOm1WG2 route REFUTED, node REPLACED** (`Ws.ws_glG_E_noFs`): ε_{Ω₁+1} is an A2 level with no gated
  ω-sequence and no Ω₁-sequence (glG = 0 there, ≥ 1 below). Replaced by the generic family with gate max 1 (glG).
- **skFormHigh SUSPECT L** (`Wu.wuVis_ref`, `Wu.wuRoad_vac`): if `WuGap` (skGap) holds, an ε-number X in (u₁, u₂)
  has a reach no repaired form can end in, so skFormHigh and `WfVisGen` fail at L(k), and `Wf.wfRoad` is vacuous.
- **skMidAssemble SUSPECT M**: its hypothesis `Wd.WdAtWall` covers only F_W ≤ m_λ < θ⁺; replaced by skMidCF.
- **skTopDyn REFUTED M** (`R2.SkRXTop`): no single image X̂ fits e = 0 and e = 1; replaced by `Wg.WgTopFamAll`.
- **skImgF REFUTED** (`Wq.wqImgF_ref`): the map f is too small, not the decomposition (`Wu.wuImg_test`).
- **skShapeNat_false REFUTED S** (`Wh.whShapeNat_false`): with `e : ℕ` the shape leaf is false (Ω₁^ω).
- Naive image formula T(ψ_{Ω_{k+3}}(β+Ω_{k+3})) REFUTED for every k ≥ 1 (`Wv.wvNoT`, node skNaiveT).
- Risk notes: skWinA/B, skTopA/B are each as strong as "ν_C is not in that window"; skX0Law is only tested.

## Suggested order of the next rounds

1. Supply: skGap (decides whether `Wf.wfRoad` survives): WuGap at X = ϑ^{u₁}(B₂ + υ_λ). If it holds, repair the
   supply forms; if it fails, prove skFormHigh. Then skImgEps, skCarryHigh.
2. Frontier A2: skBaseA2Hi (bracket comparison across Veblen levels, iterates of φ(α′, ·), α-limit cases).
3. Frontier A3: widen `Hn.HnLv` (L < Γ(1), ℓ(x) < Γ_{x+2}), the Wo family over A3 raw data, the ω-limit at t₀
   along skA3Tow, the pseudo-base φ(t₀, G); then skSysA3Lev0W, skSysA3StepW.
4. Reading: skX0Law (k = 0, β = Ω₃; k = 1, β = 0), the e = 1 formula, then skWallBase / skWallStep; skThFar.
5. The L leaves tied to the main target: skRegBlo, skRegBhi, skLongPre, skWin*/skTop*, SkE skK*.
