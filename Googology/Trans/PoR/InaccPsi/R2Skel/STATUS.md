# R₂^C skeleton: status (round 120)

Root `R2Skel.Root.skNuC (S : InaccSeq)` = the conclusion of `Ww.wwRoad` (same as `Wf.wfRoad` / `Wd.wdRoadL`:
ν_C = L(ω+1), …). Round 120: `Wf.wfRoad` is void (its hypotheses are jointly false, `Ww.wwRoad_false`), so the
root now applies the repaired road `Ww.wwRoad`, whose supply hypotheses are `Ww.WwVisGen` plus the bridge
`Ww.WwRealB`. Parts: frontier `SkF.skFront` → hUH/hLH/hVH/hVt; reading `SkR.skWall`, `SkR.skThHi` → `SkE.skEQ`
→ hT/hF; supply `SkS.skRealB` → hB, `SkS.skSupW` → h0/hn.
The bundle SkF + SkR + SkE + SkS + Root checks against the main build with only `declaration uses sorry` warnings (44).

## Node tree (STATUS SIZE)

```
skNuC REDUCED L
├ SkF.skFront REDUCED L  (U/L/V/Vt REDUCED L; skRoad REDUCED L; skHypIff PROVED S)
│ │   frontier moved to the end of A2: skLocA2, skHypIffA2, skSysA2V, skFA2Where PROVED
│ │   (F_A2 = sup_n ι(Γ(φ(glBn n, G+1))·ω) ≤ ι(Γ(φ(G, 1))), road `Wx.wxRoadA2`)
│ └ skAbove REDUCED L
│   ├ skRegA REDUCED L ─ skLocOfSys PROVED S, skSysCof REDUCED L
│   │ ├ skSysA1 PROVED M   ℓ < ε_{Ω₁+1} (region A1 CLOSED)
│   │ ├ skSysA2 REDUCED L ─ skSysA2Lev PROVED M, skSysA3All REDUCED L (the rest of skSysA2 is A3)
│   │ │   region A2 CLOSED: skBaseA2Hi PROVED L (one proof for every Veblen level), skBaseA2 PROVED L,
│   │ │   skClsA2, skSysAllG2 PROVED M; skRefuteA2Hi PROVED S
│   │ └ skSysA3 REDUCED L ─ skSysA3All ─ skSysA3Lev ─ skSysA3LevW REDUCED L (on SkPk3W = Wn.WnEnt3)
│   │     skSysA3Lev0W REDUCED L ─ skA3TowPk OPEN L, skA3QT0 OPEN L (by `Wy.wyEnt3_of`)
│   │     skSysA3StepW OPEN L
│   │     skA3Band, skA3EntHn, skA3NoBandOld PROVED S; skA3NoBand PROVED (restated with `Hn.HnLvG`)
│   │     skA3DatumAll, skA3Tow PROVED M; skA3StepLow, skA3NoGBase, skA3Datum0 PROVED S
│   ├ skRegB REDUCED L    (Wj.wjRegB_iff): skRegBlo OPEN L, skRegBhi OPEN L,
│   │   skWin: skWinA / skWinB OPEN L; skTop: skTopA / skTopB OPEN L
│   └ skRegC REDUCED L    skLongPre OPEN L; skLongMid, skLongTop PROVED S (vacuous)
├ SkR.skWall REDUCED L
│ ├ skWallLow REDUCED L: skThCof PROVED S, skWallLevAll REDUCED L
│ │   skTopFam OPEN M (skTopFam0, skTopSep PROVED S), skWallBase OPEN L, skWallStep OPEN L
│ │   images: skImgLtTh, skNaiveT, skImg1Gt, skX0Tests, skX0Tests2 PROVED S
│ │   skX0Law OPEN L (candidate, not used yet); at k = 0, β = Ω₃: skX0LowOm3 PROVED (lower half),
│ │   skX0Om3Iff PROVED S, skX0Om3 REDUCED S ─ skUpU OPEN L (upper half, `Wz.WzUpU`)
│ ├ skWallCF REDUCED L
│ └ skWallTh PROVED M: skThVal PROVED S (skThUp PROVED S, skThLow PROVED L), skThAtom PROVED S
├ SkR.skThHi REDUCED L: skThMid REDUCED M (skBlkLaw PROVED S, skMidCF PROVED M), skThFar OPEN L
│   (side: skRead REDUCED L; skMidAssemble SUSPECT M, off the road; skTopDyn REFUTED M)
├ SkE.skEQ REDUCED L
│ ├ skThLow REDUCED L: skThLow_of PROVED S
│ └ skEQfar REDUCED L: skEQfar_of PROVED S, skThFar OPEN L, skKFar REDUCED L
│     skKFar_of PROVED S, skKClosed / skKGap / skKLim OPEN L   (5 guard nodes PROVED S)
├ SkS.skRealB OPEN L  (realizer bridge `Ww.WwRealB`: ϑ-nodes at levels M ≥ B₂)
└ SkS.skSupW REDUCED L ─ skVisKW REDUCED L: skWin PROVED S, skGenW REDUCED L
    ├ skUp REDUCED S ─ skUpRR REDUCED L (from SkF)
    ├ skFormW REDUCED L: skFormEps REDUCED M (old forms are new forms, `Ww.wwForm_of_vr`),
    │   skFormHighW OPEN L (new form with ϑ-nodes in the high window)
    └ skSupKW OPEN L (carry of the ϑ-node images; implies the old skSupK by `Ww.wwSup_wf`)
    refutations: skGapW PROVED (the gap always holds, `Ww.wwGap`), skFormHigh_false, skSup_false PROVED
    off the road since round 120: skSupK, skCarryWit, skCarryEps, skCarryOther REDUCED; skImgEps, skCarryHigh OPEN L
```

## Counts (247 nodes)

| part | PROVED | REDUCED | OPEN | SUSPECT | REFUTED | REPLACED | S | M | L |
|---|---|---|---|---|---|---|---|---|---|
| SkF | 93 | 21 | 10 | 0 | 1 | 26 | 57 | 58 | 36 |
| SkR | 21 | 8 | 6 | 1 | 1 | 0 | 18 | 7 | 12 |
| SkE | 8 | 4 | 4 | 0 | 0 | 0 | 8 | 0 | 8 |
| SkS | 18 | 19 | 5 | 0 | 0 | 0 | 13 | 10 | 19 |
| Root | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 1 |
| all | 140 | 53 | 25 | 1 | 2 | 26 | 96 | 75 | 76 |

OPEN by size: SkF L 10; SkR M 1, L 5; SkE L 4; SkS L 5; all S 0, M 1, L 24 (skThFar is counted in SkR and SkE;
skImgEps and skCarryHigh are off the road, so 22 distinct OPEN nodes are on the road).
Sorry leaves (44): OPEN 25; SUSPECT skMidAssemble (M); REFUTED skTopDyn (M, kept for the record);
REPLACED 17 with sorry (15 M; skStepOm1W2, skStepOm1WG2 L; kept, not used).
Round 119 → 120: sorry leaves 42 → 44, OPEN 22 → 25 (M 2 → 1, L 20 → 24), SUSPECT 2 → 1, nodes 229 → 247.

## REFUTED and SUSPECT

- **Supply road `Wf.wfRoad` REFUTED** (`Ww.wwRoad_false`, `Ww.wwRoadZ_false`, node skSup_false): the gap holds at
  every k with the ε-number X = ϑ^{u₁}(B₂ + λ) in (u₁, u₂), so no old form ends in X (skFormHigh_false). Repaired by
  the forms `Ww.WwE` with ϑ-nodes (X has such a form, `Ww.wwForm_X`) and the road `Ww.wwRoad`.
- **skA3NoBandOld** (`Wy.wyNoBand_false`): after widening `Hn.HnLv`, "every band level datum lies below t₀" is false;
  skA3NoBand is restated with `Hn.HnLvG`.
- **skMidAssemble SUSPECT M**: its hypothesis `Wd.WdAtWall` covers only F_W ≤ m_λ < θ⁺; replaced by skMidCF.
- **skTopDyn REFUTED M** (`R2.SkRXTop`): no single image X̂ fits e = 0 and e = 1; replaced by `Wg.WgTopFamAll`.
- **skShapeNat_false REFUTED S** (`Wh.whShapeNat_false`): with `e : ℕ` the shape leaf is false (Ω₁^ω).
- skImgF (`Wq.wqImgF_ref`) and the naive image formula (`Wv.wvNoT`, skNaiveT) stay refuted.
- Risk notes: skWinA/B, skTopA/B are each as strong as "ν_C is not in that window"; skX0Law is only tested.

## Suggested order of the next rounds

1. Supply: skFormHighW (new forms in the high window), skSupKW (carry of ϑ-node images), skRealB (needs the
   translations of [W07a] Def 6.2 / Lemma 6.3 at levels ≥ B₂). Until these hold, `Ww.wwRoad` is not shown non-void.
2. Frontier A3: skA3TowPk (A3 code interface from `Wt.wtD`, its classification, the family at the tower levels),
   skA3QT0 (pseudo-base φ(t₀, G) with a start); then skSysA3StepW.
3. Reading: skUpU (transfer lemma a' ∈ Cl(a, ψ₂(a)) ⇒ T a' ∈ Cl(T a, ψ₂(T a))), skX0Law at every β and at
   k = 1, the e = 1 law, then skWallBase / skWallStep; skThFar.
4. The L leaves tied to the main target: skRegBlo, skRegBhi, skLongPre, skWin*/skTop*, SkE skK*.
