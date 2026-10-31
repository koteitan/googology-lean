# R₂^C skeleton: status (round 121)

Root `R2Skel.Root.skNuC (S : InaccSeq)` = the conclusion of `Xb.xbRoad` (same as `Ww.wwRoad` / `Wd.wdRoadL`:
ν_C = L(ω+1), …). Round 121: the bridge `Ww.WwRealB` of `Ww.wwRoad` is SUSPECT as stated, so the root applies
`Xb.xbRoad` = `Ww.wwRoad` with `hB` replaced by the shift `Xb.XbShift S` and the supply by `Xb.XbVisGen`
(forms with constant ϑ-levels). Parts: frontier `SkF.skFront` → hUH/hLH/hVH/hVt; reading `SkR.skWall`,
`SkR.skThHi` → `SkE.skEQ` → hT/hF; supply `SkS.skShiftTh` → shift, `SkS.skSupX` → h0/hn.
The bundle SkF + SkR + SkE + SkS + Root checks against the main build with only `declaration uses sorry` warnings (45).

## Node tree (STATUS SIZE)

```
skNuC REDUCED L
├ SkF.skFront REDUCED L  (U/L/V/Vt REDUCED L; frontier F_A2, road `Wx.wxRoadA2`; region A2 CLOSED)
│ └ skAbove REDUCED L
│   ├ skRegA REDUCED L ─ skLocOfSys PROVED S, skSysCof REDUCED L
│   │ ├ skSysA1 PROVED M   (region A1 CLOSED)
│   │ ├ skSysA2 REDUCED L ─ skSysA2Lev PROVED M, skSysA3All REDUCED L; skBaseA2Hi PROVED L
│   │ └ skSysA3 REDUCED L ─ skSysA3All ─ skSysA3Lev ─ skSysA3LevW REDUCED L
│   │     skSysA3Lev0W REDUCED L ─ skA3QT0 REDUCED L ─ skA3T0Start OPEN L (a start of φ(t₀, G))
│   │       skA3Cls PROVED L, skA3TowPk1 PROVED L, skA3PkT0 PROVED M, skA3T0Q PROVED M (round 121)
│   │       skA3TowPk REPLACED (gate-0 data; by skA3TowPk1, gate 1)
│   │     skSysA3StepW OPEN L
│   │     skA3Band, skA3EntHn, skA3NoBand, skA3StepLow, skA3NoGBase, skA3Datum0 PROVED S; skA3Tow PROVED M
│   ├ skRegB REDUCED L    skRegBlo OPEN L, skRegBhi OPEN L, skWinA / skWinB OPEN L, skTopA / skTopB OPEN L
│   └ skRegC REDUCED L    skLongPre OPEN L; skLongMid, skLongTop PROVED S (vacuous)
├ SkR.skWall REDUCED L ─ skWallCF REDUCED L ─ skWallLow REDUCED L
│ │ skThCof PROVED S, skWallLevAll REDUCED L: skTopFam OPEN M, skWallBase OPEN L, skWallStep OPEN L
│ │ image law: skX0LawDK OPEN L (bases β ∈ D; replaces the REFUTED skX0Law)
│ │   skX0LawD PROVED M (k = 0, every β ∈ D), skX0Law1 PROVED M (k = 1, β = 0), skX0Ref PROVED S
│ │   skUpU PROVED L (round 121), so skX0Om3 PROVED S; skX0LowOm3, skX0Om3Iff PROVED
│ └ skWallTh PROVED M
├ SkR.skThHi REDUCED L: skThMid REDUCED M, skThFar OPEN L
│   (side: skMidAssemble SUSPECT M, off the road; skTopDyn REFUTED M)
├ SkE.skEQ REDUCED L
│ ├ skThLow REDUCED L
│ └ skEQfar REDUCED L: skThFar OPEN L, skKFar REDUCED L: skKClosed / skKGap / skKLim OPEN L
├ SkS.skShiftTh OPEN L  (`Xb.XbShift`: vlShiftCore + the ϑ-node clause at constant levels B₂ ≤ Ω₁·M < θ)
│   skRealBX REDUCED L (from skShiftTh, `Xb.xbRealB`); skImgGap PROVED S (gap witness has a valid image)
└ SkS.skSupX REDUCED L ─ skVisKX REDUCED L: skWin PROVED S, skGenX REDUCED L
    ├ skUp REDUCED S ─ skUpRR REDUCED L (from SkF)
    ├ skFormX REDUCED L: skFormEps REDUCED M, skFormHighX OPEN L (forms with constant ϑ-levels)
    └ skSupKW OPEN L (carry of the ϑ-node images)
    off the road since round 121: skSupW REDUCED (from skSupX), skVisKW, skGenW REDUCED,
      skFormW, skFormHighW PROVED (`Xa.xaForm_all`: every countable x < υ_{λ+β} has a repaired form), skRealB SUSPECT
    off the road since round 120: skSupK, skCarryWit, skCarryEps, skCarryOther REDUCED; skImgEps, skCarryHigh OPEN L
```

## Counts (264 nodes)

| part | PROVED | REDUCED | OPEN | SUSPECT | REFUTED | REPLACED | S | M | L |
|---|---|---|---|---|---|---|---|---|---|
| SkF | 97 | 22 | 9 | 0 | 1 | 27 | 57 | 60 | 39 |
| SkR | 26 | 7 | 5 | 1 | 2 | 0 | 19 | 9 | 13 |
| SkE | 8 | 4 | 4 | 0 | 0 | 0 | 8 | 0 | 8 |
| SkS | 21 | 23 | 5 | 1 | 0 | 0 | 14 | 10 | 26 |
| Root | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 1 |
| all | 152 | 57 | 23 | 2 | 3 | 27 | 98 | 79 | 87 |

OPEN by size: SkF L 9; SkR M 1, L 4; SkE L 4; SkS L 5; all S 0, M 1, L 22 (skThFar is counted in SkR and SkE;
skImgEps and skCarryHigh are off the road, so 20 distinct OPEN nodes are on the road).
Sorry leaves (45): OPEN 23; SUSPECT skMidAssemble (M), skRealB (L); REFUTED skTopDyn (M), skX0Law (L), kept for the
record; REPLACED 18 with sorry (kept, not used).
Round 120 → 121: sorry leaves 44 → 45, OPEN 25 → 23 (M 1 → 1, L 24 → 22), SUSPECT 1 → 2, REFUTED 2 → 3,
nodes 247 → 264.

## REFUTED and SUSPECT

- **skX0Law REFUTED L** (`Xd.xdX0Law_false`): outside its domain D the map T = vbT gives 0, so at the base β = Ω_ω
  the image is Y₂ and a lift gives ψ₁(A+θ+z₂) with z₂ > Y₂, against the law's value ψ₁(A+θ+Y₂). Replaced by
  skX0LawDK (β ∈ D), which holds at k = 0 (skX0LawD) and at k = 1, β = 0 (skX0Law1).
- **skRealB SUSPECT L**: `Ww.WwCarry` bounds images only under `Ww.WwR` (data of every ϑ-level below υ_μ), but
  `Ww.WwWF` allows ϑ-levels with data in [υ_λ, υ_{λ+h}); for such a form the carry gives no bound. Off the road.
- **skMidAssemble SUSPECT M**: its hypothesis `Wd.WdAtWall` covers only F_W ≤ m_λ < θ⁺; replaced by skMidCF.
- **skTopDyn REFUTED M** (`R2.SkRXTop`): no single image X̂ fits e = 0 and e = 1; replaced by `Wg.WgTopFamAll`.
- **skShapeNat_false REFUTED S** (`Wh.whShapeNat_false`): with `e : ℕ` the shape leaf is false (Ω₁^ω).
- Earlier: the road `Wf.wfRoad` is void (`Ww.wwRoad_false`); skA3NoBandOld (`Wy.wyNoBand_false`); skImgF and the
  naive image formula (`Wv.wvNoT`) stay refuted.
- Risk notes: skWinA/B, skTopA/B are each as strong as "ν_C is not in that window".

## Suggested order of the next rounds

1. Supply: skShiftTh (cite the translation twin of `uvVt_trL` on [B₂, θ), case Γ^* < α; redo the UyFix node lemmas
   below θ; port FRAG to constant levels), skFormHighX (as `Xa.xaRep`, keeping ϑ-levels constant), skSupKW (reach
   values at the restart μ in the high windows; image = base change at ϑ-nodes for M ≥ B₂; the choice of (f, B)).
2. Frontier A3: skA3T0Start (all of region A3 below φ(t₀, G): pseudo-bases φ(ℓ, ν) and their starts at every
   level ℓ ≤ t₀; first the level G over the datum G); then skSysA3StepW.
3. Reading: skX0LawDK at k = 1 for every β ∈ D (a base-relative `Vn.vnPsi2_eq`), then k → k+1; skTopFam for e ≥ 1;
   skWallBase / skWallStep; skThFar.
4. The L leaves tied to the main target: skRegBlo, skRegBhi, skLongPre, skWin*/skTop*, SkE skK*.
