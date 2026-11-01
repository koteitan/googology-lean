# R₂^C skeleton: status (round 122)

Root `R2Skel.Root.skNuC (S : InaccSeq)` = the conclusion of `Xb.xbRoad` (same as `Ww.wwRoad` / `Wd.wdRoadL`:
ν_C = L(ω+1), …), with the shift `Xb.XbShift S` and the supply `Xb.XbVisGen`. Parts: frontier `SkF.skFront` →
hUH/hLH/hVH/hVt; reading `SkR.skWall`, `SkR.skThHi` → `SkE.skEQ` → hT/hF; supply `SkS.skShiftTh` → shift,
`SkS.skSupX` → h0/hn. No top statement and no road changed in round 122.
The bundle SkF + SkR + SkE + SkS + Root checks against the main build with only `declaration uses sorry` warnings (47).

## Main progress number: OPEN / SUSPECT leaves on the road from `Root.skNuC`

**21 distinct OPEN leaves, all L; 0 SUSPECT** (round 121: 20 = L 19 + M 1). Counted by walking the constants used by
`skNuC`. On the road: SkF skA3T0Start, skSysA3StepW, skLayLo, skLayHi, skBhiA, skBhiL, skWinA, skWinL, skTopA,
skTopL, skLongPre; SkR skTopUp, skWallBase, skWallStep, skThFar; SkE skThFar, skKCof, skKReachR; SkS skShiftThHi,
skFormHighX, skSupKW. The M leaf skX0LawDK is now PROVED; region B gave 6 L leaves for 4 (finer, not closed).

## Node tree (STATUS SIZE)

```
skNuC REDUCED L
├ SkF.skFront REDUCED L  (U/L/V/Vt REDUCED L; regions A1, A2 CLOSED; A3 level G built to φ(G, Γ₀))
│ └ skAbove REDUCED L
│   ├ skRegA REDUCED L ─ skLocOfSys PROVED S, skSysCof REDUCED L
│   │ ├ skSysA1 PROVED M
│   │ ├ skSysA2 REDUCED L ─ skSysA2Lev PROVED M, skSysA3G PROVED S (systems below φ(G, Γ₀)), skSysA3All
│   │ │   skA3G1 PROVED M (start of φ(G, 1)), skA3GOff PROVED L (starts of φ(G, ν), ν < Γ₀)
│   │ │   skLocG, skFGWhere, skHypIffG PROVED S (frontier F_G = sup_{ν<Γ₀} ι(Γ(φ(G, ν))·ω), road `Xf.xfRoadZ`)
│   │ └ skSysA3 REDUCED L ─ skSysA3All ─ skSysA3Lev ─ skSysA3LevW REDUCED L
│   │     skSysA3Lev0W REDUCED L ─ skA3QT0 REDUCED L ─ skA3T0Start OPEN L (a start of φ(t₀, G))
│   │     skSysA3StepW OPEN L
│   ├ skRegB REDUCED L  (cells: base β ∈ {0, Ω₂·q, b_k, b_ω} + offset ζ < Ω₂; skBhiName, skWinOff PROVED S)
│   │ ├ skRegBlo REDUCED L ─ skLay REDUCED L: skLayLo OPEN L, skLayHi OPEN L
│   │ │   skLayExists, skLayLevCof, skLayExact PROVED S; side: skL1Img OPEN M (IMG below Γ_{ρ+3})
│   │ ├ skRegBhi REDUCED L: skBhiA OPEN L, skBhiL OPEN L (skBhiNonempty PROVED S)
│   │ ├ skWinA OPEN L; skWinB REDUCED L ─ skWinL OPEN L
│   │ └ skTopA OPEN L; skTopB REDUCED L ─ skTopL OPEN L
│   └ skRegC REDUCED L    skLongPre OPEN L; skLongMid, skLongTop PROVED S (vacuous)
├ SkR.skWall REDUCED L ─ skWallCF REDUCED L ─ skWallLow REDUCED L
│ │ skWallLevAll REDUCED L: skWallBase OPEN L, skWallStep OPEN L (now from skTopUp)
│ │   skTopUp OPEN L (WzUpU bound attained at top atoms; skTopUp0 e = 0, skTopUpOm e = ω PROVED S)
│ │   skTopFam REFUTED M (replaced by skTopUp)
│ │ skX0LawDK PROVED L (image law for every k, bases β ∈ D: `Xi.xiLawDK`)
│ └ skWallTh PROVED M
├ SkR.skThHi REDUCED L: skThMid REDUCED M, skThFar OPEN L (codes > M_W, Θ < δ_λ·ω)
│   (side: skMidAssemble SUSPECT M, off the road; skTopDyn REFUTED M)
├ SkE.skEQ REDUCED L
│ ├ skThLow REDUCED L
│ └ skEQfar REDUCED L: skThFar OPEN L (far codes, δ_λ·ω ≤ Θ), skKFar REDUCED L (`Xg.xgKFar_of_R`)
│     skKCof OPEN L (closed points cofinal below B_n p where B_n jumps), skKReachR OPEN L (reach at ρ_μ)
│     off the road: skKGap PROVED S, skKClosed / skKLim REDUCED S
├ SkS.skShiftTh REDUCED L ─ skShiftThHi OPEN L (`Xe.XeShift` ⇔ `Xb.XbShift`: ϑ-clause for η ∈ Y, B₂ ≤ M < θ)
│   skNodeTh PROVED M (node lemmas, cited twin `xeVt_trL`); skRealBX REDUCED L; skImgGap PROVED S
└ SkS.skSupX REDUCED L ─ skVisKX REDUCED L: skWin PROVED S, skGenX REDUCED L
    ├ skUp REDUCED S ─ skUpRR REDUCED L (from SkF)
    ├ skFormX REDUCED L: skFormEps REDUCED M, skFormHighX OPEN L (forms with constant ϑ-levels)
    └ skSupKW OPEN L (carry of the ϑ-node images)
    off the road: skSupW, skVisKW, skGenW REDUCED; skFormW, skFormHighW PROVED; skRealB SUSPECT L;
      skImgEps, skCarryHigh OPEN L
```

## Counts (299 nodes)

| part | PROVED | REDUCED | OPEN | SUSPECT | REFUTED | REPLACED | S | M | L |
|---|---|---|---|---|---|---|---|---|---|
| SkF | 111 | 27 | 12 | 0 | 1 | 27 | 69 | 62 | 47 |
| SkR | 31 | 7 | 4 | 1 | 3 | 0 | 23 | 9 | 14 |
| SkE | 13 | 6 | 3 | 0 | 0 | 0 | 15 | 0 | 7 |
| SkS | 22 | 24 | 5 | 1 | 0 | 0 | 14 | 11 | 27 |
| Root | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 1 |
| all | 177 | 65 | 24 | 2 | 4 | 27 | 121 | 82 | 96 |

OPEN by size: SkF M 1, L 11; SkR L 4; SkE L 3; SkS L 5; all M 1, L 23 (skThFar in SkR and SkE are two different
leaves). Off the road: skL1Img (M), skImgEps, skCarryHigh (L).
Sorry leaves (47): OPEN 24; SUSPECT skMidAssemble (M), skRealB (L); REFUTED skTopDyn, skTopFam (M), skX0Law (L), kept
for the record; REPLACED 18 with sorry (kept, not used).
Round 121 → 122: sorry leaves 45 → 47, OPEN 23 → 24 (M 1 → 1, L 22 → 23), SUSPECT 2 → 2, REFUTED 3 → 4,
nodes 264 → 299; on the road 20 → 21 (M 1 → 0, L 19 → 21).

## REFUTED and SUSPECT

- **skTopFam REFUTED M** (`Xi.xiTopFam_false`): at k = 0, β = 0, e = ω the reading is ψ₁(A + P*), P* =
  ψ₂(Ω^{Ω₂+ω}) strongly critical, and no image X̂ gives ψ₁(A + 1 + Ω^{X̂+ω}) that value. Replaced by skTopUp.
- **skX0Law REFUTED L** (`Xd.xdX0Law_false`): outside D the map T gives 0; replaced by skX0LawDK (now PROVED).
- **skTopDyn REFUTED M** (`R2.SkRXTop`): no single image X̂ fits e = 0 and e = 1.
- **skShapeNat_false REFUTED S** (`Wh.whShapeNat_false`): with `e : ℕ` the shape leaf is false (Ω₁^ω).
- **skRealB SUSPECT L**: `Ww.WwCarry` gives no bound for ϑ-levels with data in [υ_λ, υ_{λ+h}). Off the road.
- **skMidAssemble SUSPECT M**: its hypothesis covers only F_W ≤ m_λ < θ⁺; replaced by skMidCF. Off the road.
- Risk notes: each region-B cell leaf (skLay*, skBhi*, skWin*, skTop*) is as strong as "ν_C is not in that cell".
  skShiftThHi is equivalent to the old skShiftTh (no vacuity risk added, no difficulty removed).

## Suggested order of the next rounds

1. Supply: skShiftThHi (a FRAG term type with constant-level ϑ-nodes for B₂ ≤ M < θ; port the node cases of
   `Vl.vlFrag_step`; the node lemmas are proved), then skFormHighX, skSupKW.
2. Frontier A3: offsets of level G read by codes (gates ≥ Γ₀) up to φ(G+1, 0); then every level G < ℓ ≤ t₀; then
   skA3T0Start, skSysA3StepW.
3. Reading: skTopUp at limit exponents (generalize `Xi.xiReadOm`), then at successors (a plateau lemma); then
   skWallBase / skWallStep from `Xi.XiTopUp`; skThFar (readings above M_W, or SkThTop).
4. EQ: skKReachR (a well-founded order on windows), skKCof where B_n jumps.
5. Region B: non-vacuity of (B-lo), skL1Img, interfaces taking the base atom Γ(c) (skLayLo, skLayHi), the transport
   ζ ↦ β + ζ (skBhi*, skWin*, skTop*), skLongPre.
