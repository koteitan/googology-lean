# R₂^C skeleton: status (round 125)

Root `R2Skel.Root.skNuC (S : InaccSeq)` = the conclusion of `Xo.xoRoadH` (same as `Ww.wwRoad` / `Wd.wdRoadL`:
ν_C = L(ω+1), …). Round 125: the root now applies the supply road with moving leaves `Xo.xoRoadH` (in place of
`Xb.xbRoad`): bridge `SkS.skRealBXo` (`Xo.XoRealB`), supply `SkS.skSupXo` (read with the repaired `Xo.XoR`). Parts:
frontier `SkF.skFront` → hUH/hLH/hVH/hVt; reading `SkR.skWall`, `SkR.skThHi` → `SkE.skEQ hRead hUH hLH` → hT/hF.
The bundle SkF + SkE + SkR + SkS + Root checks against the main build with only `declaration uses sorry` warnings (46).

**Vacuity:** no REFUTED or SUSPECT leaf is on the road any more (skFormHighX, which made `Xb.xbRoad` vacuous, is off
the road). The root is NOT known to be vacuous; non-vacuity is not proved either (`Xo.XoSup`, `Xo.XoRealB` are not
shown satisfiable; the audit asks for a covering lemma: every reach point r(λ+g) has an `XoR` decomposition).

## Main progress number: OPEN / SUSPECT leaves on the road from `Root.skNuC`

**18 distinct OPEN leaves, all L; 0 SUSPECT; 0 REFUTED** (round 124: 18 OPEN L + 1 REFUTED). Counted by a Lean walk
over the constants used by `skNuC`. On the road: SkF skLaySys, skLayLoBig, skLayHi, skBhiA, skBhiL, skWinA, skWinL,
skTopA, skTopL, skLongPre; SkR skWallBase, skWallStep; SkE skTopK (shared with SkR), skGapLh, skJumpOff,
skJumpNoRng; SkS skSupKXo, skRealBXo. Left the road: skSysA3StepW, skLayFront (PROVED); skEQJump, skKCofGap
(REDUCED); skSupKW (now off the road, follows from skSupKXo).

## Node tree (STATUS SIZE)

```
skNuC REDUCED L  (Xo.xoRoadH)
├ SkF.skFront REDUCED L
│ └ skAbove REDUCED L
│   ├ skRegA: REGION A CLOSED. skSysCof PROVED L ─ skSysA3 PROVED L ─ skSysA3All ─ skSysA3Lev ─ skSysA3LevW PROVED
│   │   skSysA3StepW PROVED L (round 125, `Xu.xuEnt3`: WnEnt3 S n for every n); skA3CodeAll, skA3ClsAll,
│   │   skA3BandsAll, skA3QStart PROVED L, skA3PkAll M, skA3End S ((A3) ends at Γ(1) = sup_n t_n)
│   │   off the road: skA3QT0 REDUCED L ─ skA3T0Start OPEN L (gate-0 pseudo-base)
│   ├ skRegB REDUCED L  (cells: base β ∈ {0, Ω₂·q, b_k, b_ω} + offset ζ < Ω₂)
│   │ ├ skRegBlo REDUCED L ─ skLay REDUCED L
│   │ │   skLayLo REDUCED L: skLayFront PROVED L (`Xx.xxLayFront`, k+1 < ε₀), skLayLocVD M, skLaySysBase S;
│   │ │     skLaySys OPEN L, skLayLoBig OPEN L;  skLayHi OPEN L
│   │ ├ skRegBhi REDUCED L: skBhiA OPEN L, skBhiL OPEN L
│   │ ├ skWinA OPEN L; skWinB REDUCED L ─ skWinL OPEN L
│   │ └ skTopA OPEN L; skTopB REDUCED L ─ skTopL OPEN L
│   └ skRegC REDUCED L    skLongPre OPEN L; skLongMid, skLongTop PROVED S (vacuous)
├ SkR.skWall REDUCED L ─ skWallCF REDUCED L ─ skWallLow REDUCED L
│ │ skWallLevAll REDUCED L: skWallBase OPEN L, skWallStep OPEN L; skTopUp PROVED L
│ │   round 125 PROVED: skBaseMove0 S (base 0, small exponent), skTop0Move M (`Xv.xvTop0Move`)
│ └ skWallTh PROVED M
├ SkR.skThHi REDUCED L: skThMid REDUCED M, skThFar REDUCED M (skWallCF, skTopK)
│   (side: skMidAssemble SUSPECT M, skTopDyn / skTopFam REFUTED M, all off the road)
├ SkE.skEQ REDUCED L
│ ├ skThLow PROVED S;  └ skEQfar REDUCED L
│     skThFar ─ skTopK OPEN L (move at window codes ≥ K_ω; shared with SkR)
│     skKFar ─ skKCof REDUCED S ─ skKCofGap REDUCED S (`Xw.xwKCofGap_iff`; decomposable p PROVED)
│       └ skGapLh OPEN L (every gap point a has lh(a) < B_n p)
│     skKReachR ─ skEQTopR REDUCED L ─ skEQJump REDUCED S (`Xw.xwJump_iff`)
│       ├ skJumpOff OPEN L (s not a range restart: B_n s ≤₁ lh(s*))
│       └ skJumpNoRng OPEN L (s a range restart: does not occur)
└ SkS.skSupXo REDUCED L ─ skVisKXo REDUCED S ─ skGenXo REDUCED S
    ├ skUp REDUCED S ─ skUpRR REDUCED L (from SkF);  skFormXo PROVED S (`Xo.xoForms_all`)
    ├ skSupKXo OPEN L (carry with the repaired XoR)
    └ skRealBXo OPEN L (bridge Xo.XoRealB)
    round 125 PROVED: skXoFixed, skXoFkEx, skXoAbsEx, skXoKeep, skXoOffWit; skXoNaiveRef PROVED NEGATION M
    off the road: skShiftTh PROVED L, skSupX REDUCED (hypotheses jointly false), skFormHighX REFUTED L,
      skSupKW OPEN L, skRealB SUSPECT L, skImgEps, skCarryHigh OPEN L
```

## Counts (402 nodes)

| part | PROVED | REDUCED | OPEN | SUSPECT | REFUTED | REPLACED | S | M | L |
|---|---|---|---|---|---|---|---|---|---|
| SkF | 156 | 20 | 11 | 0 | 1 | 27 | 90 | 66 | 59 |
| SkR | 46 | 9 | 2 | 1 | 3 | 0 | 29 | 18 | 14 |
| SkE | 36 | 11 | 4 | 0 | 0 | 0 | 42 | 0 | 9 |
| SkS | 42 | 25 | 5 | 1 | 1 | 0 | 27 | 16 | 31 |
| Root | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 1 |
| all | 280 | 66 | 22 | 2 | 5 | 27 | 188 | 100 | 114 |

OPEN by size: all L (SkF 11, SkR 2, SkE 4, SkS 5); off the road: skA3T0Start, skSupKW, skImgEps, skCarryHigh.
SUSPECT: skMidAssemble M, skRealB L. REFUTED: S 1, M 2, L 2.
Sorry leaves (46): OPEN 22; SUSPECT 2; REFUTED skTopDyn, skTopFam, skX0Law, skFormHighX (record); REPLACED 18.
Round 124 → 125: sorry leaves 45 → 46, OPEN 21 → 22 (all L), SUSPECT 2 → 2, REFUTED 5 → 5, nodes 363 → 402;
on the road 18 OPEN L + 1 REFUTED → 18 OPEN L + 0 REFUTED.

## REFUTED and SUSPECT

- **skFormHighX REFUTED L** (`Xj.xjFormHighX_fail`): X′ = ϑ^{u₁}(Ω₁·(B₂+λ) + λ) has a level whose data are never
  below λ, so no form with constant ϑ-levels ends in X′; the hypotheses of `Xb.xbRoad` are jointly false. Off the road.
- **skXoNaiveRef** (PROVED NEGATION, `Xo.xoNaive_ref`): "sub-terms without moving leaves have value < υ_μ" is not
  enough: F′_k = ψ_{Ω₁}(λ + Ω_ω + Ω_ω + P′·k) absorbs λ; hence the repaired `XoR` (closed sub-terms low).
- **skTopFam REFUTED M** (`Xi.xiTopFam_false`): no image X̂ fits k = 0, β = 0, e = ω. Replaced by skTopUp (PROVED).
- **skX0Law REFUTED L** (`Xd.xdX0Law_false`): outside D the map T gives 0; replaced by skX0LawDK (PROVED).
- **skTopDyn REFUTED M** (`R2.SkRXTop`): no single image X̂ fits e = 0 and e = 1. **skShapeNat_false REFUTED S**
  (`Wh.whShapeNat_false`): with `e : ℕ` the shape leaf is false (Ω₁^ω). PROVED counts skXoNaiveRef (a negation).
- **skRealB SUSPECT L**: `Ww.WwCarry` gives no bound for ϑ-levels with data in [υ_λ, υ_{λ+h}). Off the road.
- **skMidAssemble SUSPECT M**: its hypothesis covers only F_W ≤ m_λ < θ⁺; replaced by skMidCF. Off the road.
- Risk: a ϑ-node image whose argument leaves T has no value (inside skRealBXo).

## Suggested order of the next rounds

1. Supply: the covering lemma (every reach point has an `XoR` decomposition, `XoR` version of `Xa.xaRep`), then
   skRealBXo (bridge) and skSupKXo (carry); this decides whether the root is non-vacuous.
2. Region B: skLaySys (generalise the system recursion over Γ(k), about 126k lines hard-wired to G), skLayLoBig,
   skLayHi; then ζ ↦ β + ζ (skBhi*, skWin*, skTop*); skLongPre.
3. Reading: skWallBase / skWallStep (large exponents: inverse of B_n on atom codes; β ≠ 0); skTopK.
4. EQ: skGapLh (composition B_m ∘ C_{n,m} = B_n), then skJumpOff, skJumpNoRng.
