# R₂^C skeleton: status (round 123)

Root `R2Skel.Root.skNuC (S : InaccSeq)` = the conclusion of `Xb.xbRoad` (same as `Ww.wwRoad` / `Wd.wdRoadL`:
ν_C = L(ω+1), …), with the shift `Xb.XbShift S` and the supply `Xb.XbVisGen`. Parts: frontier `SkF.skFront` →
hUH/hLH/hVH/hVt; reading `SkR.skWall`, `SkR.skThHi` → `SkE.skEQ hRead hUH hLH` → hT/hF (round 123: the EQ induction
also takes ENUM-REACH from `SkF.skFrontU/L`); supply `SkS.skShiftTh` → shift (now PROVED), `SkS.skSupX` → h0/hn.
The bundle SkF + SkR + SkE + SkS + Root checks against the main build with only `declaration uses sorry` warnings (46).

**Warning (round 123):** the supply hypotheses of `Xb.xbRoad` are jointly false (`Xj.xbRoad_false`, skSupX_false,
skFormHighX REFUTED): the root is vacuous until the supply part gets a new road.

## Main progress number: OPEN / SUSPECT leaves on the road from `Root.skNuC`

**20 distinct OPEN leaves, all L; 0 SUSPECT** (round 122: 21, all L), plus 1 REFUTED leaf on the road (skFormHighX).
Counted by a Lean walk over the constants used by `skNuC`. On the road: SkF skA3T0Start, skSysA3StepW, skLaySys,
skLayFront, skLayLoBig, skLayHi, skBhiA, skBhiL, skWinA, skWinL, skTopA, skTopL, skLongPre; SkR skWallBase,
skWallStep, skThFar; SkE skThFar, skKCof, skEQTopR; SkS skSupKW. Closed: skShiftThHi, skTopUp, skKReachR (reduced
to skEQTopR), skLayLo (reduced to 3 leaves).

## Node tree (STATUS SIZE)

```
skNuC REDUCED L
├ SkF.skFront REDUCED L  (regions A1, A2 CLOSED; A3 level G CLOSED up to φ(G+Ω₁, 0))
│ └ skAbove REDUCED L
│   ├ skRegA REDUCED L ─ skLocOfSys PROVED S, skSysCof REDUCED L
│   │ ├ skSysA1 PROVED M;  skSysA2 PROVED S (was REDUCED)
│   │ │   skA3G1 PROVED M, skA3GOff PROVED L, skA3GAll PROVED L (φ(G, 1+λ), λ < φ(G+1, 0)), skA3GTop PROVED L
│   │ │   skA3GK PROVED L (levels G+κ, κ < Ω₁), skA3GW PROVED M (level G+Ω₁), skSysA3G/Gall/GW PROVED S
│   │ │   skLocG/GT/GW, skFG*Where, skHypIffG/GT/GW PROVED S (frontier ι(Γ(φ(G+Ω₁, 0))·ω), road `Xl.xlwRoad`)
│   │ └ skSysA3 REDUCED L ─ skSysA3All ─ skSysA3Lev ─ skSysA3LevW REDUCED L
│   │     skSysA3Lev0W REDUCED L ─ skA3QT0 REDUCED L ─ skA3T0Start OPEN L (a start of φ(t₀, G))
│   │     skSysA3StepW OPEN L
│   ├ skRegB REDUCED L  (cells: base β ∈ {0, Ω₂·q, b_k, b_ω} + offset ζ < Ω₂)
│   │ ├ skRegBlo REDUCED L ─ skLay REDUCED L
│   │ │   skLayLo REDUCED L: skLaySys OPEN L, skLayFront OPEN L (k+1 < ε₀), skLayLoBig OPEN L (rest)
│   │ │   skLayHi OPEN L;  skL1Img PROVED M;  skLayImgCst, skLayBaseSC, skLayIface, skLayFront0, skLaySys0 PROVED S
│   │ ├ skRegBhi REDUCED L: skBhiA OPEN L, skBhiL OPEN L
│   │ ├ skWinA OPEN L; skWinB REDUCED L ─ skWinL OPEN L
│   │ └ skTopA OPEN L; skTopB REDUCED L ─ skTopL OPEN L
│   └ skRegC REDUCED L    skLongPre OPEN L; skLongMid, skLongTop PROVED S (vacuous)
├ SkR.skWall REDUCED L ─ skWallCF REDUCED L ─ skWallLow REDUCED L
│ │ skWallLevAll REDUCED L: skWallBase OPEN L, skWallStep OPEN L
│ │   skTopUp PROVED L (`Xm.xmTopUp`): skPlat, skTopUpSucc, skTopUpLim PROVED M; skTopUpTests PROVED S
│ └ skWallTh PROVED M
├ SkR.skThHi REDUCED L: skThMid REDUCED M, skThFar OPEN L (codes > M_W, Θ < δ_λ·ω)
│   (side: skMidAssemble SUSPECT M, skTopDyn / skTopFam REFUTED M, all off the road)
├ SkE.skEQ REDUCED L
│ ├ skThLow PROVED S (`Xn.xnThLow`: needs no EQ; the cycle skThLow ← skEQfar is gone)
│ └ skEQfar REDUCED L: skThFar OPEN L (far codes, δ_λ·ω ≤ Θ), skKFar REDUCED L
│     skKCof OPEN L (closed points unbounded below B_n p where B_n jumps)
│     skKReachR REDUCED L (induction on the reach r(λ) = k_λ(T_λ)) ─ skEQTopR OPEN L (EQ at the top restart)
├ SkS.skShiftTh PROVED L ─ skShiftThHi PROVED L (`Xj.xeShift_holds`), skFragTh PROVED L, skRealBX PROVED L
└ SkS.skSupX REDUCED L (hypotheses jointly false: skSupX_false PROVED S) ─ skVisKX REDUCED L ─ skGenX REDUCED L
    ├ skUp REDUCED S ─ skUpRR REDUCED L (from SkF)
    ├ skFormX REDUCED L: skFormEps REDUCED M, skFormHighX REFUTED L (skFormHighX_false PROVED M)
    └ skSupKW OPEN L (carry of the ϑ-node images)
    off the road: skSupW, skVisKW, skGenW REDUCED; skRealB SUSPECT L; skImgEps, skCarryHigh OPEN L
```

## Counts (332 nodes)

| part | PROVED | REDUCED | OPEN | SUSPECT | REFUTED | REPLACED | S | M | L |
|---|---|---|---|---|---|---|---|---|---|
| SkF | 130 | 27 | 13 | 0 | 1 | 27 | 83 | 63 | 52 |
| SkR | 36 | 7 | 3 | 1 | 3 | 0 | 24 | 12 | 14 |
| SkE | 19 | 6 | 3 | 0 | 0 | 0 | 21 | 0 | 7 |
| SkS | 28 | 22 | 3 | 1 | 1 | 0 | 15 | 12 | 28 |
| Root | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 1 |
| all | 213 | 63 | 22 | 2 | 5 | 27 | 143 | 87 | 102 |

OPEN by size: all L (SkF 13, SkR 3, SkE 3, SkS 3); skThFar in SkR and SkE are two different leaves.
Off the road: skImgEps, skCarryHigh (L). SUSPECT: skMidAssemble M, skRealB L. REFUTED: S 1, M 2, L 2.
Sorry leaves (46): OPEN 22; SUSPECT 2; REFUTED skTopDyn, skTopFam (M), skX0Law, skFormHighX (L), kept for the
record; REPLACED 18 with sorry (kept, not used).
Round 122 → 123: sorry leaves 47 → 46, OPEN 24 → 22 (M 1 → 0, L 23 → 22), SUSPECT 2 → 2, REFUTED 4 → 5,
nodes 299 → 332; on the road 21 → 20 (all L).

## REFUTED and SUSPECT

- **skFormHighX REFUTED L** (`Xj.xjFormHighX_fail`): X′ = ϑ^{u₁}(Ω₁·(B₂+λ) + λ) has a level whose data are never
  below λ, so no form with constant ϑ-levels ends in X′; hence the hypotheses of `Xb.xbRoad` are jointly false.
- **skTopFam REFUTED M** (`Xi.xiTopFam_false`): no image X̂ fits k = 0, β = 0, e = ω. Replaced by skTopUp (PROVED).
- **skX0Law REFUTED L** (`Xd.xdX0Law_false`): outside D the map T gives 0; replaced by skX0LawDK (PROVED).
- **skTopDyn REFUTED M** (`R2.SkRXTop`): no single image X̂ fits e = 0 and e = 1.
- **skShapeNat_false REFUTED S** (`Wh.whShapeNat_false`): with `e : ℕ` the shape leaf is false (Ω₁^ω).
- **skRealB SUSPECT L**: `Ww.WwCarry` gives no bound for ϑ-levels with data in [υ_λ, υ_{λ+h}). Off the road.
- **skMidAssemble SUSPECT M**: its hypothesis covers only F_W ≤ m_λ < θ⁺; replaced by skMidCF. Off the road.
- Risk notes: each region-B cell leaf is as strong as "ν_C is not in that cell". skLayFront for k ≥ 1 contains all
  of region A (including skA3T0Start), so the layers can close only after A3.

## Suggested order of the next rounds

1. Supply (blocks the whole root): a new supply road whose forms allow ϑ-levels with data in [υ_λ, υ_{λ+h}):
   leaf substitution on codes in [B₂, θ), FRAG with moving-leaf levels ≥ B₂, the cited subcase Γ^* ≥ α, the carry.
2. Frontier A3: make the κ-recursion and the Ω₁-union generic in the band; the bands along `Xc.xcA3`; then
   skA3T0Start, skSysA3StepW.
3. Reading: skWallBase / skWallStep (block law for non-top atoms; the B_n move of T and A); skThFar.
4. EQ: skEQTopR (or well-foundedness of the top relation), skKCof at the jump indices.
5. Region B (after A3): skLayFront, skLaySys, skLayLoBig, skLayHi; ζ ↦ β + ζ (skBhi*, skWin*, skTop*); skLongPre.
