# R₂^C skeleton: status (round 124)

Root `R2Skel.Root.skNuC (S : InaccSeq)` = the conclusion of `Xb.xbRoad` (same as `Ww.wwRoad` / `Wd.wdRoadL`:
ν_C = L(ω+1), …), with the shift `Xb.XbShift S` and the supply `Xb.XbVisGen`. Parts: frontier `SkF.skFront` →
hUH/hLH/hVH/hVt; reading `SkR.skWall`, `SkR.skThHi` → `SkE.skEQ hRead hUH hLH` → hT/hF; supply `SkS.skShiftTh`
(PROVED) → shift, `SkS.skSupX` → h0/hn. Root unchanged. The bundle SkF + SkE + SkR + SkS + Root (SkR now
imports SkE) checks against the main build with only `declaration uses sorry` warnings (45).

**Warning:** the supply hypotheses of `Xb.xbRoad` are jointly false (`Xj.xbRoad_false`, skSupX_false, skFormHighX
REFUTED): the root is still vacuous. Leaf sup46 (new supply road `Xo.xoRoadH`, ϑ-levels as terms) was NOT merged:
BLOCKING audit gap (`XoR` restricts only the `lc` leaves, so λ has a fixed spelling and the planned carry fails).

## Main progress number: OPEN / SUSPECT leaves on the road from `Root.skNuC`

**18 distinct OPEN leaves, all L; 0 SUSPECT** (round 123: 20, all L), plus 1 REFUTED leaf on the road (skFormHighX).
Counted by a Lean walk over the constants used by `skNuC`. On the road: SkF skSysA3StepW, skLaySys, skLayFront,
skLayLoBig, skLayHi, skBhiA, skBhiL, skWinA, skWinL, skTopA, skTopL, skLongPre; SkR skWallBase, skWallStep;
SkE skTopK (shared with SkR), skEQJump, skKCofGap; SkS skSupKW. Left the road: skA3T0Start (skSysA3Lev0W PROVED
by `Xp.xpEnt3`); skThFar in SkR and SkE (→ the one leaf skTopK); skEQTopR → skEQJump; skKCof → skKCofGap.

## Node tree (STATUS SIZE)

```
skNuC REDUCED L
├ SkF.skFront REDUCED L  (A1, A2 CLOSED; A3: all bands G < ℓ < t₀ = ε_{G+1} and a start of φ(t₀, G))
│ └ skAbove REDUCED L
│   ├ skRegA REDUCED L ─ skLocOfSys PROVED S, skSysCof REDUCED L
│   │ ├ skSysA1 M, skSysA2 S, skA3G*, skSysA3G*, round 124: skA3BandStep, skA3Bands, skA3T0Bot, skA3T0G, skSysA3T0G,
│   │ │   skLocT0 (Xp): all PROVED
│   │ └ skSysA3 REDUCED L ─ skSysA3All ─ skSysA3Lev ─ skSysA3LevW REDUCED L
│   │     skSysA3Lev0W PROVED L (`Xp.xpEnt3`, was REDUCED);  skSysA3StepW OPEN L (t_n → t_{n+1})
│   │     off the road: skA3QT0 REDUCED L ─ skA3T0Start OPEN L (gate-0 pseudo-base)
│   ├ skRegB REDUCED L  (cells: base β ∈ {0, Ω₂·q, b_k, b_ω} + offset ζ < Ω₂)
│   │ ├ skRegBlo REDUCED L ─ skLay REDUCED L
│   │ │   skLayLo REDUCED L: skLaySys OPEN L, skLayFront OPEN L, skLayLoBig OPEN L;  skLayHi OPEN L
│   │ ├ skRegBhi REDUCED L: skBhiA OPEN L, skBhiL OPEN L
│   │ ├ skWinA OPEN L; skWinB REDUCED L ─ skWinL OPEN L
│   │ └ skTopA OPEN L; skTopB REDUCED L ─ skTopL OPEN L
│   └ skRegC REDUCED L    skLongPre OPEN L; skLongMid, skLongTop PROVED S (vacuous)
├ SkR.skWall REDUCED L ─ skWallCF REDUCED L ─ skWallLow REDUCED L
│ │ skWallLevAll REDUCED L: skWallBase OPEN L, skWallStep OPEN L; skTopUp PROVED L
│ │   round 124 PROVED: skWallRefNonTop S (ψ₂(T a) fails at a = Ω₃+1), skTopBlk, skTMove, skSigMove, skTopMove
│ └ skWallTh PROVED M
├ SkR.skThHi REDUCED L: skThMid REDUCED M, skThFar REDUCED L (round 124: skWallCF, skTopK; `Xs.xsFarLow`)
│   (side: skMidAssemble SUSPECT M, skTopDyn / skTopFam REFUTED M, all off the road)
├ SkE.skEQ REDUCED L
│ ├ skThLow PROVED S;  └ skEQfar REDUCED L
│     skThFar REDUCED L (`Xs.xsFar_of_top`) ─ skTopK OPEN L (move at window codes ≥ K_ω; shared with SkR)
│       skFarGe, skThTopK, skTopKTarget, skXsRef PROVED S (readings on [M_W, K_ω), `Xs.xsBase`, `Xs.xsBlk`)
│     skKFar REDUCED L ─ skKCof REDUCED L (`Xr.xrKCof_of_gap`) ─ skKCofGap OPEN L (jump gap of B_n)
│     skKReachR REDUCED L ─ skEQTopR REDUCED L (`Xr.xrTop`) ─ skEQJump OPEN L (sup of chain points where B_n jumps)
├ SkS.skShiftTh PROVED L ─ skShiftThHi, skFragTh, skRealBX PROVED L
└ SkS.skSupX REDUCED L (hypotheses jointly false: skSupX_false PROVED S) ─ skVisKX REDUCED L ─ skGenX REDUCED L
    ├ skUp REDUCED S ─ skUpRR REDUCED L (from SkF)
    ├ skFormX REDUCED L: skFormEps REDUCED M, skFormHighX REFUTED L (skFormHighX_false PROVED M)
    └ skSupKW OPEN L (carry of the ϑ-node images)
    off the road: skSupW, skVisKW, skGenW REDUCED; skRealB SUSPECT L; skImgEps, skCarryHigh OPEN L
```

## Counts (363 nodes)

| part | PROVED | REDUCED | OPEN | SUSPECT | REFUTED | REPLACED | S | M | L |
|---|---|---|---|---|---|---|---|---|---|
| SkF | 140 | 26 | 13 | 0 | 1 | 27 | 88 | 64 | 55 |
| SkR | 44 | 9 | 2 | 1 | 3 | 0 | 28 | 17 | 14 |
| SkE | 29 | 9 | 3 | 0 | 0 | 0 | 33 | 0 | 8 |
| SkS | 28 | 22 | 3 | 1 | 1 | 0 | 15 | 12 | 28 |
| Root | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 1 |
| all | 241 | 67 | 21 | 2 | 5 | 27 | 164 | 93 | 106 |

OPEN by size: all L (SkF 13, SkR 2, SkE 3, SkS 3); off the road: skA3T0Start, skImgEps, skCarryHigh.
SUSPECT: skMidAssemble M, skRealB L. REFUTED: S 1, M 2, L 2.
Sorry leaves (45): OPEN 21; SUSPECT 2; REFUTED skTopDyn, skTopFam (M), skX0Law, skFormHighX (L), kept for the
record; REPLACED 18 with sorry (kept, not used).
Round 123 → 124: sorry leaves 46 → 45, OPEN 22 → 21 (all L), SUSPECT 2 → 2, REFUTED 5 → 5, nodes 332 → 363;
on the road 20 → 18 (all L), plus skFormHighX REFUTED.

## REFUTED and SUSPECT

- **skFormHighX REFUTED L** (`Xj.xjFormHighX_fail`): X′ = ϑ^{u₁}(Ω₁·(B₂+λ) + λ) has a level whose data are never
  below λ, so no form with constant ϑ-levels ends in X′; hence the hypotheses of `Xb.xbRoad` are jointly false.
- **skTopFam REFUTED M** (`Xi.xiTopFam_false`): no image X̂ fits k = 0, β = 0, e = ω. Replaced by skTopUp (PROVED).
- **skX0Law REFUTED L** (`Xd.xdX0Law_false`): outside D the map T gives 0; replaced by skX0LawDK (PROVED).
- **skTopDyn REFUTED M** (`R2.SkRXTop`): no single image X̂ fits e = 0 and e = 1. **skShapeNat_false REFUTED S**
  (`Wh.whShapeNat_false`): with `e : ℕ` the shape leaf is false (Ω₁^ω).
- **skRealB SUSPECT L**: `Ww.WwCarry` gives no bound for ϑ-levels with data in [υ_λ, υ_{λ+h}). Off the road.
- **skMidAssemble SUSPECT M**: its hypothesis covers only F_W ≤ m_λ < θ⁺; replaced by skMidCF. Off the road.
- Refute-first records (round 124): Θ(ψ₂ a) = ψ₁(A+1+ψ₂(T a)) fails at a = Ω₃+1 (`Xq.xqRef_wit`); the level-down
  reading ψ₁(A+θ+T d) fails at d = Ω_{k+1}, k ≥ 2 (`Xs.xsRef_wit`). Risk: each region-B cell leaf is as strong as
  "ν_C is not in that cell"; skLayFront for k ≥ 1 contains all of region A, so the layers come after A3.

## Suggested order of the next rounds

1. Supply (blocks the whole root): redo sup46's road with `XoR` asking `VdLtIn` on the value of every leaf-free
   subterm, then REFUTE FIRST again; then the bridge (FRAG with moving ϑ-levels, carry) and the reach formula at μ.
2. Frontier A3: skSysA3StepW (code systems for the levels between t_n and t_{n+1}, same recursion as `Xp.xpFam`).
3. Reading: skWallBase / skWallStep (move of the base data of the top atoms; non-top atoms past the first block);
   skTopK (the plateau K_ω, then the ψ₃ / Ω₃ atoms).
4. EQ: decide whether a supremum of chain points can be a jump point of B_n (skEQJump); then skKCofGap.
5. Region B (after A3): skLayFront, skLaySys, skLayLoBig, skLayHi; ζ ↦ β + ζ (skBhi*, skWin*, skTop*); skLongPre.
