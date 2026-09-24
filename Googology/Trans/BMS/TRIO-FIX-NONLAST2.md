[← Back](../README.md) | [English](TRIO-FIX-NONLAST2.md) | [Japanese](TRIO-FIX-NONLAST2-ja.md)

# Fix G, Fix M and change 1, narrowed

This is a separate patch on top of [`TrioFixNonLastOther.lean`](TrioFixNonLastOther.lean)
(rules 1–10 of [koteitan/trio](https://github.com/koteitan/trio) with Fixes A–E, N, G, M and
changes 1–4). The code is in [`TrioFixNonLastOther2.lean`](TrioFixNonLastOther2.lean). The checks
are in [`TrioFixNonLastOther2Sheet.lean`](TrioFixNonLastOther2Sheet.lean) and in four heavy sheets
(`TrioFixNonLastOther2SheetCal1`, `…Cal2`, `…RegM`, `…RegG`), which belong to the library
`GoogologySheets`. For merging: in `placeUnitsX` and `blockX`, replace `spentX` by `spentX2`,
`fixXNeeded` by `fixXNeeded2` and `fixX` by `fixX2`.

## The fault

`TrioFixNonLastOther` fixes the leaves that are not last outside the tower regimes. On its five
calibrated families it is right, but a review found pairs outside them that were in order before
the patch (under `TrioRulesAll`) and are out of order after it:

- Fix M (change 3) in the regimes `Ω_2`, `Ω_3`, `Ω_4`, `Ω+1`, `Ω_{Ω+1}`:
  `M(Ω_{Ω_2}+Ω_ω+Ω) < M(Ω_{Ω_2}+Ω+ω)`, and the patched matrix is not standard.
- Fix G (change 2) in the regimes `Ω_{ω·2}`, `Ω_{ω+2}`, `Ω_{Ω_ω}`:
  `M(Ω_{Ω_{ω·2}}+Ω_{ω·2}) > M(Ω_{Ω_{ω·2}}+Ω_Ω+Ω)` and two more.
- Change 1 in the regime `Ω_{ω^2}`: `M(Ω_{Ω_{ω^2}}+Ω_{ω·2}) < M(Ω_{Ω_{ω^2}}+Ω_ω+Ω)`.

`M(α)` is the matrix of `ψ_0(Ω_α)`. The regime `r` is the level with `Ω_r ≤ α < Ω_{r+1}`.

## Why

- **The leaf is shared with a lower top.** Fix M and Fix G lay a copy after the leaf of a level
  `p`. That copy only helps when the leaf of `p` is not the leaf of a lower level. In `r = Ω_2`
  the leaf of `ω` has row-1 value `1`, like the leaf of the top `1` (and below the leaf `2` of
  the top `2`). In `r = Ω_{ω+2}` the leaf of `Ω` has value `2`, like the top `ω+1`. Then the
  copy lies below the plain continuation of the lower level.
- **The upgrade stops early.** For `p = Ω` the leaf is upgraded by a sub-unit whose leaf names
  `1`. In `r = Ω_{ω·2}`, `Ω_{ω·3}`, `Ω_{ω+2}` there is no such sub-unit, so the leaf of `Ω`
  stays the leaf of a lower marked level (`ω·2` in `r = Ω_{ω·3}`), and the copy starts below
  that level's mark: `(3,2,0)` against `(3,2,1)`.
- **Change 1 removes a storey that is needed.** Change 1 turns rule 6 (`spent`) off in every
  uncountable regime, because it lays a storey after a leaf at `y = 1` that is not standard. In
  `r = Ω_{ω·2}` the regime's leaf is at `y = 2`, and there the storey is what keeps the order.

## The change

Notation: `tops r = chainG r`; `N(v)` is the row-1 value of a leaf naming `v` in the current
state (`leafNameOrYN`); a level `u` is *marked* when `suffixOf (chainBase u) ≠ []`.

1. **Change 1′** (`spentX2`). In an uncountable regime, rule 6 stays off only when
   `keepSpent` fails:

       keepSpent ⇔ leafY r ≠ 1 ∨ (p marked ∧ p ∉ tops r)

2. **Fix G′** (`fixGNeeded2`):

       fixGNeeded2 = fixGNeeded ∧ leafApart ∧ upgradeFull
       leafApart   ⇔ ∀ t ∈ tops r, t < p → N(t) ≠ N(p)
       upgradeFull ⇔ the upgrade of the last leaf reaches the end of p's Ω-chain

3. **Fix M′** (`fixMNeeded2`):

       fixMNeeded2 = fixMNeeded ∧ (r is a tower ∨ leafApart)

4. `fixX2` is Fix M′ when `fixMNeeded2`, else Fix N (which is also Fix G′).

Change 4 (lifted leaves) and everything else are unchanged.

## Results

Python reference on 3,387 labels in 25 families; yaBMS `bms -s` for standardness (outside Lean).
"Broken / fixed" counts the pairs that `TrioRulesAll` has in order and the patch has out of
order, and the other way round.

| family (sums after) | `TrioFixNonLastOther` broken / fixed | this patch broken / fixed | new non-standard (`TrioFixNonLastOther` → this patch) |
|---|---|---|---|
| `Ω_{Ω_2}` (review, Fix M) | 278 / 1,695 | 0 / 1,695 | 15 → 0 |
| `Ω_{Ω_3}` | 276 / 618 | 0 / 618 | 15 → 0 |
| `Ω_{Ω_4}` | 276 / 0 | 0 / 0 | 15 → 0 |
| `Ω_{Ω+1}` | 144 / 203 | 0 / 203 | 18 → 0 |
| `Ω_{Ω_{Ω+1}}` | 153 / 218 | 0 / 218 | 21 → 0 |
| `Ω_{Ω_{ω·2}}` (Fix G, change 1) | 1,679 / 2,276 | 0 / 2,276 | 0 → 0 |
| `Ω_{Ω_{ω·3}}` | 526 / 124 | 0 / 375 | 1 → 0 |
| `Ω_{Ω_{Ω_2}}` | 899 / 22 | 0 / 0 | 0 → 0 |
| `Ω_{Ω_{Ω_2+1}}` | 415 / 0 | 0 / 0 | 59 → 0 |
| `Ω_{Ω_{ω+1}}` with `Ω_Ω` | 319 / 99 | 6 / 108 | 33 → 0 |
| `Ω_{Ω_{ω+2}}` (Fix G) | 776 / 1,078 | 52 / 1,161 | 41 → 0 |
| `Ω_{Ω_{Ω_ω}}` (Fix G) | 313 / 908 | 24 / 960 | 0 → 0 |
| `Ω_{Ω_{ω^2}}` (change 1) | 182 / 1,666 | 8 / 1,652 | 0 → 0 |
| `Ω_{Ω_{ω^2+1}}` | 834 / 872 | 22 / 904 | 42 → 0 |
| `Ω_{Ω_ω}` with `Ω_{ω·2}` (two families) | 2 / 3,288, 11 / 15,749 | unchanged | 0 → 0 |
| the five calibrated families, `Ω_{Ω_Ω}` (wide) | unchanged | unchanged | 0 → 0 |

The five calibrated families (after `Ω_{Ω_ω}`, `Ω_{Ω_{ω+1}}`, `Ω_{Ω_2}`, `Ω_{Ω_Ω}`, `Ω_Ω`),
the Python-only families after `Ω_{Ω+1}`, `Ω_{Ω+2}`, `Ω_{Ω_3}`, and the 27 BMS expansions
`M(P+t·ω)[n] = M(P+t·(n+1))` keep every matrix of `TrioFixNonLastOther`.

Lean (`leanman check`, all exit 0):

- `TrioFixNonLastOther2.lean`: the patch and 9 lemmas about where the narrowing cannot
  act (`MstepX2_psi`, `MstepX2_omega`, `spentX2_countable`, `spentX2_of_not_keep`,
  `spentX2_le_spent`, `fixGNeeded2_imp`, `fixMNeeded2_imp`, `fixMNeeded2_tower`,
  `fixXNeeded2_countable`) and `WF3_trioRuleMatrixX2`.
- `TrioFixNonLastOther2Sheet.lean` (about 140 s): the nine pairs, the 27 expansions,
  three calibrated families, eight families against `TrioRulesAll`.
- `TrioFixNonLastOther2SheetHeavy1.lean` (about 600 s): the calibrated families after
  `Ω_{Ω_ω}` and `Ω_{Ω_{ω+1}}`.
- `TrioFixNonLastOther2SheetHeavy2.lean` (about 680 s): the families after `Ω_{Ω_{ω·3}}`,
  `Ω_{Ω_{ω+2}}`, `Ω_{Ω_{Ω_ω}}`, `Ω_{Ω_{ω^2+1}}` against `TrioRulesAll`.
- The Lean builder equals the Python reference on 3,345 of the 3,387 labels (`#eval`,
  outside the sheets). The other 42 have 138–656 columns and take minutes each in Lean.
- The heavy sheets are not yet imported by `GoogologySheets.lean`.

## Still open

- **Pairs still broken after a shared leaf.** After `Ω_{Ω_{ω+1}}`, `Ω_{Ω_{ω+2}}`, `Ω_{Ω_{Ω_ω}}` and
  `Ω_{Ω_{ω^2+1}}`, 6, 52, 24 and 22 pairs that `TrioRulesAll` had in order are still out of order.
  They follow a leaf whose level shares its leaf with a lower top, for example `γ+Ω_Ω+…`
  against `γ+Ω_{ω+1}+…`. Fix G′ now leaves that leaf alone, but a later Fix G′ copy or a lifted
  leaf (change 4) still puts the pair out of order. We tried turning off every later fix after
  such a leaf. It gives `6, 52, 24 → 0, 0, 13`, but after `Ω_{Ω_{ω·2}}` the disagreements rise
  from 2,626 to 2,781. So it is not done.
- **`Ω_{Ω_{ω^2}}`:** `M(γ+Ω_ω) > M(γ+Ω_ω+x)` for `γ = Ω_Ω`, `Ω_{ω^2}` (8 pairs). The last-leaf
  version carries the mark `(3,2,1)`, and the storey that rule 6 lays after the leaf is below it.
- **Large matrices where rule 6 is back.** After `Ω_{Ω_{ω·2}}`, rule 6's storeys and change 4's
  lifted copies together give matrices of up to 656 columns (`Ω_{Ω_{ω·2}}+Ω_{ω·2}+Ω_2+Ω_2` has
  296). 117 of the 221 matrices are not standard. `TrioRulesAll` has 124 not standard (74 columns
  at most), `TrioFixNonLastOther` has 20. None of the 117 was standard under `TrioRulesAll`.
  These labels take minutes each in Lean. That is why the sheet family for this regime leaves
  out `Ω_2`.
- **The last leaves behind all this are not this item.** `M(γ+Ω_Ω) = M(γ+Ω_{ω+1})` for
  `γ = Ω_{Ω_{ω+1}}`, `Ω_{Ω_{ω+2}}`. `M(γ+Ω_ω) = M(γ+Ω_{ω·2})` for `γ = Ω_{Ω_{ω^2}}`. Both already
  hold under `TrioRulesAll`. After `Ω_{Ω_2}`, the leaf of `Ω_ω` is the leaf of `Ω` with the mark
  `(1,1,1)`, and that matrix is not standard.
- The "Still open" items of [`TrioFixNonLastOther.lean`](TrioFixNonLastOther.lean) stand, except
  the last one (the review's regressions), which this patch answers.
