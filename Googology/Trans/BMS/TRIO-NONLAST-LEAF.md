[← Back](../README.md) | [English](TRIO-NONLAST-LEAF.md) | [Japanese](TRIO-NONLAST-LEAF-ja.md)

# Fix N: a leaf with more after it, in an uncountable regime

[`TrioRules2.lean`](TrioRules2.lean) (rules 1–10 of
[koteitan/trio](https://github.com/koteitan/trio) with Fixes A–D) still puts
`Ω_{Ω_Ω}+Ω_{Ω_2}+1` above `Ω_{Ω_Ω}·2`. This note finds the cause, gives a
correction (Fix N), and reports the checks. The rules are in
[`TrioRulesNonLast.lean`](TrioRulesNonLast.lean); the checks are in
[`TrioRulesNonLastSheet.lean`](TrioRulesNonLastSheet.lean). All checks are
`#guard`s: a calibration, not a theorem.

`M(α)` is the matrix of `ψ_0(Ω_α)`. `M[n]` is BM4 expansion with `n + 1` copies
of the bad part (yaBMS `[n]`, and `expandRL 3 n` in Lean).

## The fault

Under an uncountable regime, the rules name a unit's leaf only at the end of the
matrix. A final leaf gets its upgrade (Fix B 3: one sub-unit per `Ω`). A leaf with
more after it gets nothing, and the next unit is written the same way for every
level that shares the leaf's row-1 value. With `X = M(Ω_{Ω_Ω}+Ω_{Ω_2})`, which ends
`…(7,4,0)(8,5,1)(9,5,1)(10,3,0)(4,3,1)(5,3,1)(6,2,0)`:

| α | `TrioRules2.lean` |
|---|---|
| `Ω_{Ω_Ω}+Ω_{Ω_2}` | `X` |
| `Ω_{Ω_Ω}·2` | `X ++ (2,2,1)(3,2,1)(4,1,0)` |
| `Ω_{Ω_Ω}+Ω_{Ω_2}+1` | `X` without its sub-unit, `++ (9,5,0)(10,6,0)` |
| `Ω_{Ω_Ω}+Ω_{Ω+1}+1` | the same matrix |
| `Ω_{Ω_Ω}·2+1` | the same matrix |

The shared matrix lies above `M(Ω_{Ω_Ω}·2)`, because `(9,5,0) > (4,3,1)`. The same
happens one level down: `Ω_Ω+Ω_2+1` and `Ω_Ω·2+1` get one matrix.

## Which level the plain continuation belongs to

BMS decides it. The sheet's rows 4460 (`Ω_Ω·ω`) and 4748 (`Ω_{Ω_Ω}·ω`) agree with
the rules. Their expansions are

- `M(Ω_Ω·ω)[2] = M(Ω_Ω+Ω_2) ++ (7,4,0)(8,5,1)(9,5,1)(10,2,0)`,
- `M(Ω_{Ω_Ω}·ω)[2] = M(Ω_{Ω_Ω}+Ω_{Ω+1}) ++ (9,5,0)(10,6,1)(11,6,1)(12,3,0)`.

`TrioRules2.lean` gives these two matrices to `Ω_Ω+Ω_2·2` and `Ω_{Ω_Ω}+Ω_{Ω+1}·2`.
Then `M(·ω)[n]` would be `Ω_Ω+Ω_2·n`, and its limit `Ω_Ω+Ω_2·ω` is below `Ω_Ω·2`:
the fundamental sequence of a row of the sheet would not reach it. So the plain
continuation after a leaf belongs to the **top** level of that row-1 value (here
`Ω_Ω` and `Ω_{Ω_Ω}`), and `M(·ω)[n] = M(·n + Ω_2)`, `M(·n + Ω_{Ω+1})`. Every other
level needs a different continuation.

For a regime `r = Ω_w`, the top levels are `tops(r) = [r, w, w', …]` (while
`w = Ω_{w'}`). For `r = Ω_Ω` this is `[Ω_Ω, Ω, 1]`: `Ω_{Ω_Ω}` for row-1 value 3,
`Ω` for 2, `1` for 1.

## What BMS writes for a deeper level

BMS also shows what a different continuation looks like. The two marks below are
rows of the sheet or outputs of the rules:

- `M(Ω_{Ω_Ω}+Ω_ω)[1] = M(Ω_{Ω_Ω}+Ω_2) ++ C` (row 4743),
- `M(Ω_{Ω_Ω}+Ω_{Ω_ω})[1] = M(Ω_{Ω_Ω}+Ω_{Ω_2}) ++ C'`.

`C` and `C'` are **lifted copies**: the columns from `s₀` to the end, where `s₀` is
the row-1 parent of the last leaf (the nearest row-0 ancestor with a smaller row-1
value), each one `x + 1`, and `y + 1` exactly when its row-1 ancestry reaches `s₀`
(BMS ascension). The last leaf is lifted too, so `C` names `Ω_3` and `C'` names
`Ω_{Ω_3}`. The function `blift` in `TrioRulesNonLast.lean` reproduces `C`, `C'` and
the same copy for `M(Ω_Ω+Ω_ω)[1]` exactly.

## Fix N

Let the regime `r` be a tower over `1` (`r ∈ {Ω, Ω_Ω, Ω_{Ω_Ω}, …}`). When the last
leaf names a level `p` that is not in `tops(r)`, the `Ω`-chain of `p` ends in a
level without a mark (`1`, `2`, …; not `ω`), and another add unit or another digit
follows:

1. The leaf gets its upgrade now, as if it were last (Fix B 3).
2. A lifted copy is laid, with the last leaf **kept**: one below its lifted value.
   If `s₀` is the root of the previous lifted copy, that copy itself is lifted
   (`s₀` becomes its start).
3. After the copy: the level `p` is the cap (a later leaf naming `p` is top); a
   leaf naming `r` is one higher per copy; a leaf naming `p` takes the copy's last
   value when step 1 wrote no sub-unit; the first sub-unit of an upgrade, and a
   mark, are taken from the copy.
4. The next add unit continues from the last root. So does the next digit, except
   when step 1 wrote a sub-unit: then the unit is laid again under that
   sub-unit's root (anchor, root, and the digits so far), and the digit continues
   on that root.

The new matrices:

| α | Fix N, after `X` or after the shared prefix |
|---|---|
| `Ω_{Ω_Ω}+Ω_{Ω_2}+1` | `X ++ (2,2,0)(3,3,1)(4,3,1)(5,3,0)(3,3,1)(4,3,1)(5,3,0)(3,3,1)(4,3,1)(5,1,0)(4,3,0)(5,4,1)(6,4,1)(7,4,0)(5,4,1)(6,4,1)(7,3,0)(6,4,0)(7,5,1)(8,5,1)(9,4,0)(8,5,0)(9,6,1)(10,6,1)(11,4,0)(5,4,1)(6,4,1)(7,2,0)` `++ (6,4,0)(7,5,0)` |
| `Ω_{Ω_Ω}+Ω_{Ω+1}+1` | `M(Ω_{Ω_Ω}+Ω_{Ω+1}) ++ (4,3,0)(5,4,1)(6,4,1)(7,4,0)(5,4,1)(6,4,1)(7,2,0)(6,4,0)(7,5,1)(8,5,1)(9,4,0)(8,5,0)(9,6,1)(10,6,1)(11,3,0)` `++ (10,6,0)(11,7,0)` |
| `Ω_{Ω_Ω}·2+1` | `M(Ω_{Ω_Ω}+Ω_{Ω+1}) ++ (9,5,0)(10,6,0)` (as before) |
| `Ω_Ω+Ω_2+1` | `M(Ω_Ω+Ω_2) ++ (2,2,0)(3,3,1)(4,3,1)(5,3,0)(3,3,1)(4,3,1)(5,1,0)(4,3,0)(5,4,1)(6,4,1)(7,3,0)(6,4,0)(7,5,1)(8,5,1)(9,2,0)` `++ (8,5,0)(9,6,0)` |

In each case the kept copy lies below the lifted one (`Ω_{Ω_3}`, `Ω_{Ω+2}`, `Ω_3`),
so the order is `Ω_{Ω_2} < Ω_{Ω_2}+1 < Ω_{Ω_2}·2 < Ω_{Ω_Ω}·2 < Ω_{Ω_Ω}·2+1`.
This also settles `Ω_Ω+Ω_2+1` against rows 4457 (`Ω_Ω+Ω_ω`) and 4458 (`Ω_Ω·2`),
which [TRIO-SHEET-41.md](TRIO-SHEET-41.md) lists as open: it is now below both.

## Checks

The rules with Fix N against `TrioRules2.lean`. Standard form is yaBMS `bms -s`
(outside Lean). "Disagreements" counts pairs whose labels (`cmpOrd`) and matrices
are in different order; a collision counts, since the labels differ.

| check | `TrioRules2.lean` | Fix N |
|---|---|---|
| the 813 labels of the sheet and the 9 corrected labels | — | the same matrix on all 822 |
| the 783 chosen matrices: disagreements (306,153 pairs) | 0 | 0 |
| standard, on the sheet's labels | not at 3480 and the printed label of 3552 (and not at 3481, 3482, where the sheet's matrix is not standard either) | the same |
| the 71 nearby ordinals of the `TrioRules2` report: not standard | 15 | 15 (the same 15) |
| … disagreements with the 783 chosen matrices | 27 | 20 |
| … disagreements among themselves (2,485 pairs) | 37 | 25 |
| sums and products after `Ω_{Ω_Ω}` (179 labels): not standard | 0 | 0 |
| … disagreements (15,931 pairs); pairs with one matrix | 1,961; 220 | 1; 1 |
| sums and products after `Ω_Ω` (133 labels): not standard | 0 | 0 |
| … disagreements (8,778 pairs); pairs with one matrix | 912; 74 | 0; 0 |

Of the 71 nearby ordinals, Fix N changes exactly the 5 that `TrioRules2.lean` put
out of order: `Ω_{Ω_Ω}+Ω_{Ω+1}+1`, `Ω_{Ω_Ω}+Ω_{Ω_2}+1`, `Ω_{Ω_Ω}+Ω_{Ω_2}·2`,
`Ω_{Ω_Ω}·Ω_{Ω_2}·ω`, `Ω_{Ω_Ω}·Ω_{Ω+1}·ω`. All 5 are standard, as they were before, and
now in order. The remaining 20 disagreements with the chosen matrices come from other
regions (`Ω_{Ω+1}^ω`, `Ω_ω·Ω_2·…`, `Ω_{ψ_{Ω_{ω+1}}(Ω_{ω+1})·2}`); the 25 pairs among the 71
come from the same regions and from `Ω_{Ω_{ω+1}}+Ω_Ω`, `Ω_{Ω_{ω+1}}+Ω_{ω+1}`.

**Expansion.** 27 `#guard`s check `M(γ·ω)[n]` for `n = 1, 2` (only `n = 1` for
`Ω_{Ω_Ω}·Ω_{Ω_2}·ω`) against Fix N's matrices, for `γ·ω` in: `Ω_Ω·ω`, `Ω_{Ω_Ω}·ω`,
`Ω_{Ω_Ω}^2·ω`, `Ω_{Ω_Ω}+Ω_2·ω`, `Ω_{Ω_Ω}+Ω_{Ω+1}·ω`, `Ω_{Ω_Ω}+Ω_{Ω_2}·ω`,
`Ω_{Ω_Ω}·Ω_2·ω`, `Ω_{Ω_Ω}·Ω_{Ω+1}·ω`, `Ω_{Ω_Ω}·Ω_{Ω_2}·ω`,
`Ω_{Ω_Ω}+Ω_{Ω_2}+Ω_2·ω`, `Ω_{Ω_Ω}+Ω_{Ω+1}+Ω_2·ω`, `Ω_{Ω_Ω}+Ω_{Ω_2}+Ω_{Ω+1}·ω`,
`Ω_Ω+Ω_2·ω`, `Ω_Ω+Ω_2+Ω·ω`. Each expansion is Fix N's matrix of a label: the last `·ω`
becomes `·n` or `·(n+1)`, in some cases followed by a term with `Ω_{u+1}` (the pattern of
the sheet's rows, `(Ω_{Ω_u}·ω)[1] = Ω_{Ω_u}+Ω_{u+1}`).
For instance `M(Ω_{Ω_Ω}+Ω_{Ω_2}·ω)[n] = M(Ω_{Ω_Ω}+Ω_{Ω_2}·(n+1)+Ω_{Ω+1})` for
`n = 1, 2` (and for `n = 0` with yaBMS).

## How sure this is

- The plain continuation belongs to the top level: forced by the expansions of rows
  4460 and 4748.
- The lifted copy is BMS's own (the expansions of the marks above).
- Step 4 (laying the unit again after a sub-unit) is what makes the expansion of
  `Ω_{Ω_Ω}+Ω_{Ω_2}·ω` land on `Ω_{Ω_2}·(n+1)+Ω_{Ω+1}`; without it the expansion
  lands on no label.
- `M(Ω_{Ω_Ω}+Ω_{Ω_2}+1)` itself is not the expansion of a row of the sheet. It is
  fixed by the kept copy (the same copy BMS writes for `Ω_{Ω_3}`, with the leaf one
  lower), by the order and standard form above, and by the expansions of its
  neighbours. It is the best-supported candidate, not a derived matrix. (With Fix N,
  yaBMS gives `M(γ+ω)[1] = M(γ+1)` and `M(γ+ω)[2] = M(γ+2)` for
  `γ = Ω_{Ω_Ω}+Ω_{Ω_2}`, `Ω_Ω+Ω_2`, `Ω_{Ω_Ω}+Ω_{Ω+1}`. This fits, but it does not decide
  the matrix: `TrioRules2.lean` has `M(γ+ω)[1] = M(γ+1)` too.)

## Still open

1. **Other regimes.** Fix N acts only when the regime is a tower over `1`. For
   `r = Ω_ω`, `Ω_2`, `Ω+1`, … the base rules already collide on a last leaf
   (for example `Ω_{Ω_2}+Ω_{Ω+1}` and `Ω_{Ω_2}+Ω_3`, `Ω_{Ω_ω}+Ω_{ω+1}` and
   `Ω_{Ω_ω}+Ω_2`), so the top levels there are not known yet. Applying Fix N with
   `tops` to `r = Ω_ω` lowers the disagreements of a family of 170 sums after
   `Ω_{Ω_ω}` (3,263 → 814, a Python run) but adds collisions (38 → 44 groups), so it
   is left out.
2. **Levels with a mark** (`Ω_ω`, `Ω_{Ω_ω}`) that are not last: unchanged.
3. **Levels that no leaf with sub-units names**: `Ω_3`, `Ω_{Ω+2}`, `Ω_{Ω·2}`,
   `Ω_{Ω_2+1}`, `Ω_{Ω_3}` after `Ω_{Ω_Ω}`, and `Ω_3` after `Ω_Ω`. The rules are wrong
   even when they are last: `Ω_{Ω_Ω}+Ω_3` gets the matrix of `Ω_{Ω_Ω}+Ω_{Ω+1}`,
   `Ω_{Ω_Ω}+Ω_{Ω·2}` that of `Ω_{Ω_Ω}+Ω_2`, and the others are not standard. The expansions above show
   that they need the lifted copy with the leaf lifted (`M(Ω_{Ω_Ω}+Ω_ω)[1]` is
   `Ω_{Ω_Ω}+Ω_3`). Not implemented.
4. **One collision left** in the family after `Ω_{Ω_Ω}`:
   `Ω_{Ω_Ω}+Ω_{Ω_2}+Ω_2+Ω_2` and `Ω_{Ω_Ω}+Ω_{Ω_2}+Ω_2+Ω` get one matrix (after two
   lifted copies, `Ω_2` and `Ω` share the leaf value 1).
5. **Fix E and Fix N are separate.** Fix E ([`TrioRules3.lean`](TrioRules3.lean))
   changes rule 9 (`MpsiLevel`); Fix N changes `placeUnits` and the final upgrade.
   They touch different functions, so a builder with both is `MstepN` with
   `MpsiLevel2` replaced by `TrioRules3`'s `MpsiLevel3`.
