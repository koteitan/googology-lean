[← Back](../README.md) | [English](TRIO-SHEET-FIXES.md) | [Japanese](TRIO-SHEET-FIXES-ja.md)

# Fix E: the printed label of row 3552

[TRIO-SHEET-41.md](TRIO-SHEET-41.md) reads row 3552 of the sheet
[`tools/omega_alpha_rows.tsv`](https://github.com/koteitan/trio/blob/main/tools/omega_alpha_rows.tsv)
as a label typo. The sheet's matrix belongs to `ψ_{Ω_{ω+1}}(Ω_β)`, with
`β = ψ_{Ω_{ω+1}}(Ω_{ω+1})`. The printed label is `ψ_{Ω_{Ω+1}}(Ω_β)`. For that printed label, the
rules (rules 1–10 and `TrioRules2.lean` alike) give a matrix that is not standard. This note
explains why, gives the matrix of the printed term, and adds one correction, Fix E, in
[`TrioRules3.lean`](TrioRules3.lean). [`TrioRules3Sheet.lean`](TrioRules3Sheet.lean) checks the fix
against every row of the sheet. All checks are `#guard`s: a calibration, not a theorem.

## Notation

- `M(α)` is the matrix of `ψ_0(Ω_α)`.
- `ψ(w)` is short for `ψ_{Ω_{Ω+1}}(Ω_w)`. This region lies between row 4466 (`w = Ω+1`) and row
  4468 (`Ω_{Ω+1}`).
- `P` is `M(ψ(Ω+1))` without its last column. So `P` ends with the lowered leaf `(6,2,0)` of rule 9.
- `P₂ = M(ψ(Ω_2)) = P ++ (7,3,1)(8,3,1)(9,2,0)`. This is row 4467.
- `L(x,y,z) = (x+1, y+1, z)` lifts a column by one storey.

The printed label is `ψ(β)`. Its value `β = ε_{Ω_ω+1}` lies between `Ω_ω` and `Ω_{ω+1}`. So
`Ω_2 < β < Ω_Ω`.

## Why the rules give a non-standard matrix

Rule 9 writes the argument's level `w` with `writeLevel`. It copies the tail of `M(w)` after the
deepest level column that `M(w)` shares with the ladders `M(2)`, `M(Ω+1)` and the matrix so far.
Then it lifts only the z1 columns and the level columns, by the depth the context used up.

When `Ω_ω ≤ w`, `M(w)` starts with `B ++ (1,1,1)`. It shares no level column with any ladder. So
all of `M(w)[1:]` is copied, and it is lifted by 2. The `Ω` leaves are not lifted:

- The leaf `(3,1,0)` of `B` stays at `y = 1`. So every `ψ(w)` with `w ≥ Ω_ω` begins with
  `P ++ (7,3,1)(8,3,1)(9,1,0)`. This lies below `P₂ = M(ψ(Ω_2))`, although `w > Ω_2`. For
  example, `M(ψ(Ω_ω)) = P ++ (7,3,1)(8,3,1)(9,1,0)(7,3,1)` is below `M(ψ(Ω_2))`.
- For `w = β`, the lowered leaf `(5,1,0)` of `M(β)` also stays at `y = 1`, while the level column
  above it goes to `(8,3,0)`. The result is
  `P ++ (7,3,1)(8,3,1)(9,1,0)(7,3,1)(8,3,0)(9,4,1)(10,4,1)(11,1,0)(12,4,0)`. It is not standard
  (yaBMS `bms -s`), and it lies below `M(ψ(Ω_2))`.

A correction to TRIO-SHEET-41.md: its side finding says this matrix "lies above
`M(ψ_{Ω_{Ω+1}}(Ω_{Ω_2}))`". It lies below (`bms -c` gives `-1`). The label is the one above.

The failure is wider than this one row. With `u = Ω+1`, the rules give non-standard or
out-of-order matrices for every argument level `w` that was tried in `(Ω_2, Ω_Ω]`: `Ω_2+1`,
`Ω_3`, `Ω_ω`, `Ω_ω+1`, `β`, `Ω_{ω+1}` and `Ω_Ω`. The sheet has no row there except 4466 and 4467.

## The matrix of the printed term

```
M(ψ_{Ω_{Ω+1}}(Ω_β)) = P₂ ++ L(M(β)[4:])
  = (0,0,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,1)(3,1,0)(1,1,0)(2,2,1)(3,2,1)(4,2,0)(2,2,1)(3,2,1)
    (4,1,0)(3,2,0)(4,3,1)(5,3,1)(6,2,0)(7,3,1)(8,3,1)(9,2,0)(2,2,1)(3,2,0)(4,3,1)(5,3,1)(6,2,0)(7,3,0)
```

Here `M(β)` is row 3546 of the sheet. The evidence:

1. **Standard.** yaBMS `bms -s` gives `1`.
2. **Order.** Take the 783 matrices of the order check in `TrioRules2Sheet.lean` and add this one:
   784 matrices and 306,936 pairs. The order of the matrices is the order of the labels (`cmpOrd`)
   on every pair. In particular, the matrix lies between rows 4467 and 4468. With the 9 printed
   labels of the L rows added (792 matrices), the only exception left is row 4369's printed label,
   which is the normalisation defect of `ω^3·Ω`. Before the fix, row 3552 was the other exception.
3. **Expansion.** For `n = 0, …, 3`, the BM4 expansion commutes with the construction:
   `(P₂ ++ L(M(β)[4:]))[n] = P₂ ++ L(M(β)[n][4:])`. `EntriesR.lean` proves `expandRL 3 n` to be BM4
   expansion, and the checks use it. So the matrix has the fundamental sequence of `β` (towers of
   `Ω_ω`), one storey up.
4. **The base `Ω_ω`.** The construction puts the argument `Ω_{Ω_ω}` at `P₂ ++ (2,2,1)`. This is the
   leaf `(9,2,0)` naming `Ω_2`, with the upgrade mark `(2,2,1)` of rule 5 placed where the base
   `M(Ω_{Ω+1})` already has that mark. Agreeing row 4457 has the same shape at the top level:
   `M(Ω_Ω+Ω_ω) = … (8,2,0)(2,2,1)`. Expansion `[1]` of `P₂ ++ (2,2,1)` is `P₂` followed by one
   lifted storey whose last leaf is `(10,3,0)`. That is the argument `Ω_{Ω_3}` as rule 6 spells it,
   one storey per level. Every argument of level `ω` then stacks on this base, just as the top-level
   `M(Ω_ω + δ)` stacks on `M(Ω_ω) = B ++ (1,1,1)` (rule 2).
5. **Why not below the leaf.** In the region of `ψ_{Ω_{ω+1}}` (rows 3550–3552), arguments above
   `Ω_ω` hang below the leaf `(8,1,0)`. In the region of `ψ_{Ω_{Ω+1}}`, the columns below the leaf
   `(9,2,0)` are already taken by arguments of level `Ω`:
   - expansion `[2]` of row 4468 is `P₂ ++ (10,3,1)(11,3,1)`, a nested `ψ_{Ω_{Ω+1}}`;
   - `M(ψ(ψ_{Ω_{Ω+1}}(Ω_{Ω+1}))) = P₂ ++ (10,3,0)` has the expansions `P₂ ++ (10,2,0)(11,2,0)⋯`.

   Towers of that leaf reach `ε_{Ω_Ω+1}`. So the leaf with children names `Ω_Ω`, and level `ω`
   has to go elsewhere.

What this does not settle: no row of the sheet lies strictly between rows 4467 and 4468, so the
sheet does not confirm the matrix. The evidence is standardness, order, and expansion.

## Fix E

In [`TrioRules3.lean`](TrioRules3.lean), `MpsiLevel3` is used in place of `MpsiLevel2`. The fix
applies to rule 9 when `u = Ω+1` and the argument's level satisfies `Ω_ω ≤ w < Ω_{ω+1}`:

```
M(ψ_{Ω_{Ω+1}}(Ω_w)) = M(ψ_{Ω_{Ω+1}}(Ω_{Ω_2})) ++ L(M(w)[4:])
```

The guard `M(w)[0:5] = B ++ (1,1,1)` holds for every such `w`. Everything else is `TrioRules2.lean`
unchanged.

**Scope.** Only `u = Ω+1`, because that is the only uncountable `u` for which the sheet has a row
above the first point `ψ_{Ω_u}(Ω_u)` (rows 4466 and 4467). For `u = Ω+2`, `Ω_2+1`, `Ω_ω+1` and
`Ω_Ω+1` the sheet has only that first point (rows 4492, 4526, 4619, 4754).
Only level `ω`, because the lift does not carry beyond it:

- `L(M(Ω_{ω^ω})[4:])` ends in `(4,1,0)`. That is the mark `(2,2,1)(3,2,1)(4,1,0)` that rows
  4458/4464 give `Ω_Ω`.
- For the sheet rows from `Ω_{ω^ω+1}` to `Ω_{ψ_0(Ω_Ω)}` (rows 4382–4391, row 4384 under its
  corrected label `Ω_{ω^ω·2}`), the lifted matrices are not standard.

Below that point the lift keeps standardness. Take the 286 distinct sheet labels `a` with
`Ω_ω ≤ a < Ω_{ω^ω+1}` (96 of them have level `ω`). For each of them, `P₂ ++ L(M(a)[4:])` is
standard exactly when the rules' own `M(a)` is. It fails only for the labels of rows 3480–3482,
where `M(a)` is not standard either.

**Results** (`TrioRules3Sheet.lean`):

- On all 817 distinct labels (the 808 distinct labels of the 813 rows and the 9 corrected L
  labels), Fix E gives the matrix of `TrioRules2.lean`, except on the printed label of row 3552.
- The order check above has 0 disagreements.
- Python cross-check (a patched copy of the reference program): the same 817-label comparison,
  744/744 agreeing rows, and 0 disagreements on the 783 matrices.

## Side finding: row 3551

TRIO-SHEET-41.md rates row 3551 `ψ_{Ω_{ω+1}}(Ω_{Ω_ω})` as R (weak): the rules' `… (8,1,0)(6,2,1)`
over the sheet's `… (8,1,0)(1,1,1)`. Read by analogy, the expansions point the other way:

- `[1]` of the rules' matrix adds the unit `(6,2,0)(7,3,1)(8,3,1)(9,1,0)`: a second leaf naming
  `Ω` after the leaf `(8,1,0)`. This has the same shape as the unit `(4,2,0)(5,3,1)(6,3,1)(7,1,0)` in
  the rules' top-level `M(Ω_ω+Ω)`. Read that way, `[1]` is the argument `Ω_{Ω·2}` and `[2]` adds a
  third leaf. The fundamental sequence is then `Ω·n`, so the mark is the argument `Ω_{Ω·ω}`, not
  `Ω_{Ω_ω}`.
- `[1]` of the sheet's matrix is one lifted storey ending in the leaf `(9,2,0)`, the shape of the
  argument `Ω_{Ω_2}` in `P₂`. Read that way, this is the fundamental sequence `Ω_n` of `Ω_ω`.

This is a reading by analogy, not a calibration:
- The rules' own matrices for `ψ_{Ω_{ω+1}}(Ω_x)` with `x = Ω+1, Ω·2, Ω·ω, Ω_2` are not standard
  (yaBMS `bms -s`), so they cannot confirm either reading.
- The sheet has no row between 3550 and 3551.
- The order check passes with either matrix for row 3551.

So row 3551 leans to "the sheet is right", but the evidence is weak either way. Fix E does not
change row 3551. The guards are in `TrioRules3.lean`.

## Still open

- `u = Ω+1` with `Ω_2 < w < Ω_ω` (for example `Ω_2+1`, `Ω_3`) and with `Ω_{ω+1} ≤ w ≤ Ω_Ω`: the
  rules' matrices there are still non-standard or out of order.
- `u = ω+1` with `Ω < w < Ω_ω`: the rules' matrices for `ψ_{Ω_{ω+1}}(Ω_w)` with
  `w = Ω+1, Ω·2, Ω·ω, Ω_2` are not standard (see row 3551 above).
- The same question for the other uncountable `u` (`Ω+2`, `Ω·2`, `Ω_2+1`, …). There the rules' own
  `M(ψ_{Ω_u}(Ω_{Ω_2}))` is already doubtful, for example not standard at `u = Ω+ω`.
- `Ω_ν` leaves with `2 < ν < Ω` under an uncountable regime in general. The top level has the same
  weakness: `Ω_Ω+Ω_3` is not standard, and `Ω_Ω+Ω_{ω+1}` gets the same matrix as `Ω_Ω+Ω_2`.
  Compare the collisions for `β+Ω_2, β+Ω_3, β+Ω_ω, β·2` in [TRIO-ROW-3480.md](TRIO-ROW-3480.md).
