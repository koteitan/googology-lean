[← Back](../README.md) | [English](TRIO-SHEET-41.md) | [Japanese](TRIO-SHEET-41-ja.md)

# The 41 rows where the trio sheet and rules 1–10 disagree

`TrioRules.lean` transcribes rules 1–10 of
[koteitan/trio](https://github.com/koteitan/trio)
([algorithm page](https://github.com/koteitan/trio/blob/main/ebp2bms/algorithm/2/README-en.md)).
On 785 standard rows of the sheet
[`tools/omega_alpha_rows.tsv`](https://github.com/koteitan/trio/blob/main/tools/omega_alpha_rows.tsv),
744 rows agree with the rules. On the other 41 rows, the rules (and the reference program
[`tools/probe_eps_range.py`](https://github.com/koteitan/trio/blob/main/tools/probe_eps_range.py))
give a different matrix from the sheet. `TrioRulesSheet.lean` checks these rows with `≠` guards.

This note decides each of the 41 rows. It says which matrix is standard and which one keeps the
order of `α`.

**None of the 41 is a transcription error in `TrioRules.lean`.** On every row, the Lean
transcription gives the same matrix as the reference program. Where the rules are wrong, the error
is in the rules themselves.

The finite checks behind this note are in [`TrioSheet41.lean`](TrioSheet41.lean). They are
`#guard`s: a calibration, not theorems.

## Result

| verdict | rows | which side is right |
|---|---|---|
| L: the label in the sheet is a typo | 9 | both: the sheet's matrix is right for the corrected label, and the rules are right for the printed label |
| N: the sheet's matrix belongs to a nearby ordinal | 5 | the rules (for the printed label) |
| R: the rules are right, and the sheet's matrix names no row | 3 | the rules |
| S-o: the rules put the matrix in the wrong place in the order | 12 | the sheet |
| S-c: the rules give one matrix to two ordinals | 10 | the sheet (4 of the 10 are not confirmed independently) |
| X: not a `ψ_0(Ω_α)` row | 1 | out of scope |
| Z: neither side | 1 | the label is right; the matrix is a third one, `c2` ([TRIO-ROW-3480.md](TRIO-ROW-3480.md)) |

In total, the rules are right in 17 rows, the sheet in 22 rows, and neither in 1 row.

The algorithm page sorts the same 41 rows differently: 4 where the rules are right, 3 where the
sheet is right, and 34 undecided. This note moves 3552 from "the sheet is right" to L (it is a
label typo). It moves 3480 from "the sheet is right" to Z.

Check of the whole result: take the 744 agreeing rows, and for each of the other 39 rows (3439
and 3480 are left out) the matrix chosen here, under its corrected label. That gives 783
matrices. Over all 306,153 pairs of them, the order of the matrices is the order of the labels
(`cmp_ord`), and no two labels share a matrix. Adding the rules' matrices for the 9 printed labels
of the L rows gives 792 matrices and 313,236 pairs. Then there are exactly two exceptions: the
rules' outputs for the misprinted labels of rows 3552 and 4369. Those two outputs are themselves
defects of the rules; see "Side findings".

## How each row is decided

1. **Standard form.** yaBMS `bms -s` ([koteitan/yaBMS](https://github.com/koteitan/yaBMS)). All 41
   sheet matrices are standard. The rules' matrices are standard except at rows 3480, 3492 and 3552.
2. **Order.** For standard forms, the BMS order is the lexicographic order of the columns (yaBMS
   `bms -c`, and the order of `TrioMono.lean`). Each candidate matrix is compared with all 744
   agreeing rows. It must lie on the same side of each row as its label does. Labels are compared
   with the reference program's ordinal comparison `cmp_ord`. On the 744 agreeing rows, `cmp_ord`
   and the matrix order agree on all 276,396 pairs.
3. **Collisions.** If two different ordinals get the same matrix, at least one of them is wrong.
4. **Expansion.** `M[n]` is computed with yaBMS, or with `expandRL 3 n`, which `EntriesR.lean`
   proves to be BM4 expansion. Both keep `n + 1` copies of the bad part. Expanding an agreeing row
   can give the matrix of a row in question. Agreeing rows calibrate how this works, for example
   `(Ω_{Ω_u}·ω)[1] = Ω_{Ω_u} + Ω_{u+1}` at `u = 1, ω, ω²`.
5. **Shape.** Agreeing rows of the same kind show the shape a term takes. Examples: a final `+1`
   is a column with `z = 0`, a final `·ω` is a digit with `z = 1`, and `X^X` ends in two sibling
   leaves.
6. **Below `ε₀`.** Here the rules are `omegaIndexMatrix`. `TrioStd.lean` and `TrioMono.lean` prove
   this map standard and order-preserving.

## The rows

`M(α)` is the matrix of `ψ_0(Ω_α)`. "Printed" is the label in the sheet.

| row | printed `α` | verdict | evidence |
|---|---|---|---|
| 2113 | `ω^5·3` | L → `ω^5·2` | sheet = `omegaIndexMatrix(ω^5·2)` = `M(ω^6)[1]`; rules = `omegaIndexMatrix(ω^5·3)` = `M(ω^6)[2]` |
| 2131 | `ω^ω+ω·2` | L → `ω^ω+2` | the label is repeated at 2133; sheet = `omegaIndexMatrix(ω^ω+2)`; under the printed label it is out of order against 2132 |
| 2133 | `ω^ω+ω·2` | R | rules = `omegaIndexMatrix(ω^ω+ω·2)` = `M(ω^ω+ω²)[1]`; the sheet's `…(3,2,1)(3,2,0)(4,3,1)` is not the matrix of any ordinal tried |
| 2532 | `Ω^(Ω+1)` | L → `Ω^(ω+1)` | the label is repeated at 2538; the printed label is out of order against 6 rows |
| 2723 | `Ω_2·2+Ω` | L → `Ω_2·2+ω²` | the label is repeated at 2724 |
| 3439 | garbled | X | see below |
| 3452 | `Ω_ω·ω+Ω_ω+10` | L → `Ω_ω·ω+Ω_ω+1` | the source label is one `)` short; `10` is `1)` |
| 3453 | `Ω_ω·ω+Ω_ω·2` | N: sheet = `M(Ω_ω·ω+Ω_ω+Ω)` | the sheet leaves out the mark `(1,1,1)` (compare 3403 `Ω_ω·2+Ω` and 3404 `Ω_ω·3`); sheet = `M(Ω_ω·ω·2)[1]`, and `(Ω_ω·ω)[1] = Ω_ω+Ω` |
| 3480 | `Ω_ω·Ω+Ω_3` | Z | the rules' matrix is not standard; the sheet's is `M(Ω_ω·Ω+Ω_ω·ω)`; the right matrix is `c2` ([TRIO-ROW-3480.md](TRIO-ROW-3480.md)) |
| 3492 | `Ω_ω·Ω_2·ω` | S-o | the rules' matrix is not standard and lies above `M(Ω_ω·Ω_3)` (24 rows out of order) |
| 3551 | `ψ_{Ω_{ω+1}}(Ω_{Ω_ω})` | R (weak) | the rules write the `Ω_ω` mark inside the argument, `(6,2,1)`, as rows 2180, 2181 and 2552 do; the sheet writes `(1,1,1)` at the top level |
| 3552 | `ψ_{Ω_{Ω+1}}(Ω_{ψ_{Ω_{ω+1}}(Ω_{ω+1})})` | L → `ψ_{Ω_{ω+1}}(…)` | the row sits between 3551 and 3553, inside `ψ_{Ω_{ω+1}}`; under the printed label it is 209 rows out of order |
| 3706 | `Ω_{ω+1}+Ω_ω^2` | N: sheet = `M(Ω_{ω+1}+Ω_ω^{Ω_ω})` | `^2` is leaf, digit, leaf (3494); `^{Ω_ω}` is two sibling leaves (3543) |
| 3709 | `Ω_{ω+1}·2+Ω` | N: sheet = `M(Ω_{ω+1}·2+ω)` | `+Ω` ends with a digit and an `Ω` leaf, as in 3704 |
| 3777 | `Ω_{ω+2}+ω` | L → `Ω_{ω+2}+2` | the label is repeated at 3778 |
| 3923 | `ψ_{Ω_{ω2+2}}(Ω_{ω2+2})` | R | all 14 agreeing rows `ψ_{Ω_u}(Ω_u)` end in `(x,y−1,0)(x+1,y,0)`; the sheet ends in `(8,3,0)(9,3,0)` |
| 4303 | `X^X`, `X = Ω_{ω²+ω}` | N: sheet = `M(X^X^X)` | `X^X` ends in two sibling leaves (3886, 4340); `X^X^X` ends in a leaf and its child (2770, 3545) |
| 4369 | `Ω_{ω^3·Ω}` | L → `Ω_{ω^3}·Ω` | the source label is one `)` short |
| 4384 | `Ω_{ω²·2}` | L → `Ω_{ω^ω·2}` | the label is repeated at 4309 |
| 4488 | `Ω_{Ω+1}+Ω_Ω` | S-o | the rules' matrix lies below `M(Ω_{Ω+1}+Ω_2)`, and is the rules' `M(Ω_{Ω+1}+Ω)` |
| 4490 | `Ω_{Ω+1}·ω` | S-o | the rules' matrix lies below `M(Ω_{Ω+1}·2)` |
| 4491 | `Ω_{Ω+1}^2` | S-o | the same; the rules give 4490 and 4491 one matrix |
| 4496 | `Ω_{Ω+ω}+1` | N: sheet = `M(Ω_{Ω+ω}+ω)` | the other 90 standard `+1` rows end with `z = 0`; sheet`[1]` = the rules' matrix |
| 4497 | `Ω_{Ω+ω}·ω` | S-c | the rules' matrix is sheet`[0]` and has no final `·ω` digit, which all 33 agreeing rows `(X·ω)` have; the rules give `·ω` and `·Ω` one matrix |
| 4508 | `Ω_{ψ_1(Ω_2)}` | S-o | the rules' matrix lies below `M(Ω_{Ω^Ω})` (35 rows) |
| 4609 | `Ω_{Ω_ω}+Ω_ω` | S-o | the rules' matrix is row 4611's (`Ω_{Ω_ω}+Ω_{ω·2}`) |
| 4613 | `Ω_{Ω_ω}·2` | S-o | the rules' matrix lies below `M(Ω_{Ω_ω}+Ω_Ω)`; the sheet's is that matrix followed by `(1,1,1)` |
| 4618 | `Ω_{Ω_ω}^2` | S-o | the rules' matrix lies below `M(Ω_{Ω_ω}·Ω_Ω)` |
| 4628 | `Ω_{ψ_{Ω_{ω+1}}(Ω_{ω+1})}` | S-o | 19 rows out of order |
| 4667 | `Ω_{Ω_{ω²}}·2` | S-c | the rules give `·2` and `+Ω_{ω²}` one matrix; the sheet's matrix has the shape of 4613 |
| 4674 | `Ω_{ψ_{Ω_{ω²+1}}(Ω_{ω²+1})}` | S-o | 8 rows out of order |
| 4744 | `Ω_{Ω_Ω}+Ω_Ω` | S-c | the sheet ends `+Ω_Ω` with `(2,2,1)(3,2,1)(4,1,0)`, as in 4464, 4465 and 4761 |
| 4745 | `Ω_{Ω_Ω}+Ω_{Ω+1}` | S-c | `M(Ω_{Ω_Ω}·ω)[1]` = the sheet's matrix; this is `u = Ω` in the calibrated pattern `(Ω_{Ω_u}·ω)[1] = Ω_{Ω_u}+Ω_{u+1}` |
| 4746 | `Ω_{Ω_Ω}+Ω_{Ω_2}` | S-c (not confirmed) | the rules give 4744 and 4746 one matrix |
| 4747 | `Ω_{Ω_Ω}·2` | S-c (not confirmed) | the rules give 4745 and 4747 one matrix |
| 4750 | `Ω_{Ω_Ω}·Ω_Ω` | S-c | the same tail as 4744 |
| 4751 | `Ω_{Ω_Ω}·Ω_{Ω+1}` | S-c | the same leaf as 4745 |
| 4752 | `Ω_{Ω_Ω}·Ω_{Ω_2}` | S-c (not confirmed) | the rules give 4750 and 4752 one matrix |
| 4753 | `Ω_{Ω_Ω}^2` | S-c (not confirmed) | the rules give 4751 and 4753 one matrix |
| 4762 | `Ω_{ψ_{Ω_{Ω+1}}(Ω_{Ω+1})}` | S-o | 14 rows out of order |
| 4769 | `Ω_{Ω_{ψ_1(Ω_2)}}` | S-o | 20 rows out of order |

### L: typos in the label (9 rows)

For each of these rows, the sheet's matrix is exactly the rules' matrix of a corrected label. The
corrected label lies strictly between the neighbouring agreeing rows, so the sheet's row order
confirms it. There is textual evidence in each case:

- four labels are repeated elsewhere in the sheet (2131/2133, 2532/2538, 3777/3778, 4384/4309);
- 2723 repeats 2724;
- two source labels are one parenthesis short (3452, 4369). The script
  [`normalize_sheet.py`](https://github.com/koteitan/trio/blob/main/tools/normalize_sheet.py)
  adds the missing `)` at the end, which is the wrong place;
- 2113 says `·3` where its neighbours need `·2`;
- 3552 says `Ω+1` where its place in the sheet needs `ω+1`.

### N: the sheet's matrix is a neighbour's (5 rows)

For each of these rows, the printed label is plausible, and the rules' matrix for it has the shape
that agreeing rows of the same kind have. The sheet's matrix is the rules' matrix of a nearby
ordinal instead. This note cannot tell whether the slip is in the label or in the matrix. Either
way, the sheet's row does not give `M` of its label.

### R: the rules are right, and the sheet's matrix is unidentified (3 rows)

- **2133.** Below `ε₀` the rules are `omegaIndexMatrix`, which is proved standard and
  order-preserving. `M(ω^ω+ω²)[1]` gives the same matrix.
- **3923.** All 14 agreeing rows of the form `ψ_{Ω_u}(Ω_u)` use rule 9: the last leaf is lowered
  by one, and a column one level higher follows. The sheet's row does not.
- **3551** is weaker. Both matrices are standard and in order. The rules write the `Ω_ω` mark
  inside the collapse argument, at the column where the copied subscript starts. The agreeing rows
  2180 (`ψ_0(Ω_ω²)`), 2181 and 2552 do the same. The sheet puts `(1,1,1)` at the top level. No
  agreeing row of this kind does that.

### S-o: the rules leave the order (12 rows)

For each of these rows, the rules' matrix is out of order against at least one agreeing row. The
sheet's matrix is standard and lies strictly between its agreeing neighbours. There are three
groups.

- **A subscript of the form `ψ_{Ω_u}(Ω_u)` or `ψ_1(Ω_2)`** (4508, 4628, 4674, 4762, 4769). The
  rules' matrix is the base `M(Ω_{Ω_…})` with the last column dropped. It lies below rows such as
  `W_(W^W)`, far below its place.
- **Marks in the `Ω_{Ω_ω}` family** (4609, 4613, 4618). The sheet writes `Ω_ω` as the `Ω` form
  followed by the mark `(1,1,1)`. This is the same rule as `M(Ω_{Ω_ω}) = M(Ω_Ω) ++ (1,1,1)`, which
  is confirmed by `M(Ω_{Ω_ω})[0] = M(Ω_Ω)` and `M(Ω_{Ω_ω})[1] = M(Ω_{Ω_2})`.
- **Arithmetic on `Ω_{Ω+1}`** (4488, 4490, 4491) and **3492**.

### S-c: the rules give one matrix to two ordinals (10 rows)

The rules give pairs of ordinals the same matrix:

- 4744 and 4746, 4745 and 4747, 4750 and 4752, 4751 and 4753 (the `Ω_{Ω_Ω}` family);
- 4667 and `Ω_{Ω_{ω²}}+Ω_{ω²}`;
- 4497 and `Ω_{Ω+ω}·Ω`.

The sheet's matrices for these rows are distinct and in order. Some are also confirmed separately:

- **4745**, by expansion. `(Ω_{Ω_u}·ω)[1] = Ω_{Ω_u}+Ω_{u+1}` holds on agreeing rows at
  `u = 1, ω, ω²`. At `u = Ω` it gives the sheet's matrix for `Ω_{Ω_Ω}+Ω_{Ω+1}`. So in this region
  the address `y = 3` names `Ω_{Ω+1}`, not `Ω_3` as the rules read it.
- **4744 and 4750**, by shape: the `+Ω_Ω` tail of 4464, 4465 and 4761.
- **4497**, by shape: its final `·ω` digit.
- **4667**, by shape: it has the same form as 4613.

For 4746, 4747, 4752 and 4753 the only evidence is that the sheet's matrices are consistent with
everything else and the rules' matrices collide. These four rows are not confirmed independently.

### X: row 3439 is not a `ψ_0(Ω_α)` row

The source label is `psi(W_(W_w*w0*W_W_w+W_(W_w*w))`. The `0` is a slip for `)`, so the label is
`ψ_0(Ω_{Ω_ω·ω}·Ω_{Ω_ω} + Ω_{Ω_ω·ω})`. That matches its place between rows 3438 and 3440 of the full
sheet: its matrix lies strictly between theirs. The extraction took it for a pure row. The rules
read `w0` as `ω·0 = 0` and wrote `M(Ω_{Ω_ω·ω})`, which is row 4625's matrix.

### Z: row 3480, neither side

The label `Ω_ω·Ω+Ω_3` is right, and neither matrix is. The right matrix is `c2`: `M(Ω_ω·Ω+Ω_2)` followed by a second storey, built like the agreeing row 3377. It is proved standard in Lean (`trioStdL_c2`, [`TrioRow3480.lean`](TrioRow3480.lean)), it is `M(Ω_ω·Ω+Ω_ω)[1]`, and it lies in order between rows 3479 and 3483. The rules are wrong on the whole stretch from `Ω_ω·Ω+Ω_2` to `Ω_ω·Ω·2`, `TrioRules2.lean` included. The details are in [TRIO-ROW-3480.md](TRIO-ROW-3480.md).

## Side findings

- **The literal label of 3552.** The rules' matrix for `ψ_{Ω_{Ω+1}}(Ω_{ψ_{Ω_{ω+1}}(Ω_{ω+1})})` is
  not standard, and it lies above `M(ψ_{Ω_{Ω+1}}(Ω_{Ω_2}))`. The rules fail at this ordinal, which
  is not in the sheet.
- **`ω^3·Ω` is not normalised.** `mul` in the reference program and in `TrioRules.lean` builds the
  exponent `ω^(3+Ω)` as `.o [(.W 1, 1)]` instead of the atom `.W 1`. The rule `ω^atom = atom` is
  not applied. So `cmp_ord` calls `Ω_{ω^3·Ω}` equal to `Ω_Ω`, but the rules give the two different
  matrices (the literal label of 4369). The fix is a smart constructor for exponents: when
  `addExp e1 e` is a single atom with coefficient 1, use the atom itself. This must be done in both
  the reference program and `TrioRules.lean`, to keep them the same.

## The rules fixed

[`TrioRules2.lean`](TrioRules2.lean) is `TrioRules.lean` with four corrections. It gives the sheet's matrix on the 22 rows where the sheet is right (S-o and S-c) and the same matrix as before on the other 763 standard rows. Of the 28 non-standard rows, only row 4533 changes (Fix A), toward the sheet. [`TrioRules2Sheet.lean`](TrioRules2Sheet.lean) checks this with `#guard`s, and checks that the 783 chosen matrices are in the order of their labels (306,153 pairs, no disagreement; the old rules give 171).

- **Fix A, the base `M(Ω_v)`** (rows 4508, 4628, 4674, 4762, 4769). Drop the last column of `M(v)` only if its parent is a level column or the root; otherwise keep it.
- **Fix B, the uncountable regime** (rows 4488, 4609, 4613, 4618, 4667, 4744–4747, 4750–4753). A single `Ω_w` leaf gets `N(Ω_w) = N(w) + 1`; the old step at `r = Ω_v` is skipped; the final upgrade appends one sub-unit per `Ω` in the tower.
- **Fix C, `copy_storey` with one sub-unit left** (rows 4490, 4491, 4497). The other digits of the first add unit are laid on the copy's root.
- **Fix D, the countable regime** (row 3492). A non-last digit naming `Ω_p` with `p < r` and a higher leaf is lowered, with the storeys in between laid.

Still open: row 3480; the non-standard output for the printed label of row 3552; confirming rows 4746, 4747, 4752 and 4753 by other evidence; and `Ω_{Ω_Ω}+Ω_{Ω_2}+1`, which the fixed rules still place above `Ω_{Ω_Ω}·2`.
