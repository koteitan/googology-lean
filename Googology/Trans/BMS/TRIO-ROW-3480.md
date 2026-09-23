[← Back](../README.md) | [English](TRIO-ROW-3480.md) | [Japanese](TRIO-ROW-3480-ja.md)

# Row 3480 of the trio sheet: `ψ_0(Ω_{Ω_ω·Ω+Ω_3})`

[TRIO-SHEET-41.md](TRIO-SHEET-41.md) left one row open. Row 3480 of the sheet
[`tools/omega_alpha_rows.tsv`](https://github.com/koteitan/trio/blob/main/tools/omega_alpha_rows.tsv)
of [koteitan/trio](https://github.com/koteitan/trio) has the label `Ω_ω·Ω+Ω_3`. The rules'
matrix for that label is not standard. The sheet's matrix is standard, but it is the rules' matrix
of `Ω_ω·Ω+Ω·ω`.

This note decides the row.

## Verdict

**Neither side is right. The label is right, and the matrix is a third one.** Write
`β = Ω_ω·Ω`. Then

```
M(β+Ω_3) = (0,0,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,0)(3,2,1)(4,2,1)(5,1,0)(4,2,1)(5,1,0)
           (1,1,0)(2,2,1)(3,2,1)(4,2,0)(2,2,1)(3,2,0)(4,3,1)(5,3,1)(6,2,0)(5,3,1)(6,1,0)
           (5,3,0)(6,4,1)(7,4,1)(8,2,0)
           (2,2,0)(3,3,1)(4,3,1)(5,3,0)(3,3,1)(4,3,0)(5,4,1)(6,4,1)(7,3,0)(6,4,1)(7,1,0)
           (6,4,0)(7,5,1)(8,5,1)(9,3,0)
```

The first three lines are the rules' `M(β+Ω_2)`. The last two lines are a second storey. This
matrix is called `c2` in [`TrioRow3480.lean`](TrioRow3480.lean).

| | matrix | standard | what it is |
|---|---|---|---|
| sheet | `… (6,4,1)(7,4,1)(8,1,0)(7,4,1)` | yes | the rules' `M(β+Ω·ω)`, which is below `M(β+Ω_2)` |
| rules | `… (6,4,1)(7,4,1)(8,3,0)` | no | — |
| this note | `c2` above | yes (proved in Lean) | `M(β+Ω_3)` |

The label sits in the right place: row 3479 is `β+ω` and row 3483 is `β·ω`, and
`β+ω < β+Ω_3 < β·ω`. So the label is not a typo.

## Notation

In this note, `M(α)` is the matrix of `ψ_0(Ω_α)` and `β = Ω_ω·Ω`. `A[n]` is BM4 expansion with
`n+1` copies of the bad part. It is the same as yaBMS `[n]` and as `expandRL 3 n`. `A ++ B` puts
the columns of `B` after those of `A`. These are the matrices this note uses:

| name | matrix | reading |
|---|---|---|
| `w1` | `mβ S (5,3,0)(6,4,1)(7,4,1)(8,1,0)` | `M(β+Ω)` (rules) |
| `w2` | `mβ S (5,3,0)(6,4,1)(7,4,1)(8,2,0)` | `M(β+Ω_2)` (rules) |
| `c2` | `w2 ++ storey2` (`storey2` = the last two lines of the display) | `M(β+Ω_3)` |
| `lM` | `w2 ++ (2,2,1)` | `M(β+Ω_ω)` |
| `t2` | `w2 ++ (7,4,1)` | rules: `M(β+Ω_2·ω)`; this note: `M(β+Ω_ω·ω)` |
| `b1` | `w2 ++ (7,4,1)(8,1,0)` | `M(β·2)` |

Here `mβ = M(β)` (row 3460, first line of the display above), and `S` is the first storey (second
line of the display).

## How `c2` is built

`c2` repeats what the sheet does one level lower, on a row where the sheet and the rules agree:

```
M(Ω_ω+Ω_3) = M(Ω_ω+Ω_2) ++ (2,2,0)(3,3,1)(4,3,1)(5,3,0)(3,3,1)(4,3,0)(5,4,1)(6,4,1)(7,3,0)(6,4,0)(7,5,1)(8,5,1)(9,3,0)    (row 3377)
```

The added columns are the storey of `M(Ω_ω+Ω_2)` (its columns after `M(Ω_ω+Ω)`), with `(1,1,0)`
added to each column. Its last leaf `(9,3,0)` has the new storey root `(2,2,0)` as its row-1
parent. That is how the sheet writes `Ω_3`.

`c2` does the same to `w2`. There is one exception. The column `(6,1,0)` of the storey has the
root `(0,0,0)` as its row-1 parent, so a BM4 copy does not raise its row-1 entry. It becomes
`(7,1,0)`, not `(7,2,0)`. When `(7,2,0)` is used instead, the matrix is not standard.

## Evidence

1. **`c2` is standard.** yaBMS `bms -s` gives `1`. [`TrioRow3480.lean`](TrioRow3480.lean) proves
   `TrioStdL c2`, that is, `c2` is in the trio fragment (the closure of
   `(0,0,0)(1,1,1)(2,2,1)⋯` under `expandRL 3 n`). The proof has 63 steps from
   `(0,0,0)(1,1,1)(2,2,1)` to `lM`. Each step expands, then keeps a prefix. A prefix of a standard
   form is standard (`trioStdL_prefix`). One more step gives `c2 = lM[1]`. The theorems are
   `trioStdL_lM` and `trioStdL_c2`.
2. **Expansion.** `lM[0] = w2` and `lM[1] = c2`. On agreeing rows, a final mark steps the level of
   the last `Ω` by one per copy:
   - `M(Ω_ω·2)[n] = M(Ω_ω+Ω_{n+1})` for `n = 0, 1, 2` (rows 3338, 3376, 3377);
   - `M(Ω_ω^2)[n] = M(Ω_ω·Ω_{n+1})` for `n = 0, 1, 2` (rows 3460, 3491, 3493).

   `lM` does the same, one level higher, because the leaf of `w2` has the storey root `(1,1,0)`
   as its row-1 parent. So `lM[n] = M(β+Ω_{n+2})`: `lM[0] = M(β+Ω_2)` and `lM[1] = M(β+Ω_3)`.
3. **Order.** `M(β+ω) < c2 < M(β·ω)`, where these two are the agreeing rows next to the label
   (3479 and 3483). So `c2` is on the right side of all 744 agreeing rows. Checked one by one with
   the reference program's `cmp_ord`: 0 violations. A larger check also passes. It takes the 783
   matrices of TRIO-SHEET-41.md (744 agreeing rows and the 39 decided rows). It adds 14 matrices
   under the readings of this note:
   - `c2 = M(β+Ω_3)`, `lM = M(β+Ω_ω)` and `lM[2] = M(β+Ω_4)`;
   - `t2 = M(β+Ω_ω·ω)`, `w2 ++ (7,4,0)(8,5,0) = M(β+Ω_ω+1)`, `b1 = M(β·2)` and
     `M(β·ω)[2] = M(β·3)`;
   - the four matrices of point 4;
   - the rules' `M(β+Ω)`, `M(β+Ω·ω)` and `M(β+Ω_2)`.

   Then it compares all 317,206 pairs. In every pair the order of the matrices is the order of the
   labels, and no two labels share a matrix. All 14 matrices are standard (yaBMS).
4. **There is room below `c2`.** The ordinals `β+Ω_2+1`, `β+Ω_2·ω`, `β+Ω_2·Ω` and `β+Ω_2^2` must
   lie between `w2` and `c2`. They do: the second storey with the leaf `(9,2,0)`, followed by
   `(8,5,0)(9,6,0)`, `(8,5,1)`, `(8,5,1)(9,1,0)` or `(8,5,1)(9,2,0)`. All four are standard and in
   this order. The same four forms built on `M(Ω_ω+Ω_2)` are standard and lie below
   `M(Ω_ω+Ω_3)`, so the two families match here too.

## The other reading, and why it fails

The rules give `t2 = w2 ++ (7,4,1)` for `β+Ω_2·ω`. `t2` is standard, and `lM < t2` as matrices. If
`t2` were `M(β+Ω_2·ω)`, then `lM` and `c2` would lie below `β+Ω_2·ω`, so they could not be
`M(β+Ω_ω)` and `M(β+Ω_3)`. So one of the two readings has to go. Three things show that the rules'
reading is the one that fails.

- **`(X·ω)[1] = X·2`.** `M(β·ω)` is an agreeing row (3483), and `M(β·ω)[1] = b1 = t2 ++ (8,1,0)`.
  On agreeing rows, when `X` ends in a factor `Ω_v` with `v` a successor, the first expansion of
  `X·ω` is `X·2`:

  | `X` | `M(X·ω)[1]` | rows |
  |---|---|---|
  | `Ω_2·Ω` | `M(Ω_2·Ω·2)` | 2753 → 2752 |
  | `Ω^2` | `M(Ω^2·2)` | 2524 → 2523 |
  | `Ω_2^2` | `M(Ω_2^2·2)` | 2764 → 2763 |
  | `Ω_{ω+1}` | `M(Ω_{ω+1}·2)` | 3711 → 3707 |

  When the last factor is `Ω_ω`, it becomes `Ω` (`Ω_ω·ω → Ω_ω+Ω`, 3406 → 3338), and a factor
  `Ω_ω` in front of it stays (`Ω_ω^2·ω → Ω_ω^2+Ω_ω·Ω`, 3531 → 3527). `β = Ω_ω·Ω` ends in `Ω`,
  so `M(β·ω)[1] = M(β·2)`, that is, `b1 = M(β·2)`. The rules' reading gives `b1 = M(β+Ω_2·Ω)`
  instead. That would lower the leading factor `Ω_ω` to `Ω_2`, which no agreeing row does.
- **The leaf is raised when a digit follows.** Let `X = M(Ω_ω·ω+Ω)` (rules), which ends in the
  leaf `(7,1,0)`. Row 3454 (`Ω_ω·ω·2`) is `X ++ (6,3,1)`, and row 3451 (`Ω_ω·ω+Ω_ω`) is
  `X ++ (1,1,1)`; both are agreeing rows. So the leaf `(7,1,0)` names `Ω` when it ends the matrix,
  but with the digit `(6,3,1)` after it the term is `Ω_ω·ω`, not `Ω·ω`. The leaf of `w2` sits
  under the storey mark `(2,2,1)` in the same way. Measured from the storey root `(1,1,0)`
  (subtract `(1,1,0)` from each column), the chain of ancestors of `w2`'s leaf is
  `(0,0,0)(1,1,1)(2,1,0)(3,2,1)(4,2,0)(5,3,1)(6,3,1)(7,1,0)`. That is exactly the chain of the leaf
  of `X`. So `t2 = w2 ++ (7,4,1)` is
  `β+Ω_ω·ω`, and `b1 = t2 ++ (8,1,0)` is `β+Ω_ω·Ω = β·2`. This agrees with the first point.
- **It explains which tails are standard.** In the `Ω_ω` family, every tail after the leaf
  `(8,2,0)` of `M(Ω_ω+Ω_2)` is non-standard: `+ (7,4,0)(8,5,0)`, `+ (7,4,1)`, `+ (2,2,1)`. In the
  `β` family the same tails after `w2` are standard. With the raised leaf this is expected. In the
  `Ω_ω` family the tail would name an ordinal `≥ Ω_ω·2`, for example `Ω_ω+Ω_ω+1 = Ω_ω·2+1` or
  `Ω_ω+Ω_ω·ω`. But its matrix would lie below `M(Ω_ω·2) = M(Ω_ω+Ω) ++ (1,1,1)`, which is
  impossible. In the `β` family it names
  `β+Ω_ω·ω < β·2`, which is possible. The rules' reading gives no reason for the difference.

## Status

- Proved in Lean: `c2` and `lM` are standard (`trioStdL_c2`, `trioStdL_lM`), and `lM[1] = c2`.
- Checked (`#guard`s, yaBMS, the reference program): everything else above.
- Not proved: the reading of each matrix as an ordinal. As in TRIO-SHEET-41.md, it rests on
  patterns calibrated on agreeing rows. Here the calibration is `(X·ω)[1] = X·2`, the mark
  expansion, and the storey construction of row 3377. The verdict is at the level of the
  confirmed S-c rows there (for example 4745), not a theorem.

## Side findings

The rules are wrong on the whole stretch from `β+Ω_2` to `β·2`, not only on row 3480:

| ordinal | rules | this note |
|---|---|---|
| `β+Ω_2·ω` | `t2` (standard, but it is `β+Ω_ω·ω`) | the second storey with the leaf `(9,2,0)`, then `(8,5,1)` |
| `β+Ω_2^2` | `w2 ++ (7,4,1)(8,2,0)` (not standard) | the second storey with the leaf `(9,2,0)`, then `(8,5,1)(9,2,0)` |
| `β+Ω_3` | ends `(8,3,0)` (not standard) | `c2` |
| `β+Ω_ω` | ends `(8,3,0)(5,3,1)` (not standard) | `lM = w2 ++ (2,2,1)` |
| `β·2` | ends `(8,3,0)(7,4,1)(8,1,0)` (not standard) | `b1 = w2 ++ (7,4,1)(8,1,0)` |

The two sheet rows after 3480 are not standard, and each has the leaf `(8,3,0)` where this note has
`(8,2,0)`:

- row 3481 (`β+Ω_ω`) is `w2` with `(8,3,0)`, followed by `(2,2,1)`. With `(8,2,0)` it is `lM`.
- row 3482 (`β·2`) is `w2` with `(8,3,0)`, followed by `(7,4,1)`. The matrix of `β·2` is
  `b1 = w2 ++ (7,4,1)(8,1,0)`.

So the sheet and the rules both use the leaf `(8,3,0)` for a level that is written in BM4 as
`(8,2,0)` followed by more columns.

"Rules" in this section means rules 1–10 (`TrioRules.lean`). The corrected rules of
[`TrioRules2.lean`](TrioRules2.lean) give the same matrices for `β+Ω_2`, `β+Ω_3`, `β+Ω_ω` and
`β·2`. For `β+Ω_2·ω` and `β+Ω_2^2` they give new matrices that start with `w1`. Both are not
standard (yaBMS), and both are below `w2 = M(β+Ω_2)`, so they are also out of order. The fix of this
stretch is still open for `TrioRules2.lean`.

## Proposed changes to existing files (for the lead)

- `TRIO-SHEET-41.md`:
  - Table "Result": replace the O row by a row "Z: neither side; the label is right and the
    matrix is `c2` (see TRIO-ROW-3480.md)", 1 row.
  - Row 3480 of "The rows": verdict `Z`; evidence "`M(β+Ω_3) = M(β+Ω_2)` followed by a
    second storey, as in row 3377; `= M(β+Ω_ω)[1]`; see TRIO-ROW-3480.md".
  - Section "O: row 3480 is open": replace it with a short summary of this note and a link.
  - Paragraph "Check of the whole result": 3480 can now be included. That gives 784 matrices and
    306,936 pairs; with the 13 other matrices of this note, 797 matrices and 317,206 pairs, all
    in order.
  - "In total, the rules are right in 17 rows and the sheet is right in 22 rows": add "and neither
    side in 1 row (3480)".
- `TRIO-SHEET-41-ja.md`: the same changes.
- `TrioSheet41.lean`: the comment at the guard for row 3480 can point to `TrioRow3480.lean`.
- `TrioRules2Sheet.lean`: the section "Rows 3439 and 3480: unchanged" calls row 3480 `O`; it can
  say `Z` and point to `TrioRow3480.lean`. Its order check of 783 matrices can take `c2` as a 784th.
- `TRIO-SHEET-41.md`, the paragraph on `TrioRules2.lean` (783 matrices, 306,153 pairs): the same
  update, and a note that `TrioRules2.lean` is still wrong from `β+Ω_2` to `β·2` (see "Side
  findings").
- `Googology/Trans.lean`: add `import Googology.Trans.BMS.TrioRow3480`.
- `Trans/README.md` (and `-ja`), index: add a row for `BMS/TrioRow3480.lean`: "row 3480 of the
  trio sheet: `M(Ω_ω·Ω+Ω_3)`, proved standard".
- `plan.md`: remove "row 3480" from what is left of the 41 rows. Add "the rules are wrong from
  `β+Ω_2` to `β·2`" as an item of the rule fixes.
