[← Back](../README.md) | [English](TRIO-FIX-STRETCH.md) | [Japanese](TRIO-FIX-STRETCH-ja.md)

# Fix S: the stretch from `Ω_ω·Ω+Ω_2` to `Ω_ω·Ω·2`

[TRIO-ROW-3480.md](TRIO-ROW-3480.md) decides row 3480 of the sheet
[`tools/omega_alpha_rows.tsv`](https://github.com/koteitan/trio/blob/main/tools/omega_alpha_rows.tsv)
of [koteitan/trio](https://github.com/koteitan/trio). The matrix of `β+Ω_3` is `c2`, where
`β = Ω_ω·Ω`. The note also finds that the rules are wrong on the whole stretch from `β+Ω_2` to
`β·2`. This note describes a patch, Fix S, that makes the rules give the matrices the note asks
for.

- Code: [`TrioFixStretch.lean`](TrioFixStretch.lean). It is a separate patch on top of
  [`TrioRulesAll.lean`](TrioRulesAll.lean) (rules 1–10 with Fixes A–E and N).
- Checks: [`TrioFixStretchSheet.lean`](TrioFixStretchSheet.lean). It re-runs every check of
  [`TrioRulesAllSheet.lean`](TrioRulesAllSheet.lean) and adds the checks of Fix S.

## Notation

`M(α)` is the matrix of `ψ_0(Ω_α)`. `A[n]` is BM4 expansion (`expandRL 3 n`, yaBMS `[n]`). The
names are those of [TRIO-ROW-3480.md](TRIO-ROW-3480.md):

| name | matrix |
|---|---|
| `w1` | `M(β+Ω)` |
| `w2` | `M(β+Ω_2)`, which ends in the leaf `(8,2,0)` |
| `storey2` | `(2,2,0)(3,3,1)(4,3,1)(5,3,0)(3,3,1)(4,3,0)(5,4,1)(6,4,1)(7,3,0)(6,4,1)(7,1,0)(6,4,0)(7,5,1)(8,5,1)(9,3,0)` |
| `c2` | `w2 ++ storey2` |
| `lM` | `w2 ++ (2,2,1)` |
| `s2k` | `storey2` with its last leaf `(9,2,0)` instead of `(9,3,0)` |

## Result

| ordinal | `TrioRulesAll` | Fix S | standard (yaBMS) |
|---|---|---|---|
| `β+Ω_2+1` | `w2 ++ (7,4,0)(8,5,0)` | `w2 ++ s2k ++ (8,5,0)(9,6,0)` | yes |
| `β+Ω_2·ω` | starts with `w1`, below `w2` | `w2 ++ s2k ++ (8,5,1)` | yes (was no) |
| `β+Ω_2·Ω` | starts with `w1` | `w2 ++ s2k ++ (8,5,1)(9,1,0)` | yes (was no) |
| `β+Ω_2^2` | starts with `w1` | `w2 ++ s2k ++ (8,5,1)(9,2,0)` | yes (was no) |
| `β+Ω_3` (row 3480) | `w2` with the leaf `(8,3,0)` | `c2` | yes (was no) |
| `β+Ω_4` | `w2` with the leaf `(8,4,0)` | `lM[2]` | yes (was no) |
| `β+Ω_ω` (row 3481) | leaf `(8,3,0)`, then `(5,3,1)` | `lM` | yes (was no) |
| `β+Ω_ω+1` | leaf `(8,3,0)`, then `(7,4,0)(8,5,0)` | `w2 ++ (7,4,0)(8,5,0)` | yes (was no) |
| `β+Ω_ω·ω` | leaf `(8,3,0)`, then `(7,4,1)` | `w2 ++ (7,4,1)` | yes (was no) |
| `β·2` (row 3482) | leaf `(8,3,0)`, then `(7,4,1)(8,1,0)` | `w2 ++ (7,4,1)(8,1,0)` | yes (was no) |

On 69 labels from `β` to `β·ω`, all matrices are standard. Before Fix S, 54 of them were not.

## How the stretch is built

`α = β + …` has the countable regime `r = ω`: `α ≥ Ω_ω`, and `r` itself is countable. The unit
after `β` is *laid*. `β`'s last leaf `(8,1,0)` names `Ω`, and `leafY 1 = leafY ω`. So the builder
lays a storey for the unit first. That storey is `(1,1,0)…(6,1,0)`, part of `w1`.

Inside this storey the leaf value `L = leafY r + 1 = 2` does what the value `1` does on the base
`M(Ω_ω)`:

- the leaf `(8,2,0)` names `Ω_2`;
- the leaf `(8,2,0)` with the mark `(2,2,1)` names `Ω_ω`;
- `Ω_3`, `Ω_4`, … each need one more storey.

The new storey is BMS's own copy of the old one. `blift` of
[`TrioRulesNonLast.lean`](TrioRulesNonLast.lean) builds this copy. Every column moves one to the
right. A column moves up by one only when its row-1 ancestry reaches the storey root. The column
`(6,1,0)` has the root `(0,0,0)` as its row-1 parent, so it becomes `(7,1,0)`. The plain lift
`laySt` would make it `(7,2,0)`, which is not standard.

## The change

Fix S acts only in a countable regime `r`, and only on units *in the storey*. A unit is in the
storey when it is laid, when an earlier unit of `α` was laid, or when an S3 copy was laid before
it. Everything else is `TrioRulesAll`'s, unchanged.

- **S1, the leaf name.** A unit leaf naming `r` gets `L`. Before, it got the anchor level
  `Ctx.level`. A unit leaf naming `v < r` with `leafY v > L` also gets `L`. A leaf naming the cap of
  a copy keeps the copy's value.
- **S2, deep levels.** After a digit whose leaf of value `L` names `p < r` with `leafY p > L`, the
  builder appends `leafY p - L` lifted copies. Each copy lifts its leaf too, so
  `M(β+Ω_{2+k})` is `w2` followed by `k` copies.
- **S3, a leaf with more after it.** Before the next digit, the next unit or the next summand, the
  builder may lay Fix N's lifted copy, with the leaf kept (`fixN`). It does so when the last
  column is a leaf of value `> leafY r` that names `p < r`, where `p` has no mark and is not the
  cap of an earlier copy. Then `p` becomes the cap. The rest continues on the copy. This is the
  shape the note found for `β+Ω_2+1`, `β+Ω_2·ω`, `β+Ω_2·Ω` and `β+Ω_2^2`.
- **S5, no second storey.** In a unit in the storey, a spent leaf does not lay a new storey.
  BMS agrees:
  - `M(β+Ω·ω)[1] = w1 ++ (7,4,0)(8,5,1)(9,5,1)(10,1,0)`;
  - `M(β·ω)[2] = b1 ++ (7,4,0)(8,5,1)(9,5,1)(10,2,0)(9,5,1)(10,1,0)`.

  Both stay in the same storey.
- In a unit in the storey, **Fix D and the end-of-unit storeys are not used**. S1–S3 replace them.
  Outside the storey both are unchanged, so row 3492 `Ω_ω·Ω_2·ω` keeps Fix D.

For the merge: `placeUnitsS` is `placeUnitsN` with the lines marked `-- Fix S`, and `blockS` is
`blockN` with the lines marked `-- Fix S`. `MstepS` is `MstepAll` with these two in place of
`placeUnitsN` and `blockN`. The `ψ` and `Ω_v` branches are unchanged
(`MstepS_eq_MstepAll_of_ne`).

## Checks

All of these are `#guard`s in [`TrioFixStretchSheet.lean`](TrioFixStretchSheet.lean). Standard
form is checked outside Lean, with yaBMS `bms -s`.

- **The sheet.** On the 822 labels (813 rows and 9 corrected labels), Fix S changes exactly
  rows 3480, 3481 and 3482. Rows 3481 and 3482 are two of the 28 rows whose sheet matrix is not
  standard. Every other guard of `TrioRulesAllSheet.lean` holds unchanged, including the guards of
  Fixes A–E and N, the interaction checks, and the counts of the families.
- **The order.**

  | set | matrices | pairs | disagreements |
  |---|---|---|---|
  | chosen rows | 783 | 306,153 | 0 |
  | with row 3552 | 784 | 306,936 | 0 |
  | with row 3480 (`c2`) | 785 | 307,720 | 0 |
  | the 69 labels from `β` to `β·ω` | 69 | inside the family | 0 (307 before) |
  | the 69 labels against the 785 | 69 × 785 | | 0 |

  In the family, one collision is expected: `Ω_2·Ω_2` and `Ω_2^2` are the same ordinal.
- **BMS expansion.**
  - `lM[n] = M(β+Ω_{n+2})` for `n = 0, 1, 2`;
  - `M(β·ω)[n] = M(β·(n+1))` for `n = 1, 2`;
  - `M(β+Ω_2·ω)[n] = M(β+Ω_2·(n+1))` for `n = 1, 2`;
  - `M(β+Ω_2^ω)[n] = M(β+Ω_2^(n+1))` for `n = 1, 2`;
  - `M(β+Ω·ω)[1] = M(β+Ω·2)`, `M(β+Ω_3·ω)[1] = M(β+Ω_3·2)`, `M(β+Ω_ω·2)[1] = M(β+Ω_ω+Ω_3)`.
- **Step level.** On the 1,225 labels of `TrioRulesAllSheet.lean`, `MstepS` differs from `MstepAll`
  (same `Mf`) exactly on rows 3480, 3481 and 3482.
- **Wider probe.** The probe takes 21 bases (`Ω`, …, `Ω_Ω·Ω`), each with 25 tails: 525 labels.
  Fix S changes 98 of them, on the bases `β`, `β·2`, `Ω_ω·Ω^2`, `Ω_ω^2·Ω` and `Ω_{ω^2}·Ω`.
  - Order disagreements drop from 654 to 537. They grow on no base, and on the `β` bases they drop
    to 0.
  - Of the 98 changed matrices, 78 are standard, and 72 of those were not standard before.

## What is still wrong

- **`Ω_ω·Ω^2 + …`.** Here Fix S changes 19 matrices, but they stay non-standard (they were
  non-standard before too). This is the same kind of storey one factor higher, and it is outside
  the stretch.
- **`Ω_{ω^2}·Ω+Ω_ω·2`** stays non-standard. Here the leaf names a level with a mark (`Ω_ω`), which
  S3 does not cover.
- **The `Ω_ω` family.** Tails after the leaf `(8,2,0)` of `M(Ω_ω+Ω_2)` stay non-standard, as
  TRIO-ROW-3480.md says: `Ω_ω+Ω_2+1`, `Ω_ω+Ω_2·ω`, `Ω_ω+Ω_2^ω`, `Ω_ω+Ω_3+1`, and more. Fix S does
  not touch them, because no unit there is laid. The note's four forms on `M(Ω_ω+Ω_2)` suggest that
  the same lifted copy would fix them. That needs a rule for a leaf in a storey laid by the
  end-of-unit rule, which is not part of this patch.
- **The reading of each matrix as an ordinal is not proved.** As in TRIO-ROW-3480.md, it rests on
  calibration: the order, BMS expansion, and yaBMS standardness.
