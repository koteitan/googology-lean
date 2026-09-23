[← Back](../README.md) | [English](TRIO-SHEET-4746.md) | [Japanese](TRIO-SHEET-4746-ja.md)

# Rows 4746, 4747, 4752 and 4753 of the trio sheet

[TRIO-SHEET-41.md](TRIO-SHEET-41.md) decides these four `S-c` rows of the sheet
[`tools/omega_alpha_rows.tsv`](https://github.com/koteitan/trio/blob/main/tools/omega_alpha_rows.tsv)
of [koteitan/trio](https://github.com/koteitan/trio) for the sheet. It notes that they were
"not confirmed independently": the only evidence was that the sheet's matrices are consistent and
the rules' matrices collide. This note gives other evidence. The checks are `#guard`s in
[`TrioSheet41Confirm.lean`](TrioSheet41Confirm.lean): a calibration, not theorems.

## Verdict

**All four rows are confirmed for the sheet.** For 4746 and 4752 two parts decide: the order
against the confirmed 4745 and 4751 rules out the rules' matrices, and the sub-unit law gives the
sheet's. The level of the last term agrees with the sheet there but does not separate it from the
rules. For 4747 and 4753 the level of the last term decides, and the collision with the (now
confirmed) 4746 and 4752 agrees.

The sub-unit law and the expansion form are weaker than they look. At `u = 2` (rows 4522, 4523,
outside the 744 rows) one sub-unit takes `Ω_{Ω_2}+Ω_3` straight to `Ω_{Ω_2}·2`. That is the rules'
shape at `u = Ω`. Only the level of the last term tells `u = 2` and `u = Ω` apart (part 5 and the
section on `u = 2`).

`M(α)` is the matrix of `ψ_0(Ω_α)`. Write `s₃ = (4,3,1)(5,3,1)(6,2,0)` and
`s₂ = (2,2,1)(3,2,1)(4,1,0)`. Rows 4744, 4745, 4750 and 4751 are confirmed in TRIO-SHEET-41.md
(4745 by expansion, 4744 and 4750 by shape, 4751 by its leaf). They are called "confirmed" below.

| row | `α` | sheet | rules 1–10 |
|---|---|---|---|
| 4746 | `Ω_{Ω_Ω}+Ω_{Ω_2}` | `M(4745) ++ s₃` | `M(4742) ++ s₃` |
| 4747 | `Ω_{Ω_Ω}·2` | `M(4745) ++ s₃ ++ s₂` | `M(4745) ++ s₃` (the sheet's 4746) |
| 4752 | `Ω_{Ω_Ω}·Ω_{Ω_2}` | `M(4751) ++ s₃` | `M(4749) ++ s₃` |
| 4753 | `Ω_{Ω_Ω}^2` | `M(4751) ++ s₃ ++ s₂` | `M(4751) ++ s₃` (the sheet's 4752) |

## 1. The sub-unit law

Let `m` end with a column `(x, L, 0)`. `subLaw m` is `m` followed by a copy of the last sub-unit
`(a,L,1)(a+1,L,1)(a+2,y,0)` in `m`, the one at the height `L` of the last column.

On 11 pairs of agreeing rows, `subLaw M(β) = M(β')`. Here `β'` is `β` with the innermost
successor `s+1` replaced by the least uncountable cardinal above `s`:

| `s+1 ↦` | pairs of agreeing rows |
|---|---|
| `0+1 ↦ Ω` (towers) | `Ω ↦ Ω_Ω ↦ Ω_{Ω_Ω} ↦ …`, 5 pairs up to `Ω_{Ω_{Ω_{Ω_{Ω_Ω}}}}` |
| `1+1 ↦ Ω` | `Ω_Ω+Ω_2 ↦ Ω_Ω·2`, `Ω_Ω·Ω_2 ↦ Ω_Ω^2`, `Ω_{Ω_Ω+Ω_2} ↦ Ω_{Ω_Ω·2}`, `Ω_{Ω_Ω·Ω_2} ↦ Ω_{Ω_Ω^2}` |
| `ω+1 ↦ Ω` | `Ω_{Ω_ω}+Ω_{ω+1} ↦ Ω_{Ω_ω}+Ω_Ω`, `Ω_{Ω_ω}·Ω_{ω+1} ↦ Ω_{Ω_ω}·Ω_Ω` |

The law also holds on the confirmed rows: `4742 ↦ 4744`, `4749 ↦ 4750`, and `4487 ↦ 4488`.

On the four rows it gives exactly the sheet:

- `subLaw M(4745) = sheet 4746`: `Ω_{Ω_Ω}+Ω_{Ω+1} ↦ Ω_{Ω_Ω}+Ω_{Ω_2}`, where `Ω+1 ↦ Ω_2`;
- `subLaw (sheet 4746) = sheet 4747`: `Ω_{Ω_Ω}+Ω_{Ω_2} ↦ Ω_{Ω_Ω}+Ω_{Ω_Ω}`, where `2 ↦ Ω`;
- `4751 ↦ 4752 ↦ 4753` in the same way.

The rules do something different. They append `s₃` to the `Ω_2` leaf of 4742 (and 4749), and they
write `·2` (and `^2`) with one sub-unit where the law needs two.

The limit of this evidence: no agreeing pair has an uncountable `s`, so the step `Ω+1 ↦ Ω_2`
extends the law and is not an instance of it. The step `2 ↦ Ω` is an instance, one level
further in. And the law fails on the pair 4522, 4523 (see the section on `u = 2`).

## 2. Order

- **The sheet.** Its four matrices lie on the correct side of all 744 agreeing rows and of the 4
  confirmed rows, under `cmpOrd`. The chains `4745 < 4746 < 4747 < 4748` and
  `4751 < 4752 < 4753 < 4754` hold.
- **Rules 1–10.** Their matrices for 4746 and 4752 lie below the confirmed 4745 and 4751, while
  the labels lie above. Their matrices for 4747 and 4753 lie on the correct side of every row.
- **What the order does not show.** Against the 744 agreeing rows alone, the rules' four
  matrices are also in order. So the agreeing rows alone cannot decide these rows. The order
  refutes the rules at 4746 and 4752 only through the confirmed 4745 and 4751.

## 3. Collision

The rules give 4747 the sheet's 4746, and 4753 the sheet's 4752. Once 4746 and 4752 are
confirmed, the rules' 4747 and 4753 are refuted by this collision.

## 4. Expansion

At `u = 1`, the agreeing rows 4458, 4459 and 4460 give

```
M(Ω_Ω·(k+1)) = M(Ω_Ω·ω)[k] ++ s₂      (k = 1, 2)
```

where `s₂` is the upgrade of the leaf `Ω_2` to `Ω_Ω`. At `u = Ω`, `M(Ω_{Ω_Ω}·ω)[1]` is the
confirmed 4745, and

```
sheet 4747 = M(Ω_{Ω_Ω}·ω)[1] ++ s₃ ++ s₂
```

This has the same form. The upgrade of the leaf `Ω_{Ω+1}` to `Ω_{Ω_Ω}` is `s₃ ++ s₂`, and it goes
through `Ω_{Ω_2}`. The corrected rules also give `M(Ω_{Ω_Ω}·3) = M(Ω_{Ω_Ω}·ω)[2] ++ s₃ ++ s₂`.
No row of the sheet expands to one of the four rows at `n ≤ 3` (checked with yaBMS on all 785
standard rows).

At `u = 2` the form has one sub-unit, as at `u = 1`:
`M(Ω_{Ω_2}·2) = M(Ω_{Ω_2}·ω)[1] ++ (3,3,1)(4,3,1)(5,2,0)` (rows 4522–4524, misprint corrected).
That is the rules' form at `u = Ω`. So this part does not decide the rows by itself.

## 5. The level of the last term

Take `M[1]` and look at the first new column. Its row-1 entry is `k` when the fundamental
sequence of the last term of `α` diagonalises at `Ω_{k+1}`. This holds on 83 agreeing rows:

| last term | level | `k` | agreeing rows |
|---|---|---|---|
| `Ω`, `Ω_Ω` | `Ω_1` | 0 | 61 |
| `Ω_2` | `Ω_2` | 1 | 19 |
| `Ω_3` | `Ω_3` | 2 | 3 |

The confirmed 4744 and 4750 (`+Ω_Ω`, `·Ω_Ω`) also give 0. The 83 rows are a sample. With yaBMS,
the law holds on every agreeing standard row whose last term has the level `Ω_{k+1}` for a finite
`k`: 132 of the 744 rows, `k` from 0 to 5, no exception.

`Ω_{Ω_2}` diagonalises at `Ω_2`, because its index `Ω_2` does. `Ω_{Ω_Ω}` diagonalises at `Ω_1`,
because `Ω_Ω` does. So the four rows need `1, 0, 1, 0`. The sheet gives `1, 0, 1, 0`. The rules
give `1, 1, 1, 1`: their 4747 and 4753 diagonalise at the level of `Ω_{Ω_2}`, not of `Ω_{Ω_Ω}`.

## The pair 4522, 4523 (`u = 2`)

Rows 4519–4535 are among the 28 rows whose sheet matrix is not standard, so they are not among
the 744 agreeing rows. In 4522, 4523 and 4524 the only defect is the misprint `(4,4,1)` for
`(4,3,1)`, the same as in row 4533. Corrected, the sheet gives the rules' matrix.

On this pair the sub-unit law adds one sub-unit and gives `Ω_{Ω_2}·2`. The relabelling of part 1
would give `Ω_{Ω_2}+Ω_Ω` (`3 = 2+1 ↦ Ω`). So the relabelling is not a law of all pairs.

Here `M(Ω_{Ω_2}·ω)[1] = M(Ω_{Ω_2}+Ω_3)`, so `M(Ω_{Ω_2}·2)` is `M(Ω_{Ω_2}·ω)[1]` plus one
sub-unit. That is what the rules do at `u = Ω`. The level of the last term separates the two
cases. The one sub-unit ends at level `Ω_2` in both cases (`k = 1`). That is right for `Ω_{Ω_2}·2`,
whose last term `Ω_{Ω_2}` is at `Ω_2`. It is wrong for `Ω_{Ω_Ω}·2`, whose last term is at `Ω_1`.
The sheet's second sub-unit `s₂` brings the level down to `Ω_1` (`k = 0`).

## The `+1` that is still open

The corrected rules place `Ω_{Ω_Ω}+Ω_{Ω_2}+1` above `Ω_{Ω_Ω}·2` (TRIO-SHEET-41.md, "still
open"). This does not count against the sheet's 4746 or 4747. The same defect already appears
between agreeing rows. Both rule sets give `Ω_Ω+Ω_2+1` one matrix, and that matrix lies above
4457 (`Ω_Ω+Ω_ω`) and 4458 (`Ω_Ω·2`), although the label lies below both. It is a defect of the
rules' `+1` after a final leaf. It needs its own fix.

## Changes to other files (not made here)

- **TRIO-SHEET-41.md** and **TRIO-SHEET-41-ja.md**:
  - Rows 4746, 4747, 4752 and 4753: change "S-c (not confirmed)" to "S-c". In the evidence
    column, cite this note.
  - Result table: remove "(4 of the 10 are not confirmed independently)".
  - "S-c" section: replace the paragraph "For 4746, 4747, 4752 and 4753 the only evidence is
    ..." with a pointer to this note.
  - "The rules fixed": remove "confirming rows 4746, 4747, 4752 and 4753 by other evidence" from
    "Still open". Add that the `+1` item occurs among agreeing rows too (`Ω_Ω+Ω_2+1`).
- **TrioSheet41.lean**: its comment `-- rows 4744, 4746` and the next ones may cite
  `TrioSheet41Confirm.lean`. Nothing else is needed.
- **`Googology/Trans.lean`**: add `import Googology.Trans.BMS.TrioSheet41Confirm` after
  `TrioRules2Sheet`.
- **`Googology/Trans/README.md`** and **`README-ja.md`**: add a row "BMS at three rows |
  `BMS/TrioSheet41Confirm.lean`, [TRIO-SHEET-4746.md](BMS/TRIO-SHEET-4746.md)" after the
  `TrioRules2` row. Its text: rows 4746, 4747, 4752 and 4753 confirmed for the table, by the
  sub-unit law, the order, the expansion form and the level of the last term. Calibration by
  `#guard`, not a theorem.
