[← Back](../README.md) | [English](TRIO-FIX-U.md) | [Japanese](TRIO-FIX-U-ja.md)

# Fix U: rule 9 for an uncountable `u` of finite level

This is a separate patch on top of [`TrioRulesAll.lean`](TrioRulesAll.lean), which has rules 1–10 of
[koteitan/trio](https://github.com/koteitan/trio) with Fixes A–E and N. The code is in
[`TrioFixU.lean`](TrioFixU.lean). The checks are in [`TrioFixUSheet.lean`](TrioFixUSheet.lean).

## The defect

[TRIO-SHEET-FIXES.md](TRIO-SHEET-FIXES.md) ("Still open") reports: with `u = Ω+1`, rule 9 gives a
non-standard or out-of-order matrix for every argument level `w` that was tried in `(Ω_2, Ω_Ω]`,
except level `ω` (Fix E). The same happens for the other uncountable `u`.

The wider probe of this patch confirms it. It uses 1,865 labels `ψ_{Ω_u}(Ω_w)` for 14 values of `u`
(see "Probe" below). Without Fix U, 337 of the 562 labels in the domain below are not standard
(yaBMS `bms -s`), and 3,080 pairs among them are out of order.

## Notation

- `M(v)` is the matrix of `ψ_0(Ω_v)` (the builder one step down).
- `u` has level `L` when `Ω_L ≤ u < Ω_{L+1}`. Fix U acts only on a successor `u = s+1` of finite
  level `L ≥ 1`.
- `base = low M(Ω_u)` is `M(Ω_u)` with the row-1 entry of its last column lowered by 1. Every
  `M(ψ_{Ω_u}(X))` starts with `base`.
- `P = M(ψ_{Ω_u}(Ω_{Ω_{L+1}}))` as the rules give it. For `u = Ω+1` this is row 4467 of the sheet.
- `mark = (L+1, L+1, 1)`. `P ++ mark` is the argument `Ω_{Ω_ω}`.
- `R_n = (P ++ mark)[n]` (BM4 expansion). `R_n` is the argument `Ω_{Ω_{L+1+n}}`.
- `L^k(m[4:])`: add `k` to `x` and `y` of every column of `m` from index 4 on.
- `L'^k(m[4:])`: add `k` to `x`; add `k` to `y` only on the columns whose row-1 ancestry reaches
  column 0.
- `reroot src img m`: `m` starts with `src`. The result is `img`, then the columns of `m` after
  `src`. A column that hangs (row 0) from one of the last three columns of `src` moves with it
  to the last three columns of `img`: `x + dx`, and on relative columns (rule 3) `y + dy`. Every
  other column is copied as it is.

## The change

`MpsiLevelU` replaces `MpsiLevel3` in rule 9. The cases are checked in this order:

| case | `M(ψ_{Ω_u}(Ω_w))` |
|---|---|
| `u` countable, a limit, or of infinite level | unchanged |
| `w` starts with a `ψ` and `M(w) = low M(Ω_t) ++ tail`, with `t = L+1` or `Ω+1 < t ≤ u` | `reroot (low M(Ω_t)) (low A_u(t)) M(w)` (collapse) |
| `w ≤ Ω_{L+1}` | unchanged |
| `w = Ω_m`, `L+1 < m < ω` | `R_{m-L-1}` |
| `Ω_m < w < Ω_{m+1}`, `L+1 ≤ m < ω` | `reroot (low M(Ω_{m+1})) (low R_{m-L}) M(w)` |
| `Ω_ω ≤ w < Ω_{ω+1}` | `P ++ L^L(M(w)[4:])` |
| `Ω_{ω+1} ≤ w < Ω_Ω` | `P ++ L'^L(M(w)[4:])` |
| `w = Ω_Ω` | `P ++ (L+1,L+1,1)(L+2,L+1,1)(L+3,1,0)` |
| `L = 1`, `Ω_Ω < w < Ω_{Ω+1}` | `reroot (low M(Ω_{Ω+1})) P M(w)` |
| otherwise | unchanged |

`A_u(t) = M(ψ_{Ω_u}(Ω_{Ω_t}))` by the same table. At `t = u` it is the formal leaf
`base ++ (a+1,y0,1)(a+2,y0,1)(a+3,y0,0)`, where `a` is the `x` of the last column of `base` and
`y0` is one more than its `y`. When a guard fails (the expected prefix is missing), the result is
the unchanged one.

For `L = 1`, the rows with `w < Ω_{Ω+1}` are the first version of this patch, left by an agent
that a rate limit stopped. This version adds two things:

1. **The collapse row for `t = 2`.** `ψ_1` and `ψ_{Ω_2}` arguments below `Ω_2` hang from the
   lowered leaf of `P`. Example: the rules give
   `M(ψ_{Ω_{Ω+1}}(Ω_{ψ_1(Ω_2)})) = low P ++ (10,3,0)` (ending in `(7,3,1)(8,3,1)(9,1,0)(10,3,0)`), which is not standard.
   Fix U gives `… (9,1,0)(10,2,0)`, which is standard and in order.
2. **The collapse row for `Ω+1 < t ≤ u`.** Nested arguments `ψ_{Ω_{Ω+2}}(…)`, … hang from the
   leaf of `A_u(t)`. Example: `M(ψ_{Ω_{Ω+2}}(Ω_{ψ_{Ω_{Ω+2}}(Ω_{Ω_Ω})}))` ends in
   `(11,4,1)(12,4,1)(13,1,0)(11,4,1)(12,4,1)(13,1,0)` under the rules (not standard). Fix U gives
   `(11,4,1)(12,4,1)(13,2,0)(2,2,1)(3,2,1)(4,1,0)`, the same shape as for `u = Ω+1`.

For `L ≥ 2`, the table is the same table with the index shifted: `2` becomes `L+1`. For
`u = Ω_2+1`: `P = M(ψ_{Ω_u}(Ω_{Ω_3}))`, the argument `Ω_{Ω_ω}` is `P ++ (3,3,1)`, and its
expansions are the arguments `Ω_{Ω_3}, Ω_{Ω_4}, Ω_{Ω_5}`. The rules give `Ω_{Ω_ω}` the matrix
`P` without its last column, then `(10,1,0)(8,4,1)`. That lies below `P = M(ψ_{Ω_u}(Ω_{Ω_3}))`.

## Why these rows

- **Collapse.** `ψ_{Ω_t}(Y)` lies just below `Ω_t`. Its matrix is `low M(Ω_t)` followed by the
  argument. In `ψ_{Ω_u}(Ω_w)`, the leaf of `A_u(t)` names `Ω_t`. So the argument part moves to
  hang from the lowered leaf of `A_u(t)`. For `u = Ω+1` and `t = Ω+1`, this is the first version's
  row `Ω_Ω < w < Ω_{Ω+1}`.
- **The index shift for `L ≥ 2`.** For `u = Ω+1` the first region above the level of `u` is
  `[Ω_2, Ω_ω)`, and `P` names `Ω_2`. For `u = Ω_L+1` the region is `[Ω_{L+1}, Ω_ω)`, and `P`
  names `Ω_{L+1}`. The same construction with `L+1` in place of 2 gives standard matrices in the
  right order. Other shapes fail: the rules' `Ω_{Ω_ω}` is below `Ω_{Ω_3}`, and a mark `(2,2,1)`
  gives non-standard expansions.
- **The lifts.** At `L = 2`, `P ++ L^2(M(w)[4:])` on level `ω` and `P ++ L'^2(M(w)[4:])` on
  `[Ω_{ω+1}, Ω_Ω)` are standard. The BM4 expansion commutes with the lift,
  `(P ++ lift(M(w)[4:]))[n] = P ++ lift(M(w)[n][4:])` for `n = 0, …, 3`, on exactly the arguments
  where it commutes at `L = 1` (Fix E). It fails for `n ≥ 1` only on `Ω_ω`, `Ω_ω·2` and `Ω_{ω²}`,
  where the bad root of the expansion lies in the dropped head `B`.

## Checks

All checks are `#guard`s: a calibration, not a theorem.

| check | result |
|---|---|
| Parts 1–7 of `TrioRulesAllSheet.lean`, with Fix U | all hold, with the same counts |
| labels of the sheet and the earlier checks (1,209 distinct) | Fix U changes none |
| Part 7 (one step against rules 1–10, by branch) | unchanged: 171/0, 32/6, 152/7, 870/257; `fixUFires` holds on no corpus label |
| 562 probe labels in the domain, order among themselves (157,641 pairs) | 0 disagreements (without Fix U: 3,080) |
| the 562 with the 784 chosen labels, sorted by the label order | matrices in the same order (without Fix U: not) |
| the 562 matrices, standard (yaBMS `bms -s`, outside Lean) | 562 / 562 (without Fix U: 225 / 562) |
| matrices that Fix U changes among the 562 | 403 |
| `L = 2` table: `P ++ (3,3,1)`, `R_n`, `Ω_Ω`, a sum in `(Ω_3, Ω_4)`, `ψ_2(Ω_3)` | as in the table |
| `L = 2` lifts: expansion commutes | on the same arguments as at `L = 1` |

### Probe

The probe labels are `ψ_{Ω_u}(Ω_w)` for `u` in `Ω+1`, `Ω+2`, `Ω+3`, `Ω+ω+1`, `Ω·2+1`, `Ω²+1`,
`Ω_2+1`, `Ω_2+2`, `Ω_2+Ω+1`, `Ω_2·2+1`, `Ω_3+1`, `Ω_4+1`, `Ω_ω+1`, `Ω_Ω+1`. The arguments `w` come
from a fixed list: sums and products of `Ω_v`, some `ψ_1`, `ψ_2`, `ψ_{Ω_2}`, `ψ_{Ω_3}` terms, and
for 23 uncountable `v` the terms `Ω_v`, `Ω_v+1`, `Ω_v·2` and nested `ψ_{Ω_v}(Ω_y)`. A label is kept
when `u ≤ w < Ω_u` and every `ψ_{Ω_v}(Y)` inside it has `Ω_v ≤ Y < Ω_{Ω_v}`. This gives 1,865
labels.

The domain `inDomain u w` (in `TrioFixU.lean`) needs an uncountable successor `u` and `u ≤ w`. The
label `w = u` is in it for every such `u` (this is the one domain label for `Ω_ω+1` and `Ω_Ω+1`,
where Fix U changes nothing). Above `u` it is:

- `u = Ω+k` for finite `k`: every `w`;
- any other successor `u` of level 1: `w < Ω_{Ω+1}`;
- a successor `u` of finite level `L ≥ 2`: `w ≤ Ω_Ω`, and nested `ψ_{Ω_u}(Ω_y)` with `y` again
  in the domain.

| `u` | in the domain | not standard (Fix U / rules) | outside | not standard (Fix U / rules) |
|---|---|---|---|---|
| `Ω+1` | 64 | 0 / 33 | 0 | – |
| `Ω+2` | 72 | 0 / 40 | 0 | – |
| `Ω+3` | 80 | 0 / 46 | 0 | – |
| `Ω+ω+1` | 60 | 0 / 40 | 30 | 27 / 27 |
| `Ω·2+1` | 59 | 0 / 40 | 45 | 30 / 35 |
| `Ω²+1` | 55 | 0 / 48 | 54 | 49 / 50 |
| `Ω_2+1` | 36 | 0 / 18 | 112 | 104 / 109 |
| `Ω_2+2` | 35 | 0 / 18 | 121 | 106 / 115 |
| `Ω_2+Ω+1` | 29 | 0 / 18 | 127 | 115 / 124 |
| `Ω_2·2+1` | 31 | 0 / 18 | 130 | 117 / 126 |
| `Ω_3+1` | 24 | 0 / 10 | 148 | 135 / 144 |
| `Ω_4+1` | 15 | 0 / 8 | 154 | 143 / 152 |
| `Ω_ω+1` | 1 | 0 / 0 | 180 | 169 / 169 |
| `Ω_Ω+1` | 1 | 0 / 0 | 202 | 181 / 181 |

Arguments `ψ_{Ω_v}(…) + δ` are left out of the probe. The rules already give them a wrong matrix
at the top level (see "Side findings").

## What is proved

In [`TrioFixU.lean`](TrioFixU.lean), with no `sorry`, no new axiom and no `native_decide`:

- `MstepU_notPsi`: on every `α` that is not `ψ_{Ω_u}(X)`, the step is `MstepAll`'s.
- `MstepU_psi`: on `α = ψ_{Ω_u}(X)` the step is `MpsiLevelU`, and `MstepAll`'s is `MpsiLevel3`.
- `MpsiLevelU_of_not`: for `u ≤ Ω` (every countable `u`) and for a limit `u`, rule 9 is unchanged.
- `MpsiLevelU_of_finLvl_none`: for `u` of infinite level, rule 9 is unchanged.
- `MpsiLevelU_of_countable_arg`: for a countable argument, rule 9 is unchanged.
- `tableU_of_le`: the table leaves every `w ≤ Ω_{L+1}` unchanged.
- `MstepU_eq_MstepAll`: when Fix U does not fire, the step is `MstepAll`'s.
- `reroot_prefix`, `rerootTail_size`, `reroot_size`, `liftLk_size`: `reroot src img m` starts with
  `img` and has `img.size + (m.size − src.size)` columns; the lift keeps `m.size − 4` columns.
- `WF3_trioRuleMatrixU`: every column has three rows and `z < 2`.

Nothing is proved about standardness or order. Those are the numerical checks above.

## Still open

1. **Level 1, `u` not of the form `Ω+k`, `w ≥ Ω_{Ω+1}`** (for example `u = Ω·2+1`, `Ω²+1`,
   `Ω+ω+1`). Rule 9 is unchanged there, except for the collapse row. Two constructions fail.
   (a) Moving the matrix of `u' = Ω+2` over to `u = Ω·2+1` (the argument part re-hung on the last
   storey of `M(Ω_u)`) gives `Ω_{Ω+1}+1` a matrix above `M(ψ_{Ω_u}(Ω_{Ω_{Ω+ω}}))[1]`, which is the
   natural candidate for `Ω_{Ω_{Ω+2}}`. (b) For `u' = Ω+k` with `k ≥ 3` there is no column
   correspondence at all: `M(Ω_{Ω+k})` is not a prefix of `M(Ω_u)`, and matching the last storeys
   sends `Ω_{Ω_{Ω+2}}` and `Ω_{Ω_{Ω+1}}` to the same matrix. For `u = Ω²+1`, the image of the
   collapse row at `t = u` equals the one at `t = Ω+1`, so those labels collide.
   This is why the domain stops at `Ω_{Ω+1}` for these `u`.
2. **Finite level `L ≥ 2`, `Ω_Ω < w < Ω_u`**, except nested `ψ_{Ω_u}` arguments. For `u = Ω_2+1`
   the region `[Ω_Ω, Ω_{Ω_2})` lies between the lifts and the top. Neither lift works there:
   `P ++ L'^2(M(w)[4:])` and the variant that keeps the `Ω` leaf at `y = 1` give non-standard
   matrices for all 20 tried `w` in `(Ω_Ω, Ω_{Ω_2})` (sums on `Ω_Ω`, `ψ_{Ω_{Ω+1}}` and
   `ψ_{Ω_{Ω+2}}` terms, `Ω_{Ω+1}` up to `Ω_{Ω²+1}`, `Ω_{ψ_1(Ω_2)}`, `Ω_{ψ_{Ω_2}(Ω_Ω)}`).
3. **`u` of infinite level** (`Ω_ω+1`, `Ω_Ω+1`, …) and **limit `u`**: rule 9 is unchanged. The
   sheet has no row for a limit `u`.
4. **Countable `u`** (`ω+1` with `Ω < w < Ω_ω`, [TRIO-SHEET-FIXES.md](TRIO-SHEET-FIXES.md)): not
   part of this patch.
5. **No sheet row confirms the new matrices.** The sheet has rows only at the first point of each
   uncountable `u` (and row 4467). The evidence is standardness, order, and expansion.
6. **`inDomain` is wider than the evidence** (found in review, with 110 more labels in `inDomain`).
   - `u = Ω+k`, `w ≥ Ω_{Ω+1}` not headed by `ψ`: rule 9 is unchanged there, and it is not standard
     although `M(w)` is: `ψ_{Ω_{Ω+2}}(Ω_{Ω_{Ω+1}+Ω_Ω})`, `ψ_{Ω_{Ω+2}}(Ω_{Ω_{Ω+1}·Ω_Ω})`,
     `ψ_{Ω_{Ω+3}}(Ω_{Ω_{Ω+1}+Ω_Ω})`. So "every `w`" for `u = Ω+k` does not hold.
   - When `M(w)` itself is not standard or out of order at the top level, Fix U keeps the defect:
     `w = Ω_Ω+Ω_3`, `Ω_{ψ(Ω)}+Ω_ω`, `Ω_{ω^ω}·Ω_3`, `ψ_{Ω_ω}(Ω_Ω)` (not standard), and the pairs
     `Ω_Ω+Ω_3 / Ω_Ω+Ω_ω`, `Ω_5 / ψ_{Ω_ω}(Ω_Ω)`, `Ω_{ψ(Ω_ω)} / ψ_{Ω_Ω}(Ω_Ω)`,
     `Ω_{Ω+1}^2 / Ω_{Ω+1}^{Ω_{Ω+1}}`, `Ω_{ω+1}·Ω_3 / Ω_{ω+1}^2` (out of order), and
     `M(ψ_2(Ω_Ω)) = M(ψ_{Ω_3}(Ω_Ω))`.

## Side findings

- **A sum headed by a `ψ_{Ω_v}` term** gets the matrix of `Ω_v + δ` at the top level:
  `M(ψ_{Ω_{Ω+1}}(Ω_{Ω+1}) + 1) = M(Ω_{Ω+1} + 1)`, a collision. The sum branch builds on
  `M(Ω_v)` where `v` is the `ψ`'s subscript. This is not rule 9, so Fix U does not touch it.
- `M(ψ_1(Ω_{Ω_2+1}))` is not standard at the top level, and `M(ψ_1(Ω_Ω)) = M(ψ_{Ω_2}(Ω_Ω))` while
  `cmpOrd` puts `ψ_1(Ω_Ω)` below `ψ_{Ω_2}(Ω_Ω)`.
- `M(Ω_{Ω²+1})` has the same leaf height as `M(Ω_{Ω+1})` (`y = 3`), which causes the collision in
  item 1 above.
