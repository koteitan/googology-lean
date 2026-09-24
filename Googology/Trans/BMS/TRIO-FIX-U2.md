[← Back](../README.md) | [English](TRIO-FIX-U2.md) | [Japanese](TRIO-FIX-U2-ja.md)

# Fix U2: rule 9 where Fix U is still wrong

This is a separate patch on top of [`TrioFixU.lean`](TrioFixU.lean) (rules 1–10 of
[koteitan/trio](https://github.com/koteitan/trio) with Fixes A–E, N and U). The code is in
[`TrioFixU2.lean`](TrioFixU2.lean). The checks are in [`TrioFixU2Sheet.lean`](TrioFixU2Sheet.lean).
For merging: in the step, replace `MpsiLevelU` by `MpsiLevelU2`.

## The two defects

[TRIO-FIX-U.md](TRIO-FIX-U.md) ("Still open") names two places where rule 9 is still wrong:

- **(a)** `u = Ω+k`, `w ≥ Ω_{Ω+1}` and `w` not headed by `ψ`. Example:
  `ψ_{Ω_{Ω+2}}(Ω_{Ω_{Ω+1}+Ω_Ω})`. `M(w)` is standard, but the result is not.
- **(b)** `u` of finite level `L ≥ 2`, `Ω_Ω < w < Ω_u`. For `u = Ω_2+1` almost every tried `w` gives a
  non-standard matrix.

Notation as in TRIO-FIX-U.md: `w` is the level of the argument (`X = Ω_w`), `M(v)` is the matrix
of `ψ_0(Ω_v)`, `base = low M(Ω_u)`, `P = M(ψ_{Ω_u}(Ω_{Ω_{L+1}}))`.

## Rule 9 faults and inherited faults

A rule-9 patch can only repair what rule 9 does to `M(w)`. So each probe label is sorted into one
of three classes (yaBMS [`bms -s`](https://github.com/koteitan/yaBMS) for standardness, `cmpOrd`
for the order of the labels, lexicographic order for the matrices):

- **ok**: the result is standard and in order with the other labels of the same `u`.
- **inherited**: not ok, and `M(w)` itself is not standard, or `M(w)` is out of order with the
  other arguments. When two standard matrices are out of order, the one with more such pairs is
  blamed first (greedy). This can blame an innocent argument, so "inherited" is an upper bound.
- **rule-9 fault**: not ok, although `M(w)` is ok.

## The change

### 1. Fix K: `writeLevel` keeps foreign columns in place

Where neither Fix E nor Fix U changes rule 9, rule 9 is
`base ++ writeLevel(M(w)) ++ mark`. `writeLevel` copies the tail of `M(w)` (the columns after the
prefix that the ladders cover, rule 10) with one `x` shift. Some tail columns hang (row 0) from
another prefix column, not from the one the tail hangs from. A typical case is an upgrade mark
(rule 5) that hangs from an early storey anchor. The shift moves such a column away from its
parent.

`writeLevelK` copies such a column **as it is** (`x` and `y` unchanged) when its ancestor column
is also at the same index of `base`. Fix U's `reroot` already follows this rule ("columns that do
not hang from the moved part are copied as they are"). Fix K applies the same rule to
`writeLevel`.

Example (a): for `u = Ω+2` and `w = Ω_{Ω+1}+Ω_Ω`, `M(w)` ends in `(9,2,0)(2,2,1)(3,2,1)(4,1,0)`. The
mark `Ω_Ω` hangs from the storey anchor `(1,1,0)` (index 7), and `base` has the same column at
index 7.

| | end of `M(ψ_{Ω_{Ω+2}}(Ω_{Ω_{Ω+1}+Ω_Ω}))` | standard |
|---|---|---|
| rules / Fix U | `… (12,2,0)(5,2,1)(6,2,1)(7,1,0)` | no |
| Fix U2 | `… (12,2,0)(2,2,1)(3,2,1)(4,1,0)` | yes |

The other two counterexamples change the same way: `ψ_{Ω_{Ω+2}}(Ω_{Ω_{Ω+1}·Ω_Ω})`, and
`ψ_{Ω_{Ω+3}}(Ω_{Ω_{Ω+1}+Ω_Ω})` (`(6,3,1)(7,3,1)(8,1,0)` becomes `(2,2,1)(3,2,1)(4,1,0)`).

### 2. The shift row, for `L ≥ 2` and `Ω_Ω < w ≤ Ω_{Ω_L}`

For these `w`, `M(w) = M(Ω_Ω) ++ (1,1,0) ++ T`. Then

```
M(ψ_{Ω_u}(Ω_w)) = P ++ (L+1,L+1,1)(L+2,L+1,1)(L+3,1,0) ++ T[x + L+2]
```

This is Fix U's matrix for the argument `Ω_Ω`, followed by the rest of `M(w)`. The rest is moved
right so that the column `(1,1,0)` of `M(w)` falls on the `Ω` leaf `(L+3,1,0)`. Row 1 does not
change. The row is checked before Fix U's collapse row. For `L = 1` the range `(Ω_Ω, Ω_{Ω_1}]` is
empty, so the row adds nothing there.

Why it has this shape: `base = low M(Ω_u)` has, under its anchor `(L,L,0)`, the sibling subtrees
`(L+1,L+1,1)(L+2,L+1,1)(L+3,L+1,0)` and `(L+1,L+1,1)(L+2,L+1,1)(L+3,L,0) …`. A new child of that
anchor after `P` must not be larger than these siblings. The lifts of Fix U (`P ++ L'^L(M(w)[4:])`)
begin with `(L+1,L+1,1)(L+2,L+1,1)(L+3,L+1,0)`, which is larger, so they are never standard. The
shift row stays below: it starts with Fix U's `Ω_Ω`, `(L+3,1,0)`, and puts everything else under
that leaf. yaBMS agrees: `P ++ (3,3,1)(4,3,1)(5,2,0)` expands to
`P ++ (3,3,1)(4,3,1)(5,1,0)(6,2,1)(7,2,1)(8,2,0)(6,2,1)(7,2,1)(8,2,0)(6,2,0)…`, and this begins
with the shift-row image of `Ω_{Ω_2}`.

Example: `M(ψ_{Ω_{Ω_2+1}}(Ω_{Ω_Ω+1})) = P ++ (3,3,1)(4,3,1)(5,1,0)(6,2,1)(7,2,1)(8,2,0)(6,2,1)(7,2,1)(8,1,0)(7,2,0)(8,3,1)(9,3,1)(10,2,0)(9,3,0)(10,4,0)`
(standard; Fix U: `… (10,2,0)(8,4,1)(9,4,1)(10,1,0)(9,4,0)…`, not standard). Fix U put
`ψ_{Ω_{Ω_2+1}}(Ω_{Ω_{Ω_2}})` below `P = ψ_{Ω_{Ω_2+1}}(Ω_{Ω_3})`. Fix U2 puts it above the argument `Ω_Ω`.

### 3. Above `Ω_{Ω_L}`

For `Ω_{Ω_L} < w < Ω_{Ω_L+1}`, `M(w)` starts with `base`. There the old rule 9 with Fix K equals
Fix U's `reroot base P M(w)`. For example, `Ω_{Ω_2}+1` gives `P ++ (9,4,0)(10,5,0)`. This is the
same shape as Fix U's row `Ω_Ω < w < Ω_{Ω+1}` for `L = 1`. For `u = Ω_L+k` the region
`[Ω_{Ω_L+1}, Ω_u)` is also fine under Fix K. For other `u` (`Ω_2+Ω+1`, `Ω_2·2+1`) it is not (see
"Still open").

## Domain

`inDomainU2 u w` = Fix U's `inDomain u w`, or: `u` is an uncountable successor of finite level
`L ≥ 2`, `u ≤ w`, and (`u < Ω_L+ω`, or `w < Ω_{Ω_L+1}`). Fix U's domain is part of it
(`inDomain_le_U2`).

## Checks

The probe set has 2,097 labels `ψ_{Ω_u}(Ω_w)` with `u ≤ w < Ω_u`. It holds the 1,865 labels of Fix U
and the 106 review labels, plus 126 new ones for (a) and (b). There are 15 values of `u`, from
`Ω+1` to `Ω_Ω+1`, including `Ω+4`.

| region | Fix U: ok / inherited / rule-9 fault | Fix U2: ok / inherited / rule-9 fault |
|---|---|---|
| (a) `u = Ω+k`, `w ≥ Ω_{Ω+1}`, not `ψ`-headed | 49 / 25 / **41** | 90 / 25 / **0** |
| (b) `L ≥ 2`, `Ω_Ω < w < Ω_u` | 39 / 232 / **570** | 641 / 178 / **22** |
| `L ≥ 2`, `w ≤ Ω_Ω` | 190 / 6 / 0 | 190 / 6 / 0 |
| `u = Ω+k`, other `w` | 243 / 6 / 0 | 243 / 6 / 0 |
| other `u` (not claimed) | 225 / 140 / 331 | 229 / 116 / 351 |

All 2,097 labels:

| | Fix U | Fix U2 |
|---|---|---|
| not standard | 1,258 | 664 |
| pairs out of order (same `u`) | 38,461 | 15,939 |

No label that was standard under Fix U becomes non-standard. The one exception was an invalid
label, `ψ_{Ω_{Ω_2}}(Ω_{Ω_{Ω_2}+1})`, which was dropped. For every `u`, the number of pairs out of
order goes down or stays the same. The rule-9 fault count for "other `u`" rises from 331 to 351
only because some arguments there (nested `ψ_{Ω_{Ω_2+1}}(…)` and similar) become ok. Their faults
then count as rule 9's, no longer as inherited.

**The claimed domain.** Of the 2,097 labels, 1,559 are in `inDomainU2`. Of those, 225 have an
inherited fault. The other **1,334 labels are all standard (yaBMS) and in the order of the
labels, 0 disagreements**. That holds for pairs of the same `u` and for all 1,334 sorted together.
In Lean (`TrioFixU2Sheet.lean`, Part 5), the sorted check also holds with the 784 chosen labels
added. Under Fix U's matrices it fails.

The sheet file takes about 20 minutes to check. It belongs to the library `GoogologySheets`:
on merge, add `import Googology.Trans.BMS.TrioFixU2Sheet` to `GoogologySheets.lean`, and
`import Googology.Trans.BMS.TrioFixU2` to the main library.

**Unchanged.** Fix U2 changes none of the 1,209 labels of the sheet corpus (Part 1), and none of
Fix U's 562 domain probes (Part 2). Of the Fix U domain labels in the probe set, Fix U2 changes
exactly 48: the (a) labels. 41 of them become standard. 7 stay non-standard because `M(w)` is not
standard (`+Ω_ω`, `·Ω_ω`, `+Ω_{ω²}`).

**Expansion.** For the shift-row labels of the domain, BM4 expansion commutes with the
construction, `(image of M(w))[n] = image of (M(w)[n])`, in 1,492 of 1,698 cases (`n = 0, 1, 2`).
All 206 failures have `n ≥ 1`, and in all of them the bad root of `M(w)` lies in the head
`M(Ω_Ω) ++ (1,1,0)` (column 0). This is the same situation as Fix U's lifts (see TRIO-FIX-U.md).

## What is proved

In [`TrioFixU2.lean`](TrioFixU2.lean), with no `sorry`, no new axiom and no `native_decide`
(axioms: `propext`, `Classical.choice`, `Quot.sound` at most):

- `writeLevelK_false`: without keeping, `writeLevelK` is `writeLevel` (with `arg = true`).
- `MpsiLevelK_false`: without keeping, `MpsiLevelK` is `MpsiLevel2`. So Fix K changes only the
  kept columns.
- `writeLevelK_size`: Fix K writes as many columns as `writeLevel`.
- `MstepU2_notPsi`: on every `α` that is not `ψ_{Ω_u}(X)`, the step is `MstepAll`'s.
- `MstepU2_psi`: on `α = ψ_{Ω_u}(X)` the step is `MpsiLevelU2`, and Fix U's is `MpsiLevelU`.
- `MpsiLevelU2_of_not`: for `u ≤ Ω` and for a limit `u`, rule 9 is Fix U's, which is `MpsiLevel3`.
- `MpsiLevelU2_of_countable_arg`: for a countable argument, rule 9 is Fix U's.
- `MpsiLevelU2_of_fixed`: outside the shift row, where Fix E or Fix U changes rule 9, Fix U2
  keeps that matrix.
- `MstepU2_eq_MstepU`: when Fix U2 does not fire, the step is Fix U's.
- `shiftRow_size`, `shiftRow_prefix`: the shift row has `P.size + 3 + (m.size − 8)` columns and
  starts with `P ++ (L+1,L+1,1)(L+2,L+1,1)(L+3,1,0)`.
- `WF3_trioRuleMatrixU2`: every column has three rows and `z < 2`.
- `inDomain_le_U2`: Fix U's domain is part of Fix U2's.

Nothing is proved about standardness or order. Those are the numerical checks above.

## Still open

1. **Inherited faults** (225 domain labels). `M(w)` itself is not standard or not in order. For
   example: `M(Ω_{Ω+1}+Ω_ω)`, `M(Ω_{Ω+1}·Ω_ω)`, `M(Ω_{Ω+1}+Ω_{ω²})`, `M(Ω_{Ω·2}+1)`,
   `M(Ω_{ψ_1(Ω_2)}+1)`, `M(ψ_{Ω_{Ω+ω}}(…))`, `M(ψ_{Ω_{ψ_1(Ω_2)}}(…))` are not standard.
   `M(Ω_{Ω+1}^Ω)`, `M(Ω_{Ω+1}^{Ω_Ω})` and `M(Ω_{Ω+1}^{Ω_{Ω+1}})` collide with `M(Ω_{Ω+1}^2)`. These are
   faults of the sum/product branch or of rule 9 one level down, not of this rule 9.
2. **`L ≥ 2`, `u` not of the form `Ω_L+k`, `w ≥ Ω_{Ω_L+1}`** (22 labels for `u = Ω_2+Ω+1` and
   `Ω_2·2+1`). This is the `L ≥ 2` analogue of Fix U's open item 1, and it is outside the domain
   (guard `openB` in the sheet).
3. **Level 1, `u` not `Ω+k`, `w ≥ Ω_{Ω+1}`**, **`u` of infinite level**, **limit `u`**,
   **countable `u`**: as in TRIO-FIX-U.md. Fix K also acts for an uncountable successor `u` of
   infinite level. It repairs some labels there, but nothing is claimed.
4. **No sheet row confirms the new matrices.** The evidence is standardness, order and
   expansion.

The 59 labels whose matrix was standard under Fix U and changes under Fix U2 are all in (b),
with `L ≥ 2`. Examples are `ψ_{Ω_{Ω_2+1}}(Ω_{Ω_{Ω_2}})` and the collapse arguments
`ψ_{Ω_{Ω_2}}(…)`. They were standard but out of order.
