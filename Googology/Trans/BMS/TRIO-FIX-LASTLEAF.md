[← Back](../README.md) | [English](TRIO-FIX-LASTLEAF.md) | [Japanese](TRIO-FIX-LASTLEAF-ja.md)

# Fix L: a last leaf that one column cannot name

A patch on top of [`TrioRulesAll.lean`](TrioRulesAll.lean) (rules 1–10 of
[koteitan/trio](https://github.com/koteitan/trio) with Fixes A–E and N). The rules are
in [`TrioFixLastLeaf.lean`](TrioFixLastLeaf.lean); the checks are in
[`TrioFixLastLeafSheet.lean`](TrioFixLastLeafSheet.lean). All checks are `#guard`s: a
calibration, not a theorem.

`M(α)` is the matrix of `ψ_0(Ω_α)`. `M[n]` is BM4 expansion with `n + 1` copies of the
bad part (yaBMS `[n]`, `expandRL 3 n` in Lean). `r` is the regime, `tops(r) = [r, w, w', …]`
for `r = Ω_w`, `w = Ω_{w'}`, … ([TRIO-NONLAST-LEAF.md](TRIO-NONLAST-LEAF.md)).

## The fault

Open item 3 of [TRIO-NONLAST-LEAF.md](TRIO-NONLAST-LEAF.md). Under a tower regime, a
unit's last leaf names its level `Ω_p` with one column and an upgrade. For these `p`
that is wrong even when the leaf is the last column (`TrioRulesAll.lean`):

| α | `TrioRulesAll.lean` |
|---|---|
| `Ω_{Ω_Ω}+Ω_3` | the matrix of `Ω_{Ω_Ω}+Ω_{Ω+1}` |
| `Ω_{Ω_Ω}+Ω_{Ω·2}` | the matrix of `Ω_{Ω_Ω}+Ω_2` |
| `Ω_{Ω_Ω}+Ω_{Ω+2}`, `Ω_{Ω_Ω}+Ω_{Ω_2+1}`, `Ω_{Ω_Ω}+Ω_{Ω_3}` | leaf `(10,4,0)`: not standard |
| `Ω_Ω+Ω_3` | leaf `(8,3,0)`: not standard |

## The change

`MstepFix Mf α = MstepAll Mf α`, except when `lastLeafFix Mf α = some cs`; then it is `cs`.
`lastLeafFix` acts only when

* `α` takes the sum branch of `MstepAll` (not countable, not `ψ_{Ω_u}(X)`, not `Ω_r`);
* `r` is a tower over `1` (`Ω`, `Ω_Ω`, `Ω_{Ω_Ω}`, …);
* the last term of `α` is `Ω_p·c`, or `ω^β·c` with `β` ending in `Ω_p·k`, and that `Ω_p`
  is the level the last leaf names;
* `p ∉ tops(r)`.

Write `rb(q)` for `α` with that last `Ω_p` replaced by `Ω_q`, `b` for the base of the
`Ω`-chain of `p` (`p = Ω_{Ω_{…b}}`), and `p[b := b']` for the chain with its base replaced.
`L(B)` is the lifted copy of `B[s₀:]` (Fix N's `blift`, with the last leaf lifted, not
kept), where `s₀` is the row-1 parent of the last column of `B`, moved to the start of an
earlier lifted or kept copy of `B[s₀:f]` while there is one (`copyRoot`). The four cases:

| case | when | `M(α)` | fixes |
|---|---|---|---|
| L | `b = c + m`, `c = 0, m ≥ 3` or `c = Ω_w, m ≥ 2` | `B ++ L(B)`, `B = M(rb(p[b := c+(m−1)]))` | `Ω_3`, `Ω_4`, `Ω_{Ω+2}`, `Ω_{Ω_3}`, `Ω_{Ω_2+2}` |
| K | `p = Ω_w + 1`, `Ω_w ∉ tops(r)`, `M(chainBase Ω_w)` without a suffix | `B`, its kept copy (Fix N 2), then `(x+1,y,0)(x+2,y+1,1)(x+3,y+1,1)(x+4,N(r)+1,0)` on the last root `(x, y)`; `B = M(rb(Ω_w))` | `Ω_{Ω_2+1}` |
| K' | `p = Ω_w + ω^k` | K, then the mark of `M(p)` (`appendSuffix`) | `Ω_{Ω_2+ω}` |
| D | `b = Ω_w·2`, `Ω_w ∈ tops(r)` | `B` with its last leaf set to `N(w)`, `B = M(rb(p[b := Ω_{w+1}]))` | `Ω_{Ω·2}` |

`N(v)` is Fix B's leaf name in a fresh state. In every other case the step is
`MstepAll`'s.

The new matrices. `P` is the first 34 columns of `M(Ω_{Ω_Ω}+Ω_2)`, ending `(7,4,0)(8,5,1)(9,5,1)`:

| α | Fix L, after `P` |
|---|---|
| `Ω_{Ω_Ω}+Ω_3` | `(10,2,0)` `++ (2,2,0)(3,3,1)(4,3,1)(5,3,0)(3,3,1)(4,3,1)(5,3,0)(3,3,1)(4,3,1)(5,1,0)(4,3,0)(5,4,1)(6,4,1)(7,4,0)(5,4,1)(6,4,1)(7,3,0)(6,4,0)(7,5,1)(8,5,1)(9,4,0)(8,5,0)(9,6,1)(10,6,1)(11,3,0)` |
| `Ω_{Ω_Ω}+Ω_{Ω+2}` | `(10,3,0)` `++ (4,3,0)(5,4,1)(6,4,1)(7,4,0)(5,4,1)(6,4,1)(7,2,0)(6,4,0)(7,5,1)(8,5,1)(9,4,0)(8,5,0)(9,6,1)(10,6,1)(11,4,0)` |
| `Ω_{Ω_Ω}+Ω_{Ω·2}` | `(10,3,0)(4,3,1)(5,3,1)(6,1,0)` |
| `Ω_{Ω_Ω}+Ω_{Ω_2+1}` | `(10,3,0)(4,3,1)(5,3,1)(6,2,0)` `++` (the kept copy of Fix N, ending `(5,4,1)(6,4,1)(7,2,0)`) `++ (6,4,0)(7,5,1)(8,5,1)(9,4,0)` |
| `Ω_{Ω_Ω}+Ω_{Ω_3}` | `(10,3,0)(4,3,1)(5,3,1)(6,2,0)` `++` (the lifted copy, ending `(5,4,1)(6,4,1)(7,3,0)`) |
| `Ω_Ω+Ω_3` | `M(Ω_Ω+Ω_2) ++ (2,2,0)(3,3,1)(4,3,1)(5,3,0)(3,3,1)(4,3,1)(5,1,0)(4,3,0)(5,4,1)(6,4,1)(7,3,0)(6,4,0)(7,5,1)(8,5,1)(9,3,0)` |

All six are standard (yaBMS `bms -s`), and
`Ω_2 < Ω_3 < Ω_4 < Ω_ω < Ω_Ω < Ω_{Ω+1} < Ω_{Ω+2} < Ω_{Ω+3} < Ω_{Ω+ω} < Ω_{Ω·2} < Ω_{Ω_2} < Ω_{Ω_2}+1 < Ω_{Ω_2}·2 < Ω_{Ω_2+1} < Ω_{Ω_2+2} < Ω_{Ω_2+ω} < Ω_{Ω_3} < Ω_{Ω_4} < Ω_{Ω_ω} < Ω_{Ω_Ω}·2`
(after `Ω_{Ω_Ω}+`) holds for the matrices too.

## Why these matrices

* **L is BMS's own.** For a limit `λ = γ + Ω_{c+ω}`, `M(λ)[n] = M(γ + Ω_{c+n+1})` with
  Fix L's matrices, for `n = 0…3` or `0…2`, in 16 contexts: `c = 1, Ω, Ω_Ω`, chains
  (`Ω_{Ω_ω}`, `Ω_{Ω_{Ω_ω}}`, `Ω_{Ω_{Ω+ω}}`), products (`Ω_{Ω_Ω}·Ω_ω`, `Ω_Ω·Ω_ω`,
  `Ω_{Ω_Ω}·Ω_{Ω_ω}`), after `Ω_{Ω_Ω}·2`, after a Fix N copy (`Ω_{Ω_Ω}+Ω_{Ω_2}+Ω_ω`,
  where `copyRoot` is needed), after `Ω_{Ω_Ω}+Ω_{Ω+1}`, and under `Ω_{Ω_{Ω_Ω}}`.
* **K and K' are confirmed together.** `M(γ+Ω_{Ω_2+ω})[n] = M(γ+Ω_{Ω_2+n+1})` for
  `n = 0, 1, 2` in 5 contexts: `[0]` is K, `[1]`, `[2]` are L on K. The mark `(5,4,1)`
  that `appendSuffix` writes is the only single column `(x, y, 1)` after K with this
  property (a search outside Lean). The leaf `N(r)+1` also gives `M(γ+Ω_{Ω_2+1})[1]` the
  shape of `M(γ+Ω_{Ω+1})[1]`: the successor of the cap `Ω_2` behaves as the successor of
  the top `Ω`.
* **D is supported, not derived.** `M(Ω_{Ω_Ω}+Ω_{Ω·2})` is `M(Ω_{Ω_Ω}+Ω_{Ω+1})` followed
  by `(4,3,1)(5,3,1)(6,1,0)`, the same tail that the sheet's row 4502 puts after
  `M(Ω_{Ω+1})` for `Ω_{Ω·2}`. Its `[0]` is `M(Ω_{Ω_Ω}+Ω_{Ω+ω²})`, and `[n]` goes on
  with a `(6,0,0)` column, a countable `ψ_0`: the shape of `M(Ω·2)[n]`, a supremum of
  `Ω + (countable)`. No `ω`-limit of the notation expands to it.

## Checks

| check | `TrioRulesAll.lean` | Fix L |
|---|---|---|
| every check of `TrioRulesAllSheet.lean` (932 `#guard`s) | holds | holds, same numbers |
| labels used there (sheet, families, probes, `probesEN`) changed | — | 0 |
| the six matrices standard | 0 of 6 correct (2 collisions, 4 not standard) | 6 |
| BMS expansions landing on the rules (21 limits) | — | all |
| last-leaf family, 151 labels: not standard | 43 | 0 |
| … disagreements (11,325 pairs); collisions | 555; 49 | 0; 0 |
| … disagreements with the 784 chosen matrices | 51 | 0 |

The family is `γ + Ω_p` and `Ω_{Ω_Ω}·Ω_p`, `Ω_{Ω_{Ω_Ω}}·Ω_p` for
`γ ∈ {Ω_{Ω_Ω}, Ω_{Ω_Ω}·2, Ω_{Ω_Ω}+Ω_{Ω_2}, Ω_{Ω_Ω}+Ω_{Ω+1}, Ω_{Ω_Ω}+Ω_2, Ω_Ω, Ω_Ω·2, Ω_Ω+Ω_2, Ω_{Ω_{Ω_Ω}}, Ω_{Ω_{Ω_Ω}}·2}`
and `p` around the fixed levels. Fix L changes 79 of the 151.

## Still open

1. **A leaf that is not last.** Fix L acts on the last leaf only. `+1` after the fixed
   levels (`Ω_{Ω_Ω}+Ω_3+1`, …, 69 labels) is unchanged: 340 disagreements, 26 collisions,
   21 not standard, as before. Fix N's step for a non-last leaf would have to use Fix L's
   leaf.
2. **K inside a chain.** `Ω_{Ω_{Ω_2+1}}` and `Ω_{Ω_{Ω_2+ω}}` after `Ω_{Ω_{Ω_Ω}}`: Fix L
   does not act, and the matrix of `TrioRulesAll.lean` lies above `Ω_{Ω_{Ω_3}}` and is not
   standard.
3. **Other levels of the same kind** are left alone: `Ω_{ω+1}`, `Ω_{Ω+ω+1}`, `Ω_{Ω+ω·2}`,
   `Ω_{Ω+ω^ω}`, `Ω_{Ω+ψ_0(Ω)}`, `Ω_{Ω·2+1}`, `Ω_{Ω·3}`, `Ω_{Ω²}`, `Ω_{Ω_2·2}` after
   `Ω_{Ω_Ω}` still get a wrong or non-standard matrix (the base rules write `(10,2,0)` or
   `(10,4,0)` for most of them). L, K, K', D are checked only where BMS or the sheet
   gives a reference.
4. **Other regimes** (`Ω_ω`, `Ω_2`, …): Fix L needs a tower over `1`, as Fix N does.
