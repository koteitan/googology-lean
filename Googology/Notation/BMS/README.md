[← Back](../../../README.md) | [English](README.md) | [Japanese](README-ja.md)

# BMS

Bashicu matrices with any number of rows, presented as an expansion system.

`r = 1` is the primitive sequence, `r = 2` the pair sequence, `r = 3` the trio
sequence, and so on.

## What is here

```lean
noncomputable def bms (r : ℕ) : Rewrite where
  State  := Pat.StdElt r              -- standard arrays with r rows
  step   := fun A k => expand A k     -- one bracket expansion
  halted := fun A => A.len = 0
```

Standardness is carried by the state type, so `Rewrite.Std` has nothing left
to say beyond naming the generators `(0,…,0)(1,…,1)⋯(n,…,n)`.

| theorem | statement |
|---|---|
| `bms_Rel_iff` | the one-step relation is the relation the termination proof is about |
| `bms_wf` | one-step expansion is well founded |
| `bms_terminates` | **BMS terminates, for every `r`** |
| `primitive_terminates`, `pair_terminates`, `trio_terminates` | `r = 1, 2, 3` |

## Where the work happens

Nothing about termination is proved here. The proof — labels in `R_r` and
Σ-elementary substructures, for every number of rows — is
[koteitan/bms-elem-pattern](https://github.com/koteitan/bms-elem-pattern),
which this package requires. This file supplies the three fields of `Rewrite`
and one `Subrelation.wf`, and `Googology.Core` supplies the rest.

The fit is exact: `Pat.StdR` there is `Rewrite.Rel` here, written out by hand.

```
StdR r A B      = 0 < B.len ∧ ∃ n, A = expand B n
(bms r).Rel A B = ¬ halted B ∧ ∃ k, A = step B k
```

That is the point of the library. A system that already has a termination
proof needs a few lines to join; a system that does not gets the standard
routes — a measure, a translation, an evaluation — for free.

## Status

| | |
|---|---|
| the expansion system, well-foundedness, termination | done |
| the same on every array, standard or not | done (`bmsAll`, `terminates_any`) |
| the generators | done (`bmsStd`) |
| an evaluation into the ordinals | done (`bmsEval`), as the rank of one-step expansion |
| a translation to `ExBuchholz` | done for `r = 1`, in [`Trans/BMS/`](../../Trans/README.md); `r ≥ 2` open |
