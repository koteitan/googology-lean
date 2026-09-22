[← Back](../../../README.md) | [English](README.md) | [Japanese](README-ja.md)

# DBMS

DBMS expands exactly as BM4 does. What differs is where the expansion starts.

BM4's generators are the stairs `(0,…,0)(1,…,1)⋯(n,…,n)`. DBMS's are the
arrays whose column `i` holds `i - k` in row `k`, truncated at `0`:

```
(0,0,0)(1,0,0)(2,1,0)(3,2,1)⋯
```

## What is here

```lean
def dstair (r n : ℕ) : Arr r := ⟨n + 1, fun i k => i - k⟩

inductive DStd (r : ℕ) : Arr r → Prop
  | init (n : ℕ) : DStd r (dstair r n)
  | step {A : Arr r} (N : ℕ) : DStd r A → DStd r (expand A N)

noncomputable def dbms (r : ℕ) : Rewrite where
  State  := DStdElt r                 -- arrays reachable from a DBMS generator
  step   := fun A k => expand A k     -- the same rule as BM4
  halted := fun A => A.len = 0
```

The two notions of standard form really are different. `(0,0)(1,1)` is a BM4
standard form and not a DBMS one; `(0,0)(1,0)(2,1)` is the other way round.
With one row they agree, because `i - 0 = i`.

## Status

| | |
|---|---|
| the expansion system | done |
| the generators | done (`dbmsStd`) |
| termination, any number of rows | done (`dbms_terminates`) |
| one row: an ordinal, and termination | done, in [`Trans/DBMS/`](../../Trans/README.md) |
| one row: which matrices are standard | done (`dstd_entries_iff`) |
| the expansion on the entries, at any number of rows | done (`Trans.DBMS.dbmsL`) |

Termination does not depend on the generators at all.
`Notation.BMS.terminates_any` says expansion ends from **any** array, standard
or not: the label whose height descends is the `Λ`-chain, which never looks at
the array. So `dbms_terminates` holds for every number of rows, and `dbms_wf`
and `dbmsEval` follow.

One row also terminates by translation — `Trans.DBMS.dbms_one_terminates` —
and `Trans.DBMS.dbmsOrdEval` gives the ordinal each one-row matrix names, the
same ordinals as one-row BMS since the two systems agree there.
