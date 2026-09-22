[← Back](../../README.md) | [English](README.md) | [Japanese](README-ja.md)

# Trans

Concrete translations. This is the only layer that imports two systems at
once.

## Rule

An unordered pair `{X, Y}` gets **one** file, placed under the alphabetically
earlier name:

```
Trans/BMS/DBMS.lean     everything about BMS and DBMS
Trans/BMS/Y.lean        everything about BMS and Y
```

One file per pair, not one per direction. Both simulations and the `Equiv`, if
there is one, live together; otherwise the `Equiv` has no clear home and the
two directions drift apart. The index below makes a pair findable from either
side.

Every system lives in [Notation](../Notation/README.md), so a translation from
a googological system into a proof-theoretic one is no different from any other
pair: `Trans/BMS/OTB.lean`, under the alphabetically earlier name.

## What to build

Pick the weakest structure that does the job.

| structure | ask for | get |
|---|---|---|
| `Sim` | one step maps to one step | well-foundedness and termination transfer |
| `StepHom` | commutes with expansion, plus halting | becomes a `Sim` |
| `Equiv` | mutually inverse `Sim`s | both sides equivalent |
| `OrdHom` | order-preserving only | well-foundedness transfers |

`StepHom` carries a `reindex : Nat → Nat` for renumbering brackets. Pass `id`
when the numbering is unchanged.

## Calibration is not a theorem

Agreement with a reference implementation is a finite check (`#guard`,
`decide`), not a proof about all inputs. Keep it in its own file and do not
let it be read as one of the theorems above.

## Index

| pair | file | structure | status |
|---|---|---|---|
| BMS with itself | `BMS/OneRow.lean` | — | that one-row expansion is the primitive sequence rule: keep the first `p` entries, repeat the next `s` of them `N + 1` times |
| BMS with itself | `BMS/Rows.lean` | — | that naming a parent pins the bad root down, whatever the number of rows |
| BMS with itself | `BMS/Entries.lean` | — | that an array and its entries expand the same way |
| BMS with itself | `BMS/TwoRow.lean` | — | two-row expansion: `m₀` is `0` or `1`, and at `1` row `0` takes an increment |
| BMS with itself | `BMS/Cut.lean` | — | that the block recursion `expandL` is the textbook rule: drop the last column, repeat the bad part `N + 1` times |
| BMS, extended Buchholz's ψ | `BMS/Calibrate.lean` | — | that below `ψ_0(Ω)` is exactly where the subscripts are all `0`, so the reading reaches every standard form there |
| BMS, extended Buchholz's ψ | `BMS/Prim.lean` | `StepHom` | the primitive sequence system as a `Rewrite`, that it terminates, and its ordinal |
| BMS, extended Buchholz's ψ | `BMS/Cofinal.lean` | — | that `[ ]` converges below `ψ_0(Ω)`: anything under a term is under one of its members |
| BMS, extended Buchholz's ψ | `BMS/Bms.lean` | `StepHom` | **the ordinal a one-row Bashicu matrix names**, that it is below `ψ_0(Ω)`, and that one row terminates by translation |
| BMS, extended Buchholz's ψ | `BMS/Reach.lean` | — | **the standard one-row matrices are exactly the matrices whose term is standard** |
| DBMS, extended Buchholz's ψ | `DBMS/OneRow.lean` | `StepHom` | the same for one-row DBMS, whose generators agree with BM4's there, including which matrices are standard |
| BMS, extended Buchholz's ψ | `BMS/Commute.lean` | `StepHom`, eventually | that the reading turns expansion into `[ ]`, up to the reindexing `N ↦ N + 1` |
| BMS, extended Buchholz's ψ | `BMS/ExBuchholz.lean` | `Sim`, eventually | the reading `read` for one row, that its terms are standard exactly when they descend, and that it is a bijection onto them |
