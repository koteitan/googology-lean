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

One file per pair is the starting point, not a ceiling. A pair that grows —
`BMS` and extended Buchholz's ψ runs to several files — keeps its directory
and splits by what is being proved, and the index below lists each piece. A
file about one system alone, needed only because a translation uses it, goes
in the same directory and is listed as a pair with itself.

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
| BMS with itself | `BMS/Anc.lean` | — | the row-`0` ancestor relation read off the entries, computed and proved to match `BM4.anc` |
| BMS with itself | `BMS/EntriesR.lean` | — | **every Bashicu matrix expansion, written on the entries and shown to be `BM4.expand`** — so it runs, at any number of rows |
| BMS with itself | `BMS/Entries2.lean` | — | **two-row expansion written on the entries, that it is `BM4.expand`, and that a run of it ends** |
| BMS with itself | `BMS/Pair.lean` | — | the pair sequence system as a `Rewrite` whose step runs, with its generators |
| BMS with itself | `BMS/Cut.lean` | — | that the block recursion `expandL` is the textbook rule: drop the last column, repeat the bad part `N + 1` times |
| BMS, extended Buchholz's ψ | `BMS/Calibrate.lean` | — | that below `ψ_0(Ω)` is exactly where the subscripts are all `0`, so the reading reaches every standard form there |
| BMS, extended Buchholz's ψ | `BMS/Prim.lean` | `StepHom` | the primitive sequence system as a `Rewrite`, that it terminates, and its ordinal |
| BMS, extended Buchholz's ψ | `BMS/Cofinal.lean` | — | that below `ψ_0(Ω)` a term is the least upper bound of `X[0] < X[1] < ⋯` |
| BMS, extended Buchholz's ψ | `BMS/Bms.lean` | `StepHom` | **the ordinal a one-row Bashicu matrix names**, that it is below `ψ_0(Ω)`, and that one row terminates by translation |
| BMS, extended Buchholz's ψ | `BMS/Equiv.lean` | `Equiv` | **the primitive sequence system and the standard forms below `ψ_0(Ω)` are one system written two ways** |
| BMS, extended Buchholz's ψ | `BMS/Reach.lean` | — | **the standard one-row matrices are exactly the matrices whose term is standard** |
| DBMS, extended Buchholz's ψ | `DBMS/OneRow.lean` | `StepHom` | the same for one-row DBMS, whose generators agree with BM4's there, including which matrices are standard |
| BMS, extended Buchholz's ψ | `BMS/Commute.lean` | `StepHom`, eventually | that the reading turns expansion into `[ ]`, up to the reindexing `N ↦ N + 1` |
| BMS, extended Buchholz's ψ | `BMS/ExBuchholz.lean` | `Sim`, eventually | the reading `read` for one row, that its terms are standard exactly when they descend, and that it is a bijection onto them |
