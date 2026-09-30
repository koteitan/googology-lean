[← Back](../../README.md) | [English](README.md) | [Japanese](README-ja.md)

# Trans

Concrete translations. This is the only layer that imports two systems at
once.

## Rule

```
Trans/<from>/<to>/     translations between the systems <from> and <to>
Trans/<from>/common/   facts about <from> alone that two or more <to> use
Trans/common/          facts shared by several <from> (none yet)
```

- `<from>` is the system being analysed and `<to>` the system it is measured
  against: `BMS/ExBuchholz/`, `BMS/PoR/`, `DBMS/BMS/`, `DBMS/ExBuchholz/`.
- A pair has **one** directory, not one per direction. Both simulations and
  the `Equiv`, if there is one, live together; otherwise the `Equiv` has no
  clear home and the two directions drift apart.
- A file about `<from>` alone goes to `<from>/common/` if two or more `<to>`
  use it, and otherwise into the one `<to>` that uses it.
- A directory that grows splits by the number of rows (`PSS/` for two rows,
  `Trio/` for three).
- Every `<from>/<to>/` and `<from>/common/` has a README that lists its files
  and what each proves. The table below links them.

Every system lives in [Notation](../Notation/README.md), so a translation from
a googological system into a proof-theoretic one is no different from any other
pair.

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

Each directory has a README listing its files and what each proves.

| directory | what it proves |
|---|---|
| [BMS/common/](BMS/common/README.md) | Facts about BMS alone that two or more translations use: expansion written on the entries at every number of rows, zero rows, cutting and appending, and the cofinality of three-row expansion (`TrioCof/`). |
| [BMS/ExBuchholz/](BMS/ExBuchholz/README.md) | BMS ↔ extended Buchholz ψ. The rank of a matrix as a ψ value: one row, ε-numbers, ζ, and pair sequences (rank = 1 + val, `PSS/`); and the rules that map ψ to trio sequences (`Trio/`). |
| [BMS/PoR/](BMS/PoR/README.md) | BMS → Carlson's patterns of resemblance. Two rows (`PSS/`): the map is order-preserving onto the core of R₁⁺ without 0, proved in Lean. Three rows (`Trio/`): the program `por/phi3def2.py` and the proofs on paper. |
| [DBMS/common/](DBMS/common/README.md) | Facts about DBMS alone that two or more translations use. |
| [DBMS/BMS/](DBMS/BMS/README.md) | DBMS ↔ BMS: one row, blocks and their standard lists, and the comparison of three-row DBMS with three-row BMS (the upper bound, `ThreeRowUpper*`). |
| [DBMS/ExBuchholz/](DBMS/ExBuchholz/README.md) | DBMS → extended Buchholz ψ: one and two rows, and the tables. |
