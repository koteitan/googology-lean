[← Back](../../README.md) | [English](README.md) | [Japanese](README-ja.md)

# Trans

Concrete translations. This is the only layer that imports two systems at
once.

## Rule

```
Trans/<A>/<B>/      the translation A → B
Trans/<A>/common/   facts about A alone that two or more translations use
Trans/common/       facts shared by several systems (none yet)
```

- One directory per direction. `Trans/<A>/<B>/` is the cell "A → B" of the
  tables in the [top README](../../README.md), and the goals of that cell
  (injective, order-preserving, …) are proved there. `B → A` goes to
  `Trans/<B>/<A>/`: `BMS/ExBuchholz/` reads a matrix as an ordinal, and
  `ExBuchholz/BMS/` builds the trio matrix of an ordinal.
- A translation inside one family of systems (primitive sequences → pair
  sequences, `r` rows → `r + 1` rows) goes to `Trans/<A>/<A>/`.
- What both directions need, such as a round trip, goes with the direction
  that defines it first; the other direction imports it.
- A file about `A` alone goes to `Trans/<A>/common/` if two or more
  translations use it, and otherwise into the one directory that uses it.
- A directory that grows splits by the number of rows (`PSS/` for two rows,
  `Trio/` for three).
- Every directory has a README that lists its files and what each proves.
  The table below links them.

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
| [BMS/common/](BMS/common/README.md) | Facts about BMS alone that two or more translations use: expansion written on the entries at every number of rows, cutting and appending, and the cofinality of three-row expansion (`TrioCof/`). |
| [BMS/BMS/](BMS/BMS/README.md) | BMS → BMS: the primitive sequences inside the pair sequences, and `r` rows inside `r + 1` rows (a row of zeros underneath). |
| [BMS/ExBuchholz/](BMS/ExBuchholz/README.md) | BMS → extended Buchholz ψ: which ordinal a matrix names. One row (below ε₀, ε-numbers, ζ₀, rank = value), and pair sequences (rank = 1 + val, `PSS/`). |
| [BMS/PoR/](BMS/PoR/README.md) | BMS → Carlson's patterns of resemblance. Two rows (`PSS/`): the map is order-preserving onto the core of R₁⁺ without 0, proved in Lean. Three rows (`Trio/`): the program `por/phi3def2.py` and the proofs on paper. |
| [PoR/InaccPsi/](PoR/InaccPsi/README.md) | Patterns of resemblance → InaccPsi terms, for Wilken's claim that the countable part of the notation system over ω weakly inaccessibles covers the core of R₂⁺: the precise statement, the countable values form an initial segment (Lean), every ordinal below υ_{ω·ω} is in the core of Carlson's R₂ (paper, refereed), the route as a tree of lemmas, and the experiments. |
| [ExBuchholz/BMS/](ExBuchholz/BMS/README.md) | Extended Buchholz ψ → BMS: the trio matrix of `ψ_0(Ω_α)` (`Trio/`): rules 1–10 and their fixes, standard forms and order below `ψ_0(Ω_2)`, and the checks against the sheet. |
| [DBMS/common/](DBMS/common/README.md) | Facts about DBMS alone that two or more translations use. |
| [DBMS/DBMS/](DBMS/DBMS/README.md) | DBMS → DBMS: `r + 1` rows inside `r + 2` rows. |
| [DBMS/BMS/](DBMS/BMS/README.md) | DBMS → BMS: one row on the entries, blocks and their standard lists, and the comparison of three-row DBMS with three-row BMS (`ThreeRow*`). |
| [DBMS/ExBuchholz/](DBMS/ExBuchholz/README.md) | DBMS → extended Buchholz ψ: one and two rows into the ordinals, and the table cells of one-row DBMS. |
