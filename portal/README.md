[← Back](../README.md) | [English](README.md) | [Japanese](README-ja.md)

# Links to formal proofs

Formal proofs about googological notations by koteitan and Phyrion, one entry per repository, arranged by notation.

- The status is as of 2026-09-26. "Complete" means that the main theorem is proved with no `sorry` and no axiom of its own.
- Entries inside googology-lean link into this repository.

## Y sequence

- ω-Y (official)
  - [koteitan/wy-wo-por](https://github.com/koteitan/wy-wo-por) — well-foundedness of the official ω-Y, the expansion of Naruyoko's program [Study and Expand Sequence](https://naruyoko.github.io/StudyAndExpandSequence/), by patterns of resemblance. Lean 4, complete.
- Weak Magma ω-Y
  - [Phyrion1343/omega-Y-Well-Ordering-Lean](https://github.com/Phyrion1343/omega-Y-Well-Ordering-Lean) — well-foundedness of the weak-magma, no-extraction ω-Y expansion, and well-ordering of its standard forms. Lean 4, complete.
  - [koteitan/wmwy-wo-por](https://github.com/koteitan/wmwy-wo-por) — the same well-foundedness, re-proved by patterns of resemblance. Lean 4, complete.
- 1-Y
  - [Phyrion1343/1Y-Well-Ordering-Lean](https://github.com/Phyrion1343/1Y-Well-Ordering-Lean) — well-foundedness of the 1-Y expansion and well-ordering of its standard forms, by the constructible universe L and admissible ordinals. Lean 4, complete.
  - [koteitan/1y-wo-por](https://github.com/koteitan/1y-wo-por) — the same well-foundedness, re-proved by patterns of resemblance. Lean 4, complete.
  - [koteitan/1y-expand-equiv](https://github.com/koteitan/1y-expand-equiv) — the three definitions of the 1-Y expansion (Yukito's `script.js`, Phyrion's, the wiki's) are the same function. Lean 4, complete.
  - googology-lean [Notation/Y](../Googology/Notation/Y/README.md) — the two above, ported, giving well-foundedness for Yukito's definition. Lean 4, complete.
- 0-Y
  - [Phyrion1343/0Y-Well-Ordering-Lean](https://github.com/Phyrion1343/0Y-Well-Ordering-Lean) — the order isomorphism between 0-Y and BMS, and well-ordering and termination of 0-Y. Lean 4, complete. The same content is also in 1Y-Well-Ordering-Lean.

## BMS (Bashicu matrix system)

- Any number of rows (BM4)
  - [koteitan/bms-elem-pattern](https://github.com/koteitan/bms-elem-pattern) — termination of BM4 by Carlson's structures R_N (Σ₁, …, Σ_N elementary substructures), first for pair sequences (R₂), then trio sequences (R₃), then any number of rows (R_N). Lean 4, complete.
  - [koteitan/dh-bms-wf-formal](https://github.com/koteitan/dh-bms-wf-formal) — formalization of DH's paper "Bashicu Matrix System ver. 4 の停止性と展開関係の整礎性". Lean 4, complete.
  - googology-lean [Notation/BMS](../Googology/Notation/BMS/README.md) — well-foundedness of BMS, on the standard forms and on all matrices. Lean 4, complete.
  - [koteitan/bms-paper-formalization](https://github.com/koteitan/bms-paper-formalization) — formalization of R. Hunter, "Well-Orderedness of the Bashicu Matrix System". Isabelle/HOL and Isabelle/ZF, in progress (Lemma 2.6 is an axiom for now).
- Trio sequences (3 rows)
  - [koteitan/trio](https://github.com/koteitan/trio) — a syntactic proof of termination of trio sequences. Lean 4, unfinished.
- Pair sequences (2 rows)
  - [koteitan/pss-proof](https://github.com/koteitan/pss-proof) — formalization of P進大好きbot's "ペア数列の停止性" and of Naruyoko's "変換写像の全単射性". Isabelle/HOL and Lean 4, complete.
  - [koteitan/yet-another-pss-proof](https://github.com/koteitan/yet-another-pss-proof) — a different proof of termination that uses no ordinals. Lean 4 and Isabelle/HOL, complete.
- Primitive sequences (1 row)
  - [koteitan/prss-proof](https://github.com/koteitan/prss-proof) — termination of the primitive sequence system, by a map into the ordinals below ε₀. Isabelle/HOL, complete.

## DBMS

- googology-lean [Notation/DBMS](../Googology/Notation/DBMS/README.md) — well-foundedness of DBMS, on the standard forms and on all matrices. Lean 4, complete.

## Extended Buchholz's ψ

- googology-lean [Notation/ExBuchholz](../Googology/Notation/ExBuchholz/README.md) — well-ordering as a notation system, and termination of its expansion. Lean 4, complete.

## Translations between notations

- googology-lean [Trans](../Googology/Trans/README.md) — translations between BMS and DBMS with one or two rows and extended Buchholz's ψ, and into the ordinals. Lean 4, partly complete (three rows and up in progress).
- [koteitan/bms-rathjen](https://github.com/koteitan/bms-rathjen) — a table of BMS against Rathjen's ordinal collapsing function, each row machine-checked. Lean 4, in progress.
- [koteitan/bms-vs-taranovskys-c](https://github.com/koteitan/bms-vs-taranovskys-c) — a translation function from BMS to Taranovsky's notation C, and its table. Lean 4 and JavaScript, in progress (three rows and up not yet implemented).
