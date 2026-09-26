[← Back](../README.md) | [English](README.md) | [Japanese](README-ja.md)

# Links to formal proofs

Formal proofs about googological notations by koteitan and Phyrion, one row per repository.

- The status is as of 2026-09-26.
- ✅ means that the main theorem is proved with no `sorry` and no axiom of its own.
- Entries inside googology-lean link into this repository.

| notation | link | author | what is proved | method | complete |
|---|---|---|---|---|:-:|
| ω-Y (official) | [koteitan/wy-wo-por](https://github.com/koteitan/wy-wo-por) | koteitan | well-foundedness of the official ω-Y, the expansion of Naruyoko's program [Study and Expand Sequence](https://naruyoko.github.io/StudyAndExpandSequence/) | patterns of resemblance (Σ₁ elementarity of countable ordinals), with Phyrion's combinatorial layer changed to one leg atom per node | ✅ |
| Weak Magma ω-Y | [Phyrion1343/omega-Y-Well-Ordering-Lean](https://github.com/Phyrion1343/omega-Y-Well-Ordering-Lean) | Phyrion | well-foundedness of the weak-magma, no-extraction ω-Y expansion; well-ordering of its standard forms | ordinal labels up to ω₁ and reflection of finite diagrams | ✅ |
| Weak Magma ω-Y | [koteitan/wmwy-wo-por](https://github.com/koteitan/wmwy-wo-por) | koteitan | the same well-foundedness | patterns of resemblance (Phyrion's combinatorial layer kept as it is) | ✅ |
| 1-Y | [Phyrion1343/1Y-Well-Ordering-Lean](https://github.com/Phyrion1343/1Y-Well-Ordering-Lean) | Phyrion | well-foundedness of the 1-Y expansion; well-ordering of its standard forms | Σ₁ elementarity in the constructible universe L (adequate ordinals, Skolem hulls and condensation) | ✅ |
| 1-Y | [koteitan/1y-wo-por](https://github.com/koteitan/1y-wo-por) | koteitan | the same well-foundedness | patterns of resemblance (layered Σ₁ elementarity; Phyrion's combinatorial layer kept as it is) | ✅ |
| 1-Y | [koteitan/1y-expand-equiv](https://github.com/koteitan/1y-expand-equiv) | koteitan | the three definitions of the 1-Y expansion (Yukito's `script.js`, Phyrion's, the wiki's) are the same function | each definition transcribed, then proved equal as functions | ✅ |
| 1-Y | googology-lean [Notation/Y](../Googology/Notation/Y/README.md) | koteitan | well-foundedness for Yukito's definition, on the standard forms and on all legal sequences | port of 1y-wo-por and 1y-expand-equiv | ✅ |
| 0-Y | [Phyrion1343/0Y-Well-Ordering-Lean](https://github.com/Phyrion1343/0Y-Well-Ordering-Lean) | Phyrion | the order isomorphism between 0-Y and BMS; well-ordering and termination of 0-Y (also contained in 1Y-Well-Ordering-Lean) | an order isomorphism to BMS by encoding and decoding | ✅ |
| BMS (any number of rows) | [koteitan/bms-elem-pattern](https://github.com/koteitan/bms-elem-pattern) | koteitan | termination of BM4, first for pair sequences, then trio sequences, then any number of rows | labels in Carlson's structures R_N (Σ₁, …, Σ_N elementary substructures) and finite reflection | ✅ |
| BMS (any number of rows) | [koteitan/dh-bms-wf-formal](https://github.com/koteitan/dh-bms-wf-formal) | koteitan | formalization of DH's paper "Bashicu Matrix System ver. 4 の停止性と展開関係の整礎性" | follows the paper's proof (stable labels and finite reflection) | ✅ |
| BMS (any number of rows) | googology-lean [Notation/BMS](../Googology/Notation/BMS/README.md) | koteitan | well-foundedness of BMS, on the standard forms and on all matrices | uses the theorem of bms-elem-pattern as a dependency | ✅ |
| BMS (any number of rows) | [koteitan/bms-paper-formalization](https://github.com/koteitan/bms-paper-formalization) | koteitan | formalization of R. Hunter, "Well-Orderedness of the Bashicu Matrix System" (Isabelle) | stability reflection in L_α | in progress (Lemma 2.6 is an axiom for now) |
| trio sequences | [koteitan/trio](https://github.com/koteitan/trio) | koteitan | termination of trio sequences | a syntactic proof | unfinished |
| pair sequences | [koteitan/pss-proof](https://github.com/koteitan/pss-proof) | koteitan | formalization of P進大好きbot's "ペア数列の停止性" and Naruyoko's "変換写像の全単射性" (Isabelle and Lean) | the translation Trans into Buchholz ψ terms | ✅ |
| pair sequences | [koteitan/yet-another-pss-proof](https://github.com/koteitan/yet-another-pss-proof) | koteitan | termination of pair sequences (Lean and Isabelle) | a translation into an own three-branch tree notation p_a(b)+c; no ordinals | ✅ |
| primitive sequences | [koteitan/prss-proof](https://github.com/koteitan/prss-proof) | koteitan | termination of the primitive sequence system (Isabelle) | a map into the ordinals below ε₀ (multiset and Cantor normal form versions) | ✅ |
| DBMS | googology-lean [Notation/DBMS](../Googology/Notation/DBMS/README.md) | koteitan | well-foundedness of DBMS, on the standard forms and on all matrices | the expansion rule is BM4's, so termination of BMS is used | ✅ |
| extended Buchholz's ψ | googology-lean [Notation/ExBuchholz](../Googology/Notation/ExBuchholz/README.md) | koteitan | well-ordering as a notation system, and termination of the expansion | the value of a term (an ordinal) decreases on expansion; Buchholz's Lemmas 3.2–3.6 proved in the library | ✅ |
| translations (BMS, DBMS, extended Buchholz's ψ) | googology-lean [Trans](../Googology/Trans/README.md) | koteitan | translations between BMS and DBMS with one or two rows and extended Buchholz's ψ, and into the ordinals | simulation (one step to one step), and the value equals the rank of the expansion | partly (three rows and up in progress) |
| translation (BMS and Rathjen's ψ) | [koteitan/bms-rathjen](https://github.com/koteitan/bms-rathjen) | koteitan | a table of BMS against Rathjen's ordinal collapsing function | machine-checked certificates, row by row | in progress |
| translation (BMS and Taranovsky's C) | [koteitan/bms-vs-taranovskys-c](https://github.com/koteitan/bms-vs-taranovskys-c) | koteitan | a translation function from BMS to Taranovsky's notation C, and its table | direct translation from the matrix (Lean and JavaScript) | in progress (three rows and up not yet implemented) |
