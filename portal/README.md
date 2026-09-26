[← Back](../README.md) | [English](README.md) | [Japanese](README-ja.md)

# Links to formal proofs

Formal proofs about googological notations by koteitan and Phyrion, one row per repository.

- The status is as of 2026-09-26.
- ✅ means that the main theorem is proved with no `sorry` and no axiom of its own.
- Entries inside googology-lean link into this repository.

## Termination proofs

| notation | link | author | method | complete |
|---|---|---|---|:-:|
| ω-Y (official) | [koteitan/wy-wo-por](https://github.com/koteitan/wy-wo-por) | koteitan | patterns of resemblance (Σ₁ elementarity of countable ordinals), with Phyrion's combinatorial layer changed to one leg atom per node | ✅ |
| Weak Magma ω-Y | [Phyrion1343/omega-Y-Well-Ordering-Lean](https://github.com/Phyrion1343/omega-Y-Well-Ordering-Lean) | Phyrion | ordinal labels up to ω₁ and reflection of finite diagrams | ✅ |
| Weak Magma ω-Y | [koteitan/wmwy-wo-por](https://github.com/koteitan/wmwy-wo-por) | koteitan | patterns of resemblance (Phyrion's combinatorial layer kept as it is) | ✅ |
| 1-Y | [Phyrion1343/1Y-Well-Ordering-Lean](https://github.com/Phyrion1343/1Y-Well-Ordering-Lean) | Phyrion | Σ₁ elementarity in the constructible universe L (adequate ordinals, Skolem hulls and condensation) | ✅ |
| 1-Y | [koteitan/1y-wo-por](https://github.com/koteitan/1y-wo-por) | koteitan | patterns of resemblance (layered Σ₁ elementarity; Phyrion's combinatorial layer kept as it is) | ✅ |
| 0-Y | [Phyrion1343/0Y-Well-Ordering-Lean](https://github.com/Phyrion1343/0Y-Well-Ordering-Lean) | Phyrion | an order isomorphism to BMS by encoding and decoding | ✅ |
| BMS | [koteitan/bms-elem-pattern](https://github.com/koteitan/bms-elem-pattern) | koteitan | labels in Carlson's structures R_N (Σ₁, …, Σ_N elementary substructures) and finite reflection | ✅ |
| BMS | [koteitan/dh-bms-wf-formal](https://github.com/koteitan/dh-bms-wf-formal) | koteitan | follows the paper's proof (stable labels and finite reflection) | ✅ |
| trio sequences | [koteitan/trio](https://github.com/koteitan/trio) | koteitan | a syntactic proof | unfinished |
| pair sequences | [koteitan/pss-proof](https://github.com/koteitan/pss-proof) | koteitan | the translation Trans into Buchholz ψ terms | ✅ |
| pair sequences | [koteitan/yet-another-pss-proof](https://github.com/koteitan/yet-another-pss-proof) | koteitan | a translation into an own three-branch tree notation p_a(b)+c; no ordinals | ✅ |
| primitive sequences | [koteitan/prss-proof](https://github.com/koteitan/prss-proof) | koteitan | a map into the ordinals below ε₀ (multiset and Cantor normal form versions) | ✅ |
| extended Buchholz's ψ | googology-lean [Notation/ExBuchholz](../Googology/Notation/ExBuchholz/README.md) | koteitan | the value of a term (an ordinal) decreases on expansion; Buchholz's Lemmas 3.2–3.6 proved in the library | ✅ |

## Translation maps

In the column "complete", 🚧α means that the map is finished up to α and work beyond it is in progress.

| notation | link | author | what is proved | method | complete |
|---|---|---|---|---|:-:|
| BMS, DBMS, extended Buchholz's ψ | googology-lean [Trans](../Googology/Trans/README.md) | koteitan | translations between BMS and DBMS with one or two rows and extended Buchholz's ψ, and into the ordinals | simulation (one step to one step), and the value equals the rank of the expansion | 🚧ψ₀(Ω_ω) |
| BMS and Rathjen's ψ | [koteitan/bms-rathjen](https://github.com/koteitan/bms-rathjen) | koteitan | a table of BMS against Rathjen's ordinal collapsing function | machine-checked certificates, row by row | 🚧ε_ω+1 |
| UNOCF and Taranovsky's C | [koteitan/bms-vs-taranovskys-c](https://github.com/koteitan/bms-vs-taranovskys-c) | koteitan | a translation map from UNOCF terms to Taranovsky's notation C, and its table | UNOCF terms mapped to C terms (Lean and JavaScript) | 🚧ψ₀(Ω_ω) |

## Other

Nothing here yet.
