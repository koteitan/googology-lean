[← Back](../README.md) | [English](README.md) | [Japanese](README-ja.md)

# Links to formal proofs

Formal proofs about googological notations, one row per repository.

- The status is as of 2026-09-26.
- ✅ means that the main theorem is proved with no `sorry` and no axiom of its own.
- Entries inside googology-lean link into this repository.

## Termination proofs

| notation | link | formalization | proof | method | complete |
|---|---|---|---|---|:-:|
| ω-Y (official) | [koteitan/wy-wo-por](https://github.com/koteitan/wy-wo-por) | koteitan (part of Phyrion's Lean layers moved in) | koteitan | patterns of resemblance (Σ₁ elementarity of countable ordinals), with Phyrion's combinatorial layer changed to one leg atom per node | ✅ |
| Weak Magma ω-Y | [Phyrion1343/omega-Y-Well-Ordering-Lean](https://github.com/Phyrion1343/omega-Y-Well-Ordering-Lean) | Phyrion | Phyrion | ordinal labels up to ω₁ and reflection of finite diagrams | ✅ |
| Weak Magma ω-Y | [koteitan/wmwy-wo-por](https://github.com/koteitan/wmwy-wo-por) | koteitan (the combinatorial layer is Phyrion's Lean, moved in) | koteitan | patterns of resemblance (Phyrion's combinatorial layer kept as it is) | ✅ |
| 1-Y | [Phyrion1343/1Y-Well-Ordering-Lean](https://github.com/Phyrion1343/1Y-Well-Ordering-Lean) | Phyrion | Phyrion | Σ₁ elementarity in the constructible universe L (adequate ordinals, Skolem hulls and condensation) | ✅ |
| 1-Y | [koteitan/1y-wo-por](https://github.com/koteitan/1y-wo-por) | koteitan (the combinatorial layer is Phyrion's Lean, moved in) | koteitan | patterns of resemblance (layered Σ₁ elementarity; Phyrion's combinatorial layer kept as it is) | ✅ |
| 0-Y | [Phyrion1343/0Y-Well-Ordering-Lean](https://github.com/Phyrion1343/0Y-Well-Ordering-Lean) | Phyrion (the well-ordering of BMS relies on EgoFakeFantasy's formalization) | Phyrion | an order isomorphism to BMS by encoding and decoding | ✅ |
| BMS | [koteitan/bms-elem-pattern](https://github.com/koteitan/bms-elem-pattern) | koteitan | koteitan | labels in Carlson's structures R_N (Σ₁, …, Σ_N elementary substructures) and finite reflection | ✅ |
| BMS | [koteitan/dh-bms-wf-formal](https://github.com/koteitan/dh-bms-wf-formal) | koteitan | DH | follows the paper's proof (stable labels and finite reflection) | ✅ |
| trio sequences | [koteitan/trio](https://github.com/koteitan/trio) | koteitan | koteitan | a syntactic proof | unfinished |
| pair sequences | [koteitan/pss-proof](https://github.com/koteitan/pss-proof) | koteitan | P進大好きbot (the bijectivity of the translation map: Naruyoko) | the translation Trans into Buchholz ψ terms | ✅ |
| pair sequences | [koteitan/yet-another-pss-proof](https://github.com/koteitan/yet-another-pss-proof) | koteitan | koteitan | a syntactic proof | ✅ |
| primitive sequences | [koteitan/prss-proof](https://github.com/koteitan/prss-proof) | koteitan | koteitan | a syntactic proof | ✅ |
| extended Buchholz's ψ | googology-lean [Notation/ExBuchholz](../Googology/Notation/ExBuchholz/README.md) | koteitan | koteitan | the value of a term (an ordinal) decreases on expansion; Buchholz's Lemmas 3.2–3.6 proved in the library | ✅ |

## Translation maps

In the column "complete", 🚧α means that the map is finished up to α and work beyond it is in progress. 🚧 without α means that some of the main theorems are not proved yet.

| notation | link | algorithm | formalization | proof | what is proved | method | complete |
|---|---|---|---|---|---|---|:-:|
| primitive sequences ⇒ extended Buchholz's ψ | googology-lean [Trans/BMS/ExBuchholz](../Googology/Trans/BMS/ExBuchholz/README.md) | koteitan | koteitan | koteitan | the reading of primitive sequences as standard terms below ψ₀(Ω): bijective, commutes with expansion, the value equals the rank of the expansion, cofinal | simulation (one step to one step), and the value equals the rank of the expansion | ✅ |
| pair sequences ⇒ extended Buchholz's ψ | googology-lean [Trans/BMS/ExBuchholz/PSS](../Googology/Trans/BMS/ExBuchholz/PSS/README.md) | P進大好きbot (Trans) | koteitan | koteitan (the bijectivity of Trans: Naruyoko) | a bijection onto the standard forms below ψ₀(Ω_ω), the value equals the rank of the expansion, cofinal; it does not send one step to one step (refuted) | the translation into the ordinals, and the value equals the rank of the expansion | ✅ |
| extended Buchholz's ψ ⇒ trio sequences | googology-lean [Trans/ExBuchholz/BMS](../Googology/Trans/ExBuchholz/BMS/README.md) | koteitan | koteitan | koteitan | the rules of the trio matrix of ψ₀(Ω_α) (α < ε₀), standard forms and order below ψ₀(Ω₂), injectivity | machine checks of the rule map, and comparison with the BM4-Analysis sheet | 🚧ψ₀(Ω₂) |
| extended Buchholz's ψ ⇒ trio sequences | [koteitan/trio ebp2bms](https://github.com/koteitan/trio/tree/main/ebp2bms) | koteitan | none | up to ψ₀(Ω_ω): koteitan (the formal proofs for pair sequences); beyond it: none | a general formula and table of the standard trio sequences for ψ₀(Ω_α) (α < Λ) | up to ψ₀(Ω_ω) by the formal proofs for pair sequences; beyond it, numerical comparison with the BM4-Analysis sheet | 🚧ψ₀(Ω_ω) |
| extended Buchholz's ψ ⇒ 3-row DBMS | [koteitan/trio ebp2dbms](https://github.com/koteitan/trio/tree/main/ebp2dbms) | koteitan and MrredsharkFan | none | none | a table of the standard 3-row DBMS for ψ₀(Ω_α) | the general formula of extended Buchholz's ψ ⇒ trio sequences composed with MrredsharkFan's bmsToDbms, compared numerically with that conversion | 🚧ψ₀(Ω_ω) |
| BMS ⇒ BMS | googology-lean [Trans/BMS/BMS](../Googology/Trans/BMS/BMS/README.md) | koteitan | koteitan | koteitan | primitive sequences ⇒ pair sequences, and r rows ⇒ r + 1 rows (a row of zeros underneath): commute with expansion, injective, keep the rank, cofinal; not onto (refuted) | simulation | ✅ |
| DBMS ⇒ BMS | googology-lean [Trans/DBMS/BMS](../Googology/Trans/DBMS/BMS/README.md) | koteitan | koteitan | koteitan | one-row DBMS ⇒ primitive sequences is bijective; r-row DBMS ⇒ r-row BMS (all arrays) commutes with expansion, is injective, keeps the rank and is cofinal; whether the latter is onto is open | simulation | 🚧 |
| DBMS ⇒ DBMS | googology-lean [Trans/DBMS/DBMS](../Googology/Trans/DBMS/DBMS/README.md) | koteitan | koteitan | koteitan | r rows ⇒ r + 1 rows (a row of zeros underneath): commutes with expansion, injective, keeps the rank, cofinal; not onto (refuted) | simulation | ✅ |
| DBMS ⇒ extended Buchholz's ψ | googology-lean [Trans/DBMS/ExBuchholz](../Googology/Trans/DBMS/ExBuchholz/README.md) | koteitan | koteitan | koteitan | the translations of one-row and two-row DBMS into the ordinals: the value equals the rank of the expansion, cofinal, order-preserving | the translation into the ordinals, and the value equals the rank of the expansion | 🚧ψ₀(Ω_ω) |
| BMS ⇒ Rathjen's ψ | [koteitan/bms-rathjen](https://github.com/koteitan/bms-rathjen) | koteitan | koteitan | koteitan | a table of BMS against Rathjen's ordinal collapsing function | machine-checked certificates, row by row | 🚧ε_ω+1 |
| UNOCF ⇒ Taranovsky's C | [koteitan/bms-vs-taranovskys-c](https://github.com/koteitan/bms-vs-taranovskys-c) | koteitan (two rows go through Buchholz's notation by P進大好きbot's map) | koteitan (definitions and comparison tests only) | none | a translation map from UNOCF terms to Taranovsky's notation C, and its table | UNOCF terms mapped to C terms (Lean and JavaScript) | 🚧ψ₀(Ω_ω) |

## Other

| notation | link | author | what is proved | method | complete |
|---|---|---|---|---|:-:|
| 1-Y | [koteitan/1y-expand-equiv](https://github.com/koteitan/1y-expand-equiv) | koteitan | the three definitions of the 1-Y expansion (Yukito's `script.js`, Phyrion's, the wiki's) are the same function | each definition transcribed, then proved equal as functions | ✅ |
