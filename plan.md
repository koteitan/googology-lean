[← Back](README.md) | [English](plan.md) | [Japanese](plan-ja.md)

# Plan

- Trans
  - trio sequences (BMS, 3 rows) (branch `feature/trio-pair`)
    - 🤖 prove that the transcription of rules 1–10 (`TrioRules.lean`) agrees with `trioMatrix` below `ε₀`, and that fuel 200 is enough
    - 🤖 prove that for `ε₀ ≤ α < Λ` too the image lies in the standard forms and the map is order-preserving
    - 🤖 examine the 41 rows that disagree with the table
    - 🤖 restate cofinality on the side of extended Buchholz terms and `[ ]`, not trio's own term type `Three`
  - 🤖 pair sequences → extended Buchholz's ψ: find whether one step goes to finitely many steps of the fundamental sequence
- Notation
  - ω-Y (official)
    - prove well-foundedness with the official expansion (a separate repository, koteitan/wy-wo-por)
    - connect the proof here once it is done
  - DBMS
    - 🤖 the translation into the ordinals for 2 rows and up
    - 🤖 `r` rows inside `r + 1` rows
