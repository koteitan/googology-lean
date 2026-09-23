[← Back](README.md) | [English](plan.md) | [Japanese](plan-ja.md)

# Plan

- Trans
  - trio sequences (BMS, 3 rows)
    - prove that the map of `Trio.lean` lands in the standard forms
    - prove that it is monotone
    - transcribe rules 1–10 of the trio algorithm (`ε₀ ≤ α < Λ`)
    - state and prove the relation to `[ ]` as cofinality
  - blank cells of the translation tables in the README
    - pair sequences → extended Buchholz's ψ: preserves expansion
- Notation
  - Y sequence: make termination a theorem here
    - 🤖 port [koteitan/1y-wo-por](https://github.com/koteitan/1y-wo-por) and [koteitan/1y-expand-equiv](https://github.com/koteitan/1y-expand-equiv) down to Lean 4.30.0, and connect them to `expand` here by `expand_eq`
  - ω-Y (official)
    - 🤖 prove well-foundedness with the official expansion (a separate repository, koteitan/wy-wo-por)
    - connect the proof here once it is done
  - DBMS
    - the translation into the ordinals for 2 rows and up
    - `r` rows inside `r + 1` rows
