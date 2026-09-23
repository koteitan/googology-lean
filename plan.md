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
    - re-prove Phyrion's 1-Y proof with patterns of resemblance in place of admissible ordinals (a separate repository)
      - 🤖 port the combinatorial part, rewriting the unlicensed BMS layer it depends on
      - connect the two and obtain the final theorems
    - bring the proof in here: move to Lean 4.33.1, or port it down to 4.30.0
  - ω-Y
    - decide the target: the official ω-Y (open), the weak ω-Y (proved by Phyrion), or their relation
  - DBMS
    - the translation into the ordinals for 2 rows and up
    - `r` rows inside `r + 1` rows
