[← Back](README.md) | [English](plan.md) | [Japanese](plan-ja.md)

# Plan

- Trans
  - pair sequences (BMS, 2 rows): the translation into the ordinals, through the `Trans` of [koteitan/pss-proof](https://github.com/koteitan/pss-proof)
    - add pss-proof as a Lake dependency
    - prove that its expansion `oper M (N+1)` is `expand2L N M` on the standard pair sequences, except at length 1
    - map its Buchholz terms to extended Buchholz terms, and prove that the order and the standard forms correspond
    - prove rank(M) = order type below M = `val (Trans M)`, through `belowEquiv`
  - trio sequences (BMS, 3 rows)
    - prove that the map of `Trio.lean` lands in the standard forms
    - prove that it is monotone
    - transcribe rules 1–10 of the trio algorithm (`ε₀ ≤ α < Λ`)
    - state and prove the relation to `[ ]` as cofinality
  - extended Buchholz's ψ
    - prove that the rank of `exbOT` equals `val`, through the cofinality of `[ ]` on the terms
  - blank cells of the translation tables in the README
    - one-row DBMS → ordinals: injective
    - primitive sequences → ordinals: order-preserving
    - primitive sequences → extended Buchholz's ψ, one-row DBMS → primitive sequences: rank-preserving
    - one-row DBMS → primitive sequences, primitive sequences → pair sequences: injective
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
