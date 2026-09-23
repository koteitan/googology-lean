[← Back](README.md) | [English](plan.md) | [Japanese](plan-ja.md)

# Plan

- Trans
  - trio sequences (BMS, 3 rows) (fixes go on top of `TrioRulesAll`)
    - 🤖 fix leaves that are not last outside the tower regimes (`Ω_ω`, `Ω_2`, `Ω+1`) and at marked levels that are not last ([TRIO-NONLAST-LEAF.md](Googology/Trans/BMS/TRIO-NONLAST-LEAF.md))
    - after Fix L: fix the other levels of the same kind after `Ω_{Ω_Ω}` (`Ω_{ω+1}`, `Ω_{Ω+ω+1}`, `Ω_{Ω+ω·2}`, `Ω_{Ω·2+1}`, `Ω_{Ω·3}`, `Ω_{Ω^2}`, `Ω_{Ω_2·2}`, …) and case K inside a chain (`Ω_{Ω_{Ω_2+1}}` after `Ω_{Ω_{Ω_Ω}}`) ([TRIO-FIX-LASTLEAF.md](Googology/Trans/BMS/TRIO-FIX-LASTLEAF.md))
    - prove that the fuel `max 200 (depth of α)` of `TrioFixFuel` is enough for every `α` (more fuel never changes the matrix; checked on the sheet labels and some families)
    - for `ψ_0(Ω_2) ≤ α < Λ`, prove that the image of rules 1–10 lies in the standard forms and preserves the order (done for terms whose subscripts are `0` or `1`)
    - 🤖 decide how `TrioRules.ofTerm` reads `ψ_0(b)` (`ψ_0(Ω+1) = ε₀·ω` gets the matrix of `ε₀^{ε₀^ω}`)
    - 🤖 fix the rules for `u = Ω+1` outside level `ω`, and for other uncountable `u` ([TRIO-SHEET-FIXES.md](Googology/Trans/BMS/TRIO-SHEET-FIXES.md))
    - after Fix S: fix `Ω_ω·Ω^2+…`, `Ω_{ω^2}·Ω+Ω_ω·2` and the `Ω_ω+Ω_2+…` family (a lifted copy inside storeys laid by the end-of-unit rule) ([TRIO-FIX-STRETCH.md](Googology/Trans/BMS/TRIO-FIX-STRETCH.md))
    - merge the separate fix patches (`TrioFix*.lean`) into one rule set once they are done
- Notation
  - ω-Y (official)
    - prove well-foundedness with the official expansion (a separate repository, koteitan/wy-wo-por)
    - connect the proof here once it is done
  - DBMS
    - the translation into the ordinals for 3 rows and up
      - prove the upper bound `rkL 2 (cgen 2 (n+2)) ≤ rkL 2 (bgen3 n)` for `n ≥ 2` (then 3-row DBMS and BMS have the same ordinal; the lower bound and `n = 1` are proved)
        - 🤖 `n = 2`: show `T3(C) ∈ TrioStdL` for the content states `C`, then use `trio_cofinal` and `trio_expand_lt`
