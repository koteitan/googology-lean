[← Back](README.md) | [English](plan.md) | [Japanese](plan-ja.md)

# Plan

The remaining work, arranged by the cells of the README tables.

- Table of notations (definition of expansion, well-foundedness)
  - add the row of ω-Y (official)
    - well-foundedness: prove it with the official expansion (a separate repository, koteitan/wy-wo-por)
    - connect the proof here once it is done
- Table of translations into the ordinals
  - DBMS with 3 rows and up
    - surjectivity (the image is known exactly): show that 3-row DBMS has the same ordinal as 3-row BMS
      - prove the upper bound `rkL 2 (cgen 2 (n+2)) ≤ rkL 2 (bgen3 n)` for `n ≥ 2` (then 3-row DBMS and BMS have the same ordinal; the lower bound and `n = 1` are proved)
        - `n = 2`: reduced to one statement (`DBMS/ThreeRowUpperNC*.lean`, `ThreeRowUpperRP*.lean`; `RPLastShape` is proved)
          - 🤖 prove `T3nPushStd`: if `t3n C` is trio-standard, so is `t3n (pushL C y)` (0 failures on about 1.6 million matrices)
- Table of translations between notations
  - extended Buchholz ψ → trio sequences (✅❌❌✅❌❌)
    - preserves the rank: for all of `ψ_0(Λ)`, the image lies in the standard forms of 3-row BMS and preserves the order
      - fix the rules (fixes go on top of `TrioRulesAll`)
        - 🤖 after Fix nonlast-other: narrow the regimes where Fix M, Fix G and change 1 act, so that they stop breaking pairs outside the calibrated families (e.g. `Ω_{Ω_2}+Ω_ω+Ω` vs `Ω_{Ω_2}+Ω+ω`; `BMS/TrioFixNonLastOther.lean`)
        - after Fix L: fix the other levels of the same kind after `Ω_{Ω_Ω}` (`Ω_{ω+1}`, `Ω_{Ω+ω+1}`, `Ω_{Ω+ω·2}`, `Ω_{Ω·2+1}`, `Ω_{Ω·3}`, `Ω_{Ω^2}`, `Ω_{Ω_2·2}`, …) and case K inside a chain (`Ω_{Ω_{Ω_2+1}}` after `Ω_{Ω_{Ω_Ω}}`) ([TRIO-FIX-LASTLEAF.md](Googology/Trans/BMS/TRIO-FIX-LASTLEAF.md))
        - 🤖 after Fix U: rule 9 for `u = Ω+k` with `w ≥ Ω_{Ω+1}` not starting with `ψ` (e.g. `ψ_{Ω_{Ω+2}}(Ω_{Ω_{Ω+1}+Ω_Ω})`), levels `L ≥ 2` with `Ω_Ω < w < Ω_u`, infinite levels, limit and countable `u` ([TRIO-FIX-U.md](Googology/Trans/BMS/TRIO-FIX-U.md))
        - after Fix S: fix `Ω_ω·Ω^2+…`, `Ω_{ω^2}·Ω+Ω_ω·2` and the `Ω_ω+Ω_2+…` family (a lifted copy inside storeys laid by the end-of-unit rule) ([TRIO-FIX-STRETCH.md](Googology/Trans/BMS/TRIO-FIX-STRETCH.md))
        - merge the separate fix patches (`TrioFix*.lean`) into one rule set once they are done
      - for `ψ_0(Ω_2) ≤ α < Λ`, prove that the image of rules 1–10 lies in the standard forms and preserves the order (done for terms whose subscripts are `0` or `1`)
      - 🤖 prove `CalibSt` (the rule map of Fix `strip` equals the tree map `trioE2` on terms with subscripts 0 and 1; 0 differences on 9,782 terms) ([TRIO-FIX-STRIP.md](Googology/Trans/BMS/TRIO-FIX-STRIP.md))
      - prove that the fuel `max 200 (depth of α)` of `TrioFixFuel` is enough for every `α` (more fuel never changes the matrix; checked on the sheet labels and some families)
