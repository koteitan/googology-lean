[← Back](README.md) | [English](plan.md) | [Japanese](plan-ja.md)

# Plan

- Trans
  - trio sequences (BMS, 3 rows)
    - replace the fuel 200 of the rules by a bound that grows with the term, so that `trioMatrixL` is injective at every depth (now two terms at depths 206 and 207 get the same matrix)
    - for `ψ_0(Ω_2) ≤ α < Λ`, prove that the image of rules 1–10 lies in the standard forms and preserves the order (done for terms whose subscripts are `0` or `1`)
    - decide how `TrioRules.ofTerm` reads `ψ_0(b)` (`ψ_0(Ω+1) = ε₀·ω` gets the matrix of `ε₀^{ε₀^ω}`)
    - 🤖 fix the order of `Ω_{Ω_Ω}+Ω_{Ω_2}+1` and `Ω_{Ω_Ω}·2`, which the fixed rules still reverse
    - fix the rules for `u = Ω+1` outside level `ω`, and for other uncountable `u` ([TRIO-SHEET-FIXES.md](Googology/Trans/BMS/TRIO-SHEET-FIXES.md))
    - fix the rules on the stretch from `Ω_ω·Ω+Ω_2` to `Ω_ω·Ω·2` (the verdict on row 3480, [TRIO-ROW-3480.md](Googology/Trans/BMS/TRIO-ROW-3480.md))
    - normalize `ω^atom = atom` in the rules' `mul` (the printed label of row 4369)
- Notation
  - ω-Y (official)
    - prove well-foundedness with the official expansion (a separate repository, koteitan/wy-wo-por)
    - connect the proof here once it is done
  - DBMS
    - the translation into the ordinals for 3 rows and up
      - prove the conjecture "for `n ≥ 1`, `rkL 2 (cgen 2 (n+2))` equals the rank of the BMS generator `(0,0,0)...(n,n,n)`" (so 3-row DBMS and BMS have the same ordinal; `n = 1` is proved)
      - 🤖 which lists of blocks are standard at 3 rows
