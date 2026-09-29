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
          - prove `TrioPushStd` (a statement about trio matrices only; `T3nPushStd` follows, `DBMS/ThreeRowUpperPushBMS.lean`; 0 failures on 48,438 cases). It is a standardness question of the kind koteitan/trio treats as its hard core
- Table of translations between notations
  - extended Buchholz ψ → trio sequences (✅❌❌✅❌❌)
    - preserves the rank: for all of `ψ_0(Λ)`, the image lies in the standard forms of 3-row BMS and preserves the order
      - fix the rules (fixes go on top of `TrioRulesAll`)
        - after Fix nonlast-other2: pairs still out of order after a leaf that shares its value with a lower top (`Ω_{Ω_{ω+2}}` 52, `Ω_{Ω_{Ω_ω}}` 24, `Ω_{Ω_{ω^2+1}}` 22, `Ω_{Ω_{ω^2}}` 8, `Ω_{Ω_{ω+1}}` 6), the mark above rule 6's storey after `Ω_{Ω_{ω^2}}`, and 117 non-standard matrices after `Ω_{Ω_{ω·2}}` ([TRIO-FIX-NONLAST2.md](Googology/Trans/BMS/TRIO-FIX-NONLAST2.md))
        - after Fix L: fix the other levels of the same kind after `Ω_{Ω_Ω}` (`Ω_{ω+1}`, `Ω_{Ω+ω+1}`, `Ω_{Ω+ω·2}`, `Ω_{Ω·2+1}`, `Ω_{Ω·3}`, `Ω_{Ω^2}`, `Ω_{Ω_2·2}`, …) and case K inside a chain (`Ω_{Ω_{Ω_2+1}}` after `Ω_{Ω_{Ω_Ω}}`) ([TRIO-FIX-LASTLEAF.md](Googology/Trans/BMS/TRIO-FIX-LASTLEAF.md))
        - after Fix U2: 22 rule-9 faults remain outside the claimed domain; infinite levels, limit and countable `u` ([TRIO-FIX-U2.md](Googology/Trans/BMS/TRIO-FIX-U2.md))
        - after Fix S: fix `Ω_ω·Ω^2+…`, `Ω_{ω^2}·Ω+Ω_ω·2` and the `Ω_ω+Ω_2+…` family (a lifted copy inside storeys laid by the end-of-unit rule) ([TRIO-FIX-STRETCH.md](Googology/Trans/BMS/TRIO-FIX-STRETCH.md))
        - merge the separate fix patches (`TrioFix*.lean`) into one rule set once they are done
      - for `ψ_0(Ω_2) ≤ α < Λ`, prove that the image of rules 1–10 lies in the standard forms and preserves the order (done for terms whose subscripts are `0` or `1`)
      - prove `CalibRd200` (the rule map of Fix `strip` equals `trioE2` up to reading depth 200; proved up to 100, false at 201; `CalibSt` without a bound is false because of the fuel) ([BMS/TrioFixStripCalibNo.lean](Googology/Trans/BMS/TrioFixStripCalibNo.lean))
      - prove that the fuel `max 200 (depth of α)` of `TrioFixFuel` is enough for every `α` (more fuel never changes the matrix; checked on the sheet labels and some families)
- Pair sequences and additive patterns of resemblance ([Trans/PSS/POR.md](Googology/Trans/PSS/POR.md))
  - formalize in Lean the paper proof that Φ preserves the order and that its image is the whole core of R₁⁺ ([Trans/PSS/proof/](Googology/Trans/PSS/proof/README.md): ι(Φ(M)) = 1 + val(pairTerm M))
    - the main chain is in Lean ([Trans/PSS/Main.lean](Googology/Trans/PSS/Main.lean)) except E1 and E2 ([Main/E12.lean](Googology/Trans/PSS/Main/E12.lean)): for a standard epsilon root N with α = o(N) and fold inputs Y_1, …, Y_n, E1: λ_α = α + o(Y_1) + ⋯ + o(Y_n); E2: if o(Y) > lead(lh(κ^α_ξ)) for the input Y after pre and ξ = α + o(pre), then o(Y) is α-≤₁-minimal (needs Wilken's ι_{1,α}, t^α_τ, CI, PL and [W07b] Thm 5.3, Cor 5.9)
  - extend Φ to trio sequences and R₂⁺ ([Trans/BMS/POR.md](Googology/Trans/BMS/POR.md); Φ₃i has 0 order violations below (0,0,0)(1,1,1)(2,1,1); Φ₃k extends it above row 915)
    - below (0,0,0)(1,1,1)(2,1,1): decide the 287 undecided limit-step pairs (prove that ι∘Φ₃ is monotone inside a term), row 907 (the sheet or Φ₃i on rows 906/907), row 1009 (ι(Φ₃i) ≤ ι(sheet))
    - analyse R₂⁺ itself (Wilken's R₂ is the pure structure), e.g. prove υ_ι ↔ ε₀·ι between R₂⁺ and R₂
    - rows above 915 (Φ₃k fits 787 sheet rows; 0 order violations in [(0,0,0)(1,1,1)(2,1,1), (0,0,0)(1,1,1)(2,2,1)), 4 certified just above (0,0,0)(1,1,1)(2,2,1)): root runs whose first summand has several ≤₂-levels (removes the 4 violations), nested frames (rows 1059, 1060, 1147–1151, 1283), markers of K_m followed by y=0 columns (1332–1340), the levels after a K_1 with a same-level child (1463–1550); the 372 undecided pairs of the new order test
