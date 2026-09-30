[← Back](README.md) | [English](plan.md) | [Japanese](plan-ja.md)

# Plan

The remaining work, arranged by the cells of the README tables.

- BMS → PoR converter conv (branch main; a program that turns a Bashicu matrix M into a pattern of resemblance conv(M)). Write ord(P) for the ordinal that a pattern P stands for (the least place where P occurs in R₁⁺ or R₂⁺ = (Ord; 0, +, ≤, ≤₁, ≤₂)). The goal is M < M' ⇔ ord(conv(M)) < ord(conv(M')). Matrices are compared lexicographically; υ₁ = ψ₀(Ω_ω)
  - ✅ M < (0,0,0)(1,1,1) (2-row matrices = pair sequences; ord(conv(M)) = 1 + the ordinal of M): proved on paper and in Lean without sorry ([Trans/PSS/POR.md](Googology/Trans/PSS/POR.md))
    - 🤖 remove the Lean axiom `P1_isominimal` ([Main/Cited.lean](Googology/Trans/PSS/Main/Cited.lean)): it reads Carlson–Wilken 2012 Cor 6.3(1) at τ = 1, whose content is in Wilken, JSL 72 (2007), which is not available; prove the isominimality step without it (plan: the case τ = 1 of Theorem S+)
  - (0,0,0)(1,1,1) ≤ M ≤ (0,0,0)(1,1,1)(1,1,0)(2,2,1)(2,0,0)(1,1,0)(2,2,1) (3-row matrices = trio sequences, ord(conv(M)) ≤ υ_{ω+1}; program por/phi3def2.py, [Trans/BMS/POR.md](Googology/Trans/BMS/POR.md))
    - ✅ the matrices of class R_P (sums of three kinds of root terms): order preserved, proved on paper and refereed (Theorem S, [Trans/BMS/R2PLUS.md](Googology/Trans/BMS/R2PLUS.md)); below υ_{ω+1} ord is computed: ≤₁ is that of R₁⁺ and the only <₂-pair is υ_ω <₂ υ_{ω+1} (Theorems A, EQ)
    - 🤖 all standard matrices ≤ (0,0,0)(1,1,1)(1,1,0)(2,2,1)(2,0,0)(1,1,0)(2,2,1): close the gap in the general proof of Theorem S (Theorem Pi-PAT needs two lemmas, a sum step never reaches the copied block and the closure never makes a top-part diagonal longer than the term's own, and a larger m)
  - (0,0,0)(1,1,1)(1,1,0)(2,2,1)(2,0,0)(1,1,0)(2,2,1) < M < (0,0,0)(1,1,1)(2,2,2): the program gives a pattern; 0 order violations on 7 test sets, not proved
    - 🤖 fix the gap at X = 905 (2,0,0) = (0,0,0)(1,1,1)(2,1,0)(3,2,1)(4,2,0)(2,0,0): along the fundamental sequence X[n], ord(conv(X[n])) < ord(R) < ord(conv(X)) with R the sheet's reading (certified for n ≤ 3); the same at 946 (2,0,0) (sheet rows 907, 947)
      - prove the bound for all n (and the 3-row sibling lemma it needs)
      - find the rule change that gives R, rerun the fit and the order tests
    - decide the 57 limit-step pairs still undecided (720 of 777 are certified "<"; they seem to need up-steps nested 3 deep), and prove that ord(conv(X[n])) increases with n for every BM4 fundamental sequence X[n] (needs: a down1 copy keeps the reach of the copied nodes; the base case at the bad root for nested limits)
    - ord up to υ_{ω·ω}: the <₂-pairs are υ_{ωk} <₂ υ_{ωk+1} (Theorem B, proved for R₂^S). R₂⁺ has two definitions, R₂^C (Carlson's, by coverings; the checking program uses it) and R₂^S (by Σ_n-elementarity); prove that they agree beyond υ_{ω+1} (Theorem B for R₂^C is only sketched), then prove the order for these matrices
    - ord beyond υ_{ω·ω}: prove the conjecture BLK (each "backbone" behaves like the ε₀-multiples in Wilken's R₂), then handle terms whose head has Ω₂-level structure (needs new ordinal arithmetic)
    - sheet rows that do not fit: 1334/1335/1434/1435 (a level more than the cut chain of the last summand), bare extra up-kids (1490, 1503, 1504, 1515, 1516, 1583), 1582, 569, 1476, 1489, 575, 709, 1409, 1460, 1577; fixed rows 601/718/1348/1401 where the fix and the converter differ
  - M ≥ (0,0,0)(1,1,1)(2,2,2): not tested
  - the whole program: shorten the definition of phi3def2.py (the level-column list, lh₁) and replace its named cases lwpos, lnest, kcross by general rules
- Table of notations (definition of expansion, well-foundedness)
  - add the row of ω-Y (official): done on branch feature/trio-pair (v0.6.187, the port of the well-foundedness proof); not in main yet
  - add the row of Buchholz's ψ over ω weakly inaccessibles (InaccPsi): written on branch feature/inacc-psi; not in main yet
- Table of translations into the ordinals
  - DBMS with 3 rows and up (branch feature/trio-pair; the files are not in main)
    - surjectivity (the image is known exactly): show that 3-row DBMS has the same ordinal as 3-row BMS
      - prove the upper bound `rkL 2 (cgen 2 (n+2)) ≤ rkL 2 (bgen3 n)` for `n ≥ 2` (then 3-row DBMS and BMS have the same ordinal; the lower bound and `n = 1` are proved)
        - `n = 2`: reduced to one statement (`DBMS/ThreeRowUpperNC*.lean`, `ThreeRowUpperRP*.lean`; `RPLastShape` is proved)
          - prove `TrioPushStd` (a statement about trio matrices only; `T3nPushStd` follows, `DBMS/ThreeRowUpperPushBMS.lean`; 0 failures on 48,438 cases). It is a standardness question of the kind koteitan/trio treats as its hard core
- Table of translations between notations
  - extended Buchholz ψ → trio sequences (✅❌❌✅❌❌) (branch feature/trio-pair; the files are not in main)
    - preserves the rank: for all of `ψ_0(Λ)`, the image lies in the standard forms of 3-row BMS and preserves the order
      - fix the rules (fixes go on top of `TrioRulesAll`)
        - after Fix nonlast-other2: pairs still out of order after a leaf that shares its value with a lower top (`Ω_{Ω_{ω+2}}` 52, `Ω_{Ω_{Ω_ω}}` 24, `Ω_{Ω_{ω^2+1}}` 22, `Ω_{Ω_{ω^2}}` 8, `Ω_{Ω_{ω+1}}` 6), the mark above rule 6's storey after `Ω_{Ω_{ω^2}}`, and 117 non-standard matrices after `Ω_{Ω_{ω·2}}` ([TRIO-FIX-NONLAST2.md](https://github.com/koteitan/googology-lean/blob/feature/trio-pair/Googology/Trans/BMS/TRIO-FIX-NONLAST2.md))
        - after Fix L: fix the other levels of the same kind after `Ω_{Ω_Ω}` (`Ω_{ω+1}`, `Ω_{Ω+ω+1}`, `Ω_{Ω+ω·2}`, `Ω_{Ω·2+1}`, `Ω_{Ω·3}`, `Ω_{Ω^2}`, `Ω_{Ω_2·2}`, …) and case K inside a chain (`Ω_{Ω_{Ω_2+1}}` after `Ω_{Ω_{Ω_Ω}}`) ([TRIO-FIX-LASTLEAF.md](https://github.com/koteitan/googology-lean/blob/feature/trio-pair/Googology/Trans/BMS/TRIO-FIX-LASTLEAF.md))
        - after Fix U2: 22 rule-9 faults remain outside the claimed domain; infinite levels, limit and countable `u` ([TRIO-FIX-U2.md](https://github.com/koteitan/googology-lean/blob/feature/trio-pair/Googology/Trans/BMS/TRIO-FIX-U2.md))
        - after Fix S: fix `Ω_ω·Ω^2+…`, `Ω_{ω^2}·Ω+Ω_ω·2` and the `Ω_ω+Ω_2+…` family (a lifted copy inside storeys laid by the end-of-unit rule) ([TRIO-FIX-STRETCH.md](https://github.com/koteitan/googology-lean/blob/feature/trio-pair/Googology/Trans/BMS/TRIO-FIX-STRETCH.md))
        - merge the separate fix patches (`TrioFix*.lean`) into one rule set once they are done
      - for `ψ_0(Ω_2) ≤ α < Λ`, prove that the image of rules 1–10 lies in the standard forms and preserves the order (done for terms whose subscripts are `0` or `1`)
      - prove `CalibRd200` (the rule map of Fix `strip` equals `trioE2` up to reading depth 200; proved up to 100, false at 201; `CalibSt` without a bound is false because of the fuel) ([BMS/TrioFixStripCalibNo.lean](https://github.com/koteitan/googology-lean/blob/feature/trio-pair/Googology/Trans/BMS/TrioFixStripCalibNo.lean))
      - prove that the fuel `max 200 (depth of α)` of `TrioFixFuel` is enough for every `α` (more fuel never changes the matrix; checked on the sheet labels and some families)
