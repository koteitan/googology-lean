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
  - 🤖 the Lean axiom `P1_isominimal` ([Main/Cited.lean](Googology/Trans/PSS/Main/Cited.lean)) reads Carlson–Wilken 2012 Cor 6.3(1) at τ = 1; its isominimality content is Thm 4.1 of Wilken, JSL 72 (2007), which is not available, so the reading cannot be checked from the papers we have: prove the isominimality step of the 2-row proof without Cor 6.3(1) (e.g. by induction from Carlson 2001 Thm 5.9 only) and drop the axiom
  - extend Φ to trio sequences and R₂⁺ ([Trans/BMS/POR.md](Googology/Trans/BMS/POR.md); current rule por/phi3def2.py: 1057 sheet rows fit with the fix table, 0 order violations on 7 test sets up to (0,0,0)(1,1,1)(2,2,2))
    - 🤖 fix phi3def2.py at X = 905 (2,0,0) = (0,0,0)(1,1,1)(2,1,0)(3,2,1)(4,2,0)(2,0,0): along the fundamental sequence X[n], ι(Φ(X[n])) < ι(R) < ι(Φ(X)), where R is the sheet's reading (certified for n ≤ 3), so Φ leaves a gap below X; the same happens at 946 (2,0,0) (sheet rows 907, 947)
      - prove the bound for all n (and the 3-row sibling lemma it needs)
      - find the rule change that gives R, rerun the fit and the order tests
    - decide the 57 limit-step pairs still undecided (720 of 777 are certified "<"; they seem to need up-steps nested 3 deep), and prove that ι∘Φ₃ increases along BM4 fundamental sequences (needs: a down1 copy keeps the reach of the copied nodes; the base case at the bad root for nested limits)
    - analyse R₂⁺ itself ([Trans/BMS/R2PLUS.md](Googology/Trans/BMS/R2PLUS.md); Lemma L, Theorems A, B, EQ, S, S+, M, Prop P′ and the remark of Carlson–Wilken 2012 §7 in the needed form are proved on paper and refereed)
      - 🤖 close the gap in Theorem S for all standard trio matrices ≤ U = (0,0,0)(1,1,1)(1,1,0)(2,2,1)(2,0,0)(1,1,0)(2,2,1): prove Theorem Pi-PAT with two lemmas (a sum step never reaches the copied block; the closure never makes a top-part diagonal longer than the term's own) and a larger m
      - prove that Carlson's covering definition R₂^C equals R₂^S beyond υ_{ω+1} (Theorem B in R₂^C is a sketch)
      - the backbone conjecture BLK beyond υ_{ω·ω}, then heads with Ω₂-level structure (new ordinal arithmetic)
    - sheet rows that do not fit: 1334/1335/1434/1435 (a level more than the cut chain of the last summand), bare extra up-kids (1490, 1503, 1504, 1515, 1516, 1583), 1582, 569, 1476, 1489, 575, 709, 1409, 1460, 1577; fixed rows 601/718/1348/1401 where the fix and Φ differ
    - shorten the definition of phi3def2.py (the level-column list, lh₁) and replace its named cases lwpos, lnest, kcross by general rules
