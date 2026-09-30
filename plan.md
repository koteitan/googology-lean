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
  - 🤖 confirm, with Wilken, "Assignment of ordinals to patterns of resemblance" (JSL 72, 2007; not available yet), that a 1-relativized isominimal set is an isominimal set, as read in the axiom `P1_isominimal` ([Main/Cited.lean](Googology/Trans/PSS/Main/Cited.lean)); everything else of the Lean proof of Φ is done and has no `sorry`
  - extend Φ to trio sequences and R₂⁺ ([Trans/BMS/POR.md](Googology/Trans/BMS/POR.md); Φ₃i has 0 order violations below (0,0,0)(1,1,1)(2,1,1); Φ₃k … Φ₃o extend it above row 915; Φ₃def is the single definition, Φ₃def2 adds kdl0)
    - 🤖 below (0,0,0)(1,1,1)(2,1,1): decide the 287 undecided limit-step pairs (prove that ι∘Φ₃ is monotone inside a term), rows 907 and 947 (decide the value of 905 (2,0,0) = (0,0,0)(1,1,1)(2,1,0)(3,2,1)(4,2,0)(2,0,0): the sheet's lift reading or Φ₃def2)
    - analyse R₂⁺ itself ([Trans/BMS/R2PLUS.md](Googology/Trans/BMS/R2PLUS.md); Lemma L, Theorems A, B and Prop P′ are proved on paper in the Σ_n structure R₂^S and refereed; 20 undecided pairs decided)
      - prove that Carlson's covering definition R₂^C equals R₂^S beyond υ_{ω+1} (done and refereed on [0, υ_{ω+1}], Theorem EQ; Theorem B in R₂^C is a sketch) — Carlson 2009 says it "will be established elsewhere"
      - 🤖 prove the remark of [CW12] §7 (M(σ, α) is σ-isominimal) or obtain Wilken, JSL 72 (2007); it decides 10 more pairs below υ_{ω+1}
      - 🤖 below U = (0,0,0)(1,1,1)(1,1,0)(2,2,1)(2,0,0)(1,1,0)(2,2,1) (T3(U) = υ_{ω+1}; Theorem S, with both links proved on paper, gives order preservation of phi3def2.py on the standard matrices of the class R_P): the other shapes (single XTgen terms and sums with them, conditional on the CW12 §7 remark)
      - the backbone conjecture BLK beyond υ_{ω·ω}, then heads with Ω₂-level structure (new ordinal arithmetic)
    - rows above 915 (Φ₃o fits 1051 sheet rows; all seven order tests up to (0,0,0)(1,1,1)(2,2,2) show 0 violations and 0 same-pattern pairs; POR.md §14 lists every flag with its principle; §15 restates Φ₃ as one flag-free definition in 11 clauses, phi3def.py, identical to Φ₃o on all 2973 order-test matrices and 1099 sheet rows, 3 named cases): the point with a level more than the cut chain of its last summand (1334–1336, 1434–1436), the rest of 1450–1642; shorten the level-column list and lh₁ of the definition and replace its 3 named cases (lwpos, lnest, kcross) by general rules; POR.md §16 classifies the 45 no + 3 sup rows into 12 families: rule kdl0 (phi3def2.py) fits 1526, 1527, 1553, 1594 (1055 rows, order tests still 0/0), 7 rows certified same ordinal, 1177 equals its fix; open: 1334/1335/1434/1435, bare extra up-kids (1490, 1503, 1504, 1515, 1516, 1583), 1582, 569, 1476, 1489, 575, 709, 1409, 1460, 1577, fixed rows 601/718/1348/1401; the 464 undecided pairs
