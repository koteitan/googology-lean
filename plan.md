[← Back](README.md) | [English](plan.md) | [Japanese](plan-ja.md)

# Plan

The remaining work, arranged by the cells of the README tables. Items not being worked on now are cut to one line; the details are in [memo.md](memo.md) ("2026-10-24: details moved out of the plan") and in the git history. Every item is worked on in branch main unless another branch is named.

- Wilken's claim: Core(R₂⁺) = ψ_{Ω₁}(I_ω) ([Trans/PoR/InaccPsi](Googology/Trans/PoR/InaccPsi/README.md))
  - Lean: the maps between Wilken's systems and InaccPsi
    - 🤖 R₂^C in Lean, and the chain to ν_C: the whole library builds with no sorry; the cited axioms are listed on [LEAN.md](Googology/Trans/PoR/InaccPsi/LEAN.md).
      - done (no hypotheses): codes up to ε_{Γ_{Ω₁+1}+1}·k + c'; frontier ι(Γ_{ε_{Γ_{Ω₁+1}+1}·ω}) < ι(Ω₂), P below L(0) = m*. 117 cited axioms, audited.
      - road (with hypotheses): if UPPER, LOWER and cap hold at restarts above the frontier, plus CL, EQ and others, then ν_C = L(ω+1), L(ω) <₂ L(ω+1).
      - left 1 (frontier): codes on the base ε_{Γ_{Ω₁+1}+1} (digit-wise EXACT), IMG at ζ_{Γ_{ρ+1}+1}, offsets ≥ Γ_{x+2}, ι(Ω₂) to L(0), then [L(0), L(ω+1)).
      - left 2 (CL): for a = L(n+1), targets in [υ_{a+ε_{Γ_{a+1}+1}}, L(n+2)); the long region needs ENUM-REACH for codes ≥ P′. Needed for CL and m* ≤₁ L(1).
      - left 3 (moves): B_n at ϑ-arguments in [ψ_{Ω₂}(1), Ω₂); atoms from ψ₂(φ(Γ₀, Ω₂+1)) to θ (next: levels ≥ Γ₀), then RnThMoveM, RnEQhi2.
  - paused (since 2026-10-17; resumes after the Lean work above): the rest of the upper bound (chains of length n, R₂^S, base changes), the full analysis, the lower bound, the first inaccessible
- BMS → PoR converter conv (turns a matrix M into a pattern conv(M); ord(P) is the ordinal of a pattern P; the goal is M < M' ⇔ ord(conv(M)) < ord(conv(M')))
  - ✅ M < (0,0,0)(1,1,1): proved on paper and in Lean
  - ✅ (0,0,0)(1,1,1) ≤ M < (0,0,0)(1,1,1)(1,1,0)(2,2,1)(2,0,0)(2,0,0): proved on paper
  - (0,0,0)(1,1,1)(1,1,0)(2,2,1)(2,0,0)(2,0,0) ≤ M < (0,0,0)(1,1,1)(2,2,2): fix where the program breaks the order
    - ✅ M < (0,0,0)(1,1,1)(1,1,0)(2,2,1)(2,0,0)(2,0,0)(2,0,0): proved on paper
    - left: the 26 limits X where ord(conv(X[n])) does not grow with n, the range above, the rows that disagree with the sheet
  - M ≥ (0,0,0)(1,1,1)(2,2,2): not tested
  - shorten the definition of the program
- Table of translations into the ordinals
  - DBMS with 3 rows and up: 3-row DBMS and 3-row BMS have the same ordinal (left: `TrioPushStd`)
- Table of translations between notations
  - extended Buchholz ψ → trio sequences (✅❌❌✅❌❌): order preserved below ψ_0(Λ) (the rest of the rule fixes, `CalibRd200`, `TrioFixFuel`)
- Library layout: make `BMS/common/` independent of extended Buchholz ψ
