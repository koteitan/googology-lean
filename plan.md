[← Back](README.md) | [English](plan.md) | [Japanese](plan-ja.md)

# Plan

The remaining work, arranged by the cells of the README tables. Items not being worked on now are cut to one line; the details are in [memo.md](memo.md) ("2026-10-24: details moved out of the plan") and in the git history. Every item is worked on in branch main unless another branch is named.

- Wilken's claim: Core(R₂⁺) = ψ_{Ω₁}(I_ω) ([Trans/PoR/InaccPsi](Googology/Trans/PoR/InaccPsi/README.md))
  - Lean: the maps between Wilken's systems and InaccPsi
    - R₂^C in Lean, and the chain to ν_C: the whole library builds with no sorry; the cited axioms are listed on [LEAN.md](Googology/Trans/PoR/InaccPsi/LEAN.md).
      - done (only S assumed): A1 and A2 closed; frontier F_A2 = sup_n ι(Γ(φ(glBn n, G+1))·ω), G = Γ_{Ω₁+1}. 109 axioms, none new.
      - also done: every countable x < υ_{λ+β} has a ϑ-node form (xaRep); WzUpU; image law at k = 0 for β ∈ D and at k = 1, β = 0; A3 tower packages.
      - road xbRoadZ (hyp.: UPPER, LOWER, cap past F_A2; WdThLow, WdEQfar if L(ω+1) ≤ ν_C; shift XbShift; XbVisGen at m*, L(n+1)): ν_C = L(ω+1).
      - skeleton ([STATUS.md](https://github.com/koteitan/googology-lean/blob/feature/r2-skel/Googology/Trans/PoR/InaccPsi/R2Skel/STATUS.md)): 45 sorry leaves: OPEN 23 (M 1, L 22), SUSPECT 2 (M 1, L 1), REFUTED 2 (M 1, L 1), REPLACED 18.
      - next: supply skShiftTh, skFormHighX, skSupKW; A3 skA3T0Start, skSysA3StepW; reading skX0LawDK, skTopFam, skWallBase/Step, skThFar; then L leaves.
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
