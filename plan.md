[← Back](README.md) | [English](plan.md) | [Japanese](plan-ja.md)

# Plan

The remaining work, arranged by the cells of the README tables. Items not being worked on now are cut to one line; the details are in [memo.md](memo.md) ("2026-10-24: details moved out of the plan") and in the git history. Every item is worked on in branch main unless another branch is named.

- Wilken's claim: Core(R₂⁺) = ψ_{Ω₁}(I_ω) ([Trans/PoR/InaccPsi](Googology/Trans/PoR/InaccPsi/README.md))
  - Lean: the maps between Wilken's systems and InaccPsi
    - R₂^C in Lean, and the chain to ν_C: the whole library builds with no sorry; the cited axioms are listed on [LEAN.md](Googology/Trans/PoR/InaccPsi/LEAN.md).
      - done (only S assumed): frontier ι(Γ(φ(3, G+1))) ≤ ι(Ω₂) (G = Γ_{Ω₁+1}), P < L(0) = m*; Φ_μ (μ ≤ B₂): CL, UB, EQ; H^s for all finite s. 104 axioms.
      - 4 roads, not yet one (hyp.: UPPER, LOWER, cap above frontier, CL, EQ, TopFrom/Unc in [B₂, Ω₂), UdAtMove25, …): ν_C = L(ω+1), L(ω) <₂ L(ω+1).
      - left 1 (frontier): the wall φ(3, G+1) is proved; next a system with Z ≤ B₄ (IMG holds below B₄), Veblen levels ≥ 4, atoms Γ(c), offsets ≥ Γ_{x+2}.
      - left 2 (CL): hull isomorphism done at Ω₁·M with rjDat M < κ; left: rjDat M ≥ κ, Γ ≥ ε_{Ω₁+1}, TkSucc, form of reaches, EQ at closed points, supply.
      - left 3 (moves): image T done below Y₃ = ψ₃(Ω₃) (hyp.: restart index); T past Y₃, level systems up to Y₃, H^k up to θ, its citation; θ; join roads.
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
