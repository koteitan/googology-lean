[← Back](README.md) | [English](plan.md) | [Japanese](plan-ja.md)

# Plan

Only the work still to do, as a tree under the cells of the README tables. The record of finished work is in [memo.md](memo.md). Items that name no other branch are worked on in branch main.

- Wilken's claim: Core(R₂⁺) = ψ_{Ω₁}(I_ω) ([Trans/PoR/InaccPsi](Googology/Trans/PoR/InaccPsi/README.md))
  - Lean: R₂^C and ν_C = L(ω+1) (branch feature/por; the root `skNuC` of the skeleton uses 10 unproved leaves; [STATUS.md](https://github.com/koteitan/googology-lean/blob/feature/r2-skel/Googology/Trans/PoR/InaccPsi/R2Skel/STATUS.md))
    - the restarts λ above ι(Ω₂) (leaves skBC{InR, Big}, skFixCapVF, skWin/Top{InR, Big}). Symbols: Θ_λ is the reading of codes at λ, m_λ the code of λ, δ_λ = υ_{λ+ω+1}, K_ω = ψ_{Ω₂}(Ω_ω + Ω₂), P′ = ψ_{Ω₂}(Ω_ω + Ω_ω)
      - 🤖 the reading law of the codes K_ω ≤ c < P′: Θ(ψ_{Ω₂}(Ω_ω + ξ)) = ϑˣ(Ω₁·Ω₁ + the shift of ξ), FRAG by Za.zaFragV
      - redo Lemma IMG over the context with crossings YsRstK (port GnImg, XiImg, AwImg)
      - Lemma TOP and Lemma RS at the restarts with Θ_λ(m_λ) ≥ δ_λ (the reach is k_λ(Θ_λ(m_λ)))
      - an internal induction on the restart for UPPER (InR) and LOWER (Big) at the fixed restarts
      - CapV at the restarts with Θ_λ(m_λ) ≥ δ_λ·ω (skFixCapVF)
    - skTopLwNo2: if ν_C < L(ω+1) then not L(ω) ≤₂ ν_C
    - skZlCfg: the construction of the supply restarts (Zl.ZlCfg)
    - skLevImgHi5: the level image of the shift (Zk.ZkImgP5)
    - check that the hypotheses of the root `skNuC` are not vacuous
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
