[← Back](README.md) | [English](plan.md) | [Japanese](plan-ja.md)

# Plan

The remaining work, arranged by the cells of the README tables. Items not being worked on now are cut to one line; the details are in [memo.md](memo.md) ("2026-10-24: details moved out of the plan") and in the git history. Every item is worked on in branch main unless another branch is named.

- Wilken's claim: Core(R₂⁺) = ψ_{Ω₁}(I_ω) ([Trans/PoR/InaccPsi](Googology/Trans/PoR/InaccPsi/README.md))
  - Lean: the maps between Wilken's systems and InaccPsi
    - 🤖 R₂^C in Lean, and the chain to ν_C: the whole library builds with no sorry; the cited axioms are listed on [LEAN.md](Googology/Trans/PoR/InaccPsi/LEAN.md).
      - done (only S assumed): region A closed; layer frontier and direct readings of every layer c below X (skZbDirectX), by one reading vR of all codes. 113 axioms.
      - also: window RS input and cap off υ-fixed restarts, Θ = ρ at isolated ones; atoms move to K_Y; base ι(Ω₂): reach, cap; codes ≤ K_ω read short.
      - road yqRoadS (hyp.: UPPER, LOWER, cap past the frontier; WdThLow, WdEQfar if L(ω+1) ≤ ν_C; the shift XoShift; XoSup): ν_C = L(ω+1).
      - skeleton ([STATUS.md](https://github.com/koteitan/googology-lean/blob/feature/r2-skel/Googology/Trans/PoR/InaccPsi/R2Skel/STATUS.md)): OPEN leaves on the road: 12 (all L); skZbDirectX proved (round 215); skTopLawAll, skPsi3OffRest2 and skAtHi3 proved (Kx.kxTopLawAll, Ky.kyPsi3OffRest2, Kz.kzAtHi3); root vacuity open.
      - done: the layers past X below θ (skLayPastXθ, no hypothesis): X ≤ c < B₂ (Qc, Phase C), B₂ ≤ c < B₃ (Qd, Phase D1), and every c < θ (Xi.xi_past: one layer per code bound below θ read by R_x = π∘ι, the cited ι and P₀ of R2.CitedXi; Xi.xi_imgAll: Lemma IMG at every point of Tᵖ ∩ Ω₁, the covering π⁻¹∘f against the full [W07b] Claim 5.6, R2.claim56pw); skFixCont (Xi.xi_code_cont: the codes c < m_λ lie below θ, π(Θ_λ c) = Θ_μ(c), and the restarts ι(g + ω^{e'}) with m_μ ≥ c are cofinal); also in (l₀, ι(Ω_ω)): skBCCont, the block induction Zo.zoBC3 takes the value input).
      - done: the layers θ ≤ c < Ω₂ and the base ι(Ω₂) (skLayPastTh, skBCBaseUL): the term system of a code bound ≤ K_ω, readings Θ_y, Lemma IMG and Lemma RS through the FRAG map (Aw).
      - 🤖 next: the other 10 road leaves: windows and tops (skWin/Top{InR, Big}, skTopLwNo2), skBC{InR, Big}, skFixCapVF, skZlCfg, skLevImgHi5.
        - 🤖 now: the big readings above ι(Ω₂): a reading law for the codes K_ω ≤ c < P′ (Θ(ψ_{Ω₂}(Ω_ω + ξ)) = ϑˣ(Ω₁·Ω₁ + shift of ξ), the block step G(x) ↦ υ_{λ+1+x}) with the FRAG clause at moving levels (Za.zaFragV); done: every range restart below ι(Ω₂) and the base ι(Ω₂) (Aw.aw_UV, Aw.aw_base_UL).
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
