[← Back](README.md) | [English](plan.md) | [Japanese](plan-ja.md)

# Plan

The remaining work, arranged by the cells of the README tables. Items not being worked on now are cut to one line; the details are in [memo.md](memo.md) ("2026-10-24: details moved out of the plan") and in the git history. Every item is worked on in branch main unless another branch is named.

- Wilken's claim: Core(R₂⁺) = ψ_{Ω₁}(I_ω) ([Trans/PoR/InaccPsi](Googology/Trans/PoR/InaccPsi/README.md))
  - Lean: the maps between Wilken's systems and InaccPsi
    - 🤖 R₂^C in Lean, and the chain to ν_C: the whole library builds with no sorry; the cited axioms are listed on [LEAN.md](Googology/Trans/PoR/InaccPsi/LEAN.md).
      - done (only S assumed): region A closed; layer frontier and direct readings of every layer c below X (skZbDirectX), by one reading vR of all codes. 113 axioms.
      - also: window RS input and cap off υ-fixed restarts, Θ = ρ at isolated ones; atoms move to K_Y; base ι(Ω₂): reach, cap; codes ≤ K_ω read short.
      - road yqRoadS (hyp.: UPPER, LOWER, cap past the frontier; WdThLow, WdEQfar if L(ω+1) ≤ ν_C; the shift XoShift; XoSup): ν_C = L(ω+1).
      - skeleton ([STATUS.md](https://github.com/koteitan/googology-lean/blob/feature/r2-skel/Googology/Trans/PoR/InaccPsi/R2Skel/STATUS.md)): OPEN leaves on the road: 14 (all L); skZbDirectX proved (round 215); skTopLawAll, skPsi3OffRest2 and skAtHi3 proved (Kx.kxTopLawAll, Ky.kyPsi3OffRest2, Kz.kzAtHi3); root vacuity open.
      - 🤖 next: the layers past X (skLayPastXθ): X ≤ c < B₂ = ψ_{Ω₂}(ε_{Ω₂+1}) done (Phase C), then B₂ ≤ c < θ.
        - done (Qc*): the atom system qcU of the codes below B₂; Lemma IMG below every ϑᵖ(Ω₁·N), Ω₁ ≤ N < ε_{Ω₁+1}, data below ρ (Qc.qc_img_rst; the layer tops may pass X^x, Qc.QcBd); the reading vQ, gates qcG, base readings qcA of every code below B₂.
        - done: digit systems below B₂ (Qc.QDS, its step and raised gates); the gates qcG of the codes (a code over Z has its gate below Z, Qc.qc_gate); the level reading λ(x) of H_λ(y) (Qc.qcLv_main); the readings of fixed points of Γ are closed (Qc.qc_fix_cl); Qc.QsGood with the step (Qc.qsGood_succ) and the union at a limit (Qc.qsGood_lim) with the tops at non-atoms and atoms (Qc.qsTopNA, Qc.qsTopAt).
        - done: the top at a fixed point H_λ(y) of Γ in [X, B₂) (Qc.qsTopFix: the level readings cofinal, Qc.qcLv_cof, and exact, Qc.qs_lv_pi); Qc.QsGood at every ε-number in [B_Γ, B₂) (Qc.qsGood_all).
        - done: the layers at the fixed points of Γ below B₂ (Qc.qsLay_all), Zm.ZmPastAt S c for every c < B₂ (Qc.qc_past).
        - 🤖 left: B₂ ≤ c < θ (skLayPastB2θ, Phase D; X ≤ c < B₂ is skLayPastXB2, proved).
          - done: the atom system past B₂ with the bound θ (Qt.qtU S: atoms the strongly critical members of K⁽⁰⁾_Z in (Ω₁, θ)) and its hull facts at S (Zb.ZbAS.Ok, split from Zb.ZbAS so that the atoms may depend on S).
          - 🤖 the readings of the codes below θ: first below B₃ = Qd.qdB (Veblen levels; Qd.qdLv done), then up to θ; at a fixed point Hˡ_λ(y) of Γ a level reading of λ (one cardinal down, the leaves read at x) with its data, order, cofinality and exactness (R2.CitedVd).
            - done (Qd*): the reading vD and the gates qdGt with their clauses, B₂ < B₃ ≤ θ, the codes QdCl = K⁽⁰⁾ below B₃, the bound QdBd of the tops (Veblen levels N < Γ_{Ω₁+1}).
            - open: Lemma IMG below the points of the Veblen levels (the hypothesis Qd.QdImgH): it needs the reach past ε_{Ω₁+1} ([W07b] Def 4.1 with δ an ε-number, localization, cr) and a φ case of the copy lemma.
          - the Qc chain at the new bound: digit systems, the tops, the layers, cofinal fixed points with small gates.
        - then: the other road leaves (skLayPastTh, windows and tops, skBC, skFix, skZlCfg, skLevImgHi4).
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
