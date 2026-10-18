import Googology.Trans.PoR.InaccPsi.R2.SfNF

/-!
# `B_n` on the names `P(η)`: the successor step of the shift (`TpPvStep`) is proved

`θ = ψ_{Ω₂}(Ω_ω)`, `A_η = Ω_ω + θ·η`, `P(η) = ψ_{Ω₁}(A_η)`, `L(ξ) = ψ_{Ω₁}(Ω_ω·2 + P'·ξ)`,
`c = Ω_ω + P'·ω` (so `P(c) = L(ω)`), `B_n = Bc.bcB S n`, `σ = bcSig (bcPre (n+1)) bcPreW`.
A name `η` is *own* when `A_η ∈ Cl(A_η, P(η))`.

* `sfGood_of_own`: an own name is good;
* `sfB_add` (**`B_n` on the names, with a free summand**): let `η` be good with
  `L(n+1) ≤ P(η)` and `P(η + δ) < L(n+2)`, where `θ·δ` is the value of a normal form `e` that `σ`
  fixes and lies in every `Cl(a, b)` with `a > Ω_ω`.  Then there is `ζ'` with `c + ζ'` own,
  `B_n(P(η)) = P(c + ζ')` and `B_n(P(η + δ)) = P(c + ζ' + δ)`.  (The normal form of `P(η)` is
  `ψ^S_0(a)` with `|a| = A_η = α_{n+1} + |ρ|`, `θ ∣ |ρ|`, so `|σ(ρ)| = θ·ζ'`; the normal form of
  `P(η+δ)` is `ψ^S_0(a')` with `|a'| = A_η + θ·δ`, its rest is `ρ + e`, and `σ(ρ + e) = σ(ρ) + e`.)
* `sfPvB` (`δ = 1`, `e` the term of `θ`), `sfPvStep` (**`TpPvStep S`, unconditional**), hence (S2)
  `TpSuccMove S` (`sfSuccMove`).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Sf

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Notation.InaccPsi.Term Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Bc Googology.Trans.PoR.InaccPsi.R2.Nm

variable {S : InaccSeq.{0}}

theorem sfAlpha_eq (S : InaccSeq.{0}) (k : ℕ) :
    bcAlpha S k = ConjT.Aη S (Om ω + Nc.ncPp S * (k : Ordinal.{0})) :=
  (Lw.lw_A_L S _).symm

theorem sfAlphaW_eq (S : InaccSeq.{0}) :
    bcAlphaW S = ConjT.Aη S (Om ω + Nc.ncPp S * ω) := by
  rw [Lw.lw_A_L, ncPp_mul_omega]; rfl

/-- An own name is good. -/
theorem sfGood_of_own {η : Ordinal.{0}}
    (h : ConjT.Aη S η ∈ S.CSet (ConjT.Aη S η) (S.psi (ConjT.Aη S η) (Om 1))) : Bt.Good S η := by
  rcases eq_or_ne η 0 with rfl | h0
  · exact Nm.good_zero S
  refine (good_iff S h0).2 ?_
  have hlt : ConjT.Aη S η < ConjT.Aη S η + ConjT.th S := lt_add_of_pos_right _ (sfTh_pos S)
  have hm := (psi_mono (S := S) Low.InR_Om_one hlt.le).2 h
  have := psi_lt_psi_of_mem Low.InR_Om_one hlt hm
  rwa [ConjT.A_succ] at this

/-- Below `L(n+2)` the argument of `P(η)` is below `α_{n+2}`, hence below `Λ`. -/
theorem sfA_lt {n : ℕ} {η : Ordinal.{0}} (h : Pv S η < Bc.bcC S (n + 1)) :
    ConjT.Aη S η < bcAlpha S (n + 1 + 1) ∧ ConjT.Aη S η < S.Lam := by
  have hAlt : ConjT.Aη S η < bcAlpha S (n + 1 + 1) := by
    by_contra h'
    push Not at h'
    have h1 := (psi_mono (S := S) Low.InR_Om_one h').1
    have h2 : Pv S η < S.psi (bcAlpha S (n + 1 + 1)) (Om 1) := h
    exact absurd h2 (not_lt.2 h1)
  exact ⟨hAlt, hAlt.trans (by rw [← val_pre S (n + 1 + 1)]; exact val_lt_Lam S _)⟩

/-- **`B_n` on the names, with a free summand `θ·δ`.** -/
theorem sfB_add {n : ℕ} {η δ : Ordinal.{0}} {e : Term} (hg : Bt.Good S η)
    (he : NF e) (hef : bcFree e) (hev : val S e = ConjT.th S * δ)
    (hmem : ∀ a b : Ordinal.{0}, Om ω < a → ConjT.th S * δ ∈ S.CSet a b)
    (hlo : Bc.bcC S n ≤ Pv S η) (hhi : Pv S (η + δ) < Bc.bcC S (n + 1)) :
    ∃ ζ', ConjT.Aη S (Om ω + Nc.ncPp S * ω + ζ') ∈
        S.CSet (ConjT.Aη S (Om ω + Nc.ncPp S * ω + ζ'))
          (S.psi (ConjT.Aη S (Om ω + Nc.ncPp S * ω + ζ')) (Om 1)) ∧
      Bc.bcB S n (Pv S η) = Pv S (Om ω + Nc.ncPp S * ω + ζ') ∧
      Bc.bcB S n (Pv S (η + δ)) = Pv S (Om ω + Nc.ncPp S * ω + ζ' + δ) := by
  have hP1 : Pv S η ≤ Pv S (η + δ) := Pv_mono le_self_add
  have hAL : ConjT.Aη S η < S.Lam := (sfA_lt (hP1.trans_lt hhi)).2
  have hown := sfOwn hg hAL
  have hαA : bcAlpha S (n + 1) ≤ ConjT.Aη S η := sfArg_le (sfOwn_alpha S n) hown hlo
  have hWα : Om ω < bcAlpha S (n + 1) := by
    unfold bcAlpha
    exact lt_of_lt_of_le (lt_add_of_pos_right _ (Om_pos omega0_ne_zero)) le_self_add
  have hAδ : ConjT.Aη S (η + δ) = ConjT.Aη S η + ConjT.th S * δ := Bt.A_add S η δ
  have hown1 : ConjT.Aη S η + ConjT.th S * δ ∈ S.CSet (ConjT.Aη S η + ConjT.th S * δ)
      (S.psi (ConjT.Aη S η + ConjT.th S * δ) (Om 1)) := by
    have h1 := (psi_mono (S := S) Low.InR_Om_one
      (le_self_add : ConjT.Aη S η ≤ ConjT.Aη S η + ConjT.th S * δ)).2 hown
    exact CSet.add_mem h1 (hmem _ _ (lt_of_lt_of_le hWα (hαA.trans le_self_add)))
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Qq.qqL_lt_omega S (n + 1 + 1)
  have hx0 : Pv S η < Nc.ncL S ω := (hP1.trans_lt hhi).trans hLw
  have hx1 : Pv S (η + δ) < Nc.ncL S ω := hhi.trans hLw
  obtain ⟨a, ha, hva⟩ := sfNf_psi hown (bcD_nf S hx0).1 (val_nf S hx0)
  obtain ⟨a1, ha1, hva1⟩ := sfNf_psi hown1 (bcD_nf S hx1).1
    (by rw [val_nf S hx1, ← hAδ])
  have hD : bcD S (psiS Term.zero a) := ha ▸ bcD_nf S hx0
  have hD1 : bcD S (psiS Term.zero a1) := ha1 ▸ bcD_nf S hx1
  have hN := hD.1
  have hN1 := hD1.1
  have hAW : val S a < bcAlphaW S := hD.2.2.2 rfl
  have hA1W : val S a1 < bcAlphaW S := hD1.2.2.2 rfl
  have hlo0 : bcAlpha S (n + 1) ≤ val S a := hva ▸ hαA
  have hlo1 : bcAlpha S (n + 1) ≤ val S a1 := by
    rw [hva1]; exact hαA.trans le_self_add
  have hB0 := sfB_psi (n := n) hN hlo0 hAW
  have hB1 := sfB_psi (n := n) hN1 hlo1 hA1W
  rw [hva] at hB0
  rw [hva1, ← hAδ] at hB1
  have hpre := (bc_pre_iff S hN.2.1 hAW).2 hlo0
  have hpre1 := (bc_pre_iff S hN1.2.1 hA1W).2 hlo1
  have hvρ : val S a = bcAlpha S (n + 1) + val S (bcDrop (n + 3) a) := by
    have := val_of_pre S hN.2.1 hpre; rwa [sfPre_len] at this
  have hvρ1 : val S a1 = bcAlpha S (n + 1) + val S (bcDrop (n + 3) a1) := by
    have := val_of_pre S hN1.2.1 hpre1; rwa [sfPre_len] at this
  have hdα : ConjT.th S ∣ bcAlpha S (n + 1) := by rw [sfAlpha_eq]; exact sfTh_dvd_A S _
  have hdρ : ConjT.th S ∣ val S (bcDrop (n + 3) a) := by
    have := sfTh_dvd_A S η
    rw [← hva, hvρ] at this
    exact (dvd_add_iff hdα).1 this
  have hDa : bcD S a := bcD_sub hD (sub_psiS_a _ _)
  have hDρ : bcD S (bcDrop (n + 3) a) := bcD_drop hDa (n + 3)
  obtain ⟨ζ', hζ'⟩ := sfSig_dvd n hDρ hdρ
  have hvr1 : val S (bcDrop (n + 3) a1) = val S (bcDrop (n + 3) a) + ConjT.th S * δ := by
    have e1 : bcAlpha S (n + 1) + val S (bcDrop (n + 3) a1) =
        bcAlpha S (n + 1) + (val S (bcDrop (n + 3) a) + ConjT.th S * δ) := by
      rw [← hvρ1, hva1, ← hva, hvρ, add_assoc]
    exact add_left_cancel e1
  have hNρ1 : NF (bcDrop (n + 3) a1) := NF_bcDrop _ hN1.2.1
  obtain ⟨hNadd, hvadd, -⟩ := addNF_spec (S := S) hDρ.1 he
  have hρ1 : bcDrop (n + 3) a1 = addNF (bcDrop (n + 3) a) e :=
    eq_of_val_eq S hNρ1 hNadd (by rw [hvadd, hev, hvr1])
  have hσ1 : val S (bcSig (bcPre (n + 1)) bcPreW (bcDrop (n + 3) a1)) =
      val S (bcSig (bcPre (n + 1)) bcPreW (bcDrop (n + 3) a)) + ConjT.th S * δ := by
    rw [hρ1, bcSig_addNF (k := n) hDρ (bcD_free he hef), bcSig_free hef,
      (addNF_spec (S := S) (bc_NF (k := n) hDρ) he).2.1, hev]
  have hT : bcAlphaW S + ConjT.th S * ζ' = ConjT.Aη S (Om ω + Nc.ncPp S * ω + ζ') := by
    rw [Bt.A_add, ← sfAlphaW_eq]
  refine ⟨ζ', ?_, ?_, ?_⟩
  · have hσN : NF (bcSig (bcPre (n + 1)) bcPreW (psiS Term.zero a)) := bc_NF (k := n) hD
    rw [bcSig_psiS_zero, bcArg_of_pre hpre, sfPre_len] at hσN
    have hsem : Sem S (psiS Term.zero (bcApp bcPreW
        (bcSig (bcPre (n + 1)) bcPreW (bcDrop (n + 3) a)))) := sem_of_NF hσN
    have h2 := hsem.2.2
    rw [show Om (val S Term.zero + 1) = Om 1 by rw [show val S Term.zero = 0 from rfl, zero_add],
      val_bcApp_preW, hζ', hT] at h2
    exact h2
  · rw [hB0, hζ']
    show S.psi _ (Om 1) = S.psi (ConjT.Aη S _) (Om 1)
    rw [hT]
  · rw [hB1, hσ1, hζ']
    show S.psi _ (Om 1) = S.psi (ConjT.Aη S _) (Om 1)
    rw [Bt.A_add S (Om ω + Nc.ncPp S * ω + ζ') δ, ← hT, add_assoc]

/-- **`B_n` on the names at a good `η`**: `B_n(P(η)) = P(η')`, `B_n(P(η+1)) = P(η'+1)`, `η'` own. -/
theorem sfPvB {n : ℕ} {η : Ordinal.{0}} (hg : Bt.Good S η) (hlo : Bc.bcC S n ≤ Pv S η)
    (hhi : Pv S (η + 1) < Bc.bcC S (n + 1)) :
    ∃ ζ', ConjT.Aη S (Om ω + Nc.ncPp S * ω + ζ') ∈
        S.CSet (ConjT.Aη S (Om ω + Nc.ncPp S * ω + ζ'))
          (S.psi (ConjT.Aη S (Om ω + Nc.ncPp S * ω + ζ')) (Om 1)) ∧
      Bc.bcB S n (Pv S η) = Pv S (Om ω + Nc.ncPp S * ω + ζ') ∧
      Bc.bcB S n (Pv S (η + 1)) = Pv S (Om ω + Nc.ncPp S * ω + ζ' + 1) :=
  sfB_add hg sfThT_NF sfThT_free (by rw [sfThT_val, mul_one])
    (fun a b h => by rw [mul_one]; exact ConjT.th_mem S h) hlo hhi

/-- **`TpPvStep S` holds** (no hypothesis). -/
theorem sfPvStep : Tp.TpPvStep S := by
  intro n η hg hlo hhi
  obtain ⟨ζ', -, h0, h1⟩ := sfPvB hg hlo hhi
  exact ⟨_, h0, h1⟩

/-- **(S2) `TpSuccMove S` holds** (no hypothesis beyond Theorem GEN). -/
theorem sfSuccMove : Tp.TpSuccMove S := Tp.tpStep_of_pv sfPvStep

end Googology.Trans.PoR.InaccPsi.R2.Sf
