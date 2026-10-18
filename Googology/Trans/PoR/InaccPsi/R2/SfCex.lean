import Googology.Trans.PoR.InaccPsi.R2.SfCode

/-!
# A range restart where the reading of the code moves

`θ = ψ_{Ω₂}(Ω_ω)`, `A_η = Ω_ω + θ·η`, `P(η) = ψ_{Ω₁}(A_η)`, `L(ξ) = ψ_{Ω₁}(Ω_ω·2 + P'·ξ)`,
`c_n = L(n+1)`, `B_n = Bc.bcB S n`, `ι` the index of Theorem GEN.

* `sfPred_gen`: for `A_η` own and `ω < ι(η)`, if `ι(η)` is not a restart index then `η = g + 1` or
  `η = g + ω` with `A_g` own (the argument of `Sf.sfTgt_pred`);
* `sfCexName` (**the name** `η = Ω_ω + P'·(n+1) + ω^{L(n+1)}`): `A_η` is own, `ι(η)` is a restart index,
  `c_n < P(η) < c_{n+1}`, and the code of `ι(η)` is `L(n+1) = c_n`;
* `sfEQ_route_fails` (**given (CL)**): for every `n` there are restarts `λ` of the range and `λ'` with
  `c_n < ρ_λ < c_{n+1}`, `B_n(ρ_λ) = ρ_{λ'}` and `Θ_{λ'}(m_{λ'}) ≠ Θ_λ(m_λ)`.  So the equation
  `Θ_{λ'}(m_{λ'}) = Θ_λ(m_λ)` cannot be one of the two halves of EQ^all at the top code; by
  `Sf.sfTheta_move` the right half is `Θ_{λ'}(m_{λ'}) = B_n(Θ_λ(m_λ))` (short codes).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Sf

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bc Googology.Trans.PoR.InaccPsi.R2.Nm

variable {S : InaccSeq.{0}}

/-- The predecessor of a non-restart index above `ω`. -/
theorem sfPred_gen {η : Ordinal.{0}}
    (hown : ConjT.Aη S η ∈ S.CSet (ConjT.Aη S η) (S.psi (ConjT.Aη S η) (Om 1)))
    (hω : (ω : Ordinal.{0}) < Bt.iota S η) (hnr : ¬ IsRestartIdx (Bt.iota S η)) :
    ∃ g, ConjT.Aη S g ∈ S.CSet (ConjT.Aη S g) (S.psi (ConjT.Aη S g) (Om 1)) ∧
      (η = g + 1 ∨ η = g + ω) := by
  have hg' : Bt.Good S η := sfGood_of_own hown
  have h0 : Bt.iota S η ≠ 0 := Order.one_le_iff_ne_zero.1 (Bt.one_le_iota η)
  have hAL : ConjT.Aη S η < S.Lam := sfOwn_lt_Lam hown
  rcases sfRst_cases h0 hnr with ⟨ζ, hζ⟩ | ⟨ζ, hζ⟩
  · have h1 : 1 ≤ ζ := by
      by_contra hh
      push Not at hh
      rw [Order.lt_one_iff.1 hh, zero_add] at hζ
      rw [hζ] at hω
      exact absurd hω (not_lt.2 one_lt_omega0.le)
    obtain ⟨g, hgη, hgg, hgι⟩ := Cd.cd_good_name (S := S) h1 (by rw [hζ]; exact lt_add_one ζ)
    have hogA := sfOwn hgg ((ConjT.A_mono S hgη.le).trans_lt hAL)
    have ho1 := sfOwn_th hogA (ConjT.OmW_le_A S g)
    rw [ConjT.A_succ] at ho1
    exact ⟨g, hogA, Or.inl (Cd.cd_good_inj hg' (sfGood_of_own ho1) (by rw [Bt.iota_good hgg, hgι, hζ]))⟩
  · have h1 : 1 ≤ ζ := by
      by_contra hh
      push Not at hh
      rw [Order.lt_one_iff.1 hh, zero_add] at hζ
      rw [hζ] at hω
      exact lt_irrefl _ hω
    obtain ⟨g, hgη, hgg, hgι⟩ := Cd.cd_good_name (S := S) h1
      (by rw [hζ]; exact lt_add_of_pos_right _ omega0_pos)
    have hogA := sfOwn hgg ((ConjT.A_mono S hgη.le).trans_lt hAL)
    have hoω := sfOwn_omega hogA (ConjT.OmW_le_A S g)
    rw [← Bt.A_add] at hoω
    exact ⟨g, hogA, Or.inr (Cd.cd_good_inj hg' (sfGood_of_own hoω) (by rw [sfIota_omega hogA, hgι, hζ]))⟩

/-- `ω² ∣ ω^x` for `x ≥ 2`. -/
theorem sfWW_dvd_opow {x : Ordinal.{0}} (h : 2 ≤ x) : ω ^ (2 : Ordinal.{0}) ∣ ω ^ x :=
  opow_dvd_opow ω h

theorem sfTwo_le_SC {γ : Ordinal.{0}} (h : SC γ) : (2 : Ordinal.{0}) ≤ γ :=
  ((show (2 : Ordinal.{0}) < ω from by exact_mod_cast natCast_lt_omega0 2).trans
    (Lw.lw_omega_lt_SC h)).le

/-- **The name** `η = Ω_ω + P'·(n+1) + ω^{L(n+1)}`. -/
theorem sfCexName (n : ℕ) :
    let η := Om ω + Nc.ncPp S * ((n + 1 : ℕ) : Ordinal.{0}) + ω ^ Bc.bcC S n
    ConjT.Aη S η ∈ S.CSet (ConjT.Aη S η) (S.psi (ConjT.Aη S η) (Om 1)) ∧
      IsRestartIdx (Bt.iota S η) ∧ Bc.bcC S n < Pv S η ∧ Pv S (η + 1) < Bc.bcC S (n + 1) ∧
      Cd.cdCode S (Bt.iota S η) = Bc.bcC S n := by
  intro η
  set e := Bc.bcC S n with he
  set η0 := Om ω + Nc.ncPp S * ((n + 1 : ℕ) : Ordinal.{0}) with hη0
  have hoα := sfOwn_alpha S n
  have hA0 : ConjT.Aη S η0 = bcAlpha S (n + 1) := (sfAlpha_eq S (n + 1)).symm
  have hAη : ConjT.Aη S η = bcAlpha S (n + 1) + ConjT.th S * ω ^ e := Bt.A_add S η0 _ ▸ by rw [hA0]
  have hθ := sfTh_pos S
  have hθle : ConjT.th S ≤ ConjT.th S * ω ^ e := by
    conv_lhs => rw [← mul_one (ConjT.th S)]
    exact mul_le_mul_right (Order.one_le_iff_ne_zero.2 (opow_pos e omega0_pos).ne') _
  -- `L(n+1) < P(η)`
  have hlt0 : e < S.psi (bcAlpha S (n + 1) + ConjT.th S) (Om 1) := by
    have hm := (psi_mono (S := S) Low.InR_Om_one
      (le_self_add : bcAlpha S (n + 1) ≤ bcAlpha S (n + 1) + ConjT.th S)).2 hoα
    exact psi_lt_psi_of_mem Low.InR_Om_one (lt_add_of_pos_right _ hθ) hm
  have hle1 : S.psi (bcAlpha S (n + 1) + ConjT.th S) (Om 1) ≤ S.psi (ConjT.Aη S η) (Om 1) :=
    (psi_mono (S := S) Low.InR_Om_one (by rw [hAη]; exact (add_le_add_iff_left _).2 hθle)).1
  have hePv : e < Pv S η := lt_of_lt_of_le hlt0 hle1
  -- own
  have hWα : Om ω < bcAlpha S (n + 1) := by
    unfold bcAlpha
    exact lt_of_lt_of_le (lt_add_of_pos_right _ (Om_pos omega0_ne_zero)) le_self_add
  have hown : ConjT.Aη S η ∈ S.CSet (ConjT.Aη S η) (S.psi (ConjT.Aη S η) (Om 1)) := by
    have hle : bcAlpha S (n + 1) ≤ ConjT.Aη S η := by rw [hAη]; exact le_self_add
    have h1 := (psi_mono (S := S) Low.InR_Om_one hle).2 hoα
    have h2 : ConjT.th S * ω ^ e ∈ S.CSet (ConjT.Aη S η) (S.psi (ConjT.Aη S η) (Om 1)) := by
      have ee : ConjT.th S * ω ^ e = veblen 0 (ConjT.th S + e) := by
        rw [veblen_zero_apply, opow_add, sfTh_opow]
      rw [ee]
      exact CSet.phi_mem (CSet.zero_mem _ _) (CSet.add_mem (ConjT.th_mem S (hWα.trans_le hle))
        (CSet.of_lt hePv))
    rw [hAη] at h1 h2 ⊢
    exact CSet.add_mem h1 h2
  have hg := sfGood_of_own hown
  -- below `L(n+2)`
  have hoα2 := sfOwn_alpha S (n + 1)
  have hown1 := sfOwn_th hown (ConjT.OmW_le_A S η)
  rw [ConjT.A_succ] at hown1
  have hP := (Nc.ncPp_SC S).isPrincipal
  have hθP := Nc.ncTh_lt_Pp S
  have heP : e < Nc.ncPp S :=
    (show e < Om 1 from InaccSeq.psi_lt Low.InR_Om_one _).trans (Lw.lw_Om1_lt_Pp S)
  have hθeP : ConjT.th S * ω ^ e < Nc.ncPp S := by
    rw [← sfTh_opow S, ← opow_add, ← Lw.lw_Pp_opow S]
    exact (opow_lt_opow_iff_right one_lt_omega0).2 (hP hθP heP)
  have hA1lt : ConjT.Aη S (η + 1) < bcAlpha S (n + 1 + 1) := by
    rw [← ConjT.A_succ, hAη]
    have hα : bcAlpha S (n + 1 + 1) = bcAlpha S (n + 1) + Nc.ncPp S := by
      unfold bcAlpha
      rw [Nat.cast_succ (n + 1), mul_add_one]
      simp only [add_assoc]
    rw [hα, add_assoc]
    exact (add_lt_add_iff_left _).2 (hP hθeP hθP)
  have hhi : Pv S (η + 1) < Bc.bcC S (n + 1) := by
    have hc := compare_psi Low.InR_Om_one hown1 hoα2
    rw [compare_lt_iff_lt.2 hA1lt] at hc
    exact compare_lt_iff_lt.1 hc
  -- the restart
  have hlam := Pp.ppIota_succ_restart (S := S) n
  have hιle : Bt.iota S η0 ≤ Bt.iota S η := Bt.iota_mono _ _ le_self_add
  have hω : (ω : Ordinal.{0}) < Bt.iota S η := by
    have hww : ω * ω ≤ Bt.iota S η0 := Ordinal.le_of_dvd hlam.1 (ri_iff.1 hlam).2
    refine lt_of_lt_of_le ?_ (hww.trans hιle)
    exact lt_of_lt_of_le (lt_mul_of_one_lt_right omega0_pos one_lt_omega0) le_rfl
  have hdvd : ω ^ (2 : Ordinal.{0}) ∣ η := by
    refine dvd_add (dvd_add ?_ ?_) (sfWW_dvd_opow (sfTwo_le_SC (Lw.lw_L_SC S _)))
    · rw [← Low.opow_eq_self_of_SC (SC_Om omega0_ne_zero)]
      exact sfWW_dvd_opow (sfTwo_le_SC (SC_Om omega0_ne_zero))
    · rw [← Lw.lw_Pp_opow S]
      exact dvd_mul_of_dvd_left (sfWW_dvd_opow (sfTwo_le_SC (Nc.ncPp_SC S))) _
  have hη0' : η ≠ 0 := by
    have : (0 : Ordinal.{0}) < η :=
      lt_of_lt_of_le (Om_pos omega0_ne_zero) (le_self_add.trans le_self_add)
    exact this.ne'
  have hrst : IsRestartIdx (Bt.iota S η) := by
    by_contra hnr
    obtain ⟨g, -, hcase⟩ := sfPred_gen hown hω hnr
    rcases hcase with h | h
    · have hωd : ω ∣ η := by
        have := (opow_dvd_opow ω (show (1 : Ordinal.{0}) ≤ 2 by norm_num)).trans hdvd
        rwa [opow_one] at this
      have hl : IsSuccPrelimit η := isSuccPrelimit_iff_omega0_dvd.2 hωd
      rw [h, ← Order.succ_eq_add_one] at hl
      exact Order.not_isSuccPrelimit_succ g hl
    · have hww : ω ^ (2 : Ordinal.{0}) = ω * ω := by
        rw [show (2 : Ordinal.{0}) = 1 + 1 by norm_num, opow_add, opow_one]
      exact sfNotRst_omega g (h ▸ ri_iff.2 ⟨hη0', hww ▸ hdvd⟩)
  -- the code
  have hcode : Cd.cdCode S (Bt.iota S η) = e := by
    unfold Cd.cdCode
    rw [Cd.cdEta_unique hg rfl]
    have hx : Cd.cdExp η = e := sfCdExp_any η0 e
    have hinf : ¬ e < ω := not_lt.2 (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)).le
    have he2 : e < Om (1 + 1) := (show e < Om 1 from InaccSeq.psi_lt Low.InR_Om_one _).trans
      (Om_lt_Om.2 (by norm_num))
    rw [Cd.cdCodeOf_of_lt (hx ▸ he2), hx]
    unfold Cd.cdOff
    rw [if_neg hinf]
  exact ⟨hown, hrst, hePv, hhi, hcode⟩

/-- **Given (CL), the reading of the code is not invariant under `B_n` at some range restart of every
window.** -/
theorem sfEQ_route_fails (hC : Cd.CdCL S) (n : ℕ) :
    ∃ l l', Cd.CdRange S l ∧ Bc.bcC S n < upsilon l ∧ upsilon l < Bc.bcC S (n + 1) ∧
      IsRestartIdx l' ∧ Bc.bcB S n (upsilon l) = upsilon l' ∧
      Cd.cdTheta S l' (Cd.cdCode S l') ≠ Cd.cdTheta S l (Cd.cdCode S l) := by
  obtain ⟨-, hrst, h1, h2, hcode⟩ := sfCexName (S := S) n
  set η := Om ω + Nc.ncPp S * ((n + 1 : ℕ) : Ordinal.{0}) + ω ^ Bc.bcC S n with hη
  have hpv : Pv S η = upsilon (Bt.iota S η) := (Bt.ups_iota S η).symm
  have hυ1 : Bc.bcC S n < upsilon (Bt.iota S η) := hpv ▸ h1
  have hυ2 : upsilon (Bt.iota S η) < Bc.bcC S (n + 1) := hpv ▸ (Pv_mono le_self_add).trans_lt h2
  obtain ⟨μ', hμ', hB⟩ := sfRstMove n (Bt.iota S η) hrst hυ1.le hυ2
  refine ⟨Bt.iota S η, μ', Tp.tpRange_win hC hrst hυ1 hυ2, hυ1, hυ2, hμ', hB, ?_⟩
  exact sfTheta_ne hrst.1 hυ1 hυ2 hB (by rw [hcode]; exact hυ1.le) (by rw [hcode])

end Googology.Trans.PoR.InaccPsi.R2.Sf
