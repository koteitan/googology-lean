import Googology.Trans.PoR.InaccPsi.R2.SfLh

/-!
# How `B_n` moves the codes: `m_{λ'} = B_n(m_λ)` and `Θ_{λ'}(m_{λ'}) = B_n(Θ_λ(m_λ))` for short codes

`θ = ψ_{Ω₂}(Ω_ω)`, `A_η = Ω_ω + θ·η`, `P(η) = ψ_{Ω₁}(A_η)`, `L(ξ) = ψ_{Ω₁}(Ω_ω·2 + P'·ξ)`,
`c_n = L(n+1)`, `B_n = Bc.bcB S n`, `σ = bcSig (bcPre (n+1)) bcPreW`.  For a restart `λ`, `η_λ` is its
name (`Cd.cdEta`), `m_λ = -1 + cdExp(η_λ)` its code (`Cd.cdCode`), `Θ_λ` the reading (`Cd.cdTheta`);
`λ'` is the restart with `B_n(ρ_λ) = ρ_{λ'}`.

* `sfCdExp_add`, `sfCdExp_th`: `cdExp(X + ζ) = cdExp ζ` and `cdExp(θ·ζ) = θ + cdExp ζ` for `ζ ≠ 0`;
* `sfLast_shape`: a normal form of `ω^{θ+e}` (`0 < e < L(ω)`) is `φ(0, θ + e)` with `θ + e` the chain
  `θ + nf(e)`, so `σ` sends it to `φ(0, θ + σ(nf e))`, of value `ω^{θ + B_n(e)}`;
* `sfExp_move` (**the last exponent moves by `B_n`**): at a restart `λ` with `c_n < ρ_λ < c_{n+1}` and
  `e = cdExp(η_λ) < L(ω)`: `cdExp(η_{λ'}) = B_n(e)`;
* `sfTheta_move` (**short codes**): if moreover `m_λ ≤ ρ_λ`, then `m_{λ'} = B_n(m_λ)` and
  `Θ_{λ'}(m_{λ'}) = B_n(Θ_λ(m_λ))`;
* `sfTheta_ne`: **so `Θ_{λ'}(m_{λ'}) ≠ Θ_λ(m_λ)` when `c_n ≤ m_λ ≤ ρ_λ`**: the reading of the code is not
  invariant under `B_n`; the reach equation `B_n r(λ) = r(λ')` must use `k_{λ'}(B_n p) = B_n(k_λ(p))`,
  not `k_{λ'}(p) = B_n(k_λ(p))`.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Sf

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Notation.InaccPsi.Term Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Bc Googology.Trans.PoR.InaccPsi.R2.Nm

variable {S : InaccSeq.{0}}

/-! ## Last exponents -/

theorem sfCdExp_add (X : Ordinal.{0}) {ζ : Ordinal.{0}} (hζ : ζ ≠ 0) :
    Cd.cdExp (X + ζ) = Cd.cdExp ζ := by
  obtain ⟨ζ0, hζ0, -⟩ := Cd.cdExp_decomp hζ
  rw [hζ0, ← add_assoc, sfCdExp_any, sfCdExp_any]

theorem sfCdExp_th (S : InaccSeq.{0}) {ζ : Ordinal.{0}} (hζ : ζ ≠ 0) :
    Cd.cdExp (ConjT.th S * ζ) = ConjT.th S + Cd.cdExp ζ := by
  obtain ⟨ζ0, hζ0, -⟩ := Cd.cdExp_decomp hζ
  generalize hE : Cd.cdExp ζ = E at hζ0 ⊢
  rw [hζ0, mul_add]
  have : ConjT.th S * ω ^ E = ω ^ (ConjT.th S + E) := by rw [opow_add, sfTh_opow]
  rw [this, sfCdExp_any]

/-- The last exponent of the value of a nonzero normal chain is the exponent of its last summand. -/
theorem sfCdExp_last {t : Term} (hN : NF t) {g : Ordinal.{0}}
    (hg : val S (sfLast t) = ω ^ g) : Cd.cdExp (val S t) = g := by
  rw [sfInit_val (S := S) hN, hg]
  exact sfCdExp (sfInit_dvd hN hg)

/-! ## The shape of the last summand -/

/-- **A normal form of `ω^{θ+e}`** (`0 < e < L(ω)`) is `φ(0, θ + nf(e))`. -/
theorem sfLast_shape {p : Term} (hp : NF p) {e : Ordinal.{0}} (he0 : e ≠ 0)
    (heL : e < Nc.ncL S ω) (hv : val S p = ω ^ (ConjT.th S + e)) :
    p = phi Term.zero (add sfThT (bcNf S e)) := by
  have hθ := sfTh_pos S
  -- `θ + e` is not an ε-number
  have heθ : e < ConjT.th S :=
    heL.trans ((show Nc.ncL S ω < Om 1 from InaccSeq.psi_lt Low.InR_Om_one _).trans
      (psiS_bounds (S := S) (Om ω) 1).1)
  have hne : ω ^ (ConjT.th S + e) ≠ ConjT.th S + e := by
    intro h
    have h1 : ConjT.th S * ω ≤ ω ^ (ConjT.th S + e) := by
      rw [opow_add, sfTh_opow S]
      have hωe : (ω : Ordinal.{0}) ≤ ω ^ e := by
        have := (opow_le_opow_iff_right one_lt_omega0).2 (Order.one_le_iff_ne_zero.2 he0)
        rwa [opow_one] at this
      exact mul_le_mul_right hωe _
    have h2 : ConjT.th S + e < ConjT.th S * ω := by
      calc ConjT.th S + e < ConjT.th S + ConjT.th S := (add_lt_add_iff_left _).2 heθ
        _ = ConjT.th S * 2 := by
          rw [show (2 : Ordinal.{0}) = 1 + 1 by norm_num, mul_add, mul_one]
        _ < ConjT.th S * ω := (mul_lt_mul_iff_right₀ hθ).2 (by exact_mod_cast natCast_lt_omega0 2)
    rw [h] at h1
    exact absurd h2 (not_lt.2 h1)
  have hmemE : ∀ {v : Ordinal.{0}}, v = ω ^ (ConjT.th S + e) → ω ^ v = v → False := by
    intro v hv' hE
    rw [hv'] at hE
    exact hne ((opow_right_inj one_lt_omega0).1 hE)
  have hSC : ¬ SC (val S p) := fun hs => hmemE hv (Low.opow_eq_self_of_SC hs)
  -- the term of `θ + e`
  have hmem : e ∈ ⋃ a, S.CSet a 0 := by
    rw [ncL_omega_eq] at heL; exact mem_of_lt_psi S heL
  obtain ⟨hNe, hve⟩ := bcNf_spec S hmem
  have hne0 : bcNf S e ≠ Term.zero := fun h => he0 (by rw [← hve, h]; rfl)
  have hNY : NF (add sfThT (bcNf S e)) := by
    refine ⟨sfThT_NF, hNe, rfl, hne0, ?_⟩
    have := cmp_lt_of_val S hNe.head sfThT_NF
      (by rw [sfThT_val]; exact lt_of_le_of_lt (val_head_le S hNe) (by rw [hve]; exact heθ))
    rw [this]; simp
  cases p with
  | zero => exact absurd hv (opow_pos (ConjT.th S + e) omega0_pos).ne
  | add a b =>
    exfalso
    have hI : Indec (val S (Term.add a b)) := by
      rw [hv]
      exact indec_iff.2 ⟨(opow_pos _ omega0_pos).ne', isPrincipal_add_omega0_opow _⟩
    have := isPrin_of_indec hp hI
    simp [isPrin, isSC] at this
  | inacc m => exact absurd (SC_val S hp rfl) hSC
  | inaccW => exact absurd (SC_val S hp rfl) hSC
  | om a => exact absurd (SC_val S hp rfl) hSC
  | psiS s a => exact absurd (SC_val S hp rfl) hSC
  | psiI m a => exact absurd (SC_val S hp rfl) hSC
  | phi c d =>
    by_cases hc : c = Term.zero
    · subst hc
      have hvd : val S d = ConjT.th S + e := by
        simp only [val, veblen_zero] at hv
        exact (opow_right_inj one_lt_omega0).1 hv
      have : d = add sfThT (bcNf S e) :=
        eq_of_val_eq S hp.2.1 hNY (by rw [hvd]; show _ = val S sfThT + val S (bcNf S e); rw [sfThT_val, hve])
      rw [this]
    · exfalso
      have hpos : 0 < val S c := pos_iff_ne_zero.2 (val_ne_zero S hp.1 hc)
      exact hmemE hv (Tp.tpVeblen_fix hpos)

/-! ## The last exponent of the image name -/

/-- **The last exponent moves by `B_n`.** -/
theorem sfExp_move {n : ℕ} {l : Ordinal.{0}} (hl0 : l ≠ 0) (h1 : Bc.bcC S n < upsilon l)
    (h2 : upsilon l < Bc.bcC S (n + 1)) (heL : Cd.cdExp (Cd.cdEta S l) < Nc.ncL S ω) :
    ∃ η', Bt.Good S η' ∧ Bc.bcB S n (upsilon l) = upsilon (Bt.iota S η') ∧
      Cd.cdEta S (Bt.iota S η') = η' ∧
      Cd.cdExp η' = Bc.bcB S n (Cd.cdExp (Cd.cdEta S l)) := by
  have hL : Bc.bcC S (n + 1) = Pv S (Om ω + Nc.ncPp S * ((n + 1 + 1 : ℕ) : Ordinal.{0})) :=
    Lw.lw_L_eq S _
  obtain ⟨hg, -, -, hpv⟩ := Cd.cdEta_pv_spec (S := S) hl0 (hL ▸ h2)
  set η := Cd.cdEta S l with hη
  rw [← hpv] at h1 h2 ⊢
  obtain ⟨ρ, hD, -, -, hAη, hdρ, hB, hNT⟩ := sfData hg h1.le h2
  obtain ⟨ζ, hζ⟩ := hdρ
  obtain ⟨ζ', hζ'⟩ := sfSig_dvd n hD ⟨ζ, hζ⟩
  -- the source name
  have hηe : η = Om ω + Nc.ncPp S * ((n + 1 : ℕ) : Ordinal.{0}) + ζ := by
    refine sfA_inj (S := S) ?_
    rw [hAη, hζ, Bt.A_add, ← sfAlpha_eq]
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [add_zero] at hηe
    have : Pv S η = Bc.bcC S n := by rw [hηe, ← Lw.lw_L_eq]; rfl
    exact absurd h1 (by rw [this]; exact lt_irrefl _)
  have hρ0 : ρ ≠ Term.zero := by
    rintro rfl
    have : ConjT.th S * ζ = 0 := by rw [← hζ]; rfl
    exact hζ0 ((mul_eq_zero.1 this).resolve_left (sfTh_pos S).ne')
  have hexp : Cd.cdExp η = Cd.cdExp ζ := by rw [hηe]; exact sfCdExp_add _ hζ0
  -- the last summand of `ρ`
  have hlast : val S (sfLast ρ) = ω ^ (ConjT.th S + Cd.cdExp ζ) := by
    have hd := Cd.cdExp_dvd (mul_ne_zero (sfTh_pos S).ne' hζ0)
    obtain ⟨Y, hY, -⟩ := Cd.cdExp_decomp (mul_ne_zero (sfTh_pos S).ne' hζ0)
    rw [sfCdExp_th S hζ0] at hY
    exact sfLast_val hD.1 hρ0 (by rw [hζ]; exact hY)
  have hlN : NF (sfLast ρ) := NF_of_sub (sfLast_sub ρ) hD.1
  have hσl : val S (sfLast (bcSig (bcPre (n + 1)) bcPreW ρ)) =
      ω ^ (ConjT.th S + Bc.bcB S n (Cd.cdExp ζ)) := by
    rcases eq_or_ne (Cd.cdExp ζ) 0 with h0 | h0
    · have hθv : val S (sfLast ρ) = val S sfThT := by
        rw [hlast, h0, add_zero, sfThT_val, sfTh_opow]
      have e1 := eq_of_val_eq S hlN sfThT_NF hθv
      rw [sfLast_sig, e1, bcSig_free sfThT_free, sfThT_val, h0, Bc.bcB_zero, add_zero, sfTh_opow]
    · have hshape := sfLast_shape hlN h0 (hexp ▸ heL) hlast
      rw [sfLast_sig, hshape, bcSig_phi, bcSig_zero, bcSig_add, bcSig_free sfThT_free]
      show veblen 0 (val S sfThT + val S (bcSig (bcPre (n + 1)) bcPreW (bcNf S (Cd.cdExp ζ)))) = _
      rw [veblen_zero, sfThT_val]
      rfl
  have hσN := bc_NF (k := n) hD
  have hσ0 : bcSig (bcPre (n + 1)) bcPreW ρ ≠ Term.zero := bcSig_ne_zero hρ0
  have hζ'0 : ζ' ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hζ'
    exact val_ne_zero S hσN hσ0 hζ'
  have hexp' : Cd.cdExp ζ' = Bc.bcB S n (Cd.cdExp ζ) := by
    have c1 := sfCdExp_last hσN hσl
    rw [hζ', sfCdExp_th S hζ'0] at c1
    exact add_left_cancel c1
  -- the target name
  set η' := Om ω + Nc.ncPp S * ω + ζ' with hη'
  have hAη' : ConjT.Aη S η' = bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW ρ) := by
    rw [hη', Bt.A_add, ← sfAlphaW_eq, hζ']
  have hown' : ConjT.Aη S η' ∈ S.CSet (ConjT.Aη S η') (S.psi (ConjT.Aη S η') (Om 1)) := by
    have hsem : Sem S (psiS Term.zero (bcApp bcPreW (bcSig (bcPre (n + 1)) bcPreW ρ))) :=
      sem_of_NF hNT
    have h2 := hsem.2.2
    rw [show Om (val S Term.zero + 1) = Om 1 by rw [show val S Term.zero = 0 from rfl, zero_add],
      val_bcApp_preW, ← hAη'] at h2
    exact h2
  have hg' := sfGood_of_own hown'
  refine ⟨η', hg', ?_, Cd.cdEta_unique hg' rfl, ?_⟩
  · rw [hB, Bt.ups_iota S η', hAη']
  · rw [hη', sfCdExp_add _ hζ'0, hexp', hexp]

/-! ## Short codes -/

theorem sfOff_B {n : ℕ} {e : Ordinal.{0}} (he : e < Bc.bcC S (n + 1)) :
    Cd.cdOff (Bc.bcB S n e) = Bc.bcB S n (Cd.cdOff e) := by
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Qq.qqL_lt_omega S (n + 1 + 1)
  have hωC : (ω : Ordinal.{0}) < Bc.bcC S n :=
    (show (ω : Ordinal.{0}) < Bc.bcC S n from Lw.lw_omega_lt_SC (Lw.lw_L_SC S _))
  by_cases hf : e < ω
  · have hfix : Bc.bcB S n e = e := Bc.bcB_fix (hf.trans hωC)
    unfold Cd.cdOff
    rw [hfix, if_pos hf, Bc.bcB_fix (lt_of_le_of_lt (Ordinal.sub_le_self _ _) (hf.trans hωC))]
  · have hge : ω ≤ Bc.bcB S n e := by
      rw [← Bc.bcB_fix (S := S) (k := n) (hωC)]
      rcases eq_or_lt_of_le (not_lt.1 hf) with h | h
      · rw [← h]
      · exact ((Bc.bcB_lt_iff (hωC.trans (Qq.qqL_lt_omega S (n + 1))) (he.trans hLw)).2 h).le
    unfold Cd.cdOff
    rw [if_neg hf, if_neg (not_lt.2 hge)]

/-- **Short codes move by `B_n`**: `m_{λ'} = B_n(m_λ)` and `Θ_{λ'}(m_{λ'}) = B_n(Θ_λ(m_λ))`. -/
theorem sfTheta_move {n : ℕ} {l l' : Ordinal.{0}} (hl0 : l ≠ 0) (h1 : Bc.bcC S n < upsilon l)
    (h2 : upsilon l < Bc.bcC S (n + 1)) (hB : Bc.bcB S n (upsilon l) = upsilon l')
    (hm : Cd.cdCode S l ≤ upsilon l) :
    Cd.cdCode S l' = Bc.bcB S n (Cd.cdCode S l) ∧
      Cd.cdTheta S l' (Cd.cdCode S l') = Bc.bcB S n (Cd.cdTheta S l (Cd.cdCode S l)) := by
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Qq.qqL_lt_omega S (n + 1 + 1)
  have hΩ2 : Nc.ncL S ω < Om (1 + 1) :=
    (InaccSeq.psi_lt Low.InR_Om_one _).trans (Om_lt_Om.2 (by norm_num))
  set e := Cd.cdExp (Cd.cdEta S l) with he
  -- the code is `cdOff e`, and `e` is below `c_{n+1}`
  have hcode : Cd.cdCode S l = Cd.cdOff e := by
    unfold Cd.cdCode
    by_cases h : e < Om (1 + 1)
    · exact Cd.cdCodeOf_of_lt h
    · exfalso
      unfold Cd.cdCode Cd.cdCodeOf at hm
      rw [if_neg h] at hm
      have : Om (1 : Ordinal.{0}) ≤ Cd.cdPi S (Cd.cdEta S l) := by
        unfold Cd.cdPi
        exact (psiS_bounds (S := S) _ 1).1.le
      exact absurd (this.trans hm) (not_le.2 ((h2.trans hLw).trans (InaccSeq.psi_lt Low.InR_Om_one _)))
  have heC : e < Bc.bcC S (n + 1) := by
    by_cases hf : e < ω
    · exact hf.trans (show (ω : Ordinal.{0}) < Bc.bcC S (n + 1) from Lw.lw_omega_lt_SC (Lw.lw_L_SC S _))
    · have : Cd.cdOff e = e := by unfold Cd.cdOff; rw [if_neg hf]
      rw [← this, ← hcode]; exact hm.trans_lt h2
  obtain ⟨η', hg', hBη', hη', hexp'⟩ := sfExp_move hl0 h1 h2 (heC.trans hLw)
  have hl' : l' = Bt.iota S η' := Tp.tpUps_inj (hB.symm.trans hBη')
  subst hl'
  have hcode' : Cd.cdCode S (Bt.iota S η') = Bc.bcB S n (Cd.cdCode S l) := by
    have hB' : Bc.bcB S n e < Om (1 + 1) :=
      (Bc.bcB_bound n e heC).trans ((InaccSeq.psi_lt Low.InR_Om_one _).trans (Om_lt_Om.2 (by norm_num)))
    show Cd.cdCodeOf S (Cd.cdEta S (Bt.iota S η')) = _
    rw [hη', Cd.cdCodeOf_of_lt (hexp' ▸ hB'), hexp', hcode, sfOff_B heC]
  refine ⟨hcode', ?_⟩
  have hmL : Cd.cdCode S l < Nc.ncL S ω := hm.trans_lt (h2.trans hLw)
  have hρL : upsilon l < Nc.ncL S ω := h2.trans hLw
  have hm' : Cd.cdCode S (Bt.iota S η') ≤ upsilon (Bt.iota S η') := by
    rw [hcode', ← hBη']
    rcases eq_or_lt_of_le hm with h | h
    · rw [h]
    · exact ((Bc.bcB_lt_iff hmL hρL).2 h).le
  rw [Cd.cdTheta_small S hm', Cd.cdTheta_small S hm, hcode']

/-- **The reading of a code is not invariant under `B_n`** once `c_n ≤ m_λ ≤ ρ_λ`. -/
theorem sfTheta_ne {n : ℕ} {l l' : Ordinal.{0}} (hl0 : l ≠ 0) (h1 : Bc.bcC S n < upsilon l)
    (h2 : upsilon l < Bc.bcC S (n + 1)) (hB : Bc.bcB S n (upsilon l) = upsilon l')
    (hm : Cd.cdCode S l ≤ upsilon l) (hc : Bc.bcC S n ≤ Cd.cdCode S l) :
    Cd.cdTheta S l' (Cd.cdCode S l') ≠ Cd.cdTheta S l (Cd.cdCode S l) := by
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Qq.qqL_lt_omega S (n + 1 + 1)
  obtain ⟨-, hΘ⟩ := sfTheta_move hl0 h1 h2 hB hm
  rw [hΘ, Cd.cdTheta_small S hm]
  intro h
  have hmL : Cd.cdCode S l < Nc.ncL S ω := hm.trans_lt (h2.trans hLw)
  have hge : Nc.ncL S ω ≤ Bc.bcB S n (Cd.cdCode S l) := by
    rw [← Bc.bcB_base (S := S) n]
    rcases eq_or_lt_of_le hc with e | hlt
    · rw [← e]; rfl
    · exact ((Bc.bcB_lt_iff (Qq.qqL_lt_omega S (n + 1)) hmL).2 hlt).le
  rw [h] at hge
  exact absurd hge (not_le.2 hmL)

end Googology.Trans.PoR.InaccPsi.R2.Sf
