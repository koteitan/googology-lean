import Googology.Trans.PoR.InaccPsi.R2.RbTh

/-!
# `B_n(lhᵗ(x)) = lh^{τ'}(B_n x)` at every strongly critical `x` that is not a fixed point of `Γ_`

`B_n = Bc.bcB S n`, `c_n = L(n+1) = Bc.bcC S n`, `τ = υ_ξ`, `τ' = υ_{ξ'} = B_n τ`, `lhᵗ = lhT τ`,
`PREM(n, ξ, ξ', x)` the premises of `Sf.SfLhTMove`, `Γ_ = Ordinal.gamma`, `ψ = S.psi`.

* `rbLhT_nonfix` (**the move at every strongly critical `x` with a fixed point of `Γ_` in `(τ, x]` that is not itself a
  fixed point**): `p` the largest fixed point below `x` (`rb_base_below`), `x = Γ_{p+1+δ} = ψ_{Ω₁}(B_p + 1 + δ)`
  (`Lq.lq_psi_gamma_of`, `B_p` the own argument of `p`, `Ω₁ ∣ B_p` by `rbDvd_of_fix`), `x = ϑᵗ(Ω₁·Ω₁ + (p + δ))`
  (`rb_sq_enum_fix`), `lhᵗ(x) = x·x + x + ζ` with `ζ = 0` (`δ = 0`) or `logend(p + δ)` (`Lq.lq_lh_sq`, from the cited
  `R2.CitedLq`); `B_n x = ψ_{Ω₁}(B' + 1 + B_n δ)` with `B_n p = ψ_{Ω₁}(B')` (`rbB_psi_base`), `Ω₁ ∣ B'` (`rbB_dvd`), so
  `B_n p` is a fixed point (`rbFix_of_dvd`), `B_n x = Γ_{B_n p+1+B_n δ} = ϑ^{τ'}(Ω₁·Ω₁ + B_n(p + δ))`, and `B_n` keeps
  `·`, `+`, `logend`;
* `RbLhTopFix S` (a hypothesis name): `Lq.MqLhTopF` at the fixed points `x = Γ_x` only; `rbLhTopF` (**`RbLhTopFix` gives
  `Lq.MqLhTopF`**), `rbLhTopFix_of` (the converse), `rbSfLhT` (**`RbLhTopFix` gives `Sf.SfLhTMove`**),
  `rbRoad` (the road `Lq.lqRoad` with `RbLhTopFix` in place of `Lq.MqLhTopF`).

No new axiom.  New definition: the hypothesis name `RbLhTopFix`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Rb

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Lq Googology.Trans.PoR.InaccPsi.R2.Lu
  Googology.Trans.PoR.InaccPsi.R2.Lt
  Googology.Notation.InaccPsi.Term Googology.Trans.PoR.InaccPsi.R2.Bc

variable {S : InaccSeq.{0}}

/-- **`B_n(lhᵗ(x)) = lh^{τ'}(B_n x)`** at every strongly critical `x` with `PREM(n, ξ, ξ', x)` and a fixed point of `Γ_`
in `(τ, x]` that is not itself a fixed point of `Γ_`. -/
theorem rbLhT_nonfix {n : ℕ} {ξ ξ' x : Ordinal.{0}} (hc : Bc.bcC S n ≤ upsilon ξ) (hτx : upsilon ξ < x)
    (hx2 : x < upsilon (ξ + 1)) (hξ1lt : upsilon (ξ + 1) < Bc.bcC S (n + 1)) (hE : InE x)
    (hBξ : Bc.bcB S n (upsilon ξ) = upsilon ξ')
    (hBξ1 : Bc.bcB S n (upsilon (ξ + 1)) = upsilon (ξ' + 1))
    (hxSC : SC x) (hq : ∃ q, gamma q = q ∧ upsilon ξ < q ∧ q ≤ x) (hnf : gamma x ≠ x) :
    Bc.bcB S n (lhT (upsilon ξ) x) = lhT (upsilon ξ') (Bc.bcB S n x) := by
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Qq.qqL_lt_omega S (n + 1 + 1)
  have hxX : x < Bc.bcC S (n + 1) := hx2.trans hξ1lt
  have hxL : x < Nc.ncL S ω := hxX.trans hLw
  have hτL : upsilon ξ < Nc.ncL S ω := hτx.trans hxL
  have hωC : (ω : Ordinal.{0}) < Bc.bcC S n := Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)
  have h1C : (1 : Ordinal.{0}) < Bc.bcC S n := one_lt_omega0.trans hωC
  have hOm : Nc.ncL S ω < Om1 := by rw [Br.Om1_eq]; exact InaccSeq.psi_lt Low.InR_Om_one _
  have hξ0 : ξ ≠ 0 := by
    rintro rfl
    rw [upsilon_zero] at hc
    exact absurd (lt_of_lt_of_le (zero_lt_one.trans h1C) hc) (lt_irrefl _)
  have hLω : Nc.ncL S ω ≤ Bc.bcB S n (upsilon ξ) := by
    rw [← Bc.bcB_base (S := S) n]
    rcases eq_or_lt_of_le hc with e | hlt
    · rw [← e]; exact le_rfl
    · exact ((Bc.bcB_lt_iff (Qq.qqL_lt_omega S (n + 1)) hτL).2 hlt).le
  have hξ'0 : ξ' ≠ 0 := by
    rintro rfl
    rw [hBξ, upsilon_zero] at hLω
    exact absurd (lt_of_lt_of_le (Lw.lw_L_SC S ω).1 hLω) (lt_irrefl _)
  have hτ'L1 : upsilon ξ' < Nm.Pv S (Om ω + Nc.ncPp S * (ω + 1)) := by
    rw [← Lw.lw_L_eq S, ← hBξ]; exact Bc.bcB_bound' S n _ (hτx.trans hxX)
  have hτSC : SC (upsilon ξ) := mvUps_SC hξ0 (show upsilon ξ < Nm.Pv S (Om ω + Nc.ncPp S * ω) by
    rw [← Lw.lw_L_eq S]; exact hτL)
  have hτ'SC : SC (upsilon ξ') := mvUps_SC hξ'0 hτ'L1
  have hτ1 : upsilon ξ < Om1 := hτL.trans hOm
  have hτ'1 : upsilon ξ' < Om1 := by rw [Br.Om1_eq]; exact hτ'L1.trans (Nm.Pv_lt_Om1 S _)
  have hu1 : upsilon (ξ + 1) < Om1 := (hξ1lt.trans hLw).trans hOm
  have hu1' : upsilon (ξ' + 1) < Om1 := by
    rw [← hBξ1, Br.Om1_eq]
    exact (Bc.bcB_bound n _ hξ1lt).trans (InaccSeq.psi_lt Low.InR_Om_one _)
  have hTm : ∀ a, a < upsilon (ξ + 1) → a ∈ Tset (upsilon ξ) := by
    intro a ha
    have h := upsilon_succ_T ξ (by rw [succ_eq_add_one]; exact hu1) a (ha.trans hu1)
    rw [if_neg hξ0] at h
    exact h.2 (by rw [succ_eq_add_one]; exact ha)
  have hTm' : ∀ a, a < upsilon (ξ' + 1) → a ∈ Tset (upsilon ξ') := by
    intro a ha
    have h := upsilon_succ_T ξ' (by rw [succ_eq_add_one]; exact hu1') a (ha.trans hu1')
    rw [if_neg hξ'0] at h
    exact h.2 (by rw [succ_eq_add_one]; exact ha)
  have hτE : InE (upsilon ξ) := Gg.gg_SC_eps hτSC
  have hτ'E : InE (upsilon ξ') := Gg.gg_SC_eps hτ'SC
  have hhi' : Bc.bcB S n x < upsilon (ξ' + 1) := by
    rw [← hBξ1]; exact (Bc.bcB_lt_iff hxL (hξ1lt.trans hLw)).2 hx2
  have hxx : x * x < Nc.ncL S ω := by
    have hE' : ω ^ x = x := hE
    have e : x * x = ω ^ (x + x) := by rw [opow_add, hE']
    rw [e]
    have := (Lw.lw_L_SC S ω).2 0 (Lw.lw_L_SC S ω).1 (x + x) ((Lw.lw_L_SC S ω).isPrincipal hxL hxL)
    rwa [veblen_zero_apply] at this
  have h1L : (1 : Ordinal.{0}) < Nc.ncL S ω := by
    have := mw_nat_lt_L (S := S) 1; rwa [Nat.cast_one] at this
  have hLSC := Lw.lw_L_SC S ω
  -- the largest fixed point `p` below `x`
  obtain ⟨y, hy⟩ := lq_SC_gamma hxSC
  have hyx : y < x := by
    refine lt_of_le_of_ne (hy ▸ lq_le_gamma y) fun e => hnf ?_
    rw [← e] at hy ⊢; rw [hy]
  obtain ⟨p, hbase, hpx, hmax⟩ := rb_base_below hτx hnf
  obtain ⟨q, hqq, hτq, hqx⟩ := hq
  have hqx' : q < x := lt_of_le_of_ne hqx fun e => hnf (e ▸ hqq)
  have hqp : q ≤ p := hmax q hqq hτq hqx'
  obtain ⟨hτp, hpp⟩ : upsilon ξ < p ∧ gamma p = p := by
    rcases hbase with e | h
    · exact absurd (hτq.trans_le (e ▸ hqp)) (lt_irrefl _)
    · exact h
  have hpSC : SC p := hpp ▸ lq_gamma_SC p
  have hpL : p < Nc.ncL S ω := hpx.trans hxL
  have hnofix : ∀ z, p < z → z < x → z < gamma z := by
    intro z hpz hzx
    by_contra h
    push Not at h
    have hz := le_antisymm h (lq_le_gamma z)
    exact absurd (hmax z hz (hτp.trans hpz) hzx) (not_le.2 hpz)
  have hpy : p < y := gamma_lt_gamma.1 (by rw [hpp, hy]; exact hpx)
  set D := y - p with hDdef
  have hpD : p + D = y := Ordinal.add_sub_cancel_of_le hpy.le
  have hD0 : D ≠ 0 := by
    rintro h0; rw [h0, add_zero] at hpD; exact absurd hpD hpy.ne
  have h1D : 1 ≤ D := one_le_iff_ne_zero.2 hD0
  set δ := D - 1 with hδdef
  have hδ : 1 + δ = D := Ordinal.add_sub_cancel_of_le h1D
  have hpδy : p + 1 + δ = y := by rw [add_assoc, hδ, hpD]
  have hDx : D < x := ((Ordinal.sub_le_self y p).trans_lt hyx)
  have hDL : D < Nc.ncL S ω := hDx.trans hxL
  have hδL : δ < Nc.ncL S ω := ((Ordinal.sub_le_self D 1).trans_lt hDx).trans hxL
  have hpδx : p + δ < x := by
    refine lt_of_le_of_lt ?_ hyx
    rw [← hpδy, add_assoc]; exact (add_le_add_iff_left p).2 le_add_self
  have hcondD : ∀ d, d ≤ D → d < gamma (p + d) := by
    intro d hd
    rcases eq_or_ne d 0 with rfl | hd0
    · exact gamma_pos
    have hpd : p < p + d := lt_add_of_pos_right _ (pos_iff_ne_zero.2 hd0)
    have hdx : p + d < x := lt_of_le_of_lt (by rw [← hpD]; exact (add_le_add_iff_left p).2 hd) hyx
    exact le_add_self.trans_lt (hnofix _ hpd hdx)
  have hcond : ∀ σ, σ ≤ δ → p + 1 + σ < gamma (p + 1 + σ) := by
    intro σ hσ
    refine hnofix _ (lt_of_lt_of_le (lt_add_one p) le_self_add) (lt_of_le_of_lt ?_ hyx)
    rw [← hpδy]; exact (add_le_add_iff_left _).2 hσ
  -- `x = ψ_{Ω₁}(B_p + D)`
  have hpW : p < S.psi (bcAlphaW S) (Om 1) := by rw [← Bc.ncL_omega_eq S]; exact hpL
  obtain ⟨Bp, hownp, hBp⟩ := rb_own_of_SC hpSC hpW
  obtain ⟨hval, hψ⟩ := lq_psi_gamma_of hownp (hpp.trans hBp.symm) D hcondD
  have hψx : S.psi (Bp + D) (Om 1) = x := by rw [hψ, hpD, hy]
  have hown1 : Bp + D ∈ S.CSet (Bp + D) (S.psi (Bp + D) (Om 1)) :=
    CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one (le_self_add : Bp ≤ Bp + D)).2 hownp) (CSet.of_lt hval)
  have hdvd : Om 1 ∣ Bp := rbDvd_of_fix hownp (by rw [hBp]; exact hpp)
  -- the image
  obtain ⟨r, hDr, hBr, hownB', hBp', hBx⟩ := rbB_psi_base (n := n) hownp (by rw [hBp]; exact hc.trans hτp.le)
    hown1 (by rw [hψx]; exact hxX) hDL
  set B' := bcAlphaW S + val S (Bc.bcSig (Bc.bcPre (n + 1)) Bc.bcPreW r) with hB'def
  have hdvd' : Om 1 ∣ B' := rbB_dvd hDr hBr hdvd
  rw [hBp] at hBp'
  rw [hψx] at hBx
  have hτ'p' : upsilon ξ' < S.psi B' (Om 1) := by
    rw [← hBp', ← hBξ]; exact (Bc.bcB_lt_iff hτL hpL).2 hτp
  obtain ⟨hg1, -, -, hpv1⟩ := Cd.cdEta_pv_spec hξ'0 hτ'L1
  have hpv1' : S.psi (ConjT.Aη S (Cd.cdEta S ξ')) (Om 1) = upsilon ξ' := hpv1
  have hA''le : ConjT.Aη S (Cd.cdEta S ξ') ≤ B' := by
    by_contra hlt
    push Not at hlt
    have h := psi_lt_psi Low.InR_Om_one hlt hownB'
    rw [hpv1'] at h
    exact absurd (h.trans hτ'p') (lt_irrefl _)
  have hown'' := Sf.sfOwn hg1 (hA''le.trans_lt (Sf.sfOwn_lt_Lam hownB'))
  have hpp' : gamma (S.psi B' (Om 1)) = S.psi B' (Om 1) :=
    rbFix_of_dvd hown'' hownB' hdvd' (by rw [hpv1']; exact hτ'p')
  -- `B_n x = Γ_{p' + 1 + B_n δ}`
  have hBD : Bc.bcB S n D = 1 + Bc.bcB S n δ := by rw [← hδ, Bc.bcB_add h1L hδL, mwB_one]
  have hval' : Bc.bcB S n D < S.psi (B' + Bc.bcB S n D) (Om 1) := by
    rw [← hBx]; exact (Bc.bcB_lt_iff hDL hxL).2 hDx
  have hBxg : Bc.bcB S n x = gamma (S.psi B' (Om 1) + Bc.bcB S n D) := by
    rw [hBx, lq_psi_gamma hdvd' hownB' hpp' _ hval']
  have hD' := lq_psi_valid_cond hdvd' hownB' hpp' hval'
  set p' := S.psi B' (Om 1) with hp'def
  have hcond' : ∀ σ, σ ≤ Bc.bcB S n δ → p' + 1 + σ < gamma (p' + 1 + σ) := by
    intro σ hσ
    have h1 := hD' (1 + σ) (by rw [hBD]; exact (add_le_add_iff_left 1).2 hσ)
    have h2 : p' < gamma (p' + (1 + σ)) := by
      conv_lhs => rw [← hpp']
      exact gamma_lt_gamma.2 (lt_add_of_pos_right _ (lt_of_lt_of_le zero_lt_one le_self_add))
    rw [add_assoc]
    exact (lq_SC_indec (lq_gamma_SC _)).add_lt h2 h1
  -- the `ϑ`-forms
  have hpδT : p + δ ∈ Tset (upsilon ξ) := hTm _ (hpδx.trans hx2)
  have hpδ1 : p + δ < Om1 := (hpδx.trans hx2).trans hu1
  obtain ⟨c0, hc0⟩ := lq_SC_gamma hτSC
  have hvx : vt (upsilon ξ) (Om1 * Om1 + (p + δ)) = x := by
    rw [rb_sq_enum_fix hτSC hτ1 hc0 hpp hτp δ hpδT hpδ1 hcond, hpδy, hy]
  have hBpδ : Bc.bcB S n (p + δ) = p' + Bc.bcB S n δ := by rw [Bc.bcB_add hpL hδL, hBp']
  have hpδx' : p' + Bc.bcB S n δ < Bc.bcB S n x := by
    rw [← hBpδ]; exact (Bc.bcB_lt_iff (hpδx.trans hxL) hxL).2 hpδx
  have hpδT' : p' + Bc.bcB S n δ ∈ Tset (upsilon ξ') := hTm' _ (hpδx'.trans hhi')
  have hpδ1' : p' + Bc.bcB S n δ < Om1 := (hpδx'.trans hhi').trans hu1'
  obtain ⟨c1, hc1⟩ := lq_SC_gamma hτ'SC
  have hvx' : vt (upsilon ξ') (Om1 * Om1 + (p' + Bc.bcB S n δ)) = Bc.bcB S n x := by
    rw [rb_sq_enum_fix hτ'SC hτ'1 hc1 hpp' hτ'p' _ hpδT' hpδ1' hcond', hBxg, hBD, add_assoc]
  have hlh := (lq_lh_sq hτE hτ1 hpδT hpδ1).2
  rw [hvx] at hlh
  have hlh' := (lq_lh_sq hτ'E hτ'1 hpδT' hpδ1').2
  rw [hvx'] at hlh'
  rw [hlh, hlh']
  have hxxx : x * x + x < Nc.ncL S ω := hLSC.isPrincipal hxx hxL
  rcases eq_or_ne δ 0 with h0 | h0
  · have hBδ0 : Bc.bcB S n δ = 0 := by rw [h0, Bc.bcB_zero]
    have hpT : p ∈ Tset (upsilon ξ) := by have := hpδT; rwa [h0, add_zero] at this
    have hp1 : p < Om1 := by have := hpδ1; rwa [h0, add_zero] at this
    have hpT' : p' ∈ Tset (upsilon ξ') := by have := hpδT'; rwa [hBδ0, add_zero] at this
    have hp1' : p' < Om1 := by have := hpδ1'; rwa [hBδ0, add_zero] at this
    have hz1 : lqZeta (upsilon ξ) (Om1 * Om1) (p + δ) = 0 := by
      rw [h0, add_zero]; exact rb_zeta_fix hτSC hτ1 hc0 hpp hτp hpT hp1
    have hz2 : lqZeta (upsilon ξ') (Om1 * Om1) (p' + Bc.bcB S n δ) = 0 := by
      rw [hBδ0, add_zero]; exact rb_zeta_fix hτ'SC hτ'1 hc1 hpp' hτ'p' hpT' hp1'
    rw [hz1, hz2, add_zero, add_zero, Bc.bcB_add hxx hxL, mxB_mul hE x hxx]
  · have hBδ0 : Bc.bcB S n δ ≠ 0 := by
      intro e
      have := (Bc.bcB_lt_iff (k := n) (lt_of_le_of_lt zero_le hδL) hδL).2 (pos_iff_ne_zero.2 h0)
      rw [Bc.bcB_zero, e] at this
      exact lt_irrefl _ this
    rw [rb_zeta_fix_add hτSC hτ1 hc0 hpp hτp h0 hpδT hpδ1 hcond,
      rb_zeta_fix_add hτ'SC hτ'1 hc1 hpp' hτ'p' hBδ0 hpδT' hpδ1' hcond']
    have hpδ0 : p + δ ≠ 0 := (lt_of_le_of_lt zero_le (lt_add_of_pos_right _ (pos_iff_ne_zero.2 h0))).ne'
    have hlgL : lg (p + δ) < Nc.ncL S ω := (lg_le hpδ0).trans_lt (hpδx.trans hxL)
    rw [Bc.bcB_add hxxx hlgL, Bc.bcB_add hxx hxL, mxB_mul hE x hxx, ← Tp.tpLgB hpδ0 (hpδx.trans hxL), hBpδ]

/-! ## The remaining hypothesis: the fixed points of `Γ_` -/

/-- `SfLhTMove` at the ε-numbers `x ∈ P_ω`, `x > P(υ_ξ)`, that are **fixed points of `Γ_`** (`x = Γ_x`). -/
def RbLhTopFix (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ ξ ξ' x : Ordinal.{0}, Bc.bcC S n ≤ upsilon ξ → upsilon ξ < x → x < upsilon (ξ + 1) →
    upsilon (ξ + 1) < Bc.bcC S (n + 1) → InE x → Bc.bcB S n (upsilon ξ) = upsilon ξ' →
    Bc.bcB S n (upsilon (ξ + 1)) = upsilon (ξ' + 1) → (∀ m : ℕ, VzP (m + 1) x) → ltP (upsilon ξ) < x →
    SC x → gamma x = x →
    Bc.bcB S n (lhT (upsilon ξ) x) = lhT (upsilon ξ') (Bc.bcB S n x)

/-- **`RbLhTopFix` gives `Lq.MqLhTopF`.** -/
theorem rbLhTopF (h : RbLhTopFix S) : MqLhTopF S := by
  intro n ξ ξ' x hc hτx hx2 hξ1lt hE hBξ hBξ1 hall hP hxSC hq
  by_cases hfx : gamma x = x
  · exact h n ξ ξ' x hc hτx hx2 hξ1lt hE hBξ hBξ1 hall hP hxSC hfx
  · exact rbLhT_nonfix hc hτx hx2 hξ1lt hE hBξ hBξ1 hxSC hq hfx

/-- `Lq.MqLhTopF` gives `RbLhTopFix` (so `RbLhTopFix` is the weaker hypothesis). -/
theorem rbLhTopFix_of (h : MqLhTopF S) : RbLhTopFix S :=
  fun n ξ ξ' x hc hτx hx2 hξ1lt hE hBξ hBξ1 hall hP hxSC hfx =>
    h n ξ ξ' x hc hτx hx2 hξ1lt hE hBξ hBξ1 hall hP hxSC ⟨x, hfx, hτx, le_rfl⟩

/-- **`RbLhTopFix` gives `Sf.SfLhTMove`.** -/
theorem rbSfLhT (h : RbLhTopFix S) : Sf.SfLhTMove S := lqSfLhT (rbLhTopF h)

/-- **The road of `Lq.lqRoad` with `RbLhTopFix` in place of `Lq.MqLhTopF`.** -/
theorem rbRoad (hU : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdUpper S l)
    (hO : ∀ l, Cd.CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → Cd.CdCapV S l)
    (hN : Cx.CxNamed S) (hlh : RbLhTopFix S) (hth : Nc.ncL S (ω + 1) ≤ nuC → MxThMoveW S)
    (hhi : Nc.ncL S (ω + 1) ≤ nuC → MxEQth S) :
    Cd.CdEQ S ∧ Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cx.CxT S ∧ Cd.CdCL S ∧ Cd.CdCROSS S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  lqRoad hU hO hL hV hN (rbLhTopF hlh) hth hhi

end Googology.Trans.PoR.InaccPsi.R2.Rb
