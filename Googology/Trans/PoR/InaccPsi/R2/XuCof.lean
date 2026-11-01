import Googology.Trans.PoR.InaccPsi.R2.XuMo

/-!
# XuCof: CODES BELOW `Γ(1)`: cofinality

* `xuR_lowG`, `xuG_lowG` (**below `G` it is `Gl.glR`, `Gl.glG`**), `xu_t0_le_of` (**every `ε`-number above `G` is
  at least `t₀`**), `xu_psi_ne_G`, `xu_psi_read` (**`xuPsi α η` reads `ϑˣ(Ω₁·α(x) + η(x))` on both sides of `G`**, gate
  at most those of `α`, `η`);
* `xu_omega_le` (an infinite code has an infinite reading), `xu_om_cl` (**the readings of the codes below an
  `ε`-number code `e ≥ t₀` are closed under `ω^·` up to a smaller code**);
* `XuCof`, `xu_lim_of_cof`, `xu_baseCof` (**THE CODES BELOW AN `ε`-NUMBER CODE `e = xuPsi α η ≥ t₀` HAVE READINGS
  COFINAL IN `e(x)`**, every level `α < Γ(1)`: the supremum `u` of the readings would be a fixed point of every
  `φ_γ`, `γ < α(x)`, above `x`, `α(x)`, `η(x)` and every `ϑˣ(Ω₁·α(x) + σ)`, `σ < η(x)`, so `e(x) ≤ u` by the minimality
  of `ϑˣ(Ω₁·α(x) + η(x))`, `Gl.glA_min`), `xu_cofPow`, `xuR_cof` (**COFINALITY**, one induction).

No new axiom.  New definition: `XuCof`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Xu

open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2 Googology.Notation.InaccPsi
  Googology.Notation.InaccPsi.InaccSeq Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Gn
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Wt Googology.Trans.PoR.InaccPsi.R2.Gk
  Googology.Trans.PoR.InaccPsi.R2.Gh Googology.Trans.PoR.InaccPsi.R2.Gi Googology.Trans.PoR.InaccPsi.R2.Gm
  Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Hi

theorem xuR_lowG {c : Ordinal.{0}} (hc : c < gcG 0) (x : Ordinal.{0}) : xuR c x = glR c x := by
  rw [xuR_low (hc.trans xu_G_lt_t0)]; exact goGl.step_R_low hc x

theorem xuG_lowG {c : Ordinal.{0}} (hc : c < gcG 0) : xuG c = glG c := by
  rw [xuG_low (hc.trans xu_G_lt_t0)]; exact goGl.step_g_low hc

theorem xuQ_lowG {c : Ordinal.{0}} (hc : c < gcG 0) : xuQ c = glQ c := by
  unfold xuQ glQ; rw [xuG_lowG hc]

theorem xu_t0_eN : Wj.wjT 0 = eN (gcG 0) := by
  have h := go_eN_veb (gcG 0)
  rw [wt_G_fix1] at h
  exact h.symm

/-- **Every `ε`-number above `G` is at least `t₀`.** -/
theorem xu_t0_le_of {v : Ordinal.{0}} (hv : InE v) (hGv : gcG 0 < v) : Wj.wjT 0 ≤ v := by
  rw [xu_t0_eN]; exact eN_le hGv hv

theorem xu_psi_ne_G {α η : Ordinal.{0}} (hα1 : 1 ≤ α) (hαG : α < gcG 1) : xuPsi α η ≠ gcG 0 := by
  intro h
  rcases lt_or_ge α (gcG 0) with hα | hα
  · have hP : LuP (α + 1) (gcG 0) := luP_succ.2 (gn_veb_fix (gcG_SC 0) hα)
    rw [← h] at hP
    exact xuPsi_notP α η hP
  · have := (xuPsi_gt hα1 hαG η).2
    rw [h] at this
    exact absurd hα (not_le.2 this)

section Read

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

/-- **`xuPsi α η` reads `ϑˣ(Ω₁·α(x) + η(x))`** on both sides of `G`, with gate below `x`. -/
theorem xu_psi_read {α η : Ordinal.{0}} (hα1 : 1 ≤ α) (hαG : α < gcG 1) (hηG : η < gcG 1) (hgα : xuG α < x)
    (hgη : xuG η < x) :
    xuR (xuPsi α η) x = glA (xuR α x) (xuR η x) x ∧ xuG (xuPsi α η) < x ∧ xuPsi α η < gcG 1 := by
  have hpB := xuPsi_lt_G1 hαG hηG
  rcases lt_or_ge (xuPsi α η) (gcG 0) with hp | hp
  · have hαp := (xuPsi_gt hα1 hαG η).2
    have hαG0 : α < gcG 0 := hαp.trans hp
    have hηG0 : η < gcG 0 := (lt_xuPsi α η).trans hp
    have he : xuPsi α η = glPsi α η := xuPsi_ne hαG0.ne η
    rw [he] at hp ⊢
    refine ⟨?_, ?_, he ▸ hpB⟩
    · rw [xuR_lowG hp, glR_psi hα1 hαG0 hηG0, glBA_eq hx hx1, xuR_lowG hαG0, xuR_lowG hηG0]
    · rw [xuG_lowG hp, glG_psi hα1 hαG0 hηG0]
      rw [xuG_lowG hαG0] at hgα
      rw [xuG_lowG hηG0] at hgη
      exact max_lt ((glQ_le α).trans_lt hgα) ((glQ_le η).trans_lt hgη)
  · have hGp : gcG 0 < xuPsi α η := lt_of_le_of_ne hp (xu_psi_ne_G hα1 hαG).symm
    have ht := xu_t0_le_of (xuPsi_E hα1 η) hGp
    refine ⟨xuR_psi hα1 hαG hηG ht x, ?_, hpB⟩
    rw [xuG_psi hα1 hαG hηG ht]
    exact max_lt ((xuQ_le α).trans_lt hgα) ((xuQ_le η).trans_lt hgη)

/-- **An infinite code has an infinite reading.** -/
theorem xu_omega_le {a : Ordinal.{0}} (ha : ω ≤ a) (haB : a < gcG 1) (hg : xuG a < x) : ω ≤ xuR a x := by
  rcases lt_or_ge a (Wj.wjT 0) with hat | hat
  · rw [xuR_low hat]; rw [xuG_low hat] at hg; exact wtD.R_omega x hx hx1 a ha (xu_lt_wtB hat) hg
  have hlead := xu_lead hx hx1 hat haB hg
  exact ((omega0_le_eN x).trans (xu_atom hx hx1 hat haB hg).2.2.2.2.2.1).trans hlead.2

theorem xuR_one_add {a : Ordinal.{0}} (haB : a < gcG 1) (hg : xuG a < x) : xuR (1 + a) x = 1 + xuR a x := by
  rcases lt_or_ge a ω with haω | haω
  · obtain ⟨n, hn⟩ := lt_omega0.1 haω
    have : (1 : Ordinal.{0}) + n = ((1 + n : ℕ) : Ordinal.{0}) := by push_cast; rfl
    rw [hn, this, xuR_nat, xuR_nat]; push_cast; rfl
  · rw [one_add_of_omega0_le haω, one_add_of_omega0_le (xu_omega_le hx hx1 haω haB hg)]

/-- **The powers `G^t` below `t₀`**: reading `Γ_{x+1}^{t(x)}`, gate at most that of `t`. -/
theorem xu_Gpow {t : Ordinal.{0}} (ht0 : t ≠ 0) (ht : t < Wj.wjT 0) (hg : xuG t < x) :
    gcG 0 ^ t < Wj.wjT 0 ∧ xuR (gcG 0 ^ t) x = lgG x ^ xuR t x ∧ xuG (gcG 0 ^ t) < x := by
  have hN : goGl.NB = Wj.wjT 0 := by rw [← wtD_B]; rfl
  have hp : gcG 0 ^ t < Wj.wjT 0 := by
    rw [xu_t0_eN]; exact gu_pow_lt_eN gl_G0_E (xu_t0_eN ▸ ht)
  have e1 : gcG 0 ^ t = goGl.B ^ t * 1 + 0 := by rw [mul_one, add_zero]; rfl
  have hr : (0 : Ordinal.{0}) < goGl.B ^ t := opow_pos _ gl_G0_E.pos
  have hv : goGl.B ^ t * 1 + 0 < goGl.NB := by rw [← e1, hN]; exact hp
  refine ⟨hp, ?_, ?_⟩
  · rw [xuR_low hp, xuR_low ht]
    show goGl.hR (gcG 0 ^ t) x = lgG x ^ goGl.hR t x
    rw [e1, goGl.hR_cnf ht0 one_ne_zero goGl.one_lt_B hr hv, goGl.R_one, mul_one, goGl.hR_zero, add_zero]
    rfl
  · rw [xuG_low hp]
    rw [xuG_low ht] at hg
    show goGl.hG (gcG 0 ^ t) < x
    rw [e1, goGl.hG_cnf ht0 one_ne_zero goGl.one_lt_B hr hv, goGl.hG_zero]
    have hω : ω < x := omega0_lt_inE hx
    refine max_lt (max_lt ((goGl.hQ_le t).trans_lt hg) ?_) hx.pos
    rw [goGl.Q_one]; exact hx.pos

/-- **Closure under `ω^·`**: below an `ε`-number code `e ≥ t₀`, every code `t` with gate below `x` has a code
`t' < e` with gate below `x` and `ω^{t(x)} ≤ t'(x)`. -/
theorem xu_om_cl {e t : Ordinal.{0}} (he : InE e) (hte : Wj.wjT 0 ≤ e) (heB : e < gcG 1) (ht : t < e)
    (hgt : xuG t < x) : ∃ t', t' < e ∧ xuG t' < x ∧ ω ^ xuR t x ≤ xuR t' x := by
  have hGe : gcG 0 < e := xu_G_lt_of hte
  rcases lt_or_ge t (gcG 0) with htG | htG
  · refine ⟨gcG 0, hGe, by rw [xuG_G]; exact hx.pos, ?_⟩
    rw [xuR_G, xuR_lowG htG]
    rw [xuG_lowG htG] at hgt
    have := (lgG_facts hx hx1).2.2.2.1
    exact (this.opow_lt (glR_lt_G hx hx1 htG hgt)).le
  rcases lt_or_ge t (Wj.wjT 0) with htt | htt
  · have ht0 : t ≠ 0 := (lt_of_lt_of_le gl_G0_E.pos htG).ne'
    obtain ⟨hp, hR, hg⟩ := xu_Gpow hx hx1 ht0 htt hgt
    refine ⟨gcG 0 ^ t, hp.trans_le hte, hg, ?_⟩
    rw [hR]
    exact opow_le_opow_left _ (omega0_lt_inE (lgG_facts hx hx1).2.2.2.1).le
  · have htB : t < gcG 1 := ht.trans heB
    have htE := xu_gfE_le htt
    set et := guE t with hetdef
    have het : InE et := guE_E t
    have hett : et ≤ t := gl_E_le htE
    have hett0 : Wj.wjT 0 ≤ et := xu_E_ge htt
    have htN : t < eN et := gl_lt_eN htE
    have ht0 : t ≠ 0 := (lt_of_lt_of_le xu_t0_E.pos htt).ne'
    have hpN : et ^ t < eN et := gu_pow_lt_eN het htN
    have hpe : et ^ t < e := by
      rw [gu_pow_eq het]; exact he.opow_lt (he.mul_lt (hett.trans_lt ht) ht)
    have hpB : et ^ t < gcG 1 := hpe.trans heB
    have e1 : et ^ t = et ^ t * 1 + 0 := by rw [mul_one, add_zero]
    have hE1 : (1 : Ordinal.{0}) < et := Lu.lu_one_lt_E het
    have hr : (0 : Ordinal.{0}) < et ^ t := opow_pos _ het.pos
    have hv : et ^ t * 1 + 0 < eN et := by rw [← e1]; exact hpN
    have hvB : et ^ t * 1 + 0 < gcG 1 := by rw [← e1]; exact hpB
    have hge' := xu_E_g htt htB hgt
    refine ⟨et ^ t, hpe, ?_, ?_⟩
    · rw [e1, xuG_cnf het hett0 ht0 one_ne_zero hE1 hr hv hvB, xuQ_one, xuG_zero]
      rw [xuG_base het hett0 ((hett.trans_lt htB))] at hge'
      exact max_lt (max_lt hge' ((xuQ_le t).trans_lt hgt)) (max_lt hx.pos hx.pos)
    · rw [e1, xuR_cnf het hett0 ht0 one_ne_zero hE1 hr hv hvB, xuR_one, xuR_zero, mul_one, add_zero]
      have hA := (xu_atom hx hx1 htt htB hgt).2.2.2.2.2.1
      exact opow_le_opow_left _ ((omega0_le_eN x).trans hA)

end Read

/-! ## Cofinality -/

/-- Cofinality at the code `j`: every `ν` below its reading is at most the reading of a smaller code. -/
def XuCof (x j : Ordinal.{0}) : Prop :=
  xuG j < x → ∀ ν, ν < xuR j x → ∃ b, b < j ∧ xuG b < x ∧ ν ≤ xuR b x

section Cof

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

/-- **A limit code has a limit reading.** -/
theorem xu_lim_of_cof {κ : Ordinal.{0}} (hl : IsSuccLimit κ) (hκB : κ < gcG 1) (hg : xuG κ < x)
    (hc : XuCof x κ) : IsSuccLimit (xuR κ x) := by
  have hκ0 : κ ≠ 0 := hl.bot_lt.ne'
  rcases zero_or_succ_or_isSuccLimit (xuR κ x) with h0 | ⟨ν, hν⟩ | hlim
  · exact absurd h0 (xuR_pos hx hx1 hκ0 hκB hg).ne'
  · exfalso
    rw [succ_eq_add_one] at hν
    obtain ⟨b, hb, hgb, hνb⟩ := hc hg ν (by rw [← hν]; exact lt_add_one ν)
    have hbκ : xuR b x < xuR κ x := xuR_mono hx hx1 hκB hb hg hgb
    have hbe : xuR b x = ν := le_antisymm (Order.lt_add_one_iff.1 (hν ▸ hbκ)) hνb
    have hb1 : b + 1 < κ := hl.add_one_lt hb
    have hgb1 : xuG (b + 1) < x := xuG_succ (ev_isSuccLimit_of_inE hx) b (hb1.trans hκB) hgb
    have := xuR_mono hx hx1 hκB hb1 hg hgb1
    rw [xuR_succ b (hb1.trans hκB), hbe, hν] at this
    exact lt_irrefl _ this
  · exact hlim

/-- **THE CODES BELOW AN `ε`-NUMBER CODE `e = xuPsi α η ≥ t₀` HAVE READINGS COFINAL IN `e(x)`**, given cofinality
at the level and at the index. -/
theorem xu_baseCof {e : Ordinal.{0}} (he : InE e) (hte : Wj.wjT 0 ≤ e) (heB : e < gcG 1) (hge : xuG e < x)
    (hcα : XuCof x (xuK e)) (hcη : XuCof x (xuI e)) :
    ∀ ν, ν < xuR e x → ∃ t, t < e ∧ xuG t < x ∧ ν < xuR t x := by
  intro ν hν
  by_contra hcon
  push Not at hcon
  obtain ⟨r, hk1, hke, hηe, hgk, hgη, hkR, hkT, hk1x, hηT, hη1, hRE, heR, -, -⟩ :=
    xu_eps_read hx hx1 he hte heB hge
  set α := xuK e with hαdef
  set η := xuI e with hηdef
  set β := xuR α x with hβdef
  have hce : xuPsi α η = e := (xuData_spec he (xu_G_lt_of hte) heB).2.2.2
  have hαG : α < gcG 1 := hke.trans heB
  set T : Set Ordinal.{0} := {v | ∃ t, t < e ∧ xuG t < x ∧ v = xuR t x} with hTdef
  have hbdd : BddAbove T := ⟨ν, by rintro v ⟨t, ht, hgt, rfl⟩; exact hcon t ht hgt⟩
  have hmem : ∀ t, t < e → xuG t < x → xuR t x ∈ T := fun t ht hgt => ⟨t, ht, hgt, rfl⟩
  have hle : ∀ t, t < e → xuG t < x → xuR t x ≤ sSup T := fun t ht hgt => le_csSup hbdd (hmem t ht hgt)
  have hne : T.Nonempty := ⟨_, hmem 0 he.pos (by rw [xuG_zero]; exact hx.pos)⟩
  have huν : sSup T ≤ ν := csSup_le hne (by rintro v ⟨t, ht, hgt, rfl⟩; exact hcon t ht hgt)
  have hsucc : ∀ t, t < e → xuG t < x → t + 1 < e ∧ xuG (t + 1) < x ∧ xuR (t + 1) x = xuR t x + 1 :=
    fun t ht hgt => ⟨(ev_isSuccLimit_of_inE he).add_one_lt ht,
      xuG_succ (ev_isSuccLimit_of_inE hx) t ((ev_isSuccLimit_of_inE he).add_one_lt ht |>.trans heB) hgt,
      xuR_succ t ((ev_isSuccLimit_of_inE he).add_one_lt ht |>.trans heB) x⟩
  have hlt_of : ∀ t, t < e → xuG t < x → xuR t x < sSup T := by
    intro t ht hgt
    obtain ⟨h1, h2, h3⟩ := hsucc t ht hgt
    have := hle _ h1 h2
    rw [h3] at this
    exact (lt_add_one _).trans_le this
  have hlim : IsSuccLimit (sSup T) := by
    refine gl_sup_lim hne hbdd ?_
    rintro v ⟨t, ht, hgt, rfl⟩
    obtain ⟨h1, h2, h3⟩ := hsucc t ht hgt
    exact ⟨_, hmem _ h1 h2, by rw [h3]; exact lt_add_one _⟩
  set u := sSup T with hudef
  have hEe : gfE < e := gfE_lt_G0.trans (xu_G_lt_of hte)
  have hEgate : xuG gfE < x := by rw [xuG_lowG gfE_lt_G0, glG_E]; exact hx.pos
  -- `ω^v ≤ u` for `v < u`
  have hω : ∀ v, v < u → ω ^ v ≤ u := by
    intro v hv
    obtain ⟨w, ⟨t, ht, hgt, rfl⟩, hvw⟩ := exists_lt_of_lt_csSup hne hv
    obtain ⟨t', ht', hgt', hle'⟩ := xu_om_cl hx hx1 he hte heB ht hgt
    exact (opow_le_opow_right omega0_pos hvw.le).trans (hle'.trans (hle _ ht' hgt'))
  -- `u` lies in `P_β`
  have hPu : LuP β u := by
    have hβ0 : β ≠ 0 := (lt_of_lt_of_le zero_lt_one hkR).ne'
    refine (mem_range_veblen hβ0).2 fun γ hγ => ?_
    refine le_antisymm (((isNormal_veblen _).le_iff_forall_le hlim).2 fun v hv => ?_) (right_le_veblen _ _)
    rcases eq_or_ne γ 0 with rfl | hγ0
    · rw [veblen_zero_apply]; exact (hω v hv)
    obtain ⟨α'', hα''α, hgα'', hγα''⟩ := hcα hgk γ hγ
    have hα''0 : α'' ≠ 0 := by
      rintro rfl; rw [xuR_zero] at hγα''; exact hγ0 (le_antisymm hγα'' zero_le)
    have hα''1 : 1 ≤ α'' := one_le_iff_ne_zero.2 hα''0
    have hα''G : α'' < gcG 1 := hα''α.trans hαG
    obtain ⟨w, ⟨t, ht, hgt, rfl⟩, hvw⟩ := exists_lt_of_lt_csSup hne hv
    have htB : t < gcG 1 := ht.trans heB
    obtain ⟨htT, ht1⟩ := xuR_T hx hx1 htB hgt
    have hα''R1 : 1 ≤ xuR α'' x := xuR_pos' hx hx1 hα''0 hα''G hgα''
    obtain ⟨hα''T, hα''1'⟩ := xuR_T hx hx1 hα''G hgα''
    have hpe : xuPsi α'' t < e := by
      rw [← hce]; exact (xuPsi_lt_lev hα''α hk1 hαG).2 (by rw [hce]; exact ht)
    obtain ⟨hRp, hgp, -⟩ := xu_psi_read hx hx1 hα''1 hα''G htB hgα'' hgt
    calc veblen γ v ≤ veblen (xuR α'' x) (xuR t x) :=
          (veblen_le_veblen_iff_right.2 hvw.le).trans (veblen_left_monotone _ hγα'')
      _ ≤ glA (xuR α'' x) (xuR t x) x := glA_veb_le hx hx1 hα''R1 hα''T hα''1' htT ht1
      _ = xuR (xuPsi α'' t) x := hRp.symm
      _ ≤ u := hle _ hpe hgp
  -- the other conditions of the minimality
  have hxu : x < u := by
    have := hle _ hEe hEgate
    rw [xuR_lowG gfE_lt_G0, glR_E] at this
    exact (lt_eN x).trans_le this
  have hηu : xuR η x < u := hlt_of η hηe hgη
  have hβu : β < u := hlt_of α hke hgk
  have hprev : ∀ σ, σ < xuR η x → glA β σ x < u := by
    intro σ hσ
    obtain ⟨σ', hσ'η, hgσ', hσσ'⟩ := hcη hgη σ hσ
    have hσ'B : σ' < gcG 1 := (hσ'η.trans hηe).trans heB
    obtain ⟨hσ'T, hσ'1⟩ := xuR_T hx hx1 hσ'B hgσ'
    have hσT : σ ∈ Tset x := vz_T_down hx hx1 hσ'T hσ'1 hσσ'
    have hpe : xuPsi α σ' < e := by rw [← hce]; exact xuPsi_lt_iff.2 hσ'η
    obtain ⟨h2, hgp, -⟩ := xu_psi_read hx hx1 hk1 hαG hσ'B hgk hgσ'
    have h1 : glA β σ x ≤ glA β (xuR σ' x) x :=
      (glA_le_iff hx hx1 hkR hkT hk1x hσT (lt_of_le_of_lt hσσ' hσ'1) hσ'T hσ'1).2 hσσ'
    rw [← h2] at h1
    exact h1.trans_lt (hlt_of _ hpe hgp)
  have hmin := glA_min hx hx1 hkR hkT hk1x hηT hη1 hPu hxu hηu hβu hprev
  rw [← r] at hmin
  exact absurd (hmin.trans huν) (not_le.2 hν)

/-- **The codes below `e^κ` have cofinal readings in `e(x)^{κ(x)}`** (`e ≥ t₀` an `ε`-number code). -/
theorem xu_cofPow {N e : Ordinal.{0}} (hC : ∀ j, j < N → XuCof x j) (he : InE e) (hte : Wj.wjT 0 ≤ e)
    (heB : e < gcG 1) (hge : xuG e < x) (hcα : XuCof x (xuK e)) (hcη : XuCof x (xuI e)) :
    ∀ κ, κ < N → κ ≠ 0 → κ < gcG 1 → xuG κ < x → κ < eN e →
    ∀ ν, ν < xuR e x ^ xuR κ x → ∃ t, t < e ^ κ ∧ xuG t < x ∧ ν < xuR t x := by
  set B := xuR e x with hBdef
  have hBE : InE B := (xu_eps_read hx hx1 he hte heB hge).2.2.2.2.2.2.2.2.2.2.2.1
  have hbase := xu_baseCof hx hx1 he hte heB hge hcα hcη
  intro κ
  induction κ using WellFoundedLT.induction with
  | ind κ IH =>
  intro hκN hκ0 hκB hgκ hκE ν hν
  have hEκ : e ≤ e ^ κ := by
    calc e = e ^ (1 : Ordinal.{0}) := (opow_one _).symm
      _ ≤ e ^ κ := opow_le_opow_right he.pos (one_le_iff_ne_zero.2 hκ0)
  rcases zero_or_succ_or_isSuccLimit κ with h0 | ⟨κ', hs⟩ | hl
  · exact absurd h0 hκ0
  · rw [succ_eq_add_one] at hs
    have hκ'κ : κ' < κ := by rw [← hs]; exact lt_add_one κ'
    have hκ'B : κ' + 1 < gcG 1 := hs ▸ hκB
    have r1 := xuR_succ κ' hκ'B x
    have r2 := xuG_le_succ κ' hκ'B
    rw [hs] at r1 r2
    have hgκ' : xuG κ' < x := r2.trans_lt hgκ
    rw [r1, opow_add, opow_one] at hν
    rcases eq_or_ne κ' 0 with h0 | hκ'0
    · rw [h0, xuR_zero, opow_zero, one_mul] at hν
      obtain ⟨t, ht, hgt, hvt⟩ := hbase ν hν
      exact ⟨t, ht.trans_le hEκ, hgt, hvt⟩
    · have hne : B ^ xuR κ' x ≠ 0 := opow_ne_zero _ hBE.pos.ne'
      have hq : ν / B ^ xuR κ' x < B := (Ordinal.div_lt hne).2 hν
      obtain ⟨t0, ht0, hgt0, hvt0⟩ := hbase _ hq
      have ht00 : t0 ≠ 0 := by
        rintro rfl; rw [xuR_zero] at hvt0; exact absurd hvt0 (not_lt.2 zero_le)
      have hpow : e ^ κ' * t0 < e ^ κ := by
        rw [← hs, opow_add, opow_one]; exact (mul_lt_mul_iff_right₀ (opow_pos _ he.pos)).2 ht0
      have hκpow : e ^ κ < eN e := gu_pow_lt_eN he hκE
      have hv : e ^ κ' * t0 + 0 < eN e := by rw [add_zero]; exact hpow.trans hκpow
      have hvB : e ^ κ' * t0 + 0 < gcG 1 := hv.trans_le (eN_le heB xu_G1_E)
      have hr0 : (0 : Ordinal.{0}) < e ^ κ' := opow_pos _ he.pos
      refine ⟨e ^ κ' * t0 + 0, by rw [add_zero]; exact hpow, ?_, ?_⟩
      · rw [xuG_cnf he hte hκ'0 ht00 ht0 hr0 hv hvB, xuG_zero]
        have hgE := xuG_base he hte heB
        rw [hgE] at hge
        exact max_lt (max_lt hge ((xuQ_le _).trans_lt hgκ'))
          (max_lt ((xuQ_le _).trans_lt hgt0) (lt_of_le_of_lt zero_le hx.pos))
      · rw [xuR_cnf he hte hκ'0 ht00 ht0 hr0 hv hvB, xuR_zero, add_zero, ← xuR_base he hte heB]
        calc ν < B ^ xuR κ' x * (ν / B ^ xuR κ' x + 1) := by
              rw [mul_add_one]
              conv_lhs => rw [← Ordinal.div_add_mod ν (B ^ xuR κ' x)]
              exact (add_lt_add_iff_left _).2 (Ordinal.mod_lt ν hne)
          _ ≤ B ^ xuR κ' x * xuR t0 x := mul_le_mul_right (add_one_le_of_lt hvt0) _
  · have hlim := xu_lim_of_cof hx hx1 hl hκB hgκ (hC κ hκN)
    obtain ⟨μ, hμ, hνμ⟩ := (lt_opow_of_isSuccLimit hBE.pos.ne' hlim).1 hν
    obtain ⟨κ', hκ'κ, hgκ', eκ'⟩ := hC κ hκN hgκ (μ + 1) (hlim.add_one_lt hμ)
    have hκ'0 : κ' ≠ 0 := by
      rintro rfl; rw [xuR_zero] at eκ'
      exact absurd eκ' (not_le.2 (lt_of_le_of_lt zero_le (lt_add_one μ)))
    have hν' : ν < B ^ xuR κ' x :=
      hνμ.trans_le (opow_le_opow_right hBE.pos ((lt_add_one μ).le.trans eκ'))
    obtain ⟨t, ht, hgt, hvt⟩ := IH κ' hκ'κ (hκ'κ.trans hκN) hκ'0 (hκ'κ.trans hκB) hgκ' (hκ'κ.trans hκE) ν hν'
    exact ⟨t, ht.trans_le (opow_le_opow_right he.pos hκ'κ.le), hgt, hvt⟩

/-- **COFINALITY**: every `ν` below the reading of a code `c < Γ(1)` is at most the reading of a smaller code with
gate below `x`. -/
theorem xuR_cof : ∀ c, c < gcG 1 → XuCof x c := by
  have hωx := omega0_lt_inE hx
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hg ν hν
  have hC : ∀ j, j < c → XuCof x j := fun j hj => IH j hj (hj.trans hc)
  rcases lt_or_ge c (Wj.wjT 0) with hct | hct
  · rw [xuG_low hct] at hg
    rw [xuR_low hct] at hν
    obtain ⟨b, hb, hgb, eb⟩ := wtD.cof x hx hx1 c (xu_lt_wtB hct) hg ν hν
    exact ⟨b, hb, by rw [xuG_low (hb.trans hct)]; exact hgb, by rw [xuR_low (hb.trans hct)]; exact eb⟩
  have hcE := xu_gfE_le hct
  by_cases hcI : InE c
  · have hkc := (xuData_spec hcI (xu_G_lt_of hct) hc).2.1
    have hηc := (xuData_spec hcI (xu_G_lt_of hct) hc).2.2.1
    obtain ⟨t, htc, hgt, hνt⟩ := xu_baseCof hx hx1 hcI hct hc hg (hC _ hkc) (hC _ hηc) ν hν
    exact ⟨t, htc, hgt, hνt.le⟩
  have hEc := gl_E_lt_self hcE hcI
  obtain ⟨hk, hd0, hdE, hr, hdec, hkc, hrc, hdc⟩ := gl_parts hcE
  obtain ⟨g0n, g0, g1, g2⟩ := xu_parts_g hωx hct hc hg
  obtain ⟨q0n, q0, -, -⟩ := xu_parts_Q hct hc hg
  set e := guE c with hedef
  have he : InE e := guE_E c
  have hte : Wj.wjT 0 ≤ e := xu_E_ge hct
  have heB : e < gcG 1 := hEc.trans hc
  have hge : xuG e < x := xu_E_g hct hc hg
  set k := log e c with hkdef
  set d := c / e ^ k with hddef
  set r := c % e ^ k with hrdef
  set B := xuR e x with hBdef
  have hcN' : c < eN e := gl_lt_eN hcE
  have hcη : XuCof x (xuI e) := hC _ ((xuData_spec he (xu_G_lt_of hte) heB).2.2.1.trans hEc)
  have hcα : XuCof x (xuK e) := hC _ ((xuData_spec he (xu_G_lt_of hte) heB).2.1.trans hEc)
  have hBE : InE B := (xu_eps_read hx hx1 he hte heB hge).2.2.2.2.2.2.2.2.2.2.2.1
  rw [xuR_dec hct hc, ← xu_At_eq hct hc] at hν
  have hgate : ∀ d' t, d' ≠ 0 → d' < e → t < e ^ k → e ^ k * d' + t ≤ c → xuG d' < x → xuG t < x →
      xuG (e ^ k * d' + t) < x := by
    intro d' t hd' hd'E ht hle hgd' hgt
    rw [xuG_cnf he hte hk hd' hd'E ht (hle.trans_lt hcN') (hle.trans_lt hc)]
    exact max_lt (max_lt q0n q0) (max_lt ((xuQ_le _).trans_lt hgd') hgt)
  rcases lt_or_ge ν (B ^ xuR k x * xuR d x) with hν1 | hν1
  · have hne : B ^ xuR k x ≠ 0 := opow_ne_zero _ hBE.pos.ne'
    have hμ : ν / B ^ xuR k x < xuR d x := (Ordinal.div_lt hne).2 hν1
    obtain ⟨d', hd'd, hgd', ed'⟩ := hC d hdc g1 _ hμ
    have hρ : ν % B ^ xuR k x < B ^ xuR k x := Ordinal.mod_lt ν hne
    obtain ⟨t, htk, hgt, hvt⟩ := xu_cofPow hx hx1 hC he hte heB hge hcα hcη k hkc hk (hkc.trans hc) g0
      (hkc.trans hcN') _ hρ
    have hd'E : d' < e := hd'd.trans hdE
    have hkd : e ^ k ≤ c := by
      rw [← hdec]; exact (le_mul_of_one_le_right' (one_le_iff_ne_zero.2 hd0)).trans le_self_add
    have hνe : ν = B ^ xuR k x * (ν / B ^ xuR k x) + ν % B ^ xuR k x := (Ordinal.div_add_mod ν _).symm
    rcases eq_or_ne d' 0 with hd'0 | hd'0
    · refine ⟨t, htk.trans_le hkd, hgt, ?_⟩
      rw [hd'0, xuR_zero] at ed'
      rw [hνe, nonpos_iff_eq_zero.1 ed', mul_zero, zero_add]; exact hvt.le
    · have hlt : e ^ k * d' + t < c := by
        calc e ^ k * d' + t < e ^ k * d' + e ^ k := (add_lt_add_iff_left _).2 htk
          _ = e ^ k * (d' + 1) := by rw [mul_add_one]
          _ ≤ e ^ k * d := mul_le_mul_right (add_one_le_of_lt hd'd) _
          _ ≤ c := by rw [← hdec]; exact le_self_add
      refine ⟨e ^ k * d' + t, hlt, hgate d' t hd'0 hd'E htk hlt.le hgd' hgt, ?_⟩
      rw [xuR_cnf he hte hk hd'0 hd'E htk (hlt.le.trans_lt hcN') (hlt.trans hc), ← xuR_base he hte heB, hνe]
      exact add_le_add (mul_le_mul_right ed' _) hvt.le
  · have e1 : B ^ xuR k x * xuR d x + (ν - B ^ xuR k x * xuR d x) = ν := Ordinal.add_sub_cancel_of_le hν1
    have hν' : ν - B ^ xuR k x * xuR d x < xuR r x := by
      rw [← e1] at hν; exact (add_lt_add_iff_left _).1 hν
    obtain ⟨b', hb'r, hgb', hb'⟩ := hC r hrc g2 _ hν'
    have hb'k : b' < e ^ k := hb'r.trans hr
    have hlt : e ^ k * d + b' < c := by rw [← hdec]; exact (add_lt_add_iff_left _).2 hb'r
    refine ⟨e ^ k * d + b', hlt, hgate d b' hd0 hdE hb'k hlt.le g1 hgb', ?_⟩
    rw [xuR_cnf he hte hk hd0 hdE hb'k (hlt.le.trans_lt hcN') (hlt.trans hc), ← xuR_base he hte heB, ← e1]
    exact add_le_add le_rfl hb'

end Cof

end Googology.Trans.PoR.InaccPsi.R2.Xu
