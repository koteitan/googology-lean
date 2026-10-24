import Googology.Trans.PoR.InaccPsi.R2.GlR2

/-!
# CODES BELOW `Γ_{Ω₁+1}`: readings below `Γ_{x+1}`, powers, and the cofinality at the `ε`-number codes

* `glR_lt0` (**every reading lies below `Γ_{x+1}`**), `gl_pow` (the reading of `e^j`), `gl_omega_le`, `glR_one_add`;
* `GlCof`, `gl_lim_of_cof`, `gl_sup_lim`, `gl_baseCof` (**the codes below an `ε`-number code `e = glPsi α η` of ANY
  level `α` have readings cofinal in `e(x) = ϑˣ(Ω₁·α(x) + η(x))`**, given cofinality at `α` and `η`).  One argument
  for all levels: if the readings of the codes below `e` stayed below some `ν < e(x)`, their supremum `u` would be a
  fixed point of every `φ_γ`, `γ < α(x)` (cofinality at `α` gives a code `α'' < α` with `γ ≤ α''(x)`, and the code
  `glPsi α'' t < e` reads `ϑˣ(Ω₁·α''(x) + t(x)) ≥ φ_{α''(x)}(t(x))`; for `γ = 0` the code `e_t^t` reads
  `≥ ω^{t(x)}`), above `x`, `α(x)`, `η(x)` and every `ϑˣ(Ω₁·α(x) + σ)`, `σ < η(x)` (cofinality at `η`), so
  `e(x) ≤ u` by the minimality of `ϑˣ(Ω₁·α(x) + η(x))` ([W07a] Lemma 3.30, `R2.LvLev`), a contradiction.
  `e = ε_{Ω₁+1}` by the towers of `R2.GhEps`.

No new axiom.  New definition: `GlCof`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gl

open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu

open Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh Googology.Trans.PoR.InaccPsi.R2.Gi
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gb
open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2

theorem glR_lt0 {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) {c : Ordinal.{0}} (hc : c < gcG 0)
    (hg : glG c < x) : glR c x < gq 0 x := by
  rw [gu_gq0_eq hx hx1]; exact glR_lt_G hx hx1 hc hg

/-- **The reading of `e^j`** (`e` an `ε`-number code, `j ≠ 0`, `e^j < ε_{e+1}`): `e(x)^{j(x)}`. -/
theorem gl_pow {e j : Ordinal.{0}} (he : InE e) (hOe : Om1 < e) (hj : j ≠ 0) (hv : e ^ j < eN e)
    (hB : e ^ j < gcG 0) :
    (∀ x, glR (e ^ j) x = glBA (glR (glK e) x) (glR (glI e) x) x ^ glR j x) ∧ glG (e ^ j) = max (glQE e) (glQ j) := by
  have hE1 : (1 : Ordinal.{0}) < e := Lu.lu_one_lt_E he
  have e1 : e ^ j = e ^ j * 1 + 0 := by rw [mul_one, add_zero]
  have hr : (0 : Ordinal.{0}) < e ^ j := opow_pos _ he.pos
  refine ⟨fun x => ?_, ?_⟩
  · rw [e1, glR_cnf he hOe hj one_ne_zero hE1 hr (e1 ▸ hv) (e1 ▸ hB), glR_one, glR_zero, mul_one, add_zero]
  · rw [e1, glG_cnf he hOe hj one_ne_zero hE1 hr (e1 ▸ hv) (e1 ▸ hB), glQ_one, glG_zero]
    simp

section Low

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

/-- **An infinite code has an infinite reading.** -/
theorem gl_omega_le {a : Ordinal.{0}} (ha : ω ≤ a) (haB : a < gcG 0) (hg : glG a < x) : ω ≤ glR a x := by
  rcases lt_or_ge a gfE with haE | haE
  · rw [glR_low haE]
    rcases lt_or_ge a Om1 with ha1 | ha1
    · rw [(rdc_const ha1 x).1]; exact ha
    have ha0 : a ≠ 0 := (lt_of_lt_of_le omega0_pos ha).ne'
    obtain ⟨hq, -, -, -, -, -⟩ := parts ha0
    have hl0 : log Om1 a ≠ 0 :=
      (lt_of_lt_of_le zero_lt_one (le_log_of_opow_le gf_one_lt_Om1 (by rw [opow_one]; exact ha1))).ne'
    have hlE : log Om1 a < gfE := (log_le_self Om1 a).trans_lt haE
    rw [rdc_dec ha0 haE]
    calc ω ≤ x := (omega0_lt_inE hx).le
      _ = x ^ (1 : Ordinal.{0}) := (opow_one _).symm
      _ ≤ x ^ rdc (log Om1 a) x := opow_le_opow_right hx.pos (one_le_iff_pos.2 (rdc_pos hx hl0 hlE))
      _ ≤ x ^ rdc (log Om1 a) x * (a / Om1 ^ log Om1 a) := le_mul_of_one_le_right' (one_le_iff_pos.2 hq)
      _ ≤ _ := le_self_add
  have hlead := gl_lead hx hx1 haE haB hg
  rw [← gl_At_eq haE haB] at hlead
  have hge := gl_E_g haE haB hg
  have := (gl_eps_read hx hx1 (guE_E a) (gl_Om1_lt_E haE) ((gl_E_le haE).trans_lt haB) hge).2.2.2.2.2.2.2.2.2.2.2.2
  exact (omega0_le_eN x).trans (this.trans hlead.2)

theorem glR_one_add {a : Ordinal.{0}} (haB : a < gcG 0) (hg : glG a < x) : glR (1 + a) x = 1 + glR a x := by
  rcases lt_or_ge a ω with haω | haω
  · obtain ⟨n, hn⟩ := lt_omega0.1 haω
    have : (1 : Ordinal.{0}) + n = ((1 + n : ℕ) : Ordinal.{0}) := by push_cast; rfl
    rw [hn, this, glR_nat, glR_nat]; push_cast; rfl
  · rw [one_add_of_omega0_le haω, one_add_of_omega0_le (gl_omega_le hx hx1 haω haB hg)]

end Low

/-! ## Cofinality at the `ε`-number codes -/

/-- Cofinality at the code `j`: every `ν` below its reading is at most the reading of a smaller code. -/
def GlCof (x j : Ordinal.{0}) : Prop :=
  glG j < x → ∀ ν, ν < glR j x → ∃ b, b < j ∧ glG b < x ∧ ν ≤ glR b x

/-- A nonempty bounded set of ordinals without a largest element has a limit supremum. -/
theorem gl_sup_lim {T : Set Ordinal.{0}} (hne : T.Nonempty) (hbdd : BddAbove T)
    (hup : ∀ v ∈ T, ∃ w ∈ T, v < w) : IsSuccLimit (sSup T) := by
  obtain ⟨v0, hv0⟩ := hne
  obtain ⟨w0, hw0, hvw⟩ := hup v0 hv0
  refine Ordinal.isSuccLimit_iff.2 ⟨?_, isSuccPrelimit_of_succ_lt (fun a ha => ?_)⟩
  · exact (lt_of_le_of_lt zero_le (hvw.trans_le (le_csSup hbdd hw0))).ne'
  · obtain ⟨v, hv, hav⟩ := exists_lt_of_lt_csSup ⟨v0, hv0⟩ ha
    obtain ⟨w, hw, hvw'⟩ := hup v hv
    exact (Order.succ_le_of_lt hav).trans_lt (hvw'.trans_le (le_csSup hbdd hw))

section Cof

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

/-- **A limit code has a limit reading.** -/
theorem gl_lim_of_cof {κ : Ordinal.{0}} (hl : IsSuccLimit κ) (hκB : κ < gcG 0) (hg : glG κ < x)
    (hc : GlCof x κ) : IsSuccLimit (glR κ x) := by
  have hκ0 : κ ≠ 0 := hl.bot_lt.ne'
  rcases zero_or_succ_or_isSuccLimit (glR κ x) with h0 | ⟨ν, hν⟩ | hlim
  · exact absurd h0 (glR_pos hx hx1 hκ0 hκB hg).ne'
  · exfalso
    rw [succ_eq_add_one] at hν
    obtain ⟨b, hb, hgb, hνb⟩ := hc hg ν (by rw [← hν]; exact lt_add_one ν)
    have hbκ : glR b x < glR κ x := glR_mono hx hx1 hκB hb hg hgb
    have hbe : glR b x = ν := le_antisymm (Order.lt_add_one_iff.1 (hν ▸ hbκ)) hνb
    have hb1 : b + 1 < κ := hl.add_one_lt hb
    have hgb1 : glG (b + 1) < x := glG_succ (ev_isSuccLimit_of_inE hx) b (hb1.trans hκB) hgb
    have := glR_mono hx hx1 hκB hb1 hg hgb1
    rw [glR_succ b (hb1.trans hκB), hbe, hν] at this
    exact lt_irrefl _ this
  · exact hlim

/-- **THE CODES BELOW AN `ε`-NUMBER CODE `e = glPsi α η` HAVE READINGS COFINAL IN `e(x)`**, at every level `α`, given
cofinality at the level `α` and at the index `η`. -/
theorem gl_baseCof {e : Ordinal.{0}} (he : InE e) (hOe : Om1 < e) (heB : e < gcG 0) (hge : glG e < x)
    (hcα : GlCof x (glK e)) (hcη : GlCof x (glI e)) :
    ∀ ν, ν < glR e x → ∃ t, t < e ∧ glG t < x ∧ ν < glR t x := by
  have hωx := omega0_lt_inE hx
  intro ν hν
  -- `e = ε_{Ω₁+1}`: the towers below `ε_{Ω₁+1}`
  rcases (show gfE ≤ e from eN_le hOe he).lt_or_eq with hEe | hEe
  swap
  · rw [← hEe, glR_E] at hν
    obtain ⟨i, hi⟩ := ghTw_cof hx hν
    refine ⟨ghTw i, by rw [← hEe]; exact ghTw_lt i, ?_, ?_⟩
    · rw [glG_low (ghTw_lt i)]; exact (ghTw_gtc i).trans_lt (Lu.lu_one_lt_E hx)
    · rw [glR_low (ghTw_lt i)]; exact hi
  by_contra hcon
  push Not at hcon
  obtain ⟨r, hk1, hke, hηe, hgk, hgη, hkR, hkT, hk1x, hηT, hη1, hRE, heR⟩ := gl_eps_read hx hx1 he hOe heB hge
  set α := glK e with hαdef
  set η := glI e with hηdef
  set β := glR α x with hβdef
  have hce : glPsi α η = e := (glData_spec he hOe heB).2.2.2
  have hαG : α < gcG 0 := hke.trans heB
  set T : Set Ordinal.{0} := {v | ∃ t, t < e ∧ glG t < x ∧ v = glR t x} with hTdef
  have hbdd : BddAbove T := ⟨ν, by rintro v ⟨t, ht, hgt, rfl⟩; exact hcon t ht hgt⟩
  have hmem : ∀ t, t < e → glG t < x → glR t x ∈ T := fun t ht hgt => ⟨t, ht, hgt, rfl⟩
  have hle : ∀ t, t < e → glG t < x → glR t x ≤ sSup T := fun t ht hgt => le_csSup hbdd (hmem t ht hgt)
  have hne : T.Nonempty := ⟨_, hmem 0 he.pos (by rw [glG_zero]; exact hx.pos)⟩
  have huν : sSup T ≤ ν := csSup_le hne (by rintro v ⟨t, ht, hgt, rfl⟩; exact hcon t ht hgt)
  have hsucc : ∀ t, t < e → glG t < x → t + 1 < e ∧ glG (t + 1) < x ∧ glR (t + 1) x = glR t x + 1 :=
    fun t ht hgt => ⟨(ev_isSuccLimit_of_inE he).add_one_lt ht,
      glG_succ (ev_isSuccLimit_of_inE hx) t ((ev_isSuccLimit_of_inE he).add_one_lt ht |>.trans heB) hgt,
      glR_succ_all t x⟩
  have hlt_of : ∀ t, t < e → glG t < x → glR t x < sSup T := by
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
  have hEgate : glG gfE < x := by rw [glG_E]; exact hx.pos
  -- `ω^v ≤ u` for `v < u`
  have hω : ∀ v, v < u → ω ^ v ≤ u := by
    intro v hv
    obtain ⟨w, ⟨t, ht, hgt, rfl⟩, hvw⟩ := exists_lt_of_lt_csSup hne hv
    refine (opow_le_opow_right omega0_pos hvw.le).trans ?_
    have htB : t < gcG 0 := ht.trans heB
    rcases lt_or_ge t gfE with htE | htE
    · have h1 : glR t x < eN x := by
        rw [glR_low htE]; rw [glG_low htE] at hgt; exact rdc_lt_eN hx t hgt
      have := (eN_E x).opow_lt h1
      rw [← glR_E] at this
      exact this.le.trans (hle _ hEe hEgate)
    · set et := guE t with hetdef
      have het : InE et := guE_E t
      have hOt : Om1 < et := gl_Om1_lt_E htE
      have hett : et ≤ t := gl_E_le htE
      have htN : t < eN et := gl_lt_eN htE
      have ht0 : t ≠ 0 := (lt_of_lt_of_le eW_E.pos htE).ne'
      have hpN : et ^ t < eN et := gu_pow_lt_eN het htN
      have hpe : et ^ t < e := by
        rw [gu_pow_eq het]; exact he.opow_lt (he.mul_lt (hett.trans_lt ht) ht)
      have hpB : et ^ t < gcG 0 := hpe.trans heB
      obtain ⟨hR, hG⟩ := gl_pow het hOt ht0 hpN hpB
      have hgp : glG (et ^ t) < x := by
        rw [hG]; exact max_lt (gl_parts_Q htE htB hgt).1 ((glQ_le t).trans_lt hgt)
      have hge' := gl_E_g htE htB hgt
      have hA := gl_eps_read hx hx1 het hOt (hett.trans_lt htB) hge'
      have hAω : ω ≤ glR et x := (omega0_le_eN x).trans hA.2.2.2.2.2.2.2.2.2.2.2.2
      have h2 : ω ^ glR t x ≤ glR (et ^ t) x := by
        rw [hR x, ← glR_base het hOt (hett.trans_lt htB)]
        exact opow_le_opow_left _ hAω
      exact h2.trans (hle _ hpe hgp)
  -- `u` lies in `P_β`
  have hPu : LuP β u := by
    have hβ0 : β ≠ 0 := (lt_of_lt_of_le zero_lt_one hkR).ne'
    refine (mem_range_veblen hβ0).2 fun γ hγ => ?_
    refine le_antisymm (((isNormal_veblen _).le_iff_forall_le hlim).2 fun v hv => ?_) (right_le_veblen _ _)
    rcases eq_or_ne γ 0 with rfl | hγ0
    · rw [veblen_zero_apply]; exact (hω v hv)
    obtain ⟨α'', hα''α, hgα'', hγα''⟩ := hcα hgk γ hγ
    have hα''0 : α'' ≠ 0 := by
      rintro rfl; rw [glR_zero] at hγα''; exact hγ0 (le_antisymm hγα'' zero_le)
    have hα''1 : 1 ≤ α'' := one_le_iff_ne_zero.2 hα''0
    have hα''G : α'' < gcG 0 := hα''α.trans hαG
    obtain ⟨w, ⟨t, ht, hgt, rfl⟩, hvw⟩ := exists_lt_of_lt_csSup hne hv
    have htB : t < gcG 0 := ht.trans heB
    obtain ⟨htT, ht1⟩ := glR_T hx hx1 htB hgt
    have hα''R1 : 1 ≤ glR α'' x := glR_pos' hx hx1 hα''0 hα''G hgα''
    obtain ⟨hα''T, hα''1'⟩ := glR_T hx hx1 hα''G hgα''
    have hpe : glPsi α'' t < e := by
      rw [← hce]; exact (glPsi_lt_lev hα''α hk1 hαG).2 (by rw [hce]; exact ht)
    have hgp : glG (glPsi α'' t) < x := by
      rw [glG_psi hα''1 hα''G htB]; exact max_lt ((glQ_le _).trans_lt hgα'') ((glQ_le t).trans_lt hgt)
    have hRp : glR (glPsi α'' t) x = glA (glR α'' x) (glR t x) x := by
      rw [glR_psi hα''1 hα''G htB, glBA_eq hx hx1]
    calc veblen γ v ≤ veblen (glR α'' x) (glR t x) :=
          (veblen_le_veblen_iff_right.2 hvw.le).trans (veblen_left_monotone _ hγα'')
      _ ≤ glA (glR α'' x) (glR t x) x := glA_veb_le hx hx1 hα''R1 hα''T hα''1' htT ht1
      _ = glR (glPsi α'' t) x := hRp.symm
      _ ≤ u := hle _ hpe hgp
  -- the other conditions of the minimality
  have hxu : x < u := by
    have := hle _ hEe hEgate
    rw [glR_E] at this
    exact (lt_eN x).trans_le this
  have hηu : glR η x < u := hlt_of η hηe hgη
  have hβu : β < u := hlt_of α hke hgk
  have hprev : ∀ σ, σ < glR η x → glA β σ x < u := by
    intro σ hσ
    obtain ⟨σ', hσ'η, hgσ', hσσ'⟩ := hcη hgη σ hσ
    have hσ'B : σ' < gcG 0 := (hσ'η.trans hηe).trans heB
    obtain ⟨hσ'T, hσ'1⟩ := glR_T hx hx1 hσ'B hgσ'
    have hσT : σ ∈ Tset x := vz_T_down hx hx1 hσ'T hσ'1 hσσ'
    have hpe : glPsi α σ' < e := by rw [← hce]; exact glPsi_lt_iff.2 hσ'η
    have hgp : glG (glPsi α σ') < x := by
      rw [glG_psi hk1 hαG hσ'B]; exact max_lt ((glQ_le α).trans_lt hgk) ((glQ_le σ').trans_lt hgσ')
    have h1 : glA β σ x ≤ glA β (glR σ' x) x :=
      (glA_le_iff hx hx1 hkR hkT hk1x hσT (lt_of_le_of_lt hσσ' hσ'1) hσ'T hσ'1).2 hσσ'
    have h2 : glR (glPsi α σ') x = glA β (glR σ' x) x := by rw [glR_psi hk1 hαG hσ'B, glBA_eq hx hx1]
    rw [← h2] at h1
    exact h1.trans_lt (hlt_of _ hpe hgp)
  have hmin := glA_min hx hx1 hkR hkT hk1x hηT hη1 hPu hxu hηu hβu hprev
  rw [← r] at hmin
  exact absurd (hmin.trans huν) (not_le.2 hν)

end Cof

end Googology.Trans.PoR.InaccPsi.R2.Gl
