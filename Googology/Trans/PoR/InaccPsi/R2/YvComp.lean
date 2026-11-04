import Googology.Trans.PoR.InaccPsi.R2.YvDat

/-!
# The canonical decomposition of `π z` is the `π`-image of that of `z`; the inverse base change on codes below `θ`

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`π = pi σ τ`, `up σ τ = π⁻¹` (`R2.FragBase`), `Tᵗ[σ] = TB τ σ`, `θ = ConjT.th S`, `Γ₀ = gamma 0`.  The bases of FRAG
are `υ`-points, all `≥ Γ₀` (`Gq.gq_gam_le_ups`); at such bases `B₂` is fixed by `π`.

* `yv_B_fix` (`B₂ ∈ Tᵗ[σ]`, `π B₂ = B₂` for `Γ₀ ≤ σ`), `yv_pi_eps` (**`π` of an `ε`-number `≥ Ω₁` is an
  `ε`-number**);
* `yv_comp` (**`YvR g (π z) w` whenever `YvR (g ∘ π) z w`**: the clause of `π z` is the clause of `z` with every part
  moved by `π`; this is `Vc.vc_comp` widened from `B₂` to `θ`), `yv_comp_sub` (**`yvSub g (π z) = yvSub (g ∘ π) z`**);
* `yv_sub_congr` (`yvSub` depends only on the leaves), `yv_sub_id` (**`yvSub id z = z`**), `yv_up` (**THE INVERSE
  BASE CHANGE ON CODES BELOW `θ`: `π⁻¹ G = yvSub π⁻¹ G`** for `G = π z`, `z ∈ Tᵗ[σ]` below `θ` with leaves in `Tᵗ[σ]`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yv

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Ul Googology.Trans.PoR.InaccPsi.R2.Uc
  Googology.Trans.PoR.InaccPsi.R2.Vs

variable {S : InaccSeq.{0}}

/-- `B₂` is fixed by every base change with `Γ₀ ≤ σ`. -/
theorem yv_B_fix (S : InaccSeq.{0}) {σ τ : Ordinal.{0}} (h : Bases σ τ) (hσ : gamma 0 ≤ σ) :
    ucB ∈ TB τ σ ∧ pi σ τ ucB = ucB :=
  Xe.xe_pi_fix_th (S := S) h (Lq.lq_gamma_SC 0) hσ Vd.vd_B_lt_th (Ww.ww_B_dat (Lq.lq_gamma_SC 0))

/-- `Ω_s` (`1 ≤ s < ω`) is fixed by every base change. -/
theorem yv_Om_fix {σ τ s : Ordinal.{0}} (h : Bases σ τ) (hs1 : 1 ≤ s) (hs : s < ω) :
    Om s ∈ TB τ σ ∧ pi σ τ (Om s) = Om s := by
  rcases hs1.lt_or_eq with h1 | h1
  · exact vsOm_TB h hs h1
  · rw [← h1, ← Rj.rj_Om1]; exact pi_Om1 h

/-- **The range conditions of a clause pass to `π z`.** -/
theorem yv_range (S : InaccSeq.{0}) {σ τ s ξ : Ordinal.{0}} (h : Bases σ τ) (hσ : gamma 0 ≤ σ) (hs1 : 1 ≤ s) (hs : s < ω)
    (hT : ξ ∈ TB τ σ) (h1 : Om s < ξ) (h2 : ξ < Om (s + 1)) (hB : ucB ≤ ξ) :
    Om s < pi σ τ ξ ∧ pi σ τ ξ < Om (s + 1) ∧ ucB ≤ pi σ τ ξ := by
  have hsm := (pi_bijOn h).2
  obtain ⟨hOT, hOπ⟩ := yv_Om_fix h hs1 hs
  obtain ⟨hBT, hBπ⟩ := yv_B_fix S h hσ
  refine ⟨?_, vs_pi_lt_Om h hs hs1 hT h2, ?_⟩
  · have := hsm hOT hT h1; rwa [hOπ] at this
  · rcases hB.lt_or_eq with hB | hB
    · have := hsm hBT hT hB; rw [hBπ] at this; exact this.le
    · rw [← hB, hBπ]

/-- `1 ≤ x ⇒ 1 ≤ π x` on `Tᵗ[σ]`. -/
theorem yv_pi_one_le {σ τ x : Ordinal.{0}} (h : Bases σ τ) (hx : x ∈ TB τ σ) (h1 : 1 ≤ x) : 1 ≤ pi σ τ x := by
  have h1σ : (1 : Ordinal.{0}) < σ := Ub.ub_one_lt h.1
  have h1T : (1 : Ordinal.{0}) ∈ TB τ σ := mem_TB_of_lt h h1σ
  rcases h1.lt_or_eq with h1 | h1
  · have := (pi_bijOn h).2 h1T hx h1; rw [pi_lt h h1σ] at this; exact this.le
  · rw [← h1, pi_lt h h1σ]

/-- **`π` of an `ε`-number `≥ Ω₁` is an `ε`-number.** -/
theorem yv_pi_eps {σ τ : Ordinal.{0}} (h : Bases σ τ) (r : ℕ) {ξ : Ordinal.{0}} (hL : YvLv S (· ∈ TB τ σ) ξ)
    (hG : VsG S r ξ) (hr : ξ < Om ((r : Ordinal.{0}) + 1)) (h1 : Om1 ≤ ξ) (hE : ω ^ ξ = ξ) :
    ω ^ pi σ τ ξ = pi σ τ ξ := by
  obtain ⟨hT, -⟩ := yv_pi h r ξ hL hG hr
  rcases h1.lt_or_eq with h1 | h1
  swap
  · rw [← h1, (pi_Om1 h).2]; exact Rj.rj_Om1_opow
  cases hL with
  | low hz _ => exact Vc.vc_pi_eps h hz hT h1 hE
  | om hs hs' e =>
    subst e
    rw [(vsOm_TB h hs' hs).2]; exact Gg.gg_SC_eps (SC_Om (lt_of_lt_of_le zero_lt_one hs.le).ne')
  | cnf _ _ _ _ _ hE' => exact absurd hE hE'
  | @veb s _ hs1 hs h1' h2 hB _ hS _ _ =>
    obtain ⟨L, U, G, hP, hLξ, -, hUE⟩ := yv_pkg (S := S) hs1 hs r h1' hB
    have hξE : ξ < S.psi (Om ((r : Ordinal.{0}) + 1)) (Om (s + 1)) :=
      ulK_lt_W hs (Ui.ui_psi_SC _) (Ui.ui_L_lt_psi _) (hG s hs1 hs) h2
    rcases vsShape (S := S) hs hs1 h1' hξE with ⟨hE', -⟩ | ⟨-, -, ha1, haξ, hcξ, hev⟩ | ⟨hSC, -⟩
    · exact absurd hE hE'
    · have hepsξ := hP.eps h ha1 (by rw [hev]; exact haξ) (by rw [hev]; exact hcξ) (by rw [hev]; exact hLξ)
        (by rw [hev]; exact hξE.trans_le hUE)
      rw [hev] at hepsξ
      obtain ⟨haT, hcT⟩ := hepsξ.1.1 hT
      rw [hepsξ.2 haT hcT]
      have ha1' := yv_pi_one_le h haT ha1
      rw [← veblen_zero_apply]
      exact veblen_veblen_of_lt (lt_of_lt_of_le zero_lt_one ha1') _
    · exact absurd hSC hS
  | @atom s _ hs1 hs h1' h2 hB hSC _ _ =>
    obtain ⟨L, U, G, hP, hLξ, -, hUE⟩ := yv_pkg (S := S) hs1 hs r h1' hB
    have hξE : ξ < S.psi (Om ((r : Ordinal.{0}) + 1)) (Om (s + 1)) :=
      ulK_lt_W hs (Ui.ui_psi_SC _) (Ui.ui_L_lt_psi _) (hG s hs1 hs) h2
    rcases vsShape (S := S) hs hs1 h1' hξE with ⟨hE', -⟩ | ⟨-, hS, -⟩ | ⟨-, hnf, hyξ, hlV, -⟩
    · exact absurd (yv_SC_eps hSC) hE'
    · exact absurd hSC hS
    have hy : Vp.vpI S s (Vp.vpLev S s ξ) ξ < ulH S s (Vp.vpLev S s ξ) (Vp.vpI S s (Vp.vpLev S s ξ) ξ) := by
      rw [hnf]; exact hyξ
    have hat := hP.atom h hlV hy (by rw [hnf]; exact hLξ) (by rw [hnf]; exact hξE.trans_le hUE)
    rw [hnf] at hat
    obtain ⟨hlT, hyT⟩ := hat.1.1 hT
    rw [hat.2 hlT hyT]
    exact yv_SC_eps (ulH_SC _ _)

/-- **The clause of `π z` is the clause of `z` with every part moved by `π`**: `YvR (g ∘ π) z w ⇒ YvR g (π z) w`
(bases with `Γ₀ ≤ σ`, leaves of `z` in `Tᵗ[σ]`). -/
theorem yv_comp {σ τ : Ordinal.{0}} (h : Bases σ τ) (hσ : gamma 0 ≤ σ) (r : ℕ) (g : Ordinal.{0} → Ordinal.{0}) :
    ∀ ξ, YvLv S (· ∈ TB τ σ) ξ → VsG S r ξ → ξ < Om ((r : Ordinal.{0}) + 1) →
      ∀ w, YvR S (g ∘ pi σ τ) ξ w → YvR S g (pi σ τ ξ) w := by
  have hsm := (pi_bijOn h).2
  intro ξ hL
  induction hL with
  | low hz hLv =>
    intro _ _ w hw
    obtain ⟨hT, -⟩ := Vc.vc_pi h _ hz hLv
    cases hw with
    | low _ =>
      rw [← Vc.vc_comp h g _ hz hT]
      exact YvR.low (Vc.vc_pi_lt_B h hz hT)
    | om hs _ e => exact absurd hz (not_lt.2 (e ▸ yv_Om_ge_B hs))
    | cnf _ _ _ _ hB => exact absurd hz (not_lt.2 hB)
    | veb _ _ _ _ hB => exact absurd hz (not_lt.2 hB)
    | atom _ _ _ _ hB => exact absurd hz (not_lt.2 hB)
  | om hs hs' e =>
    intro _ _ w hw
    subst e
    rw [(vsOm_TB h hs' hs).2]
    cases hw with
    | low hz => exact absurd hz (not_lt.2 (yv_Om_ge_B hs))
    | om _ _ _ => exact YvR.om hs hs' rfl
    | cnf _ _ h1 h2 => exact (yv_Om_not_in h1 h2).elim
    | veb _ _ h1 h2 => exact (yv_Om_not_in h1 h2).elim
    | atom _ _ h1 h2 => exact (yv_Om_not_in h1 h2).elim
  | @cnf s ξ hs1 hs h1 h2 hB hE hlog hmod ihg ihr =>
    intro hG hr w hw
    have hξ0 : ξ ≠ 0 := (lt_of_le_of_lt zero_le h1).ne'
    set l := log ω ξ with hldef
    have hlξ : l < ξ := Ss.ss_log_lt hξ0 hE
    have hmξ : ξ % ω ^ l < ξ := Rj.rj_mod_lt hξ0
    have hgsub : VsSub S l ξ := fun i _ _ q' hq' _ _ hK' => (ulK_dec hq' ξ hK').2
    have hrsub : VsSub S (ξ % ω ^ l) ξ := fun i _ _ q' hq' _ _ hK' => ulK_mod hq' ξ hK' _
    have hGl := yv_G_sub hG hgsub
    have hGm := yv_G_sub hG hrsub
    obtain ⟨hlT, -⟩ := yv_pi h r l hlog hGl (hlξ.trans hr)
    obtain ⟨hmT, -⟩ := yv_pi h r _ hmod hGm (hmξ.trans hr)
    obtain ⟨hT, -⟩ := yv_pi h r ξ (YvLv.cnf hs1 hs h1 h2 hB hE hlog hmod) hG hr
    cases hw with
    | low hz => exact absurd hz (not_lt.2 hB)
    | om _ _ e => rw [e] at h1 h2; exact (yv_Om_not_in h1 h2).elim
    | veb _ _ _ _ _ hE' => exact absurd hE' hE
    | atom _ _ _ _ _ hSC => exact absurd (yv_SC_eps hSC) hE
    | @cnf _ _ g'' r'' _ _ _ _ _ _ hg' hr' =>
      have IHg := ihg hGl (hlξ.trans hr) _ hg'
      have IHr := ihr hGm (hmξ.trans hr) _ hr'
      obtain ⟨L, U, G, hP, -, hGξ, hUE⟩ := yv_pkg (S := S) hs1 hs r h1 hB
      have hξE : ξ < S.psi (Om ((r : Ordinal.{0}) + 1)) (Om (s + 1)) :=
        ulK_lt_W hs (Ui.ui_psi_SC _) (Ui.ui_L_lt_psi _) (hG s hs1 hs) h2
      have hξU : ξ < U := hξE.trans_le hUE
      have hpξ : ω ^ l ≤ ξ := opow_log_le_self ω hξ0
      have hΩl : Om1 ≤ l := by
        have hΩE : ω ^ (Om s : Ordinal.{0}) = Om s :=
          Low.opow_eq_self_of_SC (SC_Om (lt_of_lt_of_le zero_lt_one hs1).ne')
        have hsl : Om s ≤ l := le_log_of_opow_le one_lt_omega0 (by rw [hΩE]; exact h1.le)
        exact (by rw [Rj.rj_Om1]; exact Om_le_Om.2 hs1 : Om1 ≤ Om s).trans hsl
      -- the power
      have hpw : ω ^ l ∈ TB τ σ ∧ pi σ τ (ω ^ l) = ω ^ pi σ τ l := by
        by_cases hlE : ω ^ l = l
        · refine ⟨by rw [hlE]; exact hlT, ?_⟩
          rw [hlE]; exact (yv_pi_eps h r hlog hGl (hlξ.trans hr) hΩl hlE).symm
        · have hGl' : G ≤ l := le_log_of_opow_le one_lt_omega0 hGξ
          obtain ⟨hiff, hπp⟩ := hP.opow h hGl' hlE (hpξ.trans_lt hξU)
          exact ⟨hiff.2 hlT, hπp hlT⟩
      have hiff : ω ^ pi σ τ l = pi σ τ l ↔ ω ^ l = l := by
        refine ⟨fun hπE => ?_, fun hlE => (yv_pi_eps h r hlog hGl (hlξ.trans hr) hΩl hlE)⟩
        by_contra hlE
        have hll : l < ω ^ l := lt_of_le_of_ne (right_le_opow l one_lt_omega0) (Ne.symm hlE)
        have := hsm hlT hpw.1 hll
        rw [hpw.2, hπE] at this
        exact lt_irrefl _ this
      -- the coefficient
      have hpos : ω ^ l ≠ 0 := opow_ne_zero _ omega0_ne_zero
      have hlt : ξ < ω ^ l * ω := by
        rw [← opow_succ]; exact lt_opow_succ_log_self one_lt_omega0 ξ
      obtain ⟨n, hn⟩ := lt_omega0.1 ((Ordinal.div_lt hpos).2 hlt)
      have hn0 : (n : Ordinal.{0}) ≠ 0 := by
        rw [← hn]; exact ((Ordinal.div_pos hpos).2 hpξ).ne'
      have hnω : (n : Ordinal.{0}) < ω := natCast_lt_omega0 n
      have hdec : ω ^ l * (n : Ordinal.{0}) + ξ % ω ^ l = ξ := by
        rw [← hn]; exact Ordinal.div_add_mod _ _
      obtain ⟨hk1, hk2⟩ := pi_mul_nat h hpw.1 hpw.2 n
      obtain ⟨c1, c2⟩ := pi_add h hk1 hmT
      rw [hdec] at c1 c2
      -- the canonical clause of `π ξ`
      set L' := pi σ τ l with hL'
      set m' := pi σ τ (ξ % ω ^ l) with hm'
      have hmlt : m' < ω ^ L' := by
        have := hsm hmT hpw.1 (Ordinal.mod_lt ξ hpos)
        rwa [hpw.2] at this
      have hpos' : ω ^ L' ≠ 0 := opow_ne_zero _ omega0_ne_zero
      have hπξ : pi σ τ ξ = ω ^ L' * (n : Ordinal.{0}) + m' := by rw [c2, hk2]
      have hlog' : log ω (pi σ τ ξ) = L' := by
        rw [hπξ, log_opow_mul_add one_lt_omega0 hn0 hmlt, log_eq_zero hnω, add_zero]
      have hdiv' : pi σ τ ξ / ω ^ log ω (pi σ τ ξ) = n := by
        rw [hlog', hπξ, Ordinal.mul_add_div _ hpos', Ordinal.div_eq_zero_of_lt hmlt, add_zero]
      have hmod' : pi σ τ ξ % ω ^ log ω (pi σ τ ξ) = m' := by
        rw [hlog', hπξ, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hmlt]
      have hEπ : ω ^ pi σ τ ξ ≠ pi σ τ ξ := by
        intro e
        have hl' : log ω (pi σ τ ξ) = pi σ τ ξ := by
          conv_lhs => rw [← e]
          exact log_opow one_lt_omega0 _
        have := hsm hlT hT hlξ
        rw [← hL', ← hlog', hl'] at this
        exact lt_irrefl _ this
      obtain ⟨r1, r2, r3⟩ := yv_range S h hσ hs1 hs hT h1 h2 hB
      have hR := YvR.cnf (S := S) (f := g) hs1 hs r1 r2 r3 hEπ
        (by rw [hlog']; exact IHg) (by rw [hmod']; exact IHr)
      rw [hdiv', hlog'] at hR
      rw [hn]
      by_cases hlE : ω ^ l = l
      · rw [if_pos hlE]; rw [if_pos (hiff.2 hlE)] at hR; exact hR
      · rw [if_neg hlE]; rw [if_neg (fun e => hlE (hiff.1 e))] at hR; exact hR
  | @veb s ξ hs1 hs h1 h2 hB hE hS hLa hLc iha ihc =>
    intro hG hr w hw
    obtain ⟨L, U, G, hP, hLξ, -, hUE⟩ := yv_pkg (S := S) hs1 hs r h1 hB
    have hξE : ξ < S.psi (Om ((r : Ordinal.{0}) + 1)) (Om (s + 1)) :=
      ulK_lt_W hs (Ui.ui_psi_SC _) (Ui.ui_L_lt_psi _) (hG s hs1 hs) h2
    have hξU : ξ < U := hξE.trans_le hUE
    obtain ⟨hT, -⟩ := yv_pi h r ξ (YvLv.veb hs1 hs h1 h2 hB hE hS hLa hLc) hG hr
    rcases vsShape (S := S) hs hs1 h1 hξE with ⟨hE', -⟩ | ⟨-, -, ha1, haξ, hcξ, hev⟩ | ⟨hSC, -⟩
    · exact absurd hE hE'
    swap
    · exact absurd hSC hS
    have hasub : VsSub S (invVeblen₁ ξ) ξ := fun i _ _ q' hq' _ _ hK' =>
      (Uo.uoK_veb (by rw [hev]; exact hK') (by rw [hev]; exact haξ) (by rw [hev]; exact hcξ)).1
    have hcsub : VsSub S (invVeblen₂ ξ) ξ := fun i _ _ q' hq' _ _ hK' =>
      (Uo.uoK_veb (by rw [hev]; exact hK') (by rw [hev]; exact haξ) (by rw [hev]; exact hcξ)).2
    have hepsξ := hP.eps h ha1 (by rw [hev]; exact haξ) (by rw [hev]; exact hcξ) (by rw [hev]; exact hLξ)
      (by rw [hev]; exact hξU)
    rw [hev] at hepsξ
    obtain ⟨haT, hcT⟩ := hepsξ.1.1 hT
    have hπξ : pi σ τ ξ = veblen (pi σ τ (invVeblen₁ ξ)) (pi σ τ (invVeblen₂ ξ)) := hepsξ.2 haT hcT
    have hπa : pi σ τ (invVeblen₁ ξ) < pi σ τ ξ := hsm haT hT haξ
    have hπc : pi σ τ (invVeblen₂ ξ) < pi σ τ ξ := hsm hcT hT hcξ
    have ha1' := yv_pi_one_le h haT ha1
    have ha0' : pi σ τ (invVeblen₁ ξ) ≠ 0 := (lt_of_lt_of_le zero_lt_one ha1').ne'
    have hcv : pi σ τ (invVeblen₂ ξ) < veblen (pi σ τ (invVeblen₁ ξ)) (pi σ τ (invVeblen₂ ξ)) := by
      rw [← hπξ]; exact hπc
    have hi1 : invVeblen₁ (pi σ τ ξ) = pi σ τ (invVeblen₁ ξ) := by rw [hπξ, invVeblen₁_veblen hcv]
    have hi2 : invVeblen₂ (pi σ τ ξ) = pi σ τ (invVeblen₂ ξ) := by rw [hπξ, invVeblen₂_veblen ha0' hcv]
    have hEπ : ω ^ pi σ τ ξ = pi σ τ ξ := by
      rw [hπξ, ← veblen_zero_apply]
      exact veblen_veblen_of_lt (lt_of_lt_of_le zero_lt_one ha1') _
    have hSπ : ¬ SC (pi σ τ ξ) := fun hSC' =>
      (Tl.tl_SC_facts hSC').2 (by rw [hi1]; exact hπa)
    obtain ⟨r1, r2, r3⟩ := yv_range S h hσ hs1 hs hT h1 h2 hB
    cases hw with
    | low hz => exact absurd hz (not_lt.2 hB)
    | om _ _ e => rw [e] at h1 h2; exact (yv_Om_not_in h1 h2).elim
    | cnf _ _ _ _ _ hE' => exact absurd hE hE'
    | atom _ _ _ _ _ hSC => exact absurd hSC hS
    | veb _ _ _ _ _ _ _ ha' hc' =>
      have IHa := iha (yv_G_sub hG hasub) (haξ.trans hr) _ ha'
      have IHc := ihc (yv_G_sub hG hcsub) (hcξ.trans hr) _ hc'
      exact YvR.veb (S := S) (f := g) hs1 hs r1 r2 r3 hEπ hSπ (by rw [hi1]; exact IHa) (by rw [hi2]; exact IHc)
  | @atom s ξ hs1 hs h1 h2 hB hSC hLl hLy ihl ihy =>
    intro hG hr w hw
    obtain ⟨L, U, G, hP, hLξ, -, hUE⟩ := yv_pkg (S := S) hs1 hs r h1 hB
    have hξE : ξ < S.psi (Om ((r : Ordinal.{0}) + 1)) (Om (s + 1)) :=
      ulK_lt_W hs (Ui.ui_psi_SC _) (Ui.ui_L_lt_psi _) (hG s hs1 hs) h2
    have hξU : ξ < U := hξE.trans_le hUE
    obtain ⟨hT, -⟩ := yv_pi h r ξ (YvLv.atom hs1 hs h1 h2 hB hSC hLl hLy) hG hr
    rcases vsShape (S := S) hs hs1 h1 hξE with ⟨hE', -⟩ | ⟨-, hS, -⟩ | ⟨-, hnf, hyξ, hlV, hlK⟩
    · exact absurd (yv_SC_eps hSC) hE'
    · exact absurd hSC hS
    set l := Vp.vpLev S s ξ with hldef
    set y := Vp.vpI S s l ξ with hydef
    have hy : y < ulH S s l y := by rw [hnf]; exact hyξ
    have hHW : ulH S s l y < Om (s + 1) := by rw [hnf]; exact h2
    have hlow : ∀ i : Ordinal.{0}, 1 ≤ i → i < s → ∀ q', SC q' → Om i < q' → q' ≤ Om (i + 1) →
        UlK S i q' ξ → UlK S i q' l ∧ UlK S i q' y := fun i _ his q' hq' _ hq'L hK' =>
      ((vs_atom_parts hs his hq' hq'L hlV hy hHW).1).1 (by rw [hnf]; exact hK')
    have hyS : VsSub S y ξ := vs_sub_of_low (fun i hi1 his q' hq' hLq hqW hK' =>
      (hlow i hi1 his q' hq' hLq hqW hK').2) hyξ.le h2
    have hlG : VsG S r l ∧ l < Om ((r : Ordinal.{0}) + 1) := by
      rcases lt_or_ge l (Om (s + 1)) with hlW | hlW
      · have hlξ : l < ξ := ulK_lt_W hs hSC h1 hlK hlW
        exact ⟨yv_G_sub hG (vs_sub_of_low (fun i hi1 his q' hq' hLq hqW hK' =>
          (hlow i hi1 his q' hq' hLq hqW hK').1) hlξ.le h2), hlξ.trans hr⟩
      · exact vs_lev_G hs hlV hy hlW (by rw [hnf]; exact hG) (by rw [hnf]; exact hξE)
    have hat := hP.atom h hlV hy (by rw [hnf]; exact hLξ) (by rw [hnf]; exact hξU)
    rw [hnf] at hat
    obtain ⟨hlT, hyT⟩ := hat.1.1 hT
    have hπξ : pi σ τ ξ = ulH S s (pi σ τ l) (pi σ τ y) := hat.2 hlT hyT
    have hs1' : (1 : Ordinal.{0}) ≤ s + 1 := hs1.trans le_self_add
    have hsω' : s + 1 < ω := Ui.ui_s1_lt_omega hs
    have hπlV : pi σ τ l < Om (s + 1 + 1) := vs_pi_lt_Om h hsω' hs1' hlT hlV
    have hπy : pi σ τ y < ulH S s (pi σ τ l) (pi σ τ y) := by rw [← hπξ]; exact (pi_bijOn h).2 hyT hT hyξ
    obtain ⟨e1, e2⟩ := Vp.vpLev_H (S := S) hπlV hπy
    have hl' : Vp.vpLev S s (pi σ τ ξ) = pi σ τ l := by rw [hπξ]; exact e1
    have hy' : Vp.vpI S s (Vp.vpLev S s (pi σ τ ξ)) (pi σ τ ξ) = pi σ τ y := by rw [hl', hπξ]; exact e2
    have hSCπ : SC (pi σ τ ξ) := by rw [hπξ]; exact ulH_SC _ _
    obtain ⟨r1, r2, r3⟩ := yv_range S h hσ hs1 hs hT h1 h2 hB
    cases hw with
    | low hz => exact absurd hz (not_lt.2 hB)
    | om _ _ e => rw [e] at h1 h2; exact (yv_Om_not_in h1 h2).elim
    | cnf _ _ _ _ _ hE' => exact absurd (yv_SC_eps hSC) hE'
    | veb _ _ _ _ _ _ hS => exact absurd hSC hS
    | atom _ _ h1' h2' _ _ hl'' hy'' =>
      have e := yv_lev_unique h1 h2 h1' h2'
      subst e
      have IHl := ihl hlG.1 hlG.2 _ hl''
      have IHy := ihy (yv_G_sub hG hyS) (hyξ.trans hr) _ hy''
      exact YvR.atom (S := S) (f := g) hs1 hs r1 r2 r3 hSCπ (by rw [hl']; exact IHl) (by rw [hy']; exact IHy)

/-- **`yvSub g (π z) = yvSub (g ∘ π) z`** for every code `z < θ` with leaves in `Tᵗ[σ]` (`Γ₀ ≤ σ`). -/
theorem yv_comp_sub {σ τ z : Ordinal.{0}} (h : Bases σ τ) (hσ : gamma 0 ≤ σ) (g : Ordinal.{0} → Ordinal.{0})
    (hz : z < ConjT.th S) (hL : YvLv S (· ∈ TB τ σ) z) (hex : ∃ w, YvR S (g ∘ pi σ τ) z w) :
    yvSub S g (pi σ τ z) = yvSub S (g ∘ pi σ τ) z := by
  obtain ⟨r, hr1, hzr⟩ := vs_th_bound hz
  obtain ⟨w, hw⟩ := hex
  rw [yvSub_eq hw]
  exact yvSub_eq (yv_comp h hσ r g z hL (vs_G_of_W2 hzr)
    ((hzr.trans (Ui.ui_psi_lt (s := 1) _)).trans_le (vs_W2_le hr1)) w hw)

end Googology.Trans.PoR.InaccPsi.R2.Yv
