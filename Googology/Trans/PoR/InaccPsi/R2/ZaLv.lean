import Googology.Trans.PoR.InaccPsi.R2.YvLev

/-!
# The leaves of `π z` are the `π`-images of the leaves of `z` (codes below `θ`)

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`π = pi σ τ`, `Tᵗ[σ] = TB τ σ`, `θ = ConjT.th S`, `Γ₀ = gamma 0`, `Yv.YvLv S P z` (every leaf of the canonical
decomposition of `z` satisfies `P`).  `Vi.vi_lv_pi` says, below `B₂`: `VcLv P (π z) ⇔ VcLv (P ∘ π) z`.  Here the same
for **every code below `θ`**, by induction on the canonical decomposition (the clause of `π z` is the `π`-image of the
clause of `z`, as computed in the proof of `Yv.yv_comp`):

* `za_lv_pi` (**`YvLv P (π ξ) ⇔ YvLv (P ∘ π) ξ`** at every part `ξ` of the visibility bound), `za_lv_pi_th` (the
  same for every `z < θ` with `z ∈ Tᵗ[σ]`, no bound hypothesis).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Za

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Ul Googology.Trans.PoR.InaccPsi.R2.Uc
  Googology.Trans.PoR.InaccPsi.R2.Vs Googology.Trans.PoR.InaccPsi.R2.Yv

variable {S : InaccSeq.{0}}

/-- **The leaves of `π ξ` are the `π`-images of the leaves of `ξ`.** -/
theorem za_lv_pi {σ τ : Ordinal.{0}} (h : Bases σ τ) (hσ : gamma 0 ≤ σ) (r : ℕ) :
    ∀ ξ, YvLv S (· ∈ TB τ σ) ξ → VsG S r ξ → ξ < Om ((r : Ordinal.{0}) + 1) →
      ∀ P : Ordinal.{0} → Prop, (YvLv S P (pi σ τ ξ) ↔ YvLv S (fun x => P (pi σ τ x)) ξ) := by
  have hsm := (pi_bijOn h).2
  intro ξ hL
  induction hL with
  | @low z hz hLv =>
    intro _ _ P
    obtain ⟨hT, -⟩ := Vc.vc_pi h _ hz hLv
    have hπB : pi σ τ z < ucB := Vc.vc_pi_lt_B h hz hT
    constructor
    · intro hP
      generalize hx : pi σ τ z = x at hP
      cases hP with
      | low _ hV => rw [← hx] at hV; exact YvLv.low hz ((Vi.vi_lv_pi h P z hz hT).1 hV)
      | om hs _ e => rw [← hx] at e; exact absurd hπB (not_lt.2 (e ▸ yv_Om_ge_B hs))
      | cnf _ _ _ _ hB' => rw [← hx] at hB'; exact absurd hπB (not_lt.2 hB')
      | veb _ _ _ _ hB' => rw [← hx] at hB'; exact absurd hπB (not_lt.2 hB')
      | atom _ _ _ _ hB' => rw [← hx] at hB'; exact absurd hπB (not_lt.2 hB')
    · intro hP
      cases hP with
      | low _ hV => exact YvLv.low hπB ((Vi.vi_lv_pi h P z hz hT).2 hV)
      | om hs _ e => exact absurd hz (not_lt.2 (e ▸ yv_Om_ge_B hs))
      | cnf _ _ _ _ hB' => exact absurd hz (not_lt.2 hB')
      | veb _ _ _ _ hB' => exact absurd hz (not_lt.2 hB')
      | atom _ _ _ _ hB' => exact absurd hz (not_lt.2 hB')
  | @om s z hs hs' e =>
    intro _ _ P
    subst e
    rw [(vsOm_TB h hs' hs).2]
    exact iff_of_true (YvLv.om hs hs' rfl) (YvLv.om hs hs' rfl)
  | @cnf s ξ hs1 hs h1 h2 hB hE hlog hmod ihg ihr =>
    intro hG hr P
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
    constructor
    · intro hQ
      generalize hx : pi σ τ ξ = x at hQ
      cases hQ with
      | low hz' => rw [← hx] at hz'; exact absurd hz' (not_lt.2 r3)
      | om _ _ e => rw [← hx] at e; rw [e] at r1 r2; exact (yv_Om_not_in r1 r2).elim
      | cnf _ _ _ _ _ _ hg hm =>
        rw [← hx, hlog'] at hg
        rw [← hx, hmod'] at hm
        exact YvLv.cnf hs1 hs h1 h2 hB hE ((ihg hGl (hlξ.trans hr) P).1 hg)
          ((ihr hGm (hmξ.trans hr) P).1 hm)
      | veb _ _ _ _ _ hE' => rw [← hx] at hE'; exact absurd hE' hEπ
      | atom _ _ _ _ _ hSC => rw [← hx] at hSC; exact absurd (yv_SC_eps hSC) hEπ
    · intro hQ
      cases hQ with
      | low hz => exact absurd hz (not_lt.2 hB)
      | om _ _ e => rw [e] at h1 h2; exact (yv_Om_not_in h1 h2).elim
      | veb _ _ _ _ _ hE' => exact absurd hE' hE
      | atom _ _ _ _ _ hSC => exact absurd (yv_SC_eps hSC) hE
      | cnf _ _ _ _ _ _ hg hm =>
        have IHg := (ihg hGl (hlξ.trans hr) P).2 hg
        have IHm := (ihr hGm (hmξ.trans hr) P).2 hm
        exact YvLv.cnf hs1 hs r1 r2 r3 hEπ (by rw [hlog']; exact IHg) (by rw [hmod']; exact IHm)
  | @veb s ξ hs1 hs h1 h2 hB hE hS hLa hLc iha ihc =>
    intro hG hr P
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
    have IHa := iha (yv_G_sub hG hasub) (haξ.trans hr) P
    have IHc := ihc (yv_G_sub hG hcsub) (hcξ.trans hr) P
    constructor
    · intro hQ
      generalize hx : pi σ τ ξ = x at hQ
      cases hQ with
      | low hz' => rw [← hx] at hz'; exact absurd hz' (not_lt.2 r3)
      | om _ _ e => rw [← hx] at e; rw [e] at r1 r2; exact (yv_Om_not_in r1 r2).elim
      | cnf _ _ _ _ _ hE' => rw [← hx] at hE'; exact absurd hEπ hE'
      | atom _ _ _ _ _ hSC => rw [← hx] at hSC; exact absurd hSC hSπ
      | veb _ _ _ _ _ _ _ ha' hc' =>
        rw [← hx, hi1] at ha'
        rw [← hx, hi2] at hc'
        exact YvLv.veb hs1 hs h1 h2 hB hE hS (IHa.1 ha') (IHc.1 hc')
    · intro hQ
      cases hQ with
      | low hz => exact absurd hz (not_lt.2 hB)
      | om _ _ e => rw [e] at h1 h2; exact (yv_Om_not_in h1 h2).elim
      | cnf _ _ _ _ _ hE' => exact absurd hE hE'
      | atom _ _ _ _ _ hSC => exact absurd hSC hS
      | veb _ _ _ _ _ _ _ ha' hc' =>
        exact YvLv.veb hs1 hs r1 r2 r3 hEπ hSπ (by rw [hi1]; exact IHa.2 ha') (by rw [hi2]; exact IHc.2 hc')
  | @atom s ξ hs1 hs h1 h2 hB hSC hLl hLy ihl ihy =>
    intro hG hr P
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
    have IHl := ihl hlG.1 hlG.2 P
    have IHy := ihy (yv_G_sub hG hyS) (hyξ.trans hr) P
    constructor
    · intro hQ
      generalize hx : pi σ τ ξ = x at hQ
      cases hQ with
      | low hz' => rw [← hx] at hz'; exact absurd hz' (not_lt.2 r3)
      | om _ _ e => rw [← hx] at e; rw [e] at r1 r2; exact (yv_Om_not_in r1 r2).elim
      | cnf _ _ _ _ _ hE' => rw [← hx] at hE'; exact absurd (yv_SC_eps hSCπ) hE'
      | veb _ _ _ _ _ _ hS' => rw [← hx] at hS'; exact absurd hSCπ hS'
      | atom _ _ h1' h2' _ _ hl'' hy'' =>
        rw [← hx] at h1' h2' hl'' hy''
        have e := yv_lev_unique r1 r2 h1' h2'
        subst e
        rw [hl'] at hl''
        rw [hy'] at hy''
        exact YvLv.atom hs1 hs h1 h2 hB hSC (IHl.1 hl'') (IHy.1 hy'')
    · intro hQ
      cases hQ with
      | low hz => exact absurd hz (not_lt.2 hB)
      | om _ _ e => rw [e] at h1 h2; exact (yv_Om_not_in h1 h2).elim
      | cnf _ _ _ _ _ hE' => exact absurd (yv_SC_eps hSC) hE'
      | veb _ _ _ _ _ _ hS' => exact absurd hSC hS'
      | atom _ _ h1' h2' _ _ hl'' hy'' =>
        have e := yv_lev_unique h1 h2 h1' h2'
        subst e
        exact YvLv.atom hs1 hs r1 r2 r3 hSCπ (by rw [hl']; exact IHl.2 hl'') (by rw [hy']; exact IHy.2 hy'')

/-- **`YvLv P (π z) ⇔ YvLv (P ∘ π) z`** for every `z < θ` in `Tᵗ[σ]` (`Γ₀ ≤ σ`). -/
theorem za_lv_pi_th {σ τ z : Ordinal.{0}} (h : Bases σ τ) (hσ : gamma 0 ≤ σ) (hz : z < ConjT.th S)
    (hT : z ∈ TB τ σ) (P : Ordinal.{0} → Prop) :
    YvLv S P (pi σ τ z) ↔ YvLv S (fun x => P (pi σ τ x)) z := by
  obtain ⟨r, hG, hr⟩ := yv_bound (S := S) hz
  exact za_lv_pi h hσ r z ((yv_TB_iff h hz).1 hT) hG hr P

end Googology.Trans.PoR.InaccPsi.R2.Za
