import Googology.Trans.PoR.InaccPsi.R2.YvComp

/-!
# Membership is decided by the leaves; the inverse base change on codes below `θ`

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`π = pi σ τ`, `up σ τ = π⁻¹ : T^σ → Tᵗ[σ]` (`R2.FragBase`), `θ = ConjT.th S`.

* `yvR_ex` (**every decomposed code has a leaf substitution under every `f`**), `yvR_congr` (**it depends only on the
  values of `f` at the leaves**), `yv_sub_id` (**`YvR id z z`**: the substitution by the identity gives the code back);
* `yv_lv_TB` (**`z ∈ Tᵗ[σ]` ⇒ every leaf in `Tᵗ[σ]`**, induction along `Vs.vsMu`), `yv_TB_iff` (**`z ∈ Tᵗ[σ] ⇔ every
  leaf in `Tᵗ[σ]`** below `θ`), `yv_pi_TB` (**`π z = yvSub π z` on `Tᵗ[σ] ∩ θ`**);
* `yv_up` (**THE INVERSE BASE CHANGE ON CODES BELOW `θ`: `π⁻¹ G = yvSub π⁻¹ G`** for `G ∈ T^σ` with `π⁻¹ G < θ`, bases
  with `Γ₀ ≤ σ`): `Vc.vc_up` widened from `B₂` to `θ`.

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yv

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Ul Googology.Trans.PoR.InaccPsi.R2.Uc
  Googology.Trans.PoR.InaccPsi.R2.Vs

variable {S : InaccSeq.{0}}

/-- **Every decomposed code has a leaf substitution.** -/
theorem yvR_ex {P : Ordinal.{0} → Prop} (f : Ordinal.{0} → Ordinal.{0}) {z : Ordinal.{0}} (h : YvLv S P z) :
    ∃ w, YvR S f z w := by
  induction h with
  | low hz _ => exact ⟨_, YvR.low hz⟩
  | om hs hs' e => exact ⟨_, YvR.om hs hs' e⟩
  | cnf a b c d e g _ _ ih1 ih2 =>
    obtain ⟨_, h1⟩ := ih1; obtain ⟨_, h2⟩ := ih2; exact ⟨_, YvR.cnf a b c d e g h1 h2⟩
  | veb a b c d e g k _ _ ih1 ih2 =>
    obtain ⟨_, h1⟩ := ih1; obtain ⟨_, h2⟩ := ih2; exact ⟨_, YvR.veb a b c d e g k h1 h2⟩
  | atom a b c d e g _ _ ih1 ih2 =>
    obtain ⟨_, h1⟩ := ih1; obtain ⟨_, h2⟩ := ih2; exact ⟨_, YvR.atom a b c d e g h1 h2⟩

/-- **The substitution depends only on the leaves.** -/
theorem yvR_congr {f g : Ordinal.{0} → Ordinal.{0}} {z : Ordinal.{0}} (h : YvLv S (fun x => f x = g x) z) :
    ∀ {w}, YvR S f z w → YvR S g z w := by
  induction h with
  | low hz hL =>
    intro w hw
    cases hw with
    | low _ => rw [Vc.vcSub_congr _ hL]; exact YvR.low hz
    | om hs _ e => exact absurd hz (not_lt.2 (e ▸ yv_Om_ge_B hs))
    | cnf _ _ _ _ hB => exact absurd hz (not_lt.2 hB)
    | veb _ _ _ _ hB => exact absurd hz (not_lt.2 hB)
    | atom _ _ _ _ hB => exact absurd hz (not_lt.2 hB)
  | om hs hs' e =>
    intro w hw
    subst e
    cases hw with
    | low hz => exact absurd hz (not_lt.2 (yv_Om_ge_B hs))
    | om _ _ _ => exact YvR.om hs hs' rfl
    | cnf _ _ h1 h2 => exact (yv_Om_not_in h1 h2).elim
    | veb _ _ h1 h2 => exact (yv_Om_not_in h1 h2).elim
    | atom _ _ h1 h2 => exact (yv_Om_not_in h1 h2).elim
  | cnf a b h1 h2 e g _ _ ih1 ih2 =>
    intro w hw
    cases hw with
    | low hz => exact absurd hz (not_lt.2 e)
    | om _ _ e' => rw [e'] at h1 h2; exact (yv_Om_not_in h1 h2).elim
    | cnf _ _ _ _ _ _ q1 q2 => exact YvR.cnf a b h1 h2 e g (ih1 q1) (ih2 q2)
    | veb _ _ _ _ _ hE' => exact absurd hE' g
    | atom _ _ _ _ _ hSC => exact absurd (yv_SC_eps hSC) g
  | veb a b h1 h2 e g k _ _ ih1 ih2 =>
    intro w hw
    cases hw with
    | low hz => exact absurd hz (not_lt.2 e)
    | om _ _ e' => rw [e'] at h1 h2; exact (yv_Om_not_in h1 h2).elim
    | cnf _ _ _ _ _ hE' => exact absurd g hE'
    | veb _ _ _ _ _ _ _ q1 q2 => exact YvR.veb a b h1 h2 e g k (ih1 q1) (ih2 q2)
    | atom _ _ _ _ _ hSC => exact absurd hSC k
  | atom a b h1 h2 e g _ _ ih1 ih2 =>
    intro w hw
    cases hw with
    | low hz => exact absurd hz (not_lt.2 e)
    | om _ _ e' => rw [e'] at h1 h2; exact (yv_Om_not_in h1 h2).elim
    | cnf _ _ _ _ _ hE' => exact absurd (yv_SC_eps g) hE'
    | veb _ _ _ _ _ _ hS => exact absurd g hS
    | atom _ _ h1' h2' _ _ q1 q2 =>
      have e' := yv_lev_unique h1 h2 h1' h2'
      subst e'
      exact YvR.atom a b h1 h2 e g (ih1 q1) (ih2 q2)

/-- **The substitution by the identity gives the code back.** -/
theorem yv_sub_id {P : Ordinal.{0} → Prop} (r : ℕ) :
    ∀ ξ, YvLv S P ξ → VsG S r ξ → ξ < Om ((r : Ordinal.{0}) + 1) → YvR S id ξ ξ := by
  intro ξ hL
  induction hL with
  | low hz hLv =>
    intro _ _
    have h := YvR.low (S := S) (f := id) hz
    have e : Vc.vcSub id _ = _ := Vc.vcSub_fix _ (Vc.VcLv_mono (Q := fun x => id x = x) (fun x _ _ => rfl) _ hLv)
    rwa [e] at h
  | om hs hs' e => intro _ _; exact YvR.om hs hs' e
  | @cnf s ξ hs1 hs h1 h2 hB hE _ _ ihg ihr =>
    intro hG hr
    have hξ0 : ξ ≠ 0 := (lt_of_le_of_lt zero_le h1).ne'
    have hlξ : log ω ξ < ξ := Ss.ss_log_lt hξ0 hE
    have hmξ : ξ % ω ^ log ω ξ < ξ := Rj.rj_mod_lt hξ0
    have hgsub : VsSub S (log ω ξ) ξ := fun i _ _ q' hq' _ _ hK' => (ulK_dec hq' ξ hK').2
    have hrsub : VsSub S (ξ % ω ^ log ω ξ) ξ := fun i _ _ q' hq' _ _ hK' => ulK_mod hq' ξ hK' _
    have hR := YvR.cnf (S := S) (f := id) hs1 hs h1 h2 hB hE (ihg (yv_G_sub hG hgsub) (hlξ.trans hr))
      (ihr (yv_G_sub hG hrsub) (hmξ.trans hr))
    have hdec : (if ω ^ log ω ξ = log ω ξ then log ω ξ else ω ^ log ω ξ) * (ξ / ω ^ log ω ξ) +
        ξ % ω ^ log ω ξ = ξ := by
      by_cases hl : ω ^ log ω ξ = log ω ξ
      · rw [if_pos hl, hl]; exact Ordinal.div_add_mod _ _
      · rw [if_neg hl]; exact Ordinal.div_add_mod _ _
    rwa [hdec] at hR
  | @veb s ξ hs1 hs h1 h2 hB hE hS _ _ iha ihc =>
    intro hG hr
    have hξE : ξ < S.psi (Om ((r : Ordinal.{0}) + 1)) (Om (s + 1)) :=
      ulK_lt_W hs (Ui.ui_psi_SC _) (Ui.ui_L_lt_psi _) (hG s hs1 hs) h2
    rcases vsShape (S := S) hs hs1 h1 hξE with ⟨hE', -⟩ | ⟨-, -, -, haξ, hcξ, hev⟩ | ⟨hSC, -⟩
    · exact absurd hE hE'
    · have hasub : VsSub S (invVeblen₁ ξ) ξ := fun i _ _ q' hq' _ _ hK' =>
        (Uo.uoK_veb (by rw [hev]; exact hK') (by rw [hev]; exact haξ) (by rw [hev]; exact hcξ)).1
      have hcsub : VsSub S (invVeblen₂ ξ) ξ := fun i _ _ q' hq' _ _ hK' =>
        (Uo.uoK_veb (by rw [hev]; exact hK') (by rw [hev]; exact haξ) (by rw [hev]; exact hcξ)).2
      have hR := YvR.veb (S := S) (f := id) hs1 hs h1 h2 hB hE hS (iha (yv_G_sub hG hasub) (haξ.trans hr))
        (ihc (yv_G_sub hG hcsub) (hcξ.trans hr))
      rwa [hev] at hR
    · exact absurd hSC hS
  | @atom s ξ hs1 hs h1 h2 hB hSC _ _ ihl ihy =>
    intro hG hr
    have hξE : ξ < S.psi (Om ((r : Ordinal.{0}) + 1)) (Om (s + 1)) :=
      ulK_lt_W hs (Ui.ui_psi_SC _) (Ui.ui_L_lt_psi _) (hG s hs1 hs) h2
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
    have hlR : YvR S id l l := by
      rcases lt_or_ge l (Om (s + 1)) with hlW | hlW
      · have hlξ : l < ξ := ulK_lt_W hs hSC h1 hlK hlW
        exact ihl (yv_G_sub hG (vs_sub_of_low (fun i hi1 his q' hq' hLq hqW hK' =>
          (hlow i hi1 his q' hq' hLq hqW hK').1) hlξ.le h2)) (hlξ.trans hr)
      · obtain ⟨hGl, hlr⟩ := vs_lev_G hs hlV hy hlW (by rw [hnf]; exact hG) (by rw [hnf]; exact hξE)
        exact ihl hGl hlr
    have hR := YvR.atom (S := S) (f := id) hs1 hs h1 h2 hB hSC hlR (ihy (yv_G_sub hG hyS) (hyξ.trans hr))
    rwa [hnf] at hR

/-- **`z ∈ Tᵗ[σ]` ⇒ every leaf of `z` lies in `Tᵗ[σ]`** (induction along `Vs.vsMu`). -/
theorem yv_lv_TB {σ τ : Ordinal.{0}} (h : Bases σ τ) (r : ℕ) :
    ∀ ξ, ξ ∈ TB τ σ → VsG S r ξ → ξ < Om ((r : Ordinal.{0}) + 1) → YvLv S (· ∈ TB τ σ) ξ := by
  intro ξ
  refine (vs_wf (S := S) r).induction (C := fun ξ => ξ ∈ TB τ σ → VsG S r ξ →
    ξ < Om ((r : Ordinal.{0}) + 1) → YvLv S (· ∈ TB τ σ) ξ) ξ ?_
  intro ξ IH hT hG hr
  have hsub : ∀ b, b < ξ → VsSub S b ξ → b ∈ TB τ σ → YvLv S (· ∈ TB τ σ) b :=
    fun b hbξ hbs hbT => IH b (vs_lex_sub r hbs hbξ) hbT (yv_G_sub hG hbs) (hbξ.trans hr)
  rcases lt_or_ge ξ ucB with hξB | hξB
  · exact YvLv.low hξB (Vc.vc_lv_TB h ξ hξB hT)
  have hξ1 : Om 1 ≤ ξ := (Vd.vd_Om1_lt_B.trans_le hξB).le
  obtain ⟨k, hkr, hk1, hk2⟩ := vs_level (r := r) hξ1 hr
  set s := (k : Ordinal.{0}) + 1 with hsdef
  have hs : s < ω := vs_nat_lt_omega k
  have hs1 : (1 : Ordinal.{0}) ≤ s := le_add_self
  rcases hk1.lt_or_eq with h1 | heq
  swap
  · have hs2 : (1 : Ordinal.{0}) < s := by
      rcases hs1.lt_or_eq with h | h
      · exact h
      · exfalso
        rw [← heq, ← h] at hξB
        exact absurd (Vd.vd_Om1_lt_B) (not_lt.2 hξB)
    exact YvLv.om hs2 hs heq.symm
  obtain ⟨L, U, G, hP, hLξ, hGξ, hUE⟩ := yv_pkg (S := S) hs1 hs r h1 hξB
  have hξE : ξ < S.psi (Om ((r : Ordinal.{0}) + 1)) (Om (s + 1)) :=
    ulK_lt_W hs (Ui.ui_psi_SC _) (Ui.ui_L_lt_psi _) (hG _ hs1 hs) hk2
  have hξU : ξ < U := hξE.trans_le hUE
  have hτξ : τ ≤ ξ := (h.2.2.2.trans (Vd.vd_Om1_lt_B.trans_le hξB |>.trans_le' (by rw [Rj.rj_Om1]))).le
  rcases vsShape (S := S) hs hs1 h1 hξE with ⟨hE, -, hlξ⟩ | ⟨hE, hS, ha1, haξ, hcξ, hev⟩ |
      ⟨hSC, hnf, hyξ, hlV, hlK⟩
  · have hξ0 : ξ ≠ 0 := (lt_of_le_of_lt zero_le h1).ne'
    have hmξ : ξ % ω ^ log ω ξ < ξ := Rj.rj_mod_lt hξ0
    have hgsub : VsSub S (log ω ξ) ξ := fun i _ _ q' hq' _ _ hK' => (ulK_dec hq' ξ hK').2
    have hrsub : VsSub S (ξ % ω ^ log ω ξ) ξ := fun i _ _ q' hq' _ _ hK' => ulK_mod hq' ξ hK' _
    have hcomps := Si.si_comps_cons hξ0
    have hwT : ω ^ log ω ξ ∈ TB τ σ := Si.siTB_of_comps h hT hτξ (fun p hp => by
      rw [comps_opow, List.mem_singleton] at hp
      rw [hcomps, hp]; exact List.mem_cons_self ..)
    have hrT : ξ % ω ^ log ω ξ ∈ TB τ σ :=
      Si.siTB_of_comps h hT hτξ (fun p hp => by rw [hcomps]; exact List.mem_cons_of_mem _ hp)
    have hlT : log ω ξ ∈ TB τ σ := by
      by_cases hl : ω ^ log ω ξ = log ω ξ
      · rw [hl] at hwT; exact hwT
      · have hGl : G ≤ log ω ξ := le_log_of_opow_le one_lt_omega0 hGξ
        exact (hP.opow h hGl hl ((opow_log_le_self ω hξ0).trans_lt hξU)).1.1 hwT
    exact YvLv.cnf hs1 hs h1 hk2 hξB hE (hsub _ hlξ hgsub hlT) (hsub _ hmξ hrsub hrT)
  · have hasub : VsSub S (invVeblen₁ ξ) ξ := fun i _ _ q' hq' _ _ hK' =>
      (Uo.uoK_veb (by rw [hev]; exact hK') (by rw [hev]; exact haξ) (by rw [hev]; exact hcξ)).1
    have hcsub : VsSub S (invVeblen₂ ξ) ξ := fun i _ _ q' hq' _ _ hK' =>
      (Uo.uoK_veb (by rw [hev]; exact hK') (by rw [hev]; exact haξ) (by rw [hev]; exact hcξ)).2
    have hepsξ := hP.eps h ha1 (by rw [hev]; exact haξ) (by rw [hev]; exact hcξ) (by rw [hev]; exact hLξ)
      (by rw [hev]; exact hξU)
    rw [hev] at hepsξ
    obtain ⟨haT, hcT⟩ := hepsξ.1.1 hT
    exact YvLv.veb hs1 hs h1 hk2 hξB hE hS (hsub _ haξ hasub haT) (hsub _ hcξ hcsub hcT)
  · set l := Vp.vpLev S s ξ with hldef
    set y := Vp.vpI S s l ξ with hydef
    have hy : y < ulH S s l y := by rw [hnf]; exact hyξ
    have hHW : ulH S s l y < Om (s + 1) := by rw [hnf]; exact hk2
    have hlow : ∀ i : Ordinal.{0}, 1 ≤ i → i < s → ∀ q', SC q' → Om i < q' → q' ≤ Om (i + 1) →
        UlK S i q' ξ → UlK S i q' l ∧ UlK S i q' y := fun i _ his q' hq' _ hq'L hK' =>
      ((vs_atom_parts hs his hq' hq'L hlV hy hHW).1).1 (by rw [hnf]; exact hK')
    have hat := hP.atom h hlV hy (by rw [hnf]; exact hLξ) (by rw [hnf]; exact hξU)
    rw [hnf] at hat
    obtain ⟨hlT, hyT⟩ := hat.1.1 hT
    have hyL := hsub y hyξ (vs_sub_of_low (fun i hi1 his q' hq' hLq hqW hK' =>
      (hlow i hi1 his q' hq' hLq hqW hK').2) hyξ.le hk2) hyT
    have hlL : YvLv S (· ∈ TB τ σ) l := by
      rcases lt_or_ge l (Om (s + 1)) with hlW | hlW
      · have hlξ : l < ξ := ulK_lt_W hs hSC h1 hlK hlW
        exact hsub l hlξ (vs_sub_of_low (fun i hi1 his q' hq' hLq hqW hK' =>
          (hlow i hi1 his q' hq' hLq hqW hK').1) hlξ.le hk2) hlT
      · obtain ⟨hGl, hlr⟩ := vs_lev_G hs hlV hy hlW (by rw [hnf]; exact hG) (by rw [hnf]; exact hξE)
        have hlK1 : UlK S s ξ l := by
          rw [← hnf]; exact (ul_vis (ulH_SC l y)).1 (ulH_D_lt l y)
        have hlow' : ∀ i : Ordinal.{0}, 1 ≤ i → i < (k : Ordinal.{0}) + 1 → ∀ q', SC q' → Om i < q' →
            q' ≤ Om (i + 1) → UlK S i q' ξ → UlK S i q' l := fun i hi1 his q' hq' hLq hq'L hK' =>
          (hlow i hi1 his q' hq' hLq hq'L hK').1
        exact IH l (vs_lex_lev hkr hlow' hlK1 hSC h1 hk2) hlT hGl hlr
    exact YvLv.atom hs1 hs h1 hk2 hξB hSC hlL hyL

theorem yv_bound {z : Ordinal.{0}} (hz : z < ConjT.th S) :
    ∃ r : ℕ, VsG S r z ∧ z < Om ((r : Ordinal.{0}) + 1) := by
  obtain ⟨r, hr1, hzr⟩ := vs_th_bound hz
  exact ⟨r, vs_G_of_W2 hzr, (hzr.trans (Ui.ui_psi_lt (s := 1) _)).trans_le (vs_W2_le hr1)⟩

/-- **Membership in `Tᵗ[σ]` is decided by the leaves** (codes below `θ`). -/
theorem yv_TB_iff {σ τ z : Ordinal.{0}} (h : Bases σ τ) (hz : z < ConjT.th S) :
    z ∈ TB τ σ ↔ YvLv S (· ∈ TB τ σ) z := by
  obtain ⟨r, hG, hr⟩ := yv_bound (S := S) hz
  exact ⟨fun hT => yv_lv_TB h r z hT hG hr, fun hL => (yv_pi h r z hL hG hr).1⟩

/-- **`π = yvSub π` on `Tᵗ[σ] ∩ θ`.** -/
theorem yv_pi_TB {σ τ z : Ordinal.{0}} (h : Bases σ τ) (hz : z < ConjT.th S) (hT : z ∈ TB τ σ) :
    pi σ τ z = yvSub S (pi σ τ) z :=
  (yv_pi_sub h hz ((yv_TB_iff h hz).1 hT)).2

/-- **THE INVERSE BASE CHANGE ON CODES BELOW `θ`**: for bases with `Γ₀ ≤ σ` and `G ∈ T^σ` with `π⁻¹ G < θ`:
`π⁻¹ G = yvSub π⁻¹ G`, and every leaf of `π⁻¹ G` lies in `Tᵗ[σ]`. -/
theorem yv_up {σ τ G : Ordinal.{0}} (h : Bases σ τ) (hσ : gamma 0 ≤ σ) (hG : G ∈ Tset σ)
    (hz : up σ τ G < ConjT.th S) :
    up σ τ G = yvSub S (up σ τ) G ∧ YvLv S (· ∈ TB τ σ) (up σ τ G) := by
  obtain ⟨hzT, hπz⟩ := up_spec h hG
  set z := up σ τ G with hzdef
  have hL := (yv_TB_iff h hz).1 hzT
  obtain ⟨r, hGr, hr⟩ := yv_bound (S := S) hz
  have hid : YvR S id z z := yv_sub_id r z hL hGr hr
  have hcong : YvLv S (fun x => id x = (up σ τ ∘ pi σ τ) x) z :=
    hL.mono fun x hx => (up_pi h hx).symm
  have hR : YvR S (up σ τ ∘ pi σ τ) z z := yvR_congr hcong hid
  have hc := yv_comp h hσ r (up σ τ) z hL hGr hr z hR
  rw [hπz] at hc
  exact ⟨(yvSub_eq hc).symm, hL⟩

end Googology.Trans.PoR.InaccPsi.R2.Yv
