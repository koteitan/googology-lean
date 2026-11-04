import Googology.Trans.PoR.InaccPsi.R2.YvSub

/-!
# The base change on codes below `θ` is the leaf substitution

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`π = pi σ τ`, `Tᵗ[σ] = TB τ σ`, `θ = ConjT.th S`, `θ_s = ψ_{Ω_{s+1}}(Ω_ω)`, `Vs.VsG S r` the bound of the visibility
induction of `Vs.vsComm` / `Xe.xe_pi_fix`.  `Vc.vc_pi` says: below `B₂` a code whose leaves lie in `Tᵗ[σ]` lies in
`Tᵗ[σ]` and `π z = vcSub π z`.  Here the same is proved for **every code below `θ`** (and every code of the higher
cardinal levels below `θ_s` that occurs as a part), by induction on the canonical decomposition `Yv.YvLv`:

* `yv_pkg` (the base-change package `Vs.VsPkg` at the cardinal of the code: `Vs.vsPkg_one` on `[B₂, θ)`,
  `Vs.vsPkg_gen` on `[Ω_s, θ_s)`);
* `yv_pi` (**THE BASE CHANGE ON CODES BELOW `θ`: leaves in `Tᵗ[σ]` ⇒ `z ∈ Tᵗ[σ]` and `YvR π z (π z)`, i.e.
  `π z = yvSub π z`**), `yv_pi_th` (the same for every `z < θ`, with no bound hypothesis), `yv_pi_sub`;
* `yv_node_pi` (**the base change of a `ϑ`-node whose level `Γ < θ` carries moving leaves**: `π(ϑᵗ(Γ + ρ)) =
  ϑ^σ(yvSub π Γ + π ρ)`; `R2.pi_vt_two`, `R2.pi_add`).

Axioms: those of `R2.CitedVd`, `R2.CitedVp`, `R2.CitedEv` (`pi_vt_two`) and of `Vc.vc_pi`.  No new axiom, no new
definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yv

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Ul Googology.Trans.PoR.InaccPsi.R2.Uc
  Googology.Trans.PoR.InaccPsi.R2.Vs

variable {S : InaccSeq.{0}}

/-- **The base-change package at the cardinal of a code `ξ ≥ B₂`, `Ω_s < ξ`.** -/
theorem yv_pkg {s : Ordinal.{0}} (hs1 : 1 ≤ s) (hs : s < ω) (r : ℕ) {ξ : Ordinal.{0}} (h1 : Om s < ξ)
    (hB : ucB ≤ ξ) :
    ∃ L U G, VsPkg S s L U G ∧ L ≤ ξ ∧ ω ^ G ≤ ξ ∧ S.psi (Om ((r : Ordinal.{0}) + 1)) (Om (s + 1)) ≤ U := by
  have hrω : ((r : Ordinal.{0}) + 1) < ω := vs_nat_lt_omega r
  have hEω : Om ((r : Ordinal.{0}) + 1) ≤ Om ω := Om_le_Om.2 hrω.le
  rcases hs1.lt_or_eq with hs2 | hs2
  · refine ⟨Om s, S.psi (Om ω) (Om (s + 1)), Om s, vsPkg_gen hs hs2, h1.le, ?_,
      (psi_mono (InR_Om_succ s) hEω).1⟩
    have hΩE : ω ^ (Om s : Ordinal.{0}) = Om s := Low.opow_eq_self_of_SC (SC_Om (lt_of_lt_of_le zero_lt_one hs1).ne')
    rw [hΩE]; exact h1.le
  · subst hs2
    refine ⟨ucB, ConjT.th S, Gg.ggE, vsPkg_one, hB, ?_, (psi_mono (InR_Om_succ 1) hEω).1⟩
    rw [Rk.rk_E_inE]; exact Vm.vm_E_le_B.trans hB

/-- `VsG` passes to parts. -/
theorem yv_G_sub {r : ℕ} {b ξ : Ordinal.{0}} (hG : VsG S r ξ) (hb : VsSub S b ξ) : VsG S r b :=
  fun i hi1 hi =>
    hb i hi1 hi _ (Ui.ui_psi_SC (s := i) _) (Ui.ui_L_lt_psi (s := i) _) (Ui.ui_psi_lt (s := i) _).le (hG i hi1 hi)

/-- **The base change on codes below `θ` is the leaf substitution.** -/
theorem yv_pi {σ τ : Ordinal.{0}} (h : Bases σ τ) (r : ℕ) :
    ∀ ξ, YvLv S (· ∈ TB τ σ) ξ → VsG S r ξ → ξ < Om ((r : Ordinal.{0}) + 1) →
      ξ ∈ TB τ σ ∧ YvR S (pi σ τ) ξ (pi σ τ ξ) := by
  intro ξ hL
  induction hL with
  | low hz hLv =>
    intro _ _
    obtain ⟨hT, hπ⟩ := Vc.vc_pi h _ hz hLv
    refine ⟨hT, ?_⟩
    rw [hπ]; exact YvR.low hz
  | om hs hs' e =>
    intro _ _
    subst e
    obtain ⟨hT, hπ⟩ := vsOm_TB h hs' hs
    refine ⟨hT, ?_⟩
    rw [hπ]; exact YvR.om hs hs' rfl
  | @cnf s ξ hs1 hs h1 h2 hB hE _ _ ihg ihr =>
    intro hG hr
    have hξ0 : ξ ≠ 0 := (lt_of_le_of_lt zero_le h1).ne'
    set l := log ω ξ with hldef
    have hlξ : l < ξ := Ss.ss_log_lt hξ0 hE
    have hmξ : ξ % ω ^ l < ξ := Rj.rj_mod_lt hξ0
    have hgsub : VsSub S l ξ := fun i _ _ q' hq' _ _ hK' => (ulK_dec hq' ξ hK').2
    have hrsub : VsSub S (ξ % ω ^ l) ξ := fun i _ _ q' hq' _ _ hK' => ulK_mod hq' ξ hK' _
    obtain ⟨hlT, hlR⟩ := ihg (yv_G_sub hG hgsub) (hlξ.trans hr)
    obtain ⟨hmT, hmR⟩ := ihr (yv_G_sub hG hrsub) (hmξ.trans hr)
    obtain ⟨L, U, G, hP, hLξ, hGξ, hUE⟩ := yv_pkg (S := S) hs1 hs r h1 hB
    have hξE : ξ < S.psi (Om ((r : Ordinal.{0}) + 1)) (Om (s + 1)) :=
      ulK_lt_W hs (Ui.ui_psi_SC _) (Ui.ui_L_lt_psi _) (hG s hs1 hs) h2
    have hξU : ξ < U := hξE.trans_le hUE
    have hpξ : ω ^ l ≤ ξ := opow_log_le_self ω hξ0
    -- the power `ω^l`
    have hpw : ω ^ l ∈ TB τ σ ∧
        pi σ τ (ω ^ l) = (if ω ^ l = l then pi σ τ l else ω ^ pi σ τ l) := by
      by_cases hlE : ω ^ l = l
      · rw [if_pos hlE, hlE]; exact ⟨hlT, rfl⟩
      · rw [if_neg hlE]
        have hGl : G ≤ l := le_log_of_opow_le one_lt_omega0 hGξ
        obtain ⟨hiff, hπp⟩ := hP.opow h hGl hlE (hpξ.trans_lt hξU)
        exact ⟨hiff.2 hlT, hπp hlT⟩
    -- the coefficient is finite
    have hpos : ω ^ l ≠ 0 := opow_ne_zero _ omega0_ne_zero
    have hlt : ξ < ω ^ l * ω := by
      rw [← opow_succ]; exact lt_opow_succ_log_self one_lt_omega0 ξ
    obtain ⟨n, hn⟩ := lt_omega0.1 ((Ordinal.div_lt hpos).2 hlt)
    have hdec : ω ^ l * (n : Ordinal.{0}) + ξ % ω ^ l = ξ := by
      rw [← hn]; exact Ordinal.div_add_mod _ _
    obtain ⟨hk1, hk2⟩ := pi_mul_nat h hpw.1 hpw.2 n
    obtain ⟨c1, c2⟩ := pi_add h hk1 hmT
    rw [hdec] at c1 c2
    refine ⟨c1, ?_⟩
    have hR := YvR.cnf (S := S) (f := pi σ τ) hs1 hs h1 h2 hB hE hlR hmR
    rw [hn] at hR
    rw [c2, hk2]
    exact hR
  | @veb s ξ hs1 hs h1 h2 hB hE hS _ _ iha ihc =>
    intro hG hr
    obtain ⟨L, U, G, hP, hLξ, -, hUE⟩ := yv_pkg (S := S) hs1 hs r h1 hB
    have hξE : ξ < S.psi (Om ((r : Ordinal.{0}) + 1)) (Om (s + 1)) :=
      ulK_lt_W hs (Ui.ui_psi_SC _) (Ui.ui_L_lt_psi _) (hG s hs1 hs) h2
    have hξU : ξ < U := hξE.trans_le hUE
    rcases vsShape (S := S) hs hs1 h1 hξE with ⟨hE', -⟩ | ⟨-, -, ha1, haξ, hcξ, hev⟩ | ⟨hSC, -⟩
    · exact absurd hE hE'
    · have hasub : VsSub S (invVeblen₁ ξ) ξ := fun i _ _ q' hq' _ _ hK' =>
        (Uo.uoK_veb (by rw [hev]; exact hK') (by rw [hev]; exact haξ) (by rw [hev]; exact hcξ)).1
      have hcsub : VsSub S (invVeblen₂ ξ) ξ := fun i _ _ q' hq' _ _ hK' =>
        (Uo.uoK_veb (by rw [hev]; exact hK') (by rw [hev]; exact haξ) (by rw [hev]; exact hcξ)).2
      obtain ⟨haT, haR⟩ := iha (yv_G_sub hG hasub) (haξ.trans hr)
      obtain ⟨hcT, hcR⟩ := ihc (yv_G_sub hG hcsub) (hcξ.trans hr)
      have hepsξ := hP.eps h ha1 (by rw [hev]; exact haξ) (by rw [hev]; exact hcξ) (by rw [hev]; exact hLξ)
        (by rw [hev]; exact hξU)
      rw [hev] at hepsξ
      refine ⟨hepsξ.1.2 ⟨haT, hcT⟩, ?_⟩
      have hR := YvR.veb (S := S) (f := pi σ τ) hs1 hs h1 h2 hB hE hS haR hcR
      have e := hepsξ.2 haT hcT
      rw [e]; exact hR
    · exact absurd hSC hS
  | @atom s ξ hs1 hs h1 h2 hB hSC _ _ ihl ihy =>
    intro hG hr
    obtain ⟨L, U, G, hP, hLξ, -, hUE⟩ := yv_pkg (S := S) hs1 hs r h1 hB
    have hξE : ξ < S.psi (Om ((r : Ordinal.{0}) + 1)) (Om (s + 1)) :=
      ulK_lt_W hs (Ui.ui_psi_SC _) (Ui.ui_L_lt_psi _) (hG s hs1 hs) h2
    have hξU : ξ < U := hξE.trans_le hUE
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
    obtain ⟨hyT, hyR⟩ := ihy (yv_G_sub hG hyS) (hyξ.trans hr)
    have hlF : l ∈ TB τ σ ∧ YvR S (pi σ τ) l (pi σ τ l) := by
      rcases lt_or_ge l (Om (s + 1)) with hlW | hlW
      · have hlξ : l < ξ := ulK_lt_W hs hSC h1 hlK hlW
        exact ihl (yv_G_sub hG (vs_sub_of_low (fun i hi1 his q' hq' hLq hqW hK' =>
          (hlow i hi1 his q' hq' hLq hqW hK').1) hlξ.le h2)) (hlξ.trans hr)
      · obtain ⟨hGl, hlr⟩ := vs_lev_G hs hlV hy hlW (by rw [hnf]; exact hG) (by rw [hnf]; exact hξE)
        exact ihl hGl hlr
    have hat := hP.atom h hlV hy (by rw [hnf]; exact hLξ) (by rw [hnf]; exact hξU)
    rw [hnf] at hat
    refine ⟨hat.1.2 ⟨hlF.1, hyT⟩, ?_⟩
    have hR := YvR.atom (S := S) (f := pi σ τ) hs1 hs h1 h2 hB hSC hlF.2 hyR
    have e := hat.2 hlF.1 hyT
    rw [e]; exact hR

/-- **Every code below `θ` whose leaves lie in `Tᵗ[σ]`** lies in `Tᵗ[σ]`, and `π z = yvSub π z`. -/
theorem yv_pi_th {σ τ z : Ordinal.{0}} (h : Bases σ τ) (hz : z < ConjT.th S) (hL : YvLv S (· ∈ TB τ σ) z) :
    z ∈ TB τ σ ∧ YvR S (pi σ τ) z (pi σ τ z) := by
  obtain ⟨r, hr1, hzr⟩ := vs_th_bound hz
  exact yv_pi h r z hL (vs_G_of_W2 hzr)
    ((hzr.trans (Ui.ui_psi_lt (s := 1) _)).trans_le (vs_W2_le hr1))

theorem yv_pi_sub {σ τ z : Ordinal.{0}} (h : Bases σ τ) (hz : z < ConjT.th S) (hL : YvLv S (· ∈ TB τ σ) z) :
    z ∈ TB τ σ ∧ pi σ τ z = yvSub S (pi σ τ) z := by
  obtain ⟨hT, hR⟩ := yv_pi_th h hz hL
  exact ⟨hT, (yvSub_eq hR).symm⟩

/-- **The base change of a `ϑ`-node whose level carries moving leaves**: for bases `σ < τ`, a level `Γ < θ` whose
leaves lie in `Tᵗ[σ]`, `ρ ∈ Tᵗ[σ] ∩ Ω₁` and `Γ + ρ < Ω₂`: the node lies in `Tᵗ[σ]` and `π(ϑᵗ(Γ + ρ)) =
ϑ^σ(yvSub π Γ + π ρ)`. -/
theorem yv_node_pi {σ τ Γ ρ : Ordinal.{0}} (h : Bases σ τ) (hΓ : Γ < ConjT.th S)
    (hL : YvLv S (· ∈ TB τ σ) Γ) (hρ : ρ ∈ TB τ σ) (h2 : Γ + ρ < OmTwo) :
    Γ + ρ ∈ TB τ σ ∧ pi σ τ (vt τ (Γ + ρ)) = vt σ (yvSub S (pi σ τ) Γ + pi σ τ ρ) := by
  obtain ⟨hΓT, hΓπ⟩ := yv_pi_sub (S := S) h hΓ hL
  obtain ⟨c1, c2⟩ := pi_add h hΓT hρ
  refine ⟨c1, ?_⟩
  rw [pi_vt_two h c1 h2, c2, hΓπ]

end Googology.Trans.PoR.InaccPsi.R2.Yv
