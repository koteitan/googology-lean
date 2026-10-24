import Googology.Trans.PoR.InaccPsi.R2.SmRoad

/-!
# Level-closed bases: strongly critical fixed points of every level `Φ_μ`, `μ < ε_{Ω₁+1}`

`Φ_μ = Rk.rkP μ`, `rkDat μ` the largest countable leaf of the code `μ` (`Rk.rkDat`), `u_μ = Ω₁^μ = Le.leOe μ`,
`ψ = S.psi · Ω₁`, `B_n = Bc.bcB S n`, `c_n = L(n+1) = Bc.bcC S n`, `ε_{Ω₁+1} = Gg.ggE`.

* `SpLC σ` (**`σ` is level-closed**: `σ` strongly critical and `Φ_μ(σ) = σ` for every `μ < ε_{Ω₁+1}` with
  `rkDat μ < σ`); every `υ`-point below `c_{n+1}` is level-closed (`spLC_ups`, `Rk.rk_ups_fix`);
* `spLC_dvd` (**`σ = ψ(B)` level-closed, `B` own ⇒ `u_{ε_{Ω₁+1}} ∣ B`**), `spLC_of_dvd` (the converse);
* `spLC_img` (**`B_n` keeps level-closed points of `[c_n, c_{n+1})`**: `B_n σ = ψ(B')` with `B'` own and
  `u_{ε_{Ω₁+1}} ∣ B'` by `Rk.rk_dvd_sig` at the code `ε_{Ω₁+1}`, which `B_n` fixes);
* `spE_mem`, `sp_dvd_add_E` (`ε_{Ω₁+1} ∣ B + ε_{Ω₁+1}`), `sp_add_lt_A` (`B < A_η ⇒ B + ε_{Ω₁+1} < A_η`);
* `spLC_exists` (**below every `υ`-point `τ = υ_ξ < c_{n+1}` the level-closed points are unbounded**: for `m < τ`
  a strongly critical `σ₀ = Γ_s ∈ (m, τ)`, `σ₀ = ψ(B₀)`, and `σ = ψ(B₀ + ε_{Ω₁+1}) ∈ (m, τ)` is level-closed).

No new axiom.  New definition: `SpLC` (a property of ordinals, built from `Rk.rkP` and `Rk.rkDat`).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Sp

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rk
  Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Notation.InaccPsi.Term

variable {S : InaccSeq.{0}}

/-- **A level-closed ordinal**: strongly critical, and a fixed point of every level `Φ_μ`, `μ < ε_{Ω₁+1}`, whose
data lie below it. -/
def SpLC (σ : Ordinal.{0}) : Prop :=
  SC σ ∧ ∀ μ, μ < ggE → rkDat μ < σ → rkP μ σ = σ

/-- **Every `υ`-point `υ_ξ < c_{n+1}`, `ξ ≠ 0`, is level-closed.** -/
theorem spLC_ups {n : ℕ} {ξ : Ordinal.{0}} (hξ0 : ξ ≠ 0) (hτc : upsilon ξ < Bc.bcC S (n + 1)) :
    SpLC (upsilon ξ) := by
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  have hτL0 : upsilon ξ < Nm.Pv S (Om ω + Nc.ncPp S * ω) := by rw [← Lw.lw_L_eq S]; exact hτc.trans hLw
  obtain ⟨-, -, -, hpv0⟩ := Cd.cdEta_pv_spec hξ0 hτL0
  have hAL : ConjT.Aη S (Cd.cdEta S ξ) < S.Lam := (Sf.sfA_lt (n := n) (by rw [hpv0]; exact hτc)).2
  exact ⟨Mv.mvUps_SC hξ0 hτL0, rk_ups_fix hξ0 hτL0 hAL⟩

/-- **`σ = ψ(B)` level-closed with `B` own ⇒ `u_{ε_{Ω₁+1}} ∣ B`.** -/
theorem spLC_dvd {B : Ordinal.{0}} (hown : B ∈ S.CSet B (S.psi B (Om 1))) (h : SpLC (S.psi B (Om 1))) :
    Le.leOe ggE ∣ B :=
  rk_dvd_of_range le_rfl hown fun j hj hd => h.2 j hj hd

/-- **`B` own, `B ≠ 0`, `u_{ε_{Ω₁+1}} ∣ B` ⇒ `ψ(B)` level-closed.** -/
theorem spLC_of_dvd {B : Ordinal.{0}} (hown : B ∈ S.CSet B (S.psi B (Om 1))) (hB : Le.leOe ggE ∣ B)
    (hB0 : B ≠ 0) : SpLC (S.psi B (Om 1)) :=
  ⟨SC_psi Low.InR_Om_one B, fun μ hμ hd =>
    rk_fwd μ hμ B hown ((rhU_dvd (Order.add_one_le_of_lt hμ)).trans hB) hB0 hd⟩

/-- `ε_{Ω₁+1}` is a code over every `Z > 1`. -/
theorem spE_cl {Z : Ordinal.{0}} (hZ : 1 < Z) : GgCl Z ggE := by
  rw [rk_E_eq]; exact GgCl.phi (GgCl.small hZ) (GgCl.add GgCl.om (GgCl.small hZ))

/-- **`B_n` keeps level-closed points of `[c_n, c_{n+1})`.** -/
theorem spLC_img {n : ℕ} {σ : Ordinal.{0}} (hσ : SpLC σ) (hc : Bc.bcC S n ≤ σ) (hσc : σ < Bc.bcC S (n + 1)) :
    SpLC (Bc.bcB S n σ) := by
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  have hσW : σ < S.psi (Bc.bcAlphaW S) (Om 1) := by rw [← Bc.ncL_omega_eq S]; exact hσc.trans hLw
  obtain ⟨B, hown, hB⟩ := Rb.rb_own_of_SC hσ.1 hσW
  have hdvd : Le.leOe ggE ∣ B := spLC_dvd hown (by rw [hB]; exact hσ)
  have hcS : SC (Bc.bcC S (n + 1)) := Lw.lw_L_SC S _
  have h0C : GgCl (Bc.bcC S (n + 1)) 0 := GgCl.small (lt_of_le_of_lt zero_le hσc)
  have e0 : B + Le.leOe 0 * 0 = B := by rw [mul_zero, add_zero]
  have hown1 : B + Le.leOe 0 * 0 ∈ S.CSet (B + Le.leOe 0 * 0) (S.psi (B + Le.leOe 0 * 0) (Om 1)) := by
    rw [e0]; exact hown
  obtain ⟨r, hDr, hBr, hownB', hBp', -⟩ := rkB_psi (n := n) h0C hown (by rw [hB]; exact hc) hown1
    (by rw [e0, hB]; exact hσc) (lt_of_lt_of_le zero_lt_one (gg_one_lt_of_SC (SC_Om one_ne_zero)).le)
    (lt_of_le_of_lt zero_le hσc)
  have hEC : GgCl (Bc.bcC S (n + 1)) ggE := spE_cl (gg_one_lt_of_SC hcS)
  rw [hBr, Rd.rd_dvd_add_left (rk_dvd_alpha le_rfl _)] at hdvd
  have hs := rk_dvd_sig (n := n) hEC hDr hdvd
  rw [(rkB_E (S := S) (n := n)).2] at hs
  have hdvd' : Le.leOe ggE ∣ Bc.bcAlphaW S + val S (Bc.bcSig (Bc.bcPre (n + 1)) Bc.bcPreW r) := by
    rw [Rd.rd_dvd_add_left (rk_dvd_alphaW le_rfl)]; exact hs
  have hB'0 : Bc.bcAlphaW S + val S (Bc.bcSig (Bc.bcPre (n + 1)) Bc.bcPreW r) ≠ 0 :=
    (lt_of_lt_of_le (lt_of_le_of_lt zero_le (Bc.bcAlpha_lt_W S 0)) le_self_add).ne'
  rw [← hB, hBp']
  exact spLC_of_dvd hownB' hdvd' hB'0

/-- `ε_{Ω₁+1}` lies in every `C(a, b)`. -/
theorem spE_mem (a b : Ordinal.{0}) : ggE ∈ S.CSet a b := by
  rw [rk_E_eq]
  exact CSet.phi_mem (CSet.one_mem a b) (CSet.add_mem (CSet.Om_mem (CSet.one_mem a b)) (CSet.one_mem a b))

/-- **`ε_{Ω₁+1} ∣ B + ε_{Ω₁+1}`** (`B = ε·q + r`, `r < ε`, `r + ε = ε`). -/
theorem sp_dvd_add_E (B : Ordinal.{0}) : ggE ∣ B + ggE := by
  have hE := ggE_spec.1
  have hr : B % ggE < ggE := Ordinal.mod_lt B (InE.pos hE).ne'
  have hab : B % ggE + ggE = ggE := by
    refine Ordinal.add_of_omega0_opow_le (b := ggE) ?_ ?_
    · rw [hE]; exact hr
    · rw [hE]
  refine ⟨B / ggE + 1, ?_⟩
  conv_lhs => rw [← Ordinal.div_add_mod B ggE]
  rw [add_assoc, hab, mul_add_one]

/-- `ε_{Ω₁+1}` is below every strongly critical `Z > Ω₁`. -/
theorem sp_E_lt_SC {Z : Ordinal.{0}} (hZ : SC Z) (h1 : Om 1 < Z) : ggE < Z := by
  have h1Z : (1 : Ordinal.{0}) < Z := gg_one_lt_of_SC hZ
  rw [rk_E_eq]
  calc veblen 1 (Om 1 + 1) < veblen 1 Z := veblen_lt_veblen_iff_right.2 (hZ.add_one_lt h1)
    _ = Z := hZ.veblen_right h1Z

/-- **`B < A_η ⇒ B + ε_{Ω₁+1} < A_η`** (`A_η = Ω_ω + θ·η`, `θ` strongly critical above `ε_{Ω₁+1}`). -/
theorem sp_add_lt_A {B η : Ordinal.{0}} (h : B < ConjT.Aη S η) : B + ggE < ConjT.Aη S η := by
  unfold ConjT.Aη at h ⊢
  have hWSC : SC (Om (ω : Ordinal.{0})) := SC_Om omega0_pos.ne'
  have hW1 : Om (1 : Ordinal.{0}) < Om ω := Om_lt_Om.2 one_lt_omega0
  have hEW : ggE < Om (ω : Ordinal.{0}) := sp_E_lt_SC hWSC hW1
  have hthSC : SC (ConjT.th S) := ConjT.SC_th S
  have hEth : ggE < ConjT.th S := sp_E_lt_SC hthSC Bt.Om1_lt_th
  rcases lt_or_ge B (Om ω) with hBW | hBW
  · exact ((Lq.lq_SC_indec hWSC).add_lt hBW hEW).trans_le le_self_add
  · obtain ⟨d, rfl⟩ := exists_add_of_le hBW
    rw [add_assoc]
    refine (add_lt_add_iff_left _).2 ?_
    have hd : d < ConjT.th S * η := (add_lt_add_iff_left _).1 h
    have hth0 : ConjT.th S ≠ 0 := (lt_of_le_of_lt zero_le hEth).ne'
    have hq : d / ConjT.th S < η := (Ordinal.lt_mul_iff_div_lt hth0).1 hd
    have hr : d % ConjT.th S < ConjT.th S := Ordinal.mod_lt d hth0
    conv_lhs => rw [← Ordinal.div_add_mod d (ConjT.th S)]
    rw [add_assoc]
    calc ConjT.th S * (d / ConjT.th S) + (d % ConjT.th S + ggE)
        < ConjT.th S * (d / ConjT.th S) + ConjT.th S :=
          (add_lt_add_iff_left _).2 ((Lq.lq_SC_indec hthSC).add_lt hr hEth)
      _ = ConjT.th S * (d / ConjT.th S + 1) := by rw [mul_add_one]
      _ ≤ ConjT.th S * η := mul_le_mul_right (Order.add_one_le_of_lt hq) _

/-- **The level-closed points are unbounded below every `υ`-point `τ = υ_ξ < c_{n+1}`**: for `m < τ` there is a
level-closed `σ` with `m < σ < τ`. -/
theorem spLC_exists {n : ℕ} {ξ m : Ordinal.{0}} (hξ0 : ξ ≠ 0) (hτc : upsilon ξ < Bc.bcC S (n + 1))
    (hm : m < upsilon ξ) : ∃ σ, SpLC σ ∧ m < σ ∧ σ < upsilon ξ := by
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  have hτL0 : upsilon ξ < Nm.Pv S (Om ω + Nc.ncPp S * ω) := by rw [← Lw.lw_L_eq S]; exact hτc.trans hLw
  obtain ⟨hg0, -, -, hpv0⟩ := Cd.cdEta_pv_spec hξ0 hτL0
  set A := ConjT.Aη S (Cd.cdEta S ξ) with hAdef
  have hpvA : S.psi A (Om 1) = upsilon ξ := hpv0
  have hAL : A < S.Lam := (Sf.sfA_lt (n := n) (by rw [hpv0]; exact hτc)).2
  have hownA : A ∈ S.CSet A (S.psi A (Om 1)) := Sf.sfOwn hg0 hAL
  have hτLC : SpLC (upsilon ξ) := spLC_ups hξ0 hτc
  -- a strongly critical `σ₀ = Φ_0(s) ∈ (m, τ)`
  have hτ0 : rkP 0 (upsilon ξ) = upsilon ξ := hτLC.2 0 (InE.pos ggE_spec.1) (by
    rw [rkDat_zero]; exact (gg_one_lt_of_SC hτLC.1).trans' zero_lt_one)
  have hlim : IsSuccLimit (upsilon ξ) := ev_isSuccLimit_of_inE (gg_SC_eps hτLC.1)
  obtain ⟨s, hs, hms⟩ := ((rkP_normal 0).lt_iff_exists_lt hlim).1 (by rw [hτ0]; exact hm)
  have hσ0τ : rkP 0 s < upsilon ξ := by rw [← hτ0]; exact (rkP_normal 0).strictMono hs
  have hσ0W : rkP 0 s < S.psi (Bc.bcAlphaW S) (Om 1) := by
    rw [← Bc.ncL_omega_eq S]; exact (hσ0τ.trans hτc).trans hLw
  obtain ⟨B0, hown0, hB0⟩ := Rb.rb_own_of_SC (rkP_SC 0 s) hσ0W
  -- `σ = ψ(B₀ + ε_{Ω₁+1})`
  have hown1 : B0 + ggE ∈ S.CSet (B0 + ggE) (S.psi (B0 + ggE) (Om 1)) :=
    CSet.add_mem ((psi_mono Low.InR_Om_one (le_self_add : B0 ≤ B0 + ggE)).2 hown0) (spE_mem _ _)
  have hdvd : Le.leOe ggE ∣ B0 + ggE :=
    (rk_dvd_eps le_rfl ggE_spec.1 ggE_spec.2).trans (sp_dvd_add_E B0)
  have hne : B0 + ggE ≠ 0 := (lt_of_lt_of_le (InE.pos ggE_spec.1) le_add_self).ne'
  refine ⟨S.psi (B0 + ggE) (Om 1), spLC_of_dvd hown1 hdvd hne, ?_, ?_⟩
  · calc m < rkP 0 s := hms
      _ = S.psi B0 (Om 1) := hB0.symm
      _ ≤ S.psi (B0 + ggE) (Om 1) := (psi_mono Low.InR_Om_one le_self_add).1
  · have hB0A : B0 < A := by
      by_contra hle
      push Not at hle
      have h := (psi_mono (S := S) Low.InR_Om_one hle).1
      rw [hpvA, hB0] at h
      exact absurd hσ0τ (not_lt.2 h)
    rw [← hpvA]
    exact psi_lt_psi Low.InR_Om_one (sp_add_lt_A hB0A) hown1

end Googology.Trans.PoR.InaccPsi.R2.Sp
