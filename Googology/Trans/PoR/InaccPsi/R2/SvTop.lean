import Googology.Trans.PoR.InaccPsi.R2.SvMove

/-!
# `Ss.SsVtTopHi` on the arguments `[E₁ + Ω₁, Ω₁·M)` under `SvCit M`; the hypothesis reduced to `[Γ_{Ω₁+1}, Ω₂)`

`B_n = Bc.bcB S n`, `c_{n+1} = Bc.bcC S (n + 1)`, `ϑ^β = vt β`, `E₁ = ε_{Ω₁+1}`, `Γ_{Ω₁+1} = Gg.ggGam`, `SpLC` the
level-closed ordinals.  An argument `η ∈ [E₁ + Ω₁, Ω₂)` is `Ω₁·μ + η₀` with the level `μ = η / Ω₁ > E₁` (`Ω₁ + μ = μ`)
and `η₀ = η mod Ω₁`; for `μ < M` it is moved by `Sv.svVtE`:

* `SvVtTopFrom S L` (a hypothesis name: `Sm.SmVtTop` on the arguments `[L, Ω₂)` at every level-closed base;
  `Ss.SsVtTopHi S` is `SvVtTopFrom S (E₁ + Ω₁)`), `svVtTopHi_eq`;
* `svVtTop_mid` (**`B_n(ϑ^β η) = ϑ^{B_n β}(B_n η)` for every level-closed `β < c_{n+1}` and `η ∈ Tᵝ ∩ [E₁ + Ω₁,
  Ω₁·M)`**, under `SvCit M` with `M ≤ Γ_{Ω₁+1}` closed under `B_n` on the codes over `c_{n+1}`);
* `svVtTopHi_of` (**`SvCit M ∧ SvVtTopFrom S (Ω₁·M) ⇒ Ss.SsVtTopHi S`**), `svVtTopHi_iff` (**under `SvCit Γ_{Ω₁+1}`:
  `Ss.SsVtTopHi S ↔ SvVtTopFrom S Γ_{Ω₁+1}`**, i.e. only the arguments `≥ Γ_{Ω₁+1}` (the `ψ_{Ω₂}`-collapses) are left),
  `svVtTopAll_iff` (the same for `Sp.SpVtTopAll`).

No new axiom.  New definition: the hypothesis name `SvVtTopFrom`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Sv

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rk
  Googology.Trans.PoR.InaccPsi.R2.Ss Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Sp

variable {S : InaccSeq.{0}}

/-- **`B_n` commutes with `ϑ^β` on the arguments `[L, Ω₂)` at every level-closed base `β < c_{n+1}`** (a hypothesis
name). -/
def SvVtTopFrom (S : InaccSeq.{0}) (L : Ordinal.{0}) : Prop :=
  ∀ n : ℕ, ∀ β, SpLC β → β < Bc.bcC S (n + 1) → ∀ η ∈ Tset β, L ≤ η → η < OmTwo →
    Bc.bcB S n (vt β η) = vt (Bc.bcB S n β) (Bc.bcB S n η)

theorem svVtTopHi_eq : SsVtTopHi S ↔ SvVtTopFrom S (ggE + Om1) := Iff.rfl

/-- `Ω₁·Γ_{Ω₁+1} = Γ_{Ω₁+1}`. -/
theorem sv_Om1_mul_G : Om1 * ggGam = (ggGam : Ordinal.{0}) := by
  rw [Rj.rj_Om1]
  conv_lhs => rw [← Bt.Om1_opow, ← sv_Gam_inE]
  rw [← opow_add, Ordinal.add_of_omega0_opow_le (by rw [sv_Gam_inE]; exact ggGam_spec.2) sv_Gam_inE.le,
    sv_Gam_inE]

/-- `Ω₁ + μ = μ` for `μ ≥ E₁`. -/
theorem sv_Om1_add_big {μ : Ordinal.{0}} (h : ggE ≤ μ) : Om1 + μ = μ := by
  rw [Rj.rj_Om1]
  exact Ordinal.add_of_omega0_opow_le (by rw [rk_E_inE]; exact rk_Om1_E) (by rw [rk_E_inE]; exact h)

/-- **The middle arguments**: `B_n(ϑ^β η) = ϑ^{B_n β}(B_n η)` for every level-closed `β < c_{n+1}` and
`η ∈ Tᵝ ∩ [E₁ + Ω₁, Ω₁·M)`, under `SvCit M`, `M ≤ Γ_{Ω₁+1}`, with `B_n μ < M` for the codes `E₁ ≤ μ < M` over
`c_{n+1}`. -/
theorem svVtTop_mid {M : Ordinal.{0}} (hC : SvCit M) (hMG : M ≤ ggGam)
    (hMB : ∀ n : ℕ, ∀ μ, ggE ≤ μ → μ < M → GgCl (Bc.bcC S (n + 1)) μ → Bc.bcB S n μ < M)
    {n : ℕ} {β η : Ordinal.{0}} (hβ : SpLC β) (hβc : β < Bc.bcC S (n + 1)) (hη : η ∈ Tset β)
    (hlo : ggE + Om1 ≤ η) (hhi : η < Om1 * M) :
    Bc.bcB S n (vt β η) = vt (Bc.bcB S n β) (Bc.bcB S n η) := by
  have hβE : InE β := gg_SC_eps hβ.1
  have hβ1 : β < Om1 := (Rt.rt_lt_Om1 hβc).1
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  have hcS : SC (Bc.bcC S (n + 1)) := Lw.lw_L_SC S _
  have hO0 : (Om1 : Ordinal.{0}) ≠ 0 := Rj.rj_Om1_pos.ne'
  set μ := η / Om1 with hμdef
  set η0 := η % Om1 with hη0def
  have hdec : Om1 * μ + η0 = η := Ordinal.div_add_mod η Om1
  have hη0Ω : η0 < Om1 := Ordinal.mod_lt η hO0
  have hEμ : ggE + 1 ≤ μ := by
    rw [hμdef]
    refine (Ordinal.mul_le_iff_le_div hO0).1 ?_
    rw [mul_add_one, ss_Om1_mul_E]; exact hlo
  have hEμ0 : ggE ≤ μ := le_self_add.trans hEμ
  have hμM : μ < M := (Ordinal.lt_mul_iff_div_lt hO0).1 hhi
  have hOμ : Om1 + μ = μ := sv_Om1_add_big hEμ0
  have hη2 : η < OmTwo := hhi.trans_le ((mul_le_mul_right hMG _).trans (by rw [sv_Om1_mul_G]; exact sv_G_le_Om2))
  have hη0T : η0 ∈ Tset β := vzRem_T hβE hβ1 hη hη2 hdec.symm (dvd_mul_right _ _) hη0Ω
  have hηeq : Om1 * (Om1 + μ) + η0 = η := by rw [hOμ, hdec]
  have hμT : ssDatL μ ∈ Tset β := svc_dat hC hβE hβ1 hEμ0 hμM hη0Ω (by rw [hηeq]; exact hη)
  -- `μ` is a code over `c_{n+1}`
  have hdx := (svK_facts hC hMG hβ.1 hβ1 hEμ0 hμM hμT hη0T hη0Ω).2.2.2.2.2.2.1
  have hvm := (svK_facts hC hMG hβ.1 hβ1 hEμ0 hμM hμT hη0T hη0Ω).2.2
  have hdc : ssDatL μ < Bc.bcC S (n + 1) := hdx.trans (Si.si_T_lt_c hβE hβc hvm.1 hvm.2.2.1)
  have hμC : GgCl (Bc.bcC S (n + 1)) μ := ss_code_lvl hcS (hμM.trans_le hMG) hdc
  obtain ⟨hDμ, -, -, -⟩ := sv_B_lvl hμC
  have hμ'M : Bc.bcB S n μ < M := hMB n μ hEμ0 hμM hμC
  have hEμ' : ggE ≤ Bc.bcB S n μ := sv_B_geE hDμ hEμ0
  -- `B_n η = Ω₁·B_n μ + B_n η₀`
  have hη0c : η0 < Bc.bcC S (n + 1) := Si.si_T_lt_c hβE hβc hη0T hη0Ω
  obtain ⟨hDm, hBm⟩ := rkB_Om1mul (S := S) (n := n) hcS hLw μ hμC
  rw [← Rj.rj_Om1] at hDm hBm
  have hBη : Bc.bcB S n η = Om1 * (Om1 + Bc.bcB S n μ) + Bc.bcB S n η0 := by
    rw [← hdec, (mvB_add (k := n) hDm (mvD_of_lt (hη0c.trans hLw))).2, hBm, sv_Om1_add_big hEμ']
  rw [hBη, ← hηeq]
  exact svVtE hC hMG hβ hβc hEμ0 hμM hμ'M hμT hη0T hη0Ω

/-- **`SvCit M ∧ SvVtTopFrom S (Ω₁·M) ⇒ Ss.SsVtTopHi S`** (`M ≤ Γ_{Ω₁+1}` closed under `B_n` on the codes). -/
theorem svVtTopHi_of {M : Ordinal.{0}} (hC : SvCit M) (hMG : M ≤ ggGam)
    (hMB : ∀ n : ℕ, ∀ μ, ggE ≤ μ → μ < M → GgCl (Bc.bcC S (n + 1)) μ → Bc.bcB S n μ < M)
    (hTop : SvVtTopFrom S (Om1 * M)) : SsVtTopHi S := by
  intro n β hβ hβc η hη hlo hη2
  rcases lt_or_ge η (Om1 * M) with hhi | hhi
  · exact svVtTop_mid hC hMG hMB hβ hβc hη hlo hhi
  · exact hTop n β hβ hβc η hη hhi hη2

/-- `B_n μ < Γ_{Ω₁+1}` for every code `μ` over `c_{n+1}`. -/
theorem sv_B_G {n : ℕ} {μ : Ordinal.{0}} (hμ : GgCl (Bc.bcC S (n + 1)) μ) : Bc.bcB S n μ < ggGam :=
  ssB_lt_Gam hμ

/-- **Under `SvCit Γ_{Ω₁+1}`: `Ss.SsVtTopHi S ↔ SvVtTopFrom S Γ_{Ω₁+1}`**: only the arguments `≥ Γ_{Ω₁+1}` are left. -/
theorem svVtTopHi_iff (hC : SvCit ggGam) : SsVtTopHi S ↔ SvVtTopFrom S ggGam := by
  constructor
  · intro h n β hβ hβc η hη hG hη2
    have hlo : ggE + Om1 ≤ ggGam :=
      ((Lq.lq_SC_indec ggGam_spec.1).add_lt Ss.ss_E_lt_Gam ss_Om1_lt_Gam).le
    exact h n β hβ hβc η hη (hlo.trans hG) hη2
  · intro h
    refine svVtTopHi_of hC le_rfl (fun n μ _ _ hμ => sv_B_G hμ) ?_
    rw [sv_Om1_mul_G]; exact h

/-- **Under `SvCit Γ_{Ω₁+1}`: `Sp.SpVtTopAll S ↔ SvVtTopFrom S Γ_{Ω₁+1}`.** -/
theorem svVtTopAll_iff (hC : SvCit ggGam) : SpVtTopAll S ↔ SvVtTopFrom S ggGam :=
  ssVtTopAll_iff.trans (svVtTopHi_iff hC)

end Googology.Trans.PoR.InaccPsi.R2.Sv
