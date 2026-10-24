import Googology.Trans.PoR.InaccPsi.R2.TiMove

/-!
# `Sv.SvVtTopFrom` moved from `Γ_{Ω₁+1}` up to `B_Γ`

`B_n = Bc.bcB S n`, `c_{n+1} = Bc.bcC S (n + 1)`, `ϑ^β = vt β`, `E₁ = ε_{Ω₁+1}`, `Γ_{Ω₁+1} = Gg.ggGam`, `B_Γ = Tf.tfBG`
(the least fixed point of `Γ` above `Ω₁`), `SpLC` the level-closed ordinals, `SvVtTopFrom S L` (`R2.SvTop`:
`B_n(ϑ^β η) = ϑ^{B_n β}(B_n η)` on the arguments `[L, Ω₂)` at every level-closed `β < c_{n+1}`).  An argument `η ∈
[E₁ + Ω₁, Ω₁·M)` is `Ω₁·μ + η₀` with the level `μ = η / Ω₁`, `E₁ < μ < M`, and is moved by `Ti.tiVtE`:

* `ti_Om1_mul_BG` (`Ω₁·B_Γ = B_Γ`), `tiVtTop_mid` (**`B_n(ϑ^β η) = ϑ^{B_n β}(B_n η)` for every level-closed
  `β < c_{n+1}` and `η ∈ Tᵝ ∩ [E₁ + Ω₁, Ω₁·M)`**, under `TiCit M`, `M ≤ B_Γ` closed under `B_n` on the codes over
  `c_{n+1}`), `tiVtTopHi_of`, `ti_MB`;
* `tiVtTopHi_iff` (**under `TiCit B_Γ`: `Ss.SsVtTopHi S ↔ SvVtTopFrom S B_Γ`**), `tiVtTopFrom_iff` (**under `TiCit B_Γ`:
  `SvVtTopFrom S Γ_{Ω₁+1} ↔ SvVtTopFrom S B_Γ`**: the arguments in `[Γ_{Ω₁+1}, B_Γ)`, i.e. all levels `μ ∈ [Γ_{Ω₁+1},
  B_Γ)`, with every atom `ψ_{Ω₂}(c)`, `c < B_Γ`, are moved), `tiVtTopAll_iff` (the same for `Sp.SpVtTopAll`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ti

open Googology.Trans.PoR.InaccPsi.R2.Tf Googology.Trans.PoR.InaccPsi.R2.Tc
  Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rk
  Googology.Trans.PoR.InaccPsi.R2.Ss Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Sp
  Googology.Trans.PoR.InaccPsi.R2.Sv

variable {S : InaccSeq.{0}}

/-- `Ω₁·B_Γ = B_Γ`. -/
theorem ti_Om1_mul_BG : Om1 * tfBG = (tfBG : Ordinal.{0}) := by
  rw [Rj.rj_Om1]
  conv_lhs => rw [← Bt.Om1_opow, ← tf_BG_inE]
  rw [← opow_add, Ordinal.add_of_omega0_opow_le (by rw [tf_BG_inE]; exact tf_Om1'_lt_BG) tf_BG_inE.le,
    tf_BG_inE]

/-- **The middle arguments**: `B_n(ϑ^β η) = ϑ^{B_n β}(B_n η)` for every level-closed `β < c_{n+1}` and
`η ∈ Tᵝ ∩ [E₁ + Ω₁, Ω₁·M)`, under `TiCit M`, `M ≤ B_Γ`, with `B_n μ < M` for the codes `E₁ ≤ μ < M` over
`c_{n+1}`. -/
theorem tiVtTop_mid {M : Ordinal.{0}} (hC : TiCit M) (hMG : M ≤ tfBG)
    (hMB : ∀ n : ℕ, ∀ μ, ggE ≤ μ → μ < M → TfCl (Bc.bcC S (n + 1)) μ → Bc.bcB S n μ < M)
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
  have hη2 : η < OmTwo := hhi.trans_le ((mul_le_mul_right hMG _).trans (by rw [ti_Om1_mul_BG]; exact tfBG_le_Om2))
  have hη0T : η0 ∈ Tset β := vzRem_T hβE hβ1 hη hη2 hdec.symm (dvd_mul_right _ _) hη0Ω
  have hηeq : Om1 * (Om1 + μ) + η0 = η := by rw [hOμ, hdec]
  have hμT : tfDatL μ ∈ Tset β := tic_dat hC hβE hβ1 hEμ0 hμM hη0Ω (by rw [hηeq]; exact hη)
  -- `μ` is a code over `c_{n+1}`
  have hdx := (tiK_facts hC ⟨hMG, tfBG_le_Om2⟩ hβ.1 hβ1 hEμ0 hμM hμT hη0T hη0Ω).2.2.2.2.2.2.1
  have hvm := (tiK_facts hC ⟨hMG, tfBG_le_Om2⟩ hβ.1 hβ1 hEμ0 hμM hμT hη0T hη0Ω).2.2
  have hdc : tfDatL μ < Bc.bcC S (n + 1) := hdx.trans (Si.si_T_lt_c hβE hβc hvm.1 hvm.2.2.1)
  have hμC : TfCl (Bc.bcC S (n + 1)) μ := tf_code_lvl hcS (hμM.trans_le hMG) hdc
  obtain ⟨hDμ, -, -, -⟩ := ti_B_lvl hμC (hμM.trans_le hMG)
  have hμ'M : Bc.bcB S n μ < M := hMB n μ hEμ0 hμM hμC
  have hEμ' : ggE ≤ Bc.bcB S n μ := sv_B_geE hDμ hEμ0
  -- `B_n η = Ω₁·B_n μ + B_n η₀`
  have hη0c : η0 < Bc.bcC S (n + 1) := Si.si_T_lt_c hβE hβc hη0T hη0Ω
  obtain ⟨hDm, hBm⟩ := tiB_Om1mul (S := S) (n := n) hcS hLw (Tc.tcB_c_le n) μ hμC
  rw [← Rj.rj_Om1] at hDm hBm
  have hBη : Bc.bcB S n η = Om1 * (Om1 + Bc.bcB S n μ) + Bc.bcB S n η0 := by
    rw [← hdec, (mvB_add (k := n) hDm (mvD_of_lt (hη0c.trans hLw))).2, hBm, sv_Om1_add_big hEμ']
  rw [hBη, ← hηeq]
  exact tiVtE hC ⟨hMG, tfBG_le_Om2⟩ hβ hβc hEμ0 hμM hμ'M hμT hη0T hη0Ω

/-- **`TiCit M ∧ SvVtTopFrom S (Ω₁·M) ⇒ Ss.SsVtTopHi S`** (`M ≤ B_Γ` closed under `B_n` on the codes). -/
theorem tiVtTopHi_of {M : Ordinal.{0}} (hC : TiCit M) (hMG : M ≤ tfBG)
    (hMB : ∀ n : ℕ, ∀ μ, ggE ≤ μ → μ < M → TfCl (Bc.bcC S (n + 1)) μ → Bc.bcB S n μ < M)
    (hTop : SvVtTopFrom S (Om1 * M)) : SsVtTopHi S := by
  intro n β hβ hβc η hη hlo hη2
  rcases lt_or_ge η (Om1 * M) with hhi | hhi
  · exact tiVtTop_mid hC hMG hMB hβ hβc hη hlo hhi
  · exact hTop n β hβ hβc η hη hhi hη2

/-- `B_n μ < B_Γ` for every code `μ < B_Γ` over `c_{n+1}`. -/
theorem ti_MB (n : ℕ) (μ : Ordinal.{0}) (_ : ggE ≤ μ) (hμ : μ < tfBG) (hC : TfCl (Bc.bcC S (n + 1)) μ) :
    Bc.bcB S n μ < tfBG := tiB_lt_BG hC

/-- **Under `TiCit B_Γ`: `Ss.SsVtTopHi S ↔ SvVtTopFrom S B_Γ`.** -/
theorem tiVtTopHi_iff (hC : TiCit tfBG) : SsVtTopHi S ↔ SvVtTopFrom S tfBG := by
  constructor
  · intro h n β hβ hβc η hη hG hη2
    have hlo : ggE + Om1 ≤ tfBG :=
      (tf_BG_indec.add_lt (ggE_le_ggGam.trans_lt tf_gg_lt_BG) tfBG_gt).le
    exact h n β hβ hβc η hη (hlo.trans hG) hη2
  · intro h
    refine tiVtTopHi_of hC le_rfl (fun n μ h1 h2 h3 => ti_MB n μ h1 h2 h3) ?_
    rw [ti_Om1_mul_BG]; exact h

/-- **Under `TiCit B_Γ`: `SvVtTopFrom S Γ_{Ω₁+1} ↔ SvVtTopFrom S B_Γ`.** -/
theorem tiVtTopFrom_iff (hC : TiCit tfBG) : SvVtTopFrom S ggGam ↔ SvVtTopFrom S tfBG :=
  Sy.syVtTopHi_iff.symm.trans (tiVtTopHi_iff hC)

/-- **Under `TiCit B_Γ`: `Sp.SpVtTopAll S ↔ SvVtTopFrom S B_Γ`.** -/
theorem tiVtTopAll_iff (hC : TiCit tfBG) : SpVtTopAll S ↔ SvVtTopFrom S tfBG :=
  Sy.syVtTopAll_iff.trans (tiVtTopFrom_iff hC)

end Googology.Trans.PoR.InaccPsi.R2.Ti
