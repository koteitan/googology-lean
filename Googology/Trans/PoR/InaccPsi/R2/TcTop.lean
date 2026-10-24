import Googology.Trans.PoR.InaccPsi.R2.TcMove

/-!
# `Sv.SvVtTopFrom` moved from `Γ_{Ω₁+1}` up to `Γ'` under `TcCit Γ'`

`B_n = Bc.bcB S n`, `c_{n+1} = Bc.bcC S (n + 1)`, `ϑ^β = vt β`, `E₁ = ε_{Ω₁+1}`, `Γ_{Ω₁+1} = Gg.ggGam`, `Γ' = lgGam'`
(the least strongly critical ordinal above `Γ_{Ω₁+1}`), `SpLC` the level-closed ordinals, `SvVtTopFrom S L` (`R2.SvTop`:
`B_n(ϑ^β η) = ϑ^{B_n β}(B_n η)` on the arguments `[L, Ω₂)` at every level-closed `β < c_{n+1}`).  An argument `η ∈
[E₁ + Ω₁, Ω₁·M)` is `Ω₁·μ + η₀` with the level `μ = η / Ω₁`, `E₁ < μ < M`, and is moved by `Tc.tcVtE`:

* `tcVtTop_mid` (**`B_n(ϑ^β η) = ϑ^{B_n β}(B_n η)` for every level-closed `β < c_{n+1}` and `η ∈ Tᵝ ∩ [E₁ + Ω₁,
  Ω₁·M)`**, under `TcCit M`, `M ≤ Γ'` closed under `B_n` on the codes over `c_{n+1}`), `tcVtTopHi_of`;
* `tcVtTopHi_iff` (**under `TcCit Γ'`: `Ss.SsVtTopHi S ↔ SvVtTopFrom S Γ'`**), `tcVtTopFrom_iff` (**under `TcCit Γ'`:
  `SvVtTopFrom S Γ_{Ω₁+1} ↔ SvVtTopFrom S Γ'`**: the arguments in `[Γ_{Ω₁+1}, Γ')`, i.e. all levels `μ ∈ [Γ_{Ω₁+1},
  Γ')`, among them the first sub-range `[Γ_{Ω₁+1}, ε_{Γ_{Ω₁+1}+1})`, are moved), `tcVtTopAll_iff` (the same for
  `Sp.SpVtTopAll`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Tc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rk
  Googology.Trans.PoR.InaccPsi.R2.Ss Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Sp
  Googology.Trans.PoR.InaccPsi.R2.Sv

variable {S : InaccSeq.{0}}

/-- `Ω₁·Γ' = Γ'`. -/
theorem tc_Om1_mul_G' : Om1 * lgGam' = (lgGam' : Ordinal.{0}) := by
  rw [Rj.rj_Om1]
  conv_lhs => rw [← Bt.Om1_opow, ← tc_G'_inE]
  rw [← opow_add, Ordinal.add_of_omega0_opow_le (by rw [tc_G'_inE]; exact tc_Om1'_lt_G') tc_G'_inE.le,
    tc_G'_inE]

/-- **The middle arguments**: `B_n(ϑ^β η) = ϑ^{B_n β}(B_n η)` for every level-closed `β < c_{n+1}` and
`η ∈ Tᵝ ∩ [E₁ + Ω₁, Ω₁·M)`, under `SvCit M`, `M ≤ Γ_{Ω₁+1}`, with `B_n μ < M` for the codes `E₁ ≤ μ < M` over
`c_{n+1}`. -/
theorem tcVtTop_mid {M : Ordinal.{0}} (hC : TcCit M) (hMG : M ≤ lgGam')
    (hMB : ∀ n : ℕ, ∀ μ, ggE ≤ μ → μ < M → LgCl (Bc.bcC S (n + 1)) μ → Bc.bcB S n μ < M)
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
  have hη2 : η < OmTwo := hhi.trans_le ((mul_le_mul_right hMG _).trans (by rw [tc_Om1_mul_G']; exact tc_G'_le_Om2 S))
  have hη0T : η0 ∈ Tset β := vzRem_T hβE hβ1 hη hη2 hdec.symm (dvd_mul_right _ _) hη0Ω
  have hηeq : Om1 * (Om1 + μ) + η0 = η := by rw [hOμ, hdec]
  have hμT : tcDatL μ ∈ Tset β := tcc_dat hC hβE hβ1 hEμ0 hμM hη0Ω (by rw [hηeq]; exact hη)
  -- `μ` is a code over `c_{n+1}`
  have hdx := (tcK_facts hC ⟨hMG, tc_G'_le_Om2 S⟩ hβ.1 hβ1 hEμ0 hμM hμT hη0T hη0Ω).2.2.2.2.2.2.1
  have hvm := (tcK_facts hC ⟨hMG, tc_G'_le_Om2 S⟩ hβ.1 hβ1 hEμ0 hμM hμT hη0T hη0Ω).2.2
  have hdc : tcDatL μ < Bc.bcC S (n + 1) := hdx.trans (Si.si_T_lt_c hβE hβc hvm.1 hvm.2.2.1)
  have hμC : LgCl (Bc.bcC S (n + 1)) μ := tc_code_lvl hcS (hμM.trans_le hMG) hdc
  obtain ⟨hDμ, -, -, -⟩ := tc_B_lvl hμC (hμM.trans_le hMG)
  have hμ'M : Bc.bcB S n μ < M := hMB n μ hEμ0 hμM hμC
  have hEμ' : ggE ≤ Bc.bcB S n μ := sv_B_geE hDμ hEμ0
  -- `B_n η = Ω₁·B_n μ + B_n η₀`
  have hη0c : η0 < Bc.bcC S (n + 1) := Si.si_T_lt_c hβE hβc hη0T hη0Ω
  obtain ⟨hDm, hBm⟩ := tcB_Om1mul (S := S) (n := n) hcS hLw μ hμC
  rw [← Rj.rj_Om1] at hDm hBm
  have hBη : Bc.bcB S n η = Om1 * (Om1 + Bc.bcB S n μ) + Bc.bcB S n η0 := by
    rw [← hdec, (mvB_add (k := n) hDm (mvD_of_lt (hη0c.trans hLw))).2, hBm, sv_Om1_add_big hEμ']
  rw [hBη, ← hηeq]
  exact tcVtE hC ⟨hMG, tc_G'_le_Om2 S⟩ hβ hβc hEμ0 hμM hμ'M hμT hη0T hη0Ω

/-- **`SvCit M ∧ SvVtTopFrom S (Ω₁·M) ⇒ Ss.SsVtTopHi S`** (`M ≤ Γ_{Ω₁+1}` closed under `B_n` on the codes). -/
theorem tcVtTopHi_of {M : Ordinal.{0}} (hC : TcCit M) (hMG : M ≤ lgGam')
    (hMB : ∀ n : ℕ, ∀ μ, ggE ≤ μ → μ < M → LgCl (Bc.bcC S (n + 1)) μ → Bc.bcB S n μ < M)
    (hTop : SvVtTopFrom S (Om1 * M)) : SsVtTopHi S := by
  intro n β hβ hβc η hη hlo hη2
  rcases lt_or_ge η (Om1 * M) with hhi | hhi
  · exact tcVtTop_mid hC hMG hMB hβ hβc hη hlo hhi
  · exact hTop n β hβ hβc η hη hhi hη2

/-- `B_n μ < Γ'` for every code `μ < Γ'` over `c_{n+1}`. -/
theorem tc_MB (n : ℕ) (μ : Ordinal.{0}) (_ : ggE ≤ μ) (hμ : μ < lgGam') (hC : LgCl (Bc.bcC S (n + 1)) μ) :
    Bc.bcB S n μ < lgGam' := tcB_lt_G' hC hμ

/-- **Under `TcCit Γ'`: `Ss.SsVtTopHi S ↔ SvVtTopFrom S Γ'`.** -/
theorem tcVtTopHi_iff (hC : TcCit lgGam') : SsVtTopHi S ↔ SvVtTopFrom S lgGam' := by
  constructor
  · intro h n β hβ hβc η hη hG hη2
    have hlo : ggE + Om1 ≤ lgGam' :=
      (tc_G'_indec.add_lt (ggE_le_ggGam.trans_lt tc_Gam_lt_G') tc_Om1_lt_G').le
    exact h n β hβ hβc η hη (hlo.trans hG) hη2
  · intro h
    refine tcVtTopHi_of hC le_rfl (fun n μ h1 h2 h3 => tc_MB n μ h1 h2 h3) ?_
    rw [tc_Om1_mul_G']; exact h

/-- **Under `TcCit Γ'`: `SvVtTopFrom S Γ_{Ω₁+1} ↔ SvVtTopFrom S Γ'`.** -/
theorem tcVtTopFrom_iff (hC : TcCit lgGam') : SvVtTopFrom S ggGam ↔ SvVtTopFrom S lgGam' :=
  Sy.syVtTopHi_iff.symm.trans (tcVtTopHi_iff hC)

/-- **Under `TcCit Γ'`: `Sp.SpVtTopAll S ↔ SvVtTopFrom S Γ'`.** -/
theorem tcVtTopAll_iff (hC : TcCit lgGam') : SpVtTopAll S ↔ SvVtTopFrom S lgGam' :=
  Sy.syVtTopAll_iff.trans (tcVtTopFrom_iff hC)

end Googology.Trans.PoR.InaccPsi.R2.Tc
