import Googology.Trans.PoR.InaccPsi.R2.UfVt
import Googology.Trans.PoR.InaccPsi.R2.TzRoad

/-!
# `Sv.SvVtTopFrom` moved from `Γ_{Ω₁+1}` (and from `X`) up to `B₂`

`B_n = Bc.bcB S n`, `c_{n+1} = Bc.bcC S (n + 1)`, `ϑ^β = vt β`, `E₁ = ε_{Ω₁+1}`, `Γ_{Ω₁+1} = Gg.ggGam`,
`X = Tl.tlX`, `B₂ = Uc.ucB = ψ_{Ω₂}(ε_{Ω₂+1})`, `SpLC` the level-closed ordinals, `SvVtTopFrom S L` (`R2.SvTop`:
`B_n(ϑ^β η) = ϑ^{B_n β}(B_n η)` on the arguments `[L, Ω₂)` at every level-closed `β < c_{n+1}`).  The proofs of
`R2.TzTop` with the bound `B₂`, the package `Uc.UcCit` and the move `Uf.ufVtE`:

* `uf_Om1_mul_B` (`Ω₁·B₂ = B₂`), `ufVtTop_mid` (**`B_n(ϑ^β η) = ϑ^{B_n β}(B_n η)` for every level-closed
  `β < c_{n+1}` and `η ∈ Tᵝ ∩ [E₁ + Ω₁, Ω₁·M)`**, under `UcCit M`, `M ≤ B₂` closed under `B_n` on the codes over
  `c_{n+1}`), `ufVtTopHi_of`, `uf_MB2`;
* `ufVtTopHi_iff` (**under `UcCit B₂`: `Ss.SsVtTopHi S ↔ SvVtTopFrom S B₂`**), `ufVtTopFrom_iff`, `ufVtTopAll_iff`;
* with `Uc.ucCit` (no hypothesis): `ufVtTopFrom_XB` (**`SvVtTopFrom S X ↔ SvVtTopFrom S B₂`**), `ufVtTopFrom_G`
  (**`SvVtTopFrom S Γ_{Ω₁+1} ↔ SvVtTopFrom S B₂`**), `ufVtTopFrom_BG`, `ufVtTopAll`.

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Uf

open Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Tw Googology.Trans.PoR.InaccPsi.R2.Ti
  Googology.Trans.PoR.InaccPsi.R2.Tf Googology.Trans.PoR.InaccPsi.R2.Tc
  Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rk
  Googology.Trans.PoR.InaccPsi.R2.Ss Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Sp
  Googology.Trans.PoR.InaccPsi.R2.Sv

variable {S : InaccSeq.{0}}

/-- `Ω₁·B₂ = B₂`. -/
theorem uf_Om1_mul_B : Om1 * ucB = (ucB : Ordinal.{0}) := by
  rw [Rj.rj_Om1]
  conv_lhs => rw [← Bt.Om1_opow, ← uf_B_inE]
  rw [← opow_add, Ordinal.add_of_omega0_opow_le (by rw [uf_B_inE]; exact uf_Om1_lt_B) uf_B_inE.le,
    uf_B_inE]

/-- **The middle arguments**: `B_n(ϑ^β η) = ϑ^{B_n β}(B_n η)` for every level-closed `β < c_{n+1}` and
`η ∈ Tᵝ ∩ [E₁ + Ω₁, Ω₁·M)`, under `UcCit M`, `M ≤ X`, with `B_n μ < M` for the codes `E₁ ≤ μ < M` over
`c_{n+1}`. -/
theorem ufVtTop_mid {M : Ordinal.{0}} (hC : UcCit M) (hMG : M ≤ ucB)
    (hMB : ∀ n : ℕ, ∀ μ, ggE ≤ μ → μ < M → UcCl (Bc.bcC S (n + 1)) μ → Bc.bcB S n μ < M)
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
  have hη2 : η < OmTwo := hhi.trans_le ((mul_le_mul_right hMG _).trans (by rw [uf_Om1_mul_B]; exact ucB_lt_Om2.le))
  have hη0T : η0 ∈ Tset β := vzRem_T hβE hβ1 hη hη2 hdec.symm (dvd_mul_right _ _) hη0Ω
  have hηeq : Om1 * (Om1 + μ) + η0 = η := by rw [hOμ, hdec]
  have hμT : ucDatL μ ∈ Tset β := ufc_dat hC hβE hβ1 hEμ0 hμM hη0Ω (by rw [hηeq]; exact hη)
  -- `μ` is a code over `c_{n+1}`
  have hdx := (ufK_facts hC ⟨hMG, ucB_lt_Om2.le⟩ hβ.1 hβ1 hEμ0 hμM hμT hη0T hη0Ω).2.2.2.2.2.2.1
  have hvm := (ufK_facts hC ⟨hMG, ucB_lt_Om2.le⟩ hβ.1 hβ1 hEμ0 hμM hμT hη0T hη0Ω).2.2
  have hdc : ucDatL μ < Bc.bcC S (n + 1) := hdx.trans (Si.si_T_lt_c hβE hβc hvm.1 hvm.2.2.1)
  have hμC : UcCl (Bc.bcC S (n + 1)) μ := uc_code_lvlL hcS (uf_c_le n) (hμM.trans_le hMG) hdc
  obtain ⟨hDμ, -, -, -⟩ := uf_B_lvl hμC (hμM.trans_le hMG)
  have hμ'M : Bc.bcB S n μ < M := hMB n μ hEμ0 hμM hμC
  have hEμ' : ggE ≤ Bc.bcB S n μ := sv_B_geE hDμ hEμ0
  -- `B_n η = Ω₁·B_n μ + B_n η₀`
  have hη0c : η0 < Bc.bcC S (n + 1) := Si.si_T_lt_c hβE hβc hη0T hη0Ω
  obtain ⟨hDm, hBm⟩ := ufB_Om1mul (S := S) (n := n) hcS hLw (Tc.tcB_c_le n) μ hμC
  rw [← Rj.rj_Om1] at hDm hBm
  have hBη : Bc.bcB S n η = Om1 * (Om1 + Bc.bcB S n μ) + Bc.bcB S n η0 := by
    rw [← hdec, (mvB_add (k := n) hDm (mvD_of_lt (hη0c.trans hLw))).2, hBm, sv_Om1_add_big hEμ']
  rw [hBη, ← hηeq]
  exact ufVtE hC ⟨hMG, ucB_lt_Om2.le⟩ hβ hβc hEμ0 hμM hμ'M hμT hη0T hη0Ω

/-- **`UcCit M ∧ SvVtTopFrom S (Ω₁·M) ⇒ Ss.SsVtTopHi S`** (`M ≤ X` closed under `B_n` on the codes). -/
theorem ufVtTopHi_of {M : Ordinal.{0}} (hC : UcCit M) (hMG : M ≤ ucB)
    (hMB : ∀ n : ℕ, ∀ μ, ggE ≤ μ → μ < M → UcCl (Bc.bcC S (n + 1)) μ → Bc.bcB S n μ < M)
    (hTop : SvVtTopFrom S (Om1 * M)) : SsVtTopHi S := by
  intro n β hβ hβc η hη hlo hη2
  rcases lt_or_ge η (Om1 * M) with hhi | hhi
  · exact ufVtTop_mid hC hMG hMB hβ hβc hη hlo hhi
  · exact hTop n β hβ hβc η hη hhi hη2

/-- `B_n μ < X` for every code `μ < X` over `c_{n+1}`. -/
theorem uf_MB2 (n : ℕ) (μ : Ordinal.{0}) (_ : ggE ≤ μ) (hμ : μ < ucB) (hC : UcCl (Bc.bcC S (n + 1)) μ) :
    Bc.bcB S n μ < ucB := ufB_lt_B hC

/-- **Under `UcCit X`: `Ss.SsVtTopHi S ↔ SvVtTopFrom S X`.** -/
theorem ufVtTopHi_iff (hC : UcCit ucB) : SsVtTopHi S ↔ SvVtTopFrom S ucB := by
  constructor
  · intro h n β hβ hβc η hη hG hη2
    have hlo : ggE + Om1 ≤ ucB :=
      (uc_B_indec.add_lt (ggE_le_ggGam.trans_lt (Tz.tz_gg_lt_X.trans uc_X_lt_B)) ucB_gt).le
    exact h n β hβ hβc η hη (hlo.trans hG) hη2
  · intro h
    refine ufVtTopHi_of hC le_rfl (fun n μ h1 h2 h3 => uf_MB2 n μ h1 h2 h3) ?_
    rw [uf_Om1_mul_B]; exact h

/-- **Under `UcCit X`: `SvVtTopFrom S Γ_{Ω₁+1} ↔ SvVtTopFrom S X`.** -/
theorem ufVtTopFrom_iff (hC : UcCit ucB) : SvVtTopFrom S ggGam ↔ SvVtTopFrom S ucB :=
  Sy.syVtTopHi_iff.symm.trans (ufVtTopHi_iff hC)

/-- **Under `UcCit X`: `Sp.SpVtTopAll S ↔ SvVtTopFrom S X`.** -/
theorem ufVtTopAll_iff (hC : UcCit ucB) : SpVtTopAll S ↔ SvVtTopFrom S ucB :=
  Sy.syVtTopAll_iff.trans (ufVtTopFrom_iff hC)


/-- **`SvVtTopFrom S X ↔ SvVtTopFrom S B₂`**, no hypothesis (`Uc.ucCit`, `Tl.tlCit`). -/
theorem ufVtTopFrom_XB : SvVtTopFrom S Tl.tlX ↔ SvVtTopFrom S ucB :=
  (Tz.tzVtTopHi_iff (S := S) Tl.tlCit).symm.trans (ufVtTopHi_iff ucCit)

/-- **`SvVtTopFrom S Γ_{Ω₁+1} ↔ SvVtTopFrom S B₂`**, no hypothesis. -/
theorem ufVtTopFrom_G : SvVtTopFrom S ggGam ↔ SvVtTopFrom S ucB := ufVtTopFrom_iff ucCit

/-- **`SvVtTopFrom S B_Γ ↔ SvVtTopFrom S B₂`**, no hypothesis. -/
theorem ufVtTopFrom_BG : SvVtTopFrom S Tf.tfBG ↔ SvVtTopFrom S ucB :=
  (Tz.tzVtTopFrom_BG (S := S)).trans ufVtTopFrom_XB

/-- **`Sp.SpVtTopAll S ↔ SvVtTopFrom S B₂`**, no hypothesis. -/
theorem ufVtTopAll : SpVtTopAll S ↔ SvVtTopFrom S ucB := ufVtTopAll_iff ucCit

end Googology.Trans.PoR.InaccPsi.R2.Uf
