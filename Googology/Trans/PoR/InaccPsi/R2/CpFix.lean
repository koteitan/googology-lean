import Googology.Trans.PoR.InaccPsi.R2.CpUp

/-!
# The isolated fixed points of `υ` below `cpB1`: ENUM-REACH as a statement on the code

`R2.CpUp` proves ENUM-REACH below `cpB1` off the fixed points of `υ`.  Here the fixed points `F = υ_F` that are
**isolated** (`CpIso F`: no fixed point of `υ` among the restart indices of some `(ν, F)`):

* `cpVz_nonfix` (**the offset off the fixed points**): `VzOrec(μ) = -1 + e(μ)` for every restart index
  `ω² < μ < Ω₁` with `μ < υ_μ` (no bound `cpB1`; `cpDecomp`, `cpVz_rel`, `cpExp_add`);
* `cpVz_iso` (**the offset at an isolated fixed point**): `VzOrec(F) = F`.  The realized terms take values
  `≤ -1 + e(μ) ≤ μ < ρ_μ` at the restarts `μ` of the window, so they have no base and their value at `ρ_F`
  is below `F`; every constant `c < F` is realized at the restarts `ω^{c+2}·(q+1)` of the window;
* `cpFix_iff` (**ENUM-REACH at an isolated fixed point `F < cpB1`**): UPPER at `F` iff `F ≤ Θ_F(m_F)`, LOWER
  iff `Θ_F(m_F) ≤ F`;
* `cpFix_code` (**the reduction to the code**): with a name (`ρ_F < P(η₁)`), `F ≤ m_F` gives UPPER at `F`,
  `m_F ≤ Ω₁` gives LOWER at `F` (`Θ_F(F) = F`, `Θ_F(Ω₁) = ρ_F = F`).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Cp

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Cd VzTm

variable {S : InaccSeq.{0}}

/-- `F` is an **isolated** fixed point region: no restart index of some `(ν, F)` is a fixed point of `υ`. -/
def CpIso (F : Ordinal.{0}) : Prop :=
  ∃ ν < F, ∀ μ, IsRestartIdx μ → ν < μ → μ < F → μ < upsilon μ

/-- **The offset off the fixed points of `υ`**: `VzOrec(μ) = -1 + e(μ)`. -/
theorem cpVz_nonfix {μ : Ordinal.{0}} (hμ : IsRestartIdx μ) (hww : ω * ω < μ) (hfix : μ < upsilon μ)
    (hμ1 : μ < Om1) : VzOrec μ = cdOff (cdExp μ) := by
  obtain ⟨l0, z, hl0, hz0, hzρ, hzd, rfl⟩ := cpDecomp hμ hww hfix
  have hl01 : l0 < Om1 := (lt_add_of_pos_right l0 hz0).trans hμ1
  rw [cpVz_rel hl0 hl01 z hz0 hzρ hzd, cpExp_add _ hz0.ne']

theorem cp_fix_facts {F : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F) :
    ω ^ F = F ∧ IsPrincipal (· + ·) F ∧ ω * ω < F := by
  have hU : UpsPt F := hfix ▸ upsPt_upsilon (pos_iff_ne_zero.2 hF.1)
  have hE : ω ^ F = F := upsPt_inE hU
  have hp := (indec_iff.1 (indec_of_upsPt hU)).2
  refine ⟨hE, hp, ?_⟩
  have h1 : (1 : Ordinal.{0}) ≤ F := Order.one_le_iff_pos.2 hU.1
  have hω : ω ≤ F := by
    calc ω = ω ^ (1 : Ordinal.{0}) := (opow_one ω).symm
      _ ≤ ω ^ F := opow_le_opow_right omega0_pos h1
      _ = F := hE
  have h2 : (2 : Ordinal.{0}) < F := lt_of_lt_of_le (by exact_mod_cast natCast_lt_omega0 2) hω
  calc ω * ω = ω ^ (2 : Ordinal.{0}) := cp_ww_eq.symm
    _ < ω ^ F := (opow_lt_opow_iff_right one_lt_omega0).2 h2
    _ = F := hE

/-- **The offset at an isolated fixed point**: `VzOrec(F) = F`. -/
theorem cpVz_iso {F : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F) (hF1 : F < Om1)
    (hiso : CpIso F) : VzOrec F = F := by
  obtain ⟨hE, hp, hww⟩ := cp_fix_facts hF hfix
  obtain ⟨ν, hνF, hν⟩ := hiso
  set ν2 := max ν (ω * ω) with hν2
  have hν2F : ν2 < F := max_lt hνF hww
  -- the restarts of the window are not fixed points, with offset `-1 + e(μ)`
  have hwin : ∀ μ, IsRestartIdx μ → ν2 < μ → μ < F →
      ω * ω < μ ∧ μ < upsilon μ ∧ VzOrec μ = cdOff (cdExp μ) := by
    intro μ hμ h1 h2
    have hww' : ω * ω < μ := (le_max_right _ _).trans_lt h1
    have hfx : μ < upsilon μ := hν μ hμ ((le_max_left _ _).trans_lt h1) h2
    exact ⟨hww', hfx, cpVz_nonfix hμ hww' hfx (h2.trans hF1)⟩
  refine le_antisymm ?_ ?_
  · refine cpVz_le (Order.one_le_iff_pos.2 (lt_of_le_of_lt zero_le hww)) fun s hCB hc => ?_
    obtain ⟨μ, hμ, h1, h2, hCBμ, hsμ⟩ := hc _ hν2F
    obtain ⟨-, hfx, hOμ⟩ := hwin μ hμ h1 h2
    have hμle : val s (upsilon μ) ≤ μ :=
      (hsμ.trans_eq hOμ).trans ((cdOff_le _).trans (cpExp_le hμ.1))
    have hn : noB s := by
      by_contra hn
      have := le_vzv_of_not_noB (ups_inE hμ) (ups_lt_Om1 _ (h2.trans hF1)) s hCBμ hn
      exact absurd (hμle.trans_lt hfx) (not_lt.2 this)
    rw [vzv_noB s hn (upsilon F) (upsilon μ)]
    exact hμle.trans_lt h2
  · refine le_of_forall_lt fun c hcF => ?_
    have hCB : CBt (cst c) (upsilon F) := (by rw [hfix]; exact hcF : c < upsilon F)
    have hcof : VzCofReal VzOrec F (cst c) := by
      intro ν0 hν0
      set ν1 := max (max ν0 ν2) c with hν1
      have hν1F : ν1 < F := max_lt (max_lt hν0 hν2F) hcF
      set a' := c + 1 + 1 with ha'
      have h1F : (1 : Ordinal.{0}) < F :=
        lt_of_le_of_lt (Order.one_le_iff_pos.2 (mul_pos omega0_pos omega0_pos)) hww
      have ha'F : a' < F := hp (hp hcF h1F) h1F
      have hpa : ω ^ a' ≠ 0 := (opow_pos _ omega0_pos).ne'
      set y := ω ^ a' * (ν1 / ω ^ a' + 1) with hy
      have hν1y : ν1 < y := by rw [hy, mul_add_one]; exact lt_mul_div_add ν1 hpa
      have hy0 : y ≠ 0 := (lt_of_le_of_lt zero_le hν1y).ne'
      have hyF : y < F := by
        have h1 : y ≤ ν1 + ω ^ a' := by
          rw [hy, mul_add_one]; exact add_le_add (mul_div_le ν1 _) le_rfl
        have h2 : ω ^ a' < F := by
          rw [← hE]; exact (opow_lt_opow_iff_right one_lt_omega0).2 ha'F
        exact h1.trans_lt (hp hν1F h2)
      have hey : a' ≤ cdExp y := cdExp_max hy0 (dvd_mul_right _ _)
      have h2a : (2 : Ordinal.{0}) ≤ a' := by
        rw [ha', add_assoc, one_add_one_eq_two]; exact le_add_self
      have hyd : ω * ω ∣ y := cp_ww_of_exp hy0 (h2a.trans hey)
      have hμ : IsRestartIdx y := ri_iff.2 ⟨hy0, hyd⟩
      have hν2y : ν2 < y := ((le_max_right ν0 ν2).trans (le_max_left _ c)).trans_lt hν1y
      obtain ⟨-, -, hOy⟩ := hwin y hμ hν2y hyF
      refine ⟨y, hμ, ((le_max_left ν0 ν2).trans (le_max_left _ c)).trans_lt hν1y, hyF, ?_, ?_⟩
      · show c < upsilon y
        exact ((le_max_right _ c).trans_lt hν1y).trans_le upsilon_normal.strictMono.le_apply
      · show c ≤ VzOrec y
        rw [hOy]
        exact (le_self_add.trans (cpOff_add_one_ge (c + 1))).trans (cpOff_mono hey)
    have := lt_vzOrec_of_cof hF hF1 hCB hcof
    simpa using this

/-- **ENUM-REACH at an isolated fixed point `F < cpB1`**: UPPER iff `F ≤ Θ_F(m_F)`, LOWER iff
`Θ_F(m_F) ≤ F`. -/
theorem cpFix_iff {F : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F) (hFB : F < cpB1)
    (hiso : CpIso F) :
    (CdUpper S F ↔ F ≤ cdTheta S F (cdCode S F)) ∧ (CdLower S F ↔ cdTheta S F (cdCode S F) ≤ F) := by
  have hO := cpVz_iso hF hfix (hFB.trans cpB1_lt_Om1) hiso
  refine ⟨?_, ?_⟩
  · rw [cpUpper_iff hF hFB, hO]
  · rw [cpLower_iff hF hFB, hO]

/-- **The reduction to the code** at an isolated fixed point `F < cpB1` with a name: `F ≤ m_F` gives UPPER,
`m_F ≤ Ω₁` gives LOWER. -/
theorem cpFix_code {F η1 : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F) (hFB : F < cpB1)
    (hiso : CpIso F) (hn : upsilon F < Pv S η1) :
    (F ≤ cdCode S F → CdUpper S F) ∧ (cdCode S F ≤ Om1 → CdLower S F) := by
  obtain ⟨hU, hL⟩ := cpFix_iff (S := S) hF hfix hFB hiso
  have hpv : Pv S (cdEta S F) = upsilon F := cdEta_pv hF.1 hn
  refine ⟨fun h => hU.2 ?_, fun h => hL.2 ?_⟩
  · calc F = cdTheta S F F := (cdTheta_small S hfix.ge).symm
      _ ≤ cdTheta S F (cdCode S F) := cdTheta_mono S F h
  · calc cdTheta S F (cdCode S F) ≤ cdTheta S F (Om 1) := cdTheta_mono S F (by rw [← Br.Om1_eq]; exact h)
      _ = upsilon F := cdTheta_Om1 hpv
      _ = F := hfix

end Googology.Trans.PoR.InaccPsi.R2.Cp
