import Googology.Trans.PoR.InaccPsi.R2.HkG

/-!
# HkFr: EVERY `φ(Ω₁·M, G+1)`, `M < ε₀`, IS LOCATED; THE FRONTIER `ι(Γ(φ(Ω₁·ε₀, G+1)))`

Each system `Hk.hkGS μ` (`μ < ε₀`, bound `φ(Ω₁·(1+μ), G+1)`, base gate `0`) is located by `Hg.hgV_locD`; the bounds
are cofinal below `φ(Ω₁·ε₀, G+1)`, so BLK^O, the exact reaches, ENUM-REACH and CapV hold at every range restart below
`ι(Γ(φ(Ω₁·ε₀, G+1)))`, UNCONDITIONALLY, and the road asks its hypotheses only above it.

* `hkGS_loc`, `hkGS_blk` (every `μ < ε₀`);
* `hkGE` (`φ(Ω₁·ε₀, G+1)`), `hkGE_cofB`, `hkGE_cof`, `hkGE_enum`, `hkGE_capV`, `hkGE_road`, `hkGE_lt1`,
  `hkGE_lt_Om2`, `hkGE_P`, `hkGE_fr_order`.

No new axiom.  New definition: `hkGE`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hk

open Googology.Trans.PoR.InaccPsi.R2.Hj Googology.Trans.PoR.InaccPsi.R2.Hi Googology.Trans.PoR.InaccPsi.R2.Hg
open Googology.Trans.PoR.InaccPsi.R2.Hf Googology.Trans.PoR.InaccPsi.R2.Hd Googology.Trans.PoR.InaccPsi.R2.He
open Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Hb
open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Lp Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Gd

theorem hkGS_γK (S : InaccSeq.{0}) {μ : Ordinal.{0}} (hμ : μ < ε₀) : (hkGS μ).γ < Td.tdK S := by
  rw [hkGS_γ hμ]; exact hg_K_pos S

/-- **`φ(Ω₁·(1+μ), G+1)` IS LOCATED** for every `μ < ε₀`: `Λ⁺ = ι(Γ(φ(Ω₁·(1+μ), G+1))·ω)`, `P(…) < L(0)`. -/
theorem hkGS_loc (S : InaccSeq.{0}) {μ : Ordinal.{0}} (hμ : μ < ε₀) :
    ∃ X : XtSys, XtTopPkg X ∧ xtB1 X = iota S (gcG (hkGS μ).B * ω) ∧
      upsilon (xtB1 X) = Pv S (gcG (hkGS μ).B * ω) ∧ Pv S (gcG (hkGS μ).B * ω) < Nc.ncL S 0 :=
  hgV_locD (hkGS μ) S (hkGS_γK S hμ)

/-- **Theorem BLK^O below `P(Γ(φ(Ω₁·(1+μ), G+1))·ω)`, with the exact reaches**, for every `μ < ε₀`. -/
theorem hkGS_blk (S : InaccSeq.{0}) {μ : Ordinal.{0}} (hμ : μ < ε₀) :
    let X := gsX (hkGS μ).step.toRS _ (hkGS μ).E_lt_B.le (hkGS μ).B_lt_NB S
      (hgV_locD_g (hkGS μ) S (hkGS_γK S hμ))
    (∀ c' d, c' < d → d < upsilon (xtB1 X) → (le2 c' d ↔ ∃ μ, ∃ j : ℕ, (μ = 0 ∨ IsRestartIdx μ) ∧ μ < xtB1 X ∧
        c' = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧ d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < xtB1 X →
      (∀ c' < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c' g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec X l)) ∧
    (∀ α < upsilon (xtB1 X), ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  hgV_locD_blk (hkGS μ) S (hkGS_γK S hμ)

/-- **`φ(Ω₁·ε₀, G+1)`.** -/
noncomputable def hkGE : Ordinal.{0} := veblen (Om1 * ε₀) (gcG 0 + 1)

theorem hk_e0_lt_G (α : Ordinal.{0}) : (ε₀ : Ordinal.{0}) < gcG α :=
  (show (ε₀ : Ordinal.{0}) ≤ Om1 by rw [Br.Om1_eq]; exact gc_eps0_le_Om1).trans_lt (hg_Om1_lt_G α)

theorem hkGE_LG (α : Ordinal.{0}) : (Om1 : Ordinal.{0}) * ε₀ < gcG α :=
  InE.mul_lt (Low.opow_eq_self_of_SC (gcG_SC α)) (hg_Om1_lt_G α) (hk_e0_lt_G α)

theorem hkGE_ne : (Om1 : Ordinal.{0}) * ε₀ ≠ 0 := (mul_pos gv_Om1_pos (epsilon_pos 0)).ne'

/-- **Every ordinal below `φ(Ω₁·ε₀, G+1)` lies below some `φ(Ω₁·(1+μ), G+1)`, `μ < ε₀`.** -/
theorem hkGE_cofB {β : Ordinal.{0}} (hβ : β < hkGE) : ∃ μ, μ < ε₀ ∧ β < (hkGS μ).B := by
  obtain ⟨b, hb, hβb⟩ := hgVeb_cof hkGE_ne (gn_veb_fix (gcG_SC 0) (hkGE_LG 0)) hβ
  have hdiv : b / Om1 < ε₀ := (lt_mul_iff_div_lt gv_Om1_pos.ne').1 hb
  have hlim : IsSuccLimit (ε₀ : Ordinal.{0}) := gc_eps0_lim
  have hμ : b / Om1 + 1 + 1 < ε₀ := hlim.add_one_lt (hlim.add_one_lt hdiv)
  refine ⟨_, hμ, hβb.trans ?_⟩
  rw [hkGS_B hμ, hkG_B_eq (hk_one_add hμ)]
  refine hdN_lt_Nx ?_
  calc b + 1 ≤ Om1 * (b / Om1) + Om1 := Order.add_one_le_of_lt (lt_mul_div_add b gv_Om1_pos.ne')
  _ = Om1 * (b / Om1 + 1) := by rw [mul_add_one]
  _ < Om1 * (b / Om1 + 1 + 1) := mul_lt_mul_of_pos_left (lt_add_one _) gv_Om1_pos
  _ ≤ Om1 * (1 + (b / Om1 + 1 + 1)) := mul_le_mul_left' le_add_self _

theorem hkGE_lim : IsSuccLimit hkGE := ev_isSuccLimit_of_inE (gg_veblen_eps hkGE_ne)

/-- **The located bounds `ι(Γ(φ(Ω₁·(1+μ), G+1))·ω)` are cofinal below `ι(Γ(φ(Ω₁·ε₀, G+1)))`.** -/
theorem hkGE_cof (S : InaccSeq.{0}) {l : Ordinal.{0}} (hl : l < iota S (gcG hkGE)) :
    ∃ μ, μ < ε₀ ∧ l < iota S (gcG (hkGS μ).B * ω) := by
  have hlim : IsSuccLimit (gcG hkGE) := ev_isSuccLimit_of_inE (Low.opow_eq_self_of_SC (gcG_SC _))
  rw [iota_limit hlim] at hl
  haveI : Nonempty (Iio (gcG hkGE)) := ⟨⟨0, hlim.bot_lt⟩⟩
  obtain ⟨e, he⟩ := (lt_ciSup_iff (iota_bdd _)).1 hl
  obtain ⟨β, hβ, heβ⟩ := gcG_lt_of_lt_limit hkGE_lim e.2
  obtain ⟨μ, hμ, hβμ⟩ := hkGE_cofB hβ
  refine ⟨μ, hμ, he.trans_le (iota_mono _ _ ((heβ.trans (gcG_lt hβμ)).trans_le ?_).le)⟩
  exact le_mul_of_one_le_right' one_lt_omega0.le

/-- **ENUM-REACH at every range restart below `ι(Γ(φ(Ω₁·ε₀, G+1)))`, fixed points included** (UNCONDITIONAL). -/
theorem hkGE_enum (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG hkGE)) :
    CdUpper S l ∧ CdLower S l := by
  obtain ⟨μ, hμ, h⟩ := hkGE_cof S hl
  exact hgV_locD_enum (hkGS μ) S (hkGS_γK S hμ) hr h

/-- **CapV at every range restart below `ι(Γ(φ(Ω₁·ε₀, G+1)))`** (UNCONDITIONAL). -/
theorem hkGE_capV (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG hkGE)) :
    CdCapV S l := by
  obtain ⟨μ, hμ, h⟩ := hkGE_cof S hl
  exact hgV_locD_capV (hkGS μ) S (hkGS_γK S hμ) hr h

/-- **THE ROAD**: UPPER, LOWER, CapV asked only at `λ ≥ ι(Γ(φ(Ω₁·ε₀, G+1)))` (CapV also `υ_λ < L(ω)`), (CL), EQ,
TCrest, (EMB₂) ⟹ `ν_C = L(ω+1)`, `L(ω) ≤ ν_C`, `L(ω) <₂ L(ω+1)`, (P), (Q), the reaches. -/
theorem hkGE_road (S : InaccSeq.{0}) (hU : ∀ l, CdRange S l → iota S (gcG hkGE) ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S (gcG hkGE) ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S (gcG hkGE) ≤ l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  gv_road_of S _ (fun _ hr h => hkGE_enum S hr h) (fun _ hr h => hkGE_capV S hr h) hU hL hV hC hEQ hrest hB2

theorem hkGE_lt1 : hkGE < gcG 1 := by
  have hG1 := gcG_SC 1
  have hE := Low.opow_eq_self_of_SC hG1
  have hfix : veblen (Om1 * ε₀) (gcG 1) = gcG 1 := gn_veb_fix hG1 (hkGE_LG 1)
  have h2 := (isNormal_veblen (Om1 * ε₀)).strictMono ((ev_isSuccLimit_of_inE hE).add_one_lt (gcG_lt zero_lt_one))
  unfold hkGE; rwa [hfix] at h2

/-- **`Γ(φ(Ω₁·ε₀, G+1)) < Ω₂`.** -/
theorem hkGE_lt_Om2 : gcG hkGE < Om (1 + 1) := by
  have hBE : InE Tf.tfBG := Low.opow_eq_self_of_SC Tf.tfBG_SC
  have hO : (Om1 : Ordinal.{0}) < Tf.tfBG := Tf.tfBG_gt
  have h1 : (1 : Ordinal.{0}) < Tf.tfBG := one_lt_omega0.trans (omega0_lt_inE hBE)
  have hG1 : gcG 1 < Tf.tfBG := by
    rw [Tf.tf_gcG, ← Tf.tfBG_fix]
    exact gamma_lt_gamma.2 ((inE_indec hBE).add_lt ((inE_indec hBE).add_lt hO h1) h1)
  have h2 : gcG hkGE < Tf.tfBG := by
    rw [Tf.tf_gcG, ← Tf.tfBG_fix]
    exact gamma_lt_gamma.2 ((inE_indec hBE).add_lt ((inE_indec hBE).add_lt hO h1) (hkGE_lt1.trans hG1))
  exact h2.trans Tf.tfBG_lt_Om2

/-- **`P(Γ(φ(Ω₁·ε₀, G+1))) < L(0)`.** -/
theorem hkGE_P (S : InaccSeq.{0}) : Pv S (gcG hkGE) < Nc.ncL S 0 := ga_Pv_lt_L0 S hkGE_lt_Om2.le

/-- **The order of the frontiers**: `φ(Ω₁·ω·2, G+1) < φ(Ω₁·ε₀, G+1)`, `ι(Γ(φ(Ω₁·ω·2, G+1))·ω) ≤ ι(Γ(φ(Ω₁·ε₀, G+1)))
≤ ι(Ω₂)` and `P(Γ(φ(Ω₁·ε₀, G+1))) ≤ P(Ω₂) < L(0)`. -/
theorem hkGE_fr_order (S : InaccSeq.{0}) :
    hjGE2 < hkGE ∧ iota S (gcG hjGE2 * ω) ≤ iota S (gcG hkGE) ∧ iota S (gcG hkGE) ≤ iota S (Om (1 + 1)) ∧
      Pv S (gcG hkGE) ≤ Pv S (Om (1 + 1)) ∧ Pv S (Om (1 + 1)) < Nc.ncL S 0 := by
  have hww : ω + ω < (ε₀ : Ordinal.{0}) :=
    (inE_indec hk_e0_E).add_lt (omega0_lt_epsilon 0) (omega0_lt_epsilon 0)
  have hlt : hjGE2 < hkGE := by
    unfold hjGE2 hkGE
    refine hd_veb_left_lt ?_ _
    rw [← mul_add]
    exact mul_lt_mul_of_pos_left hww gv_Om1_pos
  have hV : InE (gcG hkGE) := Low.opow_eq_self_of_SC (gcG_SC _)
  refine ⟨hlt, iota_mono _ _ (InE.mul_lt hV (gcG_lt hlt) (omega0_lt_inE hV)).le,
    iota_mono _ _ hkGE_lt_Om2.le, Nm.Pv_mono hkGE_lt_Om2.le, ga_Pv_lt_L0 S le_rfl⟩

end Googology.Trans.PoR.InaccPsi.R2.Hk
