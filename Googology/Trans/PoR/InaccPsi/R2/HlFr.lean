import Googology.Trans.PoR.InaccPsi.R2.HlG

/-!
# HlFr: EVERY `φ(Ω₁·(1+μ), G+1)`, `μ < K`, IS LOCATED; THE FRONTIER `ι(Γ(φ(Ω₁·K, G+1)))`

PORT of `Hk.HkFr`: `hlkGS μ` with `μ < K = ψ_{Ω₁}(Ω_ω)` has base gate `≤ 1+μ < K`, so `Hg.hgV_locD` locates it;
the bounds are cofinal below `φ(Ω₁·K, G+1)` (`hlkGE S`): BLK^O, exact reaches, ENUM-REACH and CapV hold at every
range restart below `ι(Γ(φ(Ω₁·K, G+1)))`, UNCONDITIONALLY, and the road `hlkGE_road` asks its hypotheses only above
it.

What differs from the source: the level datum is a GATED one (`Hl.HlLv`: Lemma EXACT for the reading `ℓ` only at
base pairs `(σ, ρ)` above the level gate `g`, the hull membership of `L` only at `0 < a`, `g < b`, the code gate
`g < Z` only when a code over `Z` exists at the level); every pseudo-base and base carries `g ≤` its reading gate
(fields `lg`), and the code-gate fields take the extra hypothesis `g < Z`.  Proofs are otherwise those of the source;
names: prefix `hl`/`Hl` in place of `hj`/`Hj`.

No new axiom.  New definition: `hlkGE`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hl

open Googology.Trans.PoR.InaccPsi.R2.Hk

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

section K

variable (S : InaccSeq.{0})

theorem hlK_E : InE (Td.tdK S) := Low.opow_eq_self_of_SC Td.tdK_SC

theorem hlK_lt : Td.tdK S < Om1 := by rw [Br.Om1_eq]; exact Td.tdK_lt_Om1

theorem hlK_lim : IsSuccLimit (Td.tdK S) := ev_isSuccLimit_of_inE (hlK_E S)

theorem hlK_one_add {μ : Ordinal.{0}} (hμ : μ < Td.tdK S) : 1 + μ < Td.tdK S :=
  (inE_indec (hlK_E S)).add_lt (one_lt_omega0.trans (omega0_lt_inE (hlK_E S))) hμ

/-- **The base gate of `hlkGS μ` is below `K = ψ_{Ω₁}(Ω_ω)`** for `μ < K`. -/
theorem hlkGS_γK {μ : Ordinal.{0}} (hμ : μ < Td.tdK S) : (hlkGS μ).γ < Td.tdK S :=
  (hlkGS_γ_le (hμ.trans (hlK_lt S))).trans_lt (hlK_one_add S hμ)

/-- **`φ(Ω₁·(1+μ), G+1)` IS LOCATED** for every `μ < K`: `Λ⁺ = ι(Γ(φ(Ω₁·(1+μ), G+1))·ω)`, `P(…) < L(0)`. -/
theorem hlkGS_loc {μ : Ordinal.{0}} (hμ : μ < Td.tdK S) :
    ∃ X : XtSys, XtTopPkg X ∧ xtB1 X = iota S (gcG (hlkGS μ).B * ω) ∧
      upsilon (xtB1 X) = Pv S (gcG (hlkGS μ).B * ω) ∧ Pv S (gcG (hlkGS μ).B * ω) < Nc.ncL S 0 :=
  hgV_locD (hlkGS μ) S (hlkGS_γK S hμ)

/-- **Theorem BLK^O below `P(Γ(φ(Ω₁·(1+μ), G+1))·ω)`, with the exact reaches**, for every `μ < K`. -/
theorem hlkGS_blk {μ : Ordinal.{0}} (hμ : μ < Td.tdK S) :
    let X := gsX (hlkGS μ).step.toRS _ (hlkGS μ).E_lt_B.le (hlkGS μ).B_lt_NB S
      (hgV_locD_g (hlkGS μ) S (hlkGS_γK S hμ))
    (∀ c' d, c' < d → d < upsilon (xtB1 X) → (le2 c' d ↔ ∃ μ, ∃ j : ℕ, (μ = 0 ∨ IsRestartIdx μ) ∧ μ < xtB1 X ∧
        c' = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧ d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < xtB1 X →
      (∀ c' < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c' g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec X l)) ∧
    (∀ α < upsilon (xtB1 X), ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  hgV_locD_blk (hlkGS μ) S (hlkGS_γK S hμ)

/-- **`φ(Ω₁·K, G+1)`**, `K = ψ_{Ω₁}(Ω_ω)`. -/
noncomputable def hlkGE : Ordinal.{0} := veblen (Om1 * Td.tdK S) (gcG 0 + 1)

theorem hlkGE_LG (α : Ordinal.{0}) : (Om1 : Ordinal.{0}) * Td.tdK S < gcG α :=
  InE.mul_lt (Low.opow_eq_self_of_SC (gcG_SC α)) (hg_Om1_lt_G α) ((hlK_lt S).trans (hg_Om1_lt_G α))

theorem hlkGE_ne : (Om1 : Ordinal.{0}) * Td.tdK S ≠ 0 := (mul_pos gv_Om1_pos (hlK_E S).pos).ne'

/-- **Every ordinal below `φ(Ω₁·K, G+1)` lies below some `φ(Ω₁·(1+μ), G+1)`, `μ < K`.** -/
theorem hlkGE_cofB {β : Ordinal.{0}} (hβ : β < hlkGE S) : ∃ μ, μ < Td.tdK S ∧ β < (hlkGS μ).B := by
  obtain ⟨b, hb, hβb⟩ := hgVeb_cof (hlkGE_ne S) (gn_veb_fix (gcG_SC 0) (hlkGE_LG S 0)) hβ
  have hdiv : b / Om1 < Td.tdK S := (lt_mul_iff_div_lt gv_Om1_pos.ne').1 hb
  have hlim := hlK_lim S
  have hμ : b / Om1 + 1 + 1 < Td.tdK S := hlim.add_one_lt (hlim.add_one_lt hdiv)
  have hμ1 : b / Om1 + 1 + 1 < Om1 := hμ.trans (hlK_lt S)
  refine ⟨_, hμ, hβb.trans ?_⟩
  rw [hlkGS_B hμ1, hlkG_B_eq (hl_one_add hμ1)]
  refine hdN_lt_Nx ?_
  calc b + 1 ≤ Om1 * (b / Om1) + Om1 := Order.add_one_le_of_lt (lt_mul_div_add b gv_Om1_pos.ne')
  _ = Om1 * (b / Om1 + 1) := by rw [mul_add_one]
  _ < Om1 * (b / Om1 + 1 + 1) := mul_lt_mul_of_pos_left (lt_add_one _) gv_Om1_pos
  _ ≤ Om1 * (1 + (b / Om1 + 1 + 1)) := mul_le_mul_left' le_add_self _

theorem hlkGE_lim : IsSuccLimit (hlkGE S) := ev_isSuccLimit_of_inE (gg_veblen_eps (hlkGE_ne S))

/-- **The located bounds `ι(Γ(φ(Ω₁·(1+μ), G+1))·ω)` are cofinal below `ι(Γ(φ(Ω₁·K, G+1)))`.** -/
theorem hlkGE_cof {l : Ordinal.{0}} (hl : l < iota S (gcG (hlkGE S))) :
    ∃ μ, μ < Td.tdK S ∧ l < iota S (gcG (hlkGS μ).B * ω) := by
  have hlim : IsSuccLimit (gcG (hlkGE S)) := ev_isSuccLimit_of_inE (Low.opow_eq_self_of_SC (gcG_SC _))
  rw [iota_limit hlim] at hl
  haveI : Nonempty (Iio (gcG (hlkGE S))) := ⟨⟨0, hlim.bot_lt⟩⟩
  obtain ⟨e, he⟩ := (lt_ciSup_iff (iota_bdd _)).1 hl
  obtain ⟨β, hβ, heβ⟩ := gcG_lt_of_lt_limit (hlkGE_lim S) e.2
  obtain ⟨μ, hμ, hβμ⟩ := hlkGE_cofB S hβ
  refine ⟨μ, hμ, he.trans_le (iota_mono _ _ ((heβ.trans (gcG_lt hβμ)).trans_le ?_).le)⟩
  exact le_mul_of_one_le_right' one_lt_omega0.le

/-- **ENUM-REACH at every range restart below `ι(Γ(φ(Ω₁·K, G+1)))`, fixed points included** (UNCONDITIONAL). -/
theorem hlkGE_enum {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG (hlkGE S))) :
    CdUpper S l ∧ CdLower S l := by
  obtain ⟨μ, hμ, h⟩ := hlkGE_cof S hl
  exact hgV_locD_enum (hlkGS μ) S (hlkGS_γK S hμ) hr h

/-- **CapV at every range restart below `ι(Γ(φ(Ω₁·K, G+1)))`** (UNCONDITIONAL). -/
theorem hlkGE_capV {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG (hlkGE S))) : CdCapV S l := by
  obtain ⟨μ, hμ, h⟩ := hlkGE_cof S hl
  exact hgV_locD_capV (hlkGS μ) S (hlkGS_γK S hμ) hr h

/-- **THE ROAD**: UPPER, LOWER, CapV asked only at `λ ≥ ι(Γ(φ(Ω₁·K, G+1)))` (CapV also `υ_λ < L(ω)`), (CL), EQ,
TCrest, (EMB₂) ⟹ `ν_C = L(ω+1)`, `L(ω) ≤ ν_C`, `L(ω) <₂ L(ω+1)`, (P), (Q), the reaches. -/
theorem hlkGE_road (hU : ∀ l, CdRange S l → iota S (gcG (hlkGE S)) ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S (gcG (hlkGE S)) ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S (gcG (hlkGE S)) ≤ l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  gv_road_of S _ (fun _ hr h => hlkGE_enum S hr h) (fun _ hr h => hlkGE_capV S hr h) hU hL hV hC hEQ hrest hB2

theorem hlkGE_lt1 : hlkGE S < gcG 1 := by
  have hG1 := gcG_SC 1
  have hE := Low.opow_eq_self_of_SC hG1
  have hfix : veblen (Om1 * Td.tdK S) (gcG 1) = gcG 1 := gn_veb_fix hG1 (hlkGE_LG S 1)
  have h2 := (isNormal_veblen (Om1 * Td.tdK S)).strictMono
    ((ev_isSuccLimit_of_inE hE).add_one_lt (gcG_lt zero_lt_one))
  unfold hlkGE; rwa [hfix] at h2

/-- **`Γ(φ(Ω₁·K, G+1)) < Ω₂`.** -/
theorem hlkGE_lt_Om2 : gcG (hlkGE S) < Om (1 + 1) := by
  have hBE : InE Tf.tfBG := Low.opow_eq_self_of_SC Tf.tfBG_SC
  have hO : (Om1 : Ordinal.{0}) < Tf.tfBG := Tf.tfBG_gt
  have h1 : (1 : Ordinal.{0}) < Tf.tfBG := one_lt_omega0.trans (omega0_lt_inE hBE)
  have hG1 : gcG 1 < Tf.tfBG := by
    rw [Tf.tf_gcG, ← Tf.tfBG_fix]
    exact gamma_lt_gamma.2 ((inE_indec hBE).add_lt ((inE_indec hBE).add_lt hO h1) h1)
  have h2 : gcG (hlkGE S) < Tf.tfBG := by
    rw [Tf.tf_gcG, ← Tf.tfBG_fix]
    exact gamma_lt_gamma.2 ((inE_indec hBE).add_lt ((inE_indec hBE).add_lt hO h1) ((hlkGE_lt1 S).trans hG1))
  exact h2.trans Tf.tfBG_lt_Om2

/-- **`P(Γ(φ(Ω₁·K, G+1))) < L(0)`.** -/
theorem hlkGE_P : Pv S (gcG (hlkGE S)) < Nc.ncL S 0 := ga_Pv_lt_L0 S (hlkGE_lt_Om2 S).le

/-- **The order of the frontiers**: `φ(Ω₁·ε₀, G+1) < φ(Ω₁·K, G+1)`, `ι(Γ(φ(Ω₁·ε₀, G+1))) ≤ ι(Γ(φ(Ω₁·K, G+1)))
≤ ι(Ω₂)` and `P(Γ(φ(Ω₁·K, G+1))) ≤ P(Ω₂) < L(0)`. -/
theorem hlkGE_fr_order :
    hkGE < hlkGE S ∧ iota S (gcG hkGE) ≤ iota S (gcG (hlkGE S)) ∧
      iota S (gcG (hlkGE S)) ≤ iota S (Om (1 + 1)) ∧
      Pv S (gcG (hlkGE S)) ≤ Pv S (Om (1 + 1)) ∧ Pv S (Om (1 + 1)) < Nc.ncL S 0 := by
  have hlt : hkGE < hlkGE S := by
    unfold hkGE hlkGE
    exact hd_veb_left_lt (mul_lt_mul_of_pos_left (gq_eps0_lt_gam.trans (gr_gam0_lt_tdK S)) gv_Om1_pos) _
  refine ⟨hlt, iota_mono _ _ (gcG_lt hlt).le, iota_mono _ _ (hlkGE_lt_Om2 S).le, Nm.Pv_mono (hlkGE_lt_Om2 S).le,
    ga_Pv_lt_L0 S le_rfl⟩

end K

end Googology.Trans.PoR.InaccPsi.R2.Hl
