import Googology.Trans.PoR.InaccPsi.R2.HiVG

/-!
# HiVFr: EVERY `φ(Ω₁+κ+1, G+1)`, `κ < K`, IS LOCATED; THE FRONTIER `ι(Γ(φ(Ω₁+K, G+1)))`

`Hi.hiGL κ` (bound `φ(Ω₁+κ+1, G+1)`) has base gate `κ`.  So for every `κ < K = ψ_{Ω₁}(Ω_ω)` it is located, and the
bounds are cofinal in `φ(Ω₁+K, G+1) = hdNx (Ω₁+K) G` (`hiGE`): ENUM-REACH and CapV hold at every range restart below
`ι(Γ(φ(Ω₁+K, G+1)))`, UNCONDITIONALLY; the road asks UPPER, LOWER, CapV only above it.  The level `Ω₁ + K` itself is
the next wall: its system has base gate `K`, and the location (`Hg.hgV_locD`) asks a gate below `K`.

* `hiGL_γK`, `hiGL_loc`, `hiGL_blk`, `hiGE`, `hiGE_cofB`, `hiGE_cof`, `hiGE_enum`, `hiGE_capV`, `hiGE_road`,
  `hiGE_lt1`, `hiGE_lt_Om2`, `hiGE_P`, `hiGE_fr_order`.

No new axiom.  New definition: `hiGE`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hi

open Googology.Trans.PoR.InaccPsi.R2.Hg
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

theorem hiGL_γK (S : InaccSeq.{0}) {κ : Ordinal.{0}} (hκ : κ < Td.tdK S) : (hiGL κ).γ < Td.tdK S := by
  rw [hiGL_γ (hκ.trans (hf_K_lt S))]; exact hκ

/-- **`φ(Ω₁+κ+1, G+1)` IS LOCATED** for every `κ < K`: `Λ⁺ = ι(Γ(φ(Ω₁+κ+1, G+1))·ω)`, `P(…) < L(0)`. -/
theorem hiGL_loc (S : InaccSeq.{0}) {κ : Ordinal.{0}} (hκ : κ < Td.tdK S) :
    ∃ X : XtSys, XtTopPkg X ∧ xtB1 X = iota S (gcG (hiGL κ).B * ω) ∧
      upsilon (xtB1 X) = Pv S (gcG (hiGL κ).B * ω) ∧ Pv S (gcG (hiGL κ).B * ω) < Nc.ncL S 0 :=
  hgV_locD (hiGL κ) S (hiGL_γK S hκ)

/-- **Theorem BLK^O below `P(Γ(φ(Ω₁+κ+1, G+1))·ω)`, with the exact reaches**, every `κ < K`. -/
theorem hiGL_blk (S : InaccSeq.{0}) {κ : Ordinal.{0}} (hκ : κ < Td.tdK S) :
    let X := gsX (hiGL κ).step.toRS _ (hiGL κ).E_lt_B.le (hiGL κ).B_lt_NB S (hgV_locD_g (hiGL κ) S (hiGL_γK S hκ))
    (∀ c' d, c' < d → d < upsilon (xtB1 X) → (le2 c' d ↔ ∃ μ, ∃ j : ℕ, (μ = 0 ∨ IsRestartIdx μ) ∧ μ < xtB1 X ∧
        c' = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧ d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < xtB1 X →
      (∀ c' < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c' g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec X l)) ∧
    (∀ α < upsilon (xtB1 X), ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  hgV_locD_blk (hiGL κ) S (hiGL_γK S hκ)

/-- **`φ(Ω₁+K, G+1)`.** -/
noncomputable def hiGE (S : InaccSeq.{0}) : Ordinal.{0} := veblen (Om1 + Td.tdK S) (gcG 0 + 1)

theorem hiGE_eq (S : InaccSeq.{0}) : hiGE S = hdNx (Om1 + Td.tdK S) (gcG 0) :=
  (hdNx_fixP (hiG_fixL (hf_K_lt S))).symm

/-- **Every ordinal below `φ(Ω₁+K, G+1)` lies below some `φ(Ω₁+κ+1, G+1)`, `κ < K`.** -/
theorem hiGE_cofB (S : InaccSeq.{0}) {β : Ordinal.{0}} (hβ : β < hiGE S) :
    ∃ κ, κ < Td.tdK S ∧ β < (hiGL κ).B := by
  rw [hiGE_eq] at hβ
  obtain ⟨k, hk⟩ := (hiVLmOf (Td.tdK S) (hfK_lim S) (hf_K_lt S)).cofNx Om1 hβ
  have hκ := heFs_lt (hfK_lim S) (hgf_om (hf_K_lt S)) k
  refine ⟨_, hκ, ?_⟩
  rw [(hiGL_inv _ (hκ.trans (hf_K_lt S))).1.1]
  exact hk.trans_le (hdNx_le (hc_LuP_of_fix (hcN_fix _ _) |> hd_LuP_mono le_self_add) (hcN_gt _ _))

theorem hiGE_lt1 (S : InaccSeq.{0}) : hiGE S < gcG 1 := by
  have hG1 := gcG_SC 1
  have hE := Low.opow_eq_self_of_SC hG1
  have hK := hf_K_lt S
  have hfix : veblen (Om1 + Td.tdK S) (gcG 1) = gcG 1 :=
    gn_veb_fix hG1 ((hiG_L_lt_G hK).trans (gcG_lt zero_lt_one))
  have h2 := (isNormal_veblen (Om1 + Td.tdK S)).strictMono
    ((ev_isSuccLimit_of_inE hE).add_one_lt (gcG_lt zero_lt_one))
  unfold hiGE; rwa [hfix] at h2

theorem hiGE_lim (S : InaccSeq.{0}) : IsSuccLimit (hiGE S) := ev_isSuccLimit_of_inE (gg_veblen_eps (hiv_L0 _))

/-- **The located bounds `ι(Γ(φ(Ω₁+κ+1, G+1))·ω)`, `κ < K`, are cofinal below `ι(Γ(φ(Ω₁+K, G+1)))`.** -/
theorem hiGE_cof (S : InaccSeq.{0}) {l : Ordinal.{0}} (hl : l < iota S (gcG (hiGE S))) :
    ∃ κ, κ < Td.tdK S ∧ l < iota S (gcG (hiGL κ).B * ω) := by
  have hlim : IsSuccLimit (gcG (hiGE S)) := ev_isSuccLimit_of_inE (Low.opow_eq_self_of_SC (gcG_SC _))
  rw [iota_limit hlim] at hl
  haveI : Nonempty (Iio (gcG (hiGE S))) := ⟨⟨0, hlim.bot_lt⟩⟩
  obtain ⟨e, he⟩ := (lt_ciSup_iff (iota_bdd _)).1 hl
  obtain ⟨β, hβ, heβ⟩ := gcG_lt_of_lt_limit (hiGE_lim S) e.2
  obtain ⟨κ, hκ, hβκ⟩ := hiGE_cofB S hβ
  refine ⟨κ, hκ, he.trans_le (iota_mono _ _ ((heβ.trans (gcG_lt hβκ)).trans_le ?_).le)⟩
  exact le_mul_of_one_le_right' one_lt_omega0.le

/-- **ENUM-REACH at every range restart below `ι(Γ(φ(Ω₁+K, G+1)))`, fixed points included** (UNCONDITIONAL). -/
theorem hiGE_enum (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG (hiGE S))) :
    CdUpper S l ∧ CdLower S l := by
  obtain ⟨κ, hκ, h⟩ := hiGE_cof S hl
  exact hgV_locD_enum (hiGL κ) S (hiGL_γK S hκ) hr h

/-- **CapV at every range restart below `ι(Γ(φ(Ω₁+K, G+1)))`** (UNCONDITIONAL). -/
theorem hiGE_capV (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG (hiGE S))) :
    CdCapV S l := by
  obtain ⟨κ, hκ, h⟩ := hiGE_cof S hl
  exact hgV_locD_capV (hiGL κ) S (hiGL_γK S hκ) hr h

/-- **THE ROAD**: UPPER, LOWER, CapV asked only at `λ ≥ ι(Γ(φ(Ω₁+K, G+1)))` (CapV also `υ_λ < L(ω)`), (CL), EQ,
TCrest, (EMB₂) ⟹ `ν_C = L(ω+1)`, `L(ω) ≤ ν_C`, `L(ω) <₂ L(ω+1)`, (P), (Q), the reaches. -/
theorem hiGE_road (S : InaccSeq.{0}) (hU : ∀ l, CdRange S l → iota S (gcG (hiGE S)) ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S (gcG (hiGE S)) ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S (gcG (hiGE S)) ≤ l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  gv_road_of S _ (fun _ hr h => hiGE_enum S hr h) (fun _ hr h => hiGE_capV S hr h) hU hL hV hC hEQ hrest hB2

/-- **`Γ(φ(Ω₁+K, G+1)) < Ω₂`.** -/
theorem hiGE_lt_Om2 (S : InaccSeq.{0}) : gcG (hiGE S) < Om (1 + 1) := by
  have hBE : InE Tf.tfBG := Low.opow_eq_self_of_SC Tf.tfBG_SC
  have hO : (Om1 : Ordinal.{0}) < Tf.tfBG := Tf.tfBG_gt
  have h1 : (1 : Ordinal.{0}) < Tf.tfBG := one_lt_omega0.trans (omega0_lt_inE hBE)
  have hG1 : gcG 1 < Tf.tfBG := by
    rw [Tf.tf_gcG, ← Tf.tfBG_fix]
    exact gamma_lt_gamma.2 ((inE_indec hBE).add_lt ((inE_indec hBE).add_lt hO h1) h1)
  have h2 : gcG (hiGE S) < Tf.tfBG := by
    rw [Tf.tf_gcG, ← Tf.tfBG_fix]
    exact gamma_lt_gamma.2 ((inE_indec hBE).add_lt ((inE_indec hBE).add_lt hO h1) ((hiGE_lt1 S).trans hG1))
  exact h2.trans Tf.tfBG_lt_Om2

/-- **`P(Γ(φ(Ω₁+K, G+1))) < L(0)`.** -/
theorem hiGE_P (S : InaccSeq.{0}) : Pv S (gcG (hiGE S)) < Nc.ncL S 0 := ga_Pv_lt_L0 S (hiGE_lt_Om2 S).le

/-- **The order of the frontiers**: `φ(Ω₁+1, G+1) < φ(Ω₁+K, G+1)`, `ι(Γ(φ(Ω₁+1, G+1))·ω) ≤ ι(Γ(φ(Ω₁+K, G+1))) ≤
ι(Ω₂)` and `P(Γ(φ(Ω₁+K, G+1))) ≤ P(Ω₂) < L(0)`. -/
theorem hiGE_fr_order (S : InaccSeq.{0}) :
    hiN < hiGE S ∧ iota S (gcG hiN * ω) ≤ iota S (gcG (hiGE S)) ∧ iota S (gcG (hiGE S)) ≤ iota S (Om (1 + 1)) ∧
      Pv S (gcG (hiGE S)) ≤ Pv S (Om (1 + 1)) ∧ Pv S (Om (1 + 1)) < Nc.ncL S 0 := by
  have hK := hf_K_lt S
  have hK1 : (1 : Ordinal.{0}) < Td.tdK S := by
    have := (hfK_lim S).add_one_lt (hfK_lim S).bot_lt; simpa using this
  have hlt : hiN < hiGE S := by
    rw [hiGE_eq]
    exact hdN_lt_Nx ((add_lt_add_iff_left Om1).2 hK1)
  have hV : InE (gcG (hiGE S)) := Low.opow_eq_self_of_SC (gcG_SC _)
  refine ⟨hlt, iota_mono _ _ (InE.mul_lt hV (gcG_lt hlt) (omega0_lt_inE hV)).le,
    iota_mono _ _ (hiGE_lt_Om2 S).le, Nm.Pv_mono (hiGE_lt_Om2 S).le, ga_Pv_lt_L0 S le_rfl⟩

end Googology.Trans.PoR.InaccPsi.R2.Hi
