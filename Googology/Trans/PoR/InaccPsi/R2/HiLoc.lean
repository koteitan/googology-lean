import Googology.Trans.PoR.InaccPsi.R2.HiMTop
import Googology.Trans.PoR.InaccPsi.R2.HgQV

/-!
# HiLoc: `N_{Ω₁}(G) = φ(Ω₁+1, G+1)` IS LOCATED; THE FRONTIER `ι(Γ(φ(Ω₁+1, G+1))·ω)`

`hiTU = Hi.hiMTU Hi.hgU_hiStart` is the union of the gated offset recursion of the level `Ω₁` (read as `x`) started at
`Hg.hgU` (the system at `φ(Ω₁, G+1)`): bound `N_{Ω₁}(G) = φ(Ω₁+1, G+1)`, base gate `0 < K`.  So it is located, and BLK^O
with the exact reaches, ENUM-REACH and CapV hold at every range restart below `ι(Γ(φ(Ω₁+1, G+1))·ω)`, UNCONDITIONALLY;
the road asks UPPER, LOWER, CapV only above it.  It lies past the round-100 frontier `ι(Γ(φ(Ω₁, G+ε₀)))` and below
`ι(Ω₂)`.

* `hiTU`, `hiTU_B`, `hiTU_γ`, `hiTU_loc`, `hiTU_blk`, `hiTU_enum`, `hiTU_capV`, `hiTU_road`, `hiN_lt_Om2`, `hiTU_P`,
  `hgFE_lt_hiN`, `hiTU_fr_order`, `hiTU_ext` (the union extends `Hg.hgU`).

No new axiom.  New definition: `hiTU`.
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

/-- **THE SYSTEM AT `φ(Ω₁+1, G+1)`**: the union of the gated offsets of the level `Ω₁` started at `Hg.hgU`. -/
noncomputable def hiTU : HgVD := hiMTU hgU_hiStart

theorem hiTU_B : hiTU.B = veblen (Om1 + 1) (gcG 0 + 1) := hiN_eq

theorem hiTU_γ : hiTU.γ = 0 := rfl

theorem hiTU_γK (S : InaccSeq.{0}) : hiTU.γ < Td.tdK S := hg_K_pos S

/-- **The union extends `Hg.hgU`** (readings and gates of every code below `φ(Ω₁, G+1)`). -/
theorem hiTU_ext {c : Ordinal.{0}} (hc : c < hgU.B) : (∀ x, hiTU.R c x = hgU.R c x) ∧ hiTU.g c = hgU.g c :=
  ⟨fun x => hiMTU_R0 hgU_hiStart hc x, hiMTU_g0 hgU_hiStart hc⟩

/-- **`φ(Ω₁+1, G+1)` IS LOCATED**: `Λ⁺ = ι(Γ(φ(Ω₁+1, G+1))·ω)`, `P(Γ(φ(Ω₁+1, G+1))·ω) < L(0)` (UNCONDITIONAL). -/
theorem hiTU_loc (S : InaccSeq.{0}) :
    ∃ X : XtSys, XtTopPkg X ∧ xtB1 X = iota S (gcG hiN * ω) ∧
      upsilon (xtB1 X) = Pv S (gcG hiN * ω) ∧ Pv S (gcG hiN * ω) < Nc.ncL S 0 :=
  hgV_locD hiTU S (hiTU_γK S)

/-- **Theorem BLK^O below `P(Γ(φ(Ω₁+1, G+1))·ω)`, with the exact reaches** (UNCONDITIONAL). -/
theorem hiTU_blk (S : InaccSeq.{0}) :
    let X := gsX hiTU.step.toRS _ hiTU.E_lt_B.le hiTU.B_lt_NB S (hgV_locD_g hiTU S (hiTU_γK S))
    (∀ c' d, c' < d → d < upsilon (xtB1 X) → (le2 c' d ↔ ∃ μ, ∃ j : ℕ, (μ = 0 ∨ IsRestartIdx μ) ∧ μ < xtB1 X ∧
        c' = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧ d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < xtB1 X →
      (∀ c' < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c' g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec X l)) ∧
    (∀ α < upsilon (xtB1 X), ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  hgV_locD_blk hiTU S (hiTU_γK S)

/-- **ENUM-REACH at every range restart below `ι(Γ(φ(Ω₁+1, G+1))·ω)`, fixed points included** (UNCONDITIONAL). -/
theorem hiTU_enum (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG hiN * ω)) :
    CdUpper S l ∧ CdLower S l :=
  hgV_locD_enum hiTU S (hiTU_γK S) hr hl

/-- **CapV at every range restart below `ι(Γ(φ(Ω₁+1, G+1))·ω)`** (UNCONDITIONAL). -/
theorem hiTU_capV (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG hiN * ω)) :
    CdCapV S l :=
  hgV_locD_capV hiTU S (hiTU_γK S) hr hl

/-- **THE ROAD**: UPPER, LOWER, CapV asked only at `λ ≥ ι(Γ(φ(Ω₁+1, G+1))·ω)` (CapV also `υ_λ < L(ω)`), (CL), EQ,
TCrest, (EMB₂) ⟹ `ν_C = L(ω+1)`, `L(ω) ≤ ν_C`, `L(ω) <₂ L(ω+1)`, (P), (Q), the reaches. -/
theorem hiTU_road (S : InaccSeq.{0}) (hU : ∀ l, CdRange S l → iota S (gcG hiN * ω) ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S (gcG hiN * ω) ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S (gcG hiN * ω) ≤ l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  gv_road_of S _ (fun _ hr h => hiTU_enum S hr h) (fun _ hr h => hiTU_capV S hr h) hU hL hV hC hEQ hrest hB2

/-- **`Γ(φ(Ω₁+1, G+1))·ω < Ω₂`.** -/
theorem hiN_lt_Om2 : gcG hiN * ω < Om (1 + 1) := by
  have hBE : InE Tf.tfBG := Low.opow_eq_self_of_SC Tf.tfBG_SC
  have hO : (Om1 : Ordinal.{0}) < Tf.tfBG := Tf.tfBG_gt
  have h1 : (1 : Ordinal.{0}) < Tf.tfBG := one_lt_omega0.trans (omega0_lt_inE hBE)
  have hG1 : gcG 1 < Tf.tfBG := by
    rw [Tf.tf_gcG, ← Tf.tfBG_fix]
    exact gamma_lt_gamma.2 ((inE_indec hBE).add_lt ((inE_indec hBE).add_lt hO h1) h1)
  have h2 : gcG hiN < Tf.tfBG := by
    rw [Tf.tf_gcG, ← Tf.tfBG_fix]
    exact gamma_lt_gamma.2 ((inE_indec hBE).add_lt ((inE_indec hBE).add_lt hO h1) (hiN_lt1.trans hG1))
  exact (InE.mul_lt hBE h2 (omega0_lt_inE hBE)).trans Tf.tfBG_lt_Om2

/-- **`P(Γ(φ(Ω₁+1, G+1))·ω) < L(0)`.** -/
theorem hiTU_P (S : InaccSeq.{0}) : Pv S (gcG hiN * ω) < Nc.ncL S 0 := ga_Pv_lt_L0 S hiN_lt_Om2.le

/-- **`φ(Ω₁, G+ε₀) < φ(Ω₁+1, G+1)`.** -/
theorem hgFE_lt_hiN : hgFE < hiN := by
  have h : gcG 0 + ε₀ < hiN :=
    (inE_indec hiN_E).add_lt hiG_lt_N ((gc_eps0_le_Om1.trans_lt (gcG_Om1_lt 0)).trans hiG_lt_N)
  have h2 := (isNormal_veblen Om1).strictMono h
  rwa [hiN_fix] at h2

/-- **The order of the frontiers**: `Γ(φ(Ω₁, G+ε₀)) < Γ(φ(Ω₁+1, G+1))`,
`ι(Γ(φ(Ω₁, G+ε₀))) ≤ ι(Γ(φ(Ω₁+1, G+1))·ω) ≤ ι(Ω₂)` and `P(Γ(φ(Ω₁+1, G+1))·ω) ≤ P(Ω₂) < L(0)`. -/
theorem hiTU_fr_order (S : InaccSeq.{0}) :
    gcG hgFE < gcG hiN ∧ iota S (gcG hgFE) ≤ iota S (gcG hiN * ω) ∧
      iota S (gcG hiN * ω) ≤ iota S (Om (1 + 1)) ∧
      Pv S (gcG hiN * ω) ≤ Pv S (Om (1 + 1)) ∧ Pv S (Om (1 + 1)) < Nc.ncL S 0 := by
  have hV : InE (gcG hiN) := Low.opow_eq_self_of_SC (gcG_SC _)
  refine ⟨gcG_lt hgFE_lt_hiN, iota_mono _ _ ((gcG_lt hgFE_lt_hiN).trans_le
    (le_mul_of_one_le_right' one_lt_omega0.le)).le, iota_mono _ _ hiN_lt_Om2.le, Nm.Pv_mono hiN_lt_Om2.le,
    ga_Pv_lt_L0 S le_rfl⟩

end Googology.Trans.PoR.InaccPsi.R2.Hi
