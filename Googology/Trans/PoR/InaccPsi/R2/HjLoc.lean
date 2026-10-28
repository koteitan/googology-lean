import Googology.Trans.PoR.InaccPsi.R2.HjU

/-!
# HjLoc: `φ(Ω₁+Ω₁, G+1)` IS LOCATED; THE FRONTIER PASSES THE LEVEL `Ω₁ + K`

`Hj.hjU` has base gate `0 < K`, so `Hg.hgV_locD` locates its bound `φ(Ω₁·2, G+1) = φ(Ω₁+Ω₁, G+1)`: ENUM-REACH and
CapV hold at every range restart below `ι(Γ(φ(Ω₁+Ω₁, G+1))·ω)`, UNCONDITIONALLY; this passes the wall of round 102
(the levels `Ω₁ + κ`, `K ≤ κ < Ω₁`, are now inside a located system).

* `hjU_γK`, `hjU_loc`, `hjU_blk`, `hjU_enum`, `hjU_capV`, `hjU_road`, `hjU_lt_Om2`, `hjU_fr_order`.

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hj

open Googology.Trans.PoR.InaccPsi.R2.Hi Googology.Trans.PoR.InaccPsi.R2.Hg
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

theorem hjU_γK (S : InaccSeq.{0}) : hjU.γ < Td.tdK S := hg_K_pos S

/-- **`φ(Ω₁+Ω₁, G+1)` IS LOCATED**: `Λ⁺ = ι(Γ(φ(Ω₁+Ω₁, G+1))·ω)`, `P(Γ(φ(Ω₁+Ω₁, G+1))·ω) < L(0)`
(UNCONDITIONAL). -/
theorem hjU_loc (S : InaccSeq.{0}) :
    ∃ X : XtSys, XtTopPkg X ∧ xtB1 X = iota S (gcG hjB * ω) ∧
      upsilon (xtB1 X) = Pv S (gcG hjB * ω) ∧ Pv S (gcG hjB * ω) < Nc.ncL S 0 :=
  hgV_locD hjU S (hjU_γK S)

/-- **Theorem BLK^O below `P(Γ(φ(Ω₁+Ω₁, G+1))·ω)`, with the exact reaches** (UNCONDITIONAL). -/
theorem hjU_blk (S : InaccSeq.{0}) :
    let X := gsX hjU.step.toRS _ hjU.E_lt_B.le hjU.B_lt_NB S (hgV_locD_g hjU S (hjU_γK S))
    (∀ c' d, c' < d → d < upsilon (xtB1 X) → (le2 c' d ↔ ∃ μ, ∃ j : ℕ, (μ = 0 ∨ IsRestartIdx μ) ∧ μ < xtB1 X ∧
        c' = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧ d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < xtB1 X →
      (∀ c' < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c' g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec X l)) ∧
    (∀ α < upsilon (xtB1 X), ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  hgV_locD_blk hjU S (hjU_γK S)

/-- **ENUM-REACH at every range restart below `ι(Γ(φ(Ω₁+Ω₁, G+1))·ω)`, fixed points included** (UNCONDITIONAL). -/
theorem hjU_enum (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG hjB * ω)) :
    CdUpper S l ∧ CdLower S l :=
  hgV_locD_enum hjU S (hjU_γK S) hr hl

/-- **CapV at every range restart below `ι(Γ(φ(Ω₁+Ω₁, G+1))·ω)`** (UNCONDITIONAL). -/
theorem hjU_capV (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG hjB * ω)) :
    CdCapV S l :=
  hgV_locD_capV hjU S (hjU_γK S) hr hl

/-- **THE ROAD**: UPPER, LOWER, CapV asked only at `λ ≥ ι(Γ(φ(Ω₁+Ω₁, G+1))·ω)` (CapV also `υ_λ < L(ω)`), (CL), EQ,
TCrest, (EMB₂) ⟹ `ν_C = L(ω+1)`, `L(ω) ≤ ν_C`, `L(ω) <₂ L(ω+1)`, (P), (Q), the reaches. -/
theorem hjU_road (S : InaccSeq.{0}) (hU : ∀ l, CdRange S l → iota S (gcG hjB * ω) ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S (gcG hjB * ω) ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S (gcG hjB * ω) ≤ l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  gv_road_of S _ (fun _ hr h => hjU_enum S hr h) (fun _ hr h => hjU_capV S hr h) hU hL hV hC hEQ hrest hB2

/-- **`Γ(φ(Ω₁+Ω₁, G+1))·ω < Ω₂`.** -/
theorem hjU_lt_Om2 : gcG hjB * ω < Om (1 + 1) := by
  have hBE : InE Tf.tfBG := Low.opow_eq_self_of_SC Tf.tfBG_SC
  have hO : (Om1 : Ordinal.{0}) < Tf.tfBG := Tf.tfBG_gt
  have h1 : (1 : Ordinal.{0}) < Tf.tfBG := one_lt_omega0.trans (omega0_lt_inE hBE)
  have hG1 : gcG 1 < Tf.tfBG := by
    rw [Tf.tf_gcG, ← Tf.tfBG_fix]
    exact gamma_lt_gamma.2 ((inE_indec hBE).add_lt ((inE_indec hBE).add_lt hO h1) h1)
  have h2 : gcG hjB < Tf.tfBG := by
    rw [Tf.tf_gcG, ← Tf.tfBG_fix]
    exact gamma_lt_gamma.2 ((inE_indec hBE).add_lt ((inE_indec hBE).add_lt hO h1) (hjB_lt1.trans hG1))
  exact (InE.mul_lt hBE h2 (omega0_lt_inE hBE)).trans Tf.tfBG_lt_Om2

/-- **The order of the frontiers**: `φ(Ω₁+K, G+1) < φ(Ω₁+Ω₁, G+1)`, `ι(Γ(φ(Ω₁+K, G+1))) ≤ ι(Γ(φ(Ω₁+Ω₁, G+1))·ω) ≤
ι(Ω₂)` and `P(Γ(φ(Ω₁+Ω₁, G+1))·ω) ≤ P(Ω₂) < L(0)`. -/
theorem hjU_fr_order (S : InaccSeq.{0}) :
    hiGE S < hjB ∧ iota S (gcG (hiGE S)) ≤ iota S (gcG hjB * ω) ∧
      iota S (gcG hjB * ω) ≤ iota S (Om (1 + 1)) ∧
      Pv S (gcG hjB * ω) ≤ Pv S (Om (1 + 1)) ∧ Pv S (Om (1 + 1)) < Nc.ncL S 0 := by
  have hlt := hiGE_lt_hjB S
  refine ⟨hlt, ?_, iota_mono _ _ hjU_lt_Om2.le, Nm.Pv_mono hjU_lt_Om2.le, ga_Pv_lt_L0 S le_rfl⟩
  exact iota_mono _ _ ((gcG_lt hlt).trans_le (le_mul_of_one_le_right' one_lt_omega0.le)).le

end Googology.Trans.PoR.InaccPsi.R2.Hj
