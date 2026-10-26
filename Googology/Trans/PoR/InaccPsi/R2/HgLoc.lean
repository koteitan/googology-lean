import Googology.Trans.PoR.InaccPsi.R2.HgU

/-!
# HgLoc: `φ(Ω₁, G+1)` IS LOCATED; THE FRONTIER `ι(Γ(φ(Ω₁, G+1))·ω)` PASSES `K`

The union `Hg.hgU` of all `Hf.hfGL ν`, `ν < Ω₁`, has base gate `0 < K`, so the location theorem of `HgVD`
(`Hg.hgV_locD`) applies: `Λ⁺ = ι(Γ(φ(Ω₁, G+1))·ω)`, `P(Γ(φ(Ω₁, G+1))·ω) < L(0)`; BLK^O, the exact reaches,
ENUM-REACH and CapV hold at every range restart below it, unconditionally.  The same holds for every finite iterate
of the step (`HgVD.step`: the bound `B ↦ ε_{B+1}`), base gate `0`.

* `hgU_loc`, `hgU_blk`, `hgU_enum`, `hgU_capV`, `hgU_road` (**THE ROAD**, hypotheses only at
  `λ ≥ ι(Γ(φ(Ω₁, G+1))·ω)`), `hgU_lt_Om2`, `hgU_fr_order` (**`ι(Γ(φ(K, G+1))) ≤ ι(Γ(φ(Ω₁, G+1))·ω) ≤ ι(Ω₂)`**);
* `hgIt` (the `n`-th step of `hgU`: bound `ε`-iterate `e_n`, `e_0 = φ(Ω₁, G+1)`, `e_{n+1} = ε_{e_n+1}`), `hgIt_γ`,
  `hgIt_loc`, `hgIt_enum`, `hgIt_capV`.

No new axiom.  New definitions: `hgIt`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hg

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

theorem hg_K_pos (S : InaccSeq.{0}) : (0 : Ordinal.{0}) < Td.tdK S := (hfK_lim S).bot_lt

theorem hgU_γK (S : InaccSeq.{0}) : hgU.γ < Td.tdK S := hg_K_pos S

/-- **`φ(Ω₁, G+1)` IS LOCATED**: `Λ⁺ = ι(Γ(φ(Ω₁, G+1))·ω)`, `P(Γ(φ(Ω₁, G+1))·ω) < L(0)` (UNCONDITIONAL). -/
theorem hgU_loc (S : InaccSeq.{0}) :
    ∃ X : XtSys, XtTopPkg X ∧ xtB1 X = iota S (gcG hgB * ω) ∧
      upsilon (xtB1 X) = Pv S (gcG hgB * ω) ∧ Pv S (gcG hgB * ω) < Nc.ncL S 0 :=
  hgV_locD hgU S (hgU_γK S)

/-- **Theorem BLK^O below `P(Γ(φ(Ω₁, G+1))·ω)`, with the exact reaches** (UNCONDITIONAL). -/
theorem hgU_blk (S : InaccSeq.{0}) :
    let X := gsX hgU.step.toRS _ hgU.E_lt_B.le hgU.B_lt_NB S (hgV_locD_g hgU S (hgU_γK S))
    (∀ c' d, c' < d → d < upsilon (xtB1 X) → (le2 c' d ↔ ∃ μ, ∃ j : ℕ, (μ = 0 ∨ IsRestartIdx μ) ∧ μ < xtB1 X ∧
        c' = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧ d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < xtB1 X →
      (∀ c' < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c' g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec X l)) ∧
    (∀ α < upsilon (xtB1 X), ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  hgV_locD_blk hgU S (hgU_γK S)

/-- **ENUM-REACH at every range restart below `ι(Γ(φ(Ω₁, G+1))·ω)`, fixed points included** (UNCONDITIONAL). -/
theorem hgU_enum (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG hgB * ω)) :
    CdUpper S l ∧ CdLower S l :=
  hgV_locD_enum hgU S (hgU_γK S) hr hl

/-- **CapV at every range restart below `ι(Γ(φ(Ω₁, G+1))·ω)`** (UNCONDITIONAL). -/
theorem hgU_capV (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG hgB * ω)) :
    CdCapV S l :=
  hgV_locD_capV hgU S (hgU_γK S) hr hl

/-- **THE ROAD**: UPPER, LOWER, CapV asked only at `λ ≥ ι(Γ(φ(Ω₁, G+1))·ω)` (CapV also `υ_λ < L(ω)`), (CL), EQ,
TCrest, (EMB₂) ⟹ `ν_C = L(ω+1)`, `L(ω) ≤ ν_C`, `L(ω) <₂ L(ω+1)`, (P), (Q), the reaches. -/
theorem hgU_road (S : InaccSeq.{0}) (hU : ∀ l, CdRange S l → iota S (gcG hgB * ω) ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S (gcG hgB * ω) ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S (gcG hgB * ω) ≤ l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  gv_road_of S _ (fun _ hr h => hgU_enum S hr h) (fun _ hr h => hgU_capV S hr h) hU hL hV hC hEQ hrest hB2

/-- **`Γ(φ(Ω₁, G+1))·ω < Ω₂`.** -/
theorem hgU_lt_Om2 : gcG hgB * ω < Om (1 + 1) := by
  have hBE : InE Tf.tfBG := Low.opow_eq_self_of_SC Tf.tfBG_SC
  have hO : (Om1 : Ordinal.{0}) < Tf.tfBG := Tf.tfBG_gt
  have h1 : (1 : Ordinal.{0}) < Tf.tfBG := one_lt_omega0.trans (omega0_lt_inE hBE)
  have hG1 : gcG 1 < Tf.tfBG := by
    rw [Tf.tf_gcG, ← Tf.tfBG_fix]
    exact gamma_lt_gamma.2 ((inE_indec hBE).add_lt ((inE_indec hBE).add_lt hO h1) h1)
  have h2 : gcG hgB < Tf.tfBG := by
    rw [Tf.tf_gcG, ← Tf.tfBG_fix]
    exact gamma_lt_gamma.2 ((inE_indec hBE).add_lt ((inE_indec hBE).add_lt hO h1) (hgB_lt1.trans hG1))
  exact (InE.mul_lt hBE h2 (omega0_lt_inE hBE)).trans Tf.tfBG_lt_Om2

/-- **The order of the frontiers**: `Γ(φ(K, G+1)) < Γ(φ(Ω₁, G+1))`, `ι(Γ(φ(K, G+1))) ≤ ι(Γ(φ(Ω₁, G+1))·ω) ≤ ι(Ω₂)` and
`P(Γ(φ(Ω₁, G+1))·ω) ≤ P(Ω₂) < L(0)`. -/
theorem hgU_fr_order (S : InaccSeq.{0}) :
    gcG (hfGE S) < gcG hgB ∧ iota S (gcG (hfGE S)) ≤ iota S (gcG hgB * ω) ∧
      iota S (gcG hgB * ω) ≤ iota S (Om (1 + 1)) ∧
      Pv S (gcG hgB * ω) ≤ Pv S (Om (1 + 1)) ∧ Pv S (Om (1 + 1)) < Nc.ncL S 0 := by
  have hV : InE (gcG hgB) := Low.opow_eq_self_of_SC (gcG_SC _)
  have hlt : hfGE S < hgB := hd_veb_left_lt (hf_K_lt S) _
  refine ⟨gcG_lt hlt, ?_, iota_mono _ _ hgU_lt_Om2.le, Nm.Pv_mono hgU_lt_Om2.le, ga_Pv_lt_L0 S le_rfl⟩
  exact iota_mono _ _ ((gcG_lt hlt).trans_le (le_mul_of_one_le_right' one_lt_omega0.le)).le

/-! ## The finite iterates of the step -/

/-- **The `n`-th step of `hgU`**: bound `e_n` (`e_0 = φ(Ω₁, G+1)`, `e_{n+1} = ε_{e_n+1}`), base gate `0`. -/
noncomputable def hgIt : ℕ → HgVD
  | 0 => hgU
  | n + 1 => (hgIt n).step

theorem hgIt_γ : ∀ n : ℕ, (hgIt n).γ = 0
  | 0 => rfl
  | n + 1 => by show (hgIt n).step.γ = 0; rw [HgVD.step_γ]; exact hgIt_γ n

theorem hgIt_B_succ (n : ℕ) : (hgIt (n + 1)).B = eN (hgIt n).B := rfl

theorem hgIt_γK (S : InaccSeq.{0}) (n : ℕ) : (hgIt n).γ < Td.tdK S := by rw [hgIt_γ]; exact hg_K_pos S

/-- **Every `e_n` IS LOCATED**: `Λ⁺ = ι(Γ(e_n)·ω)`, `P(Γ(e_n)·ω) < L(0)` (UNCONDITIONAL). -/
theorem hgIt_loc (S : InaccSeq.{0}) (n : ℕ) :
    ∃ X : XtSys, XtTopPkg X ∧ xtB1 X = iota S (gcG (hgIt n).B * ω) ∧
      upsilon (xtB1 X) = Pv S (gcG (hgIt n).B * ω) ∧ Pv S (gcG (hgIt n).B * ω) < Nc.ncL S 0 :=
  hgV_locD (hgIt n) S (hgIt_γK S n)

/-- **ENUM-REACH below every `ι(Γ(e_n)·ω)`** (UNCONDITIONAL). -/
theorem hgIt_enum (S : InaccSeq.{0}) (n : ℕ) {l : Ordinal.{0}} (hr : CdRange S l)
    (hl : l < iota S (gcG (hgIt n).B * ω)) : CdUpper S l ∧ CdLower S l :=
  hgV_locD_enum (hgIt n) S (hgIt_γK S n) hr hl

/-- **CapV below every `ι(Γ(e_n)·ω)`** (UNCONDITIONAL). -/
theorem hgIt_capV (S : InaccSeq.{0}) (n : ℕ) {l : Ordinal.{0}} (hr : CdRange S l)
    (hl : l < iota S (gcG (hgIt n).B * ω)) : CdCapV S l :=
  hgV_locD_capV (hgIt n) S (hgIt_γK S n) hr hl

end Googology.Trans.PoR.InaccPsi.R2.Hg
