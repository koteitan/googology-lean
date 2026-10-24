import Googology.Trans.PoR.InaccPsi.R2.GpRec
import Googology.Trans.PoR.InaccPsi.R2.TfPsi

/-!
# THE FRONTIER `ι(Γ_{Ω₁+1+ε_{G+ε₀}})`: BLK^O, exact reaches, ENUM-REACH and CapV below it, and the road

`G = Γ_{Ω₁+1}`, `Γ(c) = gcG c = Γ_{Ω₁+1+c}`, `gpE = φ(1, G + ε₀) = ε_{G+ε₀}`.  For every `ν < ε₀` the digit system
`gpD ν` (`R2.GpRec`) has the bound `ε_{G+ν}`; the generic theorems of `R2.GoRS` give, for each `ν`, the supremum
`ι(Γ(ε_{G+ν}))` of its frontiers, BLK^O with the exact reaches below `P(Γ(ε_{G+ν}))`, ENUM-REACH and CapV.  The frontier
of the whole recursion is `ι(Γ(gpE)) = sup_{ν<ε₀} ι(Γ(ε_{G+ν}))` (`gpE_cof`: `ι` is continuous at limits by its
definition, `Γ(·)` and `φ(1, G + ·)` are normal), so:

* `gp_sup`, `gp_blk`, `gp_enum`, `gp_capV`, `gp_loc` (**every code with gate below `ε₀` of every `gpD ν` located**);
* `gpE_codes` (**every code below `ε_{G+ε₀}` is a code of some `gpD ν`, `ν < ε₀`**), `gpE_cof`;
* `gpE_enum`, `gpE_capV` (**ENUM-REACH (fixed points included) and CapV at every range restart below
  `ι(Γ(ε_{G+ε₀}))`**),
  `gpE_road` (**THE ROAD**: UPPER, LOWER, CapV asked only at `λ ≥ ι(Γ(ε_{G+ε₀}))`);
* `gpE_le_Om2`, `gpE_P` (**`Γ(ε_{G+ε₀}) < Ω₂` and `P(Γ(ε_{G+ε₀})) < L(0)`**), `gpE_fr_order` (**the old frontier
  `ι(Γ(ε_{G+ω^{ω^ω}}))` and every `ι(Γ(ε_{G+ν}))` lie below `ι(Γ(ε_{G+ε₀})) ≤ ι(Ω₂)`**), `gp_top_B`.

No new axiom.  New definition: `gpE`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gp

open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gj
  Googology.Trans.PoR.InaccPsi.R2.Gi Googology.Trans.PoR.InaccPsi.R2.Gn Googology.Trans.PoR.InaccPsi.R2.Go
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Lp Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Gd

/-- **The bound of the whole recursion**: `ε_{G+ε₀} = φ(1, G + ε₀)`. -/
noncomputable def gpE : Ordinal.{0} := veblen 1 (gcG 0 + ε₀)

/-! ## Each `gpD ν` -/

section Each

variable {ν : Ordinal.{0}} (hν : ν < ε₀)
include hν

/-- **`sup = ι(Γ(ε_{G+ν}))`, `υ` of it `= P(Γ(ε_{G+ν})) < L(0)`.** -/
theorem gp_sup (S : InaccSeq.{0}) : ((gpD ν).toRS.gmFam S).famSup = iota S (gcG (veblen 1 (gcG 0 + ν))) ∧
    upsilon ((gpD ν).toRS.gmFam S).famSup = Pv S (gcG (veblen 1 (gcG 0 + ν))) ∧
    Pv S (gcG (veblen 1 (gcG 0 + ν))) < Nc.ncL S 0 := by
  rw [← gpD_B hν]; exact (gpD ν).go_sup S

/-- **ENUM-REACH at every range restart below `ι(Γ(ε_{G+ν}))`, fixed points included.** -/
theorem gp_enum (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l)
    (hl : l < iota S (gcG (veblen 1 (gcG 0 + ν)))) : CdUpper S l ∧ CdLower S l :=
  (gpD ν).go_enum S hr (by rw [gpD_B hν]; exact hl)

/-- **CapV at every range restart below `ι(Γ(ε_{G+ν}))`.** -/
theorem gp_capV (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l)
    (hl : l < iota S (gcG (veblen 1 (gcG 0 + ν)))) : CdCapV S l :=
  (gpD ν).go_capV S hr (by rw [gpD_B hν]; exact hl)

/-- **Every code `c ∈ [ε_{Ω₁+1}, ε_{G+ν})` with gate below `ε₀` located**: `Λ⁺ = ι(Γ(c)·ω)`, `P(Γ(c)·ω) < L(0)`. -/
theorem gp_loc {c : Ordinal.{0}} (h : gfE ≤ c) (hc : c < veblen 1 (gcG 0 + ν)) (hg : (gpD ν).g c < ε₀)
    (S : InaccSeq.{0}) :
    xtB1 ((gpD ν).toRS.gmX c h (by show c < (gpD ν).B; rw [gpD_B hν]; exact hc) hg) = iota S (gcG c * ω) ∧
    Pv S (gcG c * ω) < Nc.ncL S 0 :=
  let h' := (gpD ν).go_loc h (by rw [gpD_B hν]; exact hc) hg S
  ⟨h'.1, h'.2.2⟩

end Each

/-- **Theorem BLK^O below `P(Γ(ε_{G+ν}))`** (the supremum of `gpD ν`, `gp_sup`), with the exact reaches. -/
theorem gp_blk (ν : Ordinal.{0}) (S : InaccSeq.{0}) :
    (∀ c d, c < d → d < upsilon ((gpD ν).toRS.gmFam S).famSup → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < ((gpD ν).toRS.gmFam S).famSup ∧
        c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → ∀ k, l < ((gpD ν).toRS.gmFam S).bd k →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + ((gpD ν).toRS.gmFam S).off k l)) ∧
    (∀ α < upsilon ((gpD ν).toRS.gmFam S).famSup, ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  (gpD ν).go_blk S

/-- `goTop` (round 86) has the bound of `gpD (ω^{ω^ω})`. -/
theorem gp_top_B : goTop.B = (gpD (ω ^ ω ^ ω)).B := by
  rw [goTop_B, gpD_B (go_opow_lt_eps0 (go_opow_lt_eps0 (omega0_lt_epsilon 0)))]

/-! ## The whole recursion -/

theorem gpE_lim : IsSuccLimit gpE := ev_isSuccLimit_of_inE (omega0_opow_epsilon _)

/-- **Every code below `ε_{G+ε₀}` is a code of some `gpD ν`, `ν < ε₀`.** -/
theorem gpE_codes {c : Ordinal.{0}} (hc : c < gpE) : ∃ ν, ν < ε₀ ∧ c < (gpD ν).B := by
  obtain ⟨t, ht, hct⟩ := ((isNormal_veblen 1).lt_iff_exists_lt (isSuccLimit_add _ go_eps0_lim)).1 hc
  obtain ⟨d, hd, htd⟩ := (lt_add_iff (epsilon_pos 0).ne').1 ht
  exact ⟨d, hd, by rw [gpD_B hd]; exact hct.trans_le ((isNormal_veblen 1).monotone htd)⟩

theorem gpD_B_lt_E {ν : Ordinal.{0}} (hν : ν < ε₀) : (gpD ν).B < gpE := by
  rw [gpD_B hν]; exact (isNormal_veblen 1).strictMono ((add_lt_add_iff_left _).2 hν)

/-- **`ι(Γ(ε_{G+ε₀})) = sup_{ν<ε₀} ι(Γ(ε_{G+ν}))`**: below it every point lies below some `ι(Γ(ε_{G+ν}))`. -/
theorem gpE_cof (S : InaccSeq.{0}) {l : Ordinal.{0}} (hl : l < iota S (gcG gpE)) :
    ∃ ν, ν < ε₀ ∧ l < iota S (gcG (gpD ν).B) := by
  have hlim : IsSuccLimit (gcG gpE) := ev_isSuccLimit_of_inE (Low.opow_eq_self_of_SC (gcG_SC _))
  rw [iota_limit hlim] at hl
  haveI : Nonempty (Iio (gcG gpE)) := ⟨⟨0, hlim.bot_lt⟩⟩
  obtain ⟨e, he⟩ := (lt_ciSup_iff (iota_bdd _)).1 hl
  obtain ⟨β, hβ, heβ⟩ := gcG_lt_of_lt_limit gpE_lim e.2
  obtain ⟨ν, hν, hβν⟩ := gpE_codes hβ
  exact ⟨ν, hν, he.trans_le (iota_mono _ _ (heβ.trans (gcG_lt hβν)).le)⟩

theorem gpE_le_iota {ν : Ordinal.{0}} (hν : ν < ε₀) (S : InaccSeq.{0}) :
    iota S (gcG (gpD ν).B) ≤ iota S (gcG gpE) :=
  iota_mono _ _ (gcG_lt (gpD_B_lt_E hν)).le

/-- **ENUM-REACH at every range restart below `ι(Γ(ε_{G+ε₀}))`, fixed points included.** -/
theorem gpE_enum (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG gpE)) :
    CdUpper S l ∧ CdLower S l := by
  obtain ⟨ν, -, h⟩ := gpE_cof S hl
  exact (gpD ν).go_enum S hr h

/-- **CapV at every range restart below `ι(Γ(ε_{G+ε₀}))`.** -/
theorem gpE_capV (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG gpE)) :
    CdCapV S l := by
  obtain ⟨ν, -, h⟩ := gpE_cof S hl
  exact (gpD ν).go_capV S hr h

/-- **THE ROAD**: UPPER, LOWER, CapV asked only at `λ ≥ ι(Γ(ε_{G+ε₀}))` (CapV also `υ_λ < L(ω)`), (CL), EQ,
TCrest, (EMB₂) ⟹ `ν_C = L(ω+1)`, `L(ω) ≤ ν_C`, `L(ω) <₂ L(ω+1)`, (P), (Q), the reaches. -/
theorem gpE_road (S : InaccSeq.{0}) (hU : ∀ l, CdRange S l → iota S (gcG gpE) ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S (gcG gpE) ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S (gcG gpE) ≤ l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  refine goGl.go_road S (fun l hr _ => ?_) (fun l hr _ => ?_) (fun l hr hω _ => ?_) hC hEQ hrest hB2
  · by_cases h : l < iota S (gcG gpE)
    · exact (gpE_enum S hr h).1
    · exact hU l hr (not_lt.1 h)
  · by_cases h : l < iota S (gcG gpE)
    · exact (gpE_enum S hr h).2
    · exact hL l hr (not_lt.1 h)
  · by_cases h : l < iota S (gcG gpE)
    · exact gpE_capV S hr h
    · exact hV l hr hω (not_lt.1 h)

/-! ## The place of the frontier -/

theorem gpE_lt_G1 : gpE < gcG 1 := by
  have hE : InE (gcG 1) := Low.opow_eq_self_of_SC (gcG_SC 1)
  have h1 : gcG 0 + ε₀ < gcG 1 :=
    (inE_indec hE).add_lt (gcG_lt zero_lt_one) ((go_eps0_le gl_G0_E).trans_lt (gcG_lt zero_lt_one))
  exact (gcG_SC 1).2 1 (one_lt_omega0.trans (omega0_lt_inE hE)) _ h1

/-- **`Γ(ε_{G+ε₀}) < Ω₂`.** -/
theorem gpE_le_Om2 : gcG gpE < Om (1 + 1) := by
  have hBE : InE Tf.tfBG := Low.opow_eq_self_of_SC Tf.tfBG_SC
  have hO : (Om1 : Ordinal.{0}) < Tf.tfBG := Tf.tfBG_gt
  have h1 : (1 : Ordinal.{0}) < Tf.tfBG := one_lt_omega0.trans (omega0_lt_inE hBE)
  have hG1 : gcG 1 < Tf.tfBG := by
    rw [Tf.tf_gcG, ← Tf.tfBG_fix]
    exact gamma_lt_gamma.2 ((inE_indec hBE).add_lt ((inE_indec hBE).add_lt hO h1) h1)
  have h2 : gcG gpE < Tf.tfBG := by
    rw [Tf.tf_gcG, ← Tf.tfBG_fix]
    exact gamma_lt_gamma.2 ((inE_indec hBE).add_lt ((inE_indec hBE).add_lt hO h1) (gpE_lt_G1.trans hG1))
  exact h2.trans Tf.tfBG_lt_Om2

/-- **`P(Γ(ε_{G+ε₀})) < L(0)`.** -/
theorem gpE_P (S : InaccSeq.{0}) : Pv S (gcG gpE) < Nc.ncL S 0 := ga_Pv_lt_L0 S gpE_le_Om2.le

/-- **The order of the frontiers**: `ι(Γ(ε_{G+ω^{ω^ω}}))` (round 86) and every `ι(Γ(ε_{G+ν}))`, `ν < ε₀`, lie below
`ι(Γ(ε_{G+ε₀})) ≤ ι(Ω₂)`; `P(Γ(ε_{G+ε₀})) ≤ P(Ω₂) < L(0)`. -/
theorem gpE_fr_order (S : InaccSeq.{0}) :
    iota S (gcG goTop.B) ≤ iota S (gcG gpE) ∧ (∀ ν, ν < ε₀ → iota S (gcG (gpD ν).B) ≤ iota S (gcG gpE)) ∧
      iota S (gcG gpE) ≤ iota S (Om (1 + 1)) ∧ Pv S (gcG gpE) ≤ Pv S (Om (1 + 1)) ∧
      Pv S (Om (1 + 1)) < Nc.ncL S 0 := by
  have hw : ω ^ ω ^ ω < (ε₀ : Ordinal.{0}) := go_opow_lt_eps0 (go_opow_lt_eps0 (omega0_lt_epsilon 0))
  refine ⟨?_, fun ν hν => gpE_le_iota hν S, iota_mono _ _ gpE_le_Om2.le, Nm.Pv_mono gpE_le_Om2.le,
    ga_Pv_lt_L0 S le_rfl⟩
  rw [gp_top_B]; exact gpE_le_iota hw S

end Googology.Trans.PoR.InaccPsi.R2.Gp
