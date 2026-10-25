import Googology.Trans.PoR.InaccPsi.R2.GwRec

/-!
# LOCATION OF EVERY BOUND WITH GATE BELOW `K`; THE FRONTIER `ι(Γ(ζ_{G+1}))`

The bound `B = ε_{G+ν}` of any gated digit system without a cofinal sequence (`Gv.GvD`) whose base gate is below
`K = ψ_{Ω₁}(Ω_ω)` is located by its step (`gw_locD`, `Gs.gsLoc`): `Λ⁺ = ι(Γ(B)·ω)`, `P(Γ(B)·ω) < L(0)`, with
ENUM-REACH and CapV at every range restart below it and BLK^O, exact reaches below `P(Γ(B)·ω)`.

The tower `t₀ = 1`, `t_{k+1} = ε_{G+t_k}` (`gwT`) is cofinal in `ζ_{G+1}` (`gwT_sup`), and every `gwD t_k` has base
gate below every `ε`-number (`gwT_gate`: the gate of the code `t_{k+1}` is the base gate of `gwD t_k`, by the step).
Hence the bounds `ε_{G+t_k} = t_{k+1}` are located and **the new frontier is `ι(Γ(ζ_{G+1}))`** (was
`ι(Γ(ε_{G+Ω₁·ε₀}))`): ENUM-REACH and CapV at every range restart below it, unconditionally.

* `gw_locD_g`, `gw_locD`, `gw_locD_enum`, `gw_locD_capV`, `gw_locD_blk` (every `GvD` with gate below `K`);
* `gw_loc`, `gw_loc_enum`, `gw_loc_capV` (every index `ν < ζ_{G+1}` with `γ(gwD ν) < K`);
* `gwT`, `gwT_pos`, `gwT_lt`, `gwT_B`, `gwT_gate`, `gwT_K`, `gwT_sup`; `gwZ`, `gwZ_codes`, `gwZ_cof`, `gwZ_enum`,
  `gwZ_capV`, `gwZ_blk`, `gwZ_road` (**THE ROAD**), `gwZ_le_Om2`, `gwZ_P`, `gwZ_fr_order`.

No new axiom.  New definitions: `gwT`, `gwZ`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gw

open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gj
  Googology.Trans.PoR.InaccPsi.R2.Gi Googology.Trans.PoR.InaccPsi.R2.Gn Googology.Trans.PoR.InaccPsi.R2.Go
  Googology.Trans.PoR.InaccPsi.R2.Gp
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Lp Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Gd

/-! ## Location of the bound of any system with gate below `K` -/

section LocD

variable (D : GvD) (S : InaccSeq.{0}) (hγ : D.γ < Td.tdK S)
include hγ

theorem gw_locD_g : D.step.toRS.K.gt D.B < Td.tdK S := by
  rw [GsD.toRS_gt, GvD.step_g_B]; exact hγ

/-- **THE BOUND OF EVERY GATED DIGIT SYSTEM WITH BASE GATE BELOW `K` IS LOCATED**: `Λ⁺ = ι(Γ(B)·ω)`,
`P(Γ(B)·ω) < L(0)`. -/
theorem gw_locD : ∃ X : XtSys, XtTopPkg X ∧ xtB1 X = iota S (gcG D.B * ω) ∧
    upsilon (xtB1 X) = Pv S (gcG D.B * ω) ∧ Pv S (gcG D.B * ω) < Nc.ncL S 0 :=
  ⟨gsX D.step.toRS _ D.E_lt_B.le D.B_lt_NB S (gw_locD_g D S hγ),
    gsX_pkg D.step.toRS _ D.E_lt_B.le D.B_lt_NB S (gw_locD_g D S hγ),
    gsLoc D.step.toRS _ D.E_lt_B.le D.B_lt_NB S (gw_locD_g D S hγ)⟩

theorem gw_locD_enum {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG D.B * ω)) :
    CdUpper S l ∧ CdLower S l :=
  gsEnum D.step.toRS _ D.E_lt_B.le D.B_lt_NB S (gw_locD_g D S hγ) hr hl

theorem gw_locD_capV {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG D.B * ω)) : CdCapV S l :=
  gsCapV D.step.toRS _ D.E_lt_B.le D.B_lt_NB S (gw_locD_g D S hγ) hr hl

/-- **Theorem BLK^O below `P(Γ(B)·ω)`**, with the exact reaches. -/
theorem gw_locD_blk :
    let X := gsX D.step.toRS _ D.E_lt_B.le D.B_lt_NB S (gw_locD_g D S hγ)
    (∀ c' d, c' < d → d < upsilon (xtB1 X) → (le2 c' d ↔ ∃ μ, ∃ j : ℕ, (μ = 0 ∨ IsRestartIdx μ) ∧ μ < xtB1 X ∧
        c' = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧ d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < xtB1 X →
      (∀ c' < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c' g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec X l)) ∧
    (∀ α < upsilon (xtB1 X), ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  gsBlk D.step.toRS _ D.E_lt_B.le D.B_lt_NB S (gw_locD_g D S hγ)

end LocD

/-! ## Every index with gate below `K` -/

section Loc

variable (S : InaccSeq.{0}) {ν : Ordinal.{0}} (hν : ν < evZ (gcG 0)) (hγ : (gwD ν).γ < Td.tdK S)
include hν hγ

/-- **`ε_{G+ν}` IS LOCATED** for every index `ν < ζ_{G+1}` whose system has base gate below `K`. -/
theorem gw_loc : ∃ X : XtSys, XtTopPkg X ∧ xtB1 X = iota S (gcG (veblen 1 (gcG 0 + ν)) * ω) ∧
    upsilon (xtB1 X) = Pv S (gcG (veblen 1 (gcG 0 + ν)) * ω) ∧
    Pv S (gcG (veblen 1 (gcG 0 + ν)) * ω) < Nc.ncL S 0 := by
  rw [← gw_B hν]; exact gw_locD (gwD ν) S hγ

theorem gw_loc_enum {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG (veblen 1 (gcG 0 + ν)) * ω)) :
    CdUpper S l ∧ CdLower S l := by
  rw [← gw_B hν] at hl; exact gw_locD_enum (gwD ν) S hγ hr hl

theorem gw_loc_capV {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG (veblen 1 (gcG 0 + ν)) * ω)) :
    CdCapV S l := by
  rw [← gw_B hν] at hl; exact gw_locD_capV (gwD ν) S hγ hr hl

end Loc

/-! ## The tower `t₀ = 1`, `t_{k+1} = ε_{G+t_k}` -/

/-- **The tower**: `t₀ = 1`, `t_{k+1} = ε_{G+t_k} = φ(1, G + t_k)`. -/
noncomputable def gwT : ℕ → Ordinal.{0}
  | 0 => 1
  | k + 1 => veblen 1 (gcG 0 + gwT k)

theorem gwT_lt : ∀ k : ℕ, gwT k < evZ (gcG 0)
  | 0 => (one_lt_omega0.trans (omega0_lt_inE (evZ_E _)))
  | k + 1 => gw_veb_lt_Z (gwT_lt k)

theorem gwT_pos : ∀ k : ℕ, 0 < gwT k
  | 0 => zero_lt_one
  | k + 1 => InE.pos (omega0_opow_epsilon (gcG 0 + gwT k))

theorem gwT_B (k : ℕ) : (gwD (gwT k)).B = gwT (k + 1) := gw_B (gwT_lt k)

theorem gw_one_eq : gwD 1 = GvD.ofGs gw0.step := by
  have h := gwD_succ 0
  rw [zero_add, gwD_zero] at h
  exact h

/-- **Every `gwD t_k` has base gate below every `ε`-number base.** -/
theorem gwT_gate : ∀ (k : ℕ) (x : Ordinal.{0}), InE x → x < Om1 → (gwD (gwT k)).γ < x
  | 0, x, hx, _ => by
    show (gwD 1).γ < x
    rw [gw_one_eq]
    show gw0.step.γ < x
    rw [GvD.step_γ, gw0_γ]; exact hx.pos
  | k + 1, x, hx, hx1 => by
    set a := gwT k with ha
    have haZ : a < evZ (gcG 0) := gwT_lt k
    have hμ : gwT (k + 1) = (gwD a).B := (gwT_B k).symm
    have hμZ : gwT (k + 1) < evZ (gcG 0) := gwT_lt (k + 1)
    have ha1 : a + 1 ≤ gwT (k + 1) := Order.add_one_le_of_lt (by rw [hμ]; exact gw_self haZ)
    have ha1Z : a + 1 < evZ (gcG 0) := (ev_isSuccLimit_of_inE (evZ_E _)).add_one_lt haZ
    have hμB : gwT (k + 1) < (gwD (a + 1)).B := by
      rw [gw_B ha1Z]
      show veblen 1 (gcG 0 + a) < _
      exact (isNormal_veblen 1).strictMono ((add_lt_add_iff_left _).2 (lt_add_one a))
    rw [gw_γ_iff hμZ hx hx1, (gw_ext ha1 hμZ).2 _ hμB, gwD_succ]
    show (gwD a).step.g (gwT (k + 1)) < x
    rw [hμ, GvD.step_g_B]
    exact gwT_gate k x hx hx1

theorem gwT_K (S : InaccSeq.{0}) (k : ℕ) : (gwD (gwT k)).γ < Td.tdK S := by
  have hK1 : Td.tdK S < Om1 := by rw [Br.Om1_eq]; exact Td.tdK_lt_Om1
  exact gwT_gate k _ (Low.opow_eq_self_of_SC Td.tdK_SC) hK1

theorem gwT_iter (n : ℕ) : Ordinal.epsilon^[n] (gcG 0 + 1) ≤ gcG 0 + gwT n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    show veblen 1 _ ≤ gcG 0 + veblen 1 (gcG 0 + gwT n)
    exact ((isNormal_veblen 1).monotone ih).trans le_add_self

/-- **The tower is cofinal in `ζ_{G+1}`.** -/
theorem gwT_sup {t : Ordinal.{0}} (ht : t < evZ (gcG 0)) : ∃ k : ℕ, t < gwT k := by
  obtain ⟨n, hn⟩ := lt_nfp_iff.1 ht
  refine ⟨n + 1, (hn.trans_le (gwT_iter n)).trans ?_⟩
  exact gw_lt_veb (gwT_pos n) (gwT_lt n)

/-! ## The frontier `ι(Γ(ζ_{G+1}))` -/

/-- **The new bound** `ζ_{G+1}`, the least fixed point of `ε` above `G = Γ_{Ω₁+1}`. -/
noncomputable def gwZ : Ordinal.{0} := evZ (gcG 0)

theorem gwZ_lim : IsSuccLimit gwZ := ev_isSuccLimit_of_inE (evZ_E _)

theorem gwZ_codes {c : Ordinal.{0}} (hc : c < gwZ) : ∃ k : ℕ, c < (gwD (gwT k)).B := by
  obtain ⟨k, hk⟩ := gwT_sup hc
  exact ⟨k, hk.trans (gw_self (gwT_lt k))⟩

/-- **`ι(Γ(ζ_{G+1})) = sup_k ι(Γ(t_{k+1})·ω)`**, below each the code `t_{k+1} = ε_{G+t_k}` is located. -/
theorem gwZ_cof (S : InaccSeq.{0}) {l : Ordinal.{0}} (hl : l < iota S (gcG gwZ)) :
    ∃ k : ℕ, l < iota S (gcG (gwD (gwT k)).B * ω) := by
  have hlim : IsSuccLimit (gcG gwZ) := ev_isSuccLimit_of_inE (Low.opow_eq_self_of_SC (gcG_SC _))
  rw [iota_limit hlim] at hl
  haveI : Nonempty (Iio (gcG gwZ)) := ⟨⟨0, hlim.bot_lt⟩⟩
  obtain ⟨e, he⟩ := (lt_ciSup_iff (iota_bdd _)).1 hl
  obtain ⟨β, hβ, heβ⟩ := gcG_lt_of_lt_limit gwZ_lim e.2
  obtain ⟨k, hk⟩ := gwZ_codes hβ
  refine ⟨k, he.trans_le (iota_mono _ _ ((heβ.trans (gcG_lt hk)).trans_le ?_).le)⟩
  exact le_mul_of_one_le_right' one_lt_omega0.le

/-- **ENUM-REACH at every range restart below `ι(Γ(ζ_{G+1}))`, fixed points included** (UNCONDITIONAL). -/
theorem gwZ_enum (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG gwZ)) :
    CdUpper S l ∧ CdLower S l := by
  obtain ⟨k, h⟩ := gwZ_cof S hl
  exact gw_locD_enum (gwD (gwT k)) S (gwT_K S k) hr h

/-- **CapV at every range restart below `ι(Γ(ζ_{G+1}))`** (UNCONDITIONAL). -/
theorem gwZ_capV (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG gwZ)) :
    CdCapV S l := by
  obtain ⟨k, h⟩ := gwZ_cof S hl
  exact gw_locD_capV (gwD (gwT k)) S (gwT_K S k) hr h

/-- **BLK^O and the exact reaches below `P(Γ(t_{k+1})·ω)` for every `k`** (UNCONDITIONAL). -/
theorem gwZ_blk (S : InaccSeq.{0}) (k : ℕ) :
    let D := gwD (gwT k)
    let X := gsX D.step.toRS _ D.E_lt_B.le D.B_lt_NB S (gw_locD_g D S (gwT_K S k))
    xtB1 X = iota S (gcG (gwT (k + 1)) * ω) ∧
    (∀ c' d, c' < d → d < upsilon (xtB1 X) → (le2 c' d ↔ ∃ μ, ∃ j : ℕ, (μ = 0 ∨ IsRestartIdx μ) ∧ μ < xtB1 X ∧
        c' = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧ d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < xtB1 X →
      (∀ c' < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c' g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec X l)) ∧
    (∀ α < upsilon (xtB1 X), ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) := by
  intro D X
  refine ⟨?_, gw_locD_blk D S (gwT_K S k)⟩
  have h := (gsLoc D.step.toRS _ D.E_lt_B.le D.B_lt_NB S (gw_locD_g D S (gwT_K S k))).1
  rw [← gwT_B k]; exact h

/-- **THE ROAD**: UPPER, LOWER, CapV asked only at `λ ≥ ι(Γ(ζ_{G+1}))` (CapV also `υ_λ < L(ω)`), (CL), EQ,
TCrest, (EMB₂) ⟹ `ν_C = L(ω+1)`, `L(ω) ≤ ν_C`, `L(ω) <₂ L(ω+1)`, (P), (Q), the reaches. -/
theorem gwZ_road (S : InaccSeq.{0}) (hU : ∀ l, CdRange S l → iota S (gcG gwZ) ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S (gcG gwZ) ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S (gcG gwZ) ≤ l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  gv_road_of S _ (fun _ hr h => gwZ_enum S hr h) (fun _ hr h => gwZ_capV S hr h) hU hL hV hC hEQ hrest hB2

theorem gwZ_le_G1 : gwZ ≤ gcG 1 := gw_Z_le1

/-- **`Γ(ζ_{G+1}) < Ω₂`.** -/
theorem gwZ_le_Om2 : gcG gwZ < Om (1 + 1) := by
  have hBE : InE Tf.tfBG := Low.opow_eq_self_of_SC Tf.tfBG_SC
  have hO : (Om1 : Ordinal.{0}) < Tf.tfBG := Tf.tfBG_gt
  have h1 : (1 : Ordinal.{0}) < Tf.tfBG := one_lt_omega0.trans (omega0_lt_inE hBE)
  have hG1 : gcG 1 < Tf.tfBG := by
    rw [Tf.tf_gcG, ← Tf.tfBG_fix]
    exact gamma_lt_gamma.2 ((inE_indec hBE).add_lt ((inE_indec hBE).add_lt hO h1) h1)
  have h2 : gcG gwZ < Tf.tfBG := by
    rw [Tf.tf_gcG, ← Tf.tfBG_fix]
    exact gamma_lt_gamma.2 ((inE_indec hBE).add_lt ((inE_indec hBE).add_lt hO h1) (gwZ_le_G1.trans_lt hG1))
  exact h2.trans Tf.tfBG_lt_Om2

/-- **`P(Γ(ζ_{G+1})) < L(0)`.** -/
theorem gwZ_P (S : InaccSeq.{0}) : Pv S (gcG gwZ) < Nc.ncL S 0 := ga_Pv_lt_L0 S gwZ_le_Om2.le

theorem gw_E0_lt_Z : gvE0 < gwZ := by
  have hGE : InE (gcG 0) := Low.opow_eq_self_of_SC (gcG_SC 0)
  have hOG : Om1 < gcG 0 := by rw [Br.Om1_eq]; exact gcG_Om1_lt 0
  have he : Om1 * ε₀ < gcG 0 := InE.mul_lt hGE hOG (gv_eps0_lt_Om1.trans hOG)
  exact gw_veb_lt_Z (he.trans gw_G_lt_Z)

/-- **The order of the frontiers**: `ε_{G+Ω₁·ε₀} < ζ_{G+1}`, `ι(Γ(ε_{G+Ω₁·ε₀})) ≤ ι(Γ(ζ_{G+1}))`,
`ι(Γ(t_{k+1})·ω) ≤ ι(Γ(ζ_{G+1})) ≤ ι(Ω₂)` for every `k`, `P(Γ(ζ_{G+1})) ≤ P(Ω₂) < L(0)`. -/
theorem gwZ_fr_order (S : InaccSeq.{0}) (k : ℕ) :
    gvE0 < gwZ ∧ iota S (gcG gvE0) ≤ iota S (gcG gwZ) ∧
      iota S (gcG (gwT (k + 1)) * ω) ≤ iota S (gcG gwZ) ∧
      iota S (gcG gwZ) ≤ iota S (Om (1 + 1)) ∧ Pv S (gcG gwZ) ≤ Pv S (Om (1 + 1)) ∧
      Pv S (Om (1 + 1)) < Nc.ncL S 0 := by
  have hV : InE (gcG gwZ) := Low.opow_eq_self_of_SC (gcG_SC _)
  have hk : gwT (k + 1) < gwZ := gwT_lt (k + 1)
  exact ⟨gw_E0_lt_Z, iota_mono _ _ (gcG_lt gw_E0_lt_Z).le,
    iota_mono _ _ (InE.mul_lt hV (gcG_lt hk) (omega0_lt_inE hV)).le,
    iota_mono _ _ gwZ_le_Om2.le, Nm.Pv_mono gwZ_le_Om2.le, ga_Pv_lt_L0 S le_rfl⟩

end Googology.Trans.PoR.InaccPsi.R2.Gw
