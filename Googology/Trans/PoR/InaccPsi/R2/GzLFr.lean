import Googology.Trans.PoR.InaccPsi.R2.GzL

/-!
# THE FRONTIER `ι(Γ(ζ_{G+ε₀}))`, AND THE WALL `ε₀` OF THE CONSTANT `ζ`-INDICES

Every stage `λ < ε₀` (`R2.GzL`) has the tower `t_0 = 1`, `t_{k+1} = ε_{ζ_{G+1+λ}+t_k}` (`Gz.gzST`) cofinal in
`ζ_{G+1+λ+1}`, its systems have base gate below every base (`Gz.gzST_gate`), so their bounds are located
(`Gz.gzV_locD`), and so is every `ζ_{G+1+λ}` (`gzLU_loc`, base gate `0`), limit `λ` included.  **The new frontier is
`ι(Γ(ζ_{G+ε₀}))`**, `ζ_{G+ε₀} = φ(2, G + ε₀)` (was `ι(Γ(ζ_{G+ω}))` after `R2.GzN`, `ι(Γ(ζ_{G+2}))` before the round):
ENUM-REACH and CapV at every range restart below it, BLK^O and exact reaches below each located bound, unconditionally.

The wall: no stage can read its `ζ`-index as the constant `ε₀` (`gz_wall_e0`): at the base pair `(ε₀, ε_{ε₀+1})` the
index `Γ_{ρ+1} + ε₀` is not in `Tᵖ[σ]` (else `ε₀ = (Γ_{ρ+1} + ε₀) − Γ_{ρ+1} ∈ Tᵖ[σ] ∩ ρ = σ = ε₀`).

* `gzLU_loc` (**`ζ_{G+1+λ}` IS LOCATED**, every `λ < ε₀`), `gzLD_loc`, `gzZe`, `gzZe_E`, `gzZe_cof`, `gzZe_codes`,
  `gzZe_iota_cof`, `gzZe_enum`, `gzZe_capV`, `gzZe_blk`, `gzZe_road` (**THE ROAD**), `gzZe_lt_G1`, `gzZe_le_Om2`,
  `gzZe_P`, `gzZe_fr_order`, `gz_wall_e0` (**THE WALL `ε₀`**).

No new axiom.  New definition: `gzZe`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gz

open Googology.Trans.PoR.InaccPsi.R2.Gw
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

/-! ## Location -/

/-- **`ζ_{G+1+λ}` IS LOCATED** for every `λ < ε₀`: `Λ⁺ = ι(Γ(ζ_{G+1+λ})·ω)`, `P(Γ(ζ_{G+1+λ})·ω) < L(0)`. -/
theorem gzLU_loc (S : InaccSeq.{0}) {l : Ordinal.{0}} (hl : l < ε₀) :
    ∃ X : XtSys, XtTopPkg X ∧ xtB1 X = iota S (gcG (gzPBl l hl).Q * ω) ∧
      upsilon (xtB1 X) = Pv S (gcG (gzPBl l hl).Q * ω) ∧ Pv S (gcG (gzPBl l hl).Q * ω) < Nc.ncL S 0 := by
  rw [← gzL_B hl (gzLU_start hl)]
  exact gzV_locD (gzLU l) S (by rw [(gzLU_start hl).γ]; exact gv_K_pos S)

/-- **`ε_{ζ_{G+1+λ}+d}` IS LOCATED** whenever its system has base gate below `K`. -/
theorem gzLD_loc (S : InaccSeq.{0}) {l d : Ordinal.{0}} (hl : l < ε₀) (hd : d < evZ (gzPBl l hl).Q)
    (hγ : (gzLD l hl d).γ < Td.tdK S) :
    ∃ X : XtSys, XtTopPkg X ∧ xtB1 X = iota S (gcG (veblen 1 ((gzPBl l hl).Q + d)) * ω) ∧
      upsilon (xtB1 X) = Pv S (gcG (veblen 1 ((gzPBl l hl).Q + d)) * ω) ∧
      Pv S (gcG (veblen 1 ((gzPBl l hl).Q + d)) * ω) < Nc.ncL S 0 := by
  rw [← gzLD_B hl hd]; exact gzV_locD (gzLD l hl d) S hγ

/-! ## The frontier `ι(Γ(ζ_{G+ε₀}))` -/

/-- **`ζ_{G+ε₀} = φ(2, G + ε₀)`.** -/
noncomputable def gzZe : Ordinal.{0} := veblen 2 (gcG 0 + ε₀)

theorem gzZe_E : InE gzZe := gg_veblen_eps two_ne_zero

theorem gzZe_lim : IsSuccLimit gzZe := ev_isSuccLimit_of_inE gzZe_E

theorem gz_eps0_lim : IsSuccLimit (ε₀ : Ordinal.{0}) := ev_isSuccLimit_of_inE (omega0_opow_epsilon 0)

/-- **Every `c < ζ_{G+ε₀}` lies below some `ζ_{G+1+λ+1}`, `λ < ε₀`.** -/
theorem gzZe_cof {c : Ordinal.{0}} (hc : c < gzZe) : ∃ l, ∃ hl : l < ε₀, c < evZ (gzPBl l hl).Q := by
  obtain ⟨t, ht, hct⟩ := ((isNormal_veblen 2).lt_iff_exists_lt (isSuccLimit_add _ gz_eps0_lim)).1 hc
  obtain ⟨d, hd, htd⟩ := (lt_add_iff gz_eps0_lim.bot_lt.ne').1 ht
  refine ⟨d, hd, hct.trans_le ?_⟩
  rw [GzPB.evQ]
  show veblen 2 t ≤ veblen 2 (gcG 0 + 1 + d + 1)
  refine (isNormal_veblen 2).monotone
    (htd.trans ((add_le_add (le_self_add : gcG 0 ≤ gcG 0 + 1) (le_refl d)).trans le_self_add))

/-- **Every `c < ζ_{G+ε₀}` lies below a located bound `ε_{ζ_{G+1+λ}+t_k}`** (gate below every base). -/
theorem gzZe_codes {c : Ordinal.{0}} (hc : c < gzZe) :
    ∃ l, ∃ hl : l < ε₀, ∃ k : ℕ, c < (gzLD l hl (gzST (gzPBl l hl) k)).B := by
  obtain ⟨l, hl, hc'⟩ := gzZe_cof hc
  obtain ⟨k, hk⟩ := gzST_sup (gzPBl l hl) hc'
  exact ⟨l, hl, k, hk.trans (gzS_self (gzLU_start hl) (gzST_lt (gzPBl l hl) k))⟩

theorem gzZe_iota_cof (S : InaccSeq.{0}) {l : Ordinal.{0}} (hl : l < iota S (gcG gzZe)) :
    ∃ m, ∃ hm : m < ε₀, ∃ k : ℕ, l < iota S (gcG (gzLD m hm (gzST (gzPBl m hm) k)).B * ω) := by
  have hlim : IsSuccLimit (gcG gzZe) := ev_isSuccLimit_of_inE (Low.opow_eq_self_of_SC (gcG_SC _))
  rw [iota_limit hlim] at hl
  haveI : Nonempty (Iio (gcG gzZe)) := ⟨⟨0, hlim.bot_lt⟩⟩
  obtain ⟨e, he⟩ := (lt_ciSup_iff (iota_bdd _)).1 hl
  obtain ⟨β, hβ, heβ⟩ := gcG_lt_of_lt_limit gzZe_lim e.2
  obtain ⟨m, hm, k, hk⟩ := gzZe_codes hβ
  refine ⟨m, hm, k, he.trans_le (iota_mono _ _ ((heβ.trans (gcG_lt hk)).trans_le ?_).le)⟩
  exact le_mul_of_one_le_right' one_lt_omega0.le

theorem gzLD_K (S : InaccSeq.{0}) {m : Ordinal.{0}} (hm : m < ε₀) (k : ℕ) :
    (gzLD m hm (gzST (gzPBl m hm) k)).γ < Td.tdK S := gzST_K (gzLU_start hm) S k

/-- **ENUM-REACH at every range restart below `ι(Γ(ζ_{G+ε₀}))`, fixed points included** (UNCONDITIONAL). -/
theorem gzZe_enum (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG gzZe)) :
    CdUpper S l ∧ CdLower S l := by
  obtain ⟨m, hm, k, h⟩ := gzZe_iota_cof S hl
  exact gzV_locD_enum (gzLD m hm (gzST (gzPBl m hm) k)) S (gzLD_K S hm k) hr h

/-- **CapV at every range restart below `ι(Γ(ζ_{G+ε₀}))`** (UNCONDITIONAL). -/
theorem gzZe_capV (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG gzZe)) :
    CdCapV S l := by
  obtain ⟨m, hm, k, h⟩ := gzZe_iota_cof S hl
  exact gzV_locD_capV (gzLD m hm (gzST (gzPBl m hm) k)) S (gzLD_K S hm k) hr h

/-- **BLK^O and the exact reaches below `P(Γ(ε_{ζ_{G+1+λ}+t_k})·ω)` for every `λ < ε₀`, `k`** (UNCONDITIONAL). -/
theorem gzZe_blk (S : InaccSeq.{0}) {m : Ordinal.{0}} (hm : m < ε₀) (k : ℕ) :
    let D := gzLD m hm (gzST (gzPBl m hm) k)
    let X := gsX D.step.toRS _ D.E_lt_B.le D.B_lt_NB S (gzV_locD_g D S (gzLD_K S hm k))
    xtB1 X = iota S (gcG (gzST (gzPBl m hm) (k + 1)) * ω) ∧
    (∀ c' d, c' < d → d < upsilon (xtB1 X) → (le2 c' d ↔ ∃ μ, ∃ j : ℕ, (μ = 0 ∨ IsRestartIdx μ) ∧ μ < xtB1 X ∧
        c' = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧ d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < xtB1 X →
      (∀ c' < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c' g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec X l)) ∧
    (∀ α < upsilon (xtB1 X), ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) := by
  intro D X
  refine ⟨?_, gzV_locD_blk D S (gzLD_K S hm k)⟩
  have h := (gsLoc D.step.toRS _ D.E_lt_B.le D.B_lt_NB S (gzV_locD_g D S (gzLD_K S hm k))).1
  rw [← gzST_B (gzLU_start hm) k]; exact h

/-- **THE ROAD**: UPPER, LOWER, CapV asked only at `λ ≥ ι(Γ(ζ_{G+ε₀}))` (CapV also `υ_λ < L(ω)`), (CL), EQ, TCrest,
(EMB₂) ⟹ `ν_C = L(ω+1)`, `L(ω) ≤ ν_C`, `L(ω) <₂ L(ω+1)`, (P), (Q), the reaches. -/
theorem gzZe_road (S : InaccSeq.{0}) (hU : ∀ l, CdRange S l → iota S (gcG gzZe) ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S (gcG gzZe) ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S (gcG gzZe) ≤ l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  gv_road_of S _ (fun _ hr h => gzZe_enum S hr h) (fun _ hr h => gzZe_capV S hr h) hU hL hV hC hEQ hrest hB2

theorem gzZe_lt_G1 : gzZe < gcG 1 := by
  have hE : InE (gcG 1) := Low.opow_eq_self_of_SC (gcG_SC 1)
  have he : (ε₀ : Ordinal.{0}) < gcG 1 :=
    (go_eps0_le (Low.opow_eq_self_of_SC (gcG_SC 0))).trans_lt (gcG_lt zero_lt_one)
  have h1 : gcG 0 + ε₀ < gcG 1 := (inE_indec hE).add_lt (gcG_lt zero_lt_one) he
  exact (gcG_SC 1).2 2 (gw_two_lt_G.trans (gcG_lt zero_lt_one)) _ h1

/-- **`Γ(ζ_{G+ε₀}) < Ω₂`.** -/
theorem gzZe_le_Om2 : gcG gzZe < Om (1 + 1) := by
  have hBE : InE Tf.tfBG := Low.opow_eq_self_of_SC Tf.tfBG_SC
  have hO : (Om1 : Ordinal.{0}) < Tf.tfBG := Tf.tfBG_gt
  have h1 : (1 : Ordinal.{0}) < Tf.tfBG := one_lt_omega0.trans (omega0_lt_inE hBE)
  have hG1 : gcG 1 < Tf.tfBG := by
    rw [Tf.tf_gcG, ← Tf.tfBG_fix]
    exact gamma_lt_gamma.2 ((inE_indec hBE).add_lt ((inE_indec hBE).add_lt hO h1) h1)
  have h2 : gcG gzZe < Tf.tfBG := by
    rw [Tf.tf_gcG, ← Tf.tfBG_fix]
    exact gamma_lt_gamma.2 ((inE_indec hBE).add_lt ((inE_indec hBE).add_lt hO h1) (gzZe_lt_G1.trans hG1))
  exact h2.trans Tf.tfBG_lt_Om2

/-- **`P(Γ(ζ_{G+ε₀})) < L(0)`.** -/
theorem gzZe_P (S : InaccSeq.{0}) : Pv S (gcG gzZe) < Nc.ncL S 0 := ga_Pv_lt_L0 S gzZe_le_Om2.le

theorem gzZw_lt_Ze : gzZw < gzZe := by
  have h : ω < (ε₀ : Ordinal.{0}) := omega0_lt_epsilon 0
  exact (isNormal_veblen 2).strictMono ((add_lt_add_iff_left _).2 h)

/-- **The order of the frontiers**: `ζ_{G+ω} < ζ_{G+ε₀}`, `ι(Γ(ζ_{G+ω})) ≤ ι(Γ(ζ_{G+1+λ})·ω) ≤ ι(Γ(ζ_{G+ε₀})) ≤ ι(Ω₂)`
for every `λ < ε₀`, `P(Γ(ζ_{G+ε₀})) ≤ P(Ω₂) < L(0)`. -/
theorem gzZe_fr_order (S : InaccSeq.{0}) {l : Ordinal.{0}} (hl : l < ε₀) :
    gzZw < gzZe ∧ iota S (gcG gzZw) ≤ iota S (gcG gzZe) ∧
      iota S (gcG (gzPBl l hl).Q * ω) ≤ iota S (gcG gzZe) ∧
      iota S (gcG gzZe) ≤ iota S (Om (1 + 1)) ∧ Pv S (gcG gzZe) ≤ Pv S (Om (1 + 1)) ∧
      Pv S (Om (1 + 1)) < Nc.ncL S 0 := by
  have hV : InE (gcG gzZe) := Low.opow_eq_self_of_SC (gcG_SC _)
  have hQ : (gzPBl l hl).Q < gzZe := by
    rw [gzPBl_Q]
    show veblen 2 _ < veblen 2 (gcG 0 + ε₀)
    refine (isNormal_veblen 2).strictMono ?_
    rw [add_assoc]
    exact (add_lt_add_iff_left _).2
      ((inE_indec (omega0_opow_epsilon 0)).add_lt (one_lt_omega0.trans (omega0_lt_epsilon 0)) hl)
  exact ⟨gzZw_lt_Ze, iota_mono _ _ (gcG_lt gzZw_lt_Ze).le, iota_mono _ _ (InE.mul_lt hV (gcG_lt hQ)
    (omega0_lt_inE hV)).le, iota_mono _ _ gzZe_le_Om2.le, Nm.Pv_mono gzZe_le_Om2.le, ga_Pv_lt_L0 S le_rfl⟩

/-! ## The wall `ε₀` -/

/-- **THE WALL `ε₀`**: no stage reads its `ζ`-index as the constant `ε₀`: at the base pair `(ε₀, ε_{ε₀+1})`, Lemma
EXACT for `Γ_{ρ+1} + ε₀` would put `ε₀ = (Γ_{ρ+1} + ε₀) − Γ_{ρ+1}` into `Tᵖ[σ] ∩ ρ = σ = ε₀`. -/
theorem gz_wall_e0 (Bp : GzPB) (h : ∀ x, InE x → x < Om1 → Bp.tP x = lgG x + ε₀) : False := by
  have he : InE (ε₀ : Ordinal.{0}) := omega0_opow_epsilon 0
  have he1 : (ε₀ : Ordinal.{0}) < Om1 :=
    (go_eps0_le (eN_E 0)).trans_lt (eN_lt_Om1K (Rj.rj_Om1_inE.pos))
  have hB : Bases ε₀ (eN ε₀) := ⟨he, eN_E _, lt_eN _, eN_lt_Om1K he1⟩
  obtain ⟨t1, -⟩ := Bp.tP_pi _ _ hB
  rw [h _ (eN_E _) (eN_lt_Om1K he1)] at t1
  obtain ⟨g1, -⟩ : lgG (eN ε₀) ∈ TB (eN ε₀) ε₀ ∧ pi ε₀ (eN ε₀) (lgG (eN ε₀)) = lgG ε₀ := Go.goGl.ba_pi _ _ hB
  have hq : lgG (eN ε₀) + ε₀ < Om1 := by
    have hρ := eN_E (ε₀ : Ordinal.{0})
    have hρ1 := eN_lt_Om1K he1
    have hgq := gm1_facts hρ hρ1
    exact (gm1_T hρ hρ1 ((inE_indec hgq.2.2.2).add_lt (mg_lgG_lt_G1 hρ hρ1) ((lt_eN _).trans hgq.2.1))).2
  obtain ⟨d1, -⟩ := TB_sub hB g1 t1 le_self_add hq
  rw [Ordinal.add_sub_cancel] at d1
  exact lt_irrefl _ ((TB_inter_lt hB (lt_eN _)).1 d1)

end Googology.Trans.PoR.InaccPsi.R2.Gz
