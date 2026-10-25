import Googology.Trans.PoR.InaccPsi.R2.HdLvTop

/-!
# HdG: EVERY OFFSET `φ(ω, G+1+λ)`, `λ < φ(ω+1, G+1)`, READ BY A CODE WITH A GATE; THE FRONTIER `ι(Γ(φ(ω+1, G+1))·ω)`

`G = Γ_{Ω₁+1}` with the reading `Γ_{x+1}` is a base of level `ω` (`hdGA`: a fixed point of `φ(ω, ·)`, gate `0`,
outer low field `B_{ω^ω}(x)`, Lemma EXACT for `Γ_{ρ+1}` and `N_ω(Γ_{ρ+1}) = ϑᵖ(Ω₁·(ω+1) + Γ_{ρ+1})`).  The system
`Hc.hcWU` at `φ(ω, G+1)` starts the gated offset recursion over it (`hdGS`).  The recursion `Hd.hdLvU hdGA Hc.hcWU λ`
reaches every offset `λ < N_ω(G) = φ(ω+1, G+1)`, read by a code with its gate (not only the constants `ν < ε₀` of
`Hc.hcWV`), and the union of all offsets (`hdGT`, `Hd.hdLvTU`) is a system with bound `φ(ω+1, G+1)` and base gate
`0`.  So `φ(ω+1, G+1)` is located (`hdGT_loc`: `Λ⁺ = ι(Γ(φ(ω+1, G+1))·ω)`, `P(Γ(φ(ω+1, G+1))·ω) < L(0)`), and
ENUM-REACH, CapV and Theorem BLK^O hold below it, unconditionally (`hdGT_enum`, `hdGT_capV`, `hdGT_blk`, `hdGT_road`).

* `hd_G_fix1`, `hdNG`, `hdNG_eq`, `hdNG_lt1`, `hd_NG_pi` (Lemma EXACT for `N_ω(Γ_{ρ+1})`), `hdGA` (**`G` AS A BASE
  OF LEVEL `ω`**), `hdGS` (**`Hc.hcWU` STARTS THE GATED OFFSET RECURSION**), `hdGU_B`, `hdGU_start`, `hdGT` (**THE
  SYSTEM AT `φ(ω+1, G+1)`**), `hdGT_B`, `hdGT_γ`, `hdGT_R0`, `hdGT_R`, `hdGT_loc`, `hdGT_enum`, `hdGT_capV`,
  `hdGT_blk`, `hdGT_road` (**THE ROAD**), `hdGT_P`, `hdNG_lt_Om2`, `hdGT_fr_order`.

No new axiom.  New definitions: `hdNG`, `hdGA`, `hdGT`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hd

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

/-! ## `N_ω(G) = φ(ω+1, G+1)` -/

theorem hd_om1_lt_E {e : Ordinal.{0}} (he : InE e) : ω + 1 < e :=
  (ev_isSuccLimit_of_inE he).add_one_lt (omega0_lt_inE he)

theorem hd_om1_lt_gam1 : (ω + 1 : Ordinal.{0}) < gamma 1 := (hd_om1_lt_E hc_eps0_E).trans hc_eps0_lt_gam1

/-- **`G` is a fixed point of `φ(ω+1, ·)`.** -/
theorem hd_G_fix1 : veblen (ω + 1) (gcG 0) = gcG 0 :=
  gn_veb_fix (gcG_SC 0) (hd_om1_lt_E (Low.opow_eq_self_of_SC (gcG_SC 0)))

/-- **`N_ω(G) = φ(ω+1, G+1)`.** -/
noncomputable def hdNG : Ordinal.{0} := veblen (ω + 1) (gcG 0 + 1)

theorem hdNG_eq : hcNw (gcG 0) = hdNG := by
  have := hdNw_veb (gcG 0); rwa [hd_G_fix1] at this

/-- **`φ(ω+1, G+1) < Γ_{Ω₁+2}`.** -/
theorem hdNG_lt1 : hdNG < gcG 1 := by
  have hG1 := gcG_SC 1
  have hE := Low.opow_eq_self_of_SC hG1
  have hfix : veblen (ω + 1) (gcG 1) = gcG 1 := gn_veb_fix hG1 (hd_om1_lt_E hE)
  have h := (isNormal_veblen (ω + 1)).strictMono ((ev_isSuccLimit_of_inE hE).add_one_lt (gcG_lt zero_lt_one))
  rw [hfix] at h
  exact h

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem hd_om1_lt_G : ω + 1 < lgG x := hd_om1_lt_E (lgG_facts hx hx1).2.2.2.1

theorem hd_om1_q : ω + 1 < gq 1 x := (hd_om1_lt_G hx hx1).trans (mg_lgG_lt_G1 hx hx1)

theorem hd_G_fix1x : veblen (ω + 1) (lgG x) = lgG x := hc_G_fix hx hx1 le_add_self (hd_om1_lt_G hx hx1)

/-- **`N_ω(Γ_{x+1}) = ϑˣ(Ω₁·(ω+1) + Γ_{x+1})`.** -/
theorem hd_NG_glA : hcNw (lgG x) = glA (ω + 1) (lgG x) x := by
  have e : hcNw (lgG x) = veblen (ω + 1) (lgG x + 1) := by
    have := hdNw_veb (lgG x); rwa [hd_G_fix1x hx hx1] at this
  rw [e, hc_glA_fixG hx hx1 le_add_self (hd_om1_q hx hx1) (hd_G_fix1x hx hx1) (hd_om1_lt_G hx hx1)
    (lgG_facts hx hx1).2.1 (mg_lgG_lt_G1 hx hx1)]

end Base

/-- **Lemma EXACT for `N_ω(Γ_{ρ+1})`.** -/
theorem hd_NG_pi {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) :
    hcNw (lgG ρ) ∈ TB ρ σ ∧ pi σ ρ (hcNw (lgG ρ)) = hcNw (lgG σ) := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  have hkσ : ω + 1 < σ := hd_om1_lt_E hB.1
  obtain ⟨g1, g2⟩ : lgG ρ ∈ TB ρ σ ∧ pi σ ρ (lgG ρ) = lgG σ := Go.goGl.ba_pi σ ρ hB
  have h := glA_pi hB (mem_TB_of_lt hB hkσ) (gm1_T hB.2.1 hρ1 (hd_om1_q hB.2.1 hρ1)).2 g1
    (lgG_facts hB.2.1 hρ1).2.2.1
  rw [pi_lt hB hkσ, g2, ← hd_NG_glA hB.2.1 hρ1, ← hd_NG_glA hB.1 hσ1] at h
  exact h

/-! ## `G` as a base of level `ω` -/

/-- **`G` AS A BASE OF LEVEL `ω`**: reading `Γ_{x+1}`, gate `0`, outer low field `B_{ω^ω}(x)`. -/
noncomputable def hdGA : HdA where
  F := gcG 0
  Fr := lgG
  γ := 0
  Zo := hcBW
  γ_lt := Ordinal.omega_pos 1
  F_fix := hcW_G_fixW
  G_le := le_rfl
  N_lt1 := by rw [hdNG_eq]; exact hdNG_lt1
  F_mem := fun S _ _ ha _ => gmS_G0_mem S ha
  N_mem := fun S _ _ ha _ => by
    rw [hdNG_eq]
    exact CSet.phi_mem (gr_cst_mem ha _ (ω + 1) hd_om1_lt_gam1) (CSet.succ_mem (gmS_G0_mem S ha))
  F_code := fun _ _ _ _ _ _ _ => GxCl.atom (Set.mem_singleton _)
  F_cl := fun _ hZ _ _ _ _ _ => hZ.1
  N_cl := fun _ hZ _ _ => hZ.1
  Fr_gt := fun hx hx1 _ => (lgG_facts hx hx1).2.1
  Fr_fix := fun hx hx1 _ => hc_G_fixW hx hx1
  N_Zo := fun hx hx1 _ => hc_B1_lt_BW hx hx1
  Zo_fix := fun _ => veblen_veblen_of_lt ((natCast_lt_omega0 2).trans hc_om_lt_ww) _
  Zo_BR := fun _ hx hx1 => (hc_BW_lt_BR hx hx1).le
  Fr_pi := fun {σ ρ} hB _ => Go.goGl.ba_pi σ ρ hB
  N_pi := fun hB _ => hd_NG_pi hB

theorem hdGA_F : hdGA.F = gcG 0 := rfl

theorem hdGA_γ : hdGA.γ = 0 := rfl

theorem hdGA_N : hcNw hdGA.F = hdNG := hdNG_eq

/-- **`Hc.hcWU` (the system at `φ(ω, G+1)`) STARTS THE GATED OFFSET RECURSION OVER `G`.** -/
theorem hdGS : HdLvStart hdGA hcWU where
  B := by rw [add_zero]; exact hcWU_B
  Zb := fun x hx hx1 => by
    show evZ (hbBw x) ≤ hdGA.Zl x
    rw [hdGA.Zl_eq hx.pos, ← hcS_Bw]
    exact (hb_evZ_lt_fix2 (hdNw_fix2 _) (hdS_lt_Nw (hcNw_gt _))).le
  st := fun h2 hZ => {
    ix := by show hbTw = veblen ω (gcG 0 + 1 + 0); rw [add_zero, hbTw_eq]
    γ := fun x hx _ => by
      show (0 : Ordinal.{0}) < x ↔ max 0 (hcWU.g 0) < x
      rw [hcWU.g_zero, max_self]
    b := fun x hx hx1 _ => by
      show hbBw x = glA ω (lgG x + hcWU.R 0 x) x
      rw [hcWU.R_zero, add_zero, (hc_glA_GW hx hx1).1]
    Z := fun x hx hx1 => by
      unfold HcPB.Zst
      show evZ (hbBw x) = if max 0 (hcWU.g 0) < x then evZ (glA ω (lgG x + hcWU.R 0 x) x) else hdGA.Zl x
      rw [hcWU.g_zero, max_self, if_pos hx.pos, hcWU.R_zero, add_zero, (hc_glA_GW hx hx1).1] }
  high0 := fun _ _ _ _ hσ _ _ => hσ.pos

/-- **The start at every offset `λ < φ(ω+1, G+1)` has bound `φ(ω, G+1+λ)`.** -/
theorem hdGU_B {l : Ordinal.{0}} (hl : l < hdNG) : (hdLvU hdGA hcWU l).B = veblen ω (gcG 0 + 1 + l) :=
  hdLvU_B hdGS (by rw [hdGA_N]; exact hl)

/-- **The start at every offset `λ` starts the stage at the gated offset `λ`** (reading
`ϑˣ(Ω₁·ω + Γ_{x+1} + λ(x))`, gate `g(λ)`). -/
theorem hdGU_start {l : Ordinal.{0}} (hl : l < hcNw hdGA.F) :
    HcSStart (hdLvPB hdGA (hdLvU hdGA hcWU l) l (hdLvU_self hdGS hl) hl (hdLvU_Zb hdGS hl))
      (hdLvU hdGA hcWU l) := hdLvU_start hdGS hl

/-- **THE SYSTEM AT `φ(ω+1, G+1)`**: the union of all gated offsets over `G`. -/
noncomputable def hdGT : HcVD := hdLvTU hdGS

theorem hdGT_B : hdGT.B = hdNG := hdNG_eq

theorem hdGT_γ : hdGT.γ = 0 := rfl

/-- **`hdGT` extends `Hc.hcWU`.** -/
theorem hdGT_R0 {c : Ordinal.{0}} (hc : c < hcWU.B) (x : Ordinal.{0}) : hdGT.R c x = hcWU.R c x :=
  hdLvTU_R0 hdGS hc x

/-- **`hdGT` extends every start of the recursion.** -/
theorem hdGT_R {l c : Ordinal.{0}} (hl : l < hcNw hdGA.F) (hc : c < (hdLvU hdGA hcWU l).B) (x : Ordinal.{0}) :
    hdGT.R c x = (hdLvU hdGA hcWU l).R c x := hdLvTU_R hdGS hl hc x

/-! ## The frontier `ι(Γ(φ(ω+1, G+1))·ω)` -/

/-- **`φ(ω+1, G+1)` IS LOCATED**: `Λ⁺ = ι(Γ(φ(ω+1, G+1))·ω)`, `P(Γ(φ(ω+1, G+1))·ω) < L(0)`. -/
theorem hdGT_loc (S : InaccSeq.{0}) :
    ∃ X : XtSys, XtTopPkg X ∧ xtB1 X = iota S (gcG hdNG * ω) ∧
      upsilon (xtB1 X) = Pv S (gcG hdNG * ω) ∧ Pv S (gcG hdNG * ω) < Nc.ncL S 0 := by
  rw [← hdGT_B]; exact hcV_locD hdGT S (by rw [hdGT_γ]; exact Td.tdK_SC.1)

/-- **ENUM-REACH at every range restart below `ι(Γ(φ(ω+1, G+1))·ω)`, fixed points included** (UNCONDITIONAL). -/
theorem hdGT_enum (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG hdNG * ω)) :
    CdUpper S l ∧ CdLower S l := by
  rw [← hdGT_B] at hl
  exact hcV_locD_enum hdGT S (by rw [hdGT_γ]; exact Td.tdK_SC.1) hr hl

/-- **CapV at every range restart below `ι(Γ(φ(ω+1, G+1))·ω)`** (UNCONDITIONAL). -/
theorem hdGT_capV (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG hdNG * ω)) :
    CdCapV S l := by
  rw [← hdGT_B] at hl
  exact hcV_locD_capV hdGT S (by rw [hdGT_γ]; exact Td.tdK_SC.1) hr hl

/-- **Theorem BLK^O below `P(Γ(φ(ω+1, G+1))·ω)`, with the exact reaches** (UNCONDITIONAL). -/
theorem hdGT_blk (S : InaccSeq.{0}) :
    let X := gsX hdGT.step.toRS _ hdGT.E_lt_B.le hdGT.B_lt_NB S (hcV_locD_g hdGT S (by rw [hdGT_γ]; exact
      Td.tdK_SC.1))
    (∀ c' d, c' < d → d < upsilon (xtB1 X) → (le2 c' d ↔ ∃ μ, ∃ j : ℕ, (μ = 0 ∨ IsRestartIdx μ) ∧ μ < xtB1 X ∧
        c' = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧ d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < xtB1 X →
      (∀ c' < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c' g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec X l)) ∧
    (∀ α < upsilon (xtB1 X), ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  hcV_locD_blk hdGT S (by rw [hdGT_γ]; exact Td.tdK_SC.1)

/-- **THE ROAD**: UPPER, LOWER, CapV asked only at `λ ≥ ι(Γ(φ(ω+1, G+1))·ω)` (CapV also `υ_λ < L(ω)`), (CL), EQ,
TCrest, (EMB₂) ⟹ `ν_C = L(ω+1)`, `L(ω) ≤ ν_C`, `L(ω) <₂ L(ω+1)`, (P), (Q), the reaches. -/
theorem hdGT_road (S : InaccSeq.{0}) (hU : ∀ l, CdRange S l → iota S (gcG hdNG * ω) ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S (gcG hdNG * ω) ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S (gcG hdNG * ω) ≤ l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  gv_road_of S _ (fun _ hr h => hdGT_enum S hr h) (fun _ hr h => hdGT_capV S hr h) hU hL hV hC hEQ hrest hB2

/-- **`P(Γ(φ(ω+1, G+1))·ω) < L(0)`.** -/
theorem hdGT_P (S : InaccSeq.{0}) : Pv S (gcG hdNG * ω) < Nc.ncL S 0 := by
  obtain ⟨-, -, -, -, h⟩ := hdGT_loc S; exact h

/-- **`Γ(φ(ω+1, G+1))·ω < Ω₂`.** -/
theorem hdNG_lt_Om2 : gcG hdNG * ω < Om (1 + 1) := by
  have hBE : InE Tf.tfBG := Low.opow_eq_self_of_SC Tf.tfBG_SC
  have hO : (Om1 : Ordinal.{0}) < Tf.tfBG := Tf.tfBG_gt
  have h1 : (1 : Ordinal.{0}) < Tf.tfBG := one_lt_omega0.trans (omega0_lt_inE hBE)
  have hG1 : gcG 1 < Tf.tfBG := by
    rw [Tf.tf_gcG, ← Tf.tfBG_fix]
    exact gamma_lt_gamma.2 ((inE_indec hBE).add_lt ((inE_indec hBE).add_lt hO h1) h1)
  have h2 : gcG hdNG < Tf.tfBG := by
    rw [Tf.tf_gcG, ← Tf.tfBG_fix]
    exact gamma_lt_gamma.2 ((inE_indec hBE).add_lt ((inE_indec hBE).add_lt hO h1) (hdNG_lt1.trans hG1))
  exact (InE.mul_lt hBE h2 (omega0_lt_inE hBE)).trans Tf.tfBG_lt_Om2

/-- `φ(ω, G+ε₀) < φ(ω+1, G+1)`. -/
theorem hd_WE_lt_NG : hcWF ε₀ < hdNG := by
  rw [← hdNG_eq]
  have hNE := hcNw_E (gcG 0)
  have hε : (ε₀ : Ordinal.{0}) < hcNw (gcG 0) := (gc_eps0_le_Om1.trans_lt (gcG_Om1_lt 0)).trans (hcNw_gt _)
  have h1 : gcG 0 + 1 + ε₀ < hcNw (gcG 0) := (inE_indec hNE).add_lt ((hcNw_lim _).add_one_lt (hcNw_gt _)) hε
  have := (isNormal_veblen ω).strictMono h1
  rwa [hcNw_fix] at this

/-- **The order of the frontiers**: `ι(Γ(φ(ω, G+ε₀))) ≤ ι(Γ(φ(ω+1, G+1))) ≤ ι(Γ(φ(ω+1, G+1))·ω) ≤ ι(Ω₂)`, and
`P(Γ(φ(ω+1, G+1))·ω) ≤ P(Ω₂) < L(0)`. -/
theorem hdGT_fr_order (S : InaccSeq.{0}) :
    iota S (gcG (hcWF ε₀)) ≤ iota S (gcG hdNG) ∧ iota S (gcG hdNG) ≤ iota S (gcG hdNG * ω) ∧
      iota S (gcG hdNG * ω) ≤ iota S (Om (1 + 1)) ∧ Pv S (gcG hdNG * ω) ≤ Pv S (Om (1 + 1)) ∧
      Pv S (Om (1 + 1)) < Nc.ncL S 0 :=
  ⟨iota_mono _ _ (gcG_le hd_WE_lt_NG.le), iota_mono _ _ (le_mul_of_one_le_right' one_lt_omega0.le),
    iota_mono _ _ hdNG_lt_Om2.le, Nm.Pv_mono hdNG_lt_Om2.le, ga_Pv_lt_L0 S le_rfl⟩

end Googology.Trans.PoR.InaccPsi.R2.Hd
