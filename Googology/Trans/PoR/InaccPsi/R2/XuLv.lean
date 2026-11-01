import Googology.Trans.PoR.InaccPsi.R2.XuW
import Googology.Trans.PoR.InaccPsi.R2.XpLv

/-!
# XuLv: THE (A3) BANDS BELOW A BOUND `T` ALONG THE INTERFACE `Xu.xuC T`: DATA, TRANSFERS, THE FIRST TWO STEPS (port of `R2.XpLv`)

The (A3) band levels are the codes `G < ℓ < t₀` with `Ω₁ ∣ ℓ` (`XuqLv`).  The band datum at `ℓ` is the package of the
(A3) family `Xc.xcFam` (`xuqPk`, datum `Xc.xcA3.lv ℓ`), `xuqBdOf`.

* `xp_nsc_of` (a reading strictly between `y` and `ε_{y+1}` is not strongly critical), `xp_eN_nsc` (**`ε_{y+1}` is not
  strongly critical**), `xuqBdOf` (**THE BAND DATUM AT EVERY (A3) LEVEL**);
* `xuq_at_succ_lv` (**the bottom of the band `ℓ' + Ω₁` as a band of `ℓ'` is the bottom of the datum `ℓ' + Ω₁`**),
  `xuq_at_G1` (`Xl.xlW` at the bottom of `G + Ω₁`), `xuq_xg_G1` (`xuGg(G + Ω₁) = 1`);
* `XuqExt`, `XuqSm` (SMALL in level form), `XuqOk`, `XuqCoh`, `XuqStepAt`;
* `xuqStep_G1`, `xuqStep_succ` (**THE STEP AT `G + Ω₁` AND AT EVERY SUCCESSOR BAND `ℓ' + Ω₁`**).

No new axiom.  New definitions: `XuqLv`, `xuqPk`, `xuqBdOf`, `XuqExt`, `XuqSm`, `XuqOk`, `XuqCoh`, `XuqStepAt`.
-/

set_option autoImplicit false


open Googology.Trans.PoR.InaccPsi.R2.Wm Googology.Trans.PoR.InaccPsi.R2.Wh Googology.Trans.PoR.InaccPsi.R2.Ho
open Googology.Trans.PoR.InaccPsi.R2.Hn Googology.Trans.PoR.InaccPsi.R2.Hl
open Googology.Trans.PoR.InaccPsi.R2.Hj Googology.Trans.PoR.InaccPsi.R2.Hk
open Googology.Trans.PoR.InaccPsi.R2.Hi Googology.Trans.PoR.InaccPsi.R2.Hg
open Googology.Trans.PoR.InaccPsi.R2.Hf Googology.Trans.PoR.InaccPsi.R2.Hd Googology.Trans.PoR.InaccPsi.R2.He
open Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Hb
open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn Googology.Trans.PoR.InaccPsi.R2.Gf
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd
open Googology.Trans.PoR.InaccPsi.R2.Wo Googology.Trans.PoR.InaccPsi.R2.Wn Googology.Trans.PoR.InaccPsi.R2.Wp
  Googology.Trans.PoR.InaccPsi.R2.Ws Googology.Trans.PoR.InaccPsi.R2.Wt Googology.Trans.PoR.InaccPsi.R2.Wy
  Googology.Trans.PoR.InaccPsi.R2.Wx


open Googology.Trans.PoR.InaccPsi.R2.Xc
open Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Bt

open Googology.Trans.PoR.InaccPsi.R2.Xf
open Googology.Trans.PoR.InaccPsi.R2.Gk

open Googology.Trans.PoR.InaccPsi.R2.Ho

open Googology.Trans.PoR.InaccPsi.R2.Xl
open Googology.Trans.PoR.InaccPsi.R2.Xp

namespace Googology.Trans.PoR.InaccPsi.R2.Xu

/-! ## The bands below `T` and their data -/

/-- **The interface below the bound `T`.** -/
noncomputable abbrev xuCT {T : Ordinal.{0}} (hT : XuT T) : WsC := xuC T hT.E hT.t0_le hT.lt1

/-- **THE (A3) BAND LEVELS BELOW `T`**: `G < ℓ < T`, `Ω₁ ∣ ℓ`. -/
def XuqLv (T ℓ : Ordinal.{0}) : Prop := gcG 0 < ℓ ∧ Om1 ∣ ℓ ∧ ℓ < T

/-- **The reading of a code `G < ℓ < Γ(1)` is not strongly critical.** -/
theorem xu_R_nsc {ℓ x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hG : gcG 0 < ℓ) (hℓ : ℓ < gcG 1)
    (hg : xuG ℓ < x) : xuR ℓ x < veblen (xuR ℓ x) 0 := by
  rcases lt_or_ge ℓ (Wj.wjT 0) with ht | ht
  · rw [xuG_low ht] at hg
    rw [xuR_low ht]
    exact xp_nsc_of (wt_R_gtG hG ht hx hx1 hg) (goGl.hR_lt_eNb hx hx1 (wt_LB ht) hg)
  rcases (left_le_veblen (xuR ℓ x) 0).lt_or_eq with h | h
  · exact h
  exfalso
  have hSC : SC (xuR ℓ x) :=
    gl_SC_of_fix h.symm (xuR_pos hx hx1 (ne_of_gt (xu_t0_E.pos.trans_le ht)) hℓ hg)
  have hrE : InE (xuR ℓ x) := Low.opow_eq_self_of_SC hSC
  by_cases hℓE : InE ℓ
  · obtain ⟨r, -, -, -, -, -, hkR, hkT, hk1x, hηT, hη1, -, -, hK, -⟩ := xu_eps_read hx hx1 hℓE ht hℓ hg
    have hP : LuP (xuR (xuK ℓ) x + 1) (xuR ℓ x) :=
      luP_mono le_add_self (add_one_le_of_lt hK) ⟨0, h.symm⟩
    rw [r] at hP
    exact glA_notP hx hx1 hkR hkT hk1x hηT hη1 hP
  · have hEl := gl_E_lt_self (xu_gfE_le ht) hℓE
    have hte := xu_E_ge ht
    have hgE := xu_E_g ht hℓ hg
    have h1 : xuR (guE ℓ) x < xuR ℓ x := xuR_mono hx hx1 hℓ hEl hg hgE
    have h2 : xuR ℓ x < eN (xuR (guE ℓ) x) := xuR_top hx hx1 hℓ ht hg
    exact absurd (eN_le h1 hrE) (not_le.2 h2)

section Data

variable {T : Ordinal.{0}} (hT : XuT T)

theorem xuqLv_lev {ℓ : Ordinal.{0}} (h : XuqLv T ℓ) : (xuCT hT).Lev ℓ :=
  ⟨(gl_Om1_lt_G0.trans h.1).le, h.2.1, h.2.2⟩

/-- **The package of the family below `T` at the level `ℓ`.** -/
noncomputable def xuqPk (ℓ : Ordinal.{0}) (h : (xuCT hT).Lev ℓ) : HnPk := xuPk hT.E hT.t0_le hT.lt1 ℓ h

theorem xuqPk_Λ (ℓ : Ordinal.{0}) (h : (xuCT hT).Lev ℓ) : (xuqPk hT ℓ h).Λ = (xuCT hT).lv ℓ h := rfl

theorem xuq_lvl {ℓ x : Ordinal.{0}} (h : (xuCT hT).Lev ℓ) (hx : InE x) (hx1 : x < Om1) (hg : xuGg ℓ < x) :
    ((xuCT hT).lv ℓ h).l x = xuR ℓ x := (xuCT hT).lv_l h hx hx1 hg

/-- **THE BAND DATUM AT EVERY BAND LEVEL `ℓ` BELOW `T`.** -/
noncomputable def xuqBdOf (ℓ : Ordinal.{0}) (h : XuqLv T ℓ) : XuqBd T where
  K := xuqPk hT ℓ (xuqLv_lev hT h)
  hT := hT
  G_lt := h.1
  l_nsc := fun x hx hx1 hg => by
    show ((xuCT hT).lv ℓ (xuqLv_lev hT h)).l x < veblen (((xuCT hT).lv ℓ (xuqLv_lev hT h)).l x) 0
    rw [xuq_lvl hT (xuqLv_lev hT h) hx hx1 hg]
    exact xu_R_nsc hx hx1 h.1 (h.2.2.trans hT.lt1) ((xuGg_lt_iff hx).1 hg)
  l_lt := fun x hx hx1 hg => by
    show ((xuCT hT).lv ℓ (xuqLv_lev hT h)).l x < _
    rw [xuq_lvl hT (xuqLv_lev hT h) hx hx1 hg, xuqA_eq hT hx hx1]
    exact xuR_mono hx hx1 hT.lt1 h.2.2 (xuq_g_lt hT hx hx1) ((xuGg_lt_iff hx).1 hg)

theorem xuqBdOf_Λ (ℓ : Ordinal.{0}) (h : XuqLv T ℓ) : (xuqBdOf hT ℓ h).K.Λ = (xuCT hT).lv ℓ (xuqLv_lev hT h) := rfl

end Data

section Rest

variable {T : Ordinal.{0}} (hT : XuT T)

/-! ## Transfers -/

/-- **THE BOTTOM OF THE BAND `ℓ' + Ω₁` OVER THE DATUM `ℓ'` IS THE BOTTOM OVER THE DATUM `ℓ' + Ω₁`.** -/
theorem xuq_at_succ_lv {ℓ' : Ordinal.{0}} (h' : (xuCT hT).Lev ℓ') (h : (xuCT hT).Lev (ℓ' + Om1)) {U : HgVD}
    (hU : XuqAt T ((xuCT hT).lv ℓ' h').succ 0 U) : XuqAt T ((xuCT hT).lv (ℓ' + Om1) h) 0 U := by
  refine xuqAt_congr hU rfl (fun x hx _ => ⟨fun hg => (xuCT hT).succ_g_lt hx h'.2.2 h'.2.1 hg,
    fun hg => ((xuCT hT).succ_g ℓ' h'.2.2 h'.2.1).trans_lt hg⟩) ((xuCT hT).succ_g ℓ' h'.2.2 h'.2.1) (fun x hx hx1 hg => ?_)
  have hg' : (xuCT hT).g ℓ' < x := ((xuCT hT).succ_g ℓ' h'.2.2 h'.2.1).trans_lt hg
  show (xuCT hT).rd (ℓ' + Om1) x = (xuCT hT).rd ℓ' x + x
  rw [(xuCT hT).rd_eq hx hx1 h.1 h.2.2 hg, (xuCT hT).rd_eq hx hx1 h'.1 h'.2.2 hg', (xuCT hT).succ_R ℓ' h'.2.2 h'.2.1 x]

include hT in
theorem xuq_lev_G1 : XuqLv T (gcG 0 + Om1) :=
  ⟨lt_add_of_pos_right _ gv_Om1_pos, dvd_add wt_Om1_dvd_G (dvd_refl _), wt_GO_lt.trans_le hT.t0_le⟩

/-- **`xuGg(G + Ω₁) = 1`.** -/
theorem xuq_xg_G1 : xuGg (gcG 0 + Om1) = 1 := by rw [xuGg_low wt_GO_lt]; exact xp_xg_G1

/-- **`Xl.xlW` IS A SYSTEM AT THE BOTTOM OF THE DATUM `G + Ω₁`** below `T`. -/
theorem xuq_at_G1 (h : (xuCT hT).Lev (gcG 0 + Om1)) : XuqAt T ((xuCT hT).lv (gcG 0 + Om1) h) 0 xlW := by
  refine xuqAt_congr (xuq_at_xlW hT) rfl (fun x hx _ => ?_) ?_ (fun x hx hx1 hg => ?_)
  · show xfLv.g < x ↔ xuGg (gcG 0 + Om1) < x
    rw [xfLv_g, xuq_xg_G1]
  · show xfLv.g ≤ xuGg (gcG 0 + Om1)
    rw [xfLv_g, xuq_xg_G1]
  · have hg' : xuGg (gcG 0 + Om1) < x := hg
    show (xuCT hT).rd (gcG 0 + Om1) x = xfLv.l x + x
    rw [(xuCT hT).rd_eq hx hx1 h.1 h.2.2 hg', xf_l hx hx1]
    show xuR (gcG 0 + Om1) x = lgG x + x
    rw [(xu_add_Om1 (gcG 0) xu_G0_lt_G1 wt_Om1_dvd_G).1 x, xuR_G]

/-- Every (A3) band level is at least `G + Ω₁`. -/
theorem xuq_G1_le {ℓ : Ordinal.{0}} (h : XuqLv T ℓ) : gcG 0 + Om1 ≤ ℓ := wt_dvd_step wt_Om1_dvd_G h.2.1 h.1

/-! ## The invariant -/

/-- **`V` extends `U`.** -/
def XuqExt (U V : HgVD) : Prop := ∀ c x, c < U.B → V.R c x = U.R c x ∧ V.g c = U.g c

theorem XuqExt.refl (U : HgVD) : XuqExt U U := fun _ _ _ => ⟨rfl, rfl⟩

theorem XuqExt.trans {U V W : HgVD} (h1 : XuqExt U V) (h2 : XuqExt V W) (hB : U.B ≤ V.B) : XuqExt U W :=
  fun c x hc => by
    obtain ⟨a1, b1⟩ := h1 c x hc
    obtain ⟨a2, b2⟩ := h2 c x (hc.trans_le hB)
    exact ⟨a2.trans a1, b2.trans b1⟩

/-- **SMALL IN LEVEL FORM**: a code of `V` with gate below an `ε`-number `σ` lies below `φ(b, 0)` for some `b ≤ ℓ`
with `xuGg b < σ`. -/
def XuqSm (ℓ : Ordinal.{0}) (V : HgVD) : Prop :=
  ∀ c σ, c < V.B → InE σ → σ < Om1 → V.g c < σ → ∃ b, b ≤ ℓ ∧ xuGg b < σ ∧ c < veblen b 0

/-- **THE INVARIANT AT THE LEVEL `ℓ`**: `V` is a system at the bottom `φ(ℓ, 0)` of the datum `ℓ`, SMALL, and it
extends `Xl.xlW` (hence `Hg.hgU`). -/
structure XuqOk (ℓ : Ordinal.{0}) (V : HgVD) : Prop where
  at_ : ∀ h : (xuCT hT).Lev ℓ, XuqAt T ((xuCT hT).lv ℓ h) 0 V
  sm : XuqSm ℓ V
  w : XuqExt xlW V

/-- **A COHERENT FAMILY BELOW `ℓ`.** -/
def XuqCoh (ℓ : Ordinal.{0}) (f : ∀ ℓ' : Ordinal.{0}, ℓ' < ℓ → HgVD) : Prop :=
  (∀ ℓ' (h : ℓ' < ℓ), XuqLv T ℓ' → XuqOk hT ℓ' (f ℓ' h)) ∧
    ∀ ℓ'' ℓ' (h'' : ℓ'' < ℓ) (h' : ℓ' < ℓ), ℓ'' < ℓ' → XuqLv T ℓ'' → XuqLv T ℓ' → XuqExt (f ℓ'' h'') (f ℓ' h')

/-- **THE STEP AT `ℓ`**: every coherent family below `ℓ` has a system at `ℓ` extending all of it. -/
def XuqStepAt (ℓ : Ordinal.{0}) : Prop :=
  ∀ f, XuqCoh hT ℓ f → ∃ V, XuqOk hT ℓ V ∧ ∀ ℓ' (h : ℓ' < ℓ), XuqLv T ℓ' → XuqExt (f ℓ' h) V

theorem xuqOk_B {ℓ : Ordinal.{0}} (h : XuqLv T ℓ) {V : HgVD} (hV : XuqOk hT ℓ V) : V.B = veblen ℓ 0 := by
  rw [(hV.at_ (xuqLv_lev hT h)).B, add_zero]; rfl

theorem xuqOk_γ {ℓ : Ordinal.{0}} (h : XuqLv T ℓ) {V : HgVD} (hV : XuqOk hT ℓ V) : V.γ ≤ xuGg ℓ := by
  have := (hV.at_ (xuqLv_lev hT h)).γ_le
  rwa [max_eq_right zero_le] at this

/-- Coherence including equality. -/
theorem XuqCoh.ext_le {T : Ordinal.{0}} {hT : XuT T} {ℓ : Ordinal.{0}} {f : ∀ ℓ' : Ordinal.{0}, ℓ' < ℓ → HgVD} (H : XuqCoh hT ℓ f) {ℓ'' ℓ' : Ordinal.{0}}
    (h'' : ℓ'' < ℓ) (h' : ℓ' < ℓ) (hle : ℓ'' ≤ ℓ') (hl'' : XuqLv T ℓ'') (hl' : XuqLv T ℓ') :
    XuqExt (f ℓ'' h'') (f ℓ' h') := by
  rcases hle.lt_or_eq with hlt | rfl
  · exact H.2 ℓ'' ℓ' h'' h' hlt hl'' hl'
  · exact XuqExt.refl _

/-! ## The step at `G + Ω₁` -/

theorem xuq_xgG1_lt {σ : Ordinal.{0}} (hσ : InE σ) : xuGg (gcG 0 + Om1) < σ := by
  rw [xuq_xg_G1]; exact wo_one_lt_inE hσ

/-- **THE STEP AT `G + Ω₁`**: `Xl.xlW`. -/
theorem xuqStep_G1 : XuqStepAt hT (gcG 0 + Om1) := by
  intro f _
  refine ⟨xlW, ⟨fun h => xuq_at_G1 hT h, fun c σ hc hσ _ _ => ⟨gcG 0 + Om1, le_rfl, xuq_xgG1_lt hσ, hc⟩,
    XuqExt.refl _⟩,
    fun ℓ' h hl => absurd (xuq_G1_le hl) (not_le.2 h)⟩

/-! ## The step at a successor band -/

section Succ

variable {ℓ' : Ordinal.{0}} (hl' : XuqLv T ℓ') (hS : ℓ' + Om1 < T)

include hl' hS in
theorem xuq_lev_succ : XuqLv T (ℓ' + Om1) :=
  ⟨hl'.1.trans_le le_self_add, dvd_add hl'.2.1 (dvd_refl _), hS⟩

/-- **THE `Ω₁`-UNION OF THE BAND `ℓ'` IS A SYSTEM AT THE BOTTOM OF THE DATUM `ℓ' + Ω₁`.** -/
theorem xuq_at_W {U : HgVD} (hU : XuqAt T (xuqBdOf hT ℓ' hl').K.Λ 0 U) (h : (xuCT hT).Lev (ℓ' + Om1)) :
    XuqAt T ((xuCT hT).lv (ℓ' + Om1) h) 0 (xuqW (xuqBdOf hT ℓ' hl') U hU) :=
  xuq_at_succ_lv hT (xuqLv_lev hT hl') h (xuqW_at (xuqBdOf hT ℓ' hl') U hU)

include hl' hS in
/-- **THE STEP AT EVERY SUCCESSOR BAND `ℓ' + Ω₁`** (`ℓ'` an (A3) band level): the `Ω₁`-union `Xp.xuqW` of the band
`ℓ'` over the system of `ℓ'`. -/
theorem xuqStep_succ : XuqStepAt hT (ℓ' + Om1) := by
  intro f H
  have hlt : ℓ' < ℓ' + Om1 := lt_add_of_pos_right _ gv_Om1_pos
  set U := f ℓ' hlt with hUdef
  have hOk : XuqOk hT ℓ' U := H.1 ℓ' hlt hl'
  have hU : XuqAt T (xuqBdOf hT ℓ' hl').K.Λ 0 U := hOk.at_ (xuqLv_lev hT hl')
  set V := xuqW (xuqBdOf hT ℓ' hl') U hU with hVdef
  have hUB : U.B = veblen ℓ' 0 := xuqOk_B hT hl' hOk
  have hVB : V.B = veblen (ℓ' + Om1) 0 := rfl
  have hext : XuqExt U V := fun c x hc => xuqW_ext0 (xuqBdOf hT ℓ' hl') U hU hc x
  have hlev := xuq_lev_succ hl' hS
  have hwB : xlW.B ≤ U.B := by rw [xlW_B, hUB]; exact veblen_zero_le_veblen_zero.2 (xuq_G1_le hl')
  refine ⟨V, ⟨fun h => xuq_at_W hT hl' hU h, fun c σ hc hσ hσ1 hg => ?_, XuqExt.trans hOk.w hext hwB⟩,
    fun ℓ'' h hl'' => ?_⟩
  · by_cases hgσ : xuGg ℓ' < σ
    · exact ⟨ℓ' + Om1, le_rfl, (xuCT hT).succ_g_lt hσ hl'.2.2 hl'.2.1 hgσ, hc⟩
    · by_cases hcU : c < U.B
      · rw [(hext c 0 hcU).2] at hg
        obtain ⟨b, hb, hgb, hcb⟩ := hOk.sm c σ hcU hσ hσ1 hg
        exact ⟨b, hb.trans hlt.le, hgb, hcb⟩
      · exfalso
        obtain ⟨μ, hμ, hcμ⟩ := (xuqWF (xuqBdOf hT ℓ' hl') U hU).B_cof c hc
        have hg' : (xuqK (xuqBdOf hT ℓ' hl') U μ).g c < σ := by
          rw [← (xuqW_ext (xuqBdOf hT ℓ' hl') U hU hμ hcμ 0).2]; exact hg
        exact hgσ (xuqK_high hU μ hμ c (not_lt.1 hcU) hcμ σ hσ hσ1 hg')
  · have hle : ℓ'' ≤ ℓ' := by
      by_contra hcon
      exact absurd (wt_dvd_step hl'.2.1 hl''.2.1 (not_le.1 hcon)) (not_le.2 h)
    rcases hle.lt_or_eq with hlt'' | rfl
    · have h1 := H.2 ℓ'' ℓ' h hlt hlt'' hl'' hl'
      have hB : (f ℓ'' h).B ≤ U.B := by
        rw [xuqOk_B hT hl'' (H.1 ℓ'' h hl''), hUB]; exact veblen_zero_le_veblen_zero.2 hlt''.le
      exact XuqExt.trans h1 hext hB
    · exact hext

end Succ

end Rest

end Googology.Trans.PoR.InaccPsi.R2.Xu
