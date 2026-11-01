import Googology.Trans.PoR.InaccPsi.R2.XpW

/-!
# XpLv: THE (A3) BANDS ALONG THE CODE INTERFACE `Xc.xcA3`: DATA, TRANSFERS, THE FIRST TWO STEPS

The (A3) band levels are the codes `G < ℓ < t₀` with `Ω₁ ∣ ℓ` (`XpLv`).  The band datum at `ℓ` is the package of the
(A3) family `Xc.xcFam` (`xpPk`, datum `Xc.xcA3.lv ℓ`), `xpBdOf`.

* `xp_nsc_of` (a reading strictly between `y` and `ε_{y+1}` is not strongly critical), `xp_eN_nsc` (**`ε_{y+1}` is not
  strongly critical**), `xpBdOf` (**THE BAND DATUM AT EVERY (A3) LEVEL**);
* `xp_at_succ_lv` (**the bottom of the band `ℓ' + Ω₁` as a band of `ℓ'` is the bottom of the datum `ℓ' + Ω₁`**),
  `xp_at_G1` (`Xl.xlW` at the bottom of `G + Ω₁`), `xp_xg_G1` (`xg(G + Ω₁) = 1`);
* `XpExt`, `XpSm` (SMALL in level form), `XpOk`, `XpCoh`, `XpStepAt`;
* `xpStep_G1`, `xpStep_succ` (**THE STEP AT `G + Ω₁` AND AT EVERY SUCCESSOR BAND `ℓ' + Ω₁`**).

No new axiom.  New definitions: `XpLv`, `xpPk`, `xpBdOf`, `XpExt`, `XpSm`, `XpOk`, `XpCoh`, `XpStepAt`.
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

open Googology.Trans.PoR.InaccPsi.R2.Ho

open Googology.Trans.PoR.InaccPsi.R2.Xl
open Googology.Trans.PoR.InaccPsi.R2.Xp

namespace Googology.Trans.PoR.InaccPsi.R2.Xp

/-! ## Not strongly critical -/

/-- **A reading strictly between `y` and `ε_{y+1}` is not strongly critical.** -/
theorem xp_nsc_of {y r : Ordinal.{0}} (hy : y < r) (hr : r < eN y) : r < veblen r 0 := by
  rcases (left_le_veblen r 0).lt_or_eq with h | h
  · exact h
  · exfalso
    have hE : InE r := by
      have := gg_veblen_eps (x := r) (y := 0) (pos_iff_ne_zero.1 (lt_of_le_of_lt zero_le hy))
      rwa [← h] at this
    exact absurd (eN_le hy hE) (not_le.2 hr)

/-- **`ε_{y+1}` is not strongly critical.** -/
theorem xp_eN_nsc (y : Ordinal.{0}) : eN y < veblen (eN y) 0 := by
  rcases (left_le_veblen (eN y) 0).lt_or_eq with h | h
  · exact h
  · exfalso
    have hy : y < eN y := lt_eN y
    have h1 : (1 : Ordinal.{0}) < eN y := (one_lt_omega0.trans (omega0_lt_inE (eN_E y))).trans_le le_rfl
    have hfix : veblen 1 (eN y) = eN y := by
      have := veblen_veblen_of_lt h1 0; rwa [← h] at this
    have hy1 : y + 1 < eN y := (ev_isSuccLimit_of_inE (eN_E y)).add_one_lt hy
    have hE : InE (veblen 1 (y + 1)) := gg_veblen_eps one_ne_zero
    have hlt : veblen 1 (y + 1) < eN y := by
      have := (isNormal_veblen 1).strictMono hy1; rwa [hfix] at this
    have hgt : y < veblen 1 (y + 1) := (lt_add_one y).trans_le (right_le_veblen 1 _)
    exact absurd (eN_le hgt hE) (not_le.2 hlt)

/-! ## The (A3) band levels and their data -/

/-- **THE (A3) BAND LEVELS**: `G < ℓ < t₀`, `Ω₁ ∣ ℓ`. -/
def XpLv (ℓ : Ordinal.{0}) : Prop := gcG 0 < ℓ ∧ Om1 ∣ ℓ ∧ ℓ < Wj.wjT 0

theorem xpLv_lev {ℓ : Ordinal.{0}} (h : XpLv ℓ) : xcA3.Lev ℓ := ⟨(gl_Om1_lt_G0.trans h.1).le, h.2.1, h.2.2⟩

/-- **The package of the (A3) family at the level `ℓ`.** -/
noncomputable def xpPk (ℓ : Ordinal.{0}) (h : xcA3.Lev ℓ) : HnPk :=
  wsPkOf ℓ h (wsF xcCls ℓ) (xcFam ℓ h h.2.2).1

theorem xpPk_Λ (ℓ : Ordinal.{0}) (h : xcA3.Lev ℓ) : (xpPk ℓ h).Λ = xcA3.lv ℓ h := rfl

theorem xp_lvl {ℓ x : Ordinal.{0}} (h : xcA3.Lev ℓ) (hx : InE x) (hx1 : x < Om1) (hg : xg ℓ < x) :
    (xcA3.lv ℓ h).l x = wtD.R ℓ x := xcA3.lv_l h hx hx1 hg

/-- **THE BAND DATUM AT EVERY (A3) LEVEL `ℓ`.** -/
noncomputable def xpBdOf (ℓ : Ordinal.{0}) (h : XpLv ℓ) : XpBd where
  K := xpPk ℓ (xpLv_lev h)
  G_lt := h.1
  l_nsc := fun x hx hx1 hg => by
    have hg' : wtD.g ℓ < x := (xg_lt_iff hx).1 hg
    show (xcA3.lv ℓ (xpLv_lev h)).l x < veblen ((xcA3.lv ℓ (xpLv_lev h)).l x) 0
    rw [xp_lvl (xpLv_lev h) hx hx1 hg]
    exact xp_nsc_of (wt_R_gtG h.1 h.2.2 hx hx1 hg') (goGl.hR_lt_eNb hx hx1 (wt_LB h.2.2) hg')
  l_lt := fun x hx hx1 hg => by
    have hg' : wtD.g ℓ < x := (xg_lt_iff hx).1 hg
    show (xcA3.lv ℓ (xpLv_lev h)).l x < _
    rw [xp_lvl (xpLv_lev h) hx hx1 hg, wnLv3T0_l hx hx1]
    exact goGl.hR_lt_eNb hx hx1 (wt_LB h.2.2) hg'

theorem xpBdOf_Λ (ℓ : Ordinal.{0}) (h : XpLv ℓ) : (xpBdOf ℓ h).K.Λ = xcA3.lv ℓ (xpLv_lev h) := rfl

/-! ## Transfers -/

/-- **THE BOTTOM OF THE BAND `ℓ' + Ω₁` OVER THE DATUM `ℓ'` IS THE BOTTOM OVER THE DATUM `ℓ' + Ω₁`.** -/
theorem xp_at_succ_lv {ℓ' : Ordinal.{0}} (h' : xcA3.Lev ℓ') (h : xcA3.Lev (ℓ' + Om1)) {U : HgVD}
    (hU : XpAt (xcA3.lv ℓ' h').succ 0 U) : XpAt (xcA3.lv (ℓ' + Om1) h) 0 U := by
  refine xpAt_congr hU rfl (fun x hx _ => ⟨fun hg => xcA3.succ_g_lt hx h'.2.2 h'.2.1 hg,
    fun hg => (xcA3.succ_g ℓ' h'.2.2 h'.2.1).trans_lt hg⟩) (xcA3.succ_g ℓ' h'.2.2 h'.2.1) (fun x hx hx1 hg => ?_)
  have hg' : xcA3.g ℓ' < x := (xcA3.succ_g ℓ' h'.2.2 h'.2.1).trans_lt hg
  show xcA3.rd (ℓ' + Om1) x = xcA3.rd ℓ' x + x
  rw [xcA3.rd_eq hx hx1 h.1 h.2.2 hg, xcA3.rd_eq hx hx1 h'.1 h'.2.2 hg', xcA3.succ_R ℓ' h'.2.2 h'.2.1 x]

theorem xp_lev_G1 : XpLv (gcG 0 + Om1) :=
  ⟨lt_add_of_pos_right _ gv_Om1_pos, dvd_add wt_Om1_dvd_G (dvd_refl _), wt_GO_lt⟩

/-- **`Xl.xlW` IS A SYSTEM AT THE BOTTOM OF THE DATUM `G + Ω₁`.** -/
theorem xp_at_G1 (h : xcA3.Lev (gcG 0 + Om1)) : XpAt (xcA3.lv (gcG 0 + Om1) h) 0 xlW :=
  xp_at_succ_lv xf_lev_G h xp_at_xlW

/-- **`xg(G + Ω₁) = 1`.** -/
theorem xp_xg_G1 : xg (gcG 0 + Om1) = 1 := by
  have hG1 : (1 : Ordinal.{0}) < gcG 0 := xf_one_lt_G
  have h := xg_pre (j := 1) (q := 1) (t := Om1) one_ne_zero one_ne_zero hG1
    (by rw [opow_one]; exact gl_Om1_lt_G0) (by rw [opow_one, mul_one]; exact wt_GO_lt)
  rw [opow_one, mul_one, goGl.Q_one] at h
  rw [h]
  have hQ : goGl.hQ 1 = 0 := by unfold GoD.hQ; rw [if_pos one_lt_omega0]
  have hO : xg Om1 = 1 := by unfold xg; rw [xcG_Om1, max_self]
  rw [hQ, hO, max_self, max_eq_right zero_le]

theorem xp_xg_ge_one (c : Ordinal.{0}) : 1 ≤ xg c := le_max_left _ _

/-- Every (A3) band level is at least `G + Ω₁`. -/
theorem xp_G1_le {ℓ : Ordinal.{0}} (h : XpLv ℓ) : gcG 0 + Om1 ≤ ℓ := wt_dvd_step wt_Om1_dvd_G h.2.1 h.1

/-! ## The invariant -/

/-- **`V` extends `U`.** -/
def XpExt (U V : HgVD) : Prop := ∀ c x, c < U.B → V.R c x = U.R c x ∧ V.g c = U.g c

theorem XpExt.refl (U : HgVD) : XpExt U U := fun _ _ _ => ⟨rfl, rfl⟩

theorem XpExt.trans {U V W : HgVD} (h1 : XpExt U V) (h2 : XpExt V W) (hB : U.B ≤ V.B) : XpExt U W :=
  fun c x hc => by
    obtain ⟨a1, b1⟩ := h1 c x hc
    obtain ⟨a2, b2⟩ := h2 c x (hc.trans_le hB)
    exact ⟨a2.trans a1, b2.trans b1⟩

/-- **SMALL IN LEVEL FORM**: a code of `V` with gate below an `ε`-number `σ` lies below `φ(b, 0)` for some `b ≤ ℓ`
with `xg b < σ`. -/
def XpSm (ℓ : Ordinal.{0}) (V : HgVD) : Prop :=
  ∀ c σ, c < V.B → InE σ → σ < Om1 → V.g c < σ → ∃ b, b ≤ ℓ ∧ xg b < σ ∧ c < veblen b 0

/-- **THE INVARIANT AT THE LEVEL `ℓ`**: `V` is a system at the bottom `φ(ℓ, 0)` of the datum `ℓ`, SMALL, and it
extends `Xl.xlW` (hence `Hg.hgU`). -/
structure XpOk (ℓ : Ordinal.{0}) (V : HgVD) : Prop where
  at_ : ∀ h : xcA3.Lev ℓ, XpAt (xcA3.lv ℓ h) 0 V
  sm : XpSm ℓ V
  w : XpExt xlW V

/-- **A COHERENT FAMILY BELOW `ℓ`.** -/
def XpCoh (ℓ : Ordinal.{0}) (f : ∀ ℓ' : Ordinal.{0}, ℓ' < ℓ → HgVD) : Prop :=
  (∀ ℓ' (h : ℓ' < ℓ), XpLv ℓ' → XpOk ℓ' (f ℓ' h)) ∧
    ∀ ℓ'' ℓ' (h'' : ℓ'' < ℓ) (h' : ℓ' < ℓ), ℓ'' < ℓ' → XpLv ℓ'' → XpLv ℓ' → XpExt (f ℓ'' h'') (f ℓ' h')

/-- **THE STEP AT `ℓ`**: every coherent family below `ℓ` has a system at `ℓ` extending all of it. -/
def XpStepAt (ℓ : Ordinal.{0}) : Prop :=
  ∀ f, XpCoh ℓ f → ∃ V, XpOk ℓ V ∧ ∀ ℓ' (h : ℓ' < ℓ), XpLv ℓ' → XpExt (f ℓ' h) V

theorem xpOk_B {ℓ : Ordinal.{0}} (h : XpLv ℓ) {V : HgVD} (hV : XpOk ℓ V) : V.B = veblen ℓ 0 := by
  rw [(hV.at_ (xpLv_lev h)).B, add_zero]; rfl

theorem xpOk_γ {ℓ : Ordinal.{0}} (h : XpLv ℓ) {V : HgVD} (hV : XpOk ℓ V) : V.γ ≤ xg ℓ := by
  have := (hV.at_ (xpLv_lev h)).γ_le
  rwa [max_eq_right zero_le] at this

/-- Coherence including equality. -/
theorem XpCoh.ext_le {ℓ : Ordinal.{0}} {f : ∀ ℓ' : Ordinal.{0}, ℓ' < ℓ → HgVD} (H : XpCoh ℓ f) {ℓ'' ℓ' : Ordinal.{0}}
    (h'' : ℓ'' < ℓ) (h' : ℓ' < ℓ) (hle : ℓ'' ≤ ℓ') (hl'' : XpLv ℓ'') (hl' : XpLv ℓ') :
    XpExt (f ℓ'' h'') (f ℓ' h') := by
  rcases hle.lt_or_eq with hlt | rfl
  · exact H.2 ℓ'' ℓ' h'' h' hlt hl'' hl'
  · exact XpExt.refl _

/-! ## The step at `G + Ω₁` -/

theorem xp_xgG1_lt {σ : Ordinal.{0}} (hσ : InE σ) : xg (gcG 0 + Om1) < σ := by
  rw [xp_xg_G1]; exact wo_one_lt_inE hσ

/-- **THE STEP AT `G + Ω₁`**: `Xl.xlW`. -/
theorem xpStep_G1 : XpStepAt (gcG 0 + Om1) := by
  intro f _
  refine ⟨xlW, ⟨fun h => xp_at_G1 h, fun c σ hc hσ _ _ => ⟨gcG 0 + Om1, le_rfl, xp_xgG1_lt hσ, hc⟩,
    XpExt.refl _⟩,
    fun ℓ' h hl => absurd (xp_G1_le hl) (not_le.2 h)⟩

/-! ## The step at a successor band -/

section Succ

variable {ℓ' : Ordinal.{0}} (hl' : XpLv ℓ') (hS : ℓ' + Om1 < Wj.wjT 0)

include hl' hS in
theorem xp_lev_succ : XpLv (ℓ' + Om1) :=
  ⟨hl'.1.trans_le le_self_add, dvd_add hl'.2.1 (dvd_refl _), hS⟩

/-- **THE `Ω₁`-UNION OF THE BAND `ℓ'` IS A SYSTEM AT THE BOTTOM OF THE DATUM `ℓ' + Ω₁`.** -/
theorem xp_at_W {U : HgVD} (hU : XpAt (xpBdOf ℓ' hl').K.Λ 0 U) (h : xcA3.Lev (ℓ' + Om1)) :
    XpAt (xcA3.lv (ℓ' + Om1) h) 0 (xpW (xpBdOf ℓ' hl') U hU) :=
  xp_at_succ_lv (xpLv_lev hl') h (xpW_at (xpBdOf ℓ' hl') U hU)

include hl' hS in
/-- **THE STEP AT EVERY SUCCESSOR BAND `ℓ' + Ω₁`** (`ℓ'` an (A3) band level): the `Ω₁`-union `Xp.xpW` of the band
`ℓ'` over the system of `ℓ'`. -/
theorem xpStep_succ : XpStepAt (ℓ' + Om1) := by
  intro f H
  have hlt : ℓ' < ℓ' + Om1 := lt_add_of_pos_right _ gv_Om1_pos
  set U := f ℓ' hlt with hUdef
  have hOk : XpOk ℓ' U := H.1 ℓ' hlt hl'
  have hU : XpAt (xpBdOf ℓ' hl').K.Λ 0 U := hOk.at_ (xpLv_lev hl')
  set V := xpW (xpBdOf ℓ' hl') U hU with hVdef
  have hUB : U.B = veblen ℓ' 0 := xpOk_B hl' hOk
  have hVB : V.B = veblen (ℓ' + Om1) 0 := rfl
  have hext : XpExt U V := fun c x hc => xpW_ext0 (xpBdOf ℓ' hl') U hU hc x
  have hlev := xp_lev_succ hl' hS
  have hwB : xlW.B ≤ U.B := by rw [xlW_B, hUB]; exact veblen_zero_le_veblen_zero.2 (xp_G1_le hl')
  refine ⟨V, ⟨fun h => xp_at_W hl' hU h, fun c σ hc hσ hσ1 hg => ?_, XpExt.trans hOk.w hext hwB⟩,
    fun ℓ'' h hl'' => ?_⟩
  · by_cases hgσ : xg ℓ' < σ
    · exact ⟨ℓ' + Om1, le_rfl, xcA3.succ_g_lt hσ hl'.2.2 hl'.2.1 hgσ, hc⟩
    · by_cases hcU : c < U.B
      · rw [(hext c 0 hcU).2] at hg
        obtain ⟨b, hb, hgb, hcb⟩ := hOk.sm c σ hcU hσ hσ1 hg
        exact ⟨b, hb.trans hlt.le, hgb, hcb⟩
      · exfalso
        obtain ⟨μ, hμ, hcμ⟩ := (xpWF (xpBdOf ℓ' hl') U hU).B_cof c hc
        have hg' : (xpK (xpBdOf ℓ' hl') U μ).g c < σ := by
          rw [← (xpW_ext (xpBdOf ℓ' hl') U hU hμ hcμ 0).2]; exact hg
        exact hgσ (xpK_high hU μ hμ c (not_lt.1 hcU) hcμ σ hσ hσ1 hg')
  · have hle : ℓ'' ≤ ℓ' := by
      by_contra hcon
      exact absurd (wt_dvd_step hl'.2.1 hl''.2.1 (not_le.1 hcon)) (not_le.2 h)
    rcases hle.lt_or_eq with hlt'' | rfl
    · have h1 := H.2 ℓ'' ℓ' h hlt hlt'' hl'' hl'
      have hB : (f ℓ'' h).B ≤ U.B := by
        rw [xpOk_B hl'' (H.1 ℓ'' h hl''), hUB]; exact veblen_zero_le_veblen_zero.2 hlt''.le
      exact XpExt.trans h1 hext hB
    · exact hext

end Succ

end Googology.Trans.PoR.InaccPsi.R2.Xp
