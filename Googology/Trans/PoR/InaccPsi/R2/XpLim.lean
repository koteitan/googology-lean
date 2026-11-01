import Googology.Trans.PoR.InaccPsi.R2.XpLv

/-!
# XpLim: THE STEP AT A LIMIT (A3) BAND (`ω`- AND `Ω₁`-SEQUENCES OF BANDS)

At a band level `ℓ` that is not a successor `ℓ' + Ω₁`, the (A3) classification `Xc.xcCls` gives an `ω`-sequence or
an `Ω₁`-sequence of levels below `ℓ` (`Xc.xc_br`).  The members are the systems of the coherent family at
`t(c) = max(c, G + Ω₁)`.

* `xp_lv_lim`, `xp_R_lim` (**the reading of a limit code is a limit**), `xpOk_b`, `xpOk_Z`;
* `xpChL` (**THE `ω`-CHAIN OF BANDS**, bound `φ(ℓ, 0)`, gate `xg ℓ`), `xpStep_fs`;
* `xpFamO` (**THE `Ω₁`-FAMILY OF BANDS**: `Ho.HoFam`, SMALL from the level form `XpSm` of the members and the
  fourth field of `Ws.WsC.Seq1`), `xpStep_sq`.

No new axiom.  New definitions: `xpT`, `xpChL`, `xpFamO`.
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

/-! ## Limits and readings -/

theorem xp_lv_lim {ℓ : Ordinal.{0}} (h : XpLv ℓ) : IsSuccLimit ℓ := by
  obtain ⟨k, hk⟩ := h.2.1
  have hk0 : 0 < k := by
    rcases eq_or_ne k 0 with h0 | h0
    · rw [h0, mul_zero] at hk; exact absurd (hk ▸ h.1) (not_lt.2 zero_le)
    · exact pos_iff_ne_zero.2 h0
  rw [hk]; exact isSuccLimit_mul_left gl_Om1_lim hk0

/-- **The reading of a limit level is a limit.** -/
theorem xp_R_lim {ℓ x : Ordinal.{0}} (h : xcA3.Lev ℓ) (hx : InE x) (hx1 : x < Om1) (hg : xg ℓ < x) :
    IsSuccLimit (xcA3.R ℓ x) := by
  have hne : xcA3.R ℓ x ≠ 0 := WsC.R_ne0 (C := xcA3) hx hx1 h.1 h.2.2 hg
  rcases zero_or_succ_or_isSuccLimit (xcA3.R ℓ x) with h0 | ⟨a, ha⟩ | hl
  · exact absurd h0 hne
  · exfalso
    have ha' : a < xcA3.R ℓ x := by rw [← ha]; exact Order.lt_succ a
    obtain ⟨b, hb, hgb, hab⟩ := xcA3.R_cof hx hx1 h.2.2 hg a ha'
    have hb1 : b + 1 < ℓ := xcA3.lev_lim h hb
    have h2 := WsC.R_succ_lt (C := xcA3) hx hx1 h.2.2 hb1 hg hgb
    rw [← ha, Order.succ_eq_add_one] at h2
    exact absurd (hab.trans_lt ((lt_add_one _).trans_le (Order.lt_add_one_iff.1 h2))) (lt_irrefl _)
  · exact hl

section Ok

variable {ℓ : Ordinal.{0}} (hℓ : XpLv ℓ) {V : HgVD} (hV : XpOk ℓ V)
include hℓ hV

theorem xpOk_b {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hg : xg ℓ < x) :
    V.b x = veblen (xcA3.R ℓ x) 0 := by
  rw [(hV.at_ (xpLv_lev hℓ)).b x hx hx1 (by rw [max_eq_right zero_le]; exact hg), add_zero]
  exact congrArg (fun a => veblen a 0) (xcA3.lv_l (xpLv_lev hℓ) hx hx1 hg)

theorem xpOk_Z {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    V.Z x = if xg ℓ < x then evZ (veblen (xcA3.R ℓ x) 0) else xpZ x := by
  have e : (xcA3.lv ℓ (xpLv_lev hℓ)).g = xg ℓ := rfl
  rw [(hV.at_ (xpLv_lev hℓ)).Z x hx hx1, max_eq_right zero_le, e]
  by_cases hg : xg ℓ < x
  · rw [if_pos hg, if_pos hg, add_zero]
    exact congrArg (fun a => evZ (veblen a 0)) (xcA3.lv_l (xpLv_lev hℓ) hx hx1 hg)
  · rw [if_neg hg, if_neg hg]

end Ok

/-- `φ(R ℓ x, 0)` below the low field. -/
theorem xp_RZ {ℓ x : Ordinal.{0}} (hℓ : XpLv ℓ) (hx : InE x) (hx1 : x < Om1) (hg : xg ℓ < x) :
    veblen (xcA3.R ℓ x) 0 < xpZ x := by
  have h := xp_veb_lt_Z (xpBdOf ℓ hℓ) hx hx1 hg hx.pos
  rw [add_zero] at h
  rwa [show (xpBdOf ℓ hℓ).K.Λ.l x = xcA3.R ℓ x from xcA3.lv_l (xpLv_lev hℓ) hx hx1 hg] at h

theorem xp_R_nsc {ℓ x : Ordinal.{0}} (hℓ : XpLv ℓ) (hx : InE x) (hx1 : x < Om1) (hg : xg ℓ < x) :
    xcA3.R ℓ x < veblen (xcA3.R ℓ x) 0 := by
  have h := (xpBdOf ℓ hℓ).l_nsc x hx hx1 hg
  rwa [show (xpBdOf ℓ hℓ).K.Λ.l x = xcA3.R ℓ x from xcA3.lv_l (xpLv_lev hℓ) hx hx1 hg] at h

theorem xp_x_le_R {ℓ x : Ordinal.{0}} (hℓ : XpLv ℓ) (hx : InE x) (hx1 : x < Om1) (hg : xg ℓ < x) :
    x ≤ xcA3.R ℓ x := xcA3.le_R hx hx1 (xpLv_lev hℓ).1 hℓ.2.2 hg

/-- **Lemma EXACT for `φ(R ℓ x, 0)`.** -/
theorem xp_R_pi {ℓ σ ρ : Ordinal.{0}} (hℓ : XpLv ℓ) (hB : Bases σ ρ) (hγ : xg ℓ < σ) :
    veblen (xcA3.R ℓ ρ) 0 ∈ TB ρ σ ∧ pi σ ρ (veblen (xcA3.R ℓ ρ) 0) = veblen (xcA3.R ℓ σ) 0 := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  have h0σ : (0 : Ordinal.{0}) < σ := hB.1.pos
  have h := hnv_glA_pi (xpBdOf ℓ hℓ).K.Λ (ν := 0) hB hγ h0σ (mem_TB_of_lt hB h0σ) (gm1_facts hB.2.1 hρ1).2.2.2.pos
  rw [pi_lt hB h0σ, xp_glA (xpBdOf ℓ hℓ).toXpBd0 hB.2.1 hρ1 (hγ.trans hB.2.2.1) hB.2.1.pos 0 (hcN_E _ _).pos,
    xp_glA (xpBdOf ℓ hℓ).toXpBd0 hB.1 hσ1 hγ h0σ 0 (hcN_E _ _).pos, add_zero, add_zero,
    show (xpBdOf ℓ hℓ).K.Λ.l ρ = xcA3.R ℓ ρ from xcA3.lv_l (xpLv_lev hℓ) hB.2.1 hρ1 (hγ.trans hB.2.2.1),
    show (xpBdOf ℓ hℓ).K.Λ.l σ = xcA3.R ℓ σ from xcA3.lv_l (xpLv_lev hℓ) hB.1 hσ1 hγ] at h
  exact h

/-- **A code over `Z` of `φ(ℓ, 0)` has the gate of `ℓ` below `Z`.** -/
theorem xp_cl_g {ℓ Z : Ordinal.{0}} (hℓ : XpLv ℓ) (hZ : SC Z) (hZ1 : Z ≤ Om 1) (h : GxCl Z {gcG 0} (veblen ℓ 0)) :
    xg ℓ < Z := by
  have hGQ : gcG 0 < veblen ((xpBdOf ℓ hℓ).K.Λ.L + 0) 0 := by
    rw [add_zero]; exact hℓ.1.trans_le (left_le_veblen _ 0)
  have hs : veblen ((xpBdOf ℓ hℓ).K.Λ.L + 0) 0 < veblen ((xpBdOf ℓ hℓ).K.Λ.L + 0) (0 + 1) :=
    (isNormal_veblen _).strictMono (show (0 : Ordinal.{0}) < 0 + 1 by rw [zero_add]; exact zero_lt_one)
  have h' : GxCl Z {gcG 0} (veblen ((xpBdOf ℓ hℓ).K.Λ.L + 0) 0) := by rw [add_zero]; exact h
  exact hnv_cl_g (xpBdOf ℓ hℓ).K.Λ gv_Om1_pos hZ hZ1 veblen_pos hGQ h' le_rfl hs

theorem xp_t0_lt1 : Wj.wjT 0 < gcG 1 := xcLvT0.L_G1

theorem xp_B_lt1 {ℓ : Ordinal.{0}} (hℓ : XpLv ℓ) : veblen ℓ 0 < gcG 1 := by
  have h := (isNormal_veblen ℓ).strictMono (gcG_SC 1).1
  rwa [gn_veb_fix (gcG_SC 1) (hℓ.2.2.trans xp_t0_lt1)] at h

/-! ## The members `t(c) = max(c, G + Ω₁)` -/

/-- **The member level**: `max(c, G + Ω₁)`. -/
noncomputable def xpT (c : Ordinal.{0}) : Ordinal.{0} := max c (gcG 0 + Om1)

theorem xpT_lv {ℓ c : Ordinal.{0}} (hℓ : XpLv ℓ) (hG1 : gcG 0 + Om1 < ℓ) (hc : Om1 ∣ c) (hcl : c < ℓ) :
    XpLv (xpT c) ∧ xpT c < ℓ := by
  have hlt : xpT c < ℓ := max_lt hcl hG1
  refine ⟨⟨(lt_add_of_pos_right _ gv_Om1_pos).trans_le (le_max_right _ _), ?_, hlt.trans hℓ.2.2⟩, hlt⟩
  unfold xpT
  rcases le_total c (gcG 0 + Om1) with h | h
  · rw [max_eq_right h]; exact xp_lev_G1.2.1
  · rw [max_eq_left h]; exact hc

theorem xpT_g_lt {c x : Ordinal.{0}} (hx : InE x) (hg : xg c < x) : xg (xpT c) < x := by
  unfold xpT
  rcases le_total c (gcG 0 + Om1) with h | h
  · rw [max_eq_right h]; exact xp_xgG1_lt hx
  · rw [max_eq_left h]; exact hg

theorem xpT_g_le {c ℓ : Ordinal.{0}} (hg : xg c ≤ xg ℓ) : xg (xpT c) ≤ xg ℓ := by
  unfold xpT
  rcases le_total c (gcG 0 + Om1) with h | h
  · rw [max_eq_right h, xp_xg_G1]; exact xp_xg_ge_one ℓ
  · rw [max_eq_left h]; exact hg

theorem xpT_ge (c : Ordinal.{0}) : c ≤ xpT c := le_max_left _ _

theorem xpT_mono {c d : Ordinal.{0}} (h : c ≤ d) : xpT c ≤ xpT d := max_le_max h le_rfl

/-! ## A system at the bottom of a datum from its fields -/

/-- **A system with bound and index `φ(ℓ, 0)`, gate `xg ℓ`, base reading `φ(R ℓ x, 0)` and bound field
`ζ(φ(R ℓ x, 0))` is a system at the bottom of the datum `ℓ`.** -/
theorem xpAt_of {ℓ : Ordinal.{0}} {V : HgVD} (hB : V.B = veblen ℓ 0) (hix : V.ix = veblen ℓ 0) (hγ : V.γ = xg ℓ)
    (hb : ∀ x, InE x → x < Om1 → xg ℓ < x → V.b x = veblen (xcA3.R ℓ x) 0)
    (hZ : ∀ x, InE x → x < Om1 → V.Z x = if xg ℓ < x then evZ (veblen (xcA3.R ℓ x) 0) else xpZ x) :
    ∀ h : xcA3.Lev ℓ, XpAt (xcA3.lv ℓ h) 0 V := fun h => by
  have e : (xcA3.lv ℓ h).g = xg ℓ := rfl
  have eL : (xcA3.lv ℓ h).L = ℓ := rfl
  refine ⟨by rw [hB, eL, add_zero], by rw [hix, eL, add_zero], fun x _ _ => by rw [hγ, e, max_eq_right zero_le],
    fun x hx hx1 hg => ?_, by rw [hγ, e, max_eq_right zero_le], fun x hx hx1 => ?_⟩
  · rw [e, max_eq_right zero_le] at hg
    rw [hb x hx hx1 hg, add_zero, xcA3.lv_l h hx hx1 hg]
  · rw [hZ x hx hx1, e, max_eq_right zero_le]
    by_cases hg : xg ℓ < x
    · rw [if_pos hg, if_pos hg, add_zero, xcA3.lv_l h hx hx1 hg]
    · rw [if_neg hg, if_neg hg]

theorem xp_one_lt_lv {ℓ : Ordinal.{0}} (hℓ : XpLv ℓ) : (1 : Ordinal.{0}) < ℓ := xf_one_lt_G.trans hℓ.1

theorem xp_two_lt_R {ℓ x : Ordinal.{0}} (hℓ : XpLv ℓ) (hx : InE x) (hx1 : x < Om1) (hg : xg ℓ < x) :
    (2 : Ordinal.{0}) < xcA3.R ℓ x :=
  ((show (2 : Ordinal.{0}) < ω from (by exact_mod_cast natCast_lt_omega0 2)).trans (omega0_lt_inE hx)).trans_le
    (xp_x_le_R hℓ hx hx1 hg)

/-! ## The `ω`-chain of bands -/

section Fs

variable {ℓ : Ordinal.{0}} (hℓ : XpLv ℓ) (hG1 : gcG 0 + Om1 < ℓ) {f : ∀ ℓ' : Ordinal.{0}, ℓ' < ℓ → HgVD}
  (H : XpCoh ℓ f) {cs : ℕ → Ordinal.{0}} (hML : ∀ k, ML (cs k)) (hmono : ∀ k, cs k < cs (k + 1))
  (hlt : ∀ k, cs k < ℓ) (hcof : ∀ t, t < ℓ → ∃ k, t < cs k) (hgk : ∀ k, xg (cs k) ≤ xg ℓ)

include hℓ hG1 hML hlt in
theorem xpF_lv (k : ℕ) : XpLv (xpT (cs k)) ∧ xpT (cs k) < ℓ := xpT_lv hℓ hG1 (hML k).2 (hlt k)

include H in
theorem xpF_ok (k : ℕ) (hk : XpLv (xpT (cs k)) ∧ xpT (cs k) < ℓ) : XpOk (xpT (cs k)) (f (xpT (cs k)) hk.2) :=
  H.1 _ hk.2 hk.1

/-- **THE `ω`-CHAIN OF BANDS** below a limit band level `ℓ`: bound `φ(ℓ, 0)`, gate `xg ℓ`. -/
noncomputable def xpChL : HgfCh where
  D := fun k => f (xpT (cs k)) (xpF_lv hℓ hG1 hML hlt k).2
  B := veblen ℓ 0
  b := fun x => veblen (xcA3.R ℓ x) 0
  γ := xg ℓ
  Zo := xpZ
  γ_lt := xcA3.g_lt ℓ hℓ.2.2
  γ0 := fun k => (xpOk_γ (xpF_lv hℓ hG1 hML hlt k).1 (xpF_ok H k (xpF_lv hℓ hG1 hML hlt k))).trans (xpT_g_le (hgk k))
  γ_cl := fun _ hZ hZ1 h => xp_cl_g hℓ hZ hZ1 h
  B_mono := fun k => by
    rw [xpOk_B (xpF_lv hℓ hG1 hML hlt k).1 (xpF_ok H k (xpF_lv hℓ hG1 hML hlt k)),
      xpOk_B (xpF_lv hℓ hG1 hML hlt (k + 1)).1 (xpF_ok H (k + 1) (xpF_lv hℓ hG1 hML hlt (k + 1)))]
    exact veblen_zero_le_veblen_zero.2 (xpT_mono (hmono k).le)
  B_lt := fun k => by
    rw [xpOk_B (xpF_lv hℓ hG1 hML hlt k).1 (xpF_ok H k (xpF_lv hℓ hG1 hML hlt k))]
    exact veblen_zero_lt_veblen_zero.2 (xpF_lv hℓ hG1 hML hlt k).2
  B_cof := fun c hc => by
    obtain ⟨a, ha, hca⟩ := wx_veb_lim_cof0 (xp_lv_lim hℓ) hc
    obtain ⟨k, hk⟩ := hcof a ha
    refine ⟨k, ?_⟩
    rw [xpOk_B (xpF_lv hℓ hG1 hML hlt k).1 (xpF_ok H k (xpF_lv hℓ hG1 hML hlt k))]
    exact hca.trans_le (veblen_zero_le_veblen_zero.2 (hk.le.trans (xpT_ge _)))
  R_ext := fun k c x hc => (H.ext_le _ _ (xpT_mono (hmono k).le) (xpF_lv hℓ hG1 hML hlt k).1
    (xpF_lv hℓ hG1 hML hlt (k + 1)).1 c x hc).1
  g_ext := fun k c hc => (H.ext_le _ _ (xpT_mono (hmono k).le) (xpF_lv hℓ hG1 hML hlt k).1
    (xpF_lv hℓ hG1 hML hlt (k + 1)).1 c 0 hc).2
  B_lt1 := xp_B_lt1 hℓ
  B_fix := veblen_veblen_of_lt (xp_one_lt_lv hℓ) 0
  B_mem := fun S _ _ ha hb => CSet.phi_mem (xcA3.L_mem ℓ hℓ.2.2 S _ _ ha hb) (CSet.zero_mem _ _)
  b_ge := fun k x hx hx1 hγ => by
    have hgk' : xg (xpT (cs k)) < x := (xpT_g_le (hgk k)).trans_lt hγ
    rw [xpOk_b (xpF_lv hℓ hG1 hML hlt k).1 (xpF_ok H k (xpF_lv hℓ hG1 hML hlt k)) hx hx1 hgk']
    exact (veblen_zero_lt_veblen_zero.2
      (xcA3.R_mono hx hx1 hℓ.2.2 (xpF_lv hℓ hG1 hML hlt k).2 hγ hgk')).le
  b_cof := fun x hx hx1 hγ ν hν => by
    obtain ⟨a, ha, hνa⟩ := wx_veb_lim_cof0 (xp_R_lim (xpLv_lev hℓ) hx hx1 hγ) hν
    obtain ⟨b, hb, hgb, hab⟩ := xcA3.R_cof hx hx1 hℓ.2.2 hγ a ha
    obtain ⟨k, hk⟩ := hcof b hb
    have hgk' : xg (xpT (cs k)) < x := (xpT_g_le (hgk k)).trans_lt hγ
    refine ⟨k, ?_⟩
    rw [xpOk_b (xpF_lv hℓ hG1 hML hlt k).1 (xpF_ok H k (xpF_lv hℓ hG1 hML hlt k)) hx hx1 hgk']
    exact hνa.trans_le (veblen_zero_le_veblen_zero.2 (hab.trans (xcA3.R_mono hx hx1
      (xpF_lv hℓ hG1 hML hlt k).1.2.2 (hk.trans_le (xpT_ge _)) hgk' hgb).le))
  b_fix := fun x hx hx1 hγ => veblen_veblen_of_lt ((wo_one_lt_inE hx).trans_le (xp_x_le_R hℓ hx hx1 hγ)) 0
  b_gt := fun x hx hx1 hγ => (xp_x_le_R hℓ hx hx1 hγ).trans_lt (xp_R_nsc hℓ hx hx1 hγ)
  b_lt := fun x hx hx1 hγ => (xp_RZ hℓ hx hx1 hγ).trans (xpZ_G1 hx hx1)
  b_pi := fun _ _ hB hγ => xp_R_pi hℓ hB hγ
  Z_low := fun k x hx hx1 _ => by
    rw [xpOk_Z (xpF_lv hℓ hG1 hML hlt k).1 (xpF_ok H k (xpF_lv hℓ hG1 hML hlt k)) hx hx1]
    split_ifs with h
    · exact (hb_evZ_lt_fix2 (xpZ_fix x) (xp_RZ (xpF_lv hℓ hG1 hML hlt k).1 hx hx1 h)).le
    · exact le_rfl
  Zo_fix := xpZ_fix1
  Zo_G1 := fun _ hx hx1 => xpZ_G1 hx hx1

theorem xpChL_U_b (x : Ordinal.{0}) :
    (xpChL hℓ hG1 H hML hmono hlt hcof hgk).U.b x = veblen (xcA3.R ℓ x) 0 := rfl

theorem xpChL_U_Z (x : Ordinal.{0}) : (xpChL hℓ hG1 H hML hmono hlt hcof hgk).U.Z x =
    if xg ℓ < x then evZ (veblen (xcA3.R ℓ x) 0) else xpZ x := (xpChL hℓ hG1 H hML hmono hlt hcof hgk).U_Z x

end Fs

/-- **THE STEP AT A BAND LEVEL WITH AN `ω`-SEQUENCE OF LEVELS.** -/
theorem xpStep_fs {ℓ : Ordinal.{0}} (hℓ : XpLv ℓ) (hG1 : gcG 0 + Om1 < ℓ) (hfs : XFs xcA3 ML ℓ) : XpStepAt ℓ := by
  intro f H
  obtain ⟨cs, hML, hmono, hlt, hcof, hgk⟩ := hfs
  obtain ⟨C, hC⟩ : ∃ C, C = xpChL hℓ hG1 H hML hmono hlt hcof hgk := ⟨_, rfl⟩
  have hlv := xpF_lv hℓ hG1 hML hlt (cs := cs)
  refine ⟨C.U, ⟨xpAt_of (by rw [hC]; rfl) (by rw [hC]; rfl) (by rw [hC]; rfl)
    (fun x _ _ _ => by rw [hC]; exact xpChL_U_b hℓ hG1 H hML hmono hlt hcof hgk x)
    (fun x _ _ => by rw [hC]; exact xpChL_U_Z hℓ hG1 H hML hmono hlt hcof hgk x),
    fun c σ hc hσ hσ1 hg => ?_, ?_⟩, fun ℓ'' h hl'' => ?_⟩
  · obtain ⟨k, hk⟩ := C.B_cof c hc
    rw [C.U_g hk] at hg
    have hk' : c < (f (xpT (cs k)) (hlv k).2).B := by rw [hC] at hk; exact hk
    have hg' : (f (xpT (cs k)) (hlv k).2).g c < σ := by rw [hC] at hg; exact hg
    obtain ⟨b, hb, hgb, hcb⟩ := (xpF_ok H k (hlv k)).sm c σ hk' hσ hσ1 hg'
    exact ⟨b, hb.trans (hlv k).2.le, hgb, hcb⟩
  · have h1 := (xpF_ok H 0 (hlv 0)).w
    have h2 : XpExt (f (xpT (cs 0)) (hlv 0).2) C.U := fun c x hc => by
      have hc' : c < (C.D 0).B := by rw [hC]; exact hc
      rw [C.U_R hc' x, C.U_g hc', hC]; exact ⟨rfl, rfl⟩
    refine XpExt.trans h1 h2 ?_
    rw [xlW_B, xpOk_B (hlv 0).1 (xpF_ok H 0 (hlv 0))]
    exact veblen_zero_le_veblen_zero.2 (le_max_right _ _)
  · obtain ⟨k, hk⟩ := hcof ℓ'' h
    have h1 : XpExt (f ℓ'' h) (C.D k) := by
      rw [hC]; exact H.ext_le h (hlv k).2 (hk.le.trans (xpT_ge _)) hl'' (hlv k).1
    have h2 : XpExt (C.D k) C.U := fun c x hc => ⟨C.U_R hc x, C.U_g hc⟩
    have hB : (f ℓ'' h).B ≤ (C.D k).B := by
      rw [hC]; show (f ℓ'' h).B ≤ (f (xpT (cs k)) (hlv k).2).B
      rw [xpOk_B hl'' (H.1 ℓ'' h hl''), xpOk_B (hlv k).1 (H.1 _ (hlv k).2 (hlv k).1)]
      exact veblen_zero_le_veblen_zero.2 (hk.le.trans (xpT_ge _))
    exact XpExt.trans h1 h2 hB

/-! ## The `Ω₁`-family of bands -/

section Sq

variable {ℓ : Ordinal.{0}} (hℓ : XpLv ℓ) (hG1 : gcG 0 + Om1 < ℓ) {f : ∀ ℓ' : Ordinal.{0}, ℓ' < ℓ → HgVD}
  (H : XpCoh ℓ f) {s : Ordinal.{0} → Ordinal.{0}} (hs : xcA3.Seq1 ℓ s) (hML : ∀ μ, μ < Om1 → ML (s μ))

include hℓ hG1 hs hML in
theorem xpO_lv {μ : Ordinal.{0}} (hμ : μ < Om1) : XpLv (xpT (s μ)) ∧ xpT (s μ) < ℓ :=
  xpT_lv hℓ hG1 (hML μ hμ).2 (hs.1 μ hμ).2

/-- The member at `μ` (`Xl.xlW` outside `Ω₁`, never used). -/
noncomputable def xpOD (μ : Ordinal.{0}) : HgVD :=
  if hμ : μ < Om1 then f (xpT (s μ)) (xpO_lv hℓ hG1 hs hML hμ).2 else xlW

theorem xpOD_eq {μ : Ordinal.{0}} (hμ : μ < Om1) :
    xpOD hℓ hG1 hs hML (f := f) μ = f (xpT (s μ)) (xpO_lv hℓ hG1 hs hML hμ).2 := by
  unfold xpOD; rw [dif_pos hμ]

include H in
theorem xpOD_ok {μ : Ordinal.{0}} (hμ : μ < Om1) : XpOk (xpT (s μ)) (xpOD hℓ hG1 hs hML (f := f) μ) := by
  rw [xpOD_eq hℓ hG1 hs hML hμ]; exact H.1 _ _ (xpO_lv hℓ hG1 hs hML hμ).1

include H in
theorem xpOD_B {μ : Ordinal.{0}} (hμ : μ < Om1) : (xpOD hℓ hG1 hs hML (f := f) μ).B = veblen (xpT (s μ)) 0 :=
  xpOk_B (xpO_lv hℓ hG1 hs hML hμ).1 (xpOD_ok hℓ hG1 H hs hML hμ)

include hs in
theorem xpO_s_mono {μ' μ : Ordinal.{0}} (hle : μ' ≤ μ) (hμ : μ < Om1) : s μ' ≤ s μ := by
  rcases hle.lt_or_eq with h | rfl
  · exact (hs.2.1 μ' μ h hμ).le
  · exact le_rfl

include hs in
theorem xpO_g {x μ : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hg : xg ℓ < x) (hμ : μ < x) :
    xg (xpT (s μ)) < x := xpT_g_lt hx (hs.2.2.1 x hx hx1 hg μ hμ)

/-- **THE `Ω₁`-FAMILY OF BANDS** below a band level `ℓ` with an `Ω₁`-sequence of levels: bound `φ(ℓ, 0)`, gate
`xg ℓ`. -/
noncomputable def xpFamO : HoFam where
  D := xpOD hℓ hG1 hs hML (f := f)
  B := veblen ℓ 0
  γ := xg ℓ
  b := fun x => veblen (xcA3.R ℓ x) 0
  Zo := xpZ
  γ_lt := xcA3.g_lt ℓ hℓ.2.2
  γ_cl := fun _ hZ hZ1 h => xp_cl_g hℓ hZ hZ1 h
  G_lt := hℓ.1.trans_le (left_le_veblen _ 0)
  B_E := gg_veblen_eps (pos_iff_ne_zero.1 ((zero_le).trans_lt hℓ.1))
  B_lt1 := xp_B_lt1 hℓ
  B_fix1 := veblen_veblen_of_lt (xp_one_lt_lv hℓ) 0
  B_mem := fun S _ _ ha hb => CSet.phi_mem (xcA3.L_mem ℓ hℓ.2.2 S _ _ ha hb) (CSet.zero_mem _ _)
  DB_lt := fun μ hμ => by
    rw [xpOD_B hℓ hG1 H hs hML hμ]; exact veblen_zero_lt_veblen_zero.2 (xpO_lv hℓ hG1 hs hML hμ).2
  B_cof := fun c hc => by
    obtain ⟨a, ha, hca⟩ := wx_veb_lim_cof0 (xp_lv_lim hℓ) hc
    have hga : xg a < Om1 := xcA3.g_lt a (ha.trans hℓ.2.2)
    obtain ⟨μ, hμ, haμ⟩ := hs.2.2.2 (eN (xg a)) (eN_E _) (eN_lt_Om1K hga) a ha (lt_eN _)
    have hμ1 : μ < Om1 := hμ.trans (eN_lt_Om1K hga)
    refine ⟨μ, hμ1, ?_⟩
    rw [xpOD_B hℓ hG1 H hs hML hμ1]
    exact hca.trans (veblen_zero_lt_veblen_zero.2 (haμ.trans_le (xpT_ge _)))
  ext := fun μ' μ hle hμ c x hc => by
    have hμ'1 : μ' < Om1 := hle.trans_lt hμ
    rw [xpOD_eq hℓ hG1 hs hML hμ'1] at hc ⊢
    rw [xpOD_eq hℓ hG1 hs hML hμ]
    exact H.ext_le _ _ (xpT_mono (xpO_s_mono hs hle hμ)) (xpO_lv hℓ hG1 hs hML hμ'1).1
      (xpO_lv hℓ hG1 hs hML hμ).1 c x hc
  small := fun μ hμ c hc σ hσ hσ1 hg => by
    obtain ⟨b, hb, hgb, hcb⟩ := (xpOD_ok hℓ hG1 H hs hML hμ).sm c σ hc hσ hσ1 hg
    have hbl : b < ℓ := hb.trans_lt (xpO_lv hℓ hG1 hs hML hμ).2
    obtain ⟨μ', hμ', hbμ⟩ := hs.2.2.2 σ hσ hσ1 b hbl hgb
    have hμ'1 : μ' < Om1 := hμ'.trans hσ1
    refine ⟨μ', hμ', ?_⟩
    rw [xpOD_B hℓ hG1 H hs hML hμ'1]
    exact hcb.trans (veblen_zero_lt_veblen_zero.2 (hbμ.trans_le (xpT_ge _)))
  γD := fun x hx hx1 hg μ hμ =>
    (xpOk_γ (xpO_lv hℓ hG1 hs hML (hμ.trans hx1)).1 (xpOD_ok hℓ hG1 H hs hML (hμ.trans hx1))).trans_lt
      (xpO_g hs hx hx1 hg hμ)
  bD := fun x hx hx1 hg μ hμ => by
    have hμ1 : μ < Om1 := hμ.trans hx1
    rw [xpOk_b (xpO_lv hℓ hG1 hs hML hμ1).1 (xpOD_ok hℓ hG1 H hs hML hμ1) hx hx1 (xpO_g hs hx hx1 hg hμ)]
    exact veblen_zero_lt_veblen_zero.2 (xcA3.R_mono hx hx1 hℓ.2.2 (xpO_lv hℓ hG1 hs hML hμ1).2 hg
      (xpO_g hs hx hx1 hg hμ))
  ZD := fun x hx hx1 hg μ hμ => by
    have hμ1 : μ < Om1 := hμ.trans hx1
    rw [xpOk_Z (xpO_lv hℓ hG1 hs hML hμ1).1 (xpOD_ok hℓ hG1 H hs hML hμ1) hx hx1,
      if_pos (xpO_g hs hx hx1 hg hμ)]
    exact (hb_evZ_lt_fix2 (veblen_veblen_of_lt (xp_two_lt_R hℓ hx hx1 hg) 0)
      (veblen_zero_lt_veblen_zero.2 (xcA3.R_mono hx hx1 hℓ.2.2 (xpO_lv hℓ hG1 hs hML hμ1).2 hg
        (xpO_g hs hx hx1 hg hμ)))).le
  b_cof := fun x hx hx1 hg ν hν => by
    obtain ⟨a, ha, hνa⟩ := wx_veb_lim_cof0 (xp_R_lim (xpLv_lev hℓ) hx hx1 hg) hν
    obtain ⟨b, hb, hgb, hab⟩ := xcA3.R_cof hx hx1 hℓ.2.2 hg a ha
    obtain ⟨μ, hμ, hbμ⟩ := hs.2.2.2 x hx hx1 b hb hgb
    have hμ1 : μ < Om1 := hμ.trans hx1
    have hgt := xpO_g hs hx hx1 hg hμ
    refine ⟨μ, hμ, ?_⟩
    rw [xpOk_b (xpO_lv hℓ hG1 hs hML hμ1).1 (xpOD_ok hℓ hG1 H hs hML hμ1) hx hx1 hgt]
    exact hνa.trans_le (veblen_zero_le_veblen_zero.2 (hab.trans (xcA3.R_mono hx hx1
      (xpO_lv hℓ hG1 hs hML hμ1).1.2.2 (hbμ.trans_le (xpT_ge _)) hgt hgb).le))
  b_E := fun x hx hx1 hg => gg_veblen_eps (pos_iff_ne_zero.1 ((hx.pos).trans_le (xp_x_le_R hℓ hx hx1 hg)))
  x_lt_b := fun x hx hx1 hg => (xp_x_le_R hℓ hx hx1 hg).trans_lt (xp_R_nsc hℓ hx hx1 hg)
  b_fix1 := fun x hx hx1 hg => veblen_veblen_of_lt ((wo_one_lt_inE hx).trans_le (xp_x_le_R hℓ hx hx1 hg)) 0
  b_lt1 := fun x hx hx1 hg => (xp_RZ hℓ hx hx1 hg).trans (xpZ_G1 hx hx1)
  b_pi := fun _ _ hB hγ => xp_R_pi hℓ hB hγ
  Z_low := fun μ hμ x hx hx1 _ => by
    rw [xpOk_Z (xpO_lv hℓ hG1 hs hML hμ).1 (xpOD_ok hℓ hG1 H hs hML hμ) hx hx1]
    split_ifs with h
    · exact (hb_evZ_lt_fix2 (xpZ_fix x) (xp_RZ (xpO_lv hℓ hG1 hs hML hμ).1 hx hx1 h)).le
    · exact le_rfl
  Zo_fix := xpZ_fix
  Zo_G1 := fun _ hx hx1 => xpZ_G1 hx hx1

theorem xpFamO_U_b (x : Ordinal.{0}) :
    (hoOU (xpFamO hℓ hG1 H hs hML)).b x = veblen (xcA3.R ℓ x) 0 := rfl

theorem xpFamO_U_Z (x : Ordinal.{0}) : (hoOU (xpFamO hℓ hG1 H hs hML)).Z x =
    if xg ℓ < x then evZ (veblen (xcA3.R ℓ x) 0) else xpZ x := hoOU_Z _ x

end Sq

/-- **THE STEP AT A BAND LEVEL WITH AN `Ω₁`-SEQUENCE OF LEVELS.** -/
theorem xpStep_sq {ℓ : Ordinal.{0}} (hℓ : XpLv ℓ) (hG1 : gcG 0 + Om1 < ℓ) (hsq : XSq xcA3 ML ℓ) : XpStepAt ℓ := by
  intro f H
  obtain ⟨s, hs, hML⟩ := hsq
  obtain ⟨F, hF⟩ : ∃ F, F = xpFamO hℓ hG1 H hs hML := ⟨_, rfl⟩
  refine ⟨hoOU F, ⟨xpAt_of (by rw [hF]; rfl) (by rw [hF]; rfl) (by rw [hF]; rfl)
    (fun x _ _ _ => by rw [hF]; exact xpFamO_U_b hℓ hG1 H hs hML x)
    (fun x _ _ => by rw [hF]; exact xpFamO_U_Z hℓ hG1 H hs hML x),
    fun c σ hc hσ hσ1 hg => ?_, ?_⟩, fun ℓ'' h hl'' => ?_⟩
  · obtain ⟨μ, hμ, hk⟩ := F.B_cof c hc
    rw [hoOU_g F hμ hk] at hg
    have hk' : c < (xpOD hℓ hG1 hs hML (f := f) μ).B := by rw [hF] at hk; exact hk
    have hg' : (xpOD hℓ hG1 hs hML (f := f) μ).g c < σ := by rw [hF] at hg; exact hg
    obtain ⟨b, hb, hgb, hcb⟩ := (xpOD_ok hℓ hG1 H hs hML hμ).sm c σ hk' hσ hσ1 hg'
    exact ⟨b, hb.trans (xpO_lv hℓ hG1 hs hML hμ).2.le, hgb, hcb⟩
  · have h1 := (xpOD_ok hℓ hG1 H hs hML gv_Om1_pos).w
    have h2 : XpExt (xpOD hℓ hG1 hs hML (f := f) 0) (hoOU F) := fun c x hc => by
      have hc' : c < (F.D 0).B := by rw [hF]; exact hc
      rw [hoOU_R F gv_Om1_pos hc' x, hoOU_g F gv_Om1_pos hc', hF]; exact ⟨rfl, rfl⟩
    refine XpExt.trans h1 h2 ?_
    rw [xlW_B, xpOD_B hℓ hG1 H hs hML gv_Om1_pos]
    exact veblen_zero_le_veblen_zero.2 (le_max_right _ _)
  · have hg'' : xg ℓ'' < Om1 := xcA3.g_lt ℓ'' (h.trans hℓ.2.2)
    obtain ⟨μ, hμ, hlμ⟩ := hs.2.2.2 (eN (xg ℓ'')) (eN_E _) (eN_lt_Om1K hg'') ℓ'' h (lt_eN _)
    have hμ1 : μ < Om1 := hμ.trans (eN_lt_Om1K hg'')
    have hlv := xpO_lv hℓ hG1 hs hML hμ1
    have h1 : XpExt (f ℓ'' h) (F.D μ) := by
      rw [hF]; show XpExt (f ℓ'' h) (xpOD hℓ hG1 hs hML μ)
      rw [xpOD_eq hℓ hG1 hs hML hμ1]
      exact H.ext_le h hlv.2 (hlμ.le.trans (xpT_ge _)) hl'' hlv.1
    have h2 : XpExt (F.D μ) (hoOU F) := fun c x hc => ⟨hoOU_R F hμ1 hc x, hoOU_g F hμ1 hc⟩
    have hB : (f ℓ'' h).B ≤ (F.D μ).B := by
      rw [hF]; show (f ℓ'' h).B ≤ (xpOD hℓ hG1 hs hML μ).B
      rw [xpOk_B hl'' (H.1 ℓ'' h hl''), xpOD_B hℓ hG1 H hs hML hμ1]
      exact veblen_zero_le_veblen_zero.2 (hlμ.le.trans (xpT_ge _))
    exact XpExt.trans h1 h2 hB

end Googology.Trans.PoR.InaccPsi.R2.Xp
