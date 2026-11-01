import Googology.Trans.PoR.InaccPsi.R2.XuLv
import Googology.Trans.PoR.InaccPsi.R2.XpLim

/-!
# XuLim: THE STEP AT A LIMIT BAND BELOW A BOUND `T` (`ω`- AND `Ω₁`-SEQUENCES OF BANDS; port of `R2.XpLim`)

At a band level `ℓ` that is not a successor `ℓ' + Ω₁`, the (A3) classification `Xc.xcCls` gives an `ω`-sequence or
an `Ω₁`-sequence of levels below `ℓ` (`Xc.xc_br`).  The members are the systems of the coherent family at
`t(c) = max(c, G + Ω₁)`.

* `xuq_lv_lim`, `xuq_R_lim` (**the reading of a limit code is a limit**), `xuqOk_b`, `xuqOk_Z`;
* `xuqChL` (**THE `ω`-CHAIN OF BANDS**, bound `φ(ℓ, 0)`, gate `xuGg ℓ`), `xuqStep_fs`;
* `xuqFamO` (**THE `Ω₁`-FAMILY OF BANDS**: `Ho.HoFam`, SMALL from the level form `XuqSm` of the members and the
  fourth field of `Ws.WsC.Seq1`), `xuqStep_sq`.

No new axiom.  New definitions: `xuqT`, `xuqChL`, `xuqFamO`.
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

open Googology.Trans.PoR.InaccPsi.R2.Xp

namespace Googology.Trans.PoR.InaccPsi.R2.Xu

variable {T : Ordinal.{0}} (hT : XuT T)
include hT

/-! ## Limits and readings -/

theorem xuq_lv_lim {ℓ : Ordinal.{0}} (h : XuqLv T ℓ) : IsSuccLimit ℓ := by
  obtain ⟨k, hk⟩ := h.2.1
  have hk0 : 0 < k := by
    rcases eq_or_ne k 0 with h0 | h0
    · rw [h0, mul_zero] at hk; exact absurd (hk ▸ h.1) (not_lt.2 zero_le)
    · exact pos_iff_ne_zero.2 h0
  rw [hk]; exact isSuccLimit_mul_left gl_Om1_lim hk0

/-- **The reading of a limit level is a limit.** -/
theorem xuq_R_lim {ℓ x : Ordinal.{0}} (h : (xuCT hT).Lev ℓ) (hx : InE x) (hx1 : x < Om1) (hg : xuGg ℓ < x) :
    IsSuccLimit ((xuCT hT).R ℓ x) := by
  have hne : (xuCT hT).R ℓ x ≠ 0 := WsC.R_ne0 (C := (xuCT hT)) hx hx1 h.1 h.2.2 hg
  rcases zero_or_succ_or_isSuccLimit ((xuCT hT).R ℓ x) with h0 | ⟨a, ha⟩ | hl
  · exact absurd h0 hne
  · exfalso
    have ha' : a < (xuCT hT).R ℓ x := by rw [← ha]; exact Order.lt_succ a
    obtain ⟨b, hb, hgb, hab⟩ := (xuCT hT).R_cof hx hx1 h.2.2 hg a ha'
    have hb1 : b + 1 < ℓ := (xuCT hT).lev_lim h hb
    have h2 := WsC.R_succ_lt (C := (xuCT hT)) hx hx1 h.2.2 hb1 hg hgb
    rw [← ha, Order.succ_eq_add_one] at h2
    exact absurd (hab.trans_lt ((lt_add_one _).trans_le (Order.lt_add_one_iff.1 h2))) (lt_irrefl _)
  · exact hl

section Ok

variable {ℓ : Ordinal.{0}} (hℓ : XuqLv T ℓ) {V : HgVD} (hV : XuqOk hT ℓ V)
include hℓ hV

theorem xuqOk_b {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hg : xuGg ℓ < x) :
    V.b x = veblen ((xuCT hT).R ℓ x) 0 := by
  rw [(hV.at_ (xuqLv_lev hT hℓ)).b x hx hx1 (by rw [max_eq_right zero_le]; exact hg), add_zero]
  exact congrArg (fun a => veblen a 0) ((xuCT hT).lv_l (xuqLv_lev hT hℓ) hx hx1 hg)

theorem xuqOk_Z {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    V.Z x = if xuGg ℓ < x then evZ (veblen ((xuCT hT).R ℓ x) 0) else xuqZ T x := by
  have e : ((xuCT hT).lv ℓ (xuqLv_lev hT hℓ)).g = xuGg ℓ := rfl
  rw [(hV.at_ (xuqLv_lev hT hℓ)).Z x hx hx1, max_eq_right zero_le, e]
  by_cases hg : xuGg ℓ < x
  · rw [if_pos hg, if_pos hg, add_zero]
    exact congrArg (fun a => evZ (veblen a 0)) ((xuCT hT).lv_l (xuqLv_lev hT hℓ) hx hx1 hg)
  · rw [if_neg hg, if_neg hg]

end Ok

/-- `φ(R ℓ x, 0)` below the low field. -/
theorem xuq_RZ {ℓ x : Ordinal.{0}} (hℓ : XuqLv T ℓ) (hx : InE x) (hx1 : x < Om1) (hg : xuGg ℓ < x) :
    veblen ((xuCT hT).R ℓ x) 0 < xuqZ T x := by
  have h := xuq_veb_lt_Z hT (xuqBdOf hT ℓ hℓ) hx hx1 hg hx.pos
  rw [add_zero] at h
  rwa [show (xuqBdOf hT ℓ hℓ).K.Λ.l x = (xuCT hT).R ℓ x from (xuCT hT).lv_l (xuqLv_lev hT hℓ) hx hx1 hg] at h

theorem xuq_R_nsc {ℓ x : Ordinal.{0}} (hℓ : XuqLv T ℓ) (hx : InE x) (hx1 : x < Om1) (hg : xuGg ℓ < x) :
    (xuCT hT).R ℓ x < veblen ((xuCT hT).R ℓ x) 0 := by
  have h := (xuqBdOf hT ℓ hℓ).l_nsc x hx hx1 hg
  rwa [show (xuqBdOf hT ℓ hℓ).K.Λ.l x = (xuCT hT).R ℓ x from (xuCT hT).lv_l (xuqLv_lev hT hℓ) hx hx1 hg] at h

theorem xuq_x_le_R {ℓ x : Ordinal.{0}} (hℓ : XuqLv T ℓ) (hx : InE x) (hx1 : x < Om1) (hg : xuGg ℓ < x) :
    x ≤ (xuCT hT).R ℓ x := (xuCT hT).le_R hx hx1 (xuqLv_lev hT hℓ).1 hℓ.2.2 hg

/-- **Lemma EXACT for `φ(R ℓ x, 0)`.** -/
theorem xuq_R_pi {ℓ σ ρ : Ordinal.{0}} (hℓ : XuqLv T ℓ) (hB : Bases σ ρ) (hγ : xuGg ℓ < σ) :
    veblen ((xuCT hT).R ℓ ρ) 0 ∈ TB ρ σ ∧ pi σ ρ (veblen ((xuCT hT).R ℓ ρ) 0) = veblen ((xuCT hT).R ℓ σ) 0 := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  have h0σ : (0 : Ordinal.{0}) < σ := hB.1.pos
  have h := hnv_glA_pi (xuqBdOf hT ℓ hℓ).K.Λ (ν := 0) hB hγ h0σ (mem_TB_of_lt hB h0σ) (gm1_facts hB.2.1 hρ1).2.2.2.pos
  rw [pi_lt hB h0σ, xp_glA (xuqBdOf hT ℓ hℓ).toXpBd0 hB.2.1 hρ1 (hγ.trans hB.2.2.1) hB.2.1.pos 0 (hcN_E _ _).pos,
    xp_glA (xuqBdOf hT ℓ hℓ).toXpBd0 hB.1 hσ1 hγ h0σ 0 (hcN_E _ _).pos, add_zero, add_zero,
    show (xuqBdOf hT ℓ hℓ).K.Λ.l ρ = (xuCT hT).R ℓ ρ from (xuCT hT).lv_l (xuqLv_lev hT hℓ) hB.2.1 hρ1 (hγ.trans hB.2.2.1),
    show (xuqBdOf hT ℓ hℓ).K.Λ.l σ = (xuCT hT).R ℓ σ from (xuCT hT).lv_l (xuqLv_lev hT hℓ) hB.1 hσ1 hγ] at h
  exact h

/-- **A code over `Z` of `φ(ℓ, 0)` has the gate of `ℓ` below `Z`.** -/
theorem xuq_cl_g {ℓ Z : Ordinal.{0}} (hℓ : XuqLv T ℓ) (hZ : SC Z) (hZ1 : Z ≤ Om 1) (h : GxCl Z {gcG 0} (veblen ℓ 0)) :
    xuGg ℓ < Z := by
  have hGQ : gcG 0 < veblen ((xuqBdOf hT ℓ hℓ).K.Λ.L + 0) 0 := by
    rw [add_zero]; exact hℓ.1.trans_le (left_le_veblen _ 0)
  have hs : veblen ((xuqBdOf hT ℓ hℓ).K.Λ.L + 0) 0 < veblen ((xuqBdOf hT ℓ hℓ).K.Λ.L + 0) (0 + 1) :=
    (isNormal_veblen _).strictMono (show (0 : Ordinal.{0}) < 0 + 1 by rw [zero_add]; exact zero_lt_one)
  have h' : GxCl Z {gcG 0} (veblen ((xuqBdOf hT ℓ hℓ).K.Λ.L + 0) 0) := by rw [add_zero]; exact h
  exact hnv_cl_g (xuqBdOf hT ℓ hℓ).K.Λ gv_Om1_pos hZ hZ1 veblen_pos hGQ h' le_rfl hs

theorem xuq_B_lt1 {ℓ : Ordinal.{0}} (hℓ : XuqLv T ℓ) : veblen ℓ 0 < gcG 1 := by
  have h := (isNormal_veblen ℓ).strictMono (gcG_SC 1).1
  rwa [gn_veb_fix (gcG_SC 1) (hℓ.2.2.trans hT.lt1)] at h

/-! ## The members `t(c) = max(c, G + Ω₁)` -/

/-- **The member level**: `max(c, G + Ω₁)`. -/
noncomputable def xuqT (c : Ordinal.{0}) : Ordinal.{0} := max c (gcG 0 + Om1)

theorem xuqT_lv {ℓ c : Ordinal.{0}} (hℓ : XuqLv T ℓ) (hG1 : gcG 0 + Om1 < ℓ) (hc : Om1 ∣ c) (hcl : c < ℓ) :
    XuqLv T (xuqT c) ∧ xuqT c < ℓ := by
  have hlt : xuqT c < ℓ := max_lt hcl hG1
  refine ⟨⟨(lt_add_of_pos_right _ gv_Om1_pos).trans_le (le_max_right _ _), ?_, hlt.trans hℓ.2.2⟩, hlt⟩
  unfold xuqT
  rcases le_total c (gcG 0 + Om1) with h | h
  · rw [max_eq_right h]; exact (xuq_lev_G1 hT).2.1
  · rw [max_eq_left h]; exact hc

theorem xuqT_g_lt {c x : Ordinal.{0}} (hx : InE x) (hg : xuGg c < x) : xuGg (xuqT c) < x := by
  unfold xuqT
  rcases le_total c (gcG 0 + Om1) with h | h
  · rw [max_eq_right h]; exact xuq_xgG1_lt hx
  · rw [max_eq_left h]; exact hg

theorem xuqT_g_le {c ℓ : Ordinal.{0}} (hg : xuGg c ≤ xuGg ℓ) : xuGg (xuqT c) ≤ xuGg ℓ := by
  unfold xuqT
  rcases le_total c (gcG 0 + Om1) with h | h
  · rw [max_eq_right h, xuq_xg_G1]; exact xu_one_le_gg ℓ
  · rw [max_eq_left h]; exact hg

theorem xuqT_ge (c : Ordinal.{0}) : c ≤ xuqT c := le_max_left _ _

theorem xuqT_mono {c d : Ordinal.{0}} (h : c ≤ d) : xuqT c ≤ xuqT d := max_le_max h le_rfl

/-! ## A system at the bottom of a datum from its fields -/

/-- **A system with bound and index `φ(ℓ, 0)`, gate `xuGg ℓ`, base reading `φ(R ℓ x, 0)` and bound field
`ζ(φ(R ℓ x, 0))` is a system at the bottom of the datum `ℓ`.** -/
theorem xuqAt_of {ℓ : Ordinal.{0}} {V : HgVD} (hB : V.B = veblen ℓ 0) (hix : V.ix = veblen ℓ 0) (hγ : V.γ = xuGg ℓ)
    (hb : ∀ x, InE x → x < Om1 → xuGg ℓ < x → V.b x = veblen ((xuCT hT).R ℓ x) 0)
    (hZ : ∀ x, InE x → x < Om1 → V.Z x = if xuGg ℓ < x then evZ (veblen ((xuCT hT).R ℓ x) 0) else xuqZ T x) :
    ∀ h : (xuCT hT).Lev ℓ, XuqAt T ((xuCT hT).lv ℓ h) 0 V := fun h => by
  have e : ((xuCT hT).lv ℓ h).g = xuGg ℓ := rfl
  have eL : ((xuCT hT).lv ℓ h).L = ℓ := rfl
  refine ⟨by rw [hB, eL, add_zero], by rw [hix, eL, add_zero], fun x _ _ => by rw [hγ, e, max_eq_right zero_le],
    fun x hx hx1 hg => ?_, by rw [hγ, e, max_eq_right zero_le], fun x hx hx1 => ?_⟩
  · rw [e, max_eq_right zero_le] at hg
    rw [hb x hx hx1 hg, add_zero, (xuCT hT).lv_l h hx hx1 hg]
  · rw [hZ x hx hx1, e, max_eq_right zero_le]
    by_cases hg : xuGg ℓ < x
    · rw [if_pos hg, if_pos hg, add_zero, (xuCT hT).lv_l h hx hx1 hg]
    · rw [if_neg hg, if_neg hg]

theorem xuq_one_lt_lv {ℓ : Ordinal.{0}} (hℓ : XuqLv T ℓ) : (1 : Ordinal.{0}) < ℓ := xf_one_lt_G.trans hℓ.1

theorem xuq_two_lt_R {ℓ x : Ordinal.{0}} (hℓ : XuqLv T ℓ) (hx : InE x) (hx1 : x < Om1) (hg : xuGg ℓ < x) :
    (2 : Ordinal.{0}) < (xuCT hT).R ℓ x :=
  ((show (2 : Ordinal.{0}) < ω from (by exact_mod_cast natCast_lt_omega0 2)).trans (omega0_lt_inE hx)).trans_le
    (xuq_x_le_R hT hℓ hx hx1 hg)

/-! ## The `ω`-chain of bands -/

section Fs

variable {ℓ : Ordinal.{0}} (hℓ : XuqLv T ℓ) (hG1 : gcG 0 + Om1 < ℓ) {f : ∀ ℓ' : Ordinal.{0}, ℓ' < ℓ → HgVD}
  (H : XuqCoh hT ℓ f) {cs : ℕ → Ordinal.{0}} (hML : ∀ k, ML (cs k)) (hmono : ∀ k, cs k < cs (k + 1))
  (hlt : ∀ k, cs k < ℓ) (hcof : ∀ t, t < ℓ → ∃ k, t < cs k) (hgk : ∀ k, xuGg (cs k) ≤ xuGg ℓ)

include hℓ hG1 hML hlt in
theorem xuqF_lv (k : ℕ) : XuqLv T (xuqT (cs k)) ∧ xuqT (cs k) < ℓ := xuqT_lv hT hℓ hG1 (hML k).2 (hlt k)

include H in
theorem xuqF_ok (k : ℕ) (hk : XuqLv T (xuqT (cs k)) ∧ xuqT (cs k) < ℓ) : XuqOk hT (xuqT (cs k)) (f (xuqT (cs k)) hk.2) :=
  H.1 _ hk.2 hk.1

/-- **THE `ω`-CHAIN OF BANDS** below a limit band level `ℓ`: bound `φ(ℓ, 0)`, gate `xuGg ℓ`. -/
noncomputable def xuqChL : HgfCh where
  D := fun k => f (xuqT (cs k)) (xuqF_lv hT hℓ hG1 hML hlt k).2
  B := veblen ℓ 0
  b := fun x => veblen ((xuCT hT).R ℓ x) 0
  γ := xuGg ℓ
  Zo := xuqZ T
  γ_lt := (xuCT hT).g_lt ℓ hℓ.2.2
  γ0 := fun k => (xuqOk_γ hT (xuqF_lv hT hℓ hG1 hML hlt k).1 (xuqF_ok hT H k (xuqF_lv hT hℓ hG1 hML hlt k))).trans (xuqT_g_le hT (hgk k))
  γ_cl := fun _ hZ hZ1 h => xuq_cl_g hT hℓ hZ hZ1 h
  B_mono := fun k => by
    rw [xuqOk_B hT (xuqF_lv hT hℓ hG1 hML hlt k).1 (xuqF_ok hT H k (xuqF_lv hT hℓ hG1 hML hlt k)),
      xuqOk_B hT (xuqF_lv hT hℓ hG1 hML hlt (k + 1)).1 (xuqF_ok hT H (k + 1) (xuqF_lv hT hℓ hG1 hML hlt (k + 1)))]
    exact veblen_zero_le_veblen_zero.2 (xuqT_mono hT (hmono k).le)
  B_lt := fun k => by
    rw [xuqOk_B hT (xuqF_lv hT hℓ hG1 hML hlt k).1 (xuqF_ok hT H k (xuqF_lv hT hℓ hG1 hML hlt k))]
    exact veblen_zero_lt_veblen_zero.2 (xuqF_lv hT hℓ hG1 hML hlt k).2
  B_cof := fun c hc => by
    obtain ⟨a, ha, hca⟩ := wx_veb_lim_cof0 (xuq_lv_lim hT hℓ) hc
    obtain ⟨k, hk⟩ := hcof a ha
    refine ⟨k, ?_⟩
    rw [xuqOk_B hT (xuqF_lv hT hℓ hG1 hML hlt k).1 (xuqF_ok hT H k (xuqF_lv hT hℓ hG1 hML hlt k))]
    exact hca.trans_le (veblen_zero_le_veblen_zero.2 (hk.le.trans (xuqT_ge hT _)))
  R_ext := fun k c x hc => (H.ext_le _ _ (xuqT_mono hT (hmono k).le) (xuqF_lv hT hℓ hG1 hML hlt k).1
    (xuqF_lv hT hℓ hG1 hML hlt (k + 1)).1 c x hc).1
  g_ext := fun k c hc => (H.ext_le _ _ (xuqT_mono hT (hmono k).le) (xuqF_lv hT hℓ hG1 hML hlt k).1
    (xuqF_lv hT hℓ hG1 hML hlt (k + 1)).1 c 0 hc).2
  B_lt1 := xuq_B_lt1 hT hℓ
  B_fix := veblen_veblen_of_lt (xuq_one_lt_lv hT hℓ) 0
  B_mem := fun S _ _ ha hb => CSet.phi_mem ((xuCT hT).L_mem ℓ hℓ.2.2 S _ _ ha hb) (CSet.zero_mem _ _)
  b_ge := fun k x hx hx1 hγ => by
    have hgk' : xuGg (xuqT (cs k)) < x := (xuqT_g_le hT (hgk k)).trans_lt hγ
    rw [xuqOk_b hT (xuqF_lv hT hℓ hG1 hML hlt k).1 (xuqF_ok hT H k (xuqF_lv hT hℓ hG1 hML hlt k)) hx hx1 hgk']
    exact (veblen_zero_lt_veblen_zero.2
      ((xuCT hT).R_mono hx hx1 hℓ.2.2 (xuqF_lv hT hℓ hG1 hML hlt k).2 hγ hgk')).le
  b_cof := fun x hx hx1 hγ ν hν => by
    obtain ⟨a, ha, hνa⟩ := wx_veb_lim_cof0 (xuq_R_lim hT (xuqLv_lev hT hℓ) hx hx1 hγ) hν
    obtain ⟨b, hb, hgb, hab⟩ := (xuCT hT).R_cof hx hx1 hℓ.2.2 hγ a ha
    obtain ⟨k, hk⟩ := hcof b hb
    have hgk' : xuGg (xuqT (cs k)) < x := (xuqT_g_le hT (hgk k)).trans_lt hγ
    refine ⟨k, ?_⟩
    rw [xuqOk_b hT (xuqF_lv hT hℓ hG1 hML hlt k).1 (xuqF_ok hT H k (xuqF_lv hT hℓ hG1 hML hlt k)) hx hx1 hgk']
    exact hνa.trans_le (veblen_zero_le_veblen_zero.2 (hab.trans ((xuCT hT).R_mono hx hx1
      (xuqF_lv hT hℓ hG1 hML hlt k).1.2.2 (hk.trans_le (xuqT_ge hT _)) hgk' hgb).le))
  b_fix := fun x hx hx1 hγ => veblen_veblen_of_lt ((wo_one_lt_inE hx).trans_le (xuq_x_le_R hT hℓ hx hx1 hγ)) 0
  b_gt := fun x hx hx1 hγ => (xuq_x_le_R hT hℓ hx hx1 hγ).trans_lt (xuq_R_nsc hT hℓ hx hx1 hγ)
  b_lt := fun x hx hx1 hγ => (xuq_RZ hT hℓ hx hx1 hγ).trans (xuqZ_G1 hT hx hx1)
  b_pi := fun _ _ hB hγ => xuq_R_pi hT hℓ hB hγ
  Z_low := fun k x hx hx1 _ => by
    rw [xuqOk_Z hT (xuqF_lv hT hℓ hG1 hML hlt k).1 (xuqF_ok hT H k (xuqF_lv hT hℓ hG1 hML hlt k)) hx hx1]
    split_ifs with h
    · exact (hb_evZ_lt_fix2 (xuqZ_fix T x) (xuq_RZ hT (xuqF_lv hT hℓ hG1 hML hlt k).1 hx hx1 h)).le
    · exact le_rfl
  Zo_fix := xuqZ_fix1 T
  Zo_G1 := fun _ hx hx1 => xuqZ_G1 hT hx hx1

theorem xuqChL_U_b (x : Ordinal.{0}) :
    (xuqChL hT hℓ hG1 H hML hmono hlt hcof hgk).U.b x = veblen ((xuCT hT).R ℓ x) 0 := rfl

theorem xuqChL_U_Z (x : Ordinal.{0}) : (xuqChL hT hℓ hG1 H hML hmono hlt hcof hgk).U.Z x =
    if xuGg ℓ < x then evZ (veblen ((xuCT hT).R ℓ x) 0) else xuqZ T x := (xuqChL hT hℓ hG1 H hML hmono hlt hcof hgk).U_Z x

end Fs

/-- **THE STEP AT A BAND LEVEL WITH AN `ω`-SEQUENCE OF LEVELS.** -/
theorem xuqStep_fs {ℓ : Ordinal.{0}} (hℓ : XuqLv T ℓ) (hG1 : gcG 0 + Om1 < ℓ) (hfs : XFs (xuCT hT) ML ℓ) : XuqStepAt hT ℓ := by
  intro f H
  obtain ⟨cs, hML, hmono, hlt, hcof, hgk⟩ := hfs
  obtain ⟨C, hC⟩ : ∃ C, C = xuqChL hT hℓ hG1 H hML hmono hlt hcof hgk := ⟨_, rfl⟩
  have hlv := xuqF_lv hT hℓ hG1 hML hlt (cs := cs)
  refine ⟨C.U, ⟨xuqAt_of hT (by rw [hC]; rfl) (by rw [hC]; rfl) (by rw [hC]; rfl)
    (fun x _ _ _ => by rw [hC]; exact xuqChL_U_b hT hℓ hG1 H hML hmono hlt hcof hgk x)
    (fun x _ _ => by rw [hC]; exact xuqChL_U_Z hT hℓ hG1 H hML hmono hlt hcof hgk x),
    fun c σ hc hσ hσ1 hg => ?_, ?_⟩, fun ℓ'' h hl'' => ?_⟩
  · obtain ⟨k, hk⟩ := C.B_cof c hc
    rw [C.U_g hk] at hg
    have hk' : c < (f (xuqT (cs k)) (hlv k).2).B := by rw [hC] at hk; exact hk
    have hg' : (f (xuqT (cs k)) (hlv k).2).g c < σ := by rw [hC] at hg; exact hg
    obtain ⟨b, hb, hgb, hcb⟩ := (xuqF_ok hT H k (hlv k)).sm c σ hk' hσ hσ1 hg'
    exact ⟨b, hb.trans (hlv k).2.le, hgb, hcb⟩
  · have h1 := (xuqF_ok hT H 0 (hlv 0)).w
    have h2 : XuqExt (f (xuqT (cs 0)) (hlv 0).2) C.U := fun c x hc => by
      have hc' : c < (C.D 0).B := by rw [hC]; exact hc
      rw [C.U_R hc' x, C.U_g hc', hC]; exact ⟨rfl, rfl⟩
    refine XuqExt.trans h1 h2 ?_
    rw [xlW_B, xuqOk_B hT (hlv 0).1 (xuqF_ok hT H 0 (hlv 0))]
    exact veblen_zero_le_veblen_zero.2 (le_max_right _ _)
  · obtain ⟨k, hk⟩ := hcof ℓ'' h
    have h1 : XuqExt (f ℓ'' h) (C.D k) := by
      rw [hC]; exact H.ext_le h (hlv k).2 (hk.le.trans (xuqT_ge hT _)) hl'' (hlv k).1
    have h2 : XuqExt (C.D k) C.U := fun c x hc => ⟨C.U_R hc x, C.U_g hc⟩
    have hB : (f ℓ'' h).B ≤ (C.D k).B := by
      rw [hC]; show (f ℓ'' h).B ≤ (f (xuqT (cs k)) (hlv k).2).B
      rw [xuqOk_B hT hl'' (H.1 ℓ'' h hl''), xuqOk_B hT (hlv k).1 (H.1 _ (hlv k).2 (hlv k).1)]
      exact veblen_zero_le_veblen_zero.2 (hk.le.trans (xuqT_ge hT _))
    exact XuqExt.trans h1 h2 hB

/-! ## The `Ω₁`-family of bands -/

section Sq

variable {ℓ : Ordinal.{0}} (hℓ : XuqLv T ℓ) (hG1 : gcG 0 + Om1 < ℓ) {f : ∀ ℓ' : Ordinal.{0}, ℓ' < ℓ → HgVD}
  (H : XuqCoh hT ℓ f) {s : Ordinal.{0} → Ordinal.{0}} (hs : (xuCT hT).Seq1 ℓ s) (hML : ∀ μ, μ < Om1 → ML (s μ))

include hℓ hG1 hs hML in
theorem xuqO_lv {μ : Ordinal.{0}} (hμ : μ < Om1) : XuqLv T (xuqT (s μ)) ∧ xuqT (s μ) < ℓ :=
  xuqT_lv hT hℓ hG1 (hML μ hμ).2 (hs.1 μ hμ).2

/-- The member at `μ` (`Xl.xlW` outside `Ω₁`, never used). -/
noncomputable def xuqOD (μ : Ordinal.{0}) : HgVD :=
  if hμ : μ < Om1 then f (xuqT (s μ)) (xuqO_lv hT hℓ hG1 hs hML hμ).2 else xlW

theorem xuqOD_eq {μ : Ordinal.{0}} (hμ : μ < Om1) :
    xuqOD hT hℓ hG1 hs hML (f := f) μ = f (xuqT (s μ)) (xuqO_lv hT hℓ hG1 hs hML hμ).2 := by
  unfold xuqOD; rw [dif_pos hμ]

include H in
theorem xuqOD_ok {μ : Ordinal.{0}} (hμ : μ < Om1) : XuqOk hT (xuqT (s μ)) (xuqOD hT hℓ hG1 hs hML (f := f) μ) := by
  rw [xuqOD_eq hT hℓ hG1 hs hML hμ]; exact H.1 _ _ (xuqO_lv hT hℓ hG1 hs hML hμ).1

include H in
theorem xuqOD_B {μ : Ordinal.{0}} (hμ : μ < Om1) : (xuqOD hT hℓ hG1 hs hML (f := f) μ).B = veblen (xuqT (s μ)) 0 :=
  xuqOk_B hT (xuqO_lv hT hℓ hG1 hs hML hμ).1 (xuqOD_ok hT hℓ hG1 H hs hML hμ)

include hs in
theorem xuqO_s_mono {μ' μ : Ordinal.{0}} (hle : μ' ≤ μ) (hμ : μ < Om1) : s μ' ≤ s μ := by
  rcases hle.lt_or_eq with h | rfl
  · exact (hs.2.1 μ' μ h hμ).le
  · exact le_rfl

include hs in
theorem xuqO_g {x μ : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hg : xuGg ℓ < x) (hμ : μ < x) :
    xuGg (xuqT (s μ)) < x := xuqT_g_lt hT hx (hs.2.2.1 x hx hx1 hg μ hμ)

/-- **THE `Ω₁`-FAMILY OF BANDS** below a band level `ℓ` with an `Ω₁`-sequence of levels: bound `φ(ℓ, 0)`, gate
`xuGg ℓ`. -/
noncomputable def xuqFamO : HoFam where
  D := xuqOD hT hℓ hG1 hs hML (f := f)
  B := veblen ℓ 0
  γ := xuGg ℓ
  b := fun x => veblen ((xuCT hT).R ℓ x) 0
  Zo := xuqZ T
  γ_lt := (xuCT hT).g_lt ℓ hℓ.2.2
  γ_cl := fun _ hZ hZ1 h => xuq_cl_g hT hℓ hZ hZ1 h
  G_lt := hℓ.1.trans_le (left_le_veblen _ 0)
  B_E := gg_veblen_eps (pos_iff_ne_zero.1 ((zero_le).trans_lt hℓ.1))
  B_lt1 := xuq_B_lt1 hT hℓ
  B_fix1 := veblen_veblen_of_lt (xuq_one_lt_lv hT hℓ) 0
  B_mem := fun S _ _ ha hb => CSet.phi_mem ((xuCT hT).L_mem ℓ hℓ.2.2 S _ _ ha hb) (CSet.zero_mem _ _)
  DB_lt := fun μ hμ => by
    rw [xuqOD_B hT hℓ hG1 H hs hML hμ]; exact veblen_zero_lt_veblen_zero.2 (xuqO_lv hT hℓ hG1 hs hML hμ).2
  B_cof := fun c hc => by
    obtain ⟨a, ha, hca⟩ := wx_veb_lim_cof0 (xuq_lv_lim hT hℓ) hc
    have hga : xuGg a < Om1 := (xuCT hT).g_lt a (ha.trans hℓ.2.2)
    obtain ⟨μ, hμ, haμ⟩ := hs.2.2.2 (eN (xuGg a)) (eN_E _) (eN_lt_Om1K hga) a ha (lt_eN _)
    have hμ1 : μ < Om1 := hμ.trans (eN_lt_Om1K hga)
    refine ⟨μ, hμ1, ?_⟩
    rw [xuqOD_B hT hℓ hG1 H hs hML hμ1]
    exact hca.trans (veblen_zero_lt_veblen_zero.2 (haμ.trans_le (xuqT_ge hT _)))
  ext := fun μ' μ hle hμ c x hc => by
    have hμ'1 : μ' < Om1 := hle.trans_lt hμ
    rw [xuqOD_eq hT hℓ hG1 hs hML hμ'1] at hc ⊢
    rw [xuqOD_eq hT hℓ hG1 hs hML hμ]
    exact H.ext_le _ _ (xuqT_mono hT (xuqO_s_mono hT hs hle hμ)) (xuqO_lv hT hℓ hG1 hs hML hμ'1).1
      (xuqO_lv hT hℓ hG1 hs hML hμ).1 c x hc
  small := fun μ hμ c hc σ hσ hσ1 hg => by
    obtain ⟨b, hb, hgb, hcb⟩ := (xuqOD_ok hT hℓ hG1 H hs hML hμ).sm c σ hc hσ hσ1 hg
    have hbl : b < ℓ := hb.trans_lt (xuqO_lv hT hℓ hG1 hs hML hμ).2
    obtain ⟨μ', hμ', hbμ⟩ := hs.2.2.2 σ hσ hσ1 b hbl hgb
    have hμ'1 : μ' < Om1 := hμ'.trans hσ1
    refine ⟨μ', hμ', ?_⟩
    rw [xuqOD_B hT hℓ hG1 H hs hML hμ'1]
    exact hcb.trans (veblen_zero_lt_veblen_zero.2 (hbμ.trans_le (xuqT_ge hT _)))
  γD := fun x hx hx1 hg μ hμ =>
    (xuqOk_γ hT (xuqO_lv hT hℓ hG1 hs hML (hμ.trans hx1)).1 (xuqOD_ok hT hℓ hG1 H hs hML (hμ.trans hx1))).trans_lt
      (xuqO_g hT hs hx hx1 hg hμ)
  bD := fun x hx hx1 hg μ hμ => by
    have hμ1 : μ < Om1 := hμ.trans hx1
    rw [xuqOk_b hT (xuqO_lv hT hℓ hG1 hs hML hμ1).1 (xuqOD_ok hT hℓ hG1 H hs hML hμ1) hx hx1 (xuqO_g hT hs hx hx1 hg hμ)]
    exact veblen_zero_lt_veblen_zero.2 ((xuCT hT).R_mono hx hx1 hℓ.2.2 (xuqO_lv hT hℓ hG1 hs hML hμ1).2 hg
      (xuqO_g hT hs hx hx1 hg hμ))
  ZD := fun x hx hx1 hg μ hμ => by
    have hμ1 : μ < Om1 := hμ.trans hx1
    rw [xuqOk_Z hT (xuqO_lv hT hℓ hG1 hs hML hμ1).1 (xuqOD_ok hT hℓ hG1 H hs hML hμ1) hx hx1,
      if_pos (xuqO_g hT hs hx hx1 hg hμ)]
    exact (hb_evZ_lt_fix2 (veblen_veblen_of_lt (xuq_two_lt_R hT hℓ hx hx1 hg) 0)
      (veblen_zero_lt_veblen_zero.2 ((xuCT hT).R_mono hx hx1 hℓ.2.2 (xuqO_lv hT hℓ hG1 hs hML hμ1).2 hg
        (xuqO_g hT hs hx hx1 hg hμ)))).le
  b_cof := fun x hx hx1 hg ν hν => by
    obtain ⟨a, ha, hνa⟩ := wx_veb_lim_cof0 (xuq_R_lim hT (xuqLv_lev hT hℓ) hx hx1 hg) hν
    obtain ⟨b, hb, hgb, hab⟩ := (xuCT hT).R_cof hx hx1 hℓ.2.2 hg a ha
    obtain ⟨μ, hμ, hbμ⟩ := hs.2.2.2 x hx hx1 b hb hgb
    have hμ1 : μ < Om1 := hμ.trans hx1
    have hgt := xuqO_g hT hs hx hx1 hg hμ
    refine ⟨μ, hμ, ?_⟩
    rw [xuqOk_b hT (xuqO_lv hT hℓ hG1 hs hML hμ1).1 (xuqOD_ok hT hℓ hG1 H hs hML hμ1) hx hx1 hgt]
    exact hνa.trans_le (veblen_zero_le_veblen_zero.2 (hab.trans ((xuCT hT).R_mono hx hx1
      (xuqO_lv hT hℓ hG1 hs hML hμ1).1.2.2 (hbμ.trans_le (xuqT_ge hT _)) hgt hgb).le))
  b_E := fun x hx hx1 hg => gg_veblen_eps (pos_iff_ne_zero.1 ((hx.pos).trans_le (xuq_x_le_R hT hℓ hx hx1 hg)))
  x_lt_b := fun x hx hx1 hg => (xuq_x_le_R hT hℓ hx hx1 hg).trans_lt (xuq_R_nsc hT hℓ hx hx1 hg)
  b_fix1 := fun x hx hx1 hg => veblen_veblen_of_lt ((wo_one_lt_inE hx).trans_le (xuq_x_le_R hT hℓ hx hx1 hg)) 0
  b_lt1 := fun x hx hx1 hg => (xuq_RZ hT hℓ hx hx1 hg).trans (xuqZ_G1 hT hx hx1)
  b_pi := fun _ _ hB hγ => xuq_R_pi hT hℓ hB hγ
  Z_low := fun μ hμ x hx hx1 _ => by
    rw [xuqOk_Z hT (xuqO_lv hT hℓ hG1 hs hML hμ).1 (xuqOD_ok hT hℓ hG1 H hs hML hμ) hx hx1]
    split_ifs with h
    · exact (hb_evZ_lt_fix2 (xuqZ_fix T x) (xuq_RZ hT (xuqO_lv hT hℓ hG1 hs hML hμ).1 hx hx1 h)).le
    · exact le_rfl
  Zo_fix := xuqZ_fix T
  Zo_G1 := fun _ hx hx1 => xuqZ_G1 hT hx hx1

theorem xuqFamO_U_b (x : Ordinal.{0}) :
    (hoOU (xuqFamO hT hℓ hG1 H hs hML)).b x = veblen ((xuCT hT).R ℓ x) 0 := rfl

theorem xuqFamO_U_Z (x : Ordinal.{0}) : (hoOU (xuqFamO hT hℓ hG1 H hs hML)).Z x =
    if xuGg ℓ < x then evZ (veblen ((xuCT hT).R ℓ x) 0) else xuqZ T x := hoOU_Z _ x

end Sq

/-- **THE STEP AT A BAND LEVEL WITH AN `Ω₁`-SEQUENCE OF LEVELS.** -/
theorem xuqStep_sq {ℓ : Ordinal.{0}} (hℓ : XuqLv T ℓ) (hG1 : gcG 0 + Om1 < ℓ) (hsq : XSq (xuCT hT) ML ℓ) : XuqStepAt hT ℓ := by
  intro f H
  obtain ⟨s, hs, hML⟩ := hsq
  obtain ⟨F, hF⟩ : ∃ F, F = xuqFamO hT hℓ hG1 H hs hML := ⟨_, rfl⟩
  refine ⟨hoOU F, ⟨xuqAt_of hT (by rw [hF]; rfl) (by rw [hF]; rfl) (by rw [hF]; rfl)
    (fun x _ _ _ => by rw [hF]; exact xuqFamO_U_b hT hℓ hG1 H hs hML x)
    (fun x _ _ => by rw [hF]; exact xuqFamO_U_Z hT hℓ hG1 H hs hML x),
    fun c σ hc hσ hσ1 hg => ?_, ?_⟩, fun ℓ'' h hl'' => ?_⟩
  · obtain ⟨μ, hμ, hk⟩ := F.B_cof c hc
    rw [hoOU_g F hμ hk] at hg
    have hk' : c < (xuqOD hT hℓ hG1 hs hML (f := f) μ).B := by rw [hF] at hk; exact hk
    have hg' : (xuqOD hT hℓ hG1 hs hML (f := f) μ).g c < σ := by rw [hF] at hg; exact hg
    obtain ⟨b, hb, hgb, hcb⟩ := (xuqOD_ok hT hℓ hG1 H hs hML hμ).sm c σ hk' hσ hσ1 hg'
    exact ⟨b, hb.trans (xuqO_lv hT hℓ hG1 hs hML hμ).2.le, hgb, hcb⟩
  · have h1 := (xuqOD_ok hT hℓ hG1 H hs hML gv_Om1_pos).w
    have h2 : XuqExt (xuqOD hT hℓ hG1 hs hML (f := f) 0) (hoOU F) := fun c x hc => by
      have hc' : c < (F.D 0).B := by rw [hF]; exact hc
      rw [hoOU_R F gv_Om1_pos hc' x, hoOU_g F gv_Om1_pos hc', hF]; exact ⟨rfl, rfl⟩
    refine XuqExt.trans h1 h2 ?_
    rw [xlW_B, xuqOD_B hT hℓ hG1 H hs hML gv_Om1_pos]
    exact veblen_zero_le_veblen_zero.2 (le_max_right _ _)
  · have hg'' : xuGg ℓ'' < Om1 := (xuCT hT).g_lt ℓ'' (h.trans hℓ.2.2)
    obtain ⟨μ, hμ, hlμ⟩ := hs.2.2.2 (eN (xuGg ℓ'')) (eN_E _) (eN_lt_Om1K hg'') ℓ'' h (lt_eN _)
    have hμ1 : μ < Om1 := hμ.trans (eN_lt_Om1K hg'')
    have hlv := xuqO_lv hT hℓ hG1 hs hML hμ1
    have h1 : XuqExt (f ℓ'' h) (F.D μ) := by
      rw [hF]; show XuqExt (f ℓ'' h) (xuqOD hT hℓ hG1 hs hML μ)
      rw [xuqOD_eq hT hℓ hG1 hs hML hμ1]
      exact H.ext_le h hlv.2 (hlμ.le.trans (xuqT_ge hT _)) hl'' hlv.1
    have h2 : XuqExt (F.D μ) (hoOU F) := fun c x hc => ⟨hoOU_R F hμ1 hc x, hoOU_g F hμ1 hc⟩
    have hB : (f ℓ'' h).B ≤ (F.D μ).B := by
      rw [hF]; show (f ℓ'' h).B ≤ (xuqOD hT hℓ hG1 hs hML μ).B
      rw [xuqOk_B hT hl'' (H.1 ℓ'' h hl''), xuqOD_B hT hℓ hG1 H hs hML hμ1]
      exact veblen_zero_le_veblen_zero.2 (hlμ.le.trans (xuqT_ge hT _))
    exact XuqExt.trans h1 h2 hB

end Googology.Trans.PoR.InaccPsi.R2.Xu
