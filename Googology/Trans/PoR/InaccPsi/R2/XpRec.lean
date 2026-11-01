import Googology.Trans.PoR.InaccPsi.R2.XpLim

/-!
# XpRec: ONE RECURSION OVER EVERY (A3) BAND LEVEL `G < ℓ < t₀`

* `xpStep_all` (**THE STEP AT EVERY (A3) BAND LEVEL**: `G + Ω₁` (`Xl.xlW`), successors `ℓ' + Ω₁` (`Xp.xpW`), limits
  with an `ω`- or an `Ω₁`-sequence of levels (`Xc.xc_br`));
* `xpSys` (well-founded recursion), `xpFam` (**THE FAMILY**: at every (A3) band level `ℓ` a system at the bottom
  `φ(ℓ, 0)` with gate `≤ xg ℓ`, SMALL, extending `Xl.xlW` and every earlier member).

No new axiom.  New definitions: `xpGs`, `xpSys`.
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

/-- **THE STEP AT EVERY (A3) BAND LEVEL.** -/
theorem xpStep_all : ∀ ℓ, XpLv ℓ → XpStepAt ℓ := by
  intro ℓ hℓ
  by_cases hG1 : ℓ = gcG 0 + Om1
  · subst hG1; exact xpStep_G1
  by_cases hsucc : ∃ ℓ', XpLv ℓ' ∧ ℓ = ℓ' + Om1
  · obtain ⟨ℓ', hl', rfl⟩ := hsucc
    exact xpStep_succ hl' hℓ.2.2
  have hG1' : gcG 0 + Om1 < ℓ := lt_of_le_of_ne (xp_G1_le hℓ) (Ne.symm hG1)
  have hLv : LvC3 ℓ := by
    refine ⟨gl_Om1_lt_G0.trans hℓ.1, hℓ.2.1, fun ⟨ℓ', hl', he⟩ => ?_⟩
    rcases lt_trichotomy ℓ' (gcG 0) with h | h | h
    · have : ℓ' + Om1 < gcG 0 := (inE_indec gl_G0_E).add_lt h gl_Om1_lt_G0
      exact absurd (he ▸ this) (not_lt.2 hℓ.1.le)
    · exact hG1 (he.trans (by rw [h]))
    · exact hsucc ⟨ℓ', ⟨h, hl'.2.1, hl'.2.2⟩, he⟩
  rcases (xc_br ℓ hℓ.2.2 (xp_lv_lim hℓ)).2 hLv with hfs | hsq
  · exact xpStep_fs hℓ hG1' hfs
  · exact xpStep_sq hℓ hG1' hsq

open Classical in
/-- The recursion step of the family. -/
noncomputable def xpGs (ℓ : Ordinal.{0}) (f : ∀ ℓ' : Ordinal.{0}, ℓ' < ℓ → HgVD) : HgVD :=
  if h : XpLv ℓ ∧ XpCoh ℓ f then Classical.choose (xpStep_all ℓ h.1 f h.2) else xlW

/-- **The family of the (A3) band systems**, by well-founded recursion. -/
noncomputable def xpSys : Ordinal.{0} → HgVD := Ordinal.lt_wf.fix xpGs

/-- **THE FAMILY**: at every (A3) band level `ℓ` (`G < ℓ < t₀`, `Ω₁ ∣ ℓ`) a system at the bottom `φ(ℓ, 0)` of the
datum `ℓ` (gate `≤ xg ℓ`, SMALL, extending `Xl.xlW`) that extends every earlier member. -/
theorem xpFam : ∀ ℓ, XpLv ℓ → XpOk ℓ (xpSys ℓ) ∧ ∀ ℓ', ℓ' < ℓ → XpLv ℓ' → XpExt (xpSys ℓ') (xpSys ℓ) := by
  intro ℓ
  induction ℓ using WellFoundedLT.induction with
  | _ ℓ ih =>
    intro hℓ
    have hcoh : XpCoh ℓ (fun ℓ' _ => xpSys ℓ') :=
      ⟨fun ℓ' h h' => (ih ℓ' h h').1, fun ℓ'' ℓ' _ h' hlt h1 h2 => (ih ℓ' h' h2).2 ℓ'' hlt h1⟩
    have heq : xpSys ℓ = xpGs ℓ (fun ℓ' _ => xpSys ℓ') := Ordinal.lt_wf.fix_eq xpGs ℓ
    have hsp := Classical.choose_spec (xpStep_all ℓ hℓ (fun ℓ' _ => xpSys ℓ') hcoh)
    have hG : xpGs ℓ (fun ℓ' _ => xpSys ℓ') = Classical.choose (xpStep_all ℓ hℓ (fun ℓ' _ => xpSys ℓ') hcoh) := by
      unfold xpGs; rw [dif_pos ⟨hℓ, hcoh⟩]
    rw [heq, hG]
    exact ⟨hsp.1, fun ℓ' h h' => hsp.2 ℓ' h h'⟩

/-- `φ(Ω₁, G + 1) < φ(G + Ω₁, 0)`. -/
theorem xp_hgU_lt_W : hgU.B < xlW.B := by
  rw [hgU_B, xlW_B]
  have hE : InE (veblen (gcG 0 + Om1) 0) := gg_veblen_eps xl_GOm_lim.bot_lt.ne'
  have hG : gcG 0 < veblen (gcG 0 + Om1) 0 :=
    (lt_add_of_pos_right _ gv_Om1_pos).trans_le (left_le_veblen _ 0)
  have h := (isNormal_veblen Om1).strictMono ((ev_isSuccLimit_of_inE hE).add_one_lt hG)
  rwa [veblen_veblen_of_lt (gl_Om1_lt_G0.trans_le le_self_add) 0] at h

section Main

variable {ℓ : Ordinal.{0}} (hℓ : XpLv ℓ)
include hℓ

theorem xpSys_ok : XpOk ℓ (xpSys ℓ) := (xpFam ℓ hℓ).1

/-- **THE SYSTEM AT `φ(ℓ, 0)`** for every (A3) band level `ℓ`. -/
theorem xpSys_B : (xpSys ℓ).B = veblen ℓ 0 := xpOk_B hℓ (xpSys_ok hℓ)

theorem xpSys_γ : (xpSys ℓ).γ ≤ xg ℓ := xpOk_γ hℓ (xpSys_ok hℓ)

theorem xpSys_at : XpAt (xcA3.lv ℓ (xpLv_lev hℓ)) 0 (xpSys ℓ) := (xpSys_ok hℓ).at_ _

theorem xpSys_b {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hg : xg ℓ < x) :
    (xpSys ℓ).b x = veblen (xcA3.R ℓ x) 0 := xpOk_b hℓ (xpSys_ok hℓ) hx hx1 hg

/-- **It extends `Xl.xlW`, hence `Hg.hgU`.** -/
theorem xpSys_hgU {c : Ordinal.{0}} (hc : c < hgU.B) (x : Ordinal.{0}) :
    (xpSys ℓ).R c x = hgU.R c x ∧ (xpSys ℓ).g c = hgU.g c := by
  obtain ⟨a1, b1⟩ := (xpSys_ok hℓ).w c x (hc.trans xp_hgU_lt_W)
  obtain ⟨a2, b2⟩ := xlW_hgU hc x
  exact ⟨a1.trans a2, b1.trans b2⟩

/-- **Later members extend earlier ones.** -/
theorem xpSys_ext {ℓ' : Ordinal.{0}} (h : ℓ' < ℓ) (hl' : XpLv ℓ') : XpExt (xpSys ℓ') (xpSys ℓ) :=
  (xpFam ℓ hℓ).2 ℓ' h hl'

end Main

end Googology.Trans.PoR.InaccPsi.R2.Xp
