import Googology.Trans.PoR.InaccPsi.R2.XuLim
import Googology.Trans.PoR.InaccPsi.R2.XpRec

/-!
# XuRec: ONE RECURSION OVER EVERY BAND LEVEL `G < ℓ < T` (port of `R2.XpRec`)

* `xuqStep_all` (**THE STEP AT EVERY (A3) BAND LEVEL**: `G + Ω₁` (`Xl.xlW`), successors `ℓ' + Ω₁` (`Xp.xuqW`), limits
  with an `ω`- or an `Ω₁`-sequence of levels (`Xc.xc_br`));
* `xuqSys` (well-founded recursion), `xuqFam` (**THE FAMILY**: at every (A3) band level `ℓ` a system at the bottom
  `φ(ℓ, 0)` with gate `≤ xuGg ℓ`, SMALL, extending `Xl.xlW` and every earlier member).

No new axiom.  New definitions: `xuqGs`, `xuqSys`.
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

/-- **THE STEP AT EVERY (A3) BAND LEVEL.** -/
theorem xuqStep_all : ∀ ℓ, XuqLv T ℓ → XuqStepAt hT ℓ := by
  intro ℓ hℓ
  by_cases hG1 : ℓ = gcG 0 + Om1
  · subst hG1; exact xuqStep_G1 hT
  by_cases hsucc : ∃ ℓ', XuqLv T ℓ' ∧ ℓ = ℓ' + Om1
  · obtain ⟨ℓ', hl', rfl⟩ := hsucc
    exact xuqStep_succ hT hl' hℓ.2.2
  have hG1' : gcG 0 + Om1 < ℓ := lt_of_le_of_ne (xuq_G1_le hℓ) (Ne.symm hG1)
  have hLv : XuLvC T ℓ := by
    refine ⟨gl_Om1_lt_G0.trans hℓ.1, hℓ.2.1, fun ⟨ℓ', hl', he⟩ => ?_⟩
    rcases lt_trichotomy ℓ' (gcG 0) with h | h | h
    · have : ℓ' + Om1 < gcG 0 := (inE_indec gl_G0_E).add_lt h gl_Om1_lt_G0
      exact absurd (he ▸ this) (not_lt.2 hℓ.1.le)
    · exact hG1 (he.trans (by rw [h]))
    · exact hsucc ⟨ℓ', ⟨h, hl'.2.1, hl'.2.2⟩, he⟩
  rcases (xu_br hT.E hT.t0_le hT.lt1 ℓ hℓ.2.2 (xuq_lv_lim hT hℓ)).2 hLv with hfs | hsq
  · exact xuqStep_fs hT hℓ hG1' hfs
  · exact xuqStep_sq hT hℓ hG1' hsq

open Classical in
/-- The recursion step of the family. -/
noncomputable def xuqGs (ℓ : Ordinal.{0}) (f : ∀ ℓ' : Ordinal.{0}, ℓ' < ℓ → HgVD) : HgVD :=
  if h : XuqLv T ℓ ∧ XuqCoh hT ℓ f then Classical.choose (xuqStep_all hT ℓ h.1 f h.2) else xlW

/-- **The family of the (A3) band systems**, by well-founded recursion. -/
noncomputable def xuqSys : Ordinal.{0} → HgVD := Ordinal.lt_wf.fix (xuqGs hT)

/-- **THE FAMILY**: at every (A3) band level `ℓ` (`G < ℓ < t₀`, `Ω₁ ∣ ℓ`) a system at the bottom `φ(ℓ, 0)` of the
datum `ℓ` (gate `≤ xuGg ℓ`, SMALL, extending `Xl.xlW`) that extends every earlier member. -/
theorem xuqFam : ∀ ℓ, XuqLv T ℓ → XuqOk hT ℓ (xuqSys hT ℓ) ∧ ∀ ℓ', ℓ' < ℓ → XuqLv T ℓ' → XuqExt (xuqSys hT ℓ') (xuqSys hT ℓ) := by
  intro ℓ
  induction ℓ using WellFoundedLT.induction with
  | _ ℓ ih =>
    intro hℓ
    have hcoh : XuqCoh hT ℓ (fun ℓ' _ => xuqSys hT ℓ') :=
      ⟨fun ℓ' h h' => (ih ℓ' h h').1, fun ℓ'' ℓ' _ h' hlt h1 h2 => (ih ℓ' h' h2).2 ℓ'' hlt h1⟩
    have heq : xuqSys hT ℓ = xuqGs hT ℓ (fun ℓ' _ => xuqSys hT ℓ') := Ordinal.lt_wf.fix_eq (xuqGs hT) ℓ
    have hsp := Classical.choose_spec (xuqStep_all hT ℓ hℓ (fun ℓ' _ => xuqSys hT ℓ') hcoh)
    have hG : xuqGs hT ℓ (fun ℓ' _ => xuqSys hT ℓ') = Classical.choose (xuqStep_all hT ℓ hℓ (fun ℓ' _ => xuqSys hT ℓ') hcoh) := by
      unfold xuqGs; rw [dif_pos ⟨hℓ, hcoh⟩]
    rw [heq, hG]
    exact ⟨hsp.1, fun ℓ' h h' => hsp.2 ℓ' h h'⟩



section Main

variable {ℓ : Ordinal.{0}} (hℓ : XuqLv T ℓ)
include hℓ

theorem xuqSys_ok : XuqOk hT ℓ (xuqSys hT ℓ) := (xuqFam hT ℓ hℓ).1

/-- **THE SYSTEM AT `φ(ℓ, 0)`** for every (A3) band level `ℓ`. -/
theorem xuqSys_B : (xuqSys hT ℓ).B = veblen ℓ 0 := xuqOk_B hT hℓ (xuqSys_ok hT hℓ)

theorem xuqSys_γ : (xuqSys hT ℓ).γ ≤ xuGg ℓ := xuqOk_γ hT hℓ (xuqSys_ok hT hℓ)

theorem xuqSys_at : XuqAt T ((xuCT hT).lv ℓ (xuqLv_lev hT hℓ)) 0 (xuqSys hT ℓ) := (xuqSys_ok hT hℓ).at_ _

theorem xuqSys_b {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hg : xuGg ℓ < x) :
    (xuqSys hT ℓ).b x = veblen ((xuCT hT).R ℓ x) 0 := xuqOk_b hT hℓ (xuqSys_ok hT hℓ) hx hx1 hg

/-- **It extends `Xl.xlW`, hence `Hg.hgU`.** -/
theorem xuqSys_hgU {c : Ordinal.{0}} (hc : c < hgU.B) (x : Ordinal.{0}) :
    (xuqSys hT ℓ).R c x = hgU.R c x ∧ (xuqSys hT ℓ).g c = hgU.g c := by
  obtain ⟨a1, b1⟩ := (xuqSys_ok hT hℓ).w c x (hc.trans xp_hgU_lt_W)
  obtain ⟨a2, b2⟩ := xlW_hgU hc x
  exact ⟨a1.trans a2, b1.trans b2⟩

/-- **Later members extend earlier ones.** -/
theorem xuqSys_ext {ℓ' : Ordinal.{0}} (h : ℓ' < ℓ) (hl' : XuqLv T ℓ') : XuqExt (xuqSys hT ℓ') (xuqSys hT ℓ) :=
  (xuqFam hT ℓ hℓ).2 ℓ' h hl'

end Main

end Googology.Trans.PoR.InaccPsi.R2.Xu
