import Googology.Trans.PoR.InaccPsi.R2.WsLim

/-!
# WsAll: THE FAMILY OVER RAW DATA FOR EVERY CODE INTERFACE, GIVEN ITS `Ω₁`-SEQUENCES

* `WsCls C L` (**THE CLASSIFICATION BELOW `L`**: every level `ℓ < L` that is not `Ω₁`, not a successor `ℓ' + Ω₁`, and
  has no `ω`-sequence `C.Fs`, has an `Ω₁`-sequence of levels `C.Fs1`) — pure code arithmetic, no systems;
* `wsStep_all` (**THE STEP AT EVERY LEVEL BELOW `L`** from `WsCls C L`: `Ω₁`, successors, `ω`-sequences, and the
  generic `Ω₁`-cofinal step `Ws.wsStep_om1`);
* `wsF`, `wsFam` (**THE FAMILY**: an entry at every level below `L`, each extending every earlier one over every
  datum);
* `wsSh_hgU` (`Hg.hgU` has the shape at `Ω₁` over `G`, for every `C`), `wsV` (**the system over `G` at `ℓ`**),
  `wsSysAll` (`B = φ(ℓ, G+1)`, gate `≤ g ℓ`).

No new axiom.  New definitions: `WsCls`, `wsGs`, `wsF`, `wsV`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ws

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
open Googology.Trans.PoR.InaccPsi.R2.Wo WsC

variable (C : WsC)

/-- **THE CLASSIFICATION OF THE LEVELS BELOW `L`**: the remaining levels have `Ω₁`-sequences of levels. -/
def WsCls (L : Ordinal.{0}) : Prop :=
  ∀ ℓ, C.Lev ℓ → ℓ < L → ℓ ≠ Om1 → (¬ ∃ ℓ', C.Lev ℓ' ∧ ℓ = ℓ' + Om1) → ¬ C.Fs ℓ → ∃ s, C.Fs1 ℓ s

variable {C}

/-- **THE STEP AT EVERY LEVEL BELOW `L`** given the classification below `L`. -/
theorem wsStep_all {L : Ordinal.{0}} (hc : WsCls C L) : ∀ ℓ, C.Lev ℓ → ℓ < L → WsStepAt C ℓ := by
  intro ℓ hℓ hL
  by_cases h1 : ℓ = Om1
  · subst h1; exact wsStep_base
  by_cases h2 : ∃ ℓ', C.Lev ℓ' ∧ ℓ = ℓ' + Om1
  · obtain ⟨ℓ', hℓ', rfl⟩ := h2; exact wsStep_succ hℓ' hℓ.2.2
  by_cases h3 : C.Fs ℓ
  · exact wsStep_fs hℓ h3
  obtain ⟨s, hs⟩ := hc ℓ hℓ hL h1 h2 h3
  exact wsStep_om1 hs

/-- The recursion step of the family below `L`. -/
noncomputable def wsGs {L : Ordinal.{0}} (hc : WsCls C L) (ℓ : Ordinal.{0}) (f : ∀ ℓ' : Ordinal.{0}, ℓ' < ℓ → WoE) :
    WoE := by
  classical
  exact if h : C.Lev ℓ ∧ ℓ < L ∧ WsCoh C ℓ f then Classical.choose (wsStep_all hc ℓ h.1 h.2.1 f h.2.2)
    else fun _ S1 => S1

/-- **The family below `L`**, by well-founded recursion. -/
noncomputable def wsF {L : Ordinal.{0}} (hc : WsCls C L) : Ordinal.{0} → WoE := Ordinal.lt_wf.fix (wsGs hc)

/-- **THE FAMILY**: an entry at every level below `L`, each extending every earlier one over every datum. -/
theorem wsFam {L : Ordinal.{0}} (hc : WsCls C L) : ∀ ℓ, C.Lev ℓ → ℓ < L →
    WsSpec C ℓ (wsF hc ℓ) ∧ ∀ ℓ', ℓ' < ℓ → C.Lev ℓ' → WsExt C ℓ (wsF hc ℓ') (wsF hc ℓ) := by
  intro ℓ
  induction ℓ using WellFoundedLT.induction with
  | _ ℓ ih =>
    intro hℓ hL
    have hcoh : WsCoh C ℓ (fun ℓ' _ => wsF hc ℓ') :=
      ⟨fun ℓ' h h' => (ih ℓ' h h' (h.trans hL)).1,
        fun ℓ'' ℓ' _ h' hlt h1 h2 => (ih ℓ' h' h2 (h'.trans hL)).2 ℓ'' hlt h1⟩
    have heq : wsF hc ℓ = wsGs hc ℓ (fun ℓ' _ => wsF hc ℓ') := Ordinal.lt_wf.fix_eq (wsGs hc) ℓ
    have hsp := Classical.choose_spec (wsStep_all hc ℓ hℓ hL (fun ℓ' _ => wsF hc ℓ') hcoh)
    have hG : wsGs hc ℓ (fun ℓ' _ => wsF hc ℓ') =
        Classical.choose (wsStep_all hc ℓ hℓ hL (fun ℓ' _ => wsF hc ℓ') hcoh) := by
      unfold wsGs; rw [dif_pos ⟨hℓ, hL, hcoh⟩]
    rw [heq, hG]
    exact ⟨hsp.1, fun ℓ' h h' => hsp.2 ℓ' h h'⟩

/-! ## The systems over `G` -/

/-- **`Hg.hgU` has the shape at `Ω₁` over `G`** (for every code interface). -/
theorem wsSh_hgU : WsSh C (wsG C) Om1 hgU := by
  obtain ⟨sB, sγ, sb, sZ, shi⟩ := whU_shape
  have hγ0 : hgU.γ = 0 := hgU_γ
  refine ⟨?_, ⟨by rw [hγ0]; exact le_rfl, by rw [hγ0]; exact zero_le⟩, fun x hx _ => ?_, fun x hx hx1 hk => ?_,
    fun x hx hx1 => ?_, fun c σ h1 h2 hσ hσ1 h3 => shi c σ h1 h2 hσ hσ1 h3⟩
  · rw [sB]; show veblen (Om1 + 0) (gcG 0 + 1) = hdNx Om1 (gcG 0)
    rw [add_zero, hdNx_fixP (ws_G_fix (lev_Om1 (C := C)))]
  · rw [hγ0]
    exact ⟨fun _ => (cut1 hx).2 hx.pos, fun _ => hx.pos⟩
  · rw [sb x hx hx1 (by show max hnL1.g 0 < x; rw [wh_hnL1_g, max_self]; exact hx.pos)]
    show veblen (x + 0) (lgG x + 1) = hdNx (C.R Om1 x) (lgG x)
    rw [add_zero, C.R_Om1 x,
      hdNx_fixP (hjG_fix hx hx1 (one_lt_inE hx).le (wh_eN_lt_lgG hx hx1 |>.trans' (lt_eN x)))]
  · have hA : max (whGW hnL1 wh_hnL1_NB).γR 0 < x := by
      show max hnL1.g 0 < x; rw [wh_hnL1_g, max_self]; exact hx.pos
    have hB : max (wsG C).γ (C.g Om1) < x := (cut1 hx).2 (show (0 : Ordinal.{0}) < x from hx.pos)
    rw [sZ x hx hx1, if_pos hA, if_pos hB]
    show evZ (veblen (x + 0) (lgG x + 1)) = evZ (hdNx (C.R Om1 x) (lgG x))
    rw [add_zero, C.R_Om1 x,
      hdNx_fixP (hjG_fix hx hx1 (one_lt_inE hx).le (wh_eN_lt_lgG hx hx1 |>.trans' (lt_eN x)))]

/-- **THE SYSTEM OVER `G` AT THE LEVEL `ℓ`.** -/
noncomputable def wsV {L : Ordinal.{0}} (hc : WsCls C L) (ℓ : Ordinal.{0}) : HgVD := wsF hc ℓ (wsG C) hgU

theorem wsV_sh {L ℓ : Ordinal.{0}} (hc : WsCls C L) (hℓ : C.Lev ℓ) (hL : ℓ < L) : WsSh C (wsG C) ℓ (wsV hc ℓ) :=
  ((wsFam hc ℓ hℓ hL).1 (wsG C) hgU (wsGood_G hℓ) wsSh_hgU).1

theorem wsV_B {L ℓ : Ordinal.{0}} (hc : WsCls C L) (hℓ : C.Lev ℓ) (hL : ℓ < L) :
    (wsV hc ℓ).B = veblen ℓ (gcG 0 + 1) := by
  rw [(wsV_sh hc hℓ hL).1]; exact hdNx_fixP (ws_G_fix hℓ)

theorem wsV_γ {L ℓ : Ordinal.{0}} (hc : WsCls C L) (hℓ : C.Lev ℓ) (hL : ℓ < L) : (wsV hc ℓ).γ ≤ C.g ℓ := by
  have := (wsV_sh hc hℓ hL).2.1.2
  rwa [show max (wsG C).γ (C.g ℓ) = C.g ℓ from max_eq_right zero_le] at this

/-- **THE SYSTEMS OVER `G` AT EVERY LEVEL BELOW `L`** given the classification below `L`. -/
theorem wsSysAll {L : Ordinal.{0}} (hc : WsCls C L) :
    ∀ ℓ, C.Lev ℓ → ℓ < L → ∃ V : HgVD, V.B = veblen ℓ (gcG 0 + 1) ∧ V.γ ≤ C.g ℓ := fun ℓ hℓ hL =>
  ⟨wsV hc ℓ, wsV_B hc hℓ hL, wsV_γ hc hℓ hL⟩

/-- A classification below `L` holds below every `L' ≤ L`. -/
theorem wsCls_mono {L L' : Ordinal.{0}} (h : WsCls C L) (hle : L' ≤ L) : WsCls C L' :=
  fun ℓ hℓ hL => h ℓ hℓ (hL.trans_le hle)

end Googology.Trans.PoR.InaccPsi.R2.Ws
