import Googology.Trans.PoR.InaccPsi.R2.WoLimO

/-!
# WoA1: THE FAMILY OVER RAW DATA AT EVERY LEVEL BELOW `ε_{Ω₁+1}`; REGION A1 WITH NO HYPOTHESIS

* `woStep_all` (**THE STEP AT EVERY LEVEL `Ω₁ ≤ ℓ < ε_{Ω₁+1}`, `Ω₁ ∣ ℓ`**: `Ω₁`, successors, `ω`-sequences, and the
  levels of cofinality `Ω₁` through `Wo.wo_fs1` and `Wo.woStep_om1` — no remaining case);
* `woF`, `woFam` (**THE FAMILY**: an entry at every level, each extending every earlier one over every datum);
* `woSh_hgU` (`Hg.hgU` has the shape at `Ω₁` over `G`), `woV ℓ` (**the system over `G` at `ℓ`**), `woSysAll`,
  `woSysA1` (**REGION A1: every `B < φ(ε_{Ω₁+1}, G+1)` is `≤` the bound of a system over `G` with gate below `K`**,
  UNCONDITIONAL);
* `woEnt ℓ` (the package `Wo.woPkOf` and the system `woV ℓ`), `woEnt_at` (**every entry is a `Wh.WhAt` entry**),
  `woEnt_ext` (**every pair extends in the corrected sense `Wm.WmExtE`**), so the skeleton's `skFam` holds with no
  hypothesis (`woSkFam`: `Wh.WhAt` and the old extension; `woSkFamW2`: `Wh.WhAt` and `Wm.WmExtE`).

No new axiom.  New definitions: `woG0`, `woF`, `woV`, `woEnt`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Wo

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

/-- **THE STEP AT EVERY LEVEL**, with no hypothesis. -/
theorem woStep_all : ∀ ℓ, WmLev ℓ → WoStepAt ℓ := by
  intro ℓ hℓ
  by_cases h1 : ℓ = Om1
  · subst h1; exact woStep_base
  by_cases h2 : ∃ ℓ', WmLev ℓ' ∧ ℓ = ℓ' + Om1
  · obtain ⟨ℓ', hℓ', rfl⟩ := h2; exact woStep_succ hℓ' hℓ.2.2
  by_cases h3 : WmFs ℓ
  · exact woStep_fs hℓ h3
  obtain ⟨s, hs⟩ := wo_fs1 hℓ h1 h2 h3
  exact woStep_om1 hs

/-- The default entry. -/
def woG0 : WoE := fun _ S1 => S1

open Classical in
/-- The recursion step of the family. -/
noncomputable def woGs (ℓ : Ordinal.{0}) (f : ∀ ℓ' : Ordinal.{0}, ℓ' < ℓ → WoE) : WoE :=
  if h : WmLev ℓ ∧ WoCoh ℓ f then Classical.choose (woStep_all ℓ h.1 f h.2) else woG0

/-- **The family**, by well-founded recursion. -/
noncomputable def woF : Ordinal.{0} → WoE := Ordinal.lt_wf.fix woGs

/-- **THE FAMILY**: an entry at every level, each extending every earlier one over every datum. -/
theorem woFam : ∀ ℓ, WmLev ℓ → WoSpec ℓ (woF ℓ) ∧ ∀ ℓ', ℓ' < ℓ → WmLev ℓ' → WoExt ℓ (woF ℓ') (woF ℓ) := by
  intro ℓ
  induction ℓ using WellFoundedLT.induction with
  | _ ℓ ih =>
    intro hℓ
    have hcoh : WoCoh ℓ (fun ℓ' _ => woF ℓ') :=
      ⟨fun ℓ' h h' => (ih ℓ' h h').1, fun ℓ'' ℓ' _ h' hlt h1 h2 => (ih ℓ' h' h2).2 ℓ'' hlt h1⟩
    have heq : woF ℓ = woGs ℓ (fun ℓ' _ => woF ℓ') := Ordinal.lt_wf.fix_eq woGs ℓ
    have hsp := Classical.choose_spec (woStep_all ℓ hℓ (fun ℓ' _ => woF ℓ') hcoh)
    have hG : woGs ℓ (fun ℓ' _ => woF ℓ') = Classical.choose (woStep_all ℓ hℓ (fun ℓ' _ => woF ℓ') hcoh) := by
      unfold woGs; rw [dif_pos ⟨hℓ, hcoh⟩]
    rw [heq, hG]
    exact ⟨hsp.1, fun ℓ' h h' => hsp.2 ℓ' h h'⟩

/-! ## The systems over `G` -/

/-- **`Hg.hgU` has the shape at `Ω₁` over `G`.** -/
theorem woSh_hgU : WoSh woG Om1 hgU := by
  obtain ⟨sB, sγ, sb, sZ, shi⟩ := whU_shape
  have hγ0 : hgU.γ = 0 := hgU_γ
  refine ⟨?_, ⟨by rw [hγ0]; exact le_rfl, by rw [hγ0]; exact zero_le⟩, fun x hx _ => ?_, fun x hx hx1 hk => ?_,
    fun x hx hx1 => ?_, fun c σ h1 h2 hσ hσ1 h3 => shi c σ h1 h2 hσ hσ1 h3⟩
  · rw [sB]; show veblen (Om1 + 0) (gcG 0 + 1) = hdNx Om1 (gcG 0)
    rw [add_zero, hdNx_fixP (wo_G_fix wo_lev_Om1)]
  · rw [hγ0]
    exact ⟨fun _ => (wo_cut1 hx).2 hx.pos, fun _ => hx.pos⟩
  · rw [sb x hx hx1 (by show max hnL1.g 0 < x; rw [wh_hnL1_g, max_self]; exact hx.pos)]
    show veblen (x + 0) (lgG x + 1) = hdNx (rdc Om1 x) (lgG x)
    rw [add_zero, (rdc_Om1 x).1, hdNx_fixP (hjG_fix hx hx1 (wo_one_lt_inE hx).le (wh_eN_lt_lgG hx hx1 |>.trans' (lt_eN x)))]
  · have hA : max (whGW hnL1 wh_hnL1_NB).γR 0 < x := by
      show max hnL1.g 0 < x; rw [wh_hnL1_g, max_self]; exact hx.pos
    have hB : max woG.γ (gtc Om1) < x := (wo_cut1 hx).2 (show (0 : Ordinal.{0}) < x from hx.pos)
    rw [sZ x hx hx1, if_pos hA, if_pos hB]
    show evZ (veblen (x + 0) (lgG x + 1)) = evZ (hdNx (rdc Om1 x) (lgG x))
    rw [add_zero, (rdc_Om1 x).1, hdNx_fixP (hjG_fix hx hx1 (wo_one_lt_inE hx).le (wh_eN_lt_lgG hx hx1 |>.trans' (lt_eN x)))]

/-- **THE SYSTEM OVER `G` AT THE LEVEL `ℓ`.** -/
noncomputable def woV (ℓ : Ordinal.{0}) : HgVD := woF ℓ woG hgU

theorem woV_sh {ℓ : Ordinal.{0}} (hℓ : WmLev ℓ) : WoSh woG ℓ (woV ℓ) :=
  ((woFam ℓ hℓ).1 woG hgU (woGood_G hℓ) woSh_hgU).1

theorem woV_B {ℓ : Ordinal.{0}} (hℓ : WmLev ℓ) : (woV ℓ).B = veblen ℓ (gcG 0 + 1) := by
  rw [(woV_sh hℓ).1]; exact hdNx_fixP (wo_G_fix hℓ)

theorem woV_γ {ℓ : Ordinal.{0}} (hℓ : WmLev ℓ) : (woV ℓ).γ ≤ gtc ℓ := by
  have := (woV_sh hℓ).2.1.2; rwa [show max woG.γ (gtc ℓ) = gtc ℓ from max_eq_right zero_le] at this

/-- **THE SYSTEMS OVER `G` AT EVERY LEVEL BELOW `ε_{Ω₁+1}`**, with no hypothesis. -/
theorem woSysAll : ∀ ℓ, WmLev ℓ → ∃ V : HgVD, V.B = veblen ℓ (gcG 0 + 1) ∧ V.γ ≤ gtc ℓ := fun ℓ hℓ =>
  ⟨woV ℓ, woV_B hℓ, woV_γ hℓ⟩

/-- **REGION A1, UNCONDITIONAL**: every `B < φ(ε_{Ω₁+1}, G+1)` is `≤` the bound of a system over `G` whose gate
is below `K`. -/
theorem woSysA1 (S : InaccSeq.{0}) : ∀ B, B < veblen gfE (gcG 0 + 1) →
    ∃ V : HgVD, B ≤ V.B ∧ V.γ < Td.tdK S := by
  intro B hB
  obtain ⟨ℓ, hℓ, hg, hBl⟩ := whCofLev S B hB
  exact ⟨woV ℓ, (woV_B hℓ) ▸ hBl, (woV_γ hℓ).trans_lt hg⟩

end Googology.Trans.PoR.InaccPsi.R2.Wo
