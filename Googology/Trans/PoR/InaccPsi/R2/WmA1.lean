import Googology.Trans.PoR.InaccPsi.R2.WmStep

/-!
# WmA1: REGION A1 OF THE FRONTIER FROM THE REMAINING CASE, AND THE GATE DROP

* `wm_old_vacuous` (**the old extension `Hn.HnkExt K' K` holds for every pair with `K.g < K'.g`**: it says nothing
  across a gate drop), `wm_gate_drop` (**a gate drop between levels**: `Ω₁·ω < Ω₁²` but `gtc (Ω₁²) = 2 < ω =
  gtc (Ω₁·ω)`);
* `wmSysA1` (**REGION A1 GIVEN THE REMAINING CASE**: from `Wm.WmOm1Step ε_{Ω₁+1}`, every `B < φ(ε_{Ω₁+1}, G+1)` is
  `≤` the bound of a system over `G` with gate below `K`), `wmSysSq` (**the same below `φ(Ω₁², G+1)`, with no
  hypothesis**).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Wm

open Googology.Trans.PoR.InaccPsi.R2.Wh Googology.Trans.PoR.InaccPsi.R2.Ho
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

/-- **The old extension is vacuous across a gate drop**: `K.g < K'.g ⇒ Hn.HnkExt K' K`. -/
theorem wm_old_vacuous {K' K : HnPk} (h : K.Λ.g < K'.Λ.g) : HnkExt K' K := fun hg => absurd hg (not_le.2 h)

theorem wm_omega_lt_Om1 : ω < (Om1 : Ordinal.{0}) := omega0_lt_inE gl_Om1_E

/-- **A GATE DROP BETWEEN TWO LEVELS**: `Ω₁·ω < Ω₁·Ω₁` (both levels) and `gtc (Ω₁·Ω₁) = 2 < ω = gtc (Ω₁·ω)`. -/
theorem wm_gate_drop : WmLev (Om1 * ω) ∧ WmLev (Om1 * Om1) ∧ Om1 * ω < Om1 * Om1 ∧
    gtc (Om1 * Om1) = 2 ∧ gtc (Om1 * ω) = ω := by
  have h2O : (2 : Ordinal.{0}) < Om1 := (natCast_lt_omega0 2).trans wm_omega_lt_Om1
  have h1W : (1 : Ordinal.{0}) < gfE := gf_one_lt_Om1.trans Om1_lt_eW
  have h2W : (2 : Ordinal.{0}) < gfE := h2O.trans Om1_lt_eW
  have hωW : Om1 * ω < gfE := eW_E.mul_lt Om1_lt_eW (wm_omega_lt_Om1.trans Om1_lt_eW)
  have hOW : Om1 * Om1 < gfE := eW_E.mul_lt Om1_lt_eW Om1_lt_eW
  have hlt : Om1 * ω < Om1 * Om1 := mul_lt_mul_of_pos_left wm_omega_lt_Om1 wh_Om1_pos
  refine ⟨⟨le_mul_of_one_le_right' (one_le_iff_pos.2 omega0_pos), dvd_mul_right _ _, hωW⟩,
    ⟨le_mul_of_one_le_right' (one_le_iff_pos.2 wh_Om1_pos), dvd_mul_right _ _, hOW⟩, hlt, ?_, ?_⟩
  · have h := wm_gtc_term (e := 2) (d := 1) h2W one_ne_zero gf_one_lt_Om1
    rw [mul_one, ← wm_sq_eq, (rdc_const h2O 0).2] at h
    rw [h]; exact max_eq_left (by exact_mod_cast (show (1 : ℕ) ≤ 2 by norm_num))
  · have h := wm_gtc_term (e := 1) (d := ω) h1W omega0_ne_zero wm_omega_lt_Om1
    rw [opow_one, (rdc_const gf_one_lt_Om1 0).2] at h
    rw [h]; exact max_eq_right (one_le_iff_pos.2 omega0_pos)

/-- **REGION A1 GIVEN THE REMAINING CASE**: every `B < φ(ε_{Ω₁+1}, G+1)` is `≤` the bound of a system over `G` whose
gate is below `K`. -/
theorem wmSysA1 (S : InaccSeq.{0}) (hOm : WmOm1Step gfE) : ∀ B, B < veblen gfE (gcG 0 + 1) →
    ∃ V : HgVD, B ≤ V.B ∧ V.γ < Td.tdK S := by
  intro B hB
  obtain ⟨ℓ, hℓ, hg, hBl⟩ := whCofLev S B hB
  obtain ⟨V, hVB, hVg⟩ := wmSysAll hOm ℓ hℓ hℓ.2.2
  exact ⟨V, hVB ▸ hBl, hVg.trans_lt hg⟩

/-- **THE SYSTEMS AT EVERY LEVEL BELOW `Ω₁²`, WITH NO HYPOTHESIS** (`B = φ(ℓ, G+1)`, gate `≤ gtc ℓ`). -/
theorem wmSysSq : ∀ ℓ, WmLev ℓ → ℓ < Om1 * Om1 → ∃ V : HgVD, V.B = veblen ℓ (gcG 0 + 1) ∧ V.γ ≤ gtc ℓ :=
  wmSysAll wmOm1Step_sq

end Googology.Trans.PoR.InaccPsi.R2.Wm
