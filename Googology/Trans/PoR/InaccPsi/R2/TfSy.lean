import Googology.Trans.PoR.InaccPsi.R2.SsFn
import Googology.Trans.PoR.InaccPsi.R2.CitedTf

/-!
# `Tf.tfDat = Ss.ssDat` below `Γ_{Ω₁+1}`

The data `Tf.tfDat` of the generic citation `R2.CitedTf` and the data `Ss.ssDat` of the Veblen codes agree below
`Γ_{Ω₁+1}` (same recursion; no atom there): `tfDat_eq_ss`, `tfDatL_eq_ss`, and `tf_Om1_add_lt_gg` (`Ω₁ + μ <
Γ_{Ω₁+1}` for `μ < Γ_{Ω₁+1}`).  Used by `R2.CitedSy` to derive its former axioms from `R2.CitedTf`.

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Tf

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rj Googology.Trans.PoR.InaccPsi.R2.Ss

/-- **`tfDat = ssDat` below `Γ_{Ω₁+1}`.** -/
theorem tfDat_eq_ss : ∀ z : Ordinal.{0}, z < ggGam → tfDat z = ssDat z := by
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro hzG
  rcases lt_trichotomy z Om1 with h | rfl | h
  · rw [tfDat_small h, ssDat_small h]
  · rw [tfDat_Om1, ssDat_Om1]
  have hB : z < tfBG := hzG.trans tf_gg_lt_BG
  by_cases hE : ω ^ z = z
  · have h1 := ss_inv1_lt h hzG
    have h2 := ss_inv2_lt hE
    rw [tfDat_phi h hB hE h1, ssDat_eq_phi h hzG hE, IH _ h1 (h1.trans hzG), IH _ h2 (h2.trans hzG)]
  · have hz0 : z ≠ 0 := (rj_Om1_pos.trans h).ne'
    have hl := ss_log_lt hz0 hE
    have hm := rj_mod_lt hz0
    rw [tfDat_cnf h hB hE, ssDat_eq_cnf h hzG hE, IH _ hl (hl.trans hzG), IH _ hm (hm.trans hzG)]

/-- `Ω₁ + μ < Γ_{Ω₁+1}` for `μ < Γ_{Ω₁+1}`. -/
theorem tf_Om1_add_lt_gg {μ : Ordinal.{0}} (hμ : μ < ggGam) : Om1 + μ < ggGam :=
  SC.isPrincipal ggGam_spec.1 (by rw [rj_Om1]; exact ggGam_spec.2) hμ

theorem tfDatL_eq_ss {μ : Ordinal.{0}} (hμ : μ < ggGam) : tfDat (Om1 + μ) = ssDatL μ :=
  tfDat_eq_ss _ (tf_Om1_add_lt_gg hμ)

end Googology.Trans.PoR.InaccPsi.R2.Tf
