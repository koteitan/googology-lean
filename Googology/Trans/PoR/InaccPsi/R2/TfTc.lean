import Googology.Trans.PoR.InaccPsi.R2.TcFn
import Googology.Trans.PoR.InaccPsi.R2.CitedTf

/-!
# `Tf.tfDat = Tc.tcDat` below `Γ'`

The data `Tf.tfDat` of the generic citation `R2.CitedTf` and the data `Tc.tcDat` agree below `Γ' = lgGam'` (same
recursion; the only atom `Γ_{Ω₁+1} = Γ_{Ω₁+1+0}` has data `0` in both): `tfDat_eq_tc`, `tfDatL_eq_tc`; `tf_G'_lt_BG`
(`Γ' < B_Γ`: `Γ' ≤ Γ_{Ω₁+2} < B_Γ`), `tf_Om1_add_lt_G'`.  Used by `R2.CitedTc` to derive its former axioms.

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Tf

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rj Googology.Trans.PoR.InaccPsi.R2.Ss
  Googology.Trans.PoR.InaccPsi.R2.Tc

/-- **`Γ' < B_Γ`.** -/
theorem tf_G'_lt_BG : lgGam' < tfBG := by
  have h2 : (Om1 : Ordinal.{0}) + 1 + 1 < tfBG := SC.add_one_lt tfBG_SC (SC.add_one_lt tfBG_SC tfBG_gt)
  have hle : lgGam' ≤ gamma (Om1 + 1 + 1) :=
    lgGam'_le (Lq.lq_gamma_SC _) (by rw [tf_ggGam]; exact gamma_lt_gamma.2 (lt_add_one _))
  exact hle.trans_lt (by rw [← tfBG_fix]; exact gamma_lt_gamma.2 h2)

/-- **`tfDat = tcDat` below `Γ'`.** -/
theorem tfDat_eq_tc : ∀ z : Ordinal.{0}, z < lgGam' → tfDat z = tcDat z := by
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro hzG
  rcases lt_trichotomy z Om1 with h | rfl | h
  · rw [tfDat_small h, tcDat_small h]
  · rw [tfDat_Om1, tcDat_Om1]
  by_cases hG : z = ggGam
  · rw [hG, tfDat_gg, tcDat_gam]
  have hB : z < tfBG := hzG.trans tf_G'_lt_BG
  by_cases hE : ω ^ z = z
  · have h1 := tc_inv1_lt h hzG hG
    have h2 := ss_inv2_lt hE
    rw [tfDat_phi h hB hE h1, tcDat_eq_phi h hzG hG hE, IH _ h1 (h1.trans hzG), IH _ h2 (h2.trans hzG)]
  · have hz0 : z ≠ 0 := (rj_Om1_pos.trans h).ne'
    have hl := ss_log_lt hz0 hE
    have hm := rj_mod_lt hz0
    rw [tfDat_cnf h hB hE, tcDat_eq_cnf h hzG hE, IH _ hl (hl.trans hzG), IH _ hm (hm.trans hzG)]

/-- `Ω₁ + μ < Γ'` for `μ < Γ'`. -/
theorem tf_Om1_add_lt_G' {μ : Ordinal.{0}} (hμ : μ < lgGam') : Om1 + μ < lgGam' :=
  SC.isPrincipal tc_SC_G' tc_Om1_lt_G' hμ

theorem tfDatL_eq_tc {μ : Ordinal.{0}} (hμ : μ < lgGam') : tfDat (Om1 + μ) = tcDatL μ :=
  tfDat_eq_tc _ (tf_Om1_add_lt_G' hμ)

end Googology.Trans.PoR.InaccPsi.R2.Tf
