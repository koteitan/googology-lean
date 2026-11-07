import Googology.Trans.PoR.InaccPsi.R2.ZmPast
import Googology.Trans.PoR.InaccPsi.R2.TzB
import Googology.Trans.PoR.InaccPsi.R2.ZtIso
import Googology.Trans.PoR.InaccPsi.R2.TsPsi
import Googology.Trans.PoR.InaccPsi.R2.TfPsi

/-!
# Zu: strongly critical codes are atoms; `Γ` below `θ`

`θ = ψ_{Ω₂}(Ω_ω) = ConjT.th S`.

* `zuSC_atom` (**a strongly critical code above `Ω₁` is an atom**: sums and Veblen values of smaller codes are not
  strongly critical);
* `zuGamma_th` (**`Γ_θ = θ`**: `ψ_{Ω₂}(Ω_ω)` is a fixed point of `F_0 = Γ`, `Ts.ts_fwd` with `Ω₂ ∣ Ω_ω`),
  `zuGcG_lt_th` (**`Γ_{Ω₁+1+c} < θ` for `c < θ`**).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zu

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Zb
  Googology.Trans.PoR.InaccPsi.R2.Mx

/-- **A strongly critical code above `Ω₁` is an atom.** -/
theorem zuSC_atom {Z : Ordinal.{0}} {At : Set Ordinal.{0}} (hZ1 : Z ≤ Om 1) {x : Ordinal.{0}}
    (hx : GxCl Z At x) : SC x → Om 1 < x → x ∈ At := by
  induction hx with
  | small h => intro _ h1; exact absurd (h.trans_le hZ1) (not_lt.2 h1.le)
  | om => intro _ h1; exact absurd h1 (lt_irrefl _)
  | atom hs => intro _ _; exact hs
  | @add x y _ _ ihx ihy =>
    intro hSC h1
    rcases eq_or_ne y 0 with rfl | hy0
    · rw [add_zero] at hSC h1 ⊢; exact ihx hSC h1
    · have hxp : x < x + y := lt_add_of_pos_right x (pos_iff_ne_zero.2 hy0)
      have hy : y = x + y := by
        refine le_antisymm le_add_self (not_lt.1 fun hlt => ?_)
        exact absurd (hSC.isPrincipal hxp hlt) (lt_irrefl _)
      rw [← hy] at hSC h1 ⊢; exact ihy hSC h1
  | @phi x y _ _ ihx ihy =>
    intro hSC h1
    by_cases hxp : x < veblen x y
    · by_cases hyp : y < veblen x y
      · exact absurd (hSC.2 x hxp y hyp) (lt_irrefl _)
      · have hy : y = veblen x y := le_antisymm (right_le_veblen x y) (not_lt.1 hyp)
        rw [← hy] at hSC h1 ⊢; exact ihy hSC h1
    · have hx' : x = veblen x y := le_antisymm (left_le_veblen x y) (not_lt.1 hxp)
      rw [← hx'] at hSC h1 ⊢; exact ihx hSC h1

variable (S : InaccSeq.{0})

/-- **`Γ_θ = θ`.** -/
theorem zuGamma_th : gamma (ConjT.th S) = ConjT.th S := by
  have hSC : SC (Om (ω : Ordinal.{0})) := SC_Om omega0_ne_zero
  have hOw : ω ^ Om (ω : Ordinal.{0}) = Om ω := Low.opow_eq_self_of_SC hSC
  have hown : Om ω ∈ S.CSet (Om ω) (S.psi (Om ω) (Om (1 + 1))) := ConjT.OmW_mem S _ _
  have hdvd : Le.leWe (0 + 1) ∣ Om ω := by
    unfold Le.leWe
    conv_rhs => rw [← hOw]
    refine opow_dvd_opow ω ?_
    rw [zero_add, mul_one]
    exact Om_le_Om.2 (by rw [one_add_one_eq_two]; exact (natCast_lt_omega0 2).le)
  have h0 : Om (ω : Ordinal.{0}) ≠ 0 := (Om_pos omega0_ne_zero).ne'
  have hpos : (0 : Ordinal.{0}) < S.psi (Om ω) (Om (1 + 1)) := (ConjT.SC_th S).1
  have h := Ts.ts_fwd (S := S) 0 (Om ω) hown hdvd h0 hpos
  rw [Rh.rhF_zero] at h
  exact h

/-- **`Γ_{Ω₁+1+c} < θ` for every `c < θ`.** -/
theorem zuGcG_lt_th {c : Ordinal.{0}} (hc : c < ConjT.th S) : gcG c < ConjT.th S := by
  rw [Tf.tf_gcG]
  have hSC := ConjT.SC_th S
  have h1 : Om1 + 1 < ConjT.th S := by
    have hθ1 : Om 1 < ConjT.th S := Zr.zrTh_gt_Om1
    rw [← Br.Om1_eq] at hθ1
    exact hSC.isSuccLimit.add_one_lt hθ1
  have h2 : Om1 + 1 + c < ConjT.th S := hSC.isPrincipal h1 hc
  calc gamma (Om1 + 1 + c) < gamma (ConjT.th S) := gamma_lt_gamma.2 h2
    _ = ConjT.th S := zuGamma_th S

end Googology.Trans.PoR.InaccPsi.R2.Zu
