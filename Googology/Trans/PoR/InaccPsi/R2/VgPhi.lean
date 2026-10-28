import Googology.Trans.PoR.InaccPsi.R2.VdDat
import Googology.Trans.PoR.InaccPsi.R2.UoDV

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Vg

open Ordinal Order Googology.Notation.InaccPsi
open Googology.Trans.PoR.InaccPsi.R2

variable {S : InaccSeq.{0}}

/-- FWD for the level `Φ_μ` throughout `μ < θ`, from the existing Ω₂-wide theorem. -/
theorem vg_phi_fwd {μ : Ordinal.{0}} (hμ : μ < ConjT.th S) : Ul.UlFWD S 0 μ := by
  have hθ : ConjT.th S < Om (0 + 1 + 1) := by simpa using Vd.vd_th_lt_W
  exact Uo.uo_phi_fwd (hμ.trans hθ)

/-- The exact ψ-link for `Φ_μ` throughout `μ < θ`. -/
theorem vg_phi_eq {μ B c D : Ordinal.{0}} (hμ : μ < ConjT.th S)
    (hown : B ∈ S.CSet B (S.psi B (Om (0 + 1))))
    (hB : Om (0 + 1) ^ μ ∣ B)
    (hμB : μ ∈ S.CSet B (S.psi B (Om (0 + 1))))
    (hc : Ul.ulH S 0 μ c = S.psi B (Om (0 + 1)))
    (hD : D < Om (0 + 1))
    (hcond : ∀ d, d ≤ D → d < Ul.ulH S 0 μ (c + d)) :
    D < S.psi (B + Om (0 + 1) ^ μ * D) (Om (0 + 1)) ∧
      S.psi (B + Om (0 + 1) ^ μ * D) (Om (0 + 1)) = Ul.ulH S 0 μ (c + D) :=
  Uo.uo_phi_eq (hμ.trans (show ConjT.th S < Om (0 + 1 + 1) by simpa using Vd.vd_th_lt_W))
    hown hB hμB hc hD hcond

/-- The K⁽⁰⁾ datum of the level argument `Ω₁+μ` is the level datum. -/
theorem vg_phi_dat {μ q : Ordinal.{0}} (hq : SC q) :
    Vd.vdD S 0 (Om 1 + μ) < q ↔ Ul.ulD S 0 μ < q := Vd.vd_lev_dat hq

#print axioms vg_phi_fwd
#print axioms vg_phi_eq

end Googology.Trans.PoR.InaccPsi.R2.Vg
