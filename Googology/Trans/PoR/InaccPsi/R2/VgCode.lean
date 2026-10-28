import Googology.Trans.PoR.InaccPsi.R2.VdDat
import Googology.Trans.PoR.InaccPsi.R2.UoUc

/-! The full-bound code test from the K⁽⁰⁾ datum. -/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Vg

open Ordinal Order Googology.Notation.InaccPsi
open Googology.Trans.PoR.InaccPsi.R2

variable {S : InaccSeq.{0}}

/-- The Vd datum is the exact K⁽⁰⁾ visibility test at every ordinal, including above `B₂`. -/
theorem vg_code_iffK {q z : Ordinal.{0}} (hq : SC q) :
    Vd.vdD S 0 z < q ↔ Ul.UlK S 0 q z := by
  rw [Vd.vdD_eq, Ul.ul_vis hq]

/-- Every code below `θ` has the top `K⁽⁰⁾_{Ω₁}` visibility bound. -/
theorem vg_theta_K {z : Ordinal.{0}} (hz : z < ConjT.th S) :
    Ul.UlK S 0 (Om 1) z := Vd.vd_K_th z hz

/-- Every code below `θ` has K⁽⁰⁾ datum below `Ω₁`. -/
theorem vg_theta_dat_lt {z : Ordinal.{0}} (hz : z < ConjT.th S) :
    Vd.vdD S 0 z < Om 1 := Vd.vdD_lt_Om1 hz

#print axioms vg_code_iffK
#print axioms vg_theta_K

end Googology.Trans.PoR.InaccPsi.R2.Vg
