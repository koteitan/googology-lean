import Googology.Trans.PoR.InaccPsi.R2.XwFirst

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yp

open Ordinal Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2

variable {S : InaccSeq.{0}}

/-- The first jump value is `L(ω)·2`, but it has no same-reach chain below it. -/
theorem ypFirstJump_has_no_chain (n : ℕ) (R R' : Ordinal.{0}) :
    Bc.bcB S n (Bc.bcC S n * 2) = Nc.ncL S ω * 2 ∧
    ¬ ∀ x < Bc.bcC S n * 2,
      ∃ y, x < y ∧ y < Bc.bcC S n * 2 ∧ Xr.XrPt S n R R' y :=
  ⟨Xw.xwFirst_val n, Xw.xwFirst_jump_vac⟩


end Googology.Trans.PoR.InaccPsi.R2.Yp
