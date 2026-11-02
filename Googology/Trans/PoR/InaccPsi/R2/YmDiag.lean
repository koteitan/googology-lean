import Googology.Trans.PoR.InaccPsi.R2.XxRS
import Googology.Trans.PoR.InaccPsi.R2.XkImg

set_option autoImplicit false

open Ordinal Googology.Trans.PoR.InaccPsi.R2

namespace Googology.Trans.PoR.InaccPsi.R2.Ym

/-- The old XxRS interface cannot be instantiated at layer ε₀. -/
theorem no_XxRS_eps0 : ¬ Nonempty (Xx.XxRS ε₀) := by
  rintro ⟨R⟩
  exact (lt_asymm (lt_add_one ε₀) R.W_lt)

/-- The general IMG step itself has no constant-index restriction. -/
theorem img_step_at_read_index {ρ τ δ c : Ordinal.{0}} (h : RstK ρ τ δ)
    (hcT : c ∈ Tset ρ) (hc1 : c < Om1)
    (H1 : ∀ v, v < Gb.gq c ρ → Gn.GnI ρ δ v) (H2 : Gn.GnI ρ δ (Gb.gq c ρ)) :
    ∀ v, v < Gb.gq (c + 1) ρ → Gn.GnI ρ δ v :=
  Xk.xkImg_step h hcT hc1 H1 H2


end Googology.Trans.PoR.InaccPsi.R2.Ym
