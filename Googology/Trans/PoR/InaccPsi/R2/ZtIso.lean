import Googology.Trans.PoR.InaccPsi.R2.ZsCap
import Googology.Trans.PoR.InaccPsi.R2.FxIso

/-!
# Zt: the code statement at the isolated fixed restarts holds below every `ι(η)`

`Zn.ZnIsoCode S l₀ B` asks `Θ_λ(m_λ) ≤ ρ_λ` at every `υ`-fixed restart `λ ∈ (l₀, B)` with `Cp.CpIso λ` (no fixed
restart in some `(ν, λ)`).  At such a `λ` with a name the name is `η₁ + Ω₁` (`Fx.fxIso_eta`), the code is `Ω₁`
(`Fx.fxIso_code`) and `Θ_λ(m_λ) = λ = ρ_λ` (`Fx.fxIso_theta`).  Every restart below `ι(η)` has a name
(`ρ_λ < P(η)`), so:

* `ztIsoCode` (**`Zn.ZnIsoCode S l₀ (ι(η))` for all `l₀`, `η`**): in particular the window leaves skWinIsoCode
  (`B = ι(Ω_ω + P′·(k+1))`) and skTopIsoCode (`B = ι(Ω_ω + P′·(ω+1))`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zt

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- **The code statement at the isolated fixed restarts below `ι(η)`.** -/
theorem ztIsoCode (l0 η : Ordinal.{0}) : Zn.ZnIsoCode S l0 (iota S η) := by
  intro l hl _ hlB hfix hiso
  have hX : upsilon l < Pv S η := by
    rw [Fx.fx_Pv_eq (S := S) η]; exact upsilon_normal.strictMono hlB
  rw [Fx.fxIso_theta hl hfix hiso hX, hfix]

end Googology.Trans.PoR.InaccPsi.R2.Zt
