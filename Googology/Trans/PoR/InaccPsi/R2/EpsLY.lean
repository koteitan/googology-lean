import Googology.Trans.PoR.InaccPsi.R2.ORecY

/-!
# `ρ_L ≥ υ_{Λ_{ε_{x+2}}+ω²}` as one theorem

The corollary of `left_ge_LamY_ww` (`Λ_{ε_{x+2}} + ω² ≤ L`) and the monotonicity of `υ`: the left end
`ρ_L` of the first non-standard `<₂`-pair lies at or above `υ_{Λ_{ε_{x+2}}+ω²}`, the end of the block of
the restart `ρ_{Λ_{ε_{x+2}}}`.

* `nuC_boundYw`.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order

/-- **`υ_{Λ_{ε_{x+2}}+ω²} ≤ ρ_L < ν_C`**: `ρ_L <₂ ν_C = ρ_ξ` with `Λ_{ε_{x+2}} + ω² ≤ L < ξ` restart
indices. -/
theorem nuC_boundYw : ∃ L ξ, IsRestartIdx L ∧ IsRestartIdx ξ ∧ LamY + ω * ω ≤ L ∧ L < ξ ∧
    upsilon (LamY + ω * ω) ≤ upsilon L ∧ upsilon L < nuC ∧ nuC = upsilon ξ ∧ nuC < Om1 ∧
    le2 (upsilon L) nuC := by
  obtain ⟨L, ξ, hL, hξ, hLξ, he, h2, -, -, -⟩ := level2_restart
  have hLν : upsilon L < nuC := by rw [he]; exact upsilon_normal.strictMono hLξ
  have hle := left_ge_LamY_ww hL hLν h2
  exact ⟨L, ξ, hL, hξ, hle, hLξ, upsilon_normal.strictMono.monotone hle, hLν, he, nuC_lt_Om1, h2⟩

end Googology.Trans.PoR.InaccPsi.R2
