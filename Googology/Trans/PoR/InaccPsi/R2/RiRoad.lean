import Googology.Trans.PoR.InaccPsi.R2.RiLow
import Googology.Trans.PoR.InaccPsi.R2.RiMove2

/-!
# The roads with the new bound `U_T = P(Γ_{Ω₁+ω})` and the hypothesis `Ri.RiLhTopH`

`L(ξ) = Nc.ncL S ξ`, `Γ_{Ω₁+ω}` (`Ga.gaW`), `U_T = P(Γ_{Ω₁+ω})` (`Ri.riTow_low`), `RiLhTopH` the move at the points
fixed by every level `Φ_μ`, `μ < Ω₁·Ω₁` (`Ri.RiLhTopH`, equivalent to `Rh.RhLhTopG`).

* `riRoadTow_nuH` (**(TC) asked only at the restart left ends in `[U_T, L(n+2))` and at `L(n+1)`, (EMB₂) dropped,
  under `L(ω+1) ≤ ν_C` and `RiLhTopH`**: `Ri.riRoadTow_nu` with `Ri.riLhTopG_of_H`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ri

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Rd Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Bt

variable {S : InaccSeq.{0}}

/-- **The road with (EMB₂) dropped and (TC) asked only at the restart left ends in `[U_T, L(n+2))` and at `L(n+1)`**,
`U_T = P(Γ_{Ω₁+ω})`, under `L(ω+1) ≤ ν_C` and `RiLhTopH` (a reduction: `L(ω+1) ≤ ν_C` is half of the conclusion). -/
theorem riRoadTow_nuH (hU : ∀ l, CdRange S l → iota S gaW ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S gaW ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S gaW ≤ l → CdCapV S l)
    (hEQ : CdEQ S) (hν : Nc.ncL S (ω + 1) ≤ nuC) (hlh : RiLhTopH S) (htc : RdTCRst2 S (Nm.Pv S gaW)) :
    CdTC S ∧ CdEMB2 S ∧ CdCL S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  riRoadTow_nu hU hL hV hEQ hν (riLhTopG_of_H hlh) htc

end Googology.Trans.PoR.InaccPsi.R2.Ri
