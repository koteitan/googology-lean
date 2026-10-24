import Googology.Trans.PoR.InaccPsi.R2.SeLow
import Googology.Trans.PoR.InaccPsi.R2.SePi

/-!
# The roads with `SePiHom` (the commutation of `B_n` with `ϑ`) in place of `Rt.RtPiComm`

`L(ξ) = Nc.ncL S ξ`, `c_n = L(n+1) = Bc.bcC S n`, `Γ_{Ω₁+Ω₁^ω} = Ge.geV`.

* `seRoadE_nuHom` (**the road `Se.seRoadE_nuHi` with `Se.SePiHom` in place of `Rk.RkLhTopE`**: UPPER, LOWER, CapV
  at `λ ≥ ι(Γ_{Ω₁+Ω₁^ω})`, EQ, `L(ω+1) ≤ ν_C`, `SePiHom`, `T`, (CL); no (TC) hypothesis);
* `seRoadPiHom` (`Rt.rtRoadPi` with `SePiHom` in place of `Rt.RtPiComm`), `seRoadSfHom` (`Rt.rtRoadSf` with
  `SePiHom` in place of `Rt.RtPiComm`), `seRoadE_nuHom2` (`seRoadE_nuHom` with `Se.SePiHom2`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Se

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Bt

variable {S : InaccSeq.{0}}

/-- **The road with UPPER, LOWER, CapV asked only at `λ ≥ ι(Γ_{Ω₁+Ω₁^ω})`, EQ, `L(ω+1) ≤ ν_C`, `SePiHom`, `T`,
(CL)**: (TC), (EMB₂), (CL), (C1), `ν_C = L(ω+1)`, `L(ω) <₂ L(ω+1)`, (P), (Q), the reaches. -/
theorem seRoadE_nuHom (hU : ∀ l, CdRange S l → iota S Ge.geV ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S Ge.geV ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S Ge.geV ≤ l → CdCapV S l)
    (hEQ : CdEQ S) (hν : Nc.ncL S (ω + 1) ≤ nuC) (hpi : SePiHom S)
    (hT : Cx.CxT S) (hcl : ∀ n : ℕ, le1 (Bc.bcC S n) (Bc.bcC S (n + 1))) :
    CdTC S ∧ CdEMB2 S ∧ CdCL S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  seRoadE_nuHi hU hL hV hEQ hν (seLhTopE hpi) hT hcl

/-- **The road `Rt.rtRoadPi` with `SePiHom` in place of `Rt.RtPiComm`.** -/
theorem seRoadPiHom (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hN : Cx.CxNamed S) (hpi : SePiHom S) (hth : Nc.ncL S (ω + 1) ≤ nuC → Mx.MxThMoveW S)
    (hhi : Nc.ncL S (ω + 1) ≤ nuC → Mx.MxEQth S) :
    CdEQ S ∧ CdTC S ∧ CdEMB2 S ∧ Cx.CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  Rt.rtRoadPi hU hO hL hV hN (sePiComm hpi) hth hhi

/-- **The road `Rt.rtRoadSf` with `SePiHom` in place of `Rt.RtPiComm`.** -/
theorem seRoadSfHom (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hN : Cx.CxNamed S) (hpi : SePiHom S) (hq : Tp.TpEQall S) :
    CdEQ S ∧ CdTC S ∧ CdEMB2 S ∧ Cx.CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  Rt.rtRoadSf hU hO hL hV hN (sePiComm hpi) hq

/-- **The road `seRoadE_nuHom` with `SePiHom2`** (one `ϑ`-commutation statement per base). -/
theorem seRoadE_nuHom2 (hU : ∀ l, CdRange S l → iota S Ge.geV ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S Ge.geV ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S Ge.geV ≤ l → CdCapV S l)
    (hEQ : CdEQ S) (hν : Nc.ncL S (ω + 1) ≤ nuC) (hpi : SePiHom2 S)
    (hT : Cx.CxT S) (hcl : ∀ n : ℕ, le1 (Bc.bcC S n) (Bc.bcC S (n + 1))) :
    CdTC S ∧ CdEMB2 S ∧ CdCL S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  seRoadE_nuHom hU hL hV hEQ hν (sePiHom_of hpi) hT hcl

end Googology.Trans.PoR.InaccPsi.R2.Se
