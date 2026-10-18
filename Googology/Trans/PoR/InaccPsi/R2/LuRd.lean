import Googology.Trans.PoR.InaccPsi.R2.LuPh
import Googology.Trans.PoR.InaccPsi.R2.PhRoad

/-!
# ENUM-REACH at every restart of the range below `Λ⁺(luSys)`, and the road without the notation hypothesis

A named fixed point `λ = υ_λ` below `Λ⁺(luSys) ≤ ι(ω^{φ(Ω₁,1)}·ω)` has `e(η_λ) ≤ φ(Ω₁, 1)` (`Ph.phExp_le`), so THEOREM
UNI (`Gg.ggUniTh`) with `luPoly` gives `Θ_λ(m_λ) = O(λ)` there:

* `luT_fix` (**the notation hypothesis below `Λ⁺(luSys)`, proved**);
* `luEnum` (**ENUM-REACH, both halves, at every restart of the range below `Λ⁺(luSys)`**, fixed points included);
* `luRoadPh` (**the road below `Λ⁺(luSys)` without the notation hypothesis**: the rest is UPPER/LOWER at
  `λ ≥ Λ⁺(luSys)`, CapV at the outer restarts below `L(ω)`, (CL), EQ, TCrest, (EMB₂)).

No new axiom beyond `R2.CitedLu`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Lu

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Cd
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Cp Googology.Trans.PoR.InaccPsi.R2.Xt
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph

variable {S : InaccSeq.{0}}

/-- **The notation hypothesis below `Λ⁺(luSys)`**: `Θ_λ(m_λ) = O(λ)` at every fixed point of the range. -/
theorem luT_fix {l : Ordinal.{0}} (hr : CdRange S l) (hlB : l < xtB1 luSys) (hfix : upsilon l = l) :
    cdTheta S l (cdCode S l) = xtOrec luSys l :=
  ggUniTh lu_T_lt_Gam.le luPoly hr.1 hfix (cp_name_L hr.2.2.1)
    (phExp_le hr.1 hfix (cp_name_L hr.2.2.1) (hlB.trans_le (lu_fr (S := S)).2.2.1))

/-- **ENUM-REACH at every restart of the range below `Λ⁺(luSys)`.** -/
theorem luEnum {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtB1 luSys) : CdUpper S l ∧ CdLower S l := by
  rcases (upsilon_normal.strictMono.le_apply : l ≤ upsilon l).lt_or_eq with hnf | hfx
  · exact lu_init hr hl hnf
  · exact (lu_iff hr.1 hl).2 (luT_fix hr hl hfx.symm)

/-- **The road below `Λ⁺(luSys)` without the notation hypothesis.** -/
theorem luRoadPh (hU : ∀ l, CdRange S l → xtB1 luSys ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → xtB1 luSys ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut (xtB1 luSys) l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  luRoad3 hU hL (fun _ hr hlB hfix => luT_fix hr hlB hfix) hV hC hEQ hrest hB2

end Googology.Trans.PoR.InaccPsi.R2.Lu
