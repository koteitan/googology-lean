import Googology.Trans.PoR.InaccPsi.R2.LvPh
import Googology.Trans.PoR.InaccPsi.R2.LuRd

/-!
# ENUM-REACH at every restart of the range below `Λ⁺(lvSys)`, and the road without the notation hypothesis

A named fixed point `λ = υ_λ` below `Λ⁺(lvSys) ≤ ι(ω^{φ(Ω₁+Ω₁,0)}·ω)` has `e(η_λ) ≤ φ(Ω₁ + Ω₁, 0)` (`Ph.phExp_le`), so
THEOREM UNI (`Gg.ggUniTh`) with `lvPoly` gives `Θ_λ(m_λ) = O(λ)` there:

* `lvT_fix` (**the notation hypothesis below `Λ⁺(lvSys)`, proved**);
* `lvEnum` (**ENUM-REACH, both halves, at every restart of the range below `Λ⁺(lvSys)`**, fixed points included);
* `lvRoadPh` (**the road below `Λ⁺(lvSys)` without the notation hypothesis**: the rest is UPPER/LOWER at
  `λ ≥ Λ⁺(lvSys)`, CapV at the outer restarts below `L(ω)`, (CL), EQ, TCrest, (EMB₂)): the successor of
  `Lu.luRoadPh`, whose UPPER/LOWER and CapV hypotheses are asked from `Λ⁺(luSys) < Λ⁺(lvSys)` on.

No new axiom beyond `R2.CitedLu` and `R2.CitedLv`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Cd
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Cp Googology.Trans.PoR.InaccPsi.R2.Xt
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph Lu

variable {S : InaccSeq.{0}}

/-- **The notation hypothesis below `Λ⁺(lvSys)`**: `Θ_λ(m_λ) = O(λ)` at every fixed point of the range. -/
theorem lvT_fix {l : Ordinal.{0}} (hr : CdRange S l) (hlB : l < xtB1 lvSys) (hfix : upsilon l = l) :
    cdTheta S l (cdCode S l) = xtOrec lvSys l :=
  ggUniTh lv_T_lt_Gam.le lvPoly hr.1 hfix (cp_name_L hr.2.2.1)
    (phExp_le hr.1 hfix (cp_name_L hr.2.2.1) (hlB.trans_le (lv_fr (S := S)).2.2.1))

/-- **ENUM-REACH at every restart of the range below `Λ⁺(lvSys)`.** -/
theorem lvEnum {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtB1 lvSys) : CdUpper S l ∧ CdLower S l := by
  rcases (upsilon_normal.strictMono.le_apply : l ≤ upsilon l).lt_or_eq with hnf | hfx
  · exact lv_init hr hl hnf
  · exact (lv_iff hr.1 hl).2 (lvT_fix hr hl hfx.symm)

/-- **The road below `Λ⁺(lvSys)` without the notation hypothesis.** -/
theorem lvRoadPh (hU : ∀ l, CdRange S l → xtB1 lvSys ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → xtB1 lvSys ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut (xtB1 lvSys) l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  lvRoad3 hU hL (fun _ hr hlB hfix => lvT_fix hr hlB hfix) hV hC hEQ hrest hB2

end Googology.Trans.PoR.InaccPsi.R2
