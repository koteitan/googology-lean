import Googology.Trans.PoR.InaccPsi.R2.TbEc

/-!
# The road with no `LrGap`: (CL) and `m* ≤₁ L(1)` reduced to one statement per point, above `υ_{a+ε_{Γ_{a+1}+1}}`

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.

`a = m*` or `a = L(n+1)`, `b` the next point (`L(1)`, `L(n+2)`).  `TbNoUncov S a b c`: no reach `r` of `a` with
`c ≤ r < b` is uncovered (every Range window `[υ_λ, r(λ))` with `a ≤ υ_λ ≤ r` has `r(λ) ≤ r`).  With
`V(a) = ε_{Γ_{a+1}+1}` (`Tb.tbEc`) and UPPER, CapV, LOWER:

* `tbNoUncov_iff_M`, `tbNoUncov_iff_L` (**`m* ≤₁ L(1)` iff `TbNoUncov` on `[υ_{m*+V(m*)}, L(1))`; (CL) at `n` iff
  `TbNoUncov` on `[υ_{a+V(a)}, L(n+2))`**);
* `tbLong_iff` (**`(CL) ∧ m* ≤₁ L(1)` iff the `TbNoUncov` statements at `m*` and at every `L(n+1)`**: the
  statements left are exactly as strong as (CL) and `m* ≤₁ L(1)`, so none of them can be dropped);
* `tbRoadU` (**the road with no `LrGap`**: the old road hypotheses and the `TbNoUncov` statements),
  `tbNoUncov_of_gap` (the `LrGap`s above `υ_{a+V(a)}` give the `TbNoUncov` statements, so `tbRoadU` asks no more
  than `Tb.tbEcRoad`).

No new axiom.  New definition: `TbNoUncov`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Tb

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Lr

variable {S : InaccSeq.{0}}

/-- **No uncovered reach of `a` in `[c, b)`.** -/
def TbNoUncov (S : InaccSeq.{0}) (a b c : Ordinal.{0}) : Prop :=
  ¬ ∃ r, IsReach R2C a r ∧ c ≤ r ∧ r < b ∧ ∀ l, CdRange S l → a ≤ upsilon l → upsilon l ≤ r → cdR S l ≤ r

section Road

variable (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
  (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
  (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
  (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
include hU hV hVt hL

/-- **`m* ≤₁ L(1)` iff no uncovered reach of `m*` in `[υ_{m*+ε_{Γ_{m*+1}+1}}, L(1))`.** -/
theorem tbNoUncov_iff_M :
    le1 (Nc.ncL S 0) (Nc.ncL S 1) ↔
      TbNoUncov S (Nc.ncL S 0) (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + eN (lgG (Nc.ncL S 0)))) :=
  tbEcM_iff_noUncov hU hV hVt hL

/-- **(CL) at `n` iff no uncovered reach of `L(n+1)` in `[υ_{a+ε_{Γ_{a+1}+1}}, L(n+2))`.** -/
theorem tbNoUncov_iff_L (n : ℕ) :
    le1 (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0})) ↔
      TbNoUncov S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
        (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + eN (lgG (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))) :=
  tbEcCL_iff_noUncov hU hV hVt hL n

/-- **The statements left are exactly as strong as (CL) and `m* ≤₁ L(1)`.** -/
theorem tbLong_iff :
    (CdCL S ∧ le1 (Nc.ncL S 0) (Nc.ncL S 1)) ↔
      (TbNoUncov S (Nc.ncL S 0) (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + eN (lgG (Nc.ncL S 0)))) ∧
        ∀ n : ℕ, TbNoUncov S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
          (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + eN (lgG (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})))))) := by
  constructor
  · rintro ⟨hCL, hM⟩
    exact ⟨(tbNoUncov_iff_M hU hV hVt hL).1 hM, fun n => (tbNoUncov_iff_L hU hV hVt hL n).1 (hCL n)⟩
  · rintro ⟨hM, hn⟩
    exact ⟨fun n => (tbNoUncov_iff_L hU hV hVt hL n).2 (hn n), (tbNoUncov_iff_M hU hV hVt hL).2 hM⟩

/-- **The road with no `LrGap`**: the old road hypotheses and one `TbNoUncov` statement at `m*` and at every
`L(n+1)`, above `υ_{a+ε_{Γ_{a+1}+1}}`. -/
theorem tbRoadU (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hEQ : Cx.CxEQtop S) (htop : Cx.CxTCtopOff S) (hmove : Cx.CxStdMoveTop S)
    (h0 : TbNoUncov S (Nc.ncL S 0) (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + eN (lgG (Nc.ncL S 0)))))
    (hn : ∀ n : ℕ, TbNoUncov S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
      (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + eN (lgG (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})))))) :
    CdEQ S ∧ CdTC S ∧ CdEMB2 S ∧ Cx.CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  obtain ⟨hCL, hM⟩ := (tbLong_iff hU hV hVt hL).2 ⟨h0, hn⟩
  exact Sh.shRoad_CL hU hO hL hV hVt hEQ htop hmove hM hCL

end Road

/-- **Each `LrGap` above `υ_{a+V(a)}` gives the `TbNoUncov` statement** (through (CL), `Tb.tbCL_of_gap`). -/
theorem tbNoUncov_of_gap (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (h0 : LrGap S (Nc.ncL S 0) (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + eN (lgG (Nc.ncL S 0)))))
    (hn : ∀ n : ℕ, LrGap S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
      (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + eN (lgG (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})))))) :
    TbNoUncov S (Nc.ncL S 0) (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + eN (lgG (Nc.ncL S 0)))) ∧
      ∀ n : ℕ, TbNoUncov S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
        (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + eN (lgG (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))) :=
  (tbLong_iff hU hV hVt hL).1 ⟨tbCL_of_gap tbEc hU hV hVt hL hn, tbM_of_gap tbEc hU hV hVt hL h0⟩

end Googology.Trans.PoR.InaccPsi.R2.Tb
