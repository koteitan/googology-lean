import Googology.Trans.PoR.InaccPsi.R2.RdMove
import Googology.Trans.PoR.InaccPsi.R2.RdLow

/-!
# (TC) and (EMB₂) at the left ends in `[U″, L(n+2))`: what is left once `L(ω+1) ≤ ν_C`

`L(ξ) = Nc.ncL S ξ`, `c_n = L(n+1)` (`Bc.bcC`), `B_n = Bc.bcB S n`, `U″ = υ(Λ⁺(lxZ))` (`Rd.rdZ_low`).

* `rdLhMove` (**`Rd.RdLhTopFix2` gives `Tp.TpLhMove`**: `RdLhTopFix2 → Sf.SfLhTMove → Tp.TpLhEps → Tp.TpLhPrin →
  Tp.TpLhMove`);
* `rdTC_win` (**(TC) at every point of the open window `(L(n+1), L(n+2))` that is not a restart point**, given
  `L(ω+1) ≤ ν_C` and `RdLhTopFix2`: `Tp.tpTC_ups` at the `υ`-points, `Tp.tpTC_off` at the other points, with the shift
  `Sf.sfShiftAll`), `rdEMB2_of_nu` (**(EMB₂) everywhere** from `L(ω+1) ≤ ν_C`, `Tp.tpEMB2` with `Sf.sfShiftAll`);
* `RdTCRst2 S U` (a hypothesis name): (TC) at the left ends `x ∈ [U, L(n+2))` with no reach below `L(n+1)` that are
  **restart points or `x = L(n+1)`**; `rdTCRst_of` (**with `L(ω+1) ≤ ν_C` and `RdLhTopFix2`, `RdTCRst2 S U` gives
  `Rb.RbTCRst S U`**), `rdEMB2Rst_of` (**`L(ω+1) ≤ ν_C` gives `Rb.RbEMB2Rst S U`**);
* `rdRoadZ_nu` (the road `Rd.rdRoadZ_rst` with (EMB₂) dropped and (TC) asked only at the restart left ends in
  `[U″, L(n+2))` and at `L(n+1)`, **under the extra hypotheses `L(ω+1) ≤ ν_C` and `RdLhTopFix2`**; `L(ω+1) ≤ ν_C` is
  one half of the conclusion `ν_C = L(ω+1)`, so this is a reduction, not a proof of the road).

No new axiom.  New definition: the hypothesis name `RdTCRst2`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Rd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Tq
  Googology.Trans.PoR.InaccPsi.R2.Rb Googology.Trans.PoR.InaccPsi.R2.Lx

variable {S : InaccSeq.{0}}

/-- **`RdLhTopFix2` gives `Tp.TpLhMove`.** -/
theorem rdLhMove (h : RdLhTopFix2 S) : Tp.TpLhMove S :=
  Tp.tpLhMove_of_prin (Tp.tpLhPrin_of_eps (Sf.sfLhEps (rdSfLhT h)))

/-- **(TC) at every point of `(L(n+1), L(n+2))` that is not a restart point**, given `L(ω+1) ≤ ν_C` and
`RdLhTopFix2`. -/
theorem rdTC_win (hν : Nc.ncL S (ω + 1) ≤ nuC) (hlh : RdLhTopFix2 S) {n : ℕ} {x : Ordinal.{0}}
    (hx1 : Bc.bcC S n < x) (hx2 : x < Bc.bcC S (n + 1)) (hnr : ∀ l, IsRestartIdx l → x ≠ upsilon l) :
    CdTCAt S n x := by
  by_cases hU : UpsPt x
  · exact Tp.tpTC_ups hν Sf.sfShiftAll hx1 hx2 hU hnr
  · exact Tp.tpTC_off hν Sf.sfShiftAll (rdLhMove hlh) hx1 hx2 hU

/-- **(EMB₂) everywhere** from `L(ω+1) ≤ ν_C`. -/
theorem rdEMB2_of_nu (hν : Nc.ncL S (ω + 1) ≤ nuC) : CdEMB2 S := Tp.tpEMB2 hν Sf.sfShiftAll

/-- **(TC) at the left ends `x ∈ [U, L(n+2))` with no reach below `L(n+1)` that are restart points or `x = L(n+1)`.** -/
def RdTCRst2 (S : InaccSeq.{0}) (U : Ordinal.{0}) : Prop :=
  ∀ n : ℕ, ∀ x < Bc.bcC S (n + 1), U ≤ x → (¬ ∃ r < Bc.bcC S n, IsReach R2C x r) →
    (x = Bc.bcC S n ∨ ∃ l, IsRestartIdx l ∧ x = upsilon l) → CdTCAt S n x

/-- **With `L(ω+1) ≤ ν_C` and `RdLhTopFix2`, `RdTCRst2 S U` gives `Rb.RbTCRst S U`.** -/
theorem rdTCRst_of (hν : Nc.ncL S (ω + 1) ≤ nuC) (hlh : RdLhTopFix2 S) {U : Ordinal.{0}}
    (h : RdTCRst2 S U) : RbTCRst S U := by
  intro n x hx hxU hr hcase
  by_cases hrst : ∃ l, IsRestartIdx l ∧ x = upsilon l
  · exact h n x hx hxU hr (Or.inr hrst)
  rcases hcase with hcx | hrst'
  · rcases eq_or_lt_of_le hcx with e | hlt
    · exact h n x hx hxU hr (Or.inl e.symm)
    · exact rdTC_win hν hlh hlt hx fun l hl he => hrst ⟨l, hl, he⟩
  · exact absurd hrst' hrst

/-- **`L(ω+1) ≤ ν_C` gives `Rb.RbEMB2Rst S U`.** -/
theorem rdEMB2Rst_of (hν : Nc.ncL S (ω + 1) ≤ nuC) (U : Ordinal.{0}) : RbEMB2Rst S U :=
  fun n x hx y hy _ _ _ _ _ => rdEMB2_of_nu hν n x hx y hy

/-- **The road `Rd.rdRoadZ_rst` with (EMB₂) dropped and (TC) asked only at the restart left ends in `[U″, L(n+2))`
and at `L(n+1)`**, under the extra hypotheses `L(ω+1) ≤ ν_C` and `RdLhTopFix2` (a reduction: `L(ω+1) ≤ ν_C` is one half
of the conclusion). -/
theorem rdRoadZ_nu (hU : ∀ l, CdRange S l → xtB1 lxZ.sys ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → xtB1 lxZ.sys ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut (xtB1 lxZ.sys) l → CdCapV S l)
    (hEQ : CdEQ S) (hν : Nc.ncL S (ω + 1) ≤ nuC) (hlh : RdLhTopFix2 S)
    (htc : RdTCRst2 S (upsilon (xtB1 lxZ.sys))) :
    CdTC S ∧ CdEMB2 S ∧ CdCL S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  rdRoadZ_rst hU hL hV hEQ (rdTCRst_of hν hlh htc) (rdEMB2Rst_of hν _)

end Googology.Trans.PoR.InaccPsi.R2.Rd
