import Googology.Trans.PoR.InaccPsi.R2.TeCode

/-!
# ENUM-REACH for the codes `≥ P'`, and the road from it

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.

By `Te.teCode_hi_iff` the restarts of `[B₀, L(ω+1))` with code `≥ P'` are the `L(k)` (code `P'`) and `L(ω)` (code
`P' + 1`).  `hU hV hVt hL` are UPPER, CapV (below and above `L(ω)`), LOWER at the range restarts; `hO hEQ htop hmove`
the other old road hypotheses (`Sh.shRoad_CL`).

* `teEnumHi_iff` (**ENUM-REACH at every restart of `[B₀, L(ω+1))` with code `≥ P'` iff ENUM-REACH at every `L(k)`
  and at `L(ω)`**);
* `teLong_iff_nu`, `teLong_iff_reach` (**(CL) and `m* ≤₁ L(1)` iff `L(k) ≤₁ ν_C` for every `k < ω` iff
  `lh(L(k)) = ν_C` for every `k < ω`**, under the road hypotheses), `teNoUncov_iff_nu` (the same for the
  `Tb.TbNoUncov` statements);
* `teRoadNu` (**the road with the one statement `∀ k < ω, L(k) ≤₁ ν_C`** in place of every gap);
* `teCL_of_enum`, `teRoadEnum` (**the road from the LOWER half of ENUM-REACH at the `L(k)` and the count
  `otp(K_{L(k)} ∩ L(k+1)) ≤ Θ_{L(k)}(P')`**; no `LrGap`, no `TbNoUncov`; EQ under `η_a ↦ η_μ` is not used: the
  realizer route needs it only because ENUM-REACH at the `L(k)` is not available);
* `teEnum_of_road` (**given the road hypotheses, (CL) and `m* ≤₁ L(1)`: ENUM-REACH at `L(k)` iff
  `Θ_{L(k)}(P') = otp(K_{L(k)} ∩ ν_C)`, at `L(ω)` iff `Θ_{L(ω)}(P'+1) = otp(K_{L(ω)} ∩ ν_C)`**: the exact
  statements left of ENUM-REACH for the codes `≥ P'`);
* `teRoadEnum_hyp_iff` (**the hypotheses of `teRoadEnum` are exactly (CL), `m* ≤₁ L(1)` and the counts
  `otp(K_{L(k)} ∩ L(k+1)) ≤ Θ_{L(k)}(P') ≤ otp(K_{L(k)} ∩ ν_C)`**, under the road hypotheses: satisfiability).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Te

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-! ## ENUM-REACH for the codes `≥ P'` is ENUM-REACH at the `L(k)` and `L(ω)` -/

/-- **ENUM-REACH at every restart of `[B₀, L(ω+1))` with code `≥ P'` iff ENUM-REACH at every `L(k)` and at
`L(ω)`.** -/
theorem teEnumHi_iff :
    (∀ l, IsRestartIdx l → cdB0 ≤ l → upsilon l < Nc.ncL S (ω + 1) → Nc.ncPp S ≤ cdCode S l →
        CdUpper S l ∧ CdLower S l) ↔
      ((∀ k : ℕ, CdUpper S (Nc.ncL S (k : Ordinal.{0})) ∧ CdLower S (Nc.ncL S (k : Ordinal.{0}))) ∧
        (CdUpper S (Nc.ncL S ω) ∧ CdLower S (Nc.ncL S ω))) := by
  constructor
  · intro h
    refine ⟨fun k => ?_, ?_⟩
    · obtain ⟨⟨h1, h2, h3, h4⟩, -⟩ := teHi_mem (S := S) k
      exact h _ h1 h2 h3 h4.ge
    · obtain ⟨-, h1, h2, h3, h4⟩ := teHi_mem (S := S) 0
      exact h _ h1 h2 h3 (h4 ▸ le_self_add)
  · rintro ⟨hk, hw⟩ l hl _ hlt hP
    rcases (teCode_hi_iff hl.1 hlt).1 hP with ⟨k, e⟩ | e
    · have : l = Nc.ncL S (k : Ordinal.{0}) :=
        upsilon_normal.strictMono.injective (e.trans (teUps_L k).symm)
      subst this; exact hk k
    · have : l = Nc.ncL S ω := Rc.rcIdx_Lw e
      subst this; exact hw

/-! ## The long region as one statement: `L(k) ≤₁ ν_C` -/

section Road

variable (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
  (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
  (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
  (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
  (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
  (hEQ : Cx.CxEQtop S) (htop : Cx.CxTCtopOff S) (hmove : Cx.CxStdMoveTop S)
include hU hO hL hV hVt hEQ htop hmove

/-- **(CL) and `m* ≤₁ L(1)` iff `L(k) ≤₁ ν_C` for every `k < ω`.** -/
theorem teLong_iff_nu :
    (CdCL S ∧ le1 (Nc.ncL S 0) (Nc.ncL S 1)) ↔ ∀ k : ℕ, le1 (Nc.ncL S (k : Ordinal.{0})) nuC := by
  constructor
  · rintro ⟨hCL, h01⟩ k
    obtain ⟨-, -, -, -, -, -, -, hν, -, -, -, -, -, hn⟩ :=
      Sh.shRoad_CL hU hO hL hV hVt hEQ htop hmove h01 hCL
    rw [hν]
    cases k with
    | zero => simpa using le1_trans h01 (by simpa using (hn 0).1)
    | succ n => exact (hn n).1
  · intro h
    have hν := Sh.shNu hU hV hVt hL
    have hle : ∀ k : ℕ, Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC := fun k =>
      ((teL_lt_omega (k + 1)).trans (Qq.qqL_lt_succ S)).le.trans hν
    refine ⟨fun n => ?_, ?_⟩
    · exact le1_of_le_of_le1 (teL_lt_succ (n + 1)).le (hle (n + 1)) (h (n + 1))
    · have := le1_of_le_of_le1 (teL_lt_succ 0).le (hle 0) (h 0)
      simpa using this

/-- **(CL) and `m* ≤₁ L(1)` iff `lh(L(k)) = ν_C` for every `k < ω`.** -/
theorem teLong_iff_reach :
    (CdCL S ∧ le1 (Nc.ncL S 0) (Nc.ncL S 1)) ↔ ∀ k : ℕ, IsReach R2C (Nc.ncL S (k : Ordinal.{0})) nuC := by
  rw [teLong_iff_nu hU hO hL hV hVt hEQ htop hmove]
  exact forall_congr' fun k => (teReach_nu_iff (teL_lt_nu hU hV hVt hL k).le).symm

/-- **The `Tb.TbNoUncov` statements iff `L(k) ≤₁ ν_C` for every `k < ω`.** -/
theorem teNoUncov_iff_nu :
    (Tb.TbNoUncov S (Nc.ncL S 0) (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + eN (lgG (Nc.ncL S 0)))) ∧
        ∀ n : ℕ, Tb.TbNoUncov S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
          (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + eN (lgG (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})))))) ↔
      ∀ k : ℕ, le1 (Nc.ncL S (k : Ordinal.{0})) nuC :=
  (Tb.tbLong_iff hU hV hVt hL).symm.trans (teLong_iff_nu hU hO hL hV hVt hEQ htop hmove)

/-- **The road with the one statement `∀ k < ω, L(k) ≤₁ ν_C`** (no `LrGap`, no `TbNoUncov`). -/
theorem teRoadNu (h : ∀ k : ℕ, le1 (Nc.ncL S (k : Ordinal.{0})) nuC) :
    CdEQ S ∧ CdTC S ∧ CdEMB2 S ∧ Cx.CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  obtain ⟨hCL, h01⟩ := (teLong_iff_nu hU hO hL hV hVt hEQ htop hmove).2 h
  exact Sh.shRoad_CL hU hO hL hV hVt hEQ htop hmove h01 hCL

end Road

/-! ## The road from ENUM-REACH at the `L(k)` -/

/-- **LOWER at `L(k)` and `otp(K_{L(k)} ∩ L(k+1)) ≤ Θ_{L(k)}(P')` give `L(k) ≤₁ L(k+1)`.** -/
theorem teCL_of_enum (k : ℕ) (hlow : CdLower S (Nc.ncL S (k : Ordinal.{0})))
    (hc : cdOtp (cdK (Nc.ncL S (k : Ordinal.{0}))) (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) ≤
      cdTheta S (Nc.ncL S (k : Ordinal.{0})) (Nc.ncPp S)) :
    le1 (Nc.ncL S (k : Ordinal.{0})) (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) := by
  have hcode : cdCode S (Nc.ncL S (k : Ordinal.{0})) = Nc.ncPp S := (teHi_mem k).1.2.2.2
  have hR : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ cdR S (Nc.ncL S (k : Ordinal.{0})) := by
    rw [Rc.rcLe_R_iff, hcode]; exact hc
  have h := hlow
  unfold CdLower at h
  rw [teUps_L] at h
  exact le1_of_le_of_le1 (teL_lt_succ k).le hR h

section Road2

variable (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
  (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
  (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
  (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
  (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
  (hEQ : Cx.CxEQtop S) (htop : Cx.CxTCtopOff S) (hmove : Cx.CxStdMoveTop S)
include hU hO hL hV hVt hEQ htop hmove

/-- **The road from the LOWER half of ENUM-REACH at every `L(k)` with the count
`otp(K_{L(k)} ∩ L(k+1)) ≤ Θ_{L(k)}(P')`.** -/
theorem teRoadEnum
    (he : ∀ k : ℕ, CdLower S (Nc.ncL S (k : Ordinal.{0})) ∧
      cdOtp (cdK (Nc.ncL S (k : Ordinal.{0}))) (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) ≤
        cdTheta S (Nc.ncL S (k : Ordinal.{0})) (Nc.ncPp S)) :
    CdEQ S ∧ CdTC S ∧ CdEMB2 S ∧ Cx.CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  have hCL : CdCL S := fun n => teCL_of_enum (n + 1) (he (n + 1)).1 (he (n + 1)).2
  have h01 : le1 (Nc.ncL S 0) (Nc.ncL S 1) := by simpa using teCL_of_enum (S := S) 0 (he 0).1 (he 0).2
  exact Sh.shRoad_CL hU hO hL hV hVt hEQ htop hmove h01 hCL

/-- **The exact statements left of ENUM-REACH for the codes `≥ P'`**: given the road hypotheses, (CL) and
`m* ≤₁ L(1)`, ENUM-REACH at `L(k)` iff `Θ_{L(k)}(P') = otp(K_{L(k)} ∩ ν_C)`, and at `L(ω)` iff
`Θ_{L(ω)}(P' + 1) = otp(K_{L(ω)} ∩ ν_C)` (`ν_C = L(ω+1)` there). -/
theorem teEnum_of_road (hCL : CdCL S) (h01 : le1 (Nc.ncL S 0) (Nc.ncL S 1)) :
    (∀ k : ℕ, (CdUpper S (Nc.ncL S (k : Ordinal.{0})) ∧ CdLower S (Nc.ncL S (k : Ordinal.{0}))) ↔
        cdTheta S (Nc.ncL S (k : Ordinal.{0})) (Nc.ncPp S) = cdOtp (cdK (Nc.ncL S (k : Ordinal.{0}))) nuC) ∧
      ((CdUpper S (Nc.ncL S ω) ∧ CdLower S (Nc.ncL S ω)) ↔
        cdTheta S (Nc.ncL S ω) (Nc.ncPp S + 1) = cdOtp (cdK (Nc.ncL S ω)) nuC) := by
  obtain ⟨-, -, -, -, -, -, -, hν, -, -, -, -, hw, -⟩ :=
    Sh.shRoad_CL hU hO hL hV hVt hEQ htop hmove h01 hCL
  have hr := (teLong_iff_reach hU hO hL hV hVt hEQ htop hmove).1 ⟨hCL, h01⟩
  refine ⟨fun k => ?_, ?_⟩
  · have hδ : cdDelta (Nc.ncL S (k : Ordinal.{0})) ≤ nuC :=
      (teDelta_L k).le.trans (teL_lt_nu hU hV hVt hL (k + 1)).le
    have hr' : IsReach R2C (upsilon (Nc.ncL S (k : Ordinal.{0}))) nuC := by rw [teUps_L]; exact hr k
    have h := teEnum_iff_count (S := S) hr' hδ
    rw [(teHi_mem k).1.2.2.2] at h
    exact h
  · have hδ : cdDelta (Nc.ncL S ω) ≤ nuC := teDelta_Lw.trans (Sh.shNu hU hV hVt hL)
    have hr' : IsReach R2C (upsilon (Nc.ncL S ω)) nuC := by rw [Rc.rcUps_Lw, hν]; exact hw
    have h := teEnum_iff_count (S := S) hr' hδ
    rw [cdCode_Lω Rc.rcUps_Lw] at h
    exact h

/-- **The hypotheses of `teRoadEnum` are (CL), `m* ≤₁ L(1)` and the counts
`otp(K_{L(k)} ∩ L(k+1)) ≤ Θ_{L(k)}(P') ≤ otp(K_{L(k)} ∩ ν_C)`.** -/
theorem teRoadEnum_hyp_iff :
    (∀ k : ℕ, CdLower S (Nc.ncL S (k : Ordinal.{0})) ∧
      cdOtp (cdK (Nc.ncL S (k : Ordinal.{0}))) (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) ≤
        cdTheta S (Nc.ncL S (k : Ordinal.{0})) (Nc.ncPp S)) ↔
    ((CdCL S ∧ le1 (Nc.ncL S 0) (Nc.ncL S 1)) ∧
      ∀ k : ℕ, cdOtp (cdK (Nc.ncL S (k : Ordinal.{0}))) (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) ≤
          cdTheta S (Nc.ncL S (k : Ordinal.{0})) (Nc.ncPp S) ∧
        cdTheta S (Nc.ncL S (k : Ordinal.{0})) (Nc.ncPp S) ≤ cdOtp (cdK (Nc.ncL S (k : Ordinal.{0}))) nuC) := by
  have hlow : ∀ k : ℕ, (∀ k : ℕ, IsReach R2C (Nc.ncL S (k : Ordinal.{0})) nuC) →
      (CdLower S (Nc.ncL S (k : Ordinal.{0})) ↔
        cdTheta S (Nc.ncL S (k : Ordinal.{0})) (Nc.ncPp S) ≤ cdOtp (cdK (Nc.ncL S (k : Ordinal.{0}))) nuC) := by
    intro k hr
    have hδ : cdDelta (Nc.ncL S (k : Ordinal.{0})) ≤ nuC :=
      (teDelta_L k).le.trans (teL_lt_nu hU hV hVt hL (k + 1)).le
    have hr' : IsReach R2C (upsilon (Nc.ncL S (k : Ordinal.{0}))) nuC := by rw [teUps_L]; exact hr k
    have h := teLower_iff_count (S := S) hr' hδ
    rw [(teHi_mem k).1.2.2.2] at h
    exact h
  constructor
  · intro he
    have hCL : CdCL S := fun n => teCL_of_enum (n + 1) (he (n + 1)).1 (he (n + 1)).2
    have h01 : le1 (Nc.ncL S 0) (Nc.ncL S 1) := by simpa using teCL_of_enum (S := S) 0 (he 0).1 (he 0).2
    have hr := (teLong_iff_reach hU hO hL hV hVt hEQ htop hmove).1 ⟨hCL, h01⟩
    exact ⟨⟨hCL, h01⟩, fun k => ⟨(he k).2, (hlow k hr).1 (he k).1⟩⟩
  · rintro ⟨hl, hc⟩ k
    have hr := (teLong_iff_reach hU hO hL hV hVt hEQ htop hmove).1 hl
    exact ⟨(hlow k hr).2 (hc k).2, (hc k).1⟩

end Road2

end Googology.Trans.PoR.InaccPsi.R2.Te
