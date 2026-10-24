import Googology.Trans.PoR.InaccPsi.R2.TeFam

/-!
# The road with the long region starting at `υ_{a+ε_{Γ_{a+1}+ω}}`

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.

`a = m*` or `a = L(n+1)`, `b` the next point, `c_ω(a) = υ_{a+ε_{Γ_{a+1}+ω}}` (`Te.teW`), `c_0(a) = υ_{a+ε_{Γ_{a+1}+1}}`
(`Tb`).  With the realizers `Te.teRealW_M`, `Te.teRealW_L` (the proofs are those of `R2.TbRoad`):

* `teShortW_L`, `teShortW_M` (**`a ≤₁ c_ω(a)`**), `teCLW_of_gap`, `teMW_of_gap`, `teRoadW` (**the road with the gaps
  only above `c_ω(a)`**);
* `teCLW_iff_noUncov`, `teMW_iff_noUncov`, `teLongW_iff` (**(CL) and `m* ≤₁ L(1)` iff `Tb.TbNoUncov` on
  `[c_ω(a), b)` at `m*` and every `L(n+1)`**), `teRoadWU` (**the road with these statements, no `LrGap`**),
  `teNoUncovW_iff_nu` (**these statements iff `L(k) ≤₁ ν_C` for every `k < ω`**);
* `teNoUncov_mono`, `teNoUncovW_of_0` (**the statements of `Tb.tbRoadU` (on `[c_0(a), b)`) give those on
  `[c_ω(a), b)`**), `te_c0_lt_cw` (`c_0(a) < c_ω(a)`): `teRoadWU` asks strictly less than `Tb.tbRoadU`.

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Te

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Lr

variable {S : InaccSeq.{0}}

section Hyp

variable (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
  (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
  (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
  (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
include hU hV hVt hL

/-- **`L(n+1) ≤₁ υ_{a+ε_{Γ_{a+1}+ω}}`** (`a = L(n+1)`). -/
theorem teShortW_L (n : ℕ) :
    le1 (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
      (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + teW (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})))) := by
  have hν := Sh.shNu hU hV hVt hL
  have hlow : Nc.ncL S ω ≤ nuC := (Qq.qqL_lt_succ S).le.trans hν
  obtain ⟨hR, hb⟩ := teRealW_L hlow hU hL (Tp.tpStdPairTop hν) n
  obtain ⟨l, hl, e⟩ := Pp.ppL_succ_restart (S := S) n
  exact lrLe1_of_real (Rz.rzLOWER_of_rest hL) (le_self_add.trans upsilon_normal.strictMono.le_apply)
    (Cv.cvNoPair_of_nu hl e (hb.le.trans ((Pp.ppL_lt_omega (n + 1)).le.trans hlow))) hR

/-- **`m* ≤₁ υ_{m*+ε_{Γ_{m*+1}+ω}}`**. -/
theorem teShortW_M : le1 (Nc.ncL S 0) (upsilon (Nc.ncL S 0 + teW (Nc.ncL S 0))) := by
  have hν := Sh.shNu hU hV hVt hL
  have hlow : Nc.ncL S ω ≤ nuC := (Qq.qqL_lt_succ S).le.trans hν
  obtain ⟨hR, hb⟩ := teRealW_M hlow hU hL (Tp.tpStdPairTop hν)
  obtain ⟨l, hl, e⟩ := Cv.cvM_restart (S := S)
  exact lrLe1_of_real (Rz.rzLOWER_of_rest hL) (le_self_add.trans upsilon_normal.strictMono.le_apply)
    (Cv.cvNoPair_of_nu hl e (hb.le.trans ((Pp.ppL_mono one_lt_omega0.le).trans hlow))) hR

/-- **(CL) from `LrGap` above `υ_{a+ε_{Γ_{a+1}+ω}}` at every `L(n+1)`.** -/
theorem teCLW_of_gap
    (hn : ∀ n : ℕ, LrGap S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
      (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + teW (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))) :
    CdCL S := by
  have hν := Sh.shNu hU hV hVt hL
  have hlow : Nc.ncL S ω ≤ nuC := (Qq.qqL_lt_succ S).le.trans hν
  intro n
  obtain ⟨hR, hb⟩ := teRealW_L hlow hU hL (Tp.tpStdPairTop hν) n
  obtain ⟨l, hl, e⟩ := Pp.ppL_succ_restart (S := S) n
  exact Ls.lsLe1_of_gapCof (Rz.rzLOWER_of_rest hL) (Pp.ppL_lt_succ n).le
    (Cv.cvNoPair_of_nu hl e ((Pp.ppL_lt_omega (n + 1)).le.trans hlow))
    (fun y hy => ⟨_, hy, hb.le, hR⟩) (hn n)

/-- **`m* ≤₁ L(1)` from `LrGap` above `υ_{m*+ε_{Γ_{m*+1}+ω}}`.** -/
theorem teMW_of_gap (h0 : LrGap S (Nc.ncL S 0) (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + teW (Nc.ncL S 0)))) :
    le1 (Nc.ncL S 0) (Nc.ncL S 1) := by
  have hν := Sh.shNu hU hV hVt hL
  have hlow : Nc.ncL S ω ≤ nuC := (Qq.qqL_lt_succ S).le.trans hν
  obtain ⟨hR, hb⟩ := teRealW_M hlow hU hL (Tp.tpStdPairTop hν)
  obtain ⟨l, hl, e⟩ := Cv.cvM_restart (S := S)
  exact Ls.lsLe1_of_gapCof (Rz.rzLOWER_of_rest hL) (Rl.rlM_lt_L1 (S := S)).le
    (Cv.cvNoPair_of_nu hl e ((Pp.ppL_mono one_lt_omega0.le).trans hlow))
    (fun y hy => ⟨_, hy, hb.le, hR⟩) h0

/-- **(CL) at `n` iff no uncovered reach of `L(n+1)` in `[υ_{a+ε_{Γ_{a+1}+ω}}, L(n+2))`.** -/
theorem teCLW_iff_noUncov (n : ℕ) :
    le1 (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0})) ↔
      Tb.TbNoUncov S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
        (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + teW (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})))) := by
  constructor
  · rintro h ⟨r, hr, -, hrc, -⟩
    exact absurd (hr.2 _ h) (not_le.2 hrc)
  · intro h
    by_contra hf
    obtain ⟨r, hr⟩ := exists_reach (Pp.ppL_lt_succ n).le hf
    refine h ⟨r, hr, hr.2 _ (teShortW_L hU hV hVt hL n), ?_, fun l hl h1 h2 => ?_⟩
    · by_contra hge
      exact hf (le1_of_le_of_le1 (Pp.ppL_lt_succ n).le (not_lt.1 hge) hr.1)
    · by_contra hlt
      rw [not_le] at hlt
      have hl1 := le1_trans (le1_of_le_of_le1 h1 h2 hr.1) (Rz.rzLOWER_of_rest hL l hl)
      exact absurd (hr.2 _ hl1) (not_le.2 hlt)

/-- **`m* ≤₁ L(1)` iff no uncovered reach of `m*` in `[υ_{m*+ε_{Γ_{m*+1}+ω}}, L(1))`.** -/
theorem teMW_iff_noUncov :
    le1 (Nc.ncL S 0) (Nc.ncL S 1) ↔
      Tb.TbNoUncov S (Nc.ncL S 0) (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + teW (Nc.ncL S 0))) := by
  constructor
  · rintro h ⟨r, hr, -, hrc, -⟩
    exact absurd (hr.2 _ h) (not_le.2 hrc)
  · intro h
    by_contra hf
    obtain ⟨r, hr⟩ := exists_reach (Rl.rlM_lt_L1 (S := S)).le hf
    refine h ⟨r, hr, hr.2 _ (teShortW_M hU hV hVt hL), ?_, fun l hl h1 h2 => ?_⟩
    · by_contra hge
      exact hf (le1_of_le_of_le1 (Rl.rlM_lt_L1 (S := S)).le (not_lt.1 hge) hr.1)
    · by_contra hlt
      rw [not_le] at hlt
      have hl1 := le1_trans (le1_of_le_of_le1 h1 h2 hr.1) (Rz.rzLOWER_of_rest hL l hl)
      exact absurd (hr.2 _ hl1) (not_le.2 hlt)

/-- **(CL) and `m* ≤₁ L(1)` iff the `Tb.TbNoUncov` statements on `[υ_{a+ε_{Γ_{a+1}+ω}}, b)`.** -/
theorem teLongW_iff :
    (CdCL S ∧ le1 (Nc.ncL S 0) (Nc.ncL S 1)) ↔
      (Tb.TbNoUncov S (Nc.ncL S 0) (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + teW (Nc.ncL S 0))) ∧
        ∀ n : ℕ, Tb.TbNoUncov S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
          (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + teW (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))) := by
  constructor
  · rintro ⟨hCL, hM⟩
    exact ⟨(teMW_iff_noUncov hU hV hVt hL).1 hM, fun n => (teCLW_iff_noUncov hU hV hVt hL n).1 (hCL n)⟩
  · rintro ⟨hM, hn⟩
    exact ⟨fun n => (teCLW_iff_noUncov hU hV hVt hL n).2 (hn n), (teMW_iff_noUncov hU hV hVt hL).2 hM⟩

end Hyp

/-- **The road with the gaps only above `υ_{a+ε_{Γ_{a+1}+ω}}`.** -/
theorem teRoadW (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hEQ : Cx.CxEQtop S) (htop : Cx.CxTCtopOff S) (hmove : Cx.CxStdMoveTop S)
    (h0 : LrGap S (Nc.ncL S 0) (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + teW (Nc.ncL S 0))))
    (hn : ∀ n : ℕ, LrGap S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
      (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + teW (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))) :
    CdEQ S ∧ CdTC S ∧ CdEMB2 S ∧ Cx.CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  Sh.shRoad_CL hU hO hL hV hVt hEQ htop hmove (teMW_of_gap hU hV hVt hL h0) (teCLW_of_gap hU hV hVt hL hn)

/-- **The road with the `Tb.TbNoUncov` statements on `[υ_{a+ε_{Γ_{a+1}+ω}}, b)`** (no `LrGap`). -/
theorem teRoadWU (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hEQ : Cx.CxEQtop S) (htop : Cx.CxTCtopOff S) (hmove : Cx.CxStdMoveTop S)
    (h0 : Tb.TbNoUncov S (Nc.ncL S 0) (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + teW (Nc.ncL S 0))))
    (hn : ∀ n : ℕ, Tb.TbNoUncov S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
      (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + teW (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))) :
    CdEQ S ∧ CdTC S ∧ CdEMB2 S ∧ Cx.CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  obtain ⟨hCL, hM⟩ := (teLongW_iff hU hV hVt hL).2 ⟨h0, hn⟩
  exact Sh.shRoad_CL hU hO hL hV hVt hEQ htop hmove hM hCL

/-- **The statements on `[υ_{a+ε_{Γ_{a+1}+ω}}, b)` iff `L(k) ≤₁ ν_C` for every `k < ω`** (road hypotheses). -/
theorem teNoUncovW_iff_nu (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hEQ : Cx.CxEQtop S) (htop : Cx.CxTCtopOff S) (hmove : Cx.CxStdMoveTop S) :
    (Tb.TbNoUncov S (Nc.ncL S 0) (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + teW (Nc.ncL S 0))) ∧
        ∀ n : ℕ, Tb.TbNoUncov S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
          (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + teW (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))) ↔
      ∀ k : ℕ, le1 (Nc.ncL S (k : Ordinal.{0})) nuC :=
  (teLongW_iff hU hV hVt hL).symm.trans (teLong_iff_nu hU hO hL hV hVt hEQ htop hmove)

/-! ## Comparison with `Tb.tbRoadU` -/

/-- `TbNoUncov` is weaker on a shorter interval. -/
theorem teNoUncov_mono {a b c c' : Ordinal.{0}} (h : Tb.TbNoUncov S a b c) (hc : c ≤ c') :
    Tb.TbNoUncov S a b c' := fun ⟨r, hr, h1, h2, h3⟩ => h ⟨r, hr, hc.trans h1, h2, h3⟩

/-- **`υ_{a+ε_{Γ_{a+1}+1}} < υ_{a+ε_{Γ_{a+1}+ω}}`**: the interval left is strictly shorter. -/
theorem te_c0_lt_cw (a : Ordinal.{0}) : upsilon (a + eN (lgG a)) < upsilon (a + teW a) :=
  upsilon_normal.strictMono ((add_lt_add_iff_left a).2 (teW_gt a))

/-- **The statements of `Tb.tbRoadU` give those of `teRoadWU`.** -/
theorem teNoUncovW_of_0
    (h0 : Tb.TbNoUncov S (Nc.ncL S 0) (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + eN (lgG (Nc.ncL S 0)))))
    (hn : ∀ n : ℕ, Tb.TbNoUncov S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
      (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + eN (lgG (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})))))) :
    Tb.TbNoUncov S (Nc.ncL S 0) (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + teW (Nc.ncL S 0))) ∧
      ∀ n : ℕ, Tb.TbNoUncov S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
        (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + teW (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})))) :=
  ⟨teNoUncov_mono h0 (te_c0_lt_cw _).le, fun n => teNoUncov_mono (hn n) (te_c0_lt_cw _).le⟩

end Googology.Trans.PoR.InaccPsi.R2.Te
