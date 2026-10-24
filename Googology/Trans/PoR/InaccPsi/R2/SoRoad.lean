import Googology.Trans.PoR.InaccPsi.R2.SoReal

/-!
# (CL) and `m* ≤₁ L(1)` with the gaps asked only above `υ_{a+a^ω}`, and the road, with no supply hypothesis

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.

`L(ξ) = Nc.ncL S ξ`, `m* = L(0)`, `a = L(n+1)` (or `m*`), (CL): `L(n+1) ≤₁ L(n+2)` for every `n`,
`Lr.LrGap S a b c`: realizers at the targets `y ≥ c` (`a ≤₁ y`) that no Range window `[υ_λ, r(λ))` covers.
The round-86 roads (`Sl.slRoad_W`) asked the supply `Sl.SlSupW S k` and the gaps above `υ_{a+a·ω}`.  The supply
is now a theorem (`So.soSupW`), and the polynomial realizers `So.soReal_L`, `So.soReal_M` reach `υ_{a+a^ω}`:

* `soShort_L`, `soShort_M` (**`a ≤₁ υ_{a+a^ω}`** at every `L(n+1)` and at `m*`, from UPPER, CapV, LOWER);
* `soCL_of_gapP`, `soM_of_gapP` (**(CL) and `m* ≤₁ L(1)` from `LrGap` above `υ_{a+a^ω}`**);
* `soRoad_P` (**the road with the gaps above `υ_{a+a^ω}` in place of (CL) and `m* ≤₁ L(1)`**), `soRoad_W`
  (`Sl.slRoad_W` without `SlSupW`);
* `soCL_fail_P`, `soCL_iff_noUncovP` (**(CL) at `n` iff `L(n+1)` has no reach `r` in `[υ_{a+a^ω}, L(n+2))`
  that no window covers**), `soM_iff_noUncovP` (the same for `m* ≤₁ L(1)`), `soCL_iff_noUncovW` (the round-86
  form without `SlSupW`);
* `soGapP_of_gapW` (the gaps above `υ_{a+a·ω}` give the gaps above `υ_{a+a^ω}`: the new road asks less).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.So

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Lr

variable {S : InaccSeq.{0}}

/-- **`L(n+1) ≤₁ υ_{a+a^ω}`** (`a = L(n+1)`) from UPPER, CapV, LOWER. -/
theorem soShort_L (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l) (n : ℕ) :
    le1 (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
      (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) ^ ω)) := by
  have hν := Sh.shNu hU hV hVt hL
  have hlow : Nc.ncL S ω ≤ nuC := (Qq.qqL_lt_succ S).le.trans hν
  obtain ⟨hR, hb⟩ := soReal_L hlow hU hL (Tp.tpStdPairTop hν) n
  obtain ⟨l, hl, e⟩ := Pp.ppL_succ_restart (S := S) n
  exact lrLe1_of_real (Rz.rzLOWER_of_rest hL) (le_self_add.trans upsilon_normal.strictMono.le_apply)
    (Cv.cvNoPair_of_nu hl e (hb.le.trans ((Pp.ppL_lt_omega (n + 1)).le.trans hlow))) hR

/-- **`m* ≤₁ υ_{m*+m*^ω}`** from UPPER, CapV, LOWER. -/
theorem soShort_M (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l) :
    le1 (Nc.ncL S 0) (upsilon (Nc.ncL S 0 + Nc.ncL S 0 ^ ω)) := by
  have hν := Sh.shNu hU hV hVt hL
  have hlow : Nc.ncL S ω ≤ nuC := (Qq.qqL_lt_succ S).le.trans hν
  obtain ⟨hR, hb⟩ := soReal_M hlow hU hL (Tp.tpStdPairTop hν)
  obtain ⟨l, hl, e⟩ := Cv.cvM_restart (S := S)
  exact lrLe1_of_real (Rz.rzLOWER_of_rest hL) (le_self_add.trans upsilon_normal.strictMono.le_apply)
    (Cv.cvNoPair_of_nu hl e (hb.le.trans ((Pp.ppL_mono one_lt_omega0.le).trans hlow))) hR

/-- **(CL) from UPPER, CapV, LOWER and `LrGap` above `υ_{a+a^ω}` at every `L(n+1)`.** -/
theorem soCL_of_gapP (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hn : ∀ n : ℕ, LrGap S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
      (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) ^ ω))) :
    CdCL S := by
  have hν := Sh.shNu hU hV hVt hL
  have hlow : Nc.ncL S ω ≤ nuC := (Qq.qqL_lt_succ S).le.trans hν
  intro n
  obtain ⟨hR, hb⟩ := soReal_L hlow hU hL (Tp.tpStdPairTop hν) n
  obtain ⟨l, hl, e⟩ := Pp.ppL_succ_restart (S := S) n
  exact Ls.lsLe1_of_gapCof (Rz.rzLOWER_of_rest hL) (Pp.ppL_lt_succ n).le
    (Cv.cvNoPair_of_nu hl e ((Pp.ppL_lt_omega (n + 1)).le.trans hlow))
    (fun y hy => ⟨_, hy, hb.le, hR⟩) (hn n)

/-- **`m* ≤₁ L(1)` from UPPER, CapV, LOWER and `LrGap` above `υ_{m*+m*^ω}`.** -/
theorem soM_of_gapP (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (h0 : LrGap S (Nc.ncL S 0) (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Nc.ncL S 0 ^ ω))) :
    le1 (Nc.ncL S 0) (Nc.ncL S 1) := by
  have hν := Sh.shNu hU hV hVt hL
  have hlow : Nc.ncL S ω ≤ nuC := (Qq.qqL_lt_succ S).le.trans hν
  obtain ⟨hR, hb⟩ := soReal_M hlow hU hL (Tp.tpStdPairTop hν)
  obtain ⟨l, hl, e⟩ := Cv.cvM_restart (S := S)
  exact Ls.lsLe1_of_gapCof (Rz.rzLOWER_of_rest hL) (Rl.rlM_lt_L1 (S := S)).le
    (Cv.cvNoPair_of_nu hl e ((Pp.ppL_mono one_lt_omega0.le).trans hlow))
    (fun y hy => ⟨_, hy, hb.le, hR⟩) h0

/-- **The road with the gaps above `υ_{a+a^ω}`** (at `m*` and every `L(n+1)`) in place of (CL)
and `m* ≤₁ L(1)` (`Sh.shRoad_CL`). -/
theorem soRoad_P (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hEQ : Cx.CxEQtop S) (htop : Cx.CxTCtopOff S) (hmove : Cx.CxStdMoveTop S)
    (h0 : LrGap S (Nc.ncL S 0) (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Nc.ncL S 0 ^ ω)))
    (hn : ∀ n : ℕ, LrGap S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
      (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) ^ ω))) :
    CdEQ S ∧ CdTC S ∧ CdEMB2 S ∧ Cx.CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  Sh.shRoad_CL hU hO hL hV hVt hEQ htop hmove (soM_of_gapP hU hV hVt hL h0)
    (soCL_of_gapP hU hV hVt hL hn)

/-- **The shape of a failure of (CL) at `n`, above `υ_{a+a^ω}`**: `L(n+1)` has a reach `r` with
`υ_{a+a^ω} ≤ r < L(n+2)` that no window `[υ_λ, r(λ))` (`λ` a Range restart, `a ≤ υ_λ ≤ r`) covers. -/
theorem soCL_fail_P (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l) (n : ℕ)
    (hf : ¬ le1 (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))) :
    ∃ r, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) r ∧
      upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) ^ ω) ≤ r ∧
      r < Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}) ∧
      ∀ l, CdRange S l → Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) ≤ upsilon l → upsilon l ≤ r →
        cdR S l ≤ r := by
  obtain ⟨r, hr⟩ := exists_reach (Pp.ppL_lt_succ n).le hf
  refine ⟨r, hr, hr.2 _ (soShort_L hU hV hVt hL n), ?_, fun l hl h1 h2 => ?_⟩
  · by_contra hge
    exact hf (le1_of_le_of_le1 (Pp.ppL_lt_succ n).le (not_lt.1 hge) hr.1)
  · by_contra hlt
    rw [not_le] at hlt
    have hl1 := le1_trans (le1_of_le_of_le1 h1 h2 hr.1) (Rz.rzLOWER_of_rest hL l hl)
    exact absurd (hr.2 _ hl1) (not_le.2 hlt)

/-- **(CL) at `n` iff no uncovered reach of `L(n+1)` in `[υ_{a+a^ω}, L(n+2))`** (UPPER, CapV, LOWER). -/
theorem soCL_iff_noUncovP (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l) (n : ℕ) :
    le1 (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0})) ↔
      ¬ ∃ r, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) r ∧
        upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) ^ ω) ≤ r ∧
        r < Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}) ∧
        ∀ l, CdRange S l → Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) ≤ upsilon l → upsilon l ≤ r →
          cdR S l ≤ r := by
  constructor
  · rintro h ⟨r, hr, -, hrc, -⟩
    exact absurd (hr.2 _ h) (not_le.2 hrc)
  · intro h
    by_contra hf
    exact h (soCL_fail_P hU hV hVt hL n hf)

/-- **`m* ≤₁ L(1)` iff no uncovered reach of `m*` in `[υ_{m*+m*^ω}, L(1))`** (UPPER, CapV, LOWER). -/
theorem soM_iff_noUncovP (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l) :
    le1 (Nc.ncL S 0) (Nc.ncL S 1) ↔
      ¬ ∃ r, IsReach R2C (Nc.ncL S 0) r ∧ upsilon (Nc.ncL S 0 + Nc.ncL S 0 ^ ω) ≤ r ∧
        r < Nc.ncL S 1 ∧
        ∀ l, CdRange S l → Nc.ncL S 0 ≤ upsilon l → upsilon l ≤ r → cdR S l ≤ r := by
  constructor
  · rintro h ⟨r, hr, -, hrc, -⟩
    exact absurd (hr.2 _ h) (not_le.2 hrc)
  · intro h
    by_contra hf
    obtain ⟨r, hr⟩ := exists_reach (Rl.rlM_lt_L1 (S := S)).le hf
    refine h ⟨r, hr, hr.2 _ (soShort_M hU hV hVt hL), ?_, fun l hl h1 h2 => ?_⟩
    · by_contra hge
      exact hf (le1_of_le_of_le1 (Rl.rlM_lt_L1 (S := S)).le (not_lt.1 hge) hr.1)
    · by_contra hlt
      rw [not_le] at hlt
      have hl1 := le1_trans (le1_of_le_of_le1 h1 h2 hr.1) (Rz.rzLOWER_of_rest hL l hl)
      exact absurd (hr.2 _ hl1) (not_le.2 hlt)

/-- **`Sl.slRoad_W` without the supply hypothesis** (`So.soSupW`). -/
theorem soRoad_W (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hEQ : Cx.CxEQtop S) (htop : Cx.CxTCtopOff S) (hmove : Cx.CxStdMoveTop S)
    (h0 : LrGap S (Nc.ncL S 0) (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Nc.ncL S 0 * ω)))
    (hn : ∀ n : ℕ, LrGap S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
      (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) * ω))) :
    CdEQ S ∧ CdTC S ∧ CdEMB2 S ∧ Cx.CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  Sl.slRoad_W (k := 0) hU hO hL hV hVt hEQ htop hmove (soSupW 0) h0 hn

/-- **(CL) at `n` iff no uncovered reach of `L(n+1)` in `[υ_{a+a·ω}, L(n+2))`**, without `SlSupW`. -/
theorem soCL_iff_noUncovW (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l) (n : ℕ) :
    le1 (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0})) ↔
      ¬ ∃ r, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) r ∧
        upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) * ω) ≤ r ∧
        r < Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}) ∧
        ∀ l, CdRange S l → Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) ≤ upsilon l → upsilon l ≤ r →
          cdR S l ≤ r :=
  Sl.slCL_iff_noUncovW (k := 0) hU hV hVt hL (soSupW 0) n

/-- `υ_{a+a·ω} ≤ υ_{a+a^ω}` for `a > 1`. -/
theorem soW_le_P {a : Ordinal.{0}} (h : 1 < a) : upsilon (a + a * ω) ≤ upsilon (a + a ^ ω) := by
  refine upsilon_normal.strictMono.monotone (add_le_add le_rfl ?_)
  calc a * ω ≤ a ^ (1 : Ordinal.{0}) * a ^ ω := by
        rw [opow_one]; exact mul_le_mul_of_nonneg_left (right_le_opow ω h) zero_le
    _ = a ^ ω := by rw [← opow_add, one_add_omega0]

/-- **The gaps above `υ_{a+a·ω}` give the gaps above `υ_{a+a^ω}`.** -/
theorem soGapP_of_gapW {a b : Ordinal.{0}} (ha : 1 < a) (h : LrGap S a b (upsilon (a + a * ω))) :
    LrGap S a b (upsilon (a + a ^ ω)) :=
  Ls.lsGap_mono (soW_le_P ha) h

end Googology.Trans.PoR.InaccPsi.R2.So
