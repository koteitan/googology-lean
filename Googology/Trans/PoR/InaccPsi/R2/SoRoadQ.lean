import Googology.Trans.PoR.InaccPsi.R2.SoRealQ

/-!
# (CL) and `m* ≤₁ L(1)` with the gaps asked only above `υ_{a+a^a}`, and the road

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.

`L(ξ) = Nc.ncL S ξ`, `m* = L(0)`, `a = L(n+1)` (or `m*`), (CL): `L(n+1) ≤₁ L(n+2)` for every `n`,
`Lr.LrGap S a b c`: realizers at the targets `y ≥ c` (`a ≤₁ y`) that no Range window `[υ_λ, r(λ))` covers.
The base-renaming realizers `So.soRealQ_L`, `So.soRealQ_M` (codes `a·J + p` with ordinal `J` carried by the
base change `π_{υ_μ,υ_λ}` on `seg(υ_λ)`) reach `υ_{a+a^a}`:

* `soShortQ_L`, `soShortQ_M` (**`a ≤₁ υ_{a+a^a}`** at every `L(n+1)` and at `m*`, from UPPER, CapV, LOWER);
* `soCL_of_gapQ`, `soM_of_gapQ` (**(CL) and `m* ≤₁ L(1)` from `LrGap` above `υ_{a+a^a}`**);
* `soRoad_Q` (**the road with the gaps above `υ_{a+a^a}` in place of (CL) and `m* ≤₁ L(1)`**);
* `soCL_fail_Q`, `soCL_iff_noUncovQ` (**(CL) at `n` iff `L(n+1)` has no reach `r` in `[υ_{a+a^a}, L(n+2))`
  that no window covers**), `soM_iff_noUncovQ` (the same for `m* ≤₁ L(1)`);
* `soGapQ_of_gapP` (the gaps above `υ_{a+a^ω}` give the gaps above `υ_{a+a^a}`: the new road asks less).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.So

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Lr

variable {S : InaccSeq.{0}}

/-- **`L(n+1) ≤₁ υ_{a+a^a}`** (`a = L(n+1)`) from UPPER, CapV, LOWER. -/
theorem soShortQ_L (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l) (n : ℕ) :
    le1 (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
      (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})
          ^ Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))) := by
  have hν := Sh.shNu hU hV hVt hL
  have hlow : Nc.ncL S ω ≤ nuC := (Qq.qqL_lt_succ S).le.trans hν
  obtain ⟨hR, hb⟩ := soRealQ_L hlow hU hL (Tp.tpStdPairTop hν) n
  obtain ⟨l, hl, e⟩ := Pp.ppL_succ_restart (S := S) n
  exact lrLe1_of_real (Rz.rzLOWER_of_rest hL) (le_self_add.trans upsilon_normal.strictMono.le_apply)
    (Cv.cvNoPair_of_nu hl e (hb.le.trans ((Pp.ppL_lt_omega (n + 1)).le.trans hlow))) hR

/-- **`m* ≤₁ υ_{m*+m*^{m*}}`** from UPPER, CapV, LOWER. -/
theorem soShortQ_M (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l) :
    le1 (Nc.ncL S 0) (upsilon (Nc.ncL S 0 + Nc.ncL S 0 ^ Nc.ncL S 0)) := by
  have hν := Sh.shNu hU hV hVt hL
  have hlow : Nc.ncL S ω ≤ nuC := (Qq.qqL_lt_succ S).le.trans hν
  obtain ⟨hR, hb⟩ := soRealQ_M hlow hU hL (Tp.tpStdPairTop hν)
  obtain ⟨l, hl, e⟩ := Cv.cvM_restart (S := S)
  exact lrLe1_of_real (Rz.rzLOWER_of_rest hL) (le_self_add.trans upsilon_normal.strictMono.le_apply)
    (Cv.cvNoPair_of_nu hl e (hb.le.trans ((Pp.ppL_mono one_lt_omega0.le).trans hlow))) hR

/-- **(CL) from UPPER, CapV, LOWER and `LrGap` above `υ_{a+a^a}` at every `L(n+1)`.** -/
theorem soCL_of_gapQ (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hn : ∀ n : ℕ, LrGap S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
      (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})
          ^ Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})))) :
    CdCL S := by
  have hν := Sh.shNu hU hV hVt hL
  have hlow : Nc.ncL S ω ≤ nuC := (Qq.qqL_lt_succ S).le.trans hν
  intro n
  obtain ⟨hR, hb⟩ := soRealQ_L hlow hU hL (Tp.tpStdPairTop hν) n
  obtain ⟨l, hl, e⟩ := Pp.ppL_succ_restart (S := S) n
  exact Ls.lsLe1_of_gapCof (Rz.rzLOWER_of_rest hL) (Pp.ppL_lt_succ n).le
    (Cv.cvNoPair_of_nu hl e ((Pp.ppL_lt_omega (n + 1)).le.trans hlow))
    (fun y hy => ⟨_, hy, hb.le, hR⟩) (hn n)

/-- **`m* ≤₁ L(1)` from UPPER, CapV, LOWER and `LrGap` above `υ_{m*+m*^{m*}}`.** -/
theorem soM_of_gapQ (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (h0 : LrGap S (Nc.ncL S 0) (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Nc.ncL S 0 ^ Nc.ncL S 0))) :
    le1 (Nc.ncL S 0) (Nc.ncL S 1) := by
  have hν := Sh.shNu hU hV hVt hL
  have hlow : Nc.ncL S ω ≤ nuC := (Qq.qqL_lt_succ S).le.trans hν
  obtain ⟨hR, hb⟩ := soRealQ_M hlow hU hL (Tp.tpStdPairTop hν)
  obtain ⟨l, hl, e⟩ := Cv.cvM_restart (S := S)
  exact Ls.lsLe1_of_gapCof (Rz.rzLOWER_of_rest hL) (Rl.rlM_lt_L1 (S := S)).le
    (Cv.cvNoPair_of_nu hl e ((Pp.ppL_mono one_lt_omega0.le).trans hlow))
    (fun y hy => ⟨_, hy, hb.le, hR⟩) h0

/-- **The road with the gaps above `υ_{a+a^a}`** (at `m*` and every `L(n+1)`) in place of (CL)
and `m* ≤₁ L(1)` (`Sh.shRoad_CL`). -/
theorem soRoad_Q (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hEQ : Cx.CxEQtop S) (htop : Cx.CxTCtopOff S) (hmove : Cx.CxStdMoveTop S)
    (h0 : LrGap S (Nc.ncL S 0) (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Nc.ncL S 0 ^ Nc.ncL S 0)))
    (hn : ∀ n : ℕ, LrGap S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
      (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})
          ^ Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})))) :
    CdEQ S ∧ CdTC S ∧ CdEMB2 S ∧ Cx.CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  Sh.shRoad_CL hU hO hL hV hVt hEQ htop hmove (soM_of_gapQ hU hV hVt hL h0)
    (soCL_of_gapQ hU hV hVt hL hn)

/-- **The shape of a failure of (CL) at `n`, above `υ_{a+a^a}`**: `L(n+1)` has a reach `r` with
`υ_{a+a^a} ≤ r < L(n+2)` that no window `[υ_λ, r(λ))` (`λ` a Range restart, `a ≤ υ_λ ≤ r`) covers. -/
theorem soCL_fail_Q (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l) (n : ℕ)
    (hf : ¬ le1 (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))) :
    ∃ r, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) r ∧
      upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})
          ^ Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) ≤ r ∧
      r < Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}) ∧
      ∀ l, CdRange S l → Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) ≤ upsilon l → upsilon l ≤ r →
        cdR S l ≤ r := by
  obtain ⟨r, hr⟩ := exists_reach (Pp.ppL_lt_succ n).le hf
  refine ⟨r, hr, hr.2 _ (soShortQ_L hU hV hVt hL n), ?_, fun l hl h1 h2 => ?_⟩
  · by_contra hge
    exact hf (le1_of_le_of_le1 (Pp.ppL_lt_succ n).le (not_lt.1 hge) hr.1)
  · by_contra hlt
    rw [not_le] at hlt
    have hl1 := le1_trans (le1_of_le_of_le1 h1 h2 hr.1) (Rz.rzLOWER_of_rest hL l hl)
    exact absurd (hr.2 _ hl1) (not_le.2 hlt)

/-- **(CL) at `n` iff no uncovered reach of `L(n+1)` in `[υ_{a+a^a}, L(n+2))`** (UPPER, CapV, LOWER). -/
theorem soCL_iff_noUncovQ (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l) (n : ℕ) :
    le1 (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0})) ↔
      ¬ ∃ r, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) r ∧
        upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})
            ^ Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) ≤ r ∧
        r < Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}) ∧
        ∀ l, CdRange S l → Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) ≤ upsilon l → upsilon l ≤ r →
          cdR S l ≤ r := by
  constructor
  · rintro h ⟨r, hr, -, hrc, -⟩
    exact absurd (hr.2 _ h) (not_le.2 hrc)
  · intro h
    by_contra hf
    exact h (soCL_fail_Q hU hV hVt hL n hf)

/-- **`m* ≤₁ L(1)` iff no uncovered reach of `m*` in `[υ_{m*+m*^{m*}}, L(1))`** (UPPER, CapV, LOWER). -/
theorem soM_iff_noUncovQ (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l) :
    le1 (Nc.ncL S 0) (Nc.ncL S 1) ↔
      ¬ ∃ r, IsReach R2C (Nc.ncL S 0) r ∧ upsilon (Nc.ncL S 0 + Nc.ncL S 0 ^ Nc.ncL S 0) ≤ r ∧
        r < Nc.ncL S 1 ∧
        ∀ l, CdRange S l → Nc.ncL S 0 ≤ upsilon l → upsilon l ≤ r → cdR S l ≤ r := by
  constructor
  · rintro h ⟨r, hr, -, hrc, -⟩
    exact absurd (hr.2 _ h) (not_le.2 hrc)
  · intro h
    by_contra hf
    obtain ⟨r, hr⟩ := exists_reach (Rl.rlM_lt_L1 (S := S)).le hf
    refine h ⟨r, hr, hr.2 _ (soShortQ_M hU hV hVt hL), ?_, fun l hl h1 h2 => ?_⟩
    · by_contra hge
      exact hf (le1_of_le_of_le1 (Rl.rlM_lt_L1 (S := S)).le (not_lt.1 hge) hr.1)
    · by_contra hlt
      rw [not_le] at hlt
      have hl1 := le1_trans (le1_of_le_of_le1 h1 h2 hr.1) (Rz.rzLOWER_of_rest hL l hl)
      exact absurd (hr.2 _ hl1) (not_le.2 hlt)

/-- `υ_{a+a^ω} ≤ υ_{a+a^a}` for an `ε`-number `a`. -/
theorem soP_le_Q {a : Ordinal.{0}} (ha : InE a) : upsilon (a + a ^ ω) ≤ upsilon (a + a ^ a) :=
  upsilon_normal.strictMono.monotone (add_le_add le_rfl
    (opow_le_opow_right ha.pos (Sl.slE_omega_lt ha).le))

/-- **The gaps above `υ_{a+a^ω}` give the gaps above `υ_{a+a^a}`.** -/
theorem soGapQ_of_gapP {a b : Ordinal.{0}} (ha : InE a) (h : LrGap S a b (upsilon (a + a ^ ω))) :
    LrGap S a b (upsilon (a + a ^ a)) :=
  Ls.lsGap_mono (soP_le_Q ha) h

end Googology.Trans.PoR.InaccPsi.R2.So
