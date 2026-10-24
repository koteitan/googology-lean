import Googology.Trans.PoR.InaccPsi.R2.SuReal

/-!
# (CL) and `m* ≤₁ L(1)` with the gaps asked only above `υ_{a+V(a)}`, for any offset code system

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.

`K : SuCS`, `L(ξ) = Nc.ncL S ξ`, `m* = L(0)`, `a = L(n+1)` (or `m*`), (CL): `L(n+1) ≤₁ L(n+2)` for every `n`,
`Lr.LrGap S a b c`: realizers at the targets `y ≥ c` (`a ≤₁ y`) that no Range window `[υ_λ, r(λ))` covers.
The realizers `Su.suReal_L`, `Su.suReal_M` reach `υ_{a+V(a)}`:

* `suShort_L`, `suShort_M` (**`a ≤₁ υ_{a+V(a)}`** at every `L(n+1)` and at `m*`);
* `suCL_of_gap`, `suM_of_gap` (**(CL) and `m* ≤₁ L(1)` from `LrGap` above `υ_{a+V(a)}`**);
* `suRoad` (**the road with the gaps above `υ_{a+V(a)}` in place of (CL) and `m* ≤₁ L(1)`**);
* `suCL_fail`, `suCL_iff_noUncov` (**(CL) at `n` iff `L(n+1)` has no reach `r` in `[υ_{a+V(a)}, L(n+2))` that no
  window covers**), `suM_iff_noUncov`;
* `suE_le_V`, `suGap_of_gapE` (the gaps above `υ_{a+ε_{a+1}}` give the gaps above `υ_{a+V(a)}`: the road asks no
  more than `Sr.srRoad_E`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Su

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Lr

variable {S : InaccSeq.{0}}

/-- **`L(n+1) ≤₁ υ_{a+V(a)}`** (`a = L(n+1)`) from UPPER, CapV, LOWER. -/
theorem suShort_L (K : SuCS) (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l) (n : ℕ) :
    le1 (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
      (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + K.V (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})))) := by
  have hν := Sh.shNu hU hV hVt hL
  have hlow : Nc.ncL S ω ≤ nuC := (Qq.qqL_lt_succ S).le.trans hν
  obtain ⟨hR, hb⟩ := suReal_L K hlow hU hL (Tp.tpStdPairTop hν) n
  obtain ⟨l, hl, e⟩ := Pp.ppL_succ_restart (S := S) n
  exact lrLe1_of_real (Rz.rzLOWER_of_rest hL) (le_self_add.trans upsilon_normal.strictMono.le_apply)
    (Cv.cvNoPair_of_nu hl e (hb.le.trans ((Pp.ppL_lt_omega (n + 1)).le.trans hlow))) hR

/-- **`m* ≤₁ υ_{m*+V(m*)}`** from UPPER, CapV, LOWER. -/
theorem suShort_M (K : SuCS) (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l) :
    le1 (Nc.ncL S 0) (upsilon (Nc.ncL S 0 + K.V (Nc.ncL S 0))) := by
  have hν := Sh.shNu hU hV hVt hL
  have hlow : Nc.ncL S ω ≤ nuC := (Qq.qqL_lt_succ S).le.trans hν
  obtain ⟨hR, hb⟩ := suReal_M K hlow hU hL (Tp.tpStdPairTop hν)
  obtain ⟨l, hl, e⟩ := Cv.cvM_restart (S := S)
  exact lrLe1_of_real (Rz.rzLOWER_of_rest hL) (le_self_add.trans upsilon_normal.strictMono.le_apply)
    (Cv.cvNoPair_of_nu hl e (hb.le.trans ((Pp.ppL_mono one_lt_omega0.le).trans hlow))) hR

/-- **(CL) from UPPER, CapV, LOWER and `LrGap` above `υ_{a+V(a)}` at every `L(n+1)`.** -/
theorem suCL_of_gap (K : SuCS) (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hn : ∀ n : ℕ, LrGap S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
      (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + K.V (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))) :
    CdCL S := by
  have hν := Sh.shNu hU hV hVt hL
  have hlow : Nc.ncL S ω ≤ nuC := (Qq.qqL_lt_succ S).le.trans hν
  intro n
  obtain ⟨hR, hb⟩ := suReal_L K hlow hU hL (Tp.tpStdPairTop hν) n
  obtain ⟨l, hl, e⟩ := Pp.ppL_succ_restart (S := S) n
  exact Ls.lsLe1_of_gapCof (Rz.rzLOWER_of_rest hL) (Pp.ppL_lt_succ n).le
    (Cv.cvNoPair_of_nu hl e ((Pp.ppL_lt_omega (n + 1)).le.trans hlow))
    (fun y hy => ⟨_, hy, hb.le, hR⟩) (hn n)

/-- **`m* ≤₁ L(1)` from UPPER, CapV, LOWER and `LrGap` above `υ_{m*+V(m*)}`.** -/
theorem suM_of_gap (K : SuCS) (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (h0 : LrGap S (Nc.ncL S 0) (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + K.V (Nc.ncL S 0)))) :
    le1 (Nc.ncL S 0) (Nc.ncL S 1) := by
  have hν := Sh.shNu hU hV hVt hL
  have hlow : Nc.ncL S ω ≤ nuC := (Qq.qqL_lt_succ S).le.trans hν
  obtain ⟨hR, hb⟩ := suReal_M K hlow hU hL (Tp.tpStdPairTop hν)
  obtain ⟨l, hl, e⟩ := Cv.cvM_restart (S := S)
  exact Ls.lsLe1_of_gapCof (Rz.rzLOWER_of_rest hL) (Rl.rlM_lt_L1 (S := S)).le
    (Cv.cvNoPair_of_nu hl e ((Pp.ppL_mono one_lt_omega0.le).trans hlow))
    (fun y hy => ⟨_, hy, hb.le, hR⟩) h0

/-- **The road with the gaps above `υ_{a+V(a)}`** (at `m*` and every `L(n+1)`) in place of (CL) and
`m* ≤₁ L(1)` (`Sh.shRoad_CL`). -/
theorem suRoad (K : SuCS) (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hEQ : Cx.CxEQtop S) (htop : Cx.CxTCtopOff S) (hmove : Cx.CxStdMoveTop S)
    (h0 : LrGap S (Nc.ncL S 0) (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + K.V (Nc.ncL S 0))))
    (hn : ∀ n : ℕ, LrGap S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
      (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + K.V (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))) :
    CdEQ S ∧ CdTC S ∧ CdEMB2 S ∧ Cx.CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  Sh.shRoad_CL hU hO hL hV hVt hEQ htop hmove (suM_of_gap K hU hV hVt hL h0)
    (suCL_of_gap K hU hV hVt hL hn)

/-- **The shape of a failure of (CL) at `n`, above `υ_{a+V(a)}`.** -/
theorem suCL_fail (K : SuCS) (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l) (n : ℕ)
    (hf : ¬ le1 (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))) :
    ∃ r, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) r ∧
      upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + K.V (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))) ≤ r ∧
      r < Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}) ∧
      ∀ l, CdRange S l → Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) ≤ upsilon l → upsilon l ≤ r →
        cdR S l ≤ r := by
  obtain ⟨r, hr⟩ := exists_reach (Pp.ppL_lt_succ n).le hf
  refine ⟨r, hr, hr.2 _ (suShort_L K hU hV hVt hL n), ?_, fun l hl h1 h2 => ?_⟩
  · by_contra hge
    exact hf (le1_of_le_of_le1 (Pp.ppL_lt_succ n).le (not_lt.1 hge) hr.1)
  · by_contra hlt
    rw [not_le] at hlt
    have hl1 := le1_trans (le1_of_le_of_le1 h1 h2 hr.1) (Rz.rzLOWER_of_rest hL l hl)
    exact absurd (hr.2 _ hl1) (not_le.2 hlt)

/-- **(CL) at `n` iff no uncovered reach of `L(n+1)` in `[υ_{a+V(a)}, L(n+2))`** (UPPER, CapV, LOWER). -/
theorem suCL_iff_noUncov (K : SuCS) (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l) (n : ℕ) :
    le1 (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0})) ↔
      ¬ ∃ r, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) r ∧
        upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + K.V (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))) ≤ r ∧
        r < Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}) ∧
        ∀ l, CdRange S l → Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) ≤ upsilon l → upsilon l ≤ r →
          cdR S l ≤ r := by
  constructor
  · rintro h ⟨r, hr, -, hrc, -⟩
    exact absurd (hr.2 _ h) (not_le.2 hrc)
  · intro h
    by_contra hf
    exact h (suCL_fail K hU hV hVt hL n hf)

/-- **`m* ≤₁ L(1)` iff no uncovered reach of `m*` in `[υ_{m*+V(m*)}, L(1))`** (UPPER, CapV, LOWER). -/
theorem suM_iff_noUncov (K : SuCS) (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l) :
    le1 (Nc.ncL S 0) (Nc.ncL S 1) ↔
      ¬ ∃ r, IsReach R2C (Nc.ncL S 0) r ∧ upsilon (Nc.ncL S 0 + K.V (Nc.ncL S 0)) ≤ r ∧
        r < Nc.ncL S 1 ∧
        ∀ l, CdRange S l → Nc.ncL S 0 ≤ upsilon l → upsilon l ≤ r → cdR S l ≤ r := by
  constructor
  · rintro h ⟨r, hr, -, hrc, -⟩
    exact absurd (hr.2 _ h) (not_le.2 hrc)
  · intro h
    by_contra hf
    obtain ⟨r, hr⟩ := exists_reach (Rl.rlM_lt_L1 (S := S)).le hf
    refine h ⟨r, hr, hr.2 _ (suShort_M K hU hV hVt hL), ?_, fun l hl h1 h2 => ?_⟩
    · by_contra hge
      exact hf (le1_of_le_of_le1 (Rl.rlM_lt_L1 (S := S)).le (not_lt.1 hge) hr.1)
    · by_contra hlt
      rw [not_le] at hlt
      have hl1 := le1_trans (le1_of_le_of_le1 h1 h2 hr.1) (Rz.rzLOWER_of_rest hL l hl)
      exact absurd (hr.2 _ hl1) (not_le.2 hlt)

/-- `ε_{a+1} ≤ V(a)` for an `ε`-number `a < Ω₁`. -/
theorem suE_le_V (K : SuCS) {a : Ordinal.{0}} (haE : InE a) (ha1 : a < Om1) : eN a ≤ K.V a :=
  eN_le (K.V_gt a haE ha1) (K.V_E a haE ha1)

/-- **The gaps above `υ_{a+ε_{a+1}}` give the gaps above `υ_{a+V(a)}`.** -/
theorem suGap_of_gapE (K : SuCS) {a b : Ordinal.{0}} (haE : InE a) (ha1 : a < Om1)
    (h : LrGap S a b (upsilon (a + eN a))) : LrGap S a b (upsilon (a + K.V a)) :=
  Ls.lsGap_mono (upsilon_normal.strictMono.monotone (add_le_add le_rfl (suE_le_V K haE ha1))) h

end Googology.Trans.PoR.InaccPsi.R2.Su
