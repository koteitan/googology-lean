import Googology.Trans.PoR.InaccPsi.R2.ShNu

/-!
# (CL) after `L(ω+1) ≤ ν_C`: the short part, the tail that `T` needs, and the shape of a failure

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.

`L(ξ) = Nc.ncL S ξ`, `a = L(n+1) = Bc.bcC S n`, (CL): `L(n+1) ≤₁ L(n+2)` for every `n`, `T`: `L(ω) ≤₁ L(ω+1)`,
`r(λ) = Cd.cdR S λ`.  With `L(ω+1) ≤ ν_C` now a theorem of the road's hypotheses (`Sh.shNu`):

* `shCL_short` (**`L(n+1) ≤₁ υ_{L(n+1)+L(n+1)}` for every `n`, from UPPER, CapV and LOWER**: the realizers of
  `Ra.raNamed_R` with `CxStdPairTop` from `L(ω+1) ≤ ν_C`, and `CvNoPair` below `ν_C`);
* `shCL_of_gap` (`Sd.sdCL_of_gap` without the hypothesis `L(ω+1) ≤ ν_C`);
* `shT_of_CLtail` (**`T` from the road's hypotheses and (CL) only for `n ≥ N₀`**, no `LrGap` at all),
  `shT_of_gapLw` (**`T` from the road's hypotheses and `LrGap` at `L(ω)` only**);
* `shCL_iff_Lw` ((CL) iff every `L(n+1) ≤₁ L(ω)`), `shCL_iff_reflBase` (under `T`, (CL) iff `B_n` reflects
  `≤₁` at its base point for every `n`);
* `shCL_fail` (**the shape of a failure of (CL) at `n`**: the reach `r` of `L(n+1)` exists, lies in
  `[υ_{a+a}, L(n+2))`, and no range restart `λ` with `a ≤ υ_λ ≤ r` has `r < r(λ)`: `r` is a target that no
  window `[υ_λ, r(λ))` covers, i.e. exactly a target of `LrGap`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Sh

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- **(CL) iff every `L(n+1) ≤₁ L(ω)`.** -/
theorem shCL_iff_Lw :
    CdCL S ↔ ∀ n : ℕ, le1 (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S ω) := by
  constructor
  · intro hCL n
    have hch : ∀ k, n ≤ k →
        le1 (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) := by
      intro k hk
      induction k, hk using Nat.le_induction with
      | base => exact le1_refl _
      | succ k _ ih => exact le1_trans ih (hCL k)
    refine le1_of_cofinal (Pp.ppL_lt_omega n).le fun y _ hy => ?_
    obtain ⟨k, hk⟩ := Pp.ppL_cof (S := S) y hy
    refine ⟨Nc.ncL S ((max k n + 1 : ℕ) : Ordinal.{0}),
      hk.trans_le (Pp.ppL_mono (Nat.cast_le.2 (Nat.succ_le_succ (le_max_left k n)))),
      hch _ (le_max_right _ _)⟩
  · intro h n
    exact le1_of_le_of_le1 (Pp.ppL_lt_succ n).le (Pp.ppL_lt_omega (n + 1)).le (h n)

/-- **Under `T`, (CL) iff `B_n` reflects `≤₁` at its base point for every `n`.** -/
theorem shCL_iff_reflBase (hT : Cx.CxT S) : CdCL S ↔ ∀ n : ℕ, Sd.SdR1Base S n :=
  ⟨fun h n => (Sd.sdR1Base_iff_CL hT n).2 (h n), fun h n => (Sd.sdR1Base_iff_CL hT n).1 (h n)⟩

/-- `υ_{L(n+1)+L(n+1)} ≤ L(n+2)`. -/
theorem shAA_le (n : ℕ) :
    upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) ≤
      Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}) := by
  obtain ⟨hg, hι, hP, -, -, -⟩ := Ls.lsL_named (S := S) n
  have := Ls.lsAA_le hg hι hP
  have e : Om ω + Nc.ncPp S * ((n + 1 : ℕ) : Ordinal.{0}) + Nc.ncPp S =
      Om ω + Nc.ncPp S * ((n + 2 : ℕ) : Ordinal.{0}) := (Rm.rm_eta_succ (S := S) (n + 1)).symm
  rwa [e, ← Lw.lw_L_eq] at this

/-- **The short part of (CL)**: `L(n+1) ≤₁ υ_{L(n+1)+L(n+1)}` for every `n`, from UPPER, CapV and LOWER. -/
theorem shCL_short (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l) (n : ℕ) :
    le1 (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
      (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))) := by
  have hν := shNu hU hV hVt hL
  have hlow : Nc.ncL S ω ≤ nuC := (Qq.qqL_lt_succ S).le.trans hν
  obtain ⟨-, rn⟩ := Ra.raNamed_R (S := S) hlow (Tp.tpStdPairTop hν) Rx.rxSupAt.1 Rx.rxSupAt.2 hU hL
  have hbν := (shAA_le (S := S) n).trans ((Pp.ppL_lt_omega (n + 1)).le.trans hlow)
  obtain ⟨l, hl, e⟩ := Pp.ppL_succ_restart (S := S) n
  have hab : Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) ≤
      upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) :=
    (upsilon_normal.strictMono.le_apply : Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) ≤ _).trans
      (upsilon_normal.strictMono.monotone le_self_add)
  refine Ls.lsLe1_of_gapCof (Rz.rzLOWER_of_rest hL) hab (Cv.cvNoPair_of_nu hl e hbν) (fun y hy => ?_)
    (fun y _ hcy hyb => absurd hyb (not_lt.2 hcy))
  obtain ⟨t, h1, -, h3⟩ := rn n y hy
  exact ⟨min t _, lt_min h1 hy, min_le_right _ _, Lr.lrReal_mono h3 (min_le_left _ _)⟩

/-- **(CL) from UPPER, LOWER, CapV and `LrGap` at every `L(n+1)`** (`Sd.sdCL_of_gap` without the hypothesis
`L(ω+1) ≤ ν_C`). -/
theorem shCL_of_gap (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hn : ∀ n : ℕ, Lr.LrGap S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
      (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
      (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})))) :
    CdCL S :=
  Sd.sdCL_of_gap (shNu hU hV hVt hL) hU hL hn

/-- **`T` from the road's hypotheses and (CL) only from some `N₀` on** (no `LrGap`). -/
theorem shT_of_CLtail (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hEQ : Cx.CxEQtop S) (htop : Cx.CxTCtopOff S) (hmove : Cx.CxStdMoveTop S) (N0 : ℕ)
    (hCL : ∀ n, N0 ≤ n → le1 (Bc.bcC S n) (Bc.bcC S (n + 1))) : Cx.CxT S := by
  have hν := shNu hU hV hVt hL
  exact Sd.sdT_of_away (Sd.sdNoPair_of_nu hν) N0 fun n hn =>
    ⟨hCL n hn, Sd.sdR1Away_of_road (Rz.rzUPPER_of_rest hU hO) (Rz.rzLOWER_of_rest hL)
      (Cx.cxEQ_of_top (Rz.rzCapV_of_rest hV) hEQ) htop n, Sd.sdR2Away_of_nu hν hmove n⟩

/-- **`T` from UPPER, LOWER, CapV and `LrGap` at `L(ω)` alone** (`Rg.rgT_of_nu` with `L(ω+1) ≤ ν_C` proved and
the supply `Rx.rxSupAt`). -/
theorem shT_of_gapLw (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hgap : Lr.LrGap S (Nc.ncL S ω) (Nc.ncL S (ω + 1)) (upsilon (Nc.ncL S ω + Nc.ncL S ω))) :
    Cx.CxT S :=
  Rg.rgT_of_nu (shNu hU hV hVt hL) Rx.rxSupAt.2 hU hL hgap

/-- **The shape of a failure of (CL) at `n`**: if `L(n+1) ≤₁ L(n+2)` fails, then `L(n+1)` has a reach `r` with
`υ_{a+a} ≤ r < L(n+2)`, and no range restart `λ` with `a ≤ υ_λ ≤ r` has `r < r(λ)` (no window `[υ_λ, r(λ))`
covers `r`). -/
theorem shCL_fail (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l) (n : ℕ)
    (hf : ¬ le1 (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))) :
    ∃ r, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) r ∧
      upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) ≤ r ∧
      r < Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}) ∧
      ∀ l, CdRange S l → Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) ≤ upsilon l → upsilon l ≤ r →
        cdR S l ≤ r := by
  obtain ⟨r, hr⟩ := exists_reach (Pp.ppL_lt_succ n).le hf
  have hshort := shCL_short hU hV hVt hL n
  refine ⟨r, hr, hr.2 _ hshort, ?_, fun l hl h1 h2 => ?_⟩
  · by_contra hge
    exact hf (le1_of_le_of_le1 (Pp.ppL_lt_succ n).le (not_lt.1 hge) hr.1)
  · by_contra hlt
    rw [not_le] at hlt
    have hl1 := le1_trans (le1_of_le_of_le1 h1 h2 hr.1) (Rz.rzLOWER_of_rest hL l hl)
    exact absurd (hr.2 _ hl1) (not_le.2 hlt)

/-- **(CL) at `n` iff `L(n+1)` has no reach `r` in `[υ_{a+a}, L(n+2))` that no window `[υ_λ, r(λ))` (`λ` a range
restart, `a ≤ υ_λ ≤ r`) covers** (UPPER, CapV, LOWER). -/
theorem shCL_iff_noUncov (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l) (n : ℕ) :
    le1 (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0})) ↔
      ¬ ∃ r, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) r ∧
        upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) ≤ r ∧
        r < Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}) ∧
        ∀ l, CdRange S l → Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) ≤ upsilon l → upsilon l ≤ r →
          cdR S l ≤ r := by
  constructor
  · rintro h ⟨r, hr, -, hrc, -⟩
    exact absurd (hr.2 _ h) (not_le.2 hrc)
  · intro h
    by_contra hf
    exact h (shCL_fail hU hV hVt hL n hf)

/-- **The road with (CL) and `m* ≤₁ L(1)` in place of every `LrGap`**: from UPPER, `O ≤ c`, LOWER, CapV,
`CxEQtop`, `CxTCtopOff`, `CxStdMoveTop`, `L(0) ≤₁ L(1)` and (CL) (`T` by `shT_of_CLtail`, `CxUpsRestTop` and
`CxStdPairTop` from `L(ω+1) ≤ ν_C`). -/
theorem shRoad_CL (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hEQ : Cx.CxEQtop S) (htop : Cx.CxTCtopOff S) (hmove : Cx.CxStdMoveTop S)
    (h01 : le1 (Nc.ncL S 0) (Nc.ncL S 1)) (hCL : CdCL S) :
    CdEQ S ∧ CdTC S ∧ CdEMB2 S ∧ Cx.CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  have hν := shNu hU hV hVt hL
  have hlow : Nc.ncL S ω ≤ nuC := (Qq.qqL_lt_succ S).le.trans hν
  have hT := shT_of_CLtail hU hO hL hV hVt hEQ htop hmove 0 fun n _ => hCL n
  exact Cx.cxRoad_rz hU hO hL hV hEQ htop (Tp.tpUpsRestTop hlow) ⟨h01, hCL, hT⟩ hmove (Tp.tpStdPairTop hν)

end Googology.Trans.PoR.InaccPsi.R2.Sh
