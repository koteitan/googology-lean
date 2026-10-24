import Googology.Trans.PoR.InaccPsi.R2.SdSplit

/-!
# `T ⇔ RgLwPair ⇔ L(ω+1) ≤ ν_C` without the gap at `L(ω)`, and the road without `LrGap` at `L(ω)`

`L(ξ) = Nc.ncL S ξ`, `ν_C` the right end of the first non-standard `<₂`-pair, `T`: `L(ω) ≤₁ L(ω+1)`,
`RgLwPair`: no `d ∈ (L(ω), L(ω+1))` with `L(ω) ≤₂ d` and `lh(L(ω)) = d`.  `Rg.rgT_of_nu` gets `T` from
`L(ω+1) ≤ ν_C` by the realizers at `L(ω)`, and needs the uncovered targets `LrGap S L(ω) L(ω+1) υ_{L(ω)+L(ω)}`.
Here `T` comes instead from the reflecting base changes (`Sd.sdT_of_away`), whose parts are all supplied by the
hypotheses the road already has:

* `sdNoPair_of_nu` (`L(ω+1) ≤ ν_C` gives `CvNoPair L(ω) L(ω+1)`), `sdR2Away_of_nu` (**`L(ω+1) ≤ ν_C` and
  `CxStdMoveTop` give the `≤₂`-reflection away from the base point**: below `ν_C` every `<₂`-pair is standard,
  `B_n` reflects standardness, and a standard pair below `ν_C` is a `<₂`-pair);
* `sdR1Away_of_road` (**UPPER, LOWER, EQ and `CxTCtopOff` give the `≤₁`-reflection away from the base point**:
  (TC) at the points that are not Range restarts (`CxTCtopOff`), at the Range restarts with `r(λ) < L(n+2)`
  (`Rt.rtTC_range`), and at the Range restarts with `r(λ) ≥ L(n+2)` LOWER alone);
* `sdCL_of_gap` (**(CL) from `L(ω+1) ≤ ν_C`, UPPER/LOWER at the `Rz.RzRest` Range restarts and `LrGap` at the
  `L(n+1)`**; the supply is `Rx.rxSupAt`);
* `sdT_of_nu` (**`T` from `L(ω+1) ≤ ν_C`, `CxStdMoveTop`, (CL) and `SdR1Away` from some `N₀` on**),
  `sdT_of_nu_road` (the same with the road's hypotheses, **no `LrGap` at `L(ω)`**), `sdT_of_pair`,
  `sdT_iff_pair`, `sdT_iff_nu` (**`T ⇔ RgLwPair ⇔ L(ω+1) ≤ ν_C` without `LrGap` at `L(ω)`**), `sdNu_iff_no2`
  (**under UPPER, CapV: `L(ω+1) ≤ ν_C` iff no `L(ω) ≤₂ y` with `L(ω) < y < L(ω+1)`**);
* `sdRoad` (**the road `Rg.rgRoad` without `LrGap` at `L(ω)` and without the supply hypotheses**).

No new axiom, no new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Sd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- **`L(ω+1) ≤ ν_C` gives `CvNoPair L(ω) L(ω+1)`.** -/
theorem sdNoPair_of_nu (hν : Nc.ncL S (ω + 1) ≤ nuC) :
    Cv.CvNoPair (Nc.ncL S ω) (Nc.ncL S (ω + 1)) :=
  Cv.cvNoPair_of_nu (Lb.lbL_ri S) Rc.rcUps_Lw.symm hν

/-- **`L(ω+1) ≤ ν_C` and `CxStdMoveTop` give the `≤₂`-reflection of `B_n` away from the base point.** -/
theorem sdR2Away_of_nu (hν : Nc.ncL S (ω + 1) ≤ nuC) (hmove : Cx.CxStdMoveTop S) (n : ℕ) :
    SdR2Away S n := by
  intro x y hx hxy hy h2
  have hx' : x < Bc.bcC S (n + 1) := hxy.trans hy
  have hB : Bc.bcB S n x < Bc.bcB S n y :=
    Bc.bcB_mono' S n (Set.mem_Iio.2 hx') (Set.mem_Iio.2 hy) hxy
  have hBν : Bc.bcB S n y < nuC := (Bc.bcB_bound' S n y hy).trans_le hν
  have hs := (hmove n x y hx.le hxy hy).2 (std_of_lt_nuC hBν hB h2)
  exact Tp.tpStdPair_nu (hy.trans ((sdC_lt_Lw n).trans ((Qq.qqL_lt_succ S).trans_le hν))) hs

/-- **`T` from `L(ω+1) ≤ ν_C`, `CxStdMoveTop`, (CL) and the `≤₁`-reflection away from the base point for
every `n ≥ N₀`.** -/
theorem sdT_of_nu (hν : Nc.ncL S (ω + 1) ≤ nuC) (hmove : Cx.CxStdMoveTop S) (hCL : CdCL S) (N0 : ℕ)
    (h1a : ∀ n, N0 ≤ n → SdR1Away S n) : Cx.CxT S :=
  sdT_of_away (sdNoPair_of_nu hν) N0 fun n hn => ⟨hCL n, h1a n hn, sdR2Away_of_nu hν hmove n⟩

/-- **UPPER, LOWER, EQ and `CxTCtopOff` give the `≤₁`-reflection of `B_n` away from the base point.** -/
theorem sdR1Away_of_road (hU : CdUPPER S) (hL : CdLOWER S) (hEQ : CdEQ S) (htop : Cx.CxTCtopOff S)
    (n : ℕ) : SdR1Away S n := by
  intro x y hx hxy hy hB
  by_cases hR : ∃ l, CdRange S l ∧ x = upsilon l
  · obtain ⟨l, hl, rfl⟩ := hR
    rcases lt_or_ge (cdR S l) (Bc.bcC S (n + 1)) with hr | hr
    · exact sdR1_of_TCAt (Rt.rtTC_range hU hL hEQ hl hr) hxy.le hy hB
    · exact le1_of_le_of_le1 hxy.le (hy.le.trans hr) (hL l hl)
  · exact sdR1_of_TCAt (htop n x hx (hxy.trans hy) fun l hl e => hR ⟨l, hl, e⟩) hxy.le hy hB

/-- **(CL) from `L(ω+1) ≤ ν_C`, UPPER/LOWER at the `Rz.RzRest` Range restarts and `LrGap` at every
`L(n+1)`.** -/
theorem sdCL_of_gap (hν : Nc.ncL S (ω + 1) ≤ nuC)
    (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hn : ∀ n : ℕ, Lr.LrGap S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
      (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
      (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})))) :
    CdCL S := by
  have hlow : Nc.ncL S ω ≤ nuC := (Qq.qqL_lt_succ S).le.trans hν
  have hL' := Rz.rzLOWER_of_rest hL
  obtain ⟨-, rn⟩ := Ra.raNamed_R (S := S) hlow (Tp.tpStdPairTop hν) Rx.rxSupAt.1 Rx.rxSupAt.2 hU hL
  intro n
  obtain ⟨l, hl, e⟩ := Pp.ppL_succ_restart (S := S) n
  exact Ls.lsLe1_of_gapCof hL' (Pp.ppL_lt_succ n).le
    (Cv.cvNoPair_of_nu hl e ((Pp.ppL_lt_omega (n + 1)).le.trans hlow)) (rn n) (hn n)

/-- **`T` from `L(ω+1) ≤ ν_C` and the road's hypotheses, without `LrGap` at `L(ω)`.** -/
theorem sdT_of_nu_road (hν : Nc.ncL S (ω + 1) ≤ nuC)
    (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hEQ : Cx.CxEQtop S) (htop : Cx.CxTCtopOff S)
    (hn : ∀ n : ℕ, Lr.LrGap S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
      (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
      (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))
    (hmove : Cx.CxStdMoveTop S) : Cx.CxT S :=
  sdT_of_nu hν hmove (sdCL_of_gap hν hU hL hn) 0 fun n _ =>
    sdR1Away_of_road (Rz.rzUPPER_of_rest hU hO) (Rz.rzLOWER_of_rest hL)
      (Cx.cxEQ_of_top (Rz.rzCapV_of_rest hV) hEQ) htop n

/-- **`T` from `RgLwPair` and the road's hypotheses, without `LrGap` at `L(ω)`.** -/
theorem sdT_of_pair (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hEQ : Cx.CxEQtop S) (htop : Cx.CxTCtopOff S)
    (hn : ∀ n : ℕ, Lr.LrGap S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
      (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
      (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))
    (hpair : Rg.RgLwPair S) (hmove : Cx.CxStdMoveTop S) : Cx.CxT S :=
  sdT_of_nu_road (Rg.rgNu hU hV hVt hpair) hU hO hL hV hEQ htop hn hmove

/-- **`T ⇔ RgLwPair`** under the road's hypotheses, without `LrGap` at `L(ω)`. -/
theorem sdT_iff_pair (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hEQ : Cx.CxEQtop S) (htop : Cx.CxTCtopOff S)
    (hn : ∀ n : ℕ, Lr.LrGap S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
      (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
      (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))
    (hmove : Cx.CxStdMoveTop S) : Cx.CxT S ↔ Rg.RgLwPair S :=
  ⟨Rg.rgPair_of_T, fun hp => sdT_of_pair hU hO hL hV hVt hEQ htop hn hp hmove⟩

/-- **`T ⇔ L(ω+1) ≤ ν_C`** under the road's hypotheses, without `LrGap` at `L(ω)`. -/
theorem sdT_iff_nu (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hEQ : Cx.CxEQtop S) (htop : Cx.CxTCtopOff S)
    (hn : ∀ n : ℕ, Lr.LrGap S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
      (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
      (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))
    (hmove : Cx.CxStdMoveTop S) : Cx.CxT S ↔ Nc.ncL S (ω + 1) ≤ nuC :=
  ⟨fun hT => Rg.rgNu hU hV hVt (Rg.rgPair_of_T hT),
    fun hν => sdT_of_nu_road hν hU hO hL hV hEQ htop hn hmove⟩

/-- **Under UPPER and CapV (below and above `L(ω)`), `L(ω+1) ≤ ν_C` iff no `L(ω) ≤₂ y` with
`L(ω) < y < L(ω+1)`** (the second clause of `CvNoPair L(ω) L(ω+1)`, i.e. the `≤₂`-reflection of `B_n` at
its base point, `sdR2Base_of_no2`). -/
theorem sdNu_iff_no2 (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l) :
    Nc.ncL S (ω + 1) ≤ nuC ↔
      ∀ y, Nc.ncL S ω < y → y < Nc.ncL S (ω + 1) → ¬ le2 (Nc.ncL S ω) y :=
  ⟨fun hν => (sdNoPair_of_nu hν).2, fun h => Rg.rgNu hU hV hVt (Rg.rgPair_of_no2 h)⟩

/-- **The road `Rg.rgRoad` without `LrGap` at `L(ω)` and without the supply hypotheses** (`RaSupAt` is
`Rx.rxSupAt`). -/
theorem sdRoad (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hEQ : Cx.CxEQtop S) (htop : Cx.CxTCtopOff S)
    (h0 : Lr.LrGap S (Nc.ncL S 0) (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Nc.ncL S 0)))
    (hn : ∀ n : ℕ, Lr.LrGap S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
      (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
      (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))
    (hpair : Rg.RgLwPair S) (hmove : Cx.CxStdMoveTop S) :
    CdEQ S ∧ CdTC S ∧ CdEMB2 S ∧ Cx.CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  have hν := Rg.rgNu hU hV hVt hpair
  have hlow : Nc.ncL S ω ≤ nuC := (Qq.qqL_lt_succ S).le.trans hν
  exact Rx.rxRoadRa hU hO hL hV hEQ htop (Tp.tpUpsRestTop hlow) h0 hn
    (sdT_of_pair hU hO hL hV hVt hEQ htop hn hpair hmove) hmove (Tp.tpStdPairTop hν)

/-- **Satisfiability**: the road's conclusion `ν_C = L(ω+1)` gives `RgLwPair` and `CvNoPair L(ω) L(ω+1)`, and
the road's conclusions (TC), (EMB₂) give the reflections `SdR1Away`, `SdR2Away` for every `n`: no hypothesis
added here contradicts the conclusion. -/
theorem sdSat (hν : nuC = Nc.ncL S (ω + 1)) (hTC : CdTC S) (hB2 : CdEMB2 S) :
    Rg.RgLwPair S ∧ Cv.CvNoPair (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, SdRefl S n ∧ SdR1Away S n ∧ SdR2Away S n :=
  ⟨Rg.rgPair_of_nu hν.ge, sdNoPair_of_nu hν.ge, fun n =>
    ⟨sdRefl_of_TC hTC hB2 n,
      sdR1Away_of_TC fun x _ hx => hTC n x hx, sdR2Away_of_EMB2 hB2 n⟩⟩

end Googology.Trans.PoR.InaccPsi.R2.Sd
