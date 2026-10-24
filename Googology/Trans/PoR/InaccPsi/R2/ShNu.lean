import Googology.Trans.PoR.InaccPsi.R2.SdCross
import Googology.Trans.PoR.InaccPsi.R2.SeLow

/-!
# `L(ω+1) ≤ ν_C` from LOWER at one range restart: the pair `RgLwPair` is no longer a hypothesis

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.

`L(ξ) = Nc.ncL S ξ`, `P' = Nc.ncPp S`, `ν_C` the right end of the first non-standard `<₂`-pair, `T`:
`L(ω) ≤₁ L(ω+1)`, `r(λ) = Cd.cdR S λ` the predicted reach of the restart `ρ_λ = υ_λ`.

Three facts that are already theorems meet here:
* `nuC_restart`: `ν_C = υ_ξ` for a restart index `ξ`;
* `nuC_cap` (Lemma CAP at `ν_C`): no `α ≤ ν_C` is `≤₁` a point above `ν_C`, so `ν_C ≤₁ g` fails for `g > ν_C`;
* `Cd.cdRho_lt_R`: `υ_λ < r(λ)` for every `λ`.
So LOWER (`υ_λ ≤₁ r(λ)`) fails at the index of `ν_C` (`shNotLower`).  If `L(ω) < ν_C < L(ω+1)`, that index is a
restart of the range (`shCode_top`: its code is `< P'`; `shRange_top`), so LOWER there is false.  The case
`ν_C = L(ω)` is a crossing pair (`Sd.sdCross_caps`), and `ν_C < L(ω)` contradicts `Cd.cdLow`.  Hence:

* `shNu_of_lower` (**CAP-0, CAP-1 below `L(ω+1)` and LOWER at the range restarts `λ` with `L(ω) < υ_λ = ν_C` give
  `L(ω+1) ≤ ν_C`**), `shNu_iff_lowerAt` (under the caps this LOWER instance is equivalent to `L(ω+1) ≤ ν_C`, and it
  holds vacuously when `L(ω+1) ≤ ν_C`), `shNu` (**`L(ω+1) ≤ ν_C` from UPPER, CapV and LOWER of the road**);
* `shPair` (`Rg.RgLwPair`), `shNoPair` (`CvNoPair L(ω) L(ω+1)`), `shNo2` (no `L(ω) ≤₂ y` with
  `L(ω) < y < L(ω+1)`), `shT` (**`T` from the road's hypotheses, no `RgLwPair`**), `shRoad` (**the road
  `Sd.sdRoad` without `RgLwPair`**).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Sh

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm

variable {S : InaccSeq.{0}}

/-- **Every restart strictly between `L(ω)` and `L(ω+1)` has code `< P'`**: its name `η_λ` lies in
`(Ω_ω + P'·ω, Ω_ω + P'·ω + P')`, `ω^{P'} = P' ∣ Ω_ω + P'·ω`, so its last exponent is `< P'` (`Cd.cdWin`). -/
theorem shCode_top {l : Ordinal.{0}} (hl0 : l ≠ 0) (h1 : Nc.ncL S ω < upsilon l)
    (h2 : upsilon l < Nc.ncL S (ω + 1)) : cdCode S l < Nc.ncPp S := by
  have hPE : ω ^ Nc.ncPp S = Nc.ncPp S := Lw.lw_Pp_opow S
  have hWE : ω ^ Om ω = Om ω := Low.opow_eq_self_of_SC (SC_Om omega0_ne_zero)
  have hc1 : Nc.ncL S ω = Pv S (Om ω + Nc.ncPp S * ω) := Lw.lw_L_eq S _
  have hc2 : Nc.ncL S (ω + 1) = Pv S (Om ω + Nc.ncPp S * ω + Nc.ncPp S) := by
    rw [Lw.lw_L_eq S, mul_add_one, add_assoc]
  obtain ⟨hg, hι, hlt, hpv⟩ := cdEta_pv_spec hl0 (h2.trans_eq hc2)
  have hgt : Om ω + Nc.ncPp S * ω < cdEta S l := by
    by_contra hle
    push Not at hle
    rcases hle.lt_or_eq with h | h
    · have h3 := upsilon_normal.strictMono (cd_iota_lt_of_good hg h)
      rw [hι, ups_iota S] at h3
      exact absurd (h3.trans_eq hc1.symm) (not_lt.2 h1.le)
    · rw [h, ← hc1] at hpv
      exact absurd hpv (ne_of_lt h1)
  have hdvd : ω ^ Nc.ncPp S ∣ Om ω + Nc.ncPp S * ω := by
    refine dvd_add ?_ ?_
    · conv_rhs => rw [← hWE]
      exact opow_dvd_opow ω (cdPp_lt_Om_omega S).le
    · rw [hPE]; exact dvd_mul_right _ _
  have hlt' : cdEta S l < Om ω + Nc.ncPp S * ω + ω ^ Nc.ncPp S := by
    rw [hPE]; exact hlt
  exact (cdCodeOf_le_exp S _).trans_lt (cdWin hdvd hgt hlt').1

/-- **Every restart strictly between `L(ω)` and `L(ω+1)` is a restart of the range.** -/
theorem shRange_top {l : Ordinal.{0}} (hl : IsRestartIdx l) (h1 : Nc.ncL S ω < upsilon l)
    (h2 : upsilon l < Nc.ncL S (ω + 1)) : CdRange S l := by
  have hB0 : cdB0 ≤ l := by
    by_contra hB
    push Not at hB
    have h3 : upsilon l < upsilon cdB0 := upsilon_normal.strictMono hB
    have h4 : upsilon cdB0 < Nc.ncL S ω := (Fp.fpB0_lt_M (S := S)).trans_le (Pp.ppL_mono zero_le)
    exact absurd (h3.trans h4) (not_lt.2 h1.le)
  exact ⟨hl, hB0, h2, shCode_top hl.1 h1 h2⟩

/-- Every restart above `L(ω)` is above the frontier `Λ_B⁺`, so `Rz.RzRest` holds there. -/
theorem shRest_top {l : Ordinal.{0}} (h1 : Nc.ncL S ω < upsilon l) : Rz.RzRest l := by
  left
  have h : upsilon Rz.rzLam < upsilon l := (Ph.phFr_order (S := S) 0).2.1.2.1.trans h1
  exact (upsilon_normal.strictMono.lt_iff_lt.1 h).le

/-- **LOWER fails at the index of `ν_C`** (unconditionally): `υ_λ = ν_C < r(λ)`, and nothing `≤ ν_C` is `≤₁` a
point above `ν_C` (`nuC_cap`). -/
theorem shNotLower {l : Ordinal.{0}} (he : upsilon l = nuC) : ¬ CdLower S l := fun h =>
  nuC_cap (upsilon l) he.le (cdR S l) (he.symm.trans_lt (cdRho_lt_R S l)) h

/-- **`L(ω+1) ≤ ν_C` from CAP-0, CAP-1 below `L(ω+1)` and LOWER at the range restarts `λ` with
`L(ω) < υ_λ = ν_C`.** -/
theorem shNu_of_lower (h0 : CdCAP0 S) (h1 : CdCAP1 S (Nc.ncL S (ω + 1)))
    (hL : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → upsilon l = nuC → CdLower S l) :
    Nc.ncL S (ω + 1) ≤ nuC := by
  by_contra hlt
  rw [not_le] at hlt
  have h1' : CdCAP1 S (Nc.ncL S ω) := fun l hl hB hlev hlX hc =>
    h1 l hl hB hlev (hlX.trans (Qq.qqL_lt_succ S)) hc
  have hlow : Nc.ncL S ω ≤ nuC := cdLow h0 h1'
  obtain ⟨ξ, hξ, he⟩ := nuC_restart
  rcases hlow.lt_or_eq with hgt | heq
  · have h1ξ : Nc.ncL S ω < upsilon ξ := hgt.trans_eq he
    have h2ξ : upsilon ξ < Nc.ncL S (ω + 1) := he.symm.trans_lt hlt
    exact shNotLower he.symm (hL ξ (shRange_top hξ h1ξ h2ξ) h1ξ he.symm)
  · obtain ⟨⟨l, -, hlν, h2, -⟩, -⟩ := pairs_cof_nuC
    exact Sd.sdCross_caps h0 h1 (upsilon l) nuC (hlν.trans_eq heq.symm) heq.le hlt h2

/-- **Under the caps, `L(ω+1) ≤ ν_C` iff LOWER holds at the range restarts `λ` with `L(ω) < υ_λ = ν_C`**; the
instance is vacuous when `L(ω+1) ≤ ν_C` (a range restart is below `L(ω+1)`), and false at `ν_C` otherwise. -/
theorem shNu_iff_lowerAt (h0 : CdCAP0 S) (h1 : CdCAP1 S (Nc.ncL S (ω + 1))) :
    Nc.ncL S (ω + 1) ≤ nuC ↔
      ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → upsilon l = nuC → CdLower S l :=
  ⟨fun hν _l hl _ he => absurd (he ▸ hl.2.2.1) (not_lt.2 hν), shNu_of_lower h0 h1⟩

/-- **`L(ω+1) ≤ ν_C` from UPPER, CapV (below and above `L(ω)`) and LOWER at the `Rz.RzRest` range restarts.** -/
theorem shNu (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l) : Nc.ncL S (ω + 1) ≤ nuC :=
  shNu_of_lower (Rg.rgCAP_of_enum hU hV hVt).1 (Rg.rgCAP_of_enum hU hV hVt).2
    fun l hl h1 _ => hL l hl (shRest_top h1)

/-- **`RgLwPair`** from UPPER, CapV and LOWER. -/
theorem shPair (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l) : Rg.RgLwPair S :=
  Rg.rgPair_of_nu (shNu hU hV hVt hL)

/-- **`CvNoPair L(ω) L(ω+1)`** from UPPER, CapV and LOWER. -/
theorem shNoPair (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l) :
    Cv.CvNoPair (Nc.ncL S ω) (Nc.ncL S (ω + 1)) :=
  Sd.sdNoPair_of_nu (shNu hU hV hVt hL)

/-- **No `L(ω) ≤₂ y` with `L(ω) < y < L(ω+1)`** (the `≤₂`-reflection of `B_n` at its base point,
`Sd.sdR2Base_of_no2`) from UPPER, CapV and LOWER. -/
theorem shNo2 (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l) :
    ∀ y, Nc.ncL S ω < y → y < Nc.ncL S (ω + 1) → ¬ le2 (Nc.ncL S ω) y :=
  (shNoPair hU hV hVt hL).2

/-- **`T: L(ω) ≤₁ L(ω+1)` from the road's hypotheses, with no `RgLwPair`** (`Sd.sdT_iff_nu` with its right side
proved). -/
theorem shT (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hEQ : Cx.CxEQtop S) (htop : Cx.CxTCtopOff S)
    (hn : ∀ n : ℕ, Lr.LrGap S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
      (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
      (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))
    (hmove : Cx.CxStdMoveTop S) : Cx.CxT S :=
  Sd.sdT_of_nu_road (shNu hU hV hVt hL) hU hO hL hV hEQ htop hn hmove

/-- **The road `Sd.sdRoad` without `RgLwPair`**: from UPPER, `O ≤ c`, LOWER, CapV, `CxEQtop`, `CxTCtopOff`,
`LrGap` at `m*` and at every `L(n+1)`, `CxStdMoveTop`. -/
theorem shRoad (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hEQ : Cx.CxEQtop S) (htop : Cx.CxTCtopOff S)
    (h0 : Lr.LrGap S (Nc.ncL S 0) (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Nc.ncL S 0)))
    (hn : ∀ n : ℕ, Lr.LrGap S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
      (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
      (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))
    (hmove : Cx.CxStdMoveTop S) :
    CdEQ S ∧ CdTC S ∧ CdEMB2 S ∧ Cx.CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  Sd.sdRoad hU hO hL hV hVt hEQ htop h0 hn (shPair hU hV hVt hL) hmove

/-- **Satisfiability**: the road's conclusion `ν_C = L(ω+1)` makes the one LOWER instance used here vacuous, and
the conclusions agree with `Sd.sdSat`. -/
theorem shSat (hν : nuC = Nc.ncL S (ω + 1)) :
    ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → upsilon l = nuC → CdLower S l :=
  fun _l hl _ he => absurd (he.trans hν) (ne_of_lt hl.2.2.1)

end Googology.Trans.PoR.InaccPsi.R2.Sh
