import Googology.Trans.PoR.InaccPsi.R2.SdCof

/-!
# No `≤₂`-pair crosses `L(ω)` from below: the only obstruction to `T` is a pair starting at `L(ω)`

`ν_C` the right end of the first non-standard `<₂`-pair, `ρ_λ` its left end (`Lb.lbFirst`).

* `sdMin_first` (**`ρ_λ` is the least `≤₂`-predecessor of `ν_C`**, no hypothesis): a `≤₂`-predecessor `x < ρ_λ`
  of `ν_C` has `≤₁`-predecessors cofinal below it ([C09] Def 5.3, clause 1 (d)), all `≤₁ ν_C`, but below `ρ_λ`
  the `≤₁`-predecessors of `ν_C` are finite below every point; `x = 0` is excluded by `not_le1_zero`;
* `sdCross_caps` (**under CAP-0 and CAP-1 below `L(ω+1)`: no `x <₂ y` with `x < L(ω) ≤ y < L(ω+1)`**, the
  first clause of `CvNoPair L(ω) L(ω+1)`): below `ν_C` the pair is standard and cannot straddle the restart
  `L(ω)`; above `ν_C` it contradicts the cap at `ν_C`; at `y = ν_C`, `ρ_λ = L(ω)` (`Rg.rgFirst_ne`) and
  `sdMin_first`;
* `sdNoPair_iff_no2` (under the caps, `CvNoPair L(ω) L(ω+1)` iff its second clause), `sdT_of_no2` (**`T` from
  the caps, the second clause and, from some `N₀` on, (CL), `SdR1Away`, `SdR2Away`**).

No new axiom, no new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Sd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- **The left end of the first non-standard pair is the least `≤₂`-predecessor of `ν_C`.** -/
theorem sdMin_first {l : Ordinal.{0}} (hlν : upsilon l < nuC)
    (hfin : ∀ s < upsilon l, Set.Finite {u | u < s ∧ le1 u nuC}) :
    ∀ x < upsilon l, ¬ le2 x nuC := by
  classical
  intro x hx h2
  have hxν : x < nuC := hx.trans hlν
  rcases eq_or_lt_of_le (zero_le (a := x)) with hx0 | hx0
  · subst hx0
    exact not_le1_zero (hx.trans hlν) (le2_le1 h2)
  have hcof := le2_preds_cofinal h2 hxν
  set F := (hfin x hx).toFinset with hF
  have hm : F.sup id < x := by
    rw [Finset.sup_lt_iff hx0]
    intro u hu
    exact ((Set.Finite.mem_toFinset _).1 hu).1
  obtain ⟨y, hmy, hyx, hy⟩ := hcof _ hm
  have hyF : y ∈ F := (Set.Finite.mem_toFinset _).2 ⟨hyx, le1_trans hy (le2_le1 h2)⟩
  exact absurd (Finset.le_sup (f := id) hyF) (not_le.2 hmy)

/-- **Under CAP-0 and CAP-1 below `L(ω+1)`, no `≤₂`-pair `x <₂ y` has `x < L(ω) ≤ y < L(ω+1)`.** -/
theorem sdCross_caps (h0 : CdCAP0 S) (h1 : CdCAP1 S (Nc.ncL S (ω + 1))) :
    ∀ x y, x < Nc.ncL S ω → Nc.ncL S ω ≤ y → y < Nc.ncL S (ω + 1) → ¬ le2 x y := by
  intro x y hx hy hyb h2
  have h1' : CdCAP1 S (Nc.ncL S ω) := fun l hl hB hlev hlX hc =>
    h1 l hl hB hlev (hlX.trans (Qq.qqL_lt_succ S)) hc
  have hlow : Nc.ncL S ω ≤ nuC := cdLow h0 h1'
  rcases lt_trichotomy y nuC with hyν | rfl | hνy
  · refine Cx.cxStd_straddle (std_of_lt_nuC hyν (hx.trans_le hy) h2) (Lb.lbL_ri S) ?_ ?_
    · rw [Rc.rcUps_Lw]; exact hx
    · rw [Rc.rcUps_Lw]; exact hy
  · obtain ⟨l, hl, -, hlν, -, -, -, hP, hW, hfin⟩ := Lb.lbFirst
    have hX : upsilon l < Nc.ncL S (ω + 1) := hlν.trans hyb
    by_cases hne : upsilon l = Nc.ncL S ω
    · exact sdMin_first hlν hfin x (by rw [hne]; exact hx) h2
    · exact Rg.rgFirst_ne h0 h1 hl hlν hP hW hX hne
  · exact nuC_cap x (hx.trans_le hlow).le y hνy (le2_le1 h2)

/-- **Under the caps, `CvNoPair L(ω) L(ω+1)` is its second clause.** -/
theorem sdNoPair_iff_no2 (h0 : CdCAP0 S) (h1 : CdCAP1 S (Nc.ncL S (ω + 1))) :
    Cv.CvNoPair (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ↔
      ∀ y, Nc.ncL S ω < y → y < Nc.ncL S (ω + 1) → ¬ le2 (Nc.ncL S ω) y :=
  ⟨And.right, fun h => ⟨sdCross_caps h0 h1, h⟩⟩

/-- **`T` from the caps, the second clause of `CvNoPair L(ω) L(ω+1)` and, for every `n ≥ N₀`, (CL) at `n`
and the reflection away from the base point.** -/
theorem sdT_of_no2 (h0 : CdCAP0 S) (h1 : CdCAP1 S (Nc.ncL S (ω + 1)))
    (h2 : ∀ y, Nc.ncL S ω < y → y < Nc.ncL S (ω + 1) → ¬ le2 (Nc.ncL S ω) y) (N0 : ℕ)
    (h : ∀ n, N0 ≤ n → le1 (Bc.bcC S n) (Bc.bcC S (n + 1)) ∧ SdR1Away S n ∧ SdR2Away S n) :
    Cx.CxT S :=
  sdT_of_away ((sdNoPair_iff_no2 h0 h1).2 h2) N0 h

end Googology.Trans.PoR.InaccPsi.R2.Sd
