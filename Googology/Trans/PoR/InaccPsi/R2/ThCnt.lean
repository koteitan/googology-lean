import Googology.Trans.PoR.InaccPsi.R2.ThLow

/-!
# The closed points from `L(k)` below `ν_C`, and ENUM-REACH at the codes `≥ P'` as a count below `L(k+1)`

`K_λ = Cd.cdK λ` (the closed points relative to `λ`), `otp(K ∩ X) = Cd.cdOtp K X`, `Θ_λ = Cd.cdTheta`,
`L(ξ) = ψ_{Ω₁}(Ω_ω·2 + P'·ξ)`, `P' = ψ_{Ω₂}(Ω_ω·2)`, `ν_C = R2.nuC`.

* `thNotClosed`, `thK_out` (**a point `y` with `a ≤ y < g`, `ρ_λ < a`, `a ≤₁ g`, is not closed relative to
  `λ`**: `lh(a) > y`), `thOtp_cut` (**`otp(K_λ ∩ g) = otp(K_λ ∩ a)`** for such `a ≤₁ g ≤ Ω₁`);
* `thCount_L` (**`L(k+1) ≤₁ ν_C` gives `otp(K_{L(k)} ∩ ν_C) = otp(K_{L(k)} ∩ L(k+1)) ≤ L(k+1)`**);
* `thOtp_last` (**an order type `T + 1` has a last member**: `otp(C ∩ m) = T + 1` gives a largest `c ∈ C ∩ m`);
* `thNu_le_R_L` (**`ν_C ≤ r(L(k))` forces `otp(K_{L(k)} ∩ ν_C) ≤ L(k+1)`**, no hypothesis);
* under the road hypotheses `hU hO hL hV hVt hEQ htop hmove` (`Te.teRoadNu`):
  `thEnum_L_count` (**with (CL) and `m* ≤₁ L(1)`: ENUM-REACH at `L(k)` iff
  `Θ_{L(k)}(P') = otp(K_{L(k)} ∩ L(k+1))`, both sides at most `L(k+1)`**, and the reading at least
  `ψ_{Ω₁}(Ω_ω·2 + P'·k + θ·L(k))`), `thEnum_Lw_count` (**at `L(ω)`: iff
  `Θ_{L(ω)}(P') + 1 = otp(K_{L(ω)} ∩ L(ω+1))`, and then `K_{L(ω)} ∩ L(ω+1)` has a largest member**),
  `thEnumL_iff` (**ENUM-REACH at every `L(k)` together with `otp(K_{L(k)} ∩ L(k+1)) ≤ Θ_{L(k)}(P')` iff
  `L(k) ≤₁ ν_C` for every `k` together with COUNT: `Θ_{L(k)}(P') = otp(K_{L(k)} ∩ L(k+1))` for every `k`**).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Th

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-! ## Points that are not closed -/

/-- **A point `y` with `a ≤ y < g`, `ρ_λ < a` and `a ≤₁ g` is not closed relative to `λ`.** -/
theorem thNotClosed {l a g y : Ordinal.{0}} (hla : upsilon l < a) (hay : a ≤ y) (hag : le1 a g)
    (hyg : y < g) : ¬ cdClosed l y := fun h =>
  absurd (h.2 a hla hay g hag) (not_le.2 hyg)

/-- **Such a point is not in `K_λ`** when `y < Ω₁`. -/
theorem thK_out {l a g y : Ordinal.{0}} (hla : upsilon l < a) (hay : a ≤ y) (hag : le1 a g)
    (hyg : y < g) (hy1 : y < Om1) : y ∉ cdK l := by
  rintro (h | h)
  · exact thNotClosed hla hay hag hyg h
  · exact absurd h.1 (not_le.2 hy1)

/-- **`otp(K_λ ∩ g) = otp(K_λ ∩ a)`** for `ρ_λ < a ≤₁ g ≤ Ω₁`. -/
theorem thOtp_cut {l a g : Ordinal.{0}} (hla : upsilon l < a) (hag : le1 a g) (hg1 : g ≤ Om1) :
    cdOtp (cdK l) a = cdOtp (cdK l) g :=
  cdOtp_eq_of_gap (cdK l) (le1_le hag) fun _ hc hac hcg =>
    thK_out hla hac hag hcg (hcg.trans_le hg1) hc

/-- **`L(k+1) ≤₁ ν_C` gives `otp(K_{L(k)} ∩ ν_C) = otp(K_{L(k)} ∩ L(k+1)) ≤ L(k+1)`.** -/
theorem thCount_L (k : ℕ) (h : le1 (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) nuC) :
    cdOtp (cdK (Nc.ncL S (k : Ordinal.{0}))) nuC =
        cdOtp (cdK (Nc.ncL S (k : Ordinal.{0}))) (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) ∧
      cdOtp (cdK (Nc.ncL S (k : Ordinal.{0}))) (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) ≤
        Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) := by
  have hla : upsilon (Nc.ncL S (k : Ordinal.{0})) < Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) := by
    rw [Te.teUps_L]; exact Te.teL_lt_succ k
  exact ⟨(thOtp_cut hla h nuC_le_Om1).symm, cdOtp_le_self _ _⟩

open Classical in
/-- **An order type `T + 1` has a last member.** -/
theorem thOtp_last {C : Set Ordinal.{0}} {m T : Ordinal.{0}} (h : cdOtp C m = T + 1) :
    ∃ c ∈ C, c < m ∧ ∀ c' ∈ C, c' < m → c' ≤ c := by
  by_contra hno
  push Not at hno
  have hle : cdOtp C m ≤ T := by
    rw [cdOtp_eq C m]
    refine ciSup_le' fun c => ?_
    split_ifs with hc
    · obtain ⟨c', hc', hc'm, hcc'⟩ := hno c.1 hc c.2
      have h1 : cdOtp C c' + 1 ≤ cdOtp C m := by
        rw [cdOtp_eq C m]
        have := le_ciSup (f := fun c : Iio m => if c.1 ∈ C then cdOtp C c.1 + 1 else 0)
          (cdOtp_bdd C m) ⟨c', hc'm⟩
        simpa only [if_pos hc'] using this
      rw [h] at h1
      have h2 : cdOtp C c' ≤ T := Order.lt_add_one_iff.1 ((lt_add_one _).trans_le h1)
      exact Order.add_one_le_of_lt ((cdOtp_lt_of_mem hc hcc').trans_le h2)
    · exact zero_le
  rw [h] at hle
  exact absurd hle (not_le.2 (lt_add_one T))

/-- **`ν_C ≤ r(L(k))` forces `otp(K_{L(k)} ∩ ν_C) ≤ L(k+1)`.** -/
theorem thNu_le_R_L (k : ℕ) (h : nuC ≤ cdR S (Nc.ncL S (k : Ordinal.{0}))) :
    cdOtp (cdK (Nc.ncL S (k : Ordinal.{0}))) nuC ≤ Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) := by
  have hcode : cdCode S (Nc.ncL S (k : Ordinal.{0})) = Nc.ncPp S := (Te.teHi_mem k).1.2.2.2
  have h1 := (Te.teNu_le_R_iff (S := S) (Nc.ncL S (k : Ordinal.{0}))).1 h
  rw [hcode] at h1
  exact h1.trans (thTheta_Lk k)

/-! ## Under the road hypotheses -/

section Road

variable (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
  (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
  (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
  (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
  (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
  (hEQ : Cx.CxEQtop S) (htop : Cx.CxTCtopOff S) (hmove : Cx.CxStdMoveTop S)
include hU hO hL hV hVt hEQ htop hmove

/-- **ENUM-REACH at `L(k)` as a count below `L(k+1)`**: given (CL) and `m* ≤₁ L(1)`, ENUM-REACH at `L(k)` iff
`Θ_{L(k)}(P') = otp(K_{L(k)} ∩ L(k+1))`; both sides are at most `L(k+1)`, and the reading is at least
`ψ_{Ω₁}(Ω_ω·2 + P'·k + θ·L(k))`. -/
theorem thEnum_L_count (hCL : CdCL S) (h01 : le1 (Nc.ncL S 0) (Nc.ncL S 1)) (k : ℕ) :
    ((CdUpper S (Nc.ncL S (k : Ordinal.{0})) ∧ CdLower S (Nc.ncL S (k : Ordinal.{0}))) ↔
        cdTheta S (Nc.ncL S (k : Ordinal.{0})) (Nc.ncPp S) =
          cdOtp (cdK (Nc.ncL S (k : Ordinal.{0}))) (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}))) ∧
      cdOtp (cdK (Nc.ncL S (k : Ordinal.{0}))) (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) ≤
        Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ∧
      S.psi (Om ω + Om ω + Nc.ncPp S * (k : Ordinal.{0}) + ConjT.th S * Nc.ncL S (k : Ordinal.{0})) (Om 1) ≤
        cdTheta S (Nc.ncL S (k : Ordinal.{0})) (Nc.ncPp S) ∧
      cdTheta S (Nc.ncL S (k : Ordinal.{0})) (Nc.ncPp S) ≤ Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) := by
  have hall := (Te.teLong_iff_nu hU hO hL hV hVt hEQ htop hmove).1 ⟨hCL, h01⟩
  obtain ⟨hc, hcle⟩ := thCount_L (S := S) k (hall (k + 1))
  obtain ⟨hlo, hup⟩ := thTheta_Lk_bounds (S := S) k
  refine ⟨?_, hcle, hlo, hup⟩
  rw [← hc]
  exact (Te.teEnum_of_road hU hO hL hV hVt hEQ htop hmove hCL h01).1 k

/-- **ENUM-REACH at `L(ω)` as a count below `L(ω+1)`**: given (CL) and `m* ≤₁ L(1)`, ENUM-REACH at `L(ω)` iff
`Θ_{L(ω)}(P') + 1 = otp(K_{L(ω)} ∩ L(ω+1))`; and then `K_{L(ω)} ∩ L(ω+1)` has a largest member. -/
theorem thEnum_Lw_count (hCL : CdCL S) (h01 : le1 (Nc.ncL S 0) (Nc.ncL S 1)) :
    ((CdUpper S (Nc.ncL S ω) ∧ CdLower S (Nc.ncL S ω)) ↔
        cdTheta S (Nc.ncL S ω) (Nc.ncPp S) + 1 = cdOtp (cdK (Nc.ncL S ω)) (Nc.ncL S (ω + 1))) ∧
      ((CdUpper S (Nc.ncL S ω) ∧ CdLower S (Nc.ncL S ω)) →
        ∃ c ∈ cdK (Nc.ncL S ω), c < Nc.ncL S (ω + 1) ∧
          ∀ c' ∈ cdK (Nc.ncL S ω), c' < Nc.ncL S (ω + 1) → c' ≤ c) := by
  obtain ⟨-, -, -, -, -, -, -, hν, -⟩ := Sh.shRoad_CL hU hO hL hV hVt hEQ htop hmove h01 hCL
  have h := (Te.teEnum_of_road hU hO hL hV hVt hEQ htop hmove hCL h01).2
  rw [thTheta_Lw_succ.1, hν] at h
  exact ⟨h, fun he => thOtp_last (h.1 he).symm⟩

/-- **ENUM-REACH at every `L(k)` with the count `otp(K_{L(k)} ∩ L(k+1)) ≤ Θ_{L(k)}(P')` iff `L(k) ≤₁ ν_C` for
every `k` with COUNT: `Θ_{L(k)}(P') = otp(K_{L(k)} ∩ L(k+1))` for every `k`.** -/
theorem thEnumL_iff :
    (∀ k : ℕ, (CdUpper S (Nc.ncL S (k : Ordinal.{0})) ∧ CdLower S (Nc.ncL S (k : Ordinal.{0}))) ∧
        cdOtp (cdK (Nc.ncL S (k : Ordinal.{0}))) (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) ≤
          cdTheta S (Nc.ncL S (k : Ordinal.{0})) (Nc.ncPp S)) ↔
      ((∀ k : ℕ, le1 (Nc.ncL S (k : Ordinal.{0})) nuC) ∧
        ∀ k : ℕ, cdTheta S (Nc.ncL S (k : Ordinal.{0})) (Nc.ncPp S) =
          cdOtp (cdK (Nc.ncL S (k : Ordinal.{0}))) (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}))) := by
  constructor
  · intro he
    have hCL : CdCL S := fun n => Te.teCL_of_enum (n + 1) (he (n + 1)).1.2 (he (n + 1)).2
    have h01 : le1 (Nc.ncL S 0) (Nc.ncL S 1) := by
      simpa using Te.teCL_of_enum (S := S) 0 (he 0).1.2 (he 0).2
    refine ⟨(Te.teLong_iff_nu hU hO hL hV hVt hEQ htop hmove).1 ⟨hCL, h01⟩, fun k => ?_⟩
    exact (thEnum_L_count hU hO hL hV hVt hEQ htop hmove hCL h01 k).1.1 (he k).1
  · rintro ⟨hall, hc⟩ k
    obtain ⟨hCL, h01⟩ := (Te.teLong_iff_nu hU hO hL hV hVt hEQ htop hmove).2 hall
    exact ⟨(thEnum_L_count hU hO hL hV hVt hEQ htop hmove hCL h01 k).1.2 (hc k), (hc k).ge⟩

end Road

end Googology.Trans.PoR.InaccPsi.R2.Th
