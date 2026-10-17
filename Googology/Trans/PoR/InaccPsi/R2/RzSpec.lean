import Googology.Trans.PoR.InaccPsi.R2.LbCrit
import Googology.Trans.PoR.InaccPsi.R2.FxFold

/-!
# BLK^O past `B₀`: the frontier `Λ_B⁺` and the exact reaches of every restart below it

`B(x) = VzB x` is the least value of `φ(ω, ·)` above `x`; `VzOrec` is the recursive offset over the terms
`φ(n, ·)` (`R2.VzO`), `VzOrec(λ) ≤ B(ρ_λ)`; `Λ_B` (`VzLam`) is the least restart index with
`VzOrec(λ) = B(ρ_λ)`, and BLK^O was known below `B₀ = Λ_B + ω²` (`vzSpec2`).

The input of Lemma TOP at a restart index `λ` with `VzOrec(λ) = B(ρ_λ)` is the term `B` itself
(`RstK.vzPkgB`), as soon as no restart `ρ_μ > x₀` below `ρ_λ` has `VzOrec(μ) = B(ρ_μ)`.  So BLK^O holds up
to the first restart index where such restarts are cofinal:

* `RzBad λ`: `λ` is a restart index, `VzOrec(λ) = B(ρ_λ)`, and restart indices `μ < λ` with
  `VzOrec(μ) = B(ρ_μ)` have `ρ_μ` cofinal in `ρ_λ`;
* `rzLam` (**`Λ_B⁺`**): defined as `Cp.cpB1` (the least `λ > 0` below which the restart indices `μ` with
  `VzOrec(μ) = B(ρ_μ)` are cofinal, `R2.CpFront`); `rzLam_def` (**the original definition**: `Λ_B⁺` is the
  least `λ` with `RzBad λ`, `Ω₁` if there is none; `Fx.fxB1_eq`), `rzLam_eq_cpB1`;
* `rzTopIn` (**the input of Lemma TOP below `Λ_B⁺`**), `rzSpec_of_le`, `rzLam_lt_Om1` (`Λ_B⁺ < Ω₁`, the core is
  countable, [C09] Cor 15.15), `rzLam_bad`, `rzLam_ri`, `rzSpec` (**`VzOrec` is a general offset specification
  up to `Λ_B⁺`**);
* `rzB0_lt` (**`B₀ < Λ_B⁺`**): `Λ_B < Λ_B⁺` (no restart below `Λ_B` has the value `B`), and `Λ_B + ω²` has
  `VzOrec = 1`;
* `rzBlk` (**Theorem BLK^O below `υ_{Λ_B⁺}`**), `rzReach` (**the exact reach of every restart below `Λ_B⁺`**:
  `lh(ρ_λ) = δ_λ + VzOrec(λ)` in `R₂^C`, in particular for every restart index in `[B₀, Λ_B⁺)`), `rzCore`
  (`[0, υ_{Λ_B⁺}) ⊆ Core(R₂^C)`), `rzFirst` (**the left end `ρ_L` of the first non-standard pair has
  `Λ_B⁺ ≤ L`**, and so does every `≤₁`-predecessor `υ_μ < ρ_L` of `ν_C`).

No new axiom.

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Rz

open Ordinal Order Googology.Trans.PoR.InaccPsi.R2

/-- A restart index where the offset is `B` and restarts with the offset `B` are cofinal below. -/
def RzBad (l : Ordinal.{0}) : Prop :=
  IsRestartIdx l ∧ VzOrec l = VzB (upsilon l) ∧
    ∀ x0 < upsilon l, ∃ μ, IsRestartIdx μ ∧ μ < l ∧ x0 < upsilon μ ∧ VzOrec μ = VzB (upsilon μ)

/-- **`Λ_B⁺`**: the frontier `Cp.cpB1` (one point, one name; `rzLam_def` is its characterization as the
least restart index with `RzBad`). -/
noncomputable abbrev rzLam : Ordinal.{0} := Cp.cpB1

theorem rzLam_eq_cpB1 : rzLam = Cp.cpB1 := rfl

/-- **The original definition of `Λ_B⁺`**: the least restart index with `RzBad` (`Ω₁` if there is none). -/
theorem rzLam_def : rzLam = sInf (insert Om1 {l | RzBad l}) := Fx.fxB1_eq

theorem rzLam_le_Om1 : rzLam ≤ Om1 := Cp.cpB1_le_Om1

theorem rz_not_bad {l : Ordinal.{0}} (hl : l < rzLam) : ¬ RzBad l := Fx.fx_not_bad hl

/-- **The input of Lemma TOP below `Λ_B⁺`**: the term of `VzOrec(λ)` (`vzTopIn`), or `B` itself. -/
theorem rzTopIn {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlR : l < rzLam) (hl1 : l < Om1) :
    TopInH VzOrec l := by
  rcases (vzOrec_le hl hl1).lt_or_eq with h | h
  · exact vzTopIn hl hl1 h
  · have hnb := rz_not_bad hlR
    have hx : ∃ x0 < upsilon l, ∀ μ, IsRestartIdx μ → μ < l → x0 < upsilon μ →
        VzOrec μ ≠ VzB (upsilon μ) := by
      by_contra hc
      refine hnb ⟨hl, h, fun x0 hx0 => ?_⟩
      by_contra hc2
      exact hc ⟨x0, hx0, fun μ hμ hμl hxμ he => hc2 ⟨μ, hμ, hμl, hxμ, he⟩⟩
    obtain ⟨x0, hx0, hx⟩ := hx
    refine ⟨VzB, x0, h, hx0, fun μ hμ hμl hxμ => ?_, fun R => R.vzPkgB⟩
    exact lt_of_le_of_ne (vzOrec_le hμ (hμl.trans hl1)) (hx μ hμ hμl hxμ)

/-- `VzOrec` is a general offset specification up to every `B ≤ Λ_B⁺` (`ω² ∣ B`, `B < Ω₁`). -/
theorem rzSpec_of_le {B : Ordinal.{0}} (hm : ω * ω ∣ B) (hc : B < Om1) (hB : B ≤ rzLam) :
    OffSpecGen VzOrec B :=
  vzSpec hm hc (fun _ hl hlB => rzTopIn hl (lt_of_lt_of_le hlB hB) (hlB.trans hc))

/-- **`Λ_B⁺ < Ω₁`** (the core is countable, [C09] Cor 15.15). -/
theorem rzLam_lt_Om1 : rzLam < Om1 := by
  rcases rzLam_le_Om1.lt_or_eq with h | h
  · exact h
  · exfalso
    exact not_core_all (fun B hm hc => core_genGen (rzSpec_of_le hm hc (by rw [h]; exact hc.le)))

theorem rzLam_bad : RzBad rzLam := Fx.fxB1_bad

theorem rzLam_ri : IsRestartIdx rzLam := rzLam_bad.1

/-- **`VzOrec` is a general offset specification up to `Λ_B⁺`.** -/
theorem rzSpec : OffSpecGen VzOrec rzLam :=
  rzSpec_of_le (ri_iff.1 rzLam_ri).2 rzLam_lt_Om1 le_rfl

/-- `Λ_B ≤ λ` whenever `VzOrec(λ) = B(ρ_λ)` at a restart index `λ`. -/
theorem rz_vzLam_le {l : Ordinal.{0}} (hl : IsRestartIdx l) (h : VzOrec l = VzB (upsilon l)) :
    VzLam ≤ l :=
  csInf_le (OrderBot.bddBelow _)
    (Set.mem_insert_of_mem _ (show l ∈ {l | IsRestartIdx l ∧ VzOrec l = VzB (upsilon l)} from ⟨hl, h⟩))

/-- A successor restart index `λ₀ + ω²` has `c(λ) < 2`. -/
theorem rz_cL_succ {l0 : Ordinal.{0}} (hl0 : ω * ω ∣ l0) : cL (l0 + ω * ω) < 2 := by
  have hl : IsRestartIdx (l0 + ω * ω) :=
    ri_iff.2 ⟨(lt_of_lt_of_le (mul_pos omega0_pos omega0_pos) le_add_self).ne', dvd_add hl0 (dvd_refl _)⟩
  by_contra h2
  have hd := (le_cL_iff hl 2).1 (not_lt.1 h2)
  obtain ⟨p, rfl⟩ := hl0
  have e3 : ω ^ (1 + (2 : Ordinal.{0})) = ω * ω * ω := by
    rw [show (1 : Ordinal.{0}) + 2 = ((3 : ℕ) : Ordinal.{0}) by norm_num, opow_natCast, pow_succ, pow_two]
  rw [e3] at hd
  obtain ⟨c, hc⟩ := hd
  have hww : (0 : Ordinal.{0}) < ω * ω := mul_pos omega0_pos omega0_pos
  have hc' : p + 1 = ω * c := by
    rw [← mul_add_one, mul_assoc (ω * ω) ω c] at hc
    exact (isNormal_mul_right hww).strictMono.injective hc
  have hdiv : ω ∣ p + 1 := ⟨c, hc'⟩
  rw [← succ_eq_add_one] at hdiv
  exact (isSuccPrelimit_iff_omega0_dvd.2 hdiv).succ_ne _ rfl

/-- **`B₀ < Λ_B⁺`**. -/
theorem rzB0_lt : VzLam + ω * ω < rzLam := by
  obtain ⟨hri, hB, hcof⟩ := rzLam_bad
  have hle : VzLam ≤ rzLam := rz_vzLam_le hri hB
  have hne : VzLam ≠ rzLam := by
    intro he
    obtain ⟨μ, hμ, hμl, -, hμB⟩ := hcof 0 (ups_ri hri).1
    rw [← he] at hμl
    exact absurd hμB (vzOrec_lt_top hμ hμl).ne
  have h1 : VzLam + ω * ω ≤ rzLam :=
    next_mult (ri_iff.1 vzLam_ri).2 (ri_iff.1 hri).2 (lt_of_le_of_ne hle hne)
  refine lt_of_le_of_ne h1 fun he => ?_
  have hs : VzOrec rzLam = 1 := by
    rw [← he]
    exact vzOrec_succ (by rw [he]; exact hri) (rz_cL_succ (ri_iff.1 vzLam_ri).2)
  obtain ⟨-, hlt, -⟩ := vzB_omega (ups_inE hri) (ups_lt_Om1 _ rzLam_lt_Om1)
  have h1ρ : 1 ≤ upsilon rzLam := Order.one_le_iff_pos.2 (ups_ri hri).1
  rw [hs] at hB
  exact absurd (hB ▸ h1ρ.trans_lt hlt) (lt_irrefl _)

/-- **Theorem BLK^O with `VzOrec` below `υ_{Λ_B⁺}`** in `R₂^C`. -/
theorem rzBlk :
    (∀ c d, c < d → d < upsilon rzLam → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < rzLam ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < rzLam →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + VzOrec l)) ∧
    (∀ α < upsilon rzLam, ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  blk_genGen rzSpec

/-- **The exact reach of every restart below `Λ_B⁺`**: `lh(ρ_λ) = δ_λ + VzOrec(λ)` in `R₂^C`. -/
theorem rzReach {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlR : l < rzLam) :
    IsReach R2C (upsilon l) (upsilon (l + ω + 1) + VzOrec l) :=
  reach_allGen rzSpec hl hlR

/-- **CORE-C up to `υ_{Λ_B⁺}`.** -/
theorem rzCore : Set.Iio (upsilon rzLam) ⊆ Core R2C := core_genGen rzSpec

/-- **The first non-standard pair lies above `υ_{Λ_B⁺}`**: `ρ_L <₂ ν_C` with `Λ_B⁺ ≤ L`, and every
`≤₁`-predecessor `υ_μ < ρ_L` of `ν_C` has `Λ_B⁺ ≤ μ`. -/
theorem rzFirst : ∃ l, IsRestartIdx l ∧ rzLam ≤ l ∧ upsilon l < nuC ∧ le2 (upsilon l) nuC ∧
    IsReach R2C (upsilon l) nuC ∧
    (∀ y < upsilon l, le1 y nuC → ∃ μ, IsRestartIdx μ ∧ rzLam ≤ μ ∧ y = upsilon μ ∧
      IsReach R2C (upsilon μ) nuC) := by
  obtain ⟨l, hl, hB, hlν, h2, hr, -, -, hW, -⟩ := Lb.lbFirstB rzSpec
  exact ⟨l, hl, hB, hlν, h2, hr, hW⟩

end Googology.Trans.PoR.InaccPsi.R2.Rz
