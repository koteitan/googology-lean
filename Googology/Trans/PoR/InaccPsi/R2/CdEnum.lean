import Googology.Trans.PoR.InaccPsi.R2.CdCodes

/-!
# ENUM-REACH on `[B₀, L(ω+1))`: the two halves as propositions

`B₀ = Λ_B + ω²` (`cdB0`, the BLK^O frontier of `R2.VzW`), `P' = ψ_{Ω₂}(Ω_ω·2)` (`Nc.ncPp`),
`L(ξ) = ψ_{Ω₁}(Ω_ω·2 + P'·ξ)` (`Nc.ncL`), `r(λ) = k_λ(Θ_λ(m_λ))` the predicted reach (`cdR`).

* `CdRange S λ`: `λ` is a restart index with `B₀ ≤ λ`, `ρ_λ < L(ω+1)` and code `m_λ < P'` (the range of
  the docs' Theorem ENUM-REACH: every code below `P'` at levels 1 and 2);
* `CdUpper S λ` (**UPPER**, the cap half): not `ρ_λ ≤₁ r(λ) + 1`;
  `CdLower S λ` (**LOWER**, the realizer half): `ρ_λ ≤₁ r(λ)`;
  `CdUPPER S`, `CdLOWER S`: the halves at every `λ` of `CdRange S`.

Main statements:

* `cdUpper_iff`: UPPER at `λ` iff every `≤₁`-successor of `ρ_λ` is at most `r(λ)`;
  `cdExact_iff`: UPPER and LOWER at `λ` iff `r(λ)` is the reach `lh(ρ_λ)`; `cdEnum_exact`;
* `cdLower_iff_le`, `cdUpper_iff_ge`: when `ρ_λ` has a reach `r`, LOWER is `r(λ) ≤ r` and UPPER is
  `r ≤ r(λ)` (the two halves are the two inequalities);
* `cdEnum_iff_index`: when `ρ_λ` has a reach `r ≥ δ_λ`, `r = k_λ(p)` for one `p`, and ENUM-REACH at
  `λ` holds iff `Θ_λ(m_λ) = p`;
* `cdAgree_B0` (**agreement below `B₀`**): for every restart index `λ < B₀` the repo's reach
  `lh(ρ_λ) = δ_λ + O(λ)` (`reach_allGen`) is `k_λ(p)` for one `p`, and ENUM-REACH at `λ` holds iff
  `Θ_λ(m_λ) = p`, iff `r(λ) = δ_λ + O(λ)`.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Cd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm

/-- `B₀ = Λ_B + ω²`. -/
noncomputable abbrev cdB0 : Ordinal.{0} := VzLam + ω * ω

/-- The range of ENUM-REACH: a restart index `λ ∈ [B₀, L(ω+1))` (by `ρ_λ < L(ω+1)`) with code `< P'`. -/
def CdRange (S : InaccSeq.{0}) (l : Ordinal.{0}) : Prop :=
  IsRestartIdx l ∧ cdB0 ≤ l ∧ upsilon l < Nc.ncL S (ω + 1) ∧ cdCode S l < Nc.ncPp S

/-- **UPPER** at `λ` (the cap half): not `ρ_λ ≤₁ k_λ(Θ_λ(m_λ)) + 1`. -/
def CdUpper (S : InaccSeq.{0}) (l : Ordinal.{0}) : Prop := ¬ le1 (upsilon l) (cdR S l + 1)

/-- **LOWER** at `λ` (the realizer half): `ρ_λ ≤₁ k_λ(Θ_λ(m_λ))`. -/
def CdLower (S : InaccSeq.{0}) (l : Ordinal.{0}) : Prop := le1 (upsilon l) (cdR S l)

/-- **UPPER on `[B₀, L(ω+1))`**. -/
def CdUPPER (S : InaccSeq.{0}) : Prop := ∀ l, CdRange S l → CdUpper S l

/-- **LOWER on `[B₀, L(ω+1))`**. -/
def CdLOWER (S : InaccSeq.{0}) : Prop := ∀ l, CdRange S l → CdLower S l

variable {S : InaccSeq.{0}}

/-- UPPER at `λ` iff every `≤₁`-successor of `ρ_λ` is at most `r(λ)`. -/
theorem cdUpper_iff {l : Ordinal.{0}} : CdUpper S l ↔ ∀ g, le1 (upsilon l) g → g ≤ cdR S l := by
  constructor
  · intro hU g hg
    by_contra hlt
    push Not at hlt
    exact hU (le1_of_le_of_le1 ((cdRho_lt_R S l).le.trans le_self_add)
      (Order.add_one_le_of_lt hlt) hg)
  · intro H h
    exact absurd (H _ h) (not_le.2 (lt_add_one _))

/-- **UPPER and LOWER at `λ` iff `r(λ) = lh(ρ_λ)`.** -/
theorem cdExact_iff {l : Ordinal.{0}} :
    (CdUpper S l ∧ CdLower S l) ↔ IsReach R2C (upsilon l) (cdR S l) :=
  ⟨fun h => ⟨h.2, cdUpper_iff.1 h.1⟩, fun h => ⟨cdUpper_iff.2 h.2, h.1⟩⟩

/-- **ENUM-REACH gives the exact reaches** on `[B₀, L(ω+1))`. -/
theorem cdEnum_exact (hU : CdUPPER S) (hL : CdLOWER S) {l : Ordinal.{0}} (hl : CdRange S l) :
    IsReach R2C (upsilon l) (cdR S l) :=
  cdExact_iff.1 ⟨hU l hl, hL l hl⟩

/-- With a reach `r` of `ρ_λ`, LOWER at `λ` is `r(λ) ≤ r`. -/
theorem cdLower_iff_le {l r : Ordinal.{0}} (hr : IsReach R2C (upsilon l) r) :
    CdLower S l ↔ cdR S l ≤ r :=
  ⟨fun h => hr.2 _ h, fun h => le1_of_le_of_le1 (cdRho_lt_R S l).le h hr.1⟩

/-- With a reach `r` of `ρ_λ`, UPPER at `λ` is `r ≤ r(λ)`. -/
theorem cdUpper_iff_ge {l r : Ordinal.{0}} (hr : IsReach R2C (upsilon l) r) :
    CdUpper S l ↔ r ≤ cdR S l := by
  rw [cdUpper_iff]
  exact ⟨fun h => h r hr.1, fun h g hg => (hr.2 g hg).trans h⟩

/-- **ENUM-REACH at `λ` as an equation of readings**: if `ρ_λ` has a reach `r ≥ δ_λ`, then `r = k_λ(p)`
for one `p`, and UPPER and LOWER hold at `λ` iff `Θ_λ(m_λ) = p`. -/
theorem cdEnum_iff_index {l r : Ordinal.{0}} (hr : IsReach R2C (upsilon l) r) (hδ : cdDelta l ≤ r) :
    ∃ p, cdk l p = r ∧ ((CdUpper S l ∧ CdLower S l) ↔ cdTheta S l (cdCode S l) = p) := by
  obtain ⟨p, hp, -⟩ := cdk_index hr hδ
  refine ⟨p, hp, ?_⟩
  rw [cdExact_iff]
  constructor
  · intro h
    have e : cdR S l = r := Lb.lbReach_unique h hr
    exact (cdk_inj l).1 (e.trans hp.symm)
  · intro h
    have e : cdR S l = r := by
      show cdk l (cdTheta S l (cdCode S l)) = r
      rw [h, hp]
    rw [e]; exact hr

/-- **Agreement below `B₀`**: for a restart index `λ < B₀`, the repo's reach `δ_λ + O(λ)` is `k_λ(p)` for
one `p`; ENUM-REACH at `λ` holds iff `Θ_λ(m_λ) = p`, iff `r(λ) = δ_λ + O(λ)`. -/
theorem cdAgree_B0 {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlB : l < cdB0) :
    ∃ p, cdk l p = cdDelta l + VzOrec l ∧
      ((CdUpper S l ∧ CdLower S l) ↔ cdTheta S l (cdCode S l) = p) ∧
      ((CdUpper S l ∧ CdLower S l) ↔ cdR S l = cdDelta l + VzOrec l) := by
  have hr : IsReach R2C (upsilon l) (cdDelta l + VzOrec l) := reach_allGen vzSpec2 hl hlB
  obtain ⟨p, hp, hiff⟩ := cdEnum_iff_index (S := S) hr le_self_add
  refine ⟨p, hp, hiff, ?_⟩
  rw [cdExact_iff]
  exact ⟨fun h => Lb.lbReach_unique h hr, fun h => h ▸ hr⟩

end Googology.Trans.PoR.InaccPsi.R2.Cd
