import Googology.Trans.PoR.InaccPsi.R2.CdEnum

/-!
# The closed points of a restart with a first block: `k_λ(x) = δ_λ + x` for `x < δ_λ`

`ρ_λ = υ_λ`, `τ_λ = υ_{λ+ω}`, `δ_λ = υ_{λ+ω+1}`; `RstK ρ τ δ` is the restart context of `R2.RstK` (the first
pair `τ <₂ δ`, nothing below `ρ` reaches `ρ`, …), which holds at every restart below a BLK^O frontier.
`cdClosed`, `cdK`, `cdk`, `cdR` are the closed points, their enumeration `k_λ` and the predicted reach
`r(λ) = k_λ(Θ_λ(m_λ))` of `R2.CdDef`.

* `rzClosed` (**every `δ_λ + x`, `x < δ_λ`, is closed relative to `λ`**): a point of `(ρ_λ, δ_λ]` has no
  `≤₁`-successor above `δ_λ` (`RstK.capδ`), and a point of `(δ_λ, δ_λ + x]` is decomposable, so it has no
  `≤₁`-successor but itself (`indec_of_lt1`);
* `rzk_eq` (**`k_λ(x) = δ_λ + x` for `x < δ_λ`**, by `cdk_interval`);
* `rzR_eq`: `r(λ) = δ_λ + Θ_λ(m_λ)` when `Θ_λ(m_λ) < δ_λ`;
* `rzEnum_of_reach` (**ENUM-REACH at a restart with a short reach**): if `RstK` holds at `λ` and
  `lh(ρ_λ) = δ_λ + o` with `o < δ_λ`, then LOWER at `λ` iff `Θ_λ(m_λ) ≤ o`, UPPER at `λ` iff `o ≤ Θ_λ(m_λ)`,
  and both iff `Θ_λ(m_λ) = o`.

No new axiom, no new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Rz

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- A point strictly between `δ` and `δ + δ` is decomposable. -/
theorem rz_not_indec {δ a : Ordinal.{0}} (h1 : δ < a) (h2 : a < δ + δ) : ¬ Indec a := by
  intro hI
  obtain ⟨z, rfl⟩ := exists_add_of_le h1.le
  have hz : z < δ := (add_lt_add_iff_left δ).1 h2
  have hp := (indec_iff.1 hI).2
  have hlt : δ + z < δ + z := hp h1 (hz.trans h1)
  exact lt_irrefl _ hlt

/-- **Every `δ_λ + x` with `x < δ_λ` is closed relative to `λ`.** -/
theorem rzClosed {l x : Ordinal.{0}} (R : RstK (upsilon l) (upsilon (l + ω)) (upsilon (l + ω + 1)))
    (hx : x < cdDelta l) : cdClosed l (cdDelta l + x) := by
  refine ⟨le_self_add, fun a ha hay g hag => ?_⟩
  by_cases had : a ≤ cdDelta l
  · by_contra hg
    exact R.capδ a ha had g (lt_of_le_of_lt le_self_add (not_le.1 hg)) hag
  · have hδa : cdDelta l < a := not_le.1 had
    have ha2 : a < cdDelta l + cdDelta l := lt_of_le_of_lt hay ((add_lt_add_iff_left _).2 hx)
    have hga : g ≤ a := by
      by_contra hlt
      exact rz_not_indec hδa ha2 (indec_of_lt1 hag (not_le.1 hlt))
    exact hga.trans hay

theorem rzK_mem {l x : Ordinal.{0}} (R : RstK (upsilon l) (upsilon (l + ω)) (upsilon (l + ω + 1)))
    (hx : x < cdDelta l) : cdDelta l + x ∈ cdK l := Or.inl (rzClosed R hx)

/-- **`k_λ(x) = δ_λ + x` for `x < δ_λ`.** -/
theorem rzk_eq {l x : Ordinal.{0}} (R : RstK (upsilon l) (upsilon (l + ω)) (upsilon (l + ω + 1)))
    (hx : x < cdDelta l) : cdk l x = cdDelta l + x :=
  cdk_interval (fun _ hy => rzK_mem R (lt_of_le_of_lt hy hx)) x le_rfl

/-- `r(λ) = δ_λ + Θ_λ(m_λ)` when `Θ_λ(m_λ) < δ_λ`. -/
theorem rzR_eq {l : Ordinal.{0}} (R : RstK (upsilon l) (upsilon (l + ω)) (upsilon (l + ω + 1)))
    (h : cdTheta S l (cdCode S l) < cdDelta l) : cdR S l = cdDelta l + cdTheta S l (cdCode S l) :=
  rzk_eq R h

/-- **ENUM-REACH at a restart with a short reach `δ_λ + o`** (`o < δ_λ`): LOWER iff `Θ_λ(m_λ) ≤ o`, UPPER iff
`o ≤ Θ_λ(m_λ)`, both iff `Θ_λ(m_λ) = o`. -/
theorem rzEnum_of_reach {l o : Ordinal.{0}}
    (R : RstK (upsilon l) (upsilon (l + ω)) (upsilon (l + ω + 1))) (ho : o < cdDelta l)
    (hr : IsReach R2C (upsilon l) (cdDelta l + o)) :
    (CdLower S l ↔ cdTheta S l (cdCode S l) ≤ o) ∧ (CdUpper S l ↔ o ≤ cdTheta S l (cdCode S l)) ∧
      ((CdUpper S l ∧ CdLower S l) ↔ cdTheta S l (cdCode S l) = o) := by
  have hko : cdk l o = cdDelta l + o := rzk_eq R ho
  have hR : cdR S l = cdk l (cdTheta S l (cdCode S l)) := rfl
  have hmono := (cdk_strictMono l)
  refine ⟨?_, ?_, ?_⟩
  · rw [cdLower_iff_le hr, hR, ← hko]; exact hmono.le_iff_le
  · rw [cdUpper_iff_ge hr, hR, ← hko]; exact hmono.le_iff_le
  · rw [cdExact_iff]
    constructor
    · intro h
      have e : cdR S l = cdDelta l + o := Lb.lbReach_unique h hr
      rw [hR, ← hko] at e
      exact (cdk_inj l).1 e
    · intro h
      have e : cdR S l = cdDelta l + o := by rw [hR, h, hko]
      rw [e]; exact hr

end Googology.Trans.PoR.InaccPsi.R2.Rz
