import Googology.Trans.PoR.InaccPsi.R2.MvK

/-!
# `SfEQlong` from `L(ω+1) ≤ ν_C`: the long codes whose reading lies below `δ_λ` need only the reading

`B_n = Bc.bcB S n`, `c_n = L(n+1)`, `ρ_λ = υ_λ`, `δ_λ = υ_{λ+ω+1}`, `m_λ` the code, `Θ_λ` the reading (the
order type of the codes of `Cl(A_{η_λ}, ρ_λ)` below `m_λ`), `r(λ) = k_λ(Θ_λ(m_λ))`, `λ'` the restart with
`B_n(ρ_λ) = ρ_{λ'}`.  A long code is `ρ_λ < m_λ`.

* `MvThLong S` (**the reading moves with `B_n`** at the long codes with `Θ_λ(m_λ) < δ_λ`; a hypothesis name):
  `Θ_{λ'}(m_{λ'}) = B_n(Θ_λ(m_λ))` — a statement on the hulls `Cl(A_η, ρ)` and `B_n` only (no `≤₁`);
* `MvEQbig S` (a hypothesis name): `SfEQlong` at the long codes with `δ_λ ≤ Θ_λ(m_λ)`;
* `mvEQlong`: **`L(ω+1) ≤ ν_C`, `MvThLong` and `MvEQbig` give `Sf.SfEQlong S`** (below `δ_λ`,
  `k_λ(x) = δ_λ + x` and `k_{λ'}(B_n x) = B_n(k_λ(x))`, `Mv.mvk_move`);
* `mvThLong_of_EQlong` (**`MvThLong` is not stronger than `SfEQlong`**): under `L(ω+1) ≤ ν_C`, `SfEQlong`
  gives `MvThLong` (`k_{λ'}(B_n Θ_λ(m_λ)) = B_n(r(λ)) = r(λ') = k_{λ'}(Θ_{λ'}(m_{λ'}))`, `k_{λ'}` injective).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Mv

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cx

variable {S : InaccSeq.{0}}

/-- **The reading moves with `B_n`** at the long codes of the range whose reading is below `δ_λ`. -/
def MvThLong (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
    IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' → upsilon l < cdCode S l →
    cdTheta S l (cdCode S l) < cdDelta l →
    cdTheta S l' (cdCode S l') = Bc.bcB S n (cdTheta S l (cdCode S l))

/-- `SfEQlong` at the long codes of the range whose reading is at least `δ_λ`. -/
def MvEQbig (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
    IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' → upsilon l < cdCode S l →
    cdDelta l ≤ cdTheta S l (cdCode S l) → Bc.bcB S n (cdR S l) = cdR S l'

/-- **`L(ω+1) ≤ ν_C`, `MvThLong` and `MvEQbig` give `SfEQlong`.** -/
theorem mvEQlong (hν : Nc.ncL S (ω + 1) ≤ nuC) (hth : MvThLong S) (hbig : MvEQbig S) :
    Sf.SfEQlong S := by
  intro n l l' hR h1 hr hl' hB hm
  by_cases hΘ : cdDelta l ≤ cdTheta S l (cdCode S l)
  · exact hbig n l l' hR h1 hr hl' hB hm hΘ
  · have hΘ' := not_le.1 hΘ
    have hδr : cdDelta l < Bc.bcC S (n + 1) := (cdR_ge S l).trans_lt hr
    show Bc.bcB S n (cdk l (cdTheta S l (cdCode S l))) = cdk l' (cdTheta S l' (cdCode S l'))
    rw [hth n l l' hR h1 hr hl' hB hm hΘ']
    exact (mvk_move hν hR.1 hl' h1 hδr hB hΘ').symm

/-- **`SfEQlong` gives `MvThLong`** under `L(ω+1) ≤ ν_C`. -/
theorem mvThLong_of_EQlong (hν : Nc.ncL S (ω + 1) ≤ nuC) (h : Sf.SfEQlong S) : MvThLong S := by
  intro n l l' hR h1 hr hl' hB hm hΘ
  have hδr : cdDelta l < Bc.bcC S (n + 1) := (cdR_ge S l).trans_lt hr
  have hEQ := h n l l' hR h1 hr hl' hB hm
  have hk := mvk_move hν hR.1 hl' h1 hδr hB hΘ
  have e : cdk l' (Bc.bcB S n (cdTheta S l (cdCode S l))) = cdk l' (cdTheta S l' (cdCode S l')) :=
    hk.trans hEQ
  exact ((cdk_inj l').1 e).symm

end Googology.Trans.PoR.InaccPsi.R2.Mv
