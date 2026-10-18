import Googology.Trans.PoR.InaccPsi.R2.SfCex

/-!
# `TpEQall` split at the short codes: `k_{λ'}(B_n p) = B_n(k_λ(p))`

`B_n = Bc.bcB S n`, `c_n = L(n+1)`, `r(λ) = k_λ(Θ_λ(m_λ))` (`Cd.cdR`), `λ'` the restart with
`B_n(ρ_λ) = ρ_{λ'}`.  A code is *short* when `m_λ ≤ ρ_λ` (then `Θ_λ(m_λ) = m_λ`).

* `SfKMove S` (**the closed points move with `B_n`** at the short codes; a hypothesis name): for `λ` of
  the range with `c_n < ρ_λ`, `r(λ) < c_{n+1}`, `m_λ ≤ ρ_λ`, and `p = Θ_λ(m_λ)`:
  `k_{λ'}(B_n p) = B_n(k_λ(p))`;
* `SfEQlong S` (a hypothesis name): `TpEQall` at the long codes `ρ_λ < m_λ` of the range;
* `sfEQall`: **`SfKMove` and `SfEQlong` give `TpEQall`** (at a short code `Θ_{λ'}(m_{λ'}) = B_n(Θ_λ(m_λ))`,
  `Sf.sfTheta_move`);
* `sfRoad_min`: the road with `TpShift` proved, `TpLhEps` replaced by `SfLhTMove` and `TpEQall` by
  `SfKMove`, `SfEQlong`.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Sf

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cx

variable {S : InaccSeq.{0}}

/-- **The closed points move with `B_n`** at the short codes of the range. -/
def SfKMove (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
    IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' → cdCode S l ≤ upsilon l →
    cdk l' (Bc.bcB S n (cdTheta S l (cdCode S l))) = Bc.bcB S n (cdk l (cdTheta S l (cdCode S l)))

/-- `TpEQall` at the long codes of the range. -/
def SfEQlong (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
    IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' → upsilon l < cdCode S l →
    Bc.bcB S n (cdR S l) = cdR S l'

/-- **`SfKMove` and `SfEQlong` give `TpEQall`.** -/
theorem sfEQall (hk : SfKMove S) (hlong : SfEQlong S) : Tp.TpEQall S := by
  intro n l l' hR h1 hr hl' hB
  by_cases hm : cdCode S l ≤ upsilon l
  · have h2 : upsilon l < Bc.bcC S (n + 1) := (Tp.tpRho_le_R l).trans_lt hr
    obtain ⟨-, hΘ⟩ := sfTheta_move hR.1.1 h1 h2 hB hm
    show Bc.bcB S n (cdk l (cdTheta S l (cdCode S l))) = cdk l' (cdTheta S l' (cdCode S l'))
    rw [hΘ]
    exact (hk n l l' hR h1 hr hl' hB hm).symm
  · exact hlong n l l' hR h1 hr hl' hB (not_le.1 hm)

/-- **The road with `TpShift` proved and `TpLhEps`, `TpEQall` reduced.** -/
theorem sfRoad_min (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hN : CxNamed S) (hlh : SfLhTMove S) (hk : SfKMove S) (hlong : SfEQlong S) :
    CdEQ S ∧ CdTC S ∧ CdEMB2 S ∧ CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  sfRoad_lhT hU hO hL hV hN hlh (sfEQall hk hlong)

end Googology.Trans.PoR.InaccPsi.R2.Sf
