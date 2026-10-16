import Googology.Trans.PoR.InaccPsi.R2.Defs

/-!
# `k`-nests: the definition

A **`k`-nest** of `R₂^C` is `a₀ < a₁ < ⋯ < a_{k-1} < b_{k-1} < ⋯ < b₀` with `aᵢ <₂ bᵢ` (`NestSeq k a b`).
The definition stands alone here so that the cited fact `C09_nestk` of `R2.CitedCore` (a `k`-nest exists
for every `k`) can be stated before the modules that use the case `k = 2`.  The facts about nests are in
`R2.NestK`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

/-- **A `k`-nest**: `a 0 < ⋯ < a (k-1) < b (k-1) < ⋯ < b 0` with `a i <₂ b i`. -/
def NestSeq (k : ℕ) (a b : ℕ → Ordinal.{0}) : Prop :=
  (∀ i, i + 1 < k → a i < a (i + 1) ∧ b (i + 1) < b i) ∧ (∀ i, i < k → a i < b i ∧ le2 (a i) (b i))

end Googology.Trans.PoR.InaccPsi.R2
