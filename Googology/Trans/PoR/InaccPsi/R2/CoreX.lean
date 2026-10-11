import Googology.Trans.PoR.InaccPsi.R2.OffV
import Googology.Trans.PoR.InaccPsi.R2.CoreC

/-!
# Theorem CORE-C in `R₂^C` up to `V_ω(1)` (FRAG-free)

By the block structure (`Good.below`: no point below `υ_B` is `≤₁` a point `≥ υ_B`), no `κ < υ_B` has
`κ ≤₁ ∞`; so by Carlson's theorem on the core (Carlson, Patterns of resemblance of order 2, APAL 158
(2009), Theorem 14.14: the core of `R₂` is the least `κ` with `κ ≤₁ ∞`, or all ordinals) every
ordinal below `υ_B` is in `Core(R₂^C)`.

* `core_gen`: for an offset specification `OffSpec O B`, `[0, υ_B) ⊆ Core(R₂^C)`.
* `core_Xi` (**Theorem CORE-C^Ξ**, with the referee's extension): `[0, υ_{Ξ_ω+ω²}) ⊆ Core(R₂^C)`;
  `core_Phi`: `[0, Φ_1) ⊆ Core(R₂^C)`; `core_V`: `[0, V_ω(1)) ⊆ Core(R₂^C)`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order

theorem core_gen {O : Ordinal.{0} → Ordinal.{0}} {B : Ordinal.{0}} (S : OffSpec O B) :
    Set.Iio (upsilon B) ⊆ Core R2C := by
  intro x hx
  have hno : ∀ κ < upsilon B, ¬ LeInfC κ := fun κ hκ h =>
    (good_B S).below κ hκ (upsilon B) le_rfl (h _ hκ.le)
  by_cases hex : ∃ κ, LeInfC κ
  · obtain ⟨κ, hκ⟩ := exists_isLeast_leInfC hex
    rw [C09_thm14_14.1 κ hκ]
    exact lt_of_lt_of_le hx (not_lt.1 (fun h => hno κ h hκ.1))
  · rw [C09_thm14_14.2 hex]; trivial

/-- **Theorem CORE-C^Ξ**: every ordinal below `υ_{Ξ_ω+ω²}` is in `Core(R₂^C)`. -/
theorem core_Xi : Set.Iio (upsilon (XiW + ω * ω)) ⊆ Core R2C := core_gen specXi

/-- Every ordinal below `Φ_1` is in `Core(R₂^C)`. -/
theorem core_Phi : Set.Iio Phi1 ⊆ Core R2C := by
  have := core_gen specPhi; rwa [Phi1_ups] at this

/-- Every ordinal below `V_ω(1)` is in `Core(R₂^C)`. -/
theorem core_V : Set.Iio Vw1 ⊆ Core R2C := by
  have := core_gen specV; rwa [Vw1_ups] at this

end Googology.Trans.PoR.InaccPsi.R2
