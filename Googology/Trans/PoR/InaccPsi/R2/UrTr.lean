import Googology.Trans.PoR.InaccPsi.R2.CitedUr
import Googology.Trans.PoR.InaccPsi.R2.SiUnc

/-!
# The subcase `Γ^* < α` at every level with data below `α`: `R2.uhVt_tr` as a theorem

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

* `urDat_le` (**`rjDat(Ω₁·M) ≤ rjDat M`** for every `M < ε_{Ω₁+1}`, from `Si.si_rjDat_Om1_mul` and
  `Si.si_rjDat_Om1_mul_small`);
* `urVt_tr_uh` (**the statement of `R2.uhVt_tr`, proved from `R2.urVt_tr2`**: data `rjDat M < τ` gives
  `rjDat(Ω₁·M) < τ < α`), so after the merge `uhVt_tr` is a theorem and the axiom count is unchanged.

No new axiom beyond `R2.urVt_tr2`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ur

open Ordinal Googology.Trans.PoR.InaccPsi.R2

/-- **`rjDat(Ω₁·M) ≤ rjDat M`** for `M < ε_{Ω₁+1}`. -/
theorem urDat_le {M : Ordinal.{0}} (hME : M < Gg.ggE) : Rj.rjDat (Om1 * M) ≤ Rj.rjDat M := by
  rcases lt_or_ge M Om1 with h | h
  · rw [Rj.rjDat_small h]; exact Si.si_rjDat_Om1_mul_small M h
  · exact Si.si_rjDat_Om1_mul M h hME

/-- **`R2.uhVt_tr` is a theorem from `R2.urVt_tr2`** (the same statement): for `τ ∈ E ∩ Ω₁`, `n ≥ 1`, a code
`1 ≤ M < ε_{Ω₁+1}` with `rjDat M < τ` and `ρ < Ω₁`, both translations of the subcase `Γ^* < α`. -/
theorem urVt_tr_uh {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) {n : ℕ} (hn : 1 ≤ n) {M ρ : Ordinal.{0}}
    (hM1 : 1 ≤ M) (hME : M < Gg.ggE) (hMτ : Rj.rjDat M < τ) (hρ1 : ρ < Om1) :
    (Om1 * M + ρ ∈ Tset (Dl τ n) → vt (Dl τ n) (Om1 * M + ρ) < Dp τ n →
      vt (Dl τ n) (Om1 * M + ρ) = vt τ (Om1 * M + (Dl τ n + ρ))) ∧
    (Om1 * M + (Dl τ n + ρ) ∈ Tset τ → vt τ (Om1 * M + (Dl τ n + ρ)) < Dp τ n →
      vt τ (Om1 * M + (Dl τ n + ρ)) = vt (Dl τ n) (Om1 * M + ρ)) := by
  have hΓE : Om1 * M < Gg.ggE := Si.si_E_inE.mul_lt Rj.rj_Om1_lt_E hME
  have hα : Rj.rjDat (Om1 * M) < Dl τ n :=
    lt_of_le_of_lt (urDat_le hME) (hMτ.trans (Dl_E hτ hτ1 hn).1)
  obtain ⟨h1, h2⟩ := urVt_tr2 hτ hτ1 hn hM1 hΓE hα hρ1
  exact ⟨fun a b => (h1 a b).2, fun a b => (h2 a b).2⟩

end Googology.Trans.PoR.InaccPsi.R2.Ur
