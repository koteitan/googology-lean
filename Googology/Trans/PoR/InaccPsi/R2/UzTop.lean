import Googology.Trans.PoR.InaccPsi.R2.UzL1
import Googology.Trans.PoR.InaccPsi.R2.UwTop

/-!
# The ordinals visible at every top `θ_i` are closed under every lifted level map (no notation hypothesis)

`θ_i = ψ_{Ω_{i+1}}(Ω_ω)`, `Hˡ^{(s)}_γ = Ul.ulH S s γ`, `K^{(i)}_q = Ul.UlK S i q`.

* `uz_top_hl` (**closure under `Hˡ^{(s)}`**: for every level `γ < Ω_{s+2}` and `y < Ω_{s+1}`, both in
  `K^{(i)}_{θ_i}` for every finite `i`, also `Hˡ^{(s)}_γ(y)` is, and `Hˡ^{(s)}_γ(y) < θ_s`; `Uw.uw_top_hl` without
  the hypothesis `γ ∈ ⋃ a, Cl(a, 0)`, through `Uz.uz_L1_mpr`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Uz

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Ul
  Googology.Trans.PoR.InaccPsi.R2.Uo Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Us
  Googology.Trans.PoR.InaccPsi.R2.Uw

variable {S : InaccSeq.{0}} {s : Ordinal.{0}}

/-- **Closure under `Hˡ^{(s)}`**: for every level `γ < Ω_{s+2}` and `y < Ω_{s+1}` with
`γ, y ∈ K^{(i)}_{θ_i}` for every finite `i`: `Hˡ^{(s)}_γ(y) < θ_s` and `Hˡ^{(s)}_γ(y) ∈ K^{(i)}_{θ_i}` for every
finite `i`. -/
theorem uz_top_hl (hs : s < ω) {γ y : Ordinal.{0}} (hγV : γ < Om (s + 1 + 1))
    (hyW : y < Om (s + 1)) (hγ : ∀ i, i < ω → UlK S i (S.psi (Om ω) (Om (i + 1))) γ)
    (hy : ∀ i, i < ω → UlK S i (S.psi (Om ω) (Om (i + 1))) y) :
    ulH S s γ y < S.psi (Om ω) (Om (s + 1)) ∧ ∀ i, i < ω → UlK S i (S.psi (Om ω) (Om (i + 1))) (ulH S s γ y) := by
  have hs1 : s + 1 < ω := Ui.ui_s1_lt_omega hs
  have hγθ : γ < S.psi (Om ω) (Om (s + 1 + 1)) := uw_top_bound hs1 (hγ (s + 1) hs1) hγV
  have hyθ : y < S.psi (Om ω) (Om (s + 1)) := uw_top_bound hs (hy s hs) hyW
  have hlt : ulH S s γ y < S.psi (Om ω) (Om (s + 1)) := us_top_lt hs hγθ (hγ s hs) hyθ
  refine ⟨hlt, fun i hi => ?_⟩
  rcases lt_or_ge i s with his | hsi
  · by_cases hfix : ulH S s γ y = y
    · rw [hfix]; exact hy i hi
    exact uz_L1_mpr hs his (uw_top_q i).1 (uw_top_q i).2.2 hγV hyW hfix (hγ i hi) (hy i hi)
  · rcases hsi.lt_or_eq with hsi' | rfl
    · refine UlK.small (hlt.trans ((psiS_bounds _ s).2.trans_le ?_))
      exact (Om_le_Om.2 (Order.add_one_le_of_lt hsi')).trans (uw_top_q i).2.1.le
    · exact UlK.small hlt

end Googology.Trans.PoR.InaccPsi.R2.Uz
