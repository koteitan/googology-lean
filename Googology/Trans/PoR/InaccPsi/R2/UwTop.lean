import Googology.Trans.PoR.InaccPsi.R2.UwL1
import Googology.Trans.PoR.InaccPsi.R2.UsTop

/-!
# The ordinals visible at every top `θ_i` are closed under every lifted level map

`θ_i = ψ_{Ω_{i+1}}(Ω_ω)` (`θ_1 = ConjT.th S = θ`), `Hˡ^{(s)}_γ = Ul.ulH S s γ`, `K^{(i)}_q = Ul.UlK S i q`.  The ψ-side
of the bound `Tᵗ ∩ Ω_{k+1} ⊆ θ_k` ([W07a] Thm 3.23 / Cor 3.24) is the invariant "`x ∈ K^{(i)}_{θ_i}` for every
finite `i`":

* `uw_top_q` (`θ_i` is strongly critical, `Ω_i < θ_i ≤ Ω_{i+1}`), `uw_top_bound` (**a member of `K^{(k)}_{θ_k}` below
  `Ω_{k+1}` is below `θ_k`**);
* `uw_top_hl` (**closure under `Hˡ^{(s)}`**: for a level `γ < Ω_{s+2}` of the notation and `y < Ω_{s+1}`, both in
  `K^{(i)}_{θ_i}` for every finite `i`, also `Hˡ^{(s)}_γ(y)` is, and `Hˡ^{(s)}_γ(y) < θ_s`; below `s` by (L1)
  `Uw.uw_L1_mpr`, at `s` by `Us.us_top_lt`, above `s` since the value is below `θ_s`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Uw

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Ul
  Googology.Trans.PoR.InaccPsi.R2.Uo Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Us

variable {S : InaccSeq.{0}} {s : Ordinal.{0}}

/-- `θ_i = ψ_{Ω_{i+1}}(Ω_ω)` is strongly critical with `Ω_i < θ_i ≤ Ω_{i+1}`. -/
theorem uw_top_q (i : Ordinal.{0}) :
    SC (S.psi (Om ω) (Om (i + 1))) ∧ Om i < S.psi (Om ω) (Om (i + 1)) ∧ S.psi (Om ω) (Om (i + 1)) ≤ Om (i + 1) :=
  ⟨Ui.ui_psi_SC _, (psiS_bounds _ i).1, (psiS_bounds _ i).2.le⟩

/-- **A member of `K^{(k)}_{θ_k}` below `Ω_{k+1}` is below `θ_k`.** -/
theorem uw_top_bound {k x : Ordinal.{0}} (hk : k < ω) (hx : UlK S k (S.psi (Om ω) (Om (k + 1))) x)
    (hxk : x < Om (k + 1)) : x < S.psi (Om ω) (Om (k + 1)) :=
  ulK_lt_W hk (uw_top_q k).1 (uw_top_q k).2.1 hx hxk

/-- **Closure under `Hˡ^{(s)}`**: for a level `γ < Ω_{s+2}` of the notation and `y < Ω_{s+1}` with
`γ, y ∈ K^{(i)}_{θ_i}` for every finite `i`: `Hˡ^{(s)}_γ(y) < θ_s` and `Hˡ^{(s)}_γ(y) ∈ K^{(i)}_{θ_i}` for every
finite `i`. -/
theorem uw_top_hl (hs : s < ω) {γ y : Ordinal.{0}} (hγV : γ < Om (s + 1 + 1)) (hγN : γ ∈ ⋃ a, S.CSet a 0)
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
    exact uw_L1_mpr hs his (uw_top_q i).1 (uw_top_q i).2.2 hγV hγN hyW hfix (hγ i hi) (hy i hi)
  · rcases hsi.lt_or_eq with hsi' | rfl
    · refine UlK.small (hlt.trans ((psiS_bounds _ s).2.trans_le ?_))
      exact (Om_le_Om.2 (Order.add_one_le_of_lt hsi')).trans (uw_top_q i).2.1.le
    · exact UlK.small hlt

end Googology.Trans.PoR.InaccPsi.R2.Uw
