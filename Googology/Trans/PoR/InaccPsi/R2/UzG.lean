import Googology.Trans.PoR.InaccPsi.R2.UzTop
import Googology.Trans.PoR.InaccPsi.R2.UzIdx

/-!
# The ordinals visible at every top `θ_i`, `i ≥ i₀`: closure under `+`, `φ` and every lifted level map

`θ_i = ψ_{Ω_{i+1}}(Ω_ω)`, `Hˡ^{(s)}_γ = Ul.ulH S s γ`, `K^{(i)}_q = Ul.UlK S i q`.  `G_{i₀}` is the class of `x` with
`x ∈ K^{(i)}_{θ_i}` for every finite `i ≥ i₀` (`i₀ = 1` for the notation `T₁` of [W07a], whose parameters are all
ordinals below `Ω₁`):

* `uz_top_hl_ge` (**`G_{i₀}` is closed under `Hˡ^{(s)}` for `s ≥ i₀`**: for every level `γ < Ω_{s+2}` and
  `y < Ω_{s+1}` in `G_{i₀}`, `Hˡ^{(s)}_γ(y) ∈ G_{i₀}` and `Hˡ^{(s)}_γ(y) < θ_s`; the proof of `Uz.uz_top_hl` with the
  thresholds `i ≥ i₀`);
* `uz_G_add`, `uz_G_phi` (**`G_{i₀}` is closed under `+` and `φ`, and `θ_k` under both**), `uz_G_small` (every
  `x < Ω_{i₀}` is in `G_{i₀}`), `uz_G_Om` (`Ω_{k+1} ∈ G_{i₀}`), `uz_G_bound` (**`G_{i₀} ∩ Ω_{k+1} ⊆ θ_k`** for
  `k ≥ i₀`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Uz

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Ul
  Googology.Trans.PoR.InaccPsi.R2.Uo Googology.Trans.PoR.InaccPsi.R2.Us
  Googology.Trans.PoR.InaccPsi.R2.Uw

variable {S : InaccSeq.{0}} {s : Ordinal.{0}}

/-- **Closure under `Hˡ^{(s)}` from a threshold `i₀ ≤ s`**: for a level `γ < Ω_{s+2}` and `y < Ω_{s+1}` with
`γ, y ∈ K^{(i)}_{θ_i}` for every finite `i ≥ i₀`: `Hˡ^{(s)}_γ(y) < θ_s` and `Hˡ^{(s)}_γ(y) ∈ K^{(i)}_{θ_i}` for every
finite `i ≥ i₀`. -/
theorem uz_top_hl_ge (hs : s < ω) {i₀ γ y : Ordinal.{0}} (hi₀ : i₀ ≤ s) (hγV : γ < Om (s + 1 + 1))
    (hyW : y < Om (s + 1)) (hγ : ∀ i, i₀ ≤ i → i < ω → UlK S i (S.psi (Om ω) (Om (i + 1))) γ)
    (hy : ∀ i, i₀ ≤ i → i < ω → UlK S i (S.psi (Om ω) (Om (i + 1))) y) :
    ulH S s γ y < S.psi (Om ω) (Om (s + 1)) ∧
      ∀ i, i₀ ≤ i → i < ω → UlK S i (S.psi (Om ω) (Om (i + 1))) (ulH S s γ y) := by
  have hs1 : s + 1 < ω := Ui.ui_s1_lt_omega hs
  have hγθ : γ < S.psi (Om ω) (Om (s + 1 + 1)) :=
    uw_top_bound hs1 (hγ (s + 1) (hi₀.trans (lt_add_one s).le) hs1) hγV
  have hyθ : y < S.psi (Om ω) (Om (s + 1)) := uw_top_bound hs (hy s hi₀ hs) hyW
  have hlt : ulH S s γ y < S.psi (Om ω) (Om (s + 1)) := us_top_lt hs hγθ (hγ s hi₀ hs) hyθ
  refine ⟨hlt, fun i hi0 hi => ?_⟩
  rcases lt_or_ge i s with his | hsi
  · by_cases hfix : ulH S s γ y = y
    · rw [hfix]; exact hy i hi0 hi
    exact uz_L1_mpr hs his (uw_top_q i).1 (uw_top_q i).2.2 hγV hyW hfix (hγ i hi0 hi) (hy i hi0 hi)
  · rcases hsi.lt_or_eq with hsi' | rfl
    · refine UlK.small (hlt.trans ((psiS_bounds _ s).2.trans_le ?_))
      exact (Om_le_Om.2 (Order.add_one_le_of_lt hsi')).trans (uw_top_q i).2.1.le
    · exact UlK.small hlt

/-- `G_{i₀}` is closed under `+`. -/
theorem uz_G_add {i₀ a b : Ordinal.{0}} (ha : ∀ i, i₀ ≤ i → i < ω → UlK S i (S.psi (Om ω) (Om (i + 1))) a)
    (hb : ∀ i, i₀ ≤ i → i < ω → UlK S i (S.psi (Om ω) (Om (i + 1))) b) :
    ∀ i, i₀ ≤ i → i < ω → UlK S i (S.psi (Om ω) (Om (i + 1))) (a + b) :=
  fun i hi0 hi => UlK.add (ha i hi0 hi) (hb i hi0 hi)

/-- **`G_{i₀}` is closed under `φ`, and so is `θ_k`.** -/
theorem uz_G_phi {i₀ k a b : Ordinal.{0}} (ha : ∀ i, i₀ ≤ i → i < ω → UlK S i (S.psi (Om ω) (Om (i + 1))) a)
    (hb : ∀ i, i₀ ≤ i → i < ω → UlK S i (S.psi (Om ω) (Om (i + 1))) b)
    (haθ : a < S.psi (Om ω) (Om (k + 1))) (hbθ : b < S.psi (Om ω) (Om (k + 1))) :
    veblen a b < S.psi (Om ω) (Om (k + 1)) ∧
      ∀ i, i₀ ≤ i → i < ω → UlK S i (S.psi (Om ω) (Om (i + 1))) (veblen a b) :=
  ⟨(uw_top_q k).1.2 a haθ b hbθ, fun i hi0 hi => UlK.phi (ha i hi0 hi) (hb i hi0 hi)⟩

/-- Every `x < Ω_{i₀}` is in `G_{i₀}`. -/
theorem uz_G_small {i₀ x : Ordinal.{0}} (hx : x < Om i₀) :
    ∀ i, i₀ ≤ i → i < ω → UlK S i (S.psi (Om ω) (Om (i + 1))) x := fun i hi0 _ =>
  UlK.small (hx.trans_le ((Om_le_Om.2 hi0).trans (uw_top_q i).2.1.le))

/-- `Ω_{k+1} ∈ G_{i₀}` for finite `k`. -/
theorem uz_G_Om {i₀ k : Ordinal.{0}} (hk : k < ω) :
    ∀ i, i₀ ≤ i → i < ω → UlK S i (S.psi (Om ω) (Om (i + 1))) (Om (k + 1)) := fun _ _ _ => us_K_Om hk

/-- **`G_{i₀} ∩ Ω_{k+1} ⊆ θ_k`** for finite `k ≥ i₀`. -/
theorem uz_G_bound {i₀ k x : Ordinal.{0}} (hk : k < ω) (hik : i₀ ≤ k)
    (hx : ∀ i, i₀ ≤ i → i < ω → UlK S i (S.psi (Om ω) (Om (i + 1))) x) (hxk : x < Om (k + 1)) :
    x < S.psi (Om ω) (Om (k + 1)) :=
  uw_top_bound hk (hx k hik hk) hxk

end Googology.Trans.PoR.InaccPsi.R2.Uz
