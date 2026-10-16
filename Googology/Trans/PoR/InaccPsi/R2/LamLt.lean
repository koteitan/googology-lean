import Googology.Trans.PoR.InaccPsi.R2.ORec
import Googology.Trans.PoR.InaccPsi.R2.CitedCore

/-!
# `Λ_ε < Ω₁`

The core of `R₂^C` is a countable ordinal ([C09] Corollary 15.15, `C09_cor15_15`), while CORE-C
(`coreO`) puts `[0, υ_B)` into the core for every `B ≤ Λ_ε` (`ω² ∣ B`, `B < Ω₁`).  If `Λ_ε` were `Ω₁`,
every countable `B` would do, and the core would contain `[0, Ω₁)`.

* `not_core_all` (no countable family of initial segments `[0, υ_B)` exhausting `Ω₁` lies in the core);
* `LamE_lt_Om1` (**`Λ_ε < Ω₁`**);
* `blkO_LamE`, `coreO_LamE` (Theorem BLK^O and CORE-C at `B = Λ_ε` itself).

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order

theorem Om1_mul_lt {x y : Ordinal.{0}} (hx : x < Om1) (hy : y < Om1) : x * y < Om1 :=
  isPrincipal_mul_omega 1 hx hy

/-- If `[0, υ_B) ⊆ Core(R₂^C)` for every countable multiple `B` of `ω²`, then `False`: the core is a
countable ordinal ([C09] Cor 15.15). -/
theorem not_core_all
    (h : ∀ B, ω * ω ∣ B → B < Om1 → Set.Iio (upsilon B) ⊆ Core R2C) : False := by
  obtain ⟨κ, hκ, hC⟩ := C09_cor15_15
  set B := ω * ω * (κ + 1) with hB
  have hκ1 : κ + 1 < Om1 := Om1_add_lt hκ (lt_trans one_lt_omega0 omega0_lt_omega_one)
  have hB1 : B < Om1 := Om1_mul_lt ww_lt_Om1 hκ1
  have hκB : κ < B := lt_of_lt_of_le (lt_add_one κ)
    (le_mul_right (κ + 1) (mul_pos omega0_pos omega0_pos))
  have hκu : κ < upsilon B := lt_of_lt_of_le hκB (upsilon_normal.strictMono.le_apply)
  have := h B (dvd_mul_right _ _) hB1 hκu
  rw [hC] at this
  exact lt_irrefl κ this

/-- **`Λ_ε < Ω₁`**: the least restart index below which `ε_{x+1}` is realized cofinally (for the
recursive offset `O` of `R2.ORec`) is countable. -/
theorem LamE_lt_Om1 : LamE < Om1 := by
  rcases LamE_le_Om1.lt_or_eq with h | h
  · exact h
  · exfalso
    exact not_core_all (fun B hm hc => coreO hm hc (by rw [h]; exact hc.le))

/-- `Λ_ε` is a restart index (a nonzero multiple of `ω²`) with `ε_{x+1}` realized cofinally below
it. -/
theorem LamE_spec : IsRestartIdx LamE ∧ CofE Orec LamE := by
  have hne : (insert Om1 {l | IsRestartIdx l ∧ CofE Orec l}).Nonempty := ⟨Om1, Set.mem_insert _ _⟩
  rcases csInf_mem hne with h | h
  · exact absurd (h ▸ LamE_lt_Om1 : Om1 < Om1) (lt_irrefl _)
  · exact h

/-- **Theorem BLK^O at `B = Λ_ε`** (now that `Λ_ε < Ω₁`). -/
theorem blkO_LamE :
    (∀ c d, c < d → d < upsilon LamE → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < LamE ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < LamE →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + Orec l)) ∧
    (∀ α < upsilon LamE, ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  blkO (by have := (ri_iff.1 LamE_spec.1).2; exact this) LamE_lt_Om1 le_rfl

/-- **CORE-C at `Λ_ε`**: `[0, υ_{Λ_ε}) ⊆ Core(R₂^C)`. -/
theorem coreO_LamE : Set.Iio (upsilon LamE) ⊆ Core R2C :=
  coreO (ri_iff.1 LamE_spec.1).2 LamE_lt_Om1 le_rfl

end Googology.Trans.PoR.InaccPsi.R2
