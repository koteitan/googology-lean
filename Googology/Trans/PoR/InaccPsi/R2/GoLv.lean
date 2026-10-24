import Googology.Trans.PoR.InaccPsi.R2.GoIt

/-!
# THE PULL-BACK TEST AT EVERY FINITE VEBLEN LEVEL AND AT LEVEL `ω`

`R2.GnZ` (`gn_eps_down`) pulls the `ε`-test back along `π`: if `π(u)` is an `ε`-number then so is `u`, through
`le1R_two_iff` (`a ≤₁ a·2 ⇔ a ∈ P₁`) and `down_le1R`.  The same works at every finite level `n ≥ 1` with
`R2.VzR` (`vz_le1R_level`: `a ≤₁ a·(n+1) ⇒ a ∈ P_n = range φ(n, ·)`) and at level `ω`:

* `go_level_down` (**`π(u) ≤₁ π(u)·(n+1)` in `R₁⁺` ⇒ `u ∈ range φ(n, ·)`**, `υ`-points `σ < ρ`, `1 ≤ n < ω`);
* `go_level_down_omega` (**`π(u) ≤₁ π(u)·(n+1)` for every `n` ⇒ `u ∈ range φ(ω, ·)`**);
* `go_level_gap` (no ordinal of level `≥ n` lies strictly between `φ(n, β)` and `φ(n, β+1)`), `go_level_pull`
  (**the successor case of Lemma IMG at level `n`**: a pull-back `u` with `π(u) ≤₁ π(u)·(n+1)` above `φ(n, β)` is at
  least `φ(n, β+1)`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Go

open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2

/-- **The pull-back test at level `n`**: `π(u) ≤₁ π(u)·(n+1)` gives `u ∈ range φ(n, ·)`. -/
theorem go_level_down {σ ρ u : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) (hu : u ∈ TB ρ σ)
    (hu1 : u < Om1) (hu0 : 0 < u) {n : ℕ} (hn : 1 ≤ n)
    (h : le1R (pi σ ρ u) (pi σ ρ u * ((n + 1 : ℕ) : Ordinal.{0}))) : u ∈ Set.range (veblen (n : Ordinal.{0})) := by
  obtain ⟨m1, m2⟩ := pi_mul_nat hB hu rfl (n + 1)
  have h2 := (down_le1R hσ hρ hB hu m1 hu1).2 (by rw [m2]; exact h)
  exact vz_le1R_level n hn u hu0 h2

/-- **The pull-back test at level `ω`**: `π(u) ≤₁ π(u)·(n+1)` for every `n` gives `u ∈ range φ(ω, ·)`. -/
theorem go_level_down_omega {σ ρ u : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ)
    (hu : u ∈ TB ρ σ) (hu1 : u < Om1) (hu0 : 0 < u)
    (h : ∀ n : ℕ, le1R (pi σ ρ u) (pi σ ρ u * ((n + 1 : ℕ) : Ordinal.{0}))) :
    u ∈ Set.range (veblen ω) := by
  refine (mem_range_veblen omega0_ne_zero).2 fun b hb => ?_
  obtain ⟨n, rfl⟩ := lt_omega0.1 hb
  have hP := go_level_down hσ hρ hB hu hu1 hu0 (n := n + 1) (by omega) (h (n + 1))
  exact (mem_range_veblen (by exact_mod_cast Nat.succ_ne_zero n)).1 hP n (by exact_mod_cast Nat.lt_succ_self n)

/-- No ordinal of level `≥ n` lies strictly between `φ(n, β)` and `φ(n, β+1)`. -/
theorem go_level_gap {o β u : Ordinal.{0}} (hu : u ∈ Set.range (veblen o)) (h : veblen o β < u) :
    veblen o (β + 1) ≤ u := by
  obtain ⟨γ, rfl⟩ := hu
  have hβγ : β < γ := (veblen_lt_veblen_iff_right).1 h
  exact (veblen_le_veblen_iff_right).2 (Order.add_one_le_of_lt hβγ)

/-- **The successor case of Lemma IMG at level `n`**: a pull-back `u` (`π(u) ≤₁ π(u)·(n+1)`) above `φ(n, β)` is at
least `φ(n, β+1)`; so `π(u) = f(φ(n, β+1)) < π(φ(n, β+1))` is impossible once `π(φ(n, β)) ≤ f(φ(n, β))`. -/
theorem go_level_pull {σ ρ u β : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) (hu : u ∈ TB ρ σ)
    (hu1 : u < Om1) {n : ℕ} (hn : 1 ≤ n)
    (h : le1R (pi σ ρ u) (pi σ ρ u * ((n + 1 : ℕ) : Ordinal.{0}))) (hβ : veblen (n : Ordinal.{0}) β < u) :
    veblen (n : Ordinal.{0}) (β + 1) ≤ u :=
  go_level_gap (go_level_down hσ hρ hB hu hu1 (lt_of_le_of_lt zero_le hβ) hn h) hβ

end Googology.Trans.PoR.InaccPsi.R2.Go
