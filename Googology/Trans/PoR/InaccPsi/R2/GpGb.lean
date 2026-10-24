import Googology.Trans.PoR.InaccPsi.R2.GpNo

/-!
# LEMMA EXACT FOR THE BASE `ε_{Γ_{x+1}+ν(x)}` WHEN THE `ε`-INDEX IS A CODE (the base data of a gated digit system)

`R2.GpNo` shows that a constant index `ν ≥ ε₀` cannot be exact at every pair of bases.  It is exact at the pairs
`σ < ρ` with `ν < σ` (a gate), and an index read with `Ω₁ ↦ x` is exact at every pair once its reading is:

* `gp_b_pi_code` (**if `ν(ρ) ∈ Tᵖ[σ]`, `ω ≤ ν(ρ) < Γ_{ρ+1}` and `π(ν(ρ)) = ν(σ)`, then
  `π(φ(1, gpI ρ + ν(ρ))) = φ(1, gpI σ + ν(σ))`**, from [W07a] through `Te.teEvA_pi`);
* `gp_b_pi_gate` (**a constant index `ν < σ`: `π(φ(1, gpI ρ + ν)) = φ(1, gpI σ + ν)`**: the gated form of `b_pi`);
* `gp_b_pi_x` (**the index `x + t` (`t < σ`): `π(φ(1, gpI ρ + ρ + t)) = φ(1, gpI σ + σ + t)`**, no gate on `x`);
* `gp_b_eN` (**`ε_{b(x)+1} = ϑˣ(Ω₁ + Γ_{x+1} + ν + 1)` for `b(x) = φ(1, gpI x + ν)`, `ω ≤ ν`, `ν + 1 < Γ_{x+1}`**: the
  offset of a code index).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gp

open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
open Googology.Trans.PoR.InaccPsi.R2.Gn Googology.Trans.PoR.InaccPsi.R2.Go
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2

/-- **Lemma EXACT for `φ(1, gpI ρ + ν(ρ))` with a code index `ν`.** -/
theorem gp_b_pi_code {σ ρ ν ν' : Ordinal.{0}} (hB : Bases σ ρ) (hνT : ν ∈ TB ρ σ) (hν : ν < lgG ρ) (hω : ω ≤ ν)
    (hπ : pi σ ρ ν = ν') :
    veblen 1 (gpI ρ + ν) ∈ TB ρ σ ∧ pi σ ρ (veblen 1 (gpI ρ + ν)) = veblen 1 (gpI σ + ν') := by
  obtain ⟨e1, e2⟩ := Te.teEvA_pi hB hνT hν
  have hωσ : ω < σ := omega0_lt_inE hB.1
  have hωT : ω ∈ TB ρ σ := mem_TB_of_lt hB hωσ
  have hω' : ω ≤ ν' := by
    rw [← hπ, ← pi_lt hB hωσ]
    exact ((pi_bijOn hB).2.le_iff_le hωT hνT).2 hω
  rw [hπ, one_add_of_omega0_le hω'] at e2
  rw [one_add_of_omega0_le hω] at e1 e2
  exact ⟨e1, e2⟩

/-- **The gated form of `b_pi`**: a constant index `ν` with `ω ≤ ν < σ` is exact. -/
theorem gp_b_pi_gate {σ ρ ν : Ordinal.{0}} (hB : Bases σ ρ) (hνσ : ν < σ) (hω : ω ≤ ν) :
    veblen 1 (gpI ρ + ν) ∈ TB ρ σ ∧ pi σ ρ (veblen 1 (gpI ρ + ν)) = veblen 1 (gpI σ + ν) := by
  obtain ⟨-, hρG, -, -, -⟩ := lgG_facts hB.2.1 hB.2.2.2
  exact gp_b_pi_code hB (mem_TB_of_lt hB hνσ) ((hνσ.trans hB.2.2.1).trans hρG) hω (pi_lt hB hνσ)

/-- **The index read with `Ω₁ ↦ x`**: `π(φ(1, gpI ρ + ρ + t)) = φ(1, gpI σ + σ + t)` for `t < σ`. -/
theorem gp_b_pi_x {σ ρ t : Ordinal.{0}} (hB : Bases σ ρ) (ht : t < σ) :
    veblen 1 (gpI ρ + (ρ + t)) ∈ TB ρ σ ∧ pi σ ρ (veblen 1 (gpI ρ + (ρ + t))) = veblen 1 (gpI σ + (σ + t)) := by
  obtain ⟨r1, r2⟩ := pi_base hB
  obtain ⟨s1, s2⟩ := pi_add hB r1 (mem_TB_of_lt hB ht)
  rw [r2, pi_lt hB ht] at s2
  obtain ⟨-, hρG, -, hGE, -⟩ := lgG_facts hB.2.1 hB.2.2.2
  have hν : ρ + t < lgG ρ := (inE_indec hGE).add_lt hρG ((ht.trans hB.2.2.1).trans hρG)
  exact gp_b_pi_code hB s1 hν ((omega0_lt_inE hB.2.1).le.trans le_self_add) s2

/-- **The offset of a code index**: `ε_{φ(1, gpI x + ν)+1} = ϑˣ(Ω₁ + Γ_{x+1} + ν + 1)` (`ω ≤ ν`, `ν + 1 < Γ_{x+1}`). -/
theorem gp_b_eN {x ν : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hω : ω ≤ ν) (hν : ν + 1 < lgG x) :
    eN (veblen 1 (gpI x + ν)) = glA 1 (lgG x + (ν + 1)) x := by
  rw [Te.teGlA_eq_lt hx hx1 hν, one_add_of_omega0_le (hω.trans le_self_add), go_eN_veb, add_assoc]; rfl

end Googology.Trans.PoR.InaccPsi.R2.Gp
