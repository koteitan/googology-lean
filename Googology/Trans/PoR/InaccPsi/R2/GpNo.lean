import Googology.Trans.PoR.InaccPsi.R2.GpFr
import Googology.Trans.PoR.InaccPsi.R2.TeAtom

/-!
# THE EXACT FAILING CASE: no digit system has a constant `ε`-index `≥ ε₀` in its base

A digit system `D : GoD` (`R2.GoD`) asks Lemma EXACT for its base reading `b` at EVERY pair of bases `σ < ρ` (the field
`b_pi` has no gate).  The recursion `R2.GpRec` reads the base of `gpD ν` as `b(x) = φ(1, Γ_{x+1}-index + ν)` with a
CONSTANT `ν < ε₀`.  Its first missing index is `ν = ε₀`, and there the constant reading is impossible:

* `gp_no_const` (**for every `ε`-number `δ < Ω₁` and `t < δ`, NO digit system has the base reading
  `b(x) = φ(1, gpI x + δ + t)`**: at `σ = δ`, `ρ = ε_{δ+1}` the base change sends both `b(ρ)` and
  `ε_{Γ_{ρ+1}+1+ρ+t}` (`R2.TeAtom`, `teEvA_pi`) to `b(σ)`, and `π` is injective on `Tᵖ[σ]`, so `δ = ρ`);
* `gp_no_eps0` (**the case `ν = ε₀`**: no digit system reads its base as `φ(1, gpI x + ε₀)`), `gp_no_union`
  (**so the systems `gpD ν`, `ν < ε₀`, have no union inside `GoD` with the base reading continuing them**).

So the next base `ε_{G+ε₀}` needs a digit system whose base reading has a gate (`b_pi` only for `σ` above the gate),
i.e. the `ε`-index read with `Ω₁ ↦ x` as a code.

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gp

open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
open Googology.Trans.PoR.InaccPsi.R2.Gn Googology.Trans.PoR.InaccPsi.R2.Go
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2

/-- **NO DIGIT SYSTEM HAS A CONSTANT `ε`-INDEX `δ + t` (`δ` an `ε`-number, `t < δ`) IN ITS BASE READING.** -/
theorem gp_no_const {δ t : Ordinal.{0}} (hδ : InE δ) (hδ1 : δ < Om1) (ht : t < δ) (D : GoD)
    (hb : ∀ x, InE x → x < Om1 → D.b x = veblen 1 (gpI x + (δ + t))) : False := by
  have hB : Bases δ (eN δ) := ⟨hδ, eN_E δ, lt_eN δ, eN_lt_Om1K hδ1⟩
  set ρ := eN δ with hρdef
  have hρ1 : ρ < Om1 := hB.2.2.2
  obtain ⟨b1, b2⟩ := D.b_pi δ ρ hB
  obtain ⟨r1, r2⟩ := pi_base hB
  have htT : t ∈ TB ρ δ := mem_TB_of_lt hB ht
  obtain ⟨s1, s2⟩ := pi_add hB r1 htT
  rw [r2, pi_lt hB ht] at s2
  obtain ⟨-, hρG, -, hGE, -⟩ := lgG_facts hB.2.1 hρ1
  have htρ : t < ρ := ht.trans hB.2.2.1
  have hν : ρ + t < lgG ρ := (inE_indec hGE).add_lt hρG (htρ.trans hρG)
  obtain ⟨e1, e2⟩ := Te.teEvA_pi hB s1 hν
  rw [s2] at e2
  have hω1 : ω ≤ ρ + t := (omega0_lt_inE hB.2.1).le.trans le_self_add
  have hω2 : ω ≤ δ + t := (omega0_lt_inE hδ).le.trans le_self_add
  have hσ : evA (lgG δ) (1 + (δ + t)) = D.b δ := by
    rw [hb δ hδ hδ1, one_add_of_omega0_le hω2]; rfl
  have hy : evA (lgG ρ) (1 + (ρ + t)) = veblen 1 (gpI ρ + (ρ + t)) := by
    rw [one_add_of_omega0_le hω1]; rfl
  rw [hσ, ← b2] at e2
  have heq : D.b ρ = evA (lgG ρ) (1 + (ρ + t)) := (pi_bijOn hB).1.injOn b1 e1 e2.symm
  rw [hb ρ hB.2.1 hρ1, hy] at heq
  have h1 := (veblen_injective 1) heq
  have h2 : δ + t < ρ + t := ((inE_indec hB.2.1).add_lt (lt_eN δ) htρ).trans_le le_self_add
  exact absurd (add_left_cancel h1) h2.ne

/-- **THE FIRST MISSING INDEX `ε₀`**: no digit system reads its base as `φ(1, gpI x + ε₀) = ε_{Γ_{x+1}+ε₀}`. -/
theorem gp_no_eps0 (D : GoD) (hb : ∀ x, InE x → x < Om1 → D.b x = veblen 1 (gpI x + ε₀)) : False := by
  have h0 : (ε₀ : Ordinal.{0}) < Om1 := (go_eps0_le (eN_E 0)).trans_lt (eN_lt_Om1K (Rj.rj_Om1_inE.pos))
  refine gp_no_const go_eps0_E h0 (epsilon_pos 0) D fun x hx hx1 => ?_
  rw [add_zero]; exact hb x hx hx1

/-- **The systems `gpD ν`, `ν < ε₀`, have no union in `GoD` continuing their base readings**: a digit system whose
base reading is the supremum `sup_{ν<ε₀} φ(1, gpI x + ν)` of theirs does not exist. -/
theorem gp_no_union (D : GoD)
    (hb : ∀ x, InE x → x < Om1 → D.b x = ⨆ ν : Iio (ε₀ : Ordinal.{0}), (gpD ν.1).b x) : False := by
  refine gp_no_eps0 D fun x hx hx1 => ?_
  rw [hb x hx hx1]
  have hbd : BddAbove (range fun ν : Iio (ε₀ : Ordinal.{0}) => (gpD ν.1).b x) :=
    ⟨veblen 1 (gpI x + ε₀), by
      rintro _ ⟨ν, rfl⟩
      show (gpD ν.1).b x ≤ _
      rw [gpD_b ν.2 hx hx1]
      exact (isNormal_veblen 1).monotone ((add_le_add_iff_left _).2 ν.2.le)⟩
  haveI : Nonempty (Iio (ε₀ : Ordinal.{0})) := ⟨⟨0, epsilon_pos 0⟩⟩
  refine le_antisymm (ciSup_le fun ν => ?_) ?_
  · show (gpD ν.1).b x ≤ _
    rw [gpD_b ν.2 hx hx1]
    exact (isNormal_veblen 1).monotone ((add_le_add_iff_left _).2 ν.2.le)
  · have hlim : IsSuccLimit (gpI x + ε₀) := isSuccLimit_add _ go_eps0_lim
    refine ((isNormal_veblen 1).le_iff_forall_le hlim).2 fun a ha => ?_
    obtain ⟨d, hd, had⟩ := (lt_add_iff (epsilon_pos 0).ne').1 ha
    refine ((isNormal_veblen 1).monotone had).trans ?_
    refine le_trans ?_ (le_ciSup hbd ⟨d, hd⟩)
    rw [gpD_b hd hx hx1]

end Googology.Trans.PoR.InaccPsi.R2.Gp
