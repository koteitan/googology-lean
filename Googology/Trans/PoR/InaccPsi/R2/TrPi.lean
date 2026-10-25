import Googology.Trans.PoR.InaccPsi.R2.SoFrag

/-!
# Composition of base changes

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`π_{σ,τ} : Tᵗ[σ] → T^σ` is a strictly increasing bijection ([W07a] Lemma 5.3 (b), (d), `R2.pi_bijOn`) that keeps
the parameters ([W07a] Lemma 5.3 (e), `R2.pi_ht_Par`).  Two strictly increasing maps of a set of ordinals with the
same image agree (a well-order has no non-trivial automorphism).  From these:

* `trEqOn_of_image` (**two strictly increasing maps of a set of ordinals with the same image are equal on it**);
* `trBases_trans`, `trPi_TB` (`π_{σ,τ}` maps `Tᵗ[ρ]` into `T^σ[ρ]`), `trPi_image` (onto), `trUp_TB`;
* `trPi_comp` (**`π_{ρ,σ} ∘ π_{σ,τ} = π_{ρ,τ}` on `Tᵗ[ρ]`**, the composition of base changes),
  `trUp_comp` (**`π_{σ,τ}⁻¹ ∘ π_{ρ,σ}⁻¹ = π_{ρ,τ}⁻¹` on `T^ρ`**), `trPi_up` (`π_{σ,τ} ∘ π_{ρ,τ}⁻¹ = π_{ρ,σ}⁻¹`);
* `trTB_sub` (`Tᵗ[σ] ∩ Ω₁` is closed under right subtraction: `x + y = z` with `x, z ∈ Tᵗ[σ]`, `z < Ω₁` gives
  `y ∈ Tᵗ[σ]`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Tr

open Ordinal Set Googology.Trans.PoR.InaccPsi.R2

/-- **Two strictly increasing maps of a set of ordinals with the same image agree on it.** -/
theorem trEqOn_of_image {A : Set Ordinal.{0}} {f g : Ordinal.{0} → Ordinal.{0}}
    (hf : StrictMonoOn f A) (hg : StrictMonoOn g A) (h : f '' A = g '' A) : EqOn f g A := by
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hx
  rcases lt_trichotomy (f x) (g x) with hlt | heq | hgt
  · exfalso
    obtain ⟨y, hy, hyx⟩ : f x ∈ g '' A := h ▸ ⟨x, hx, rfl⟩
    have hyx' : y < x := by
      by_contra hle
      rcases (not_lt.1 hle).lt_or_eq with h' | h'
      · have : g x < f x := by rw [← hyx]; exact hg hx hy h'
        exact absurd hlt (not_lt.2 this.le)
      · subst h'; exact absurd hyx (ne_of_gt hlt)
    have := IH y hyx' hy
    rw [hyx] at this
    exact absurd (hf hy hx hyx') (not_lt.2 this.symm.le)
  · exact heq
  · exfalso
    obtain ⟨y, hy, hyx⟩ : g x ∈ f '' A := h.symm ▸ ⟨x, hx, rfl⟩
    have hyx' : y < x := by
      by_contra hle
      rcases (not_lt.1 hle).lt_or_eq with h' | h'
      · have : f x < g x := by rw [← hyx]; exact hf hx hy h'
        exact absurd hgt (not_lt.2 this.le)
      · subst h'; exact absurd hyx (ne_of_gt hgt)
    have := IH y hyx' hy
    rw [hyx] at this
    exact absurd (hg hy hx hyx') (not_lt.2 this.le)

theorem trBases_trans {ρ σ τ : Ordinal.{0}} (h1 : Bases ρ σ) (h2 : Bases σ τ) : Bases ρ τ :=
  ⟨h1.1, h2.2.1, h1.2.2.1.trans h2.2.2.1, h2.2.2.2⟩

theorem trTB_mono {τ σ σ' : Ordinal.{0}} (h : σ ≤ σ') {x : Ordinal.{0}} (hx : x ∈ TB τ σ) : x ∈ TB τ σ' :=
  ⟨hx.1, hx.2.trans (Set.Iio_subset_Iio h)⟩

/-- **`π_{σ,τ}` maps `Tᵗ[ρ]` into `T^σ[ρ]`** (`ρ ≤ σ`). -/
theorem trPi_TB {ρ σ τ : Ordinal.{0}} (h : Bases σ τ) (hρ : ρ ≤ σ) {x : Ordinal.{0}} (hx : x ∈ TB τ ρ) :
    pi σ τ x ∈ TB σ ρ := by
  have hx' : x ∈ TB τ σ := trTB_mono hρ hx
  refine ⟨(pi_bijOn h).1.mapsTo hx', ?_⟩
  rw [(pi_ht_Par h hx').2]; exact hx.2

/-- **`π_{σ,τ}⁻¹` maps `T^σ[ρ]` into `Tᵗ[ρ]`** (`ρ ≤ σ`). -/
theorem trUp_TB {ρ σ τ : Ordinal.{0}} (h : Bases σ τ) {y : Ordinal.{0}} (hy : y ∈ TB σ ρ) :
    up σ τ y ∈ TB τ ρ := by
  obtain ⟨h1, h2⟩ := up_spec h hy.1
  refine ⟨h1.1, ?_⟩
  have := (pi_ht_Par h h1).2
  rw [h2] at this
  rw [← this]; exact hy.2

/-- **`π_{σ,τ}` maps `Tᵗ[ρ]` onto `T^σ[ρ]`.** -/
theorem trPi_image {ρ σ τ : Ordinal.{0}} (h : Bases σ τ) (hρ : ρ ≤ σ) :
    pi σ τ '' TB τ ρ = TB σ ρ := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩; exact trPi_TB h hρ hx
  · intro hy
    exact ⟨up σ τ y, trUp_TB h hy, (up_spec h hy.1).2⟩

/-- **The composition of base changes: `π_{ρ,σ} ∘ π_{σ,τ} = π_{ρ,τ}` on `Tᵗ[ρ]`.** -/
theorem trPi_comp {ρ σ τ : Ordinal.{0}} (h1 : Bases ρ σ) (h2 : Bases σ τ) {x : Ordinal.{0}}
    (hx : x ∈ TB τ ρ) : pi ρ σ (pi σ τ x) = pi ρ τ x := by
  have h3 := trBases_trans h1 h2
  have hρσ := h1.2.2.1.le
  refine trEqOn_of_image (A := TB τ ρ) (f := fun u => pi ρ σ (pi σ τ u)) ?_ (pi_bijOn h3).2 ?_ hx
  · intro u hu v hv huv
    exact (pi_bijOn h1).2 (trPi_TB h2 hρσ hu) (trPi_TB h2 hρσ hv)
      ((pi_bijOn h2).2 (trTB_mono hρσ hu) (trTB_mono hρσ hv) huv)
  · rw [show (fun u => pi ρ σ (pi σ τ u)) = pi ρ σ ∘ pi σ τ from rfl, Set.image_comp,
      trPi_image h2 hρσ]
    have hT1 : pi ρ σ '' TB σ ρ = Tset ρ := (pi_bijOn h1).1.image_eq
    have hT3 : pi ρ τ '' TB τ ρ = Tset ρ := (pi_bijOn h3).1.image_eq
    rw [hT1, hT3]

/-- **`π_{σ,τ}⁻¹ ∘ π_{ρ,σ}⁻¹ = π_{ρ,τ}⁻¹` on `T^ρ`.** -/
theorem trUp_comp {ρ σ τ : Ordinal.{0}} (h1 : Bases ρ σ) (h2 : Bases σ τ) {y : Ordinal.{0}}
    (hy : y ∈ Tset ρ) : up σ τ (up ρ σ y) = up ρ τ y := by
  have h3 := trBases_trans h1 h2
  obtain ⟨hu1, hp1⟩ := up_spec h1 hy
  have hu2 : up σ τ (up ρ σ y) ∈ TB τ ρ := trUp_TB h2 hu1
  have hc := trPi_comp h1 h2 hu2
  rw [(up_spec h2 hu1.1).2, hp1] at hc
  exact (up_pi h3 hu2).symm.trans (congrArg (up ρ τ) hc.symm)

/-- `π_{σ,τ} ∘ π_{ρ,τ}⁻¹ = π_{ρ,σ}⁻¹` on `T^ρ`. -/
theorem trPi_up {ρ σ τ : Ordinal.{0}} (h1 : Bases ρ σ) (h2 : Bases σ τ) {y : Ordinal.{0}}
    (hy : y ∈ Tset ρ) : pi σ τ (up ρ τ y) = up ρ σ y := by
  rw [← trUp_comp h1 h2 hy, (up_spec h2 (up_spec h1 hy).1.1).2]

/-- **`Tᵗ[σ] ∩ Ω₁` is closed under right subtraction.** -/
theorem trTB_sub {σ τ : Ordinal.{0}} (h : Bases σ τ) {x y z : Ordinal.{0}} (hx : x ∈ TB τ σ)
    (hz : z ∈ TB τ σ) (hz1 : z < Om1) (hxyz : x + y = z) : y ∈ TB τ σ := by
  obtain ⟨m, -, -, -, hT, -⟩ := T_next (Or.inr h.1) (h.2.2.1.trans h.2.2.2)
  have hxz : x ≤ z := hxyz ▸ le_self_add
  have hpm := (pi_bijOn h).2.monotoneOn hx hz hxz
  have hpz1 : pi σ τ z < Om1 := down_lt_Om1 h hz hz1
  have hpzT : pi σ τ z ∈ Tset σ := (pi_bijOn h).1.mapsTo hz
  set y' := pi σ τ z - pi σ τ x with hy'
  have hy'le : y' ≤ pi σ τ z := Ordinal.sub_le_self _ _
  have hy'T : y' ∈ Tset σ :=
    (hT y' (hy'le.trans_lt hpz1)).2 (hy'le.trans_lt ((hT _ hpz1).1 hpzT))
  obtain ⟨hu, hpu⟩ := up_spec h hy'T
  obtain ⟨hxu, hpxu⟩ := pi_add h hx hu
  have e : pi σ τ (x + up σ τ y') = pi σ τ z := by
    rw [hpxu, hpu, hy']; exact Ordinal.add_sub_cancel_of_le hpm
  have e2 : x + up σ τ y' = z := (pi_bijOn h).1.injOn hxu hz e
  rw [← hxyz] at e2
  rw [← add_left_cancel e2]; exact hu

end Googology.Trans.PoR.InaccPsi.R2.Tr
