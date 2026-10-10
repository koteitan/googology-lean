import Googology.Trans.PoR.InaccPsi.R2.FragM

/-!
# Theorem FRAG2 for `R₂^C`

Def SK and Theorem FRAG2 of the paper proof (see RESTARTS.md §1), for `R₂^C` as defined in `Defs.lean`.
`R₂^C` is skeletal on `Z` if for `a < b` in `Z`: (SK1) a non-`υ`-point `a` has
`a ≤₁ b ⇔ a ≤₁ b in R₁⁺`; (SK2) a `υ`-point `a` has `a ≤₁ b ⇔ b ≤ cap(a)`; (SK3) `a <₂ b`
only if `a` and `b` are `υ`-points (the paper proof asks `b = a^∞`; only this weaker form is used).
Theorem FRAG2: a map that keeps `0, +, ≤, ≤₁` of `R₁⁺` and the `υ`-points (e.g. a FRAG map,
`frag`) is an isomorphism of `R₂^C` on `Y` iff it keeps (C1) `z ≤ cap(u)` and (C2) `u <₂ z` for
`υ`-points `u < z` in `Y`.  No axiom beyond those of FRAG (the statement itself uses only
`le1R`, `UpsPt`).
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal

/-- `R₂^C` is skeletal on `Z` with caps `cap` (Def SK of the paper proof). -/
def Skeletal (cap : Ordinal.{0} → Ordinal.{0}) (Z : Set Ordinal.{0}) : Prop :=
  ∀ a ∈ Z, ∀ b ∈ Z, a < b →
    (¬ UpsPt a → (le1 a b ↔ le1R a b)) ∧ (UpsPt a → (le1 a b ↔ b ≤ cap a)) ∧
      (le2 a b → UpsPt a ∧ UpsPt b)

/-- **Theorem FRAG2** (the paper proof). -/
theorem frag2 {cap : Ordinal.{0} → Ordinal.{0}} {Y : Finset Ordinal.{0}}
    {Ψ : Ordinal.{0} → Ordinal.{0}} (hmono : StrictMonoOn Ψ ↑Y)
    (hle1R : ∀ x ∈ Y, ∀ y ∈ Y, le1R x y ↔ le1R (Ψ x) (Ψ y))
    (hups : ∀ x ∈ Y, UpsPt (Ψ x) ↔ UpsPt x)
    (hSK : Skeletal cap (↑Y ∪ Ψ '' ↑Y)) :
    ((∀ x ∈ Y, ∀ y ∈ Y, le1 x y ↔ le1 (Ψ x) (Ψ y)) ∧
      (∀ x ∈ Y, ∀ y ∈ Y, le2 x y ↔ le2 (Ψ x) (Ψ y))) ↔
    (∀ u ∈ Y, ∀ z ∈ Y, UpsPt u → u < z →
      ((z ≤ cap u ↔ Ψ z ≤ cap (Ψ u)) ∧ (le2 u z ↔ le2 (Ψ u) (Ψ z)))) := by
  have hY : ∀ x ∈ Y, x ∈ (↑Y ∪ Ψ '' ↑Y : Set Ordinal.{0}) := fun x hx => Or.inl hx
  have hΨY : ∀ x ∈ Y, Ψ x ∈ (↑Y ∪ Ψ '' ↑Y : Set Ordinal.{0}) := fun x hx =>
    Or.inr ⟨x, hx, rfl⟩
  constructor
  · rintro ⟨H1, H2⟩ u hu z hz hU huz
    have hΨ := hmono hu hz huz
    refine ⟨?_, H2 u hu z hz⟩
    rw [← (hSK u (hY u hu) z (hY z hz) huz).2.1 hU,
      ← (hSK (Ψ u) (hΨY u hu) (Ψ z) (hΨY z hz) hΨ).2.1 ((hups u hu).2 hU)]
    exact H1 u hu z hz
  · intro H
    -- the pairs `x < y`
    have key1 : ∀ x ∈ Y, ∀ y ∈ Y, x < y → (le1 x y ↔ le1 (Ψ x) (Ψ y)) := by
      intro x hx y hy hxy
      have hΨ := hmono hx hy hxy
      by_cases hU : UpsPt x
      · rw [(hSK x (hY x hx) y (hY y hy) hxy).2.1 hU,
          (hSK (Ψ x) (hΨY x hx) (Ψ y) (hΨY y hy) hΨ).2.1 ((hups x hx).2 hU)]
        exact (H x hx y hy hU hxy).1
      · have hU' : ¬ UpsPt (Ψ x) := fun h => hU ((hups x hx).1 h)
        rw [(hSK x (hY x hx) y (hY y hy) hxy).1 hU,
          (hSK (Ψ x) (hΨY x hx) (Ψ y) (hΨY y hy) hΨ).1 hU']
        exact hle1R x hx y hy
    have key2 : ∀ x ∈ Y, ∀ y ∈ Y, x < y → (le2 x y ↔ le2 (Ψ x) (Ψ y)) := by
      intro x hx y hy hxy
      have hΨ := hmono hx hy hxy
      by_cases hU : UpsPt x
      · exact (H x hx y hy hU hxy).2
      · have hU' : ¬ UpsPt (Ψ x) := fun h => hU ((hups x hx).1 h)
        exact ⟨fun h => absurd ((hSK x (hY x hx) y (hY y hy) hxy).2.2 h).1 hU,
          fun h => absurd ((hSK (Ψ x) (hΨY x hx) (Ψ y) (hΨY y hy) hΨ).2.2 h).1 hU'⟩
    refine ⟨fun x hx y hy => ?_, fun x hx y hy => ?_⟩
    · rcases lt_trichotomy x y with hxy | rfl | hxy
      · exact key1 x hx y hy hxy
      · exact ⟨fun _ => le1_refl _, fun _ => le1_refl _⟩
      · have hΨ := hmono hy hx hxy
        exact ⟨fun h => absurd (le1_le h) (not_le.2 hxy),
          fun h => absurd (le1_le h) (not_le.2 hΨ)⟩
    · rcases lt_trichotomy x y with hxy | rfl | hxy
      · exact key2 x hx y hy hxy
      · exact ⟨fun _ => le2_refl _, fun _ => le2_refl _⟩
      · have hΨ := hmono hy hx hxy
        exact ⟨fun h => absurd (le2_le h) (not_le.2 hxy),
          fun h => absurd (le2_le h) (not_le.2 hΨ)⟩

end Googology.Trans.PoR.InaccPsi.R2
