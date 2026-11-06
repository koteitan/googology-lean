import Googology.Trans.PoR.InaccPsi.R2.KuPhi

/-!
# Ku: THE CLOSURE CONDITION OF `Ks.ksLow` FROM ITS `ψ₂`-ATOMS

`Bt.HCl S M Z` is `Cl(M, Z)` without the countable collapses.  A member `ξ < P < Ω₂` of `HCl(M, Z)` is built from
ordinals below `Z`, `Ω₁` and the atoms `ψ₂(e)`, `e < M`, by `+` and `φ`; the collapses at the other levels lie at or
above `Ω₂`.  So `ξ` lies below a member of a directed family `𝒴` of strongly critical ordinals above `Ω₁` once every
atom `ψ₂(e) < P` does.

* `kuPsi_ge` (`Ω₂ ≤ ψ_π(e)` for every regular `π ∉ {Ω₁, Ω₂}`), `kuDom` (**THE REDUCTION TO THE ATOMS**).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ku

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Bt

variable {S : InaccSeq.{0}}

/-- `Ω₂ ≤ ψ_π(e)` for every regular `π` other than `Ω₁` and `Ω₂`. -/
theorem kuPsi_ge {π e : Ordinal.{0}} (hπ : S.InR π) (h1 : π ≠ Om 1) (h2 : π ≠ Om (1 + 1)) :
    Om (1 + 1) ≤ S.psi e π := by
  rcases hπ with ⟨n, rfl⟩ | ⟨s, rfl⟩
  · -- `ψ_{I_n}(e)` is a fixed point of `Ω` above `Ω₁`
    have hfix := Om_psiI (S := S) e n
    have h1lt := Om_one_lt_psiI (S := S) e n
    by_contra hc
    push Not at hc
    have h2le : (1 + 1 : Ordinal.{0}) ≤ S.psi e (S.I n) := by
      by_contra hc2
      push Not at hc2
      have : S.psi e (S.I n) ≤ 1 := Order.lt_add_one_iff.1 hc2
      have : Om (S.psi e (S.I n)) ≤ Om 1 := Om_le_Om.2 this
      rw [hfix] at this
      exact absurd h1lt (not_lt.2 this)
    have : Om (1 + 1) ≤ Om (S.psi e (S.I n)) := Om_le_Om.2 h2le
    rw [hfix] at this
    exact absurd hc (not_lt.2 this)
  · have hs0 : s ≠ 0 := by rintro rfl; exact h1 (by rw [zero_add])
    have hs1 : s ≠ 1 := by rintro rfl; exact h2 rfl
    have hs2 : (1 + 1 : Ordinal.{0}) ≤ s := by
      rw [one_add_one_eq_two]
      by_contra hc
      push Not at hc
      have : s < 2 := hc
      have : s ≤ 1 := Order.lt_add_one_iff.1 (by rwa [one_add_one_eq_two])
      rcases (Order.le_one_iff).1 this with h | h
      · exact hs0 h
      · exact hs1 h
    exact (Om_le_Om.2 hs2).trans (psiS_bounds (S := S) e s).1.le

/-- `Ω₂ ≤ I_n`. -/
theorem kuI_ge (n : ℕ) : Om (1 + 1) ≤ S.I n := by
  have hl := I_isSuccLimit (S := S) n
  have h1 : (0 : Ordinal.{0}) + 1 < S.I n := hl.add_one_lt hl.bot_lt
  rw [zero_add] at h1
  have h2 : (1 : Ordinal.{0}) + 1 ≤ S.I n := (hl.add_one_lt h1).le
  have := Om_le_Om.2 h2
  rwa [Om_I] at this

/-- **THE REDUCTION TO THE ATOMS**: every member `ξ < P` of `HCl(M, Z)` lies below a member of `𝒴` once every atom
`ψ₂(e) < P`, `e ∈ HCl(M, Z)`, `e < M`, does (`𝒴` nonempty, directed, of strongly critical members above `Ω₁`,
`Z < Ω₁`, `P ≤ Ω₂`). -/
theorem kuDom {M Z P : Ordinal.{0}} {𝒴 : Set Ordinal.{0}} (hZ1 : Z < Om 1) (hP2 : P ≤ Om (1 + 1))
    (hne : ∃ y, y ∈ 𝒴) (hSC : ∀ y ∈ 𝒴, SC y ∧ Om 1 < y)
    (hdir : ∀ y₁ ∈ 𝒴, ∀ y₂ ∈ 𝒴, ∃ y ∈ 𝒴, y₁ ≤ y ∧ y₂ ≤ y)
    (hsub : ∀ e, HCl S M Z e → e < M → S.psi e (Om (1 + 1)) < P →
      ∃ y ∈ 𝒴, S.psi e (Om (1 + 1)) < y) :
    ∀ ξ, HCl S M Z ξ → ξ < P → ∃ y ∈ 𝒴, ξ < y := by
  obtain ⟨y₀, hy₀⟩ := hne
  have hlow : ∀ x, x ≤ Om 1 → ∃ y ∈ 𝒴, x < y := fun x hx => ⟨y₀, hy₀, hx.trans_lt (hSC y₀ hy₀).2⟩
  have hjoin : ∀ x x', (∃ y ∈ 𝒴, x < y) → (∃ y ∈ 𝒴, x' < y) →
      ∃ y ∈ 𝒴, x < y ∧ x' < y := by
    rintro x x' ⟨y₁, h1, hx⟩ ⟨y₂, h2, hx'⟩
    obtain ⟨y, hy, hy1, hy2⟩ := hdir y₁ h1 y₂ h2
    exact ⟨y, hy, hx.trans_le hy1, hx'.trans_le hy2⟩
  intro ξ hξ
  induction hξ with
  | @small x hx => exact fun _ => hlow x (hx.trans hZ1).le
  | zero => exact fun _ => hlow 0 zero_le
  | inacc n =>
    intro h
    exfalso
    exact absurd (h.trans_le hP2) (not_lt.2 (kuI_ge n))
  | inaccW =>
    intro h
    exfalso
    exact absurd (h.trans_le hP2) (not_lt.2 ((kuI_ge 0).trans (S.I_lt_Iw 0).le))
  | @add x y _ _ ihx ihy =>
    intro h
    obtain ⟨y', hy', h1, h2⟩ := hjoin x y (ihx (le_self_add.trans_lt h)) (ihy (le_add_self.trans_lt h))
    exact ⟨y', hy', (hSC y' hy').1.isPrincipal h1 h2⟩
  | @phi x y _ _ ihx ihy =>
    intro h
    obtain ⟨y', hy', h1, h2⟩ := hjoin x y (ihx ((left_le_veblen x y).trans_lt h))
      (ihy ((right_le_veblen x y).trans_lt h))
    exact ⟨y', hy', (hSC y' hy').1.2 x h1 y h2⟩
  | @om x _ _ =>
    intro h
    rcases le_or_gt x 1 with hx | hx
    · exact hlow _ (Om_le_Om.2 hx)
    · exfalso
      have : Om (1 + 1) ≤ Om x := Om_le_Om.2 (Order.add_one_le_of_lt hx)
      exact absurd (h.trans_le hP2) (not_lt.2 this)
  | @coll π e hπ hπ1 _ _ he _ _ =>
    intro h
    by_cases hπ2 : π = Om (1 + 1)
    · subst hπ2
      exact hsub e ‹_› he h
    · exfalso
      exact absurd (h.trans_le hP2) (not_lt.2 (kuPsi_ge hπ hπ1 hπ2))

end Googology.Trans.PoR.InaccPsi.R2.Ku

#print axioms Googology.Trans.PoR.InaccPsi.R2.Ku.kuDom
