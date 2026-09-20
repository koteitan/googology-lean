import Googology.Notation.ExBuchholz.Basic

/-!
# The order on extended Buchholz terms is a strict linear order

Irreflexivity, transitivity and trichotomy.  Together these are what
`OrdHom.injective` in `Googology.Core.Morphism` consumes, so a translation
into this notation system is injective as soon as it is order-preserving.

Well-foundedness is *not* proved here; see the directory README.
-/

namespace Googology.Notation.ExBuchholz.Term

/-- Splitting a `cons`/`cons` comparison at `.lt`. -/
theorem cmp_cons_lt_iff {a b t c d u : Term} :
    cmp (cons a b t) (cons c d u) = .lt ↔
      cmp a c = .lt ∨
        (cmp a c = .eq ∧ (cmp b d = .lt ∨ (cmp b d = .eq ∧ cmp t u = .lt))) := by
  simp only [cmp]
  generalize cmp a c = x
  generalize cmp b d = y
  generalize cmp t u = z
  cases x <;> cases y <;> cases z <;> simp

private theorem lt_of_lt_of_cmp_eq {p q r : Term}
    (h₁ : cmp p q = .lt) (h₂ : cmp q r = .eq) : cmp p r = .lt := by
  rw [cmp_eq_iff] at h₂; subst h₂; exact h₁

private theorem lt_of_cmp_eq_of_lt {p q r : Term}
    (h₁ : cmp p q = .eq) (h₂ : cmp q r = .lt) : cmp p r = .lt := by
  rw [cmp_eq_iff] at h₁; subst h₁; exact h₂

private theorem cmp_eq_trans {p q r : Term}
    (h₁ : cmp p q = .eq) (h₂ : cmp q r = .eq) : cmp p r = .eq := by
  rw [cmp_eq_iff] at h₁ h₂; subst h₁; subst h₂; exact cmp_self _

private theorem cmp_lt_trans_aux (x : Term) :
    ∀ y z : Term, cmp x y = .lt → cmp y z = .lt → cmp x z = .lt := by
  induction x with
  | nil =>
    intro y z hxy hyz
    cases y with
    | nil => cases hxy
    | cons _ _ _ =>
      cases z with
      | nil => cases hyz
      | cons _ _ _ => rfl
  | cons a b t ha hb ht =>
    intro y z hxy hyz
    cases y with
    | nil => cases hxy
    | cons c d u =>
      cases z with
      | nil => cases hyz
      | cons e f v =>
        rw [cmp_cons_lt_iff] at hxy hyz ⊢
        rcases hxy with h1 | ⟨h1, hxy'⟩ <;> rcases hyz with h2 | ⟨h2, hyz'⟩
        · exact Or.inl (ha _ _ h1 h2)
        · exact Or.inl (lt_of_lt_of_cmp_eq h1 h2)
        · exact Or.inl (lt_of_cmp_eq_of_lt h1 h2)
        · refine Or.inr ⟨cmp_eq_trans h1 h2, ?_⟩
          rcases hxy' with k1 | ⟨k1, hxy''⟩ <;> rcases hyz' with k2 | ⟨k2, hyz''⟩
          · exact Or.inl (hb _ _ k1 k2)
          · exact Or.inl (lt_of_lt_of_cmp_eq k1 k2)
          · exact Or.inl (lt_of_cmp_eq_of_lt k1 k2)
          · exact Or.inr ⟨cmp_eq_trans k1 k2, ht _ _ hxy'' hyz''⟩

/-- The order is irreflexive. -/
theorem lt_irrefl (x : Term) : ¬ x < x := by
  show ¬ cmp x x = .lt
  rw [cmp_self]
  intro h; cases h

/-- The order is transitive. -/
theorem lt_trans {x y z : Term} (h₁ : x < y) (h₂ : y < z) : x < z :=
  cmp_lt_trans_aux x y z h₁ h₂

/-- The order is trichotomous. -/
theorem lt_trichotomy (x y : Term) : x < y ∨ x = y ∨ y < x := by
  cases h : cmp x y with
  | lt => exact Or.inl h
  | eq => exact Or.inr (Or.inl (cmp_eq_iff.mp h))
  | gt =>
    refine Or.inr (Or.inr ?_)
    have hs := cmp_swap x y
    rw [h] at hs
    exact hs.symm

/-- Asymmetry, from irreflexivity and transitivity. -/
theorem lt_asymm {x y : Term} (h : x < y) : ¬ y < x :=
  fun h' => lt_irrefl x (lt_trans h h')

/-! ### Sanity checks

`0`, `1 = ψ_0(0)`, `2 = 1 + 1`, `ω = ψ_0(1)` and `Ω = ψ_1(0)`. -/

/-- The term `0`. -/
abbrev t0 : Term := nil
/-- The term `1 = ψ_0(0)`. -/
abbrev t1 : Term := psi nil nil
/-- The term `2 = 1 + 1`. -/
abbrev t2 : Term := cons nil nil t1
/-- The term `ω = ψ_0(1)`. -/
abbrev tw : Term := psi nil t1
/-- The term `Ω = ψ_1(0)`. -/
abbrev tW : Term := psi t1 nil

#guard cmp t0 t1 = .lt
#guard cmp t1 t2 = .lt
#guard cmp t2 tw = .lt
#guard cmp tw tW = .lt
#guard cmp tW tw = .gt
#guard cmp t1 t1 = .eq
#guard cmp (psi nil tw) (psi nil tW) = .lt

end Googology.Notation.ExBuchholz.Term
