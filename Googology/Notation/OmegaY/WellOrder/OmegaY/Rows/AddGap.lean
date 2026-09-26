/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Rows/AddGap.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Rows/AddGap.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Rows.Intervals

set_option backward.do.legacy false

/-!
# Exact coefficient addition and right gap

The operations match `add` and `gap` in omega-y/engine.js. `gap` is totalized
outside its intended domain; all cancellation statements require `a <= b`,
exactly the domain checked by the JavaScript implementation.
-/

namespace OmegaY.Row

private def fromSupport (s : Finset Nat) (f : Nat → Nat)
    (hf : ∀ i, f i ≠ 0 → i ∈ s) : Row where
  coeffs := {
    support := s.filter fun i => f i ≠ 0
    toFun := f
    mem_support_toFun := by
      intro i
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨hf i h, h⟩⟩ }

private def addCoeff (a b : Row) (i : Nat) : Nat :=
  if b = 0 then coeff a i
  else
    let d := jump 0 b - 1
    if i < d then coeff b i else if i = d then coeff a i + coeff b i else coeff a i

/-- Ordinal right addition of finite Cantor rows. -/
def add (a b : Row) : Row :=
  fromSupport (a.coeffs.support ∪ b.coeffs.support) (addCoeff a b) (by
    intro i hi
    simp only [Finset.mem_union, Finsupp.mem_support_iff]
    change coeff a i ≠ 0 ∨ coeff b i ≠ 0
    simp only [addCoeff] at hi
    split_ifs at hi <;> omega)

theorem coeff_add (a b : Row) (i : Nat) :
    coeff (add a b) i =
      if b = 0 then coeff a i else
        if i < jump 0 b - 1 then coeff b i
        else if i = jump 0 b - 1 then coeff a i + coeff b i else coeff a i := rfl

@[simp] theorem add_zero (a : Row) : add a 0 = a := by
  apply ext
  intro i
  simp [coeff_add]

theorem lt_add_of_ne_zero (a : Row) {b : Row} (hb : b ≠ 0) : a < add a b := by
  have hv := lexLt_iff_last.mp (lt_of_le_of_ne (zero_le b) hb.symm)
  rw [coeff_zero] at hv
  apply lt_iff.mpr
  refine ⟨jump 0 b - 1, ?_, ?_⟩
  · intro i hi
    rw [coeff_add]
    have h₁ : ¬ i < jump 0 b - 1 := by omega
    have h₂ : i ≠ jump 0 b - 1 := by omega
    simp [hb, h₁, h₂]
  · rw [coeff_add]
    simp only [hb, ↓reduceIte, Nat.lt_irrefl]
    omega

theorem le_add (a b : Row) : a ≤ add a b := by
  by_cases hb : b = 0
  · rw [hb, add_zero]
  · exact le_of_lt (lt_add_of_ne_zero a hb)

theorem coeff_add_high_of_jump_le {a b : Row} {e i : Nat}
    (hb : jump 0 b ≤ e) (hi : e ≤ i) : coeff (add a b) i = coeff a i := by
  by_cases hz : b = 0
  · simp [hz]
  · have hp : 0 < jump 0 b := Nat.pos_of_ne_zero (by
      intro he
      exact hz (jump_eq_zero.mp he).symm)
    have h₁ : ¬ i < jump 0 b - 1 := by omega
    have h₂ : i ≠ jump 0 b - 1 := by omega
    simp [coeff_add, hz, h₁, h₂]

theorem add_eq_of_jump_le {a b c : Row} (h : jump a b ≤ jump 0 c - 1) :
    add a c = add b c := by
  by_cases hc : c = 0
  · have he : a = b := jump_eq_zero.mp (by
      rw [hc, jump_self] at h
      exact Nat.eq_zero_of_le_zero h)
    rw [he]
  · apply ext
    intro i
    by_cases hi : i < jump 0 c - 1
    · simp [coeff_add, hc, hi]
    · have he := jump_le_iff.mp h i (Nat.le_of_not_gt hi)
      simp only [coeff_add, hc, ↓reduceIte, hi, he]

/-- Ordinal addition is monotone in its left argument, but not strictly so. -/
theorem add_monotone (c : Row) : Monotone (fun a : Row => add a c) := by
  intro a b hab
  by_cases hc : c = 0
  · simpa [hc] using hab
  rcases eq_or_lt_of_le hab with rfl | hab
  · exact le_refl _
  obtain ⟨i, hh, hi⟩ := lt_iff.mp hab
  by_cases hid : i < jump 0 c - 1
  · apply le_of_eq
    apply ext
    intro j
    by_cases hj : j < jump 0 c - 1
    · simp [coeff_add, hc, hj]
    · have he := hh j (by omega)
      simp only [coeff_add, hc, ↓reduceIte, hj, he]
  · apply le_of_lt
    apply lt_iff.mpr
    refine ⟨i, ?_, ?_⟩
    · intro j hij
      have h₁ : ¬ j < jump 0 c - 1 := by omega
      have h₂ : j ≠ jump 0 c - 1 := by omega
      simpa [coeff_add, hc, h₁, h₂] using hh j hij
    · simp only [coeff_add, hc, ↓reduceIte, hid]
      split_ifs <;> omega

private def gapCoeff (a b : Row) (i : Nat) : Nat :=
  if a = b then 0
  else
    let d := jump a b - 1
    if i < d then coeff b i else if i = d then coeff b i - coeff a i else 0

/-- The engine's right difference: the least row g with a + g = b when a<=b. -/
def gap (a b : Row) : Row :=
  fromSupport b.coeffs.support (gapCoeff a b) (by
    intro i hi
    simp only [Finsupp.mem_support_iff]
    change coeff b i ≠ 0
    simp only [gapCoeff] at hi
    split_ifs at hi <;> omega)

theorem coeff_gap (a b : Row) (i : Nat) :
    coeff (gap a b) i =
      if a = b then 0 else
        if i < jump a b - 1 then coeff b i
        else if i = jump a b - 1 then coeff b i - coeff a i else 0 := rfl

@[simp] theorem gap_self (a : Row) : gap a a = 0 := by
  apply ext
  intro i
  simp [coeff_gap]

theorem jump_zero_gap_of_lt {a b : Row} (hab : a < b) :
    jump 0 (gap a b) = jump a b := by
  have hne := ne_of_lt hab
  have hj : 0 < jump a b := Nat.pos_of_ne_zero (fun h => hne (jump_eq_zero.mp h))
  have hi := lexLt_iff_last.mp hab
  have he : jump 0 (gap a b) = (jump a b - 1) + 1 := by
    apply jump_eq_succ_of_last
    · rw [coeff_zero, coeff_gap]
      simp only [hne, ↓reduceIte, Nat.lt_irrefl]
      omega
    · intro i hik
      rw [coeff_zero, coeff_gap]
      simp only [hne, ↓reduceIte]
      have h₁ : ¬ i < jump a b - 1 := by omega
      have h₂ : i ≠ jump a b - 1 := by omega
      simp [h₁, h₂]
  omega

theorem gap_ne_zero_of_lt {a b : Row} (hab : a < b) : gap a b ≠ 0 := by
  intro he
  have hj := jump_zero_gap_of_lt hab
  rw [he, jump_self] at hj
  exact (ne_of_lt hab) (jump_eq_zero.mp hj.symm)

theorem jump_zero_gap {a b : Row} (hab : a ≤ b) : jump 0 (gap a b) = jump a b := by
  rcases eq_or_lt_of_le hab with rfl | h
  · simp
  · exact jump_zero_gap_of_lt h

theorem add_gap {a b : Row} (hab : a ≤ b) : add a (gap a b) = b := by
  rcases eq_or_lt_of_le hab with rfl | hab
  · simp
  have hne := ne_of_lt hab
  have hg := gap_ne_zero_of_lt hab
  have hj := jump_zero_gap_of_lt hab
  have hlast := lexLt_iff_last.mp hab
  apply ext
  intro i
  rw [coeff_add]
  simp only [hg, ↓reduceIte, hj]
  rcases Nat.lt_trichotomy i (jump a b - 1) with hi | hi | hi
  · simp [hi, coeff_gap, hne]
  · subst i
    simp only [Nat.lt_irrefl, coeff_gap, hne, ↓reduceIte]
    omega
  · have h₁ : ¬ i < jump a b - 1 := by omega
    have h₂ : i ≠ jump a b - 1 := by omega
    simp only [h₁, h₂, ↓reduceIte]
    exact jump_le_iff.mp (Nat.le_refl (jump a b)) i (by omega)

/-- One monomial omega^d, represented by the same executable bump operation. -/
def power (d : Nat) : Row := bump 0 d

theorem coeff_power (d i : Nat) : coeff (power d) i = if i = d then 1 else 0 := by
  simp only [power, coeff_bump, coeff_zero, Nat.zero_add]
  split_ifs <;> omega

theorem power_ne_zero (d : Nat) : power d ≠ 0 := ne_of_gt (lt_bump 0 d)

@[simp] theorem jump_zero_power (d : Nat) : jump 0 (power d) = d+1 := jump_bump _ _

/-- Confirms that `bump` implements ordinal right addition by one omega power. -/
theorem add_power (a : Row) (d : Nat) : add a (power d) = bump a d := by
  apply ext
  intro i
  rw [coeff_add]
  simp only [power_ne_zero d, ↓reduceIte, jump_zero_power, Nat.add_sub_cancel,
    coeff_power, coeff_bump]
  split_ifs <;> omega

example : toList (add (ofList [7, 2, 3]) (ofList [5, 1])) = [5, 3, 3] := by decide
example : toList (gap (ofList [7, 2, 3]) (ofList [5, 3, 3])) = [5, 1] := by decide

end OmegaY.Row

#print axioms OmegaY.Row.add_gap
#print axioms OmegaY.Row.add_power
