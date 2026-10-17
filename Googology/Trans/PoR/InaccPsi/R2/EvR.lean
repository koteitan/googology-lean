import Googology.Trans.PoR.InaccPsi.R2.EvA

/-!
# A lower bound in `R₁⁺` read off a reach `α ≤₁ α·2 + z`

If `α ≤₁ α·2 + z` in `R₁⁺` with `z < α`, and `b < α` is an `ε`-number, then `α ≥ ε_{b+ω^z}`.  For `z = 0` this is the
test `α ≤₁ α·2 ⇔ α ∈ E` ([W07b] §2, after Theorem 2.2); for `z > 0` the finite-set criterion (`le1R_copy`,
the direction `⇒`) copies the configuration `α < α·2 < α·2 + z'` (`z' < z`) below `α` above any `c < α`, so `α`
is a limit of ordinals `e` with `e ≤₁ e·2 + z'`, and induction on `z` gives the bound.  So `ε_{ρ+ω}` (`z = 1`) is
not copied to any `ε_{x+n}`, which the test `α ≤₁ α·2` alone does not show.  No new axiom.

* `le1R_copy_two` (**the copy of `α ≤₁ α·2 + z'` below `α`**), `le1R_two_add_E`, `le1R_ge_evAg` (**`α ≥ ε_{b+ω^z}`**),
  `le1R_ge_evA` (the case `z ≤ b`).

[W07b] G. Wilken, "Σ₁-elementarity and Skolem hull operators", APAL 145 (2007) 162–175.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order

/-- **The copy below `α`**: if `α ≤₁ α·2 + z` and `z' < z`, `z' < α`, `c < α`, there is `e ∈ (c, α)` with
`e ≤₁ e·2 + z'`. -/
theorem le1R_copy_two {a z z' c : Ordinal.{0}} (h : le1R a (a * 2 + z)) (hz : z' < z) (hz'a : z' < a)
    (hca : c < a) : ∃ e, c < e ∧ e < a ∧ le1R e (e * 2 + z') := by
  classical
  set b := a * 2 + z' + 1 with hb
  have hab : a ≤ a * 2 := by rw [mul_two_eq]; exact le_self_add
  have hbz : b ≤ a * 2 + z := by
    rw [hb, add_assoc]; exact add_le_add_right (add_one_le_of_lt hz) _
  have hab' : a ≤ b := hab.trans (le_self_add.trans le_self_add)
  have hle : le1R a b := le1R_of_le hab' hbz h
  have hle' : le1R a (a * 2 + z') := le1R_of_le (hab.trans le_self_add) le_self_add hle
  set X : Finset Ordinal.{0} := {c, z'} with hX
  set Y : Finset Ordinal.{0} := {a, a * 2, a * 2 + z'} with hY
  have hXa : ∀ x ∈ X, x < a := by
    intro x hx; simp only [hX, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hca
    · exact hz'a
  have hYb : ∀ y ∈ Y, a ≤ y ∧ y < b := by
    intro y hy; simp only [hY, Finset.mem_insert, Finset.mem_singleton] at hy
    have h1 : a * 2 + z' < b := lt_add_one _
    rcases hy with rfl | rfl | rfl
    · exact ⟨le_rfl, lt_of_le_of_lt (hab.trans le_self_add) h1⟩
    · exact ⟨hab, lt_of_le_of_lt le_self_add h1⟩
    · exact ⟨hab.trans le_self_add, h1⟩
  obtain ⟨Yt, hYt, φ, hbij, hfix, hmono, hadd, h1R⟩ := le1R_copy hle X Y hXa hYb
  have mX : ∀ x ∈ X, x ∈ X ∪ Y := fun x hx => Finset.mem_union_left _ hx
  have mY : ∀ y ∈ Y, y ∈ X ∪ Y := fun y hy => Finset.mem_union_right _ hy
  have hcX : c ∈ X := by simp [hX]
  have hz'X : z' ∈ X := by simp [hX]
  have haY : a ∈ Y := by simp [hY]
  have ha2Y : a * 2 ∈ Y := by simp [hY]
  have ha2zY : a * 2 + z' ∈ Y := by simp [hY]
  have himg : φ a ∈ X ∪ Yt := hbij.mapsTo (Finset.mem_coe.2 (mY a haY))
  have hea : φ a < a := by
    rcases Finset.mem_union.1 himg with hx | hy
    · exact hXa _ hx
    · exact hYt _ hy
  have hce : c < φ a := by
    have := hmono (Finset.mem_coe.2 (mX c hcX)) (Finset.mem_coe.2 (mY a haY)) hca
    rwa [hfix c hcX] at this
  have e1 : φ a + φ a = φ (a * 2) :=
    (hadd a (mY a haY) a (mY a haY) (a * 2) (mY _ ha2Y)).1 (mul_two_eq a).symm
  have e2 : φ (a * 2) + φ z' = φ (a * 2 + z') :=
    (hadd (a * 2) (mY _ ha2Y) z' (mX z' hz'X) (a * 2 + z') (mY _ ha2zY)).1 rfl
  have h3 := (h1R a (mY a haY) (a * 2 + z') (mY _ ha2zY)).1 hle'
  rw [← e2, ← e1, hfix z' hz'X, ← mul_two_eq] at h3
  exact ⟨φ a, hce, hea, h3⟩

/-- `α ≤₁ α·2 + z` gives `α ∈ E` (`α > 0`). -/
theorem le1R_two_add_E {a z : Ordinal.{0}} (ha : 0 < a) (h : le1R a (a * 2 + z)) : InE a := by
  have hab : a ≤ a * 2 := by rw [mul_two_eq]; exact le_self_add
  exact (le1R_two_iff ha).1 (le1R_of_le hab le_self_add h)

/-- A point below `ω^{z'+1} = ω^{z'}·ω` is below some `ω^{z'}·n`. -/
theorem ev_lt_opow_succ_nat {z' d : Ordinal.{0}} (hd : d < ω ^ (z' + 1)) : ∃ n : ℕ, d < ω ^ z' * n := by
  rw [opow_add_one] at hd
  have hN := isNormal_mul_right (opow_pos z' omega0_pos)
  rw [hN.apply_of_isSuccLimit isSuccLimit_omega0] at hd
  obtain ⟨k, hk⟩ := Ordinal.lt_iSup_iff.1 hd
  obtain ⟨n, hn⟩ := lt_omega0.1 k.2
  exact ⟨n, by rw [← hn]; exact hk⟩

/-- **The lower bound**: if `α ≤₁ α·2 + z` in `R₁⁺`, `z < α`, and `b < α` is an `ε`-number, then
`ε_{b+ω^z} ≤ α`. -/
theorem le1R_ge_evAg : ∀ z a b : Ordinal.{0}, InE b → b < a → z < a → le1R a (a * 2 + z) →
    evA b (ω ^ z) ≤ a := by
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro a b hb hba hza h
  have ha0 : 0 < a := lt_of_le_of_lt zero_le hba
  have haE := le1R_two_add_E ha0 h
  rcases eq_or_ne z 0 with rfl | hz0
  · rw [opow_zero, ← zero_add (1 : Ordinal.{0}), evA_add_one, evA_zero hb]
    exact eN_le hba haE
  -- every `ε_{b+d}` with `d < ω^{z'+1}`, `z' < z`, is below `α`
  have hstep : ∀ z' < z, ∀ n : ℕ, evA b (ω ^ z' * n) < a := by
    intro z' hz' n
    induction n with
    | zero => rw [Nat.cast_zero, mul_zero, evA_zero hb]; exact hba
    | succ n ihn =>
      set c := evA b (ω ^ z' * n) with hc
      have hz'a : z' < a := hz'.trans hza
      obtain ⟨e, hce, hea, he⟩ := le1R_copy_two h hz' hz'a (max_lt ihn hz'a)
      have hce' : c < e := lt_of_le_of_lt (le_max_left _ _) hce
      have hz'e : z' < e := lt_of_le_of_lt (le_max_right _ _) hce
      have := IH z' hz' e c (evA_E _ _) hce' hz'e he
      rw [hc, evA_add, ← mul_add_one, ← Nat.cast_succ] at this
      exact lt_of_le_of_lt this hea
  refine evA_le_of_lt haE (opow_pos z omega0_pos).ne' (fun d hd => ?_)
  rcases eq_or_ne d 0 with rfl | hd0
  · rw [evA_zero hb]; exact hba
  set z' := log ω d with hz'
  have hz'z : z' < z := by
    have h1 : ω ^ z' ≤ d := opow_log_le_self ω hd0
    exact (opow_lt_opow_iff_right one_lt_omega0).1 (lt_of_le_of_lt h1 hd)
  have hd' : d < ω ^ (z' + 1) := by
    rw [← succ_eq_add_one]; exact lt_opow_succ_log_self one_lt_omega0 d
  obtain ⟨n, hn⟩ := ev_lt_opow_succ_nat hd'
  exact (evA_lt_iff.2 hn).trans (hstep z' hz'z n)

/-- The bound with `z ≤ b`. -/
theorem le1R_ge_evA (z a b : Ordinal.{0}) (hb : InE b) (hba : b < a) (hzb : z ≤ b)
    (h : le1R a (a * 2 + z)) : evA b (ω ^ z) ≤ a :=
  le1R_ge_evAg z a b hb hba (lt_of_le_of_lt hzb hba) h

end Googology.Trans.PoR.InaccPsi.R2
