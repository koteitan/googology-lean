import Googology.Trans.PoR.InaccPsi.R2.EvR

/-!
# The `R₁⁺`-tests of every finite level: `α ≤₁ α·(n+1) + z`

For `1 ≤ n < ω` (`φ_n = veblen n`, `P_n` its range):

* `vz_le1R_copy` (**the copy of `α ≤₁ α·(n+1) + z'` below `α`**: if `α ≤₁ α·(n+1) + z`, `z' < z`, `z' < α`, `c < α`,
  there is `e ∈ (c, α)` with `e ≤₁ e·(n+1) + z'`; the finite-set criterion `le1R_copy` applied to
  `{c, z'}` and `{α, α·2, …, α·(n+1), α·(n+1) + z'}`);
* `vz_le1R_level` (**`α ≤₁ α·(n+1)` gives `α ∈ P_n`**; `n = 1`: [W07b] §2 after Theorem 2.2, `le1R_two_iff`);
* `vz_le1R_ge` (**`α ≤₁ α·(n+1) + z`, `z < α`, `φ_n(i) < α` give `φ_n(i + ω^z) ≤ α`**; for `n = 1` this is
  `le1R_ge_evAg` of `R2.EvR`).

The two are proved together by induction on `n`: the bound at level `n` by induction on `z` (the copy below `α`), and
`α ≤₁ α·(n+2)` gives `α ≤₁ α·(n+1) + z'` for every `z' < α`, so `φ_n(j) ≤ α` for every `j < α`, `φ_n(α) = α`.
Only the `R₁⁺` axioms of `R2.Cited` and `R2.CitedR1` are used; no new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order

/-- `α ≤ α·m` for `m ≥ 1`. -/
theorem vz_le_mul {a : Ordinal.{0}} {m : ℕ} (hm : 1 ≤ m) : a ≤ a * (m : Ordinal.{0}) := by
  have h1 : (1 : Ordinal.{0}) ≤ (m : Ordinal.{0}) := by exact_mod_cast hm
  calc a = a * 1 := (mul_one a).symm
    _ ≤ a * (m : Ordinal.{0}) := mul_le_mul_right h1 a

theorem vz_mul_succ (a : Ordinal.{0}) (k : ℕ) : a * ((k + 1 : ℕ) : Ordinal.{0}) = a * (k : Ordinal.{0}) + a := by
  rw [Nat.cast_succ, mul_add_one]

/-- **The copy below `α`**: if `α ≤₁ α·(n+1) + z` and `z' < z`, `z' < α`, `c < α`, there is `e ∈ (c, α)` with
`e ≤₁ e·(n+1) + z'`. -/
theorem vz_le1R_copy {a z z' c : Ordinal.{0}} (n : ℕ) (h : le1R a (a * ((n + 1 : ℕ) : Ordinal.{0}) + z))
    (hz : z' < z) (hz'a : z' < a) (hca : c < a) :
    ∃ e, c < e ∧ e < a ∧ le1R e (e * ((n + 1 : ℕ) : Ordinal.{0}) + z') := by
  classical
  set N : ℕ := n + 1 with hN
  set b := a * (N : Ordinal.{0}) + z' + 1 with hb
  have haN : a ≤ a * (N : Ordinal.{0}) := vz_le_mul (by omega)
  have hbz : b ≤ a * (N : Ordinal.{0}) + z := by
    rw [hb, add_assoc]; exact add_le_add_right (add_one_le_of_lt hz) _
  have hab : a ≤ b := haN.trans (le_self_add.trans le_self_add)
  have hle : le1R a b := le1R_of_le hab hbz h
  have hle' : le1R a (a * (N : Ordinal.{0}) + z') := le1R_of_le (haN.trans le_self_add) le_self_add hle
  set X : Finset Ordinal.{0} := {c, z'} with hX
  set Y : Finset Ordinal.{0} :=
    insert (a * (N : Ordinal.{0}) + z') ((Finset.range N).image (fun k => a * ((k + 1 : ℕ) : Ordinal.{0})))
    with hY
  have hXa : ∀ x ∈ X, x < a := by
    intro x hx; simp only [hX, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hca
    · exact hz'a
  have hmulN : ∀ k : ℕ, k < N → a * ((k + 1 : ℕ) : Ordinal.{0}) ≤ a * (N : Ordinal.{0}) := fun k hk =>
    mul_le_mul_right (by exact_mod_cast hk) a
  have hYb : ∀ y ∈ Y, a ≤ y ∧ y < b := by
    intro y hy
    have h1 : a * (N : Ordinal.{0}) + z' < b := lt_add_one _
    simp only [hY, Finset.mem_insert, Finset.mem_image, Finset.mem_range] at hy
    rcases hy with rfl | ⟨k, hk, rfl⟩
    · exact ⟨haN.trans le_self_add, h1⟩
    · exact ⟨vz_le_mul (by omega), lt_of_le_of_lt ((hmulN k hk).trans le_self_add) h1⟩
  obtain ⟨Yt, hYt, φ, hbij, hfix, hmono, hadd, h1R⟩ := le1R_copy hle X Y hXa hYb
  have mX : ∀ x ∈ X, x ∈ X ∪ Y := fun x hx => Finset.mem_union_left _ hx
  have mY : ∀ y ∈ Y, y ∈ X ∪ Y := fun y hy => Finset.mem_union_right _ hy
  have hcX : c ∈ X := by simp [hX]
  have hz'X : z' ∈ X := by simp [hX]
  have hkY : ∀ k : ℕ, k < N → a * ((k + 1 : ℕ) : Ordinal.{0}) ∈ Y := fun k hk => by
    simp only [hY, Finset.mem_insert, Finset.mem_image, Finset.mem_range]
    exact Or.inr ⟨k, hk, rfl⟩
  have haY : a ∈ Y := by
    have := hkY 0 (by omega); rwa [zero_add, Nat.cast_one, mul_one] at this
  have hNzY : a * (N : Ordinal.{0}) + z' ∈ Y := by simp [hY]
  have hNY : a * (N : Ordinal.{0}) ∈ X ∪ Y := mY _ (hkY n (by omega))
  -- `φ(α·(k+1)) = φ(α)·(k+1)`
  have hmul : ∀ k : ℕ, k < N → φ (a * ((k + 1 : ℕ) : Ordinal.{0})) = φ a * ((k + 1 : ℕ) : Ordinal.{0}) := by
    intro k
    induction k with
    | zero => intro _; simp only [zero_add, Nat.cast_one, mul_one]
    | succ k ih =>
      intro hk
      have e1 := (hadd _ (mY _ (hkY k (by omega))) a (mY a haY) _ (mY _ (hkY (k + 1) hk))).1
        (by rw [vz_mul_succ a (k + 1)])
      rw [← e1, ih (by omega), ← vz_mul_succ]
  have himg : φ a ∈ X ∪ Yt := hbij.mapsTo (Finset.mem_coe.2 (mY a haY))
  have hea : φ a < a := by
    rcases Finset.mem_union.1 himg with hx | hy
    · exact hXa _ hx
    · exact hYt _ hy
  have hce : c < φ a := by
    have := hmono (Finset.mem_coe.2 (mX c hcX)) (Finset.mem_coe.2 (mY a haY)) hca
    rwa [hfix c hcX] at this
  have e2 : φ (a * (N : Ordinal.{0})) + φ z' = φ (a * (N : Ordinal.{0}) + z') :=
    (hadd _ hNY z' (mX z' hz'X) _ (mY _ hNzY)).1 rfl
  have h3 := (h1R a (mY a haY) _ (mY _ hNzY)).1 hle'
  rw [← e2, hfix z' hz'X, hmul n (by omega)] at h3
  exact ⟨φ a, hce, hea, h3⟩

/-- `α ≤₁ α·(n+1) + z` gives `α ≤₁ α·(n+1)`. -/
theorem vz_le1R_base {a z : Ordinal.{0}} {n : ℕ} (h : le1R a (a * ((n + 1 : ℕ) : Ordinal.{0}) + z)) :
    le1R a (a * ((n + 1 : ℕ) : Ordinal.{0})) :=
  le1R_of_le (vz_le_mul (by omega)) le_self_add h

/-- A value of `φ_o` above every `φ_o(d)`, `d < D`, is at least `φ_o(D)`. -/
theorem vz_veblen_le_of_lt {o v D : Ordinal.{0}} (hv : v ∈ Set.range (veblen o))
    (h : ∀ d < D, veblen o d < v) : veblen o D ≤ v := by
  obtain ⟨j, rfl⟩ := hv
  by_contra hlt
  push Not at hlt
  have hjD : j < D := (veblen_lt_veblen_iff_right).1 hlt
  exact lt_irrefl _ (h j hjD)

/-- **The bound at level `n`** from the level test at `n`. -/
theorem vz_le1R_ge_of {n : ℕ}
    (hA : ∀ a : Ordinal.{0}, 0 < a → le1R a (a * ((n + 1 : ℕ) : Ordinal.{0})) → a ∈ Set.range (veblen (n : Ordinal.{0}))) :
    ∀ z a i : Ordinal.{0}, z < a → veblen (n : Ordinal.{0}) i < a →
      le1R a (a * ((n + 1 : ℕ) : Ordinal.{0}) + z) → veblen (n : Ordinal.{0}) (i + ω ^ z) ≤ a := by
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro a i hza hia h
  have ha0 : 0 < a := lt_of_le_of_lt zero_le hia
  have haP := hA a ha0 (vz_le1R_base h)
  rcases eq_or_ne z 0 with rfl | hz0
  · rw [opow_zero]
    obtain ⟨j, rfl⟩ := haP
    have hij : i < j := (veblen_lt_veblen_iff_right).1 hia
    exact (veblen_le_veblen_iff_right).2 (add_one_le_of_lt hij)
  have hstep : ∀ z' < z, ∀ k : ℕ, veblen (n : Ordinal.{0}) (i + ω ^ z' * k) < a := by
    intro z' hz' k
    induction k with
    | zero => rw [Nat.cast_zero, mul_zero, add_zero]; exact hia
    | succ k ihk =>
      set c := veblen (n : Ordinal.{0}) (i + ω ^ z' * k) with hc
      have hz'a : z' < a := hz'.trans hza
      obtain ⟨e, hce, hea, he⟩ := vz_le1R_copy n h hz' hz'a (max_lt ihk hz'a)
      have hce' : c < e := lt_of_le_of_lt (le_max_left _ _) hce
      have hz'e : z' < e := lt_of_le_of_lt (le_max_right _ _) hce
      have := IH z' hz' e (i + ω ^ z' * k) hz'e hce' he
      rw [add_assoc, ← mul_add_one, ← Nat.cast_succ] at this
      exact lt_of_le_of_lt this hea
  refine vz_veblen_le_of_lt haP (fun d hd => ?_)
  rcases le_or_gt d i with hdi | hid
  · exact lt_of_le_of_lt ((veblen_le_veblen_iff_right).2 hdi) hia
  set d' := d - i with hd'
  have hdd : i + d' = d := Ordinal.add_sub_cancel_of_le hid.le
  have hd'z : d' < ω ^ z := by
    rw [← hdd] at hd; exact (add_lt_add_iff_left i).1 hd
  have hd'0 : d' ≠ 0 := by
    intro h0; rw [h0, add_zero] at hdd; exact lt_irrefl _ (hdd ▸ hid)
  set z' := log ω d' with hz'
  have hz'z : z' < z := by
    have h1 : ω ^ z' ≤ d' := opow_log_le_self ω hd'0
    exact (opow_lt_opow_iff_right one_lt_omega0).1 (lt_of_le_of_lt h1 hd'z)
  have hd'' : d' < ω ^ (z' + 1) := by
    rw [← succ_eq_add_one]; exact lt_opow_succ_log_self one_lt_omega0 d'
  obtain ⟨k, hk⟩ := ev_lt_opow_succ_nat hd''
  rw [← hdd]
  exact ((veblen_lt_veblen_iff_right).2 ((add_lt_add_iff_left i).2 hk)).trans (hstep z' hz'z k)

/-- The level test at `n + 1` from the tests at `n`. -/
theorem vz_le1R_level_succ {n : ℕ} (hn : 1 ≤ n)
    (hA : ∀ a : Ordinal.{0}, 0 < a → le1R a (a * ((n + 1 : ℕ) : Ordinal.{0})) → a ∈ Set.range (veblen (n : Ordinal.{0}))) :
    ∀ a : Ordinal.{0}, 0 < a → le1R a (a * ((n + 1 + 1 : ℕ) : Ordinal.{0})) →
      a ∈ Set.range (veblen ((n + 1 : ℕ) : Ordinal.{0})) := by
  intro a ha0 h
  have hB := vz_le1R_ge_of hA
  rw [vz_mul_succ] at h
  have haP := hA a ha0 (vz_le1R_base h)
  obtain ⟨e, he0, hea, he⟩ := vz_le1R_copy n h ha0 ha0 ha0
  rw [add_zero] at he
  obtain ⟨i1, hi1⟩ := hA e he0 he
  have hle : ∀ j, j < a → veblen (n : Ordinal.{0}) j ≤ a := by
    intro j hj
    have h' : le1R a (a * ((n + 1 : ℕ) : Ordinal.{0}) + j) := le1R_of_le
      ((vz_le_mul (by omega)).trans le_self_add) (add_le_add_right hj.le _) h
    have := hB j a i1 hj (by rw [hi1]; exact hea) h'
    exact ((veblen_le_veblen_iff_right).2 ((right_le_opow j one_lt_omega0).trans le_add_self)).trans this
  have hfix : veblen (n : Ordinal.{0}) a = a := by
    obtain ⟨j0, hj0⟩ := haP
    have hE : InE a := by
      have hn0 : (n : Ordinal.{0}) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
      rw [← hj0]
      have := veblen_veblen_of_lt (o₁ := 0) (o₂ := (n : Ordinal.{0})) (pos_iff_ne_zero.2 hn0) j0
      rw [veblen_zero_apply] at this
      exact this
    refine le_antisymm ?_ (right_le_veblen _ a)
    rw [(isNormal_veblen _).apply_of_isSuccLimit (ev_isSuccLimit_of_inE hE)]
    exact Ordinal.iSup_le (fun j => hle j.1 j.2)
  rw [Nat.cast_succ, veblen_add_one]
  exact (mem_range_deriv (isNormal_veblen _)).2 hfix

/-- **The level test**: `α ≤₁ α·(n+1)` in `R₁⁺` (`α > 0`, `1 ≤ n`) gives `α ∈ P_n = range φ_n`. -/
theorem vz_le1R_level : ∀ n : ℕ, 1 ≤ n → ∀ a : Ordinal.{0}, 0 < a →
    le1R a (a * ((n + 1 : ℕ) : Ordinal.{0})) → a ∈ Set.range (veblen (n : Ordinal.{0})) := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn'
    · intro a ha0 h
      have h2 : le1R a (a * 2) := by
        have e : ((0 + 1 + 1 : ℕ) : Ordinal.{0}) = 2 := by norm_num
        rwa [e] at h
      have hE := (le1R_two_iff ha0).1 h2
      have := inE_iff_mem_range_epsilon.1 hE
      simpa using this
    · exact vz_le1R_level_succ hn' (ih hn')

/-- **The bound at level `n`**: `α ≤₁ α·(n+1) + z` in `R₁⁺`, `z < α`, `φ_n(i) < α` give `φ_n(i + ω^z) ≤ α`. -/
theorem vz_le1R_ge {n : ℕ} (hn : 1 ≤ n) :
    ∀ z a i : Ordinal.{0}, z < a → veblen (n : Ordinal.{0}) i < a →
      le1R a (a * ((n + 1 : ℕ) : Ordinal.{0}) + z) → veblen (n : Ordinal.{0}) (i + ω ^ z) ≤ a :=
  vz_le1R_ge_of (vz_le1R_level n hn)

end Googology.Trans.PoR.InaccPsi.R2
