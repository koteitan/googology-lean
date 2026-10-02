import Googology.Trans.PoR.InaccPsi.ConjT

/-!
# LowerT: the InaccPsi side of Theorem T-LOW (README §3)

* `A_omega_mul_succ`, `A_omega_mul_omega` : `A_η` is continuous at `ω·(k+1)` and at `ω·ω`
* `lower_bound`, `lower_bound_ww` : the induction of Theorem T-LOW for `η ≤ ω²`, with Theorem LOW-0
  (`h1`) and Theorem LOW-STEP (`hstep`) as hypotheses on an abstract function `u` (Wilken's `υ`)
* `conjT`, `conjT_ww` : with the hypotheses of `ConjT.upper_bound` as well, `u (1 + η) = ψ_{Ω_1}(A_η)`
  for `η ≤ ω²` (Conjecture T, given LOW-0, LOW-STEP, STEP-0, STEP and the limit rules)

Wilken's `υ`, his systems and the map `E` are not formalized: LOW-0 and LOW-STEP are hypotheses.
LOW-STEP is assumed only for `A = A_η`: the paper proves it there, and the induction uses it only there.
-/

namespace Googology.Notation.InaccPsi.ConjT

open Ordinal Order Set Googology.Notation.InaccPsi Term InaccSeq

universe u

variable (S : InaccSeq.{u})

theorem A_omega_mul_succ (k : ℕ) :
    Aη S (ω * ((k + 1 : ℕ) : Ordinal.{u})) = ⨆ n : ℕ, Aη S (ω * k + n) := by
  simp only [Aη]
  rw [← Ordinal.add_iSup, ← Ordinal.mul_iSup, Ordinal.iSup_add_natCast]
  push_cast
  rw [mul_add_one]

theorem A_omega_mul_omega :
    Aη S (ω * ω) = ⨆ m : ℕ, Aη S (ω * (m : Ordinal.{u})) := by
  simp only [Aη]
  rw [← Ordinal.add_iSup, ← Ordinal.mul_iSup, ← Ordinal.mul_iSup, Ordinal.iSup_natCast]

theorem A_nat_mono (k : ℕ) : Monotone fun n : ℕ => Aη S (ω * (k : Ordinal.{u}) + n) :=
  fun _ _ h => A_mono S (add_le_add le_rfl (Nat.cast_le.2 h))

theorem A_mul_mono : Monotone fun m : ℕ => Aη S (ω * (m : Ordinal.{u})) :=
  fun _ _ h => A_mono S (mul_le_mul_left' (Nat.cast_le.2 h) _)

/-- The induction of Theorem T-LOW, with LOW-0 (`h1`) and LOW-STEP (`hstep`) as hypotheses. -/
theorem lower_bound (u : Ordinal.{u} → Ordinal.{u})
    (h1 : S.psi (Om ω) (Om 1) ≤ u 1)
    (hstep : ∀ ξ η, S.psi (Aη S η) (Om 1) ≤ u ξ → S.psi (Aη S η + th S) (Om 1) ≤ u (ξ + 1))
    (hmono : Monotone u) :
    ∀ m n : ℕ, S.psi (Aη S (ω * m + n)) (Om 1) ≤ u (1 + (ω * m + n)) := by
  intro m
  induction m with
  | zero =>
    intro n
    induction n with
    | zero => simpa [Aη] using h1
    | succ n ihn =>
      have e1 : (1 : Ordinal.{u}) + (ω * ((0 : ℕ) : Ordinal.{u}) + ((n + 1 : ℕ) : Ordinal.{u})) =
          1 + (ω * ((0 : ℕ) : Ordinal.{u}) + n) + 1 := by
        push_cast; simp only [add_assoc]
      have e2 : Aη S (ω * ((0 : ℕ) : Ordinal.{u}) + ((n + 1 : ℕ) : Ordinal.{u})) =
          Aη S (ω * ((0 : ℕ) : Ordinal.{u}) + n) + th S := by
        rw [A_succ]; push_cast; rw [add_assoc]
      rw [e1, e2]
      exact hstep _ _ ihn
  | succ k ihk =>
    intro n
    induction n with
    | zero =>
      simp only [Nat.cast_zero, add_zero]
      rw [A_omega_mul_succ, Low.psi_one_iSup (A_nat_mono S k)]
      apply ciSup_le
      intro n
      have hle : ω * (k : Ordinal.{u}) + n ≤ ω * ((k + 1 : ℕ) : Ordinal.{u}) := by
        push_cast
        rw [mul_add_one]
        exact add_le_add le_rfl (natCast_lt_omega0 n).le
      exact (ihk n).trans (hmono (add_le_add le_rfl hle))
    | succ n ihn =>
      have e1 : (1 : Ordinal.{u}) + (ω * ((k + 1 : ℕ) : Ordinal.{u}) + ((n + 1 : ℕ) : Ordinal.{u})) =
          1 + (ω * ((k + 1 : ℕ) : Ordinal.{u}) + n) + 1 := by
        push_cast; simp only [add_assoc]
      have e2 : Aη S (ω * ((k + 1 : ℕ) : Ordinal.{u}) + ((n + 1 : ℕ) : Ordinal.{u})) =
          Aη S (ω * ((k + 1 : ℕ) : Ordinal.{u}) + n) + th S := by
        rw [A_succ]; push_cast; rw [add_assoc]
      rw [e1, e2]
      exact hstep _ _ ihn

/-- The limit `η = ω²`. -/
theorem lower_bound_ww (u : Ordinal.{u} → Ordinal.{u})
    (h1 : S.psi (Om ω) (Om 1) ≤ u 1)
    (hstep : ∀ ξ η, S.psi (Aη S η) (Om 1) ≤ u ξ → S.psi (Aη S η + th S) (Om 1) ≤ u (ξ + 1))
    (hmono : Monotone u) :
    S.psi (Aη S (ω * ω)) (Om 1) ≤ u (ω * ω) := by
  rw [A_omega_mul_omega, Low.psi_one_iSup (A_mul_mono S)]
  apply ciSup_le
  intro m
  have h := lower_bound S u h1 hstep hmono m 0
  simp only [Nat.cast_zero, add_zero] at h
  have hm1 : (m : Ordinal.{u}) + 1 < ω := by exact_mod_cast natCast_lt_omega0 (m + 1)
  have h2 : ω * (m : Ordinal.{u}) + ω ≤ ω * ω := by
    rw [← mul_add_one]
    exact mul_le_mul_left' hm1.le _
  have hle1 : 1 + ω * (m : Ordinal.{u}) ≤ ω * (m : Ordinal.{u}) + ω := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simpa using one_lt_omega0.le
    · rw [one_add_of_omega0_le (le_mul_left _ (by exact_mod_cast hm))]
      exact Ordinal.le_add_right _ _
  have hle : 1 + ω * (m : Ordinal.{u}) ≤ ω * ω := hle1.trans h2
  exact h.trans (hmono hle)

/-- **Conjecture T** for `η < ω²`, given both halves of the step as hypotheses. -/
theorem conjT (u : Ordinal.{u} → Ordinal.{u})
    (hl1 : S.psi (Om ω) (Om 1) ≤ u 1)
    (hlstep : ∀ ξ η, S.psi (Aη S η) (Om 1) ≤ u ξ → S.psi (Aη S η + th S) (Om 1) ≤ u (ξ + 1))
    (hmono : Monotone u)
    (hu1 : u 1 ≤ S.psi (Om ω) (Om 1))
    (hustep : ∀ ξ A, Om ω ≤ A → HA S A → u ξ ≤ S.psi A (Om 1) →
      u (ξ + 1) ≤ S.psi (A + th S) (Om 1))
    (hulim : ∀ l B, IsSuccLimit l → (∀ ι, 1 ≤ ι → ι < l → u ι ≤ B) → u l ≤ B)
    (m n : ℕ) : u (1 + (ω * m + n)) = S.psi (Aη S (ω * m + n)) (Om 1) :=
  le_antisymm (upper_bound S u hu1 hustep hulim m n) (lower_bound S u hl1 hlstep hmono m n)

/-- **Conjecture T** at `η = ω²`: `u (ω²) = ψ_{Ω_1}(Ω_ω + θ·ω²)`. -/
theorem conjT_ww (u : Ordinal.{u} → Ordinal.{u})
    (hl1 : S.psi (Om ω) (Om 1) ≤ u 1)
    (hlstep : ∀ ξ η, S.psi (Aη S η) (Om 1) ≤ u ξ → S.psi (Aη S η + th S) (Om 1) ≤ u (ξ + 1))
    (hmono : Monotone u)
    (hu1 : u 1 ≤ S.psi (Om ω) (Om 1))
    (hustep : ∀ ξ A, Om ω ≤ A → HA S A → u ξ ≤ S.psi A (Om 1) →
      u (ξ + 1) ≤ S.psi (A + th S) (Om 1))
    (hulim : ∀ l B, IsSuccLimit l → (∀ ι, 1 ≤ ι → ι < l → u ι ≤ B) → u l ≤ B) :
    u (ω * ω) = S.psi (Aη S (ω * ω)) (Om 1) :=
  le_antisymm (upper_bound_ww S u hu1 hustep hulim) (lower_bound_ww S u hl1 hlstep hmono)

end Googology.Notation.InaccPsi.ConjT
