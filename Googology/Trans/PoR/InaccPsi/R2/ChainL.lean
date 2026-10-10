import Googology.Trans.PoR.InaccPsi.R2.CitedL
import Googology.Trans.PoR.InaccPsi.R2.Ups
import Googology.Trans.PoR.InaccPsi.R2.FragM

/-!
# Lemma L: the chain bound in a gap of `R₁⁺`

The project's Lemma L (chain bound): for `τ ∈ {1} ∪ E` countable and `z₀ ∈ Tᵗ ∩ (τ, Ω₁)`,
a chain `z₀ <₁ z₁ <₁ ⋯ <₁ z_k` of `R₁⁺` has `k ≤ htᵗ(z₀) + 1`.

Proof (as in the paper proof): (1) every `zᵢ` with two successors is an `ε`-number
([W07b] §2 after Thm 2.2, `le1R_lim_P`, `le1R_two_iff`); (2) `z₁ ≤ lh(z₀) = lhᵗ(z₀)` ([W07b] Thm 5.3)
and `lh(z₀)` lies below the next point `<₁ ∞` above `z₀`, so `z₁ ∈ T^{z₀}` ([W07b] Cor 5.10);
(3) `ht_{z₀}(z₁) ≤ ht_{z₀}(lhᵗ(z₀)) < htᵗ(z₀)` ([W07a] Lemma 3.27, [W07b] Lemma 4.5); induction on `k`.

* `T_next`: the next point `<₁ ∞` above a base `τ ∈ {1} ∪ E` is `Tᵗ ∩ Ω₁` and is countable.
* `not_ltInf1_of_T`, `ltInf1_of_le1R`, `lh_lt_next`, `ht_mono`, `indec_of_lt1R`, `inE_of_chain2`.
* `chain_bound` (**Lemma L**), `chain_bound_le` (the form with a top `β`: `k ≤ htᵗ(β) + 1`).
* `chain_bound_gap`: inside a gap `(τ, m)` with `τ ∈ E`, every chain `τ < z₀ <₁ ⋯ <₁ z_k ≤ β` has
  `k ≤ htᵗ(β) + 1`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal

/-- The next point `<₁ ∞` above a countable base `τ ∈ {1} ∪ E`: it is `Tᵗ ∩ Ω₁` and it is countable
([W07b] Cor 5.10; [W07a] Thm 3.23, Lemma 3.27). -/
theorem T_next {τ : Ordinal.{0}} (hτ : τ = 1 ∨ InE τ) (hτ1 : τ < Om1) :
    ∃ m, τ < m ∧ LtInf1 m ∧ (∀ a, τ < a → LtInf1 a → m ≤ a) ∧
      (∀ a, a < Om1 → (a ∈ Tset τ ↔ a < m)) ∧ m < Om1 := by
  rcases hτ with rfl | hE
  · obtain ⟨m, h1m, hm, hmin, hT⟩ := T_inter_Om1_one
    obtain ⟨f, hf, hfb⟩ := T_one_bound
    exact ⟨m, h1m, hm, hmin, hT, lt_Om1_of_bound hT hf hfb⟩
  · obtain ⟨m, hτm, hm, hmin, hT⟩ := T_inter_Om1 hE hτ1
    exact ⟨m, hτm, hm, hmin, hT, lt_Om1_of_bound hT (f := Dl τ)
      (fun n => (Dl_spec hE hτ1 n).2.1) (fun a ha haT => (ht_spec hE hτ1 haT ha).1)⟩

/-- A point of `Tᵗ ∩ (τ, Ω₁)` is not `<₁ ∞`. -/
theorem not_ltInf1_of_T {τ x : Ordinal.{0}} (hτ : τ = 1 ∨ InE τ) (hτ1 : τ < Om1)
    (hxT : x ∈ Tset τ) (hτx : τ < x) (hx1 : x < Om1) : ¬ LtInf1 x := by
  intro hx
  obtain ⟨m, -, -, hmin, hT, -⟩ := T_next hτ hτ1
  exact absurd ((hT x hx1).1 hxT) (not_lt.2 (hmin x hτx hx))

/-- `x ≤₁ y <₁ ∞` gives `x <₁ ∞`. -/
theorem ltInf1_of_le1R {x y : Ordinal.{0}} (h : le1R x y) (hy : LtInf1 y) : LtInf1 x := by
  intro g hxg
  by_cases hgy : g ≤ y
  · exact le1R_of_le hxg hgy h
  · exact le1R_trans h (hy g (le_of_not_ge hgy))

/-- The reach of a point of `Tᵗ ∩ (τ, Ω₁)` lies below every point `<₁ ∞` above it. -/
theorem lh_lt_next {τ x l m : Ordinal.{0}} (hτ : τ = 1 ∨ InE τ) (hτ1 : τ < Om1)
    (hxT : x ∈ Tset τ) (hτx : τ < x) (hx1 : x < Om1) (hl : IsLh1 x l) (hmL : LtInf1 m)
    (hxm : x < m) : l < m := by
  by_contra hle
  exact not_ltInf1_of_T hτ hτ1 hxT hτx hx1
    (ltInf1_of_le1R (le1R_of_le hxm.le (not_lt.1 hle) hl.1) hmL)

/-- **[W07a] Lemma 3.27** (second sentence), from the first: `htᵗ` is weakly increasing on
`Tᵗ ∩ Ω₁` (`τ ∈ E`). -/
theorem ht_mono {τ x y : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hxT : x ∈ Tset τ)
    (hx1 : x < Om1) (hyT : y ∈ Tset τ) (hy1 : y < Om1) (hxy : x ≤ y) : ht τ x ≤ ht τ y := by
  obtain ⟨hex, heq⟩ := ht_spec hτ hτ1 hyT hy1
  obtain ⟨-, heqx⟩ := ht_spec hτ hτ1 hxT hx1
  rw [heqx, heq]
  apply Nat.sInf_le
  exact lt_of_le_of_lt hxy (Nat.sInf_mem hex)

/-- A proper `≤₁`-left end of `R₁⁺` is indecomposable ([W07b] §2 after Thm 2.2). -/
theorem indec_of_lt1R {a b : Ordinal.{0}} (h : le1R a b) (hab : a < b) : Indec a := by
  obtain ⟨hpos, hlim⟩ := le1R_lim_P h hab
  exact indec_of_limit hpos hlim

/-- `a <₁ b <₁ c` in `R₁⁺` gives `a ∈ E` (step (1) of Lemma L). -/
theorem inE_of_chain2 {a b c : Ordinal.{0}} (hab : le1R a b) (hab' : a < b) (hbc : le1R b c)
    (hbc' : b < c) : InE a := by
  have ha0 : 0 < a := (le1R_lim_P hab hab').1
  obtain ⟨-, hlim⟩ := le1R_lim_P hbc hbc'
  obtain ⟨p, hap, hpb, hp⟩ := hlim a hab'
  have h2 : a * 2 ≤ b := by
    rw [mul_two_eq]; exact (hp.add_lt hap hap).le.trans hpb.le
  exact (le1R_two_iff ha0).1
    (le1R_of_le (by rw [mul_two_eq]; exact le_self_add) h2 hab)

/-- **Lemma L** (chain bound).  For a countable base `τ ∈ {1} ∪ E` and `z₀ ∈ Tᵗ ∩ (τ, Ω₁)`: if
`z₀ <₁ z₁ <₁ ⋯ <₁ z_k` in `R₁⁺` (all countable), then `k ≤ htᵗ(z₀) + 1`. -/
theorem chain_bound (k : ℕ) : ∀ {τ : Ordinal.{0}} (z : ℕ → Ordinal.{0}), (τ = 1 ∨ InE τ) →
    τ < Om1 → z 0 ∈ Tset τ → τ < z 0 → (∀ i ≤ k, z i < Om1) →
    (∀ i < k, z i < z (i + 1) ∧ le1R (z i) (z (i + 1))) → k ≤ ht τ (z 0) + 1 := by
  induction k with
  | zero => intros; omega
  | succ k ih =>
    intro τ z hτ hτ1 hz0T hτz0 hlt hch
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · omega
    obtain ⟨h01, h01R⟩ := hch 0 (by omega)
    obtain ⟨h12, h12R⟩ := hch 1 (by omega)
    have hz01 : z 0 < Om1 := hlt 0 (by omega)
    have hz0E : InE (z 0) := inE_of_chain2 h01R h01 h12R h12
    have hz0I : Indec (z 0) := indec_of_lt1R h01R h01
    have hl := lh_eq_lhT hτ hτ1 hz0T hτz0 hz01 hz0I
    have hz1l : z 1 ≤ lhT τ (z 0) := hl.2 _ h01R
    obtain ⟨m, hzm, hmL, -, hT, hm1⟩ := T_next (Or.inr hz0E) hz01
    have hlm : lhT τ (z 0) < m := lh_lt_next hτ hτ1 hz0T hτz0 hz01 hl hmL hzm
    have hz1T : z 1 ∈ Tset (z 0) := (hT _ (hlt 1 (by omega))).2 (lt_of_le_of_lt hz1l hlm)
    have hlT : lhT τ (z 0) ∈ Tset (z 0) := (hT _ (hlm.trans hm1)).2 hlm
    have hmono : ht (z 0) (z 1) ≤ ht (z 0) (lhT τ (z 0)) :=
      ht_mono hz0E hz01 hz1T (hlt 1 (by omega)) hlT (hlm.trans hm1) hz1l
    have hdec := ht_lhT_lt hτ hτ1 hz0T hτz0 hz01 hz0E
    have := ih (fun i => z (i + 1)) (Or.inr hz0E) hz01 hz1T h01
      (fun i hi => hlt (i + 1) (by omega)) (fun i hi => hch (i + 1) (by omega))
    simp only [zero_add] at this
    omega

/-- **Lemma L**, the form with a top: for `τ ∈ E` countable and `β ∈ Tᵗ ∩ Ω₁`, a chain
`τ < z₀ <₁ ⋯ <₁ z_k ≤ β` has `k ≤ htᵗ(β) + 1`. -/
theorem chain_bound_le {τ β : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hβT : β ∈ Tset τ)
    (hβ1 : β < Om1) (k : ℕ) (z : ℕ → Ordinal.{0}) (hτz0 : τ < z 0) (hzk : z k ≤ β)
    (hch : ∀ i < k, z i < z (i + 1) ∧ le1R (z i) (z (i + 1))) : k ≤ ht τ β + 1 := by
  have hmono : ∀ i ≤ k, z i ≤ z k := by
    intro i hi
    induction hi using Nat.decreasingInduction with
    | self => exact le_rfl
    | of_succ j hj ih => exact (hch j hj).1.le.trans ih
  have hlt : ∀ i ≤ k, z i < Om1 := fun i hi => lt_of_le_of_lt ((hmono i hi).trans hzk) hβ1
  obtain ⟨m, -, -, -, hT, -⟩ := T_next (Or.inr hτ) hτ1
  have hz0β : z 0 ≤ β := (hmono 0 (Nat.zero_le k)).trans hzk
  have hz0T : z 0 ∈ Tset τ :=
    (hT _ (hlt 0 (Nat.zero_le k))).2 (lt_of_le_of_lt hz0β ((hT β hβ1).1 hβT))
  have h1 := chain_bound k z (Or.inr hτ) hτ1 hz0T hτz0 hlt hch
  have h2 := ht_mono hτ hτ1 hz0T (hlt 0 (Nat.zero_le k)) hβT hβ1 hz0β
  omega

/-- **Lemma L** inside a gap: for `τ ∈ E` countable with `Tᵗ ∩ Ω₁ = m` and `τ < β < m`, a chain
`τ < z₀ <₁ ⋯ <₁ z_k ≤ β` of `R₁⁺` has `k ≤ htᵗ(β) + 1`. -/
theorem chain_bound_gap {τ m β : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1)
    (hT : ∀ a, a < Om1 → (a ∈ Tset τ ↔ a < m)) (hβm : β < m) (hβ1 : β < Om1) (k : ℕ)
    (z : ℕ → Ordinal.{0}) (hτz0 : τ < z 0) (hzk : z k ≤ β)
    (hch : ∀ i < k, z i < z (i + 1) ∧ le1R (z i) (z (i + 1))) : k ≤ ht τ β + 1 :=
  chain_bound_le hτ hτ1 ((hT β hβ1).2 hβm) hβ1 k z hτz0 hzk hch

end Googology.Trans.PoR.InaccPsi.R2
