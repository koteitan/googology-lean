import Googology.Trans.PoR.InaccPsi.R2.VzV
import Googology.Trans.PoR.InaccPsi.R2.VzR

/-!
# The fixed-point levels of `ϑᵗ(Ω₁·k + η)`, `1 ≤ k < ω`

`P_k` is the range of `φ_k = veblen k` (`P_1 = E`).  From the cited facts of `R2.CitedVz` ([W07a] Lemma 3.30, Lemma 4.4,
Convention 4.1) and `R2.CitedEv`, for a base `τ ∈ E ∩ Ω₁` and `η ∈ Tᵗ ∩ Ω₁` (the remark after [W07a] Convention 4.1:
`η ↦ ϑᵗ(Δ + η)` "enumerates the ordinals of the interval `(τ, Ω₁)` of the same 'fixed point level' which is
indicated by `Δ`", here proved for `Δ = Ω₁·k`):

* `VzP`, `vzP_E`, `vzP_mono`, `vzP_succ`; `vz_th_facts` (`ϑᵗ(Ω₁·k + η) ∈ Tᵗ ∩ E ∩ (τ, Ω₁)`, above `η`),
  `vz_th_lt`, `vz_th_le` (monotone in `η`);
* `vz_level` (by strong induction on `k`):
  - **minimality**: every `u ∈ P_k` above `τ`, above `η` and above every `ϑᵗ(Ω₁·k + σ)`, `σ < η`, is
    `≥ ϑᵗ(Ω₁·k + η)` (a smaller one is `ϑᵗ(Ω₁·q + r)`, `q ≤ k`, by Lemma 3.30 and Convention 4.1; `q = k` is excluded
    by the hypothesis, `q < k` by the next item at `q`);
  - **`ϑᵗ(Ω₁·k + η) ∉ P_{k+1}`** (a fixed point `a` of `φ_k` would have every `ϑᵗ(Ω₁·k + σ)`, `σ < a`, below `a`, so
    by Lemma 4.4 its argument would be `≥ Ω₁·(k + 1)`);
* `vz_th_min`, `vz_th_notP`, `vz_th_ub` (**`ϑᵗ(Ω₁·k + s' + d) ≤ φ_k(i + d + 1)`** whenever `ϑᵗ(Ω₁·k + s') ≤ φ_k(i)`
  and `s' < φ_k(i)`), `vz_th_ub0` (`ϑᵗ(Ω₁·k + σ) ≤ φ_k(τ + σ + 1)`);
* `vz_th_P` (**`ϑᵗ(Ω₁·k + η) ∈ P_k`**), `vz_th_least` (**`ϑᵗ(Ω₁·k)` is the least element of `P_k` above `τ`**);
* `vz_lh_th_fix`, `vz_lh_th_lim` (**the `R₁⁺`-reach**: `lh(ϑᵗ(Ω₁·k + η)) = ϑᵗ(Ω₁·k + η)·(k + 1) + ζ`, `ζ = logend(η)`
  if `η < ϑᵗ(Ω₁·k + σ)` for some `σ < η`, else `0`; [W07b] Theorem 5.3 with `vzLhT_fix`, `vzLhT_lim`).
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order

/-- `P_k`: the range of `φ_k`. -/
def VzP (k : ℕ) (a : Ordinal.{0}) : Prop := a ∈ Set.range (veblen (k : Ordinal.{0}))

theorem vzP_veblen (k : ℕ) (i : Ordinal.{0}) : VzP k (veblen (k : Ordinal.{0}) i) := ⟨i, rfl⟩

theorem vzP_E {k : ℕ} (hk : 1 ≤ k) {a : Ordinal.{0}} (h : VzP k a) : InE a := by
  obtain ⟨j, rfl⟩ := h
  have hk0 : (0 : Ordinal.{0}) < (k : Ordinal.{0}) := by exact_mod_cast (by omega : 0 < k)
  have := veblen_veblen_of_lt (o₁ := 0) (o₂ := (k : Ordinal.{0})) hk0 j
  rw [veblen_zero_apply] at this
  exact this

theorem vzP_mono {k k' : ℕ} (hk : 1 ≤ k) (hkk : k ≤ k') {a : Ordinal.{0}} (h : VzP k' a) : VzP k a := by
  have hk0 : (k : Ordinal.{0}) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hk0' : (k' : Ordinal.{0}) ≠ 0 := by exact_mod_cast (by omega : k' ≠ 0)
  have h' := (mem_range_veblen hk0').1 h
  refine (mem_range_veblen hk0).2 (fun b hb => h' b (lt_of_lt_of_le hb (by exact_mod_cast hkk)))

theorem vzP_succ {k : ℕ} {a : Ordinal.{0}} : VzP (k + 1) a ↔ veblen (k : Ordinal.{0}) a = a := by
  unfold VzP
  rw [Nat.cast_succ, veblen_add_one]
  exact mem_range_deriv (isNormal_veblen _)

theorem vzP_one {a : Ordinal.{0}} : VzP 1 a ↔ InE a := by
  unfold VzP
  rw [Nat.cast_one, inE_iff_mem_range_epsilon]

/-- The facts on a term `ϑᵗ(Ω₁·k + η)` (`1 ≤ k`, `η ∈ Tᵗ ∩ Ω₁`). -/
theorem vz_th_facts {τ η : Ordinal.{0}} {k : ℕ} (hτ : InE τ) (hτ1 : τ < Om1) (hk : 1 ≤ k) (hη : η ∈ Tset τ)
    (hη1 : η < Om1) :
    Om1 * (k : Ordinal.{0}) + η ∈ Tset τ ∧ Om1 * (k : Ordinal.{0}) + η < OmTwo ∧
    vt τ (Om1 * (k : Ordinal.{0}) + η) ∈ Tset τ ∧ τ < vt τ (Om1 * (k : Ordinal.{0}) + η) ∧
    vt τ (Om1 * (k : Ordinal.{0}) + η) < Om1 ∧ InE (vt τ (Om1 * (k : Ordinal.{0}) + η)) ∧
    Indec (vt τ (Om1 * (k : Ordinal.{0}) + η)) ∧ η < vt τ (Om1 * (k : Ordinal.{0}) + η) := by
  have hγT := vzOm1_mul_T hτ hτ1 hη k
  have hγ2 := vzOm1_mul_lt hη1 k
  obtain ⟨hvT, -, hv1, hvP, -⟩ := vt_memTwo hτ hτ1 hγT hγ2
  have hΩ : Om1 ≤ Om1 * (k : Ordinal.{0}) + η := (vz_le_mul hk).trans le_self_add
  have hE := (vt_E_iff hτ hτ1 hγT hγ2).2 hΩ
  exact ⟨hγT, hγ2, hvT, hE.1, hv1, hE.2, hvP, vzLt_vt_self hτ hτ1 hk hη hη1⟩

/-- `η ↦ ϑᵗ(Ω₁·k + η)` is strictly increasing on `Tᵗ ∩ Ω₁`. -/
theorem vz_th_lt {τ σ η : Ordinal.{0}} {k : ℕ} (hτ : InE τ) (hτ1 : τ < Om1) (hk : 1 ≤ k) (hσ : σ ∈ Tset τ)
    (hη : η ∈ Tset τ) (hη1 : η < Om1) (h : σ < η) :
    vt τ (Om1 * (k : Ordinal.{0}) + σ) < vt τ (Om1 * (k : Ordinal.{0}) + η) :=
  vzVt_lt hτ hτ1 hσ (h.trans hη1) hη hη1 ((add_lt_add_iff_left _).2 h)
    (h.trans (vz_th_facts hτ hτ1 hk hη hη1).2.2.2.2.2.2.2)

theorem vz_th_le {τ σ η : Ordinal.{0}} {k : ℕ} (hτ : InE τ) (hτ1 : τ < Om1) (hk : 1 ≤ k) (hσ : σ ∈ Tset τ)
    (hη : η ∈ Tset τ) (hη1 : η < Om1) (h : σ ≤ η) :
    vt τ (Om1 * (k : Ordinal.{0}) + σ) ≤ vt τ (Om1 * (k : Ordinal.{0}) + η) := by
  rcases h.lt_or_eq with h | rfl
  · exact (vz_th_lt hτ hτ1 hk hσ hη hη1 h).le
  · exact le_rfl

/-- Division by `Ω₁`: `ξ = Ω₁·(ξ/Ω₁) + ξ % Ω₁` with `ξ % Ω₁ < Ω₁`. -/
theorem vz_div_Om1 (ξ : Ordinal.{0}) : Om1 * (ξ / Om1) + ξ % Om1 = ξ ∧ ξ % Om1 < Om1 :=
  ⟨Ordinal.div_add_mod ξ Om1, Ordinal.mod_lt ξ (Ordinal.omega_pos 1).ne'⟩

/-- **The fixed-point levels** (`vz_level`): minimality at level `k`, and `ϑᵗ(Ω₁·k + η) ∉ P_{k+1}`. -/
theorem vz_level {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) : ∀ k : ℕ, 1 ≤ k →
    (∀ η u, η ∈ Tset τ → η < Om1 → VzP k u → τ < u → η < u →
      (∀ σ, σ < η → vt τ (Om1 * (k : Ordinal.{0}) + σ) < u) → vt τ (Om1 * (k : Ordinal.{0}) + η) ≤ u) ∧
    (∀ η, η ∈ Tset τ → η < Om1 → ¬ VzP (k + 1) (vt τ (Om1 * (k : Ordinal.{0}) + η))) := by
  obtain ⟨m, -, -, -, hTm, -⟩ := T_next (Or.inr hτ) hτ1
  intro k
  induction k using Nat.strong_induction_on with
  | _ k IH =>
  intro hk
  -- minimality at `k`
  have Hmin : ∀ η u, η ∈ Tset τ → η < Om1 → VzP k u → τ < u → η < u →
      (∀ σ, σ < η → vt τ (Om1 * (k : Ordinal.{0}) + σ) < u) → vt τ (Om1 * (k : Ordinal.{0}) + η) ≤ u := by
    intro η u hηT hη1 hPu hτu hηu hprev
    by_contra hlt
    push Not at hlt
    obtain ⟨-, -, haT, -, ha1, -, -, -⟩ := vz_th_facts hτ hτ1 hk hηT hη1
    set a := vt τ (Om1 * (k : Ordinal.{0}) + η) with hadef
    have hu1 : u < Om1 := hlt.trans ha1
    have huT : u ∈ Tset τ := (hTm u hu1).2 (hlt.trans ((hTm a ha1).1 haT))
    have huE : InE u := vzP_E hk hPu
    obtain ⟨ξ, hξT, hξ2, hξu⟩ := vt_rep hτ hτ1 huT hτu.le hu1 (inE_indec huE)
    have hΩξ : Om1 ≤ ξ := (vt_E_iff hτ hτ1 hξT hξ2).1 ⟨by rw [hξu]; exact hτu, by rw [hξu]; exact huE⟩
    have hξlt : ξ < Om1 * (k : Ordinal.{0}) + η :=
      vzLt_of_vt_lt hτ hτ1 hξT hξ2 hηT hη1 (by rw [hξu]; exact hηu) (by rw [hξu]; exact hlt)
    obtain ⟨hdec, hr1⟩ := vz_div_Om1 ξ
    set q := ξ / Om1 with hq
    set r := ξ % Om1 with hr
    have hqk : q < ((k + 1 : ℕ) : Ordinal.{0}) := by
      have h1 : Om1 * q < Om1 * ((k + 1 : ℕ) : Ordinal.{0}) := by
        calc Om1 * q ≤ ξ := hdec ▸ le_self_add
          _ < Om1 * (k : Ordinal.{0}) + η := hξlt
          _ < Om1 * (k : Ordinal.{0}) + Om1 := (add_lt_add_iff_left _).2 hη1
          _ = Om1 * ((k + 1 : ℕ) : Ordinal.{0}) := by rw [Nat.cast_succ, mul_add_one]
      exact (mul_lt_mul_iff_right₀ (Ordinal.omega_pos 1)).1 h1
    obtain ⟨q', hq'⟩ := lt_omega0.1 (hqk.trans (natCast_lt_omega0 _))
    have hq'k : q' ≤ k := by
      have : (q' : Ordinal.{0}) < ((k + 1 : ℕ) : Ordinal.{0}) := hq' ▸ hqk
      exact Nat.lt_succ_iff.1 (by exact_mod_cast this)
    have hq'1 : 1 ≤ q' := by
      rcases Nat.eq_zero_or_pos q' with h0 | h0
      · exfalso
        rw [h0, Nat.cast_zero] at hq'
        rw [hq', mul_zero, zero_add] at hdec
        exact absurd (hdec ▸ hr1) (not_lt.2 hΩξ)
      · exact h0
    have hrT : r ∈ Tset τ := vzRem_T hτ hτ1 hξT hξ2 hdec.symm (dvd_mul_right _ _) hr1
    have hu' : vt τ (Om1 * (q' : Ordinal.{0}) + r) = u := by rw [← hq', hdec, hξu]
    rcases hq'k.lt_or_eq with hlt' | heq
    · exact (IH q' hlt' hq'1).2 r hrT hr1 (by rw [hu']; exact vzP_mono (by omega) (by omega) hPu)
    · subst heq
      have hrη : r < η := by
        have e : Om1 * (q' : Ordinal.{0}) + r = ξ := by rw [← hq']; exact hdec
        have : Om1 * (q' : Ordinal.{0}) + r < Om1 * (q' : Ordinal.{0}) + η := by rw [e]; exact hξlt
        exact (add_lt_add_iff_left _).1 this
      have := hprev r hrη
      rw [hu'] at this
      exact lt_irrefl _ this
  refine ⟨Hmin, ?_⟩
  -- not a fixed point of `φ_k`
  have Hub : ∀ σ, σ ∈ Tset τ → σ < Om1 →
      vt τ (Om1 * (k : Ordinal.{0}) + σ) ≤ veblen (k : Ordinal.{0}) (τ + σ + 1) := by
    intro σ
    induction σ using WellFoundedLT.induction with
    | ind σ IHσ =>
    intro hσT hσ1
    obtain ⟨-, -, hvT, -, hv1, -, -, -⟩ := vz_th_facts hτ hτ1 hk hσT hσ1
    have hσm : σ < m := (hTm σ hσ1).1 hσT
    refine Hmin σ _ hσT hσ1 (vzP_veblen k _) ?_ ?_ (fun σ' hσ' => ?_)
    · exact lt_of_lt_of_le (lt_of_le_of_lt le_self_add (lt_add_one _)) (right_le_veblen _ _)
    · exact lt_of_lt_of_le (lt_of_le_of_lt le_add_self (lt_add_one _)) (right_le_veblen _ _)
    · have hσ'T : σ' ∈ Tset τ := (hTm σ' (hσ'.trans hσ1)).2 (hσ'.trans hσm)
      refine lt_of_le_of_lt (IHσ σ' hσ' hσ'T (hσ'.trans hσ1)) ?_
      refine (veblen_lt_veblen_iff_right).2 ?_
      rw [add_assoc, add_assoc]
      exact (add_lt_add_iff_left τ).2 ((add_one_le_of_lt hσ').trans_lt (lt_add_one σ))
  intro η hηT hη1 hP
  obtain ⟨hγT, hγ2, haT, hτa, ha1, haE, -, -⟩ := vz_th_facts hτ hτ1 hk hηT hη1
  set a := vt τ (Om1 * (k : Ordinal.{0}) + η) with hadef
  have hfixa : veblen (k : Ordinal.{0}) a = a := vzP_succ.1 hP
  have ham : a < m := (hTm a ha1).1 haT
  have hfix : ∀ σ, σ < a → vt τ (Om1 * (k : Ordinal.{0}) + σ) < a := by
    intro σ hσ
    have hσ1 : σ < Om1 := hσ.trans ha1
    have hσT : σ ∈ Tset τ := (hTm σ hσ1).2 (hσ.trans ham)
    refine lt_of_le_of_lt (Hub σ hσT hσ1) ?_
    have hI := inE_indec haE
    have h1 : τ + σ + 1 < a :=
      hI.add_lt (hI.add_lt hτa hσ) (lt_of_lt_of_le one_lt_omega0 (omega0_lt_inE haE).le)
    have := (veblen_lt_veblen_iff_right (o := (k : Ordinal.{0}))).2 h1
    rwa [hfixa] at this
  have := vzFix_level hτ hτ1 hk haT ha1 haE.pos hfix hγT hγ2 rfl
  have h2 : Om1 * (k : Ordinal.{0}) + η < Om1 * ((k + 1 : ℕ) : Ordinal.{0}) := by
    rw [Nat.cast_succ, mul_add_one]; exact (add_lt_add_iff_left _).2 hη1
  exact absurd this (not_le.2 h2)

/-- **Minimality at level `k`**. -/
theorem vz_th_min {τ η u : Ordinal.{0}} {k : ℕ} (hτ : InE τ) (hτ1 : τ < Om1) (hk : 1 ≤ k) (hη : η ∈ Tset τ)
    (hη1 : η < Om1) (hPu : VzP k u) (hτu : τ < u) (hηu : η < u)
    (hprev : ∀ σ, σ < η → vt τ (Om1 * (k : Ordinal.{0}) + σ) < u) : vt τ (Om1 * (k : Ordinal.{0}) + η) ≤ u :=
  (vz_level hτ hτ1 k hk).1 η u hη hη1 hPu hτu hηu hprev

/-- **`ϑᵗ(Ω₁·k + η) ∉ P_{k+1}`**. -/
theorem vz_th_notP {τ η : Ordinal.{0}} {k : ℕ} (hτ : InE τ) (hτ1 : τ < Om1) (hk : 1 ≤ k) (hη : η ∈ Tset τ)
    (hη1 : η < Om1) : ¬ VzP (k + 1) (vt τ (Om1 * (k : Ordinal.{0}) + η)) :=
  (vz_level hτ hτ1 k hk).2 η hη hη1

/-- `Tᵗ ∩ Ω₁` is an initial segment. -/
theorem vz_T_down {τ x y : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hx : x ∈ Tset τ) (hx1 : x < Om1)
    (hy : y ≤ x) : y ∈ Tset τ := by
  obtain ⟨m, -, -, -, hTm, -⟩ := T_next (Or.inr hτ) hτ1
  exact (hTm y (lt_of_le_of_lt hy hx1)).2 (lt_of_le_of_lt hy ((hTm x hx1).1 hx))

/-- **The upper bound by `φ_k`**: if `ϑᵗ(Ω₁·k + s') ≤ φ_k(i)` and `s' < φ_k(i)`, then
`ϑᵗ(Ω₁·k + s' + d) ≤ φ_k(i + d + 1)` for every `d` with `s' + d ∈ Tᵗ ∩ Ω₁`. -/
theorem vz_th_ub {τ s' i : Ordinal.{0}} {k : ℕ} (hτ : InE τ) (hτ1 : τ < Om1) (hk : 1 ≤ k)
    (hs' : s' ∈ Tset τ) (hs'1 : s' < Om1) (hb : vt τ (Om1 * (k : Ordinal.{0}) + s') ≤ veblen (k : Ordinal.{0}) i)
    (hsb : s' < veblen (k : Ordinal.{0}) i) :
    ∀ d, s' + d ∈ Tset τ → s' + d < Om1 →
      vt τ (Om1 * (k : Ordinal.{0}) + (s' + d)) ≤ veblen (k : Ordinal.{0}) (i + d + 1) := by
  intro d
  induction d using WellFoundedLT.induction with
  | ind d IHd =>
  intro hdT hd1
  have hPi := vzP_veblen k (i + d + 1)
  have hτb : τ < veblen (k : Ordinal.{0}) i :=
    lt_of_lt_of_le (vz_th_facts hτ hτ1 hk hs' hs'1).2.2.2.1 hb
  have hii : veblen (k : Ordinal.{0}) i ≤ veblen (k : Ordinal.{0}) (i + d + 1) :=
    (veblen_le_veblen_iff_right).2 (le_self_add.trans le_self_add)
  have huE : InE (veblen (k : Ordinal.{0}) (i + d + 1)) := vzP_E hk hPi
  refine vz_th_min hτ hτ1 hk hdT hd1 hPi (hτb.trans_le hii) ?_ ?_
  · have h1 : d < veblen (k : Ordinal.{0}) (i + d + 1) :=
      lt_of_lt_of_le (lt_of_le_of_lt le_add_self (lt_add_one _)) (right_le_veblen _ _)
    exact (inE_indec huE).add_lt (hsb.trans_le hii) h1
  · intro σ hσ
    have hσT : σ ∈ Tset τ := vz_T_down hτ hτ1 hdT hd1 hσ.le
    rcases lt_or_ge σ s' with hσs | hsσ
    · exact ((vz_th_lt hτ hτ1 hk hσT hs' hs'1 hσs).trans_le hb).trans_le hii
    · set d' := σ - s' with hd'
      have hσe : s' + d' = σ := Ordinal.add_sub_cancel_of_le hsσ
      have hd'd : d' < d := (add_lt_add_iff_left s').1 (by rw [hσe]; exact hσ)
      have h2 := IHd d' hd'd (by rw [hσe]; exact hσT) (by rw [hσe]; exact hσ.trans hd1)
      rw [hσe] at h2
      refine lt_of_le_of_lt h2 ((veblen_lt_veblen_iff_right).2 ?_)
      rw [add_assoc, add_assoc]
      exact (add_lt_add_iff_left i).2 ((add_one_le_of_lt hd'd).trans_lt (lt_add_one d))

/-- `ϑᵗ(Ω₁·k + σ) ≤ φ_k(τ + σ + 1)`. -/
theorem vz_th_ub0 {τ : Ordinal.{0}} {k : ℕ} (hτ : InE τ) (hτ1 : τ < Om1) (hk : 1 ≤ k) :
    ∀ σ, σ ∈ Tset τ → σ < Om1 → vt τ (Om1 * (k : Ordinal.{0}) + σ) ≤ veblen (k : Ordinal.{0}) (τ + σ + 1) := by
  intro σ
  induction σ using WellFoundedLT.induction with
  | ind σ IHσ =>
  intro hσT hσ1
  refine vz_th_min hτ hτ1 hk hσT hσ1 (vzP_veblen k _) ?_ ?_ (fun σ' hσ' => ?_)
  · exact lt_of_lt_of_le (lt_of_le_of_lt le_self_add (lt_add_one _)) (right_le_veblen _ _)
  · exact lt_of_lt_of_le (lt_of_le_of_lt le_add_self (lt_add_one _)) (right_le_veblen _ _)
  · have hσ'T : σ' ∈ Tset τ := vz_T_down hτ hτ1 hσT hσ1 hσ'.le
    refine lt_of_le_of_lt (IHσ σ' hσ' hσ'T (hσ'.trans hσ1)) ((veblen_lt_veblen_iff_right).2 ?_)
    rw [add_assoc, add_assoc]
    exact (add_lt_add_iff_left τ).2 ((add_one_le_of_lt hσ').trans_lt (lt_add_one σ))

/-- **The `R₁⁺`-reach of `ϑᵗ(Ω₁·k + η)`** when `ϑᵗ(Ω₁·k + σ) ≤ η` for every `σ < η`:
`lh = ϑᵗ(Ω₁·k + η)·(k + 1)`. -/
theorem vz_lh_th_fix {τ η : Ordinal.{0}} {k : ℕ} (hτ : InE τ) (hτ1 : τ < Om1) (hk : 1 ≤ k) (hη : η ∈ Tset τ)
    (hη1 : η < Om1) (hfix : ∀ σ, σ < η → vt τ (Om1 * (k : Ordinal.{0}) + σ) ≤ η) :
    IsLh1 (vt τ (Om1 * (k : Ordinal.{0}) + η))
      (vt τ (Om1 * (k : Ordinal.{0}) + η) * ((k + 1 : ℕ) : Ordinal.{0})) := by
  obtain ⟨-, -, hvT, hτv, hv1, -, hvP, -⟩ := vz_th_facts hτ hτ1 hk hη hη1
  have h := lh_eq_lhT (Or.inr hτ) hτ1 hvT hτv hv1 hvP
  rwa [vzLhT_fix hτ hτ1 hk hη hη1 hfix] at h

/-- **The `R₁⁺`-reach of `ϑᵗ(Ω₁·k + η)`** when `η < ϑᵗ(Ω₁·k + σ)` for some `σ < η`:
`lh = ϑᵗ(Ω₁·k + η)·(k + 1) + logend(η)`. -/
theorem vz_lh_th_lim {τ η : Ordinal.{0}} {k : ℕ} (hτ : InE τ) (hτ1 : τ < Om1) (hk : 1 ≤ k) (hη : η ∈ Tset τ)
    (hη1 : η < Om1) (hη0 : η ≠ 0) (hlim : ∃ σ, σ < η ∧ η < vt τ (Om1 * (k : Ordinal.{0}) + σ)) :
    IsLh1 (vt τ (Om1 * (k : Ordinal.{0}) + η))
      (vt τ (Om1 * (k : Ordinal.{0}) + η) * ((k + 1 : ℕ) : Ordinal.{0}) + lg η) := by
  obtain ⟨-, -, hvT, hτv, hv1, -, hvP, -⟩ := vz_th_facts hτ hτ1 hk hη hη1
  have h := lh_eq_lhT (Or.inr hτ) hτ1 hvT hτv hv1 hvP
  rwa [vzLhT_lim hτ hτ1 hk hη hη1 hη0 hlim] at h

/-- **`ϑᵗ(Ω₁·k + η) ∈ P_k`** (`1 ≤ k`): for `k + 1`, every `φ_k(j)`, `j < a`, is at most `ϑᵗ(Ω₁·k + j) < a`, so
`a = ϑᵗ(Ω₁·(k+1) + η)` is a fixed point of `φ_k`. -/
theorem vz_th_P {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) : ∀ k : ℕ, 1 ≤ k →
    ∀ η, η ∈ Tset τ → η < Om1 → VzP k (vt τ (Om1 * (k : Ordinal.{0}) + η)) := by
  intro k hk
  induction k with
  | zero => omega
  | succ k ih =>
    intro η hηT hη1
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · exact vzP_one.2 (vz_th_facts hτ hτ1 hk hηT hη1).2.2.2.2.2.1
    have ih' := ih hk1
    obtain ⟨-, -, haT, -, ha1, haE, -, -⟩ := vz_th_facts hτ hτ1 hk hηT hη1
    set a := vt τ (Om1 * ((k + 1 : ℕ) : Ordinal.{0}) + η) with hadef
    -- `φ_k(j) ≤ ϑᵗ(Ω₁·k + j)`
    have hC : ∀ j, j ∈ Tset τ → j < Om1 → veblen (k : Ordinal.{0}) j ≤ vt τ (Om1 * (k : Ordinal.{0}) + j) := by
      intro j
      induction j using WellFoundedLT.induction with
      | ind j IHj =>
      intro hjT hj1
      refine vz_veblen_le_of_lt (ih' j hjT hj1) (fun d hd => ?_)
      have hdT := vz_T_down hτ hτ1 hjT hj1 hd.le
      exact lt_of_le_of_lt (IHj d hd hdT (hd.trans hj1)) (vz_th_lt hτ hτ1 hk1 hdT hjT hj1 hd)
    refine vzP_succ.2 (le_antisymm ?_ (right_le_veblen _ a))
    rw [(isNormal_veblen _).apply_of_isSuccLimit (ev_isSuccLimit_of_inE haE)]
    refine Ordinal.iSup_le (fun j => ?_)
    have hj1 : j.1 < Om1 := j.2.trans ha1
    have hjT : j.1 ∈ Tset τ := vz_T_down hτ hτ1 haT ha1 j.2.le
    refine (hC j.1 hjT hj1).trans (vzVt_lt hτ hτ1 hjT hj1 hηT hη1 ?_ j.2).le
    calc Om1 * (k : Ordinal.{0}) + j.1 < Om1 * (k : Ordinal.{0}) + Om1 := (add_lt_add_iff_left _).2 hj1
      _ = Om1 * ((k + 1 : ℕ) : Ordinal.{0}) := by rw [Nat.cast_succ, mul_add_one]
      _ ≤ Om1 * ((k + 1 : ℕ) : Ordinal.{0}) + η := le_self_add

/-- **`ϑᵗ(Ω₁·k)` is the least value of `φ_k` above `τ`** (`1 ≤ k`). -/
theorem vz_th_least {τ : Ordinal.{0}} {k : ℕ} (hτ : InE τ) (hτ1 : τ < Om1) (hk : 1 ≤ k) :
    VzP k (vt τ (Om1 * (k : Ordinal.{0}) + 0)) ∧ τ < vt τ (Om1 * (k : Ordinal.{0}) + 0) ∧
      ∀ u, VzP k u → τ < u → vt τ (Om1 * (k : Ordinal.{0}) + 0) ≤ u := by
  have h0T := mem_T_of_le hτ hτ1 (zero_le : (0 : Ordinal.{0}) ≤ τ)
  refine ⟨vz_th_P hτ hτ1 k hk 0 h0T (Ordinal.omega_pos 1),
    (vz_th_facts hτ hτ1 hk h0T (Ordinal.omega_pos 1)).2.2.2.1, fun u hu hτu => ?_⟩
  exact vz_th_min hτ hτ1 hk h0T (Ordinal.omega_pos 1) hu hτu (lt_of_le_of_lt zero_le hτu)
    (fun σ hσ => absurd hσ (not_lt.2 zero_le))

end Googology.Trans.PoR.InaccPsi.R2
