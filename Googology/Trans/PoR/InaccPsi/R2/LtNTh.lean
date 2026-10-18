import Googology.Trans.PoR.InaccPsi.R2.LtSw

/-!
# The level `ω` below the bounds `c_K(x)`: `c_0 = y_ω`, `c_{K+1} = ϑˣ(Ω₁·ω + c_K)`

For a base `x ∈ E ∩ Ω₁`, `ltC x K = c_K(x)` (`c_1 = sup_K T_K = ltTw`, `ltC_one`).  From [W07a] Lemma 3.30 at
`Ω₁·ω + η` (the axioms of `R2.CitedLz`) and the cited value `ltLhT_w_lim` (`R2.CitedLt`), for `η ∈ Tˣ ∩ Ω₁` below
some `c_K(x)`:

* `ltC_facts`, `ltC_step` (**`c_j < r` gives `c_{j+1} < ϑˣ(Ω₁·ω + r)`**, with `c_j < c_{j+1}`), `ltC_strict`;
* `ltn_self` (**`η < ϑˣ(Ω₁·ω + η)`**), `ltn_mono`, `ltn_mono_le`, `ltn_lim` (**`η < ϑˣ(Ω₁·ω + σ)` for some
  `σ < η`**, `η > 0`), `ltn_lh` (**`lh(ϑˣ(Ω₁·ω + η)) = ϑˣ(Ω₁·ω + η)·ω + logend(η)`**), `ltn_le1R`, `ltn_ub`
  (**`ϑˣ(Ω₁·ω + s' + d) ≤ φ_ω(i + d + 1)`** under `ϑˣ(Ω₁·ω + s') ≤ φ_ω(i)`, `s' < φ_ω(i)`).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Lt

open Ordinal Order Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Xt
  Googology.Trans.PoR.InaccPsi.R2.Lz

/-- The bounds `c_0 = y_ω`, `c_{K+1} = ϑˣ(Ω₁·ω + c_K)`. -/
noncomputable def ltC (x : Ordinal.{0}) : ℕ → Ordinal.{0}
  | 0 => lzYw x
  | K + 1 => vt x (Om1 * ω + ltC x K)

theorem ltC_zero (x : Ordinal.{0}) : ltC x 0 = lzYw x := rfl

theorem ltC_succ (x : Ordinal.{0}) (K : ℕ) : ltC x (K + 1) = vt x (Om1 * ω + ltC x K) := rfl

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

/-- The facts on `c_K(x)`. -/
theorem ltC_facts : ∀ K : ℕ, ltC x K ∈ Tset x ∧ ltC x K < Om1 ∧ x < ltC x K ∧ InE (ltC x K)
  | 0 => ⟨(ltYw_T hx hx1).1, (ltYw_T hx hx1).2, (lzY_facts hx hx1 0).2.1.trans_le (lzY_le_w x 0),
      ltYw_E hx hx1⟩
  | K + 1 => by
    obtain ⟨hT, h1, -, -⟩ := ltC_facts K
    obtain ⟨hvT, hxv, hv1, hvE, -⟩ := lt_w_facts hx hx1 hT h1
    exact ⟨hvT, hv1, hxv, hvE⟩

theorem ltC_one : ltC x 1 = ltTw x := (ltTw_eq hx hx1).symm

theorem ltYw_lt_w_arg {r : Ordinal.{0}} (hrT : r ∈ Tset x) (hr1 : r < Om1) (hωr : (ω : Ordinal.{0}) < r) :
    lzYw x < vt x (Om1 * ω + r) := by
  have hω := lt_omega_T hx hx1
  have hE := (lt_w_facts hx hx1 hrT hr1).2.2.2.1
  have h := lzVt_lt_ww hx hx1 hω.1 hrT hr1 hωr (omega0_lt_inE hE)
  rwa [← ltYw_eq hx hx1] at h

/-- **The step**: `c_j < c_{j+1}`, and `c_j < r` gives `c_{j+1} < ϑˣ(Ω₁·ω + r)`. -/
theorem ltC_step : ∀ j : ℕ, ltC x j < ltC x (j + 1) ∧
    ∀ r, r ∈ Tset x → r < Om1 → ltC x j < r → ltC x (j + 1) < vt x (Om1 * ω + r)
  | 0 => by
    refine ⟨ltYw_lt_self hx hx1, fun r hrT hr1 hjr => ?_⟩
    obtain ⟨hcT, hc1, -, hcE⟩ := ltC_facts hx hx1 0
    have hωr : (ω : Ordinal.{0}) < r := (omega0_lt_inE hcE).trans hjr
    exact lzVt_lt_ww hx hx1 hcT hrT hr1 hjr (ltYw_lt_w_arg hx hx1 hrT hr1 hωr)
  | j + 1 => by
    obtain ⟨hs, hP⟩ := ltC_step j
    obtain ⟨hcT, hc1, -, -⟩ := ltC_facts hx hx1 (j + 1)
    refine ⟨hP _ hcT hc1 hs, fun r hrT hr1 hjr => ?_⟩
    exact lzVt_lt_ww hx hx1 hcT hrT hr1 hjr (hP r hrT hr1 (hs.trans hjr))

theorem ltC_strict {j K : ℕ} (h : j < K) : ltC x j < ltC x K := by
  induction K with
  | zero => omega
  | succ K ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h' | rfl
    · exact (ih h').trans (ltC_step hx hx1 K).1
    · exact (ltC_step hx hx1 j).1

theorem ltC_mono {j K : ℕ} (h : j ≤ K) : ltC x j ≤ ltC x K := by
  rcases h.lt_or_eq with h | rfl
  · exact (ltC_strict hx hx1 h).le
  · exact le_rfl

/-- **`η < ϑˣ(Ω₁·ω + η)` below `c_K(x)`.** -/
theorem ltn_self : ∀ K : ℕ, ∀ {η : Ordinal.{0}}, η ∈ Tset x → η < Om1 → η < ltC x K →
    η < vt x (Om1 * ω + η)
  | 0, _, hη, hη1, hηK => lt_w_self hx hx1 hη hη1 hηK
  | K + 1, η, hη, hη1, hηK => by
    rcases lt_trichotomy η (ltC x K) with h | rfl | h
    · exact ltn_self K hη hη1 h
    · exact (ltC_step hx hx1 K).1
    · exact hηK.trans ((ltC_step hx hx1 K).2 η hη hη1 h)

theorem ltn_mono {K : ℕ} {σ η : Ordinal.{0}} (hσ : σ ∈ Tset x) (hη : η ∈ Tset x) (hη1 : η < Om1)
    (hηK : η < ltC x K) (h : σ < η) : vt x (Om1 * ω + σ) < vt x (Om1 * ω + η) :=
  lzVt_lt_ww hx hx1 hσ hη hη1 h (h.trans (ltn_self hx hx1 K hη hη1 hηK))

theorem ltn_mono_le {K : ℕ} {σ η : Ordinal.{0}} (hσ : σ ∈ Tset x) (hη : η ∈ Tset x) (hη1 : η < Om1)
    (hηK : η < ltC x K) (h : σ ≤ η) : vt x (Om1 * ω + σ) ≤ vt x (Om1 * ω + η) := by
  rcases h.lt_or_eq with h | rfl
  · exact (ltn_mono hx hx1 hσ hη hη1 hηK h).le
  · exact le_rfl

/-- **`η < ϑˣ(Ω₁·ω + σ)` for some `σ < η`** (`0 < η < c_K(x)`). -/
theorem ltn_lim : ∀ K : ℕ, ∀ {η : Ordinal.{0}}, η ∈ Tset x → η < Om1 → η ≠ 0 → η < ltC x K →
    ∃ σ, σ < η ∧ η < vt x (Om1 * ω + σ)
  | 0, η, hη, hη1, hη0, hηK => by
    obtain ⟨k, hk⟩ := lzYw_lt_iff.1 hηK
    rcases lt_or_ge (k : Ordinal.{0}) η with hkη | hηk
    · exact ⟨k, hkη, hk⟩
    · refine ⟨0, pos_iff_ne_zero.2 hη0, ?_⟩
      have hE := (lt_w_facts hx hx1 (mem_T_of_le hx hx1 (zero_le : (0 : Ordinal.{0}) ≤ x))
        (Ordinal.omega_pos 1)).2.2.2.1
      exact lt_of_le_of_lt hηk ((natCast_lt_omega0 k).trans (omega0_lt_inE hE))
  | K + 1, η, hη, hη1, hη0, hηK => by
    obtain ⟨hcT, hc1, -, hcE⟩ := ltC_facts hx hx1 K
    rcases lt_trichotomy η (ltC x K) with h | rfl | h
    · exact ltn_lim K hη hη1 hη0 h
    · rcases K with _ | K
      · -- `η = y_ω`, `σ = ω + 1`
        have hω := lt_omega_T hx hx1
        have hω1T : (ω : Ordinal.{0}) + 1 ∈ Tset x :=
          vzT_add hx hx1 hω.1 (by exact_mod_cast (lz_natT hx hx1 1).1)
        have hω1y : (ω : Ordinal.{0}) + 1 < ltC x 0 :=
          (inE_indec hcE).add_lt (omega0_lt_inE hcE) (one_lt_omega0.trans (omega0_lt_inE hcE))
        refine ⟨ω + 1, hω1y, ?_⟩
        exact ltYw_lt_w_arg hx hx1 hω1T (hω1y.trans hc1) (lt_add_one _)
      · -- `η = c_{K+1} = ϑ(Ω₁·ω + c_K)`, `σ = c_K + 1`
        obtain ⟨hdT, hd1, -, hdE⟩ := ltC_facts hx hx1 K
        have hd1T : ltC x K + 1 ∈ Tset x := vzT_add hx hx1 hdT (by exact_mod_cast (lz_natT hx hx1 1).1)
        have hlt : ltC x K + 1 < ltC x (K + 1) :=
          (inE_indec hcE).add_lt (ltC_step hx hx1 K).1 (one_lt_omega0.trans (omega0_lt_inE hcE))
        refine ⟨ltC x K + 1, hlt, ?_⟩
        have hd11 : ltC x K + 1 < Om1 := hlt.trans hc1
        have hE1 := (lt_w_facts hx hx1 hd1T hd11).2.2.2.1
        have hK1 : ltC x K + 1 < ltC x (K + 1 + 1) := hlt.trans (ltC_step hx hx1 (K + 1)).1
        exact lzVt_lt_ww hx hx1 hdT hd1T hd11 (lt_add_one _) ((lt_add_one _).trans
          (ltn_self hx hx1 (K + 1 + 1) hd1T hd11 hK1))
    · exact ⟨ltC x K, h, hηK⟩

/-- **The `R₁⁺`-reach of `ϑˣ(Ω₁·ω + η)`** for `0 < η < c_K(x)`: `lh = ϑˣ(Ω₁·ω + η)·ω + logend(η)`. -/
theorem ltn_lh {K : ℕ} {η : Ordinal.{0}} (hη : η ∈ Tset x) (hη1 : η < Om1) (hη0 : η ≠ 0)
    (hηK : η < ltC x K) : IsLh1 (vt x (Om1 * ω + η)) (vt x (Om1 * ω + η) * ω + lg η) := by
  obtain ⟨hvT, hxv, hv1, -, hvP⟩ := lt_w_facts hx hx1 hη hη1
  have h := lh_eq_lhT (Or.inr hx) hx1 hvT hxv hv1 hvP
  rwa [ltLhT_w_lim hx hx1 hη hη1 hη0 (ltn_self hx hx1 K hη hη1 hηK) (ltn_lim hx hx1 K hη hη1 hη0 hηK)] at h

/-- `ϑˣ(Ω₁·ω + η) ≤₁ ϑˣ(Ω₁·ω + η)·ω` in `R₁⁺` for `η < c_K(x)`. -/
theorem ltn_le1R {K : ℕ} {η : Ordinal.{0}} (hη : η ∈ Tset x) (hη1 : η < Om1) (hηK : η < ltC x K) :
    le1R (vt x (Om1 * ω + η)) (vt x (Om1 * ω + η) * ω) := by
  rcases eq_or_ne η 0 with rfl | hη0
  · exact (lt_w_lh0 hx hx1).1
  · exact lt_le1R_w_base (ltn_lh hx hx1 hη hη1 hη0 hηK).1

/-- **The upper bound by `φ_ω`** below `c_K(x)`. -/
theorem ltn_ub {K : ℕ} {s' i : Ordinal.{0}} (hs' : s' ∈ Tset x) (hs'1 : s' < Om1) (hs'K : s' < ltC x K)
    (hb : vt x (Om1 * ω + s') ≤ veblen ω i) (hsb : s' < veblen ω i) :
    ∀ d, s' + d ∈ Tset x → s' + d < Om1 → vt x (Om1 * ω + (s' + d)) ≤ veblen ω (i + d + 1) := by
  intro d
  induction d using WellFoundedLT.induction with
  | ind d IHd =>
  intro hdT hd1
  have hPi : veblen ω (i + d + 1) ∈ Set.range (veblen ω) := ⟨_, rfl⟩
  have hxb : x < veblen ω i := lt_of_lt_of_le (lt_w_facts hx hx1 hs' hs'1).2.1 hb
  have hii : veblen ω i ≤ veblen ω (i + d + 1) :=
    (veblen_le_veblen_iff_right).2 (le_self_add.trans le_self_add)
  have huE : InE (veblen ω (i + d + 1)) := vz_omega_E hPi
  refine lt_w_min hx hx1 hdT hd1 hPi (hxb.trans_le hii) ?_ ?_
  · have h1 : d < veblen ω (i + d + 1) :=
      lt_of_lt_of_le (lt_of_le_of_lt le_add_self (lt_add_one _)) (right_le_veblen _ _)
    exact (inE_indec huE).add_lt (hsb.trans_le hii) h1
  · intro σ hσ
    have hσT : σ ∈ Tset x := vz_T_down hx hx1 hdT hd1 hσ.le
    rcases lt_or_ge σ s' with hσs | hsσ
    · exact ((ltn_mono hx hx1 hσT hs' hs'1 hs'K hσs).trans_le hb).trans_le hii
    · have hσe : s' + (σ - s') = σ := Ordinal.add_sub_cancel_of_le hsσ
      have hd'd : σ - s' < d := (add_lt_add_iff_left s').1 (by rw [hσe]; exact hσ)
      have h2 := IHd _ hd'd (by rw [hσe]; exact hσT) (by rw [hσe]; exact hσ.trans hd1)
      rw [hσe] at h2
      refine lt_of_le_of_lt h2 ((veblen_lt_veblen_iff_right).2 ?_)
      rw [add_assoc, add_assoc]
      exact (add_lt_add_iff_left i).2 ((add_one_le_of_lt hd'd).trans_lt (lt_add_one d))

end Base

end Googology.Trans.PoR.InaccPsi.R2.Lt
