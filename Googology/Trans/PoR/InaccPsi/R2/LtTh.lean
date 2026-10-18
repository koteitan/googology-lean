import Googology.Trans.PoR.InaccPsi.R2.LtOm

/-!
# The level `ω` of `ϑˣ(Ω₁·ω + η)` for arguments `η < y_ω(x)`

For a base `x ∈ E ∩ Ω₁` and `η ∈ Tˣ ∩ Ω₁` (`P_ω = range φ(ω, ·)`), from [W07a] Lemma 3.30 at `Ω₁·ω + η` (the cited
facts of `R2.CitedLz`), Convention 4.1 (`vzRem_T`), and the cited value `ltLhT_w_lim` (`R2.CitedLt`):

* `lt_w_self` (**`η < ϑˣ(Ω₁·ω + η)` for `η < y_ω(x)`**: `η < y_k(x) = ϑˣ(Ω₁·ω + k)` and `k < η` or `η` finite),
  `lt_w_mono`, `lt_w_mono_le` (monotone in `η < y_ω(x)`);
* `lt_w_omega` (**`ϑˣ(Ω₁·ω + η) ∈ P_ω`**), `lt_w_min` (**minimality**: every `u ∈ P_ω` above `x`, above `η` and above
  every `ϑˣ(Ω₁·ω + σ)`, `σ < η`, is `≥ ϑˣ(Ω₁·ω + η)`), `lt_w_ub` (**`ϑˣ(Ω₁·ω + s' + d) ≤ φ_ω(i + d + 1)`** whenever
  `ϑˣ(Ω₁·ω + s') ≤ φ_ω(i)`, `s' < φ_ω(i)`, `s' < y_ω(x)`);
* `lt_w_lh0`, `lt_w_lh` (**the `R₁⁺`-reach**: `lh(ϑˣ(Ω₁·ω)) = ϑˣ(Ω₁·ω)·ω`, and for `0 < η < y_ω(x)`,
  `lh(ϑˣ(Ω₁·ω + η)) = ϑˣ(Ω₁·ω + η)·ω + logend(η)`), `lt_w_le1R` (`ϑˣ(Ω₁·ω + η) ≤₁ ϑˣ(Ω₁·ω + η)·ω`).
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Lt

open Ordinal Order Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Xt
  Googology.Trans.PoR.InaccPsi.R2.Lz

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

/-- **`η < ϑˣ(Ω₁·ω + η)` for `η < y_ω(x)`.** -/
theorem lt_w_self {η : Ordinal.{0}} (hη : η ∈ Tset x) (hη1 : η < Om1) (hηw : η < lzYw x) :
    η < vt x (Om1 * ω + η) := by
  obtain ⟨k, hk⟩ := lzYw_lt_iff.1 hηw
  have hvE := (lt_w_facts hx hx1 hη hη1).2.2.2.1
  rcases lt_or_ge (k : Ordinal.{0}) η with hkη | hηk
  · exact hk.trans (lzVt_lt_ww hx hx1 (lz_natT hx hx1 k).1 hη hη1 hkη
      ((natCast_lt_omega0 k).trans (omega0_lt_inE hvE)))
  · exact lt_of_le_of_lt hηk ((natCast_lt_omega0 k).trans (omega0_lt_inE hvE))

/-- `η ↦ ϑˣ(Ω₁·ω + η)` is strictly increasing below `y_ω(x)`. -/
theorem lt_w_mono {σ η : Ordinal.{0}} (hσ : σ ∈ Tset x) (hη : η ∈ Tset x) (hη1 : η < Om1)
    (hηw : η < lzYw x) (h : σ < η) : vt x (Om1 * ω + σ) < vt x (Om1 * ω + η) :=
  lzVt_lt_ww hx hx1 hσ hη hη1 h (h.trans (lt_w_self hx hx1 hη hη1 hηw))

theorem lt_w_mono_le {σ η : Ordinal.{0}} (hσ : σ ∈ Tset x) (hη : η ∈ Tset x) (hη1 : η < Om1)
    (hηw : η < lzYw x) (h : σ ≤ η) : vt x (Om1 * ω + σ) ≤ vt x (Om1 * ω + η) := by
  rcases h.lt_or_eq with h | rfl
  · exact (lt_w_mono hx hx1 hσ hη hη1 hηw h).le
  · exact le_rfl

/-- **`ϑˣ(Ω₁·ω + η)` is a value of `φ(ω, ·)`.** -/
theorem lt_w_omega {η : Ordinal.{0}} (hη : η ∈ Tset x) (hη1 : η < Om1) :
    vt x (Om1 * ω + η) ∈ Set.range (veblen ω) := by
  obtain ⟨hvT, -, hv1, hvE, -⟩ := lt_w_facts hx hx1 hη hη1
  refine (mem_range_veblen omega0_ne_zero).2 (fun b hb => ?_)
  obtain ⟨n, rfl⟩ := lt_omega0.1 hb
  refine le_antisymm ?_ (right_le_veblen _ _)
  rw [(isNormal_veblen _).apply_of_isSuccLimit (ev_isSuccLimit_of_inE hvE)]
  refine Ordinal.iSup_le (fun j => ?_)
  have hj1 : j.1 < Om1 := j.2.trans hv1
  have hjT : j.1 ∈ Tset x := vz_T_down hx hx1 hvT hv1 j.2.le
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.cast_zero, veblen_zero_apply]
    exact (hvE.opow_lt j.2).le
  · exact ((lz_veblen_le_th hx hx1 hn j.1 hjT hj1).trans_lt
      (lzVt_lt_w hx hx1 hjT hj1 hη hη1 j.2)).le

/-- **Minimality at level `ω`.** -/
theorem lt_w_min {η u : Ordinal.{0}} (hη : η ∈ Tset x) (hη1 : η < Om1) (hPu : u ∈ Set.range (veblen ω))
    (hxu : x < u) (hηu : η < u) (hprev : ∀ σ, σ < η → vt x (Om1 * ω + σ) < u) :
    vt x (Om1 * ω + η) ≤ u := by
  by_contra hlt
  push Not at hlt
  obtain ⟨haT, -, ha1, -, -⟩ := lt_w_facts hx hx1 hη hη1
  have hu1 : u < Om1 := hlt.trans ha1
  have huT : u ∈ Tset x := vz_T_down hx hx1 haT ha1 hlt.le
  have huE : InE u := vz_omega_E hPu
  obtain ⟨ξ, hξT, hξ2, hξu⟩ := vt_rep hx hx1 huT hxu.le hu1 (inE_indec huE)
  have hΩξ : Om1 ≤ ξ := (vt_E_iff hx hx1 hξT hξ2).1 ⟨by rw [hξu]; exact hxu, by rw [hξu]; exact huE⟩
  have hξlt : ξ < Om1 * ω + η :=
    lzLt_of_vt_lt_ww hx hx1 hξT hξ2 hη hη1 (by rw [hξu]; exact hηu) (by rw [hξu]; exact hlt)
  rcases lt_or_ge ξ (Om1 * ω) with hξω | hωξ
  · obtain ⟨hdec, hr1⟩ := vz_div_Om1 ξ
    set q := ξ / Om1 with hq
    set r := ξ % Om1 with hr
    have hqw : q < ω := by
      have h1 : Om1 * q < Om1 * ω := lt_of_le_of_lt (hdec ▸ le_self_add) hξω
      exact (mul_lt_mul_iff_right₀ (Ordinal.omega_pos 1)).1 h1
    obtain ⟨q', hq'⟩ := lt_omega0.1 hqw
    have hq'1 : 1 ≤ q' := by
      rcases Nat.eq_zero_or_pos q' with h0 | h0
      · exfalso
        rw [h0, Nat.cast_zero] at hq'
        rw [hq', mul_zero, zero_add] at hdec
        exact absurd (hdec ▸ hr1) (not_lt.2 hΩξ)
      · exact h0
    have hrT : r ∈ Tset x := vzRem_T hx hx1 hξT hξ2 hdec.symm (dvd_mul_right _ _) hr1
    have e : Om1 * (q' : Ordinal.{0}) + r = ξ := by rw [← hq']; exact hdec
    have hnot := vz_th_notP hx hx1 hq'1 hrT hr1
    rw [e, hξu] at hnot
    exact hnot (vz_omega_P hPu q')
  · have hξe : Om1 * ω + (ξ - Om1 * ω) = ξ := Ordinal.add_sub_cancel_of_le hωξ
    have hrη : ξ - Om1 * ω < η := (add_lt_add_iff_left _).1 (by rw [hξe]; exact hξlt)
    have := hprev _ hrη
    rw [hξe, hξu] at this
    exact lt_irrefl _ this

/-- **The upper bound by `φ_ω`**: if `ϑˣ(Ω₁·ω + s') ≤ φ_ω(i)`, `s' < φ_ω(i)` and `s' < y_ω(x)`, then
`ϑˣ(Ω₁·ω + s' + d) ≤ φ_ω(i + d + 1)` for every `d` with `s' + d ∈ Tˣ ∩ Ω₁`. -/
theorem lt_w_ub {s' i : Ordinal.{0}} (hs' : s' ∈ Tset x) (hs'1 : s' < Om1) (hs'w : s' < lzYw x)
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
    · exact ((lt_w_mono hx hx1 hσT hs' hs'1 hs'w hσs).trans_le hb).trans_le hii
    · have hσe : s' + (σ - s') = σ := Ordinal.add_sub_cancel_of_le hsσ
      have hd'd : σ - s' < d := (add_lt_add_iff_left s').1 (by rw [hσe]; exact hσ)
      have h2 := IHd _ hd'd (by rw [hσe]; exact hσT) (by rw [hσe]; exact hσ.trans hd1)
      rw [hσe] at h2
      refine lt_of_le_of_lt h2 ((veblen_lt_veblen_iff_right).2 ?_)
      rw [add_assoc, add_assoc]
      exact (add_lt_add_iff_left i).2 ((add_one_le_of_lt hd'd).trans_lt (lt_add_one d))

/-- **The `R₁⁺`-reach of `ϑˣ(Ω₁·ω) = B(x)`**: `lh = ϑˣ(Ω₁·ω)·ω`. -/
theorem lt_w_lh0 : IsLh1 (vt x (Om1 * ω + 0)) (vt x (Om1 * ω + 0) * ω) := by
  rw [add_zero, vz_vt_w_eq hx hx1]; exact vz_lh_B hx hx1

/-- **The `R₁⁺`-reach of `ϑˣ(Ω₁·ω + η)` for `0 < η < y_ω(x)`**: `lh = ϑˣ(Ω₁·ω + η)·ω + logend(η)`. -/
theorem lt_w_lh {η : Ordinal.{0}} (hη : η ∈ Tset x) (hη1 : η < Om1) (hη0 : η ≠ 0) (hηw : η < lzYw x) :
    IsLh1 (vt x (Om1 * ω + η)) (vt x (Om1 * ω + η) * ω + lg η) := by
  obtain ⟨hvT, hxv, hv1, -, hvP⟩ := lt_w_facts hx hx1 hη hη1
  have hlim : ∃ σ, σ < η ∧ η < vt x (Om1 * ω + σ) := by
    obtain ⟨k, hk⟩ := lzYw_lt_iff.1 hηw
    rcases lt_or_ge (k : Ordinal.{0}) η with hkη | hηk
    · exact ⟨k, hkη, hk⟩
    · refine ⟨0, pos_iff_ne_zero.2 hη0, ?_⟩
      have hE := (lt_w_facts hx hx1 (mem_T_of_le hx hx1 (zero_le : (0 : Ordinal.{0}) ≤ x))
        (Ordinal.omega_pos 1)).2.2.2.1
      exact lt_of_le_of_lt hηk ((natCast_lt_omega0 k).trans (omega0_lt_inE hE))
  have h := lh_eq_lhT (Or.inr hx) hx1 hvT hxv hv1 hvP
  rwa [ltLhT_w_lim hx hx1 hη hη1 hη0 (lt_w_self hx hx1 hη hη1 hηw) hlim] at h

/-- `ϑˣ(Ω₁·ω + η) ≤₁ ϑˣ(Ω₁·ω + η)·ω` in `R₁⁺` for `η < y_ω(x)`. -/
theorem lt_w_le1R {η : Ordinal.{0}} (hη : η ∈ Tset x) (hη1 : η < Om1) (hηw : η < lzYw x) :
    le1R (vt x (Om1 * ω + η)) (vt x (Om1 * ω + η) * ω) := by
  rcases eq_or_ne η 0 with rfl | hη0
  · exact (lt_w_lh0 hx hx1).1
  · exact lt_le1R_w_base (lt_w_lh hx hx1 hη hη1 hη0 hηw).1

end Base

end Googology.Trans.PoR.InaccPsi.R2.Lt
