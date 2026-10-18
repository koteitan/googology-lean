import Googology.Trans.PoR.InaccPsi.R2.LzWS
import Googology.Trans.PoR.InaccPsi.R2.CitedLt

/-!
# The level `ω`: `y_ω(x) = ϑˣ(Ω₁·ω + ω)`, its `R₁⁺`-reach, and the `R₁⁺`-test `α ≤₁ α·ω + z`

For a base `x ∈ E ∩ Ω₁` (`y_k(x) = ϑˣ(Ω₁·ω + k)`, `y_ω(x) = sup_k y_k(x)`, `R2.LzY`, `R2.LzWS`):

* `lt_sup_range` (the supremum of a strictly increasing sequence of values of `φ_o` is a value of `φ_o`),
  `ltYw_omega` (**`y_ω(x)` is a value of `φ(ω, ·)`**), `ltYw_eq` (**`y_ω(x) = ϑˣ(Ω₁·ω + ω)`**: a smaller value
  `ϑˣ(ξ)` would have `ξ < Ω₁·ω + ω` by [W07a] Lemma 3.30 (`lzLt_of_vt_lt_ww`), so `ξ = Ω₁·q + r` (not a value of
  `φ_{q+1}`) or `ξ = Ω₁·ω + j`, `j < ω`), `ltYw_lh` (**`lh(y_ω(x)) = y_ω(x)·ω + 1`** in `R₁⁺`: [W07b] Theorem 5.3
  (`lh_eq_lhT`) with the cited value `ltLhT_w_lim` of [W07b] Def 4.1 at `η = ω`, `logend(ω) = 1`);
* `lt_B_veblen` (`B(φ_ω(i)) = φ_ω(i + 1)`), `lt_Y_veblen` (`y_0(x) = φ_ω(i₀)` gives `y_k(x) = φ_ω(i₀ + k)`),
  `ltYw_le_veblen` (`y_ω(x) ≤ φ_ω(i₀ + ω)`);
* `lt_le1R_copy_w` (**the copy of `α ≤₁ α·ω + z` below `α`**: the finite-set criterion `le1R_copy` applied to
  `{c, z'}` and `{α, α·ω, α·ω + z'}`), `lt_le1R_ge_w` (**`α ≤₁ α·ω + z`, `z < α`, `φ_ω(i) < α` give
  `φ_ω(i + ω^z) ≤ α`**; the argument of `vz_le1R_ge_of` of `R2.VzR` at the level `ω`, with `vz_le1R_omega`).

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.
[W07b] G. Wilken, "Σ₁-elementarity and Skolem hull operators", APAL 145 (2007) 162–175.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Lt

open Ordinal Order Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Xt
  Googology.Trans.PoR.InaccPsi.R2.Lz

/-- The supremum of a strictly increasing sequence of values of `φ_o` (`o ≠ 0`) is a value of `φ_o`. -/
theorem lt_sup_range {o : Ordinal.{0}} (ho : o ≠ 0) (g : ℕ → Ordinal.{0})
    (hg : ∀ k, g k ∈ Set.range (veblen o)) (hs : ∀ k, g k < g (k + 1)) :
    (⨆ k, g k) ∈ Set.range (veblen o) := by
  have hle : ∀ k, g k ≤ ⨆ k, g k := fun k => Ordinal.le_iSup g k
  have hlt : ∀ a, a < (⨆ k, g k) → ∃ k, a < g k := fun a ha => Ordinal.lt_iSup_iff.1 ha
  have hlim : IsSuccLimit (⨆ k, g k) := by
    refine Ordinal.isSuccLimit_iff.2 ⟨(lt_of_le_of_lt zero_le ((hs 0).trans_le (hle 1))).ne', ?_⟩
    refine isSuccPrelimit_of_succ_lt (fun a ha => ?_)
    obtain ⟨k, hk⟩ := hlt a ha
    exact (Order.succ_le_of_lt hk).trans_lt ((hs k).trans_le (hle (k + 1)))
  refine (mem_range_veblen ho).2 (fun b hb => le_antisymm ?_ (right_le_veblen _ _))
  rw [(isNormal_veblen b).apply_of_isSuccLimit hlim]
  refine Ordinal.iSup_le (fun j => ?_)
  obtain ⟨k, hk⟩ := hlt j.1 j.2
  have hfix : veblen b (g k) = g k := (mem_range_veblen ho).1 (hg k) b hb
  exact ((veblen_lt_veblen_iff_right).2 hk).le.trans (hfix.le.trans (hle k))

/-- `B(φ_ω(i)) = φ_ω(i + 1)`. -/
theorem lt_B_veblen {i : Ordinal.{0}} (h1 : veblen ω i < Om1) : VzB (veblen ω i) = veblen ω (i + 1) := by
  have hE : InE (veblen ω i) := vz_omega_E ⟨i, rfl⟩
  obtain ⟨hBω, hlt, hmin⟩ := vzB_omega hE h1
  refine le_antisymm (hmin _ ⟨i + 1, rfl⟩ ((veblen_lt_veblen_iff_right).2 (lt_add_one i))) ?_
  obtain ⟨j, hj⟩ := hBω
  rw [← hj] at hlt ⊢
  exact (veblen_le_veblen_iff_right).2 (add_one_le_of_lt ((veblen_lt_veblen_iff_right).1 hlt))

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem lt_w_arg {η : Ordinal.{0}} (hη : η ∈ Tset x) (hη1 : η < Om1) :
    Om1 * ω + η ∈ Tset x ∧ Om1 * ω + η < OmTwo :=
  ⟨vzT_add hx hx1 (vzOm1w_T hx hx1) hη, lz_Om1w_add_lt hη1⟩

/-- The facts on a term `ϑˣ(Ω₁·ω + η)`, `η ∈ Tˣ ∩ Ω₁`. -/
theorem lt_w_facts {η : Ordinal.{0}} (hη : η ∈ Tset x) (hη1 : η < Om1) :
    vt x (Om1 * ω + η) ∈ Tset x ∧ x < vt x (Om1 * ω + η) ∧ vt x (Om1 * ω + η) < Om1 ∧
      InE (vt x (Om1 * ω + η)) ∧ Indec (vt x (Om1 * ω + η)) := by
  obtain ⟨hT, h2⟩ := lt_w_arg hx hx1 hη hη1
  obtain ⟨hvT, -, hv1, hvP, -⟩ := vt_memTwo hx hx1 hT h2
  have hΩ : Om1 ≤ Om1 * ω + η := by
    calc Om1 = Om1 * 1 := (mul_one _).symm
      _ ≤ Om1 * ω := mul_le_mul_right one_lt_omega0.le Om1
      _ ≤ _ := le_self_add
  have hE := (vt_E_iff hx hx1 hT h2).2 hΩ
  exact ⟨hvT, hE.1, hv1, hE.2, hvP⟩

theorem lt_omega_T : (ω : Ordinal.{0}) ∈ Tset x ∧ (ω : Ordinal.{0}) < Om1 :=
  ⟨mem_T_of_le hx hx1 (omega0_lt_inE hx).le, (omega0_lt_inE hx).trans hx1⟩

/-- **`y_ω(x)` is a value of `φ(ω, ·)`.** -/
theorem ltYw_omega : lzYw x ∈ Set.range (veblen ω) :=
  lt_sup_range omega0_ne_zero (lzY x) (lzY_omega hx hx1) (fun k => lzY_strict hx hx1 (Nat.lt_succ_self k))

/-- **`y_ω(x) = ϑˣ(Ω₁·ω + ω)`.** -/
theorem ltYw_eq : lzYw x = vt x (Om1 * ω + ω) := by
  obtain ⟨hωT, hω1⟩ := lt_omega_T hx hx1
  obtain ⟨hvT, -, hv1, hvE, -⟩ := lt_w_facts hx hx1 hωT hω1
  have hk : ∀ k : ℕ, lzY x k < vt x (Om1 * ω + ω) := fun k =>
    lzVt_lt_ww hx hx1 (lz_natT hx hx1 k).1 hωT hω1 (natCast_lt_omega0 k)
      ((natCast_lt_omega0 k).trans (omega0_lt_inE hvE))
  have hle : lzYw x ≤ vt x (Om1 * ω + ω) := Ordinal.iSup_le (fun k => (hk k).le)
  refine le_antisymm hle ?_
  by_contra hlt
  push Not at hlt
  have hwω := ltYw_omega hx hx1
  have hwE : InE (lzYw x) := vz_omega_E hwω
  have hw1 : lzYw x < Om1 := hlt.trans hv1
  have hwT : lzYw x ∈ Tset x := vz_T_down hx hx1 hvT hv1 hlt.le
  have hxw : x < lzYw x := (lzY_facts hx hx1 0).2.1.trans_le (lzY_le_w x 0)
  obtain ⟨ξ, hξT, hξ2, hξw⟩ := vt_rep hx hx1 hwT hxw.le hw1 (inE_indec hwE)
  have hΩξ : Om1 ≤ ξ := (vt_E_iff hx hx1 hξT hξ2).1 ⟨by rw [hξw]; exact hxw, by rw [hξw]; exact hwE⟩
  have hξlt : ξ < Om1 * ω + ω :=
    lzLt_of_vt_lt_ww hx hx1 hξT hξ2 hωT hω1 (by rw [hξw]; exact omega0_lt_inE hwE) (by rw [hξw]; exact hlt)
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
    rw [e, hξw] at hnot
    exact hnot (vz_omega_P hwω q')
  · have hξe : Om1 * ω + (ξ - Om1 * ω) = ξ := Ordinal.add_sub_cancel_of_le hωξ
    have hjω : ξ - Om1 * ω < ω := (add_lt_add_iff_left _).1 (by rw [hξe]; exact hξlt)
    obtain ⟨j', hj'⟩ := lt_omega0.1 hjω
    have hyj : lzY x j' = lzYw x := by
      show vt x (Om1 * ω + (j' : Ordinal.{0})) = lzYw x
      rw [← hj', hξe, hξw]
    have h2 := lzY_lt_w hx hx1 j'
    rw [hyj] at h2
    exact lt_irrefl _ h2

/-- **The `R₁⁺`-reach of `y_ω(x)`**: `lh(y_ω(x)) = y_ω(x)·ω + 1` ([W07b] Theorem 5.3 through `lh_eq_lhT`, with the
cited value `ltLhT_w_lim` at `η = ω`, `logend(ω) = 1`). -/
theorem ltYw_lh : IsLh1 (lzYw x) (lzYw x * ω + 1) := by
  obtain ⟨hωT, hω1⟩ := lt_omega_T hx hx1
  obtain ⟨hvT, hxv, hv1, hvE, hvP⟩ := lt_w_facts hx hx1 hωT hω1
  have hB : vt x (Om1 * ω + 0) = VzB x := by rw [add_zero]; exact vz_vt_w_eq hx hx1
  have hlim : ∃ σ, σ < ω ∧ (ω : Ordinal.{0}) < vt x (Om1 * ω + σ) :=
    ⟨0, omega0_pos, by rw [hB]; exact omega0_lt_inE (vz_omega_E (vzB_omega hx hx1).1)⟩
  have hself : (ω : Ordinal.{0}) < vt x (Om1 * ω + ω) := omega0_lt_inE hvE
  have h := lh_eq_lhT (Or.inr hx) hx1 hvT hxv hv1 hvP
  rw [ltLhT_w_lim hx hx1 hωT hω1 omega0_ne_zero hself hlim, lg_omega] at h
  rw [ltYw_eq hx hx1]
  exact h

/-- `y_0(x) = φ_ω(i₀)` gives `y_k(x) = φ_ω(i₀ + k)`. -/
theorem lt_Y_veblen {i0 : Ordinal.{0}} (h0 : lzY x 0 = veblen ω i0) :
    ∀ k : ℕ, lzY x k = veblen ω (i0 + k) := by
  intro k
  induction k with
  | zero => rw [Nat.cast_zero, add_zero]; exact h0
  | succ k ih =>
    have h1 : veblen ω (i0 + k) < Om1 := by rw [← ih]; exact (lzY_facts hx hx1 k).2.2.1
    rw [lzY_succ hx hx1 k, ih, lt_B_veblen h1, Nat.cast_succ, add_assoc]

/-- `y_0(x) = φ_ω(i₀)` gives `y_ω(x) ≤ φ_ω(i₀ + ω)`. -/
theorem ltYw_le_veblen {i0 : Ordinal.{0}} (h0 : lzY x 0 = veblen ω i0) : lzYw x ≤ veblen ω (i0 + ω) :=
  Ordinal.iSup_le fun k => by
    rw [lt_Y_veblen hx hx1 h0 k]
    exact (veblen_le_veblen_iff_right).2 (add_le_add le_rfl (natCast_lt_omega0 k).le)

end Base

/-! ## The `R₁⁺`-test `α ≤₁ α·ω + z` -/

theorem lt_le_mul_w (a : Ordinal.{0}) : a ≤ a * ω := by
  calc a = a * 1 := (mul_one a).symm
    _ ≤ a * ω := mul_le_mul_right one_lt_omega0.le a

/-- **The copy below `α`**: if `α ≤₁ α·ω + z` and `z' < z`, `z' < α`, `c < α`, there is `e ∈ (c, α)` with
`e ≤₁ e·ω + z'`. -/
theorem lt_le1R_copy_w {a z z' c : Ordinal.{0}} (h : le1R a (a * ω + z)) (hz : z' < z) (hz'a : z' < a)
    (hca : c < a) : ∃ e, c < e ∧ e < a ∧ le1R e (e * ω + z') := by
  classical
  have haω := lt_le_mul_w a
  have hbz : a * ω + z' + 1 ≤ a * ω + z := by
    rw [add_assoc]; exact add_le_add le_rfl (add_one_le_of_lt hz)
  have hab : a ≤ a * ω + z' + 1 := haω.trans (le_self_add.trans le_self_add)
  have hle : le1R a (a * ω + z' + 1) := le1R_of_le hab hbz h
  have hle' : le1R a (a * ω + z') := le1R_of_le (haω.trans le_self_add) le_self_add hle
  have hXa : ∀ x ∈ ({c, z'} : Finset Ordinal.{0}), x < a := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hca
    · exact hz'a
  have hYb : ∀ y ∈ ({a, a * ω, a * ω + z'} : Finset Ordinal.{0}), a ≤ y ∧ y < a * ω + z' + 1 := by
    intro y hy
    have h1 : a * ω + z' < a * ω + z' + 1 := lt_add_one _
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl
    · exact ⟨le_rfl, lt_of_le_of_lt (haω.trans le_self_add) h1⟩
    · exact ⟨haω, lt_of_le_of_lt le_self_add h1⟩
    · exact ⟨haω.trans le_self_add, h1⟩
  obtain ⟨Yt, hYt, φ, hbij, hfix, hmono, hadd, h1R⟩ := le1R_copy hle _ _ hXa hYb
  have hcX : c ∈ ({c, z'} : Finset Ordinal.{0}) := by simp
  have hz'X : z' ∈ ({c, z'} : Finset Ordinal.{0}) := by simp
  have haU : a ∈ ({c, z'} : Finset Ordinal.{0}) ∪ {a, a * ω, a * ω + z'} := by simp
  have hcU : c ∈ ({c, z'} : Finset Ordinal.{0}) ∪ {a, a * ω, a * ω + z'} := by simp
  have hz'U : z' ∈ ({c, z'} : Finset Ordinal.{0}) ∪ {a, a * ω, a * ω + z'} := by simp
  have hωU : a * ω ∈ ({c, z'} : Finset Ordinal.{0}) ∪ {a, a * ω, a * ω + z'} := by simp
  have hzU : a * ω + z' ∈ ({c, z'} : Finset Ordinal.{0}) ∪ {a, a * ω, a * ω + z'} := by simp
  have himg : φ a ∈ ({c, z'} : Finset Ordinal.{0}) ∪ Yt := hbij.mapsTo (Finset.mem_coe.2 haU)
  have hea : φ a < a := by
    rcases Finset.mem_union.1 himg with hx | hy
    · exact hXa _ hx
    · exact hYt _ hy
  have hce : c < φ a := by
    have := hmono (Finset.mem_coe.2 hcU) (Finset.mem_coe.2 haU) hca
    rwa [hfix c hcX] at this
  have e1 : φ a + φ (a * ω) = φ (a * ω) :=
    (hadd a haU (a * ω) hωU (a * ω) hωU).1 (add_eq_right_iff_mul_omega0_le.2 le_rfl)
  have hge : φ a * ω ≤ φ (a * ω) := add_eq_right_iff_mul_omega0_le.1 e1
  have e2 : φ (a * ω) + φ z' = φ (a * ω + z') := (hadd _ hωU z' hz'U _ hzU).1 rfl
  have h3 := (h1R a haU _ hzU).1 hle'
  rw [← e2, hfix z' hz'X] at h3
  exact ⟨φ a, hce, hea, le1R_of_le ((lt_le_mul_w _).trans le_self_add) (add_le_add hge le_rfl) h3⟩

/-- `α ≤₁ α·ω + z` gives `α ≤₁ α·ω`. -/
theorem lt_le1R_w_base {a z : Ordinal.{0}} (h : le1R a (a * ω + z)) : le1R a (a * ω) :=
  le1R_of_le (lt_le_mul_w a) le_self_add h

/-- **The bound at level `ω`**: `α ≤₁ α·ω + z` in `R₁⁺`, `z < α`, `φ_ω(i) < α` give `φ_ω(i + ω^z) ≤ α`. -/
theorem lt_le1R_ge_w : ∀ z a i : Ordinal.{0}, z < a → veblen ω i < a →
    le1R a (a * ω + z) → veblen ω (i + ω ^ z) ≤ a := by
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro a i hza hia h
  have ha0 : 0 < a := lt_of_le_of_lt zero_le hia
  have haP := vz_le1R_omega ha0 (lt_le1R_w_base h)
  rcases eq_or_ne z 0 with rfl | hz0
  · rw [opow_zero]
    obtain ⟨j, rfl⟩ := haP
    have hij : i < j := (veblen_lt_veblen_iff_right).1 hia
    exact (veblen_le_veblen_iff_right).2 (add_one_le_of_lt hij)
  have hstep : ∀ z' < z, ∀ k : ℕ, veblen ω (i + ω ^ z' * k) < a := by
    intro z' hz' k
    induction k with
    | zero => rw [Nat.cast_zero, mul_zero, add_zero]; exact hia
    | succ k ihk =>
      have hz'a : z' < a := hz'.trans hza
      obtain ⟨e, hce, hea, he⟩ := lt_le1R_copy_w h hz' hz'a (max_lt ihk hz'a)
      have hce' : veblen ω (i + ω ^ z' * k) < e := lt_of_le_of_lt (le_max_left _ _) hce
      have hz'e : z' < e := lt_of_le_of_lt (le_max_right _ _) hce
      have := IH z' hz' e (i + ω ^ z' * k) hz'e hce' he
      rw [add_assoc, ← mul_add_one, ← Nat.cast_succ] at this
      exact lt_of_le_of_lt this hea
  refine vz_veblen_le_of_lt haP (fun d hd => ?_)
  rcases le_or_gt d i with hdi | hid
  · exact lt_of_le_of_lt ((veblen_le_veblen_iff_right).2 hdi) hia
  have hdd : i + (d - i) = d := Ordinal.add_sub_cancel_of_le hid.le
  have hd'z : d - i < ω ^ z := by
    rw [← hdd] at hd; exact (add_lt_add_iff_left i).1 hd
  have hd'0 : d - i ≠ 0 := by
    intro h0; rw [h0, add_zero] at hdd; exact lt_irrefl _ (hdd ▸ hid)
  have hz'z : log ω (d - i) < z := by
    have h1 : ω ^ log ω (d - i) ≤ d - i := opow_log_le_self ω hd'0
    exact (opow_lt_opow_iff_right one_lt_omega0).1 (lt_of_le_of_lt h1 hd'z)
  have hd'' : d - i < ω ^ (log ω (d - i) + 1) := by
    rw [← succ_eq_add_one]; exact lt_opow_succ_log_self one_lt_omega0 (d - i)
  obtain ⟨k, hk⟩ := ev_lt_opow_succ_nat hd''
  rw [← hdd]
  exact ((veblen_lt_veblen_iff_right).2 ((add_lt_add_iff_left i).2 hk)).trans (hstep _ hz'z k)

end Googology.Trans.PoR.InaccPsi.R2.Lt
