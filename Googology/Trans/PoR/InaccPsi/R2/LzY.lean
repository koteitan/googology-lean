import Googology.Trans.PoR.InaccPsi.R2.LzVB
import Googology.Trans.PoR.InaccPsi.R2.CitedLz

/-!
# The values `y_k(x) = ϑˣ(Ω₁·ω + k)` of `φ(ω, ·)`: `y_0 = B`, `y_{k+1} = B(y_k)`, EXACT, reach, IMG

For a base `x ∈ E ∩ Ω₁` and `k < ω`, `lzY x k := ϑˣ(Ω₁·ω + k)`.  From [W07a] Lemma 3.30 at `Ω₁·ω + η` (the axioms of
`R2.CitedLz`) and the cited facts of `R2.CitedEv`, `R2.CitedVz`, `R2.CitedXt`:

* `lzY_facts` (`y_k(x) ∈ Tˣ ∩ E ∩ (x, Ω₁)`), `lzY_zero` (**`y_0(x) = B(x)`**), `lzY_strict` (`k ↦ y_k(x)` increasing),
  `lzY_th_lt` (**`ϑˣ(Ω₁·n + σ) < y_k(x)` for `σ < y_k(x)`**), `lzY_omega` (**`y_k(x)` is a value of `φ(ω, ·)`**),
  `lzY_succ` (**`y_{k+1}(x) = B(y_k(x))`**: a value of `φ(ω, ·)` strictly between `y_k(x)` and `y_{k+1}(x)` would be
  `ϑˣ(ξ)` with `ξ < Ω₁·ω + k + 1`, by `lzLt_of_vt_lt_ww`), `lzY_one` (`y_1(x) = B₁(x)`);
* `lzY_pi` (**Lemma EXACT**: `y_k(ρ) ∈ Tᵖ[σ]`, `π_{σ,ρ}(y_k(ρ)) = y_k(σ)`: [W07a] Def 5.1 fourth clause `pi_vt_two`,
  `xtOm1w_TB`, `pi_add`);
* `lzY_lt_ups`, `lzY_lh` (**`lh(y_k(x)) = y_k(x)·ω`** in `R₁⁺`: `vz_lh_B` at the base `y_{k-1}(x)`), `lzY_pkg`
  (**the IMG package of `y_k`**: every covering copy `f` has `y_k(f(ρ)) ≤ f(y_k(ρ))`, by induction on `k`).

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Lz

open Ordinal Order Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Xt

/-- `y_k(x) = ϑˣ(Ω₁·ω + k)`. -/
noncomputable def lzY (x : Ordinal.{0}) (k : ℕ) : Ordinal.{0} := vt x (Om1 * ω + (k : Ordinal.{0}))

theorem lz_nat_lt_inE {x : Ordinal.{0}} (hx : InE x) (k : ℕ) : (k : Ordinal.{0}) < x :=
  (natCast_lt_omega0 k).trans (omega0_lt_inE hx)

theorem lz_Om1w_add_lt {η : Ordinal.{0}} (hη : η < Om1) : Om1 * ω + η < OmTwo :=
  isPrincipal_add_omega 2 vzOm1w_lt (hη.trans Om1_lt_OmTwo)

section Facts

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem lz_natT (k : ℕ) : (k : Ordinal.{0}) ∈ Tset x ∧ (k : Ordinal.{0}) < Om1 :=
  ⟨mem_T_of_le hx hx1 (lz_nat_lt_inE hx k).le, (lz_nat_lt_inE hx k).trans hx1⟩

theorem lzY_arg (k : ℕ) : Om1 * ω + (k : Ordinal.{0}) ∈ Tset x ∧ Om1 * ω + (k : Ordinal.{0}) < OmTwo :=
  ⟨vzT_add hx hx1 (vzOm1w_T hx hx1) (lz_natT hx hx1 k).1, lz_Om1w_add_lt (lz_natT hx hx1 k).2⟩

/-- The facts on `y_k(x)`. -/
theorem lzY_facts (k : ℕ) :
    lzY x k ∈ Tset x ∧ x < lzY x k ∧ lzY x k < Om1 ∧ InE (lzY x k) ∧ Indec (lzY x k) := by
  obtain ⟨hT, h2⟩ := lzY_arg hx hx1 k
  obtain ⟨hvT, -, hv1, hvP, -⟩ := vt_memTwo hx hx1 hT h2
  have hΩ : Om1 ≤ Om1 * ω + (k : Ordinal.{0}) := by
    calc Om1 = Om1 * 1 := (mul_one _).symm
      _ ≤ Om1 * ω := mul_le_mul_right one_lt_omega0.le Om1
      _ ≤ _ := le_self_add
  have hE := (vt_E_iff hx hx1 hT h2).2 hΩ
  exact ⟨hvT, hE.1, hv1, hE.2, hvP⟩

/-- **`y_0(x) = B(x)`.** -/
theorem lzY_zero : lzY x 0 = VzB x := by
  rw [lzY, Nat.cast_zero, add_zero]; exact vz_vt_w_eq hx hx1

/-- **`k ↦ y_k(x)` is strictly increasing.** -/
theorem lzY_strict {k K : ℕ} (h : k < K) : lzY x k < lzY x K := by
  have hk := lz_natT hx hx1 k
  have hK := lz_natT hx hx1 K
  have hkK : (k : Ordinal.{0}) < (K : Ordinal.{0}) := by exact_mod_cast h
  refine lzVt_lt_ww hx hx1 hk.1 hK.1 hK.2 hkK ?_
  exact (natCast_lt_omega0 k).trans (omega0_lt_inE (lzY_facts hx hx1 K).2.2.2.1)

theorem lzY_mono {k K : ℕ} (h : k ≤ K) : lzY x k ≤ lzY x K := by
  rcases h.lt_or_eq with h | rfl
  · exact (lzY_strict hx hx1 h).le
  · exact le_rfl

/-- **`ϑˣ(Ω₁·n + σ) < y_k(x)` for `σ ∈ Tˣ`, `σ < y_k(x)`.** -/
theorem lzY_th_lt (n : ℕ) {k : ℕ} {σ : Ordinal.{0}} (hσT : σ ∈ Tset x) (hσ : σ < lzY x k) :
    vt x (Om1 * (n : Ordinal.{0}) + σ) < lzY x k :=
  lzVt_lt_w hx hx1 hσT (hσ.trans (lzY_facts hx hx1 k).2.2.1) (lz_natT hx hx1 k).1 (lz_natT hx hx1 k).2 hσ

/-- `φ_n(j) ≤ ϑˣ(Ω₁·n + j)` for `1 ≤ n`, `j ∈ Tˣ ∩ Ω₁`. -/
theorem lz_veblen_le_th {n : ℕ} (hn : 1 ≤ n) :
    ∀ j, j ∈ Tset x → j < Om1 → veblen (n : Ordinal.{0}) j ≤ vt x (Om1 * (n : Ordinal.{0}) + j) := by
  intro j
  induction j using WellFoundedLT.induction with
  | ind j IHj =>
  intro hjT hj1
  refine vz_veblen_le_of_lt (vz_th_P hx hx1 n hn j hjT hj1) (fun d hd => ?_)
  have hdT := vz_T_down hx hx1 hjT hj1 hd.le
  exact lt_of_le_of_lt (IHj d hd hdT (hd.trans hj1)) (vz_th_lt hx hx1 hn hdT hjT hj1 hd)

/-- **`y_k(x)` is a value of `φ(ω, ·)`.** -/
theorem lzY_omega (k : ℕ) : lzY x k ∈ Set.range (veblen ω) := by
  obtain ⟨hyT, hxy, hy1, hyE, -⟩ := lzY_facts hx hx1 k
  refine (mem_range_veblen omega0_ne_zero).2 (fun b hb => ?_)
  obtain ⟨n, rfl⟩ := lt_omega0.1 hb
  refine le_antisymm ?_ (right_le_veblen _ _)
  rw [(isNormal_veblen _).apply_of_isSuccLimit (ev_isSuccLimit_of_inE hyE)]
  refine Ordinal.iSup_le (fun j => ?_)
  have hj1 : j.1 < Om1 := j.2.trans hy1
  have hjT : j.1 ∈ Tset x := vz_T_down hx hx1 hyT hy1 j.2.le
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.cast_zero, veblen_zero_apply]
    exact (hyE.opow_lt j.2).le
  · exact ((lz_veblen_le_th hx hx1 hn j.1 hjT hj1).trans_lt (lzY_th_lt hx hx1 n hjT j.2)).le

/-- **`y_{k+1}(x) = B(y_k(x))`.** -/
theorem lzY_succ (k : ℕ) : lzY x (k + 1) = VzB (lzY x k) := by
  obtain ⟨-, hxw, hw1, hwE, -⟩ := lzY_facts hx hx1 k
  obtain ⟨haT, hxa, ha1, haE, -⟩ := lzY_facts hx hx1 (k + 1)
  have hwa : lzY x k < lzY x (k + 1) := lzY_strict hx hx1 (Nat.lt_succ_self k)
  obtain ⟨hzω, hwz, -⟩ := vzB_omega hwE hw1
  refine le_antisymm ?_ ((vzB_omega hwE hw1).2.2 _ (lzY_omega hx hx1 (k + 1)) hwa)
  by_contra hlt
  push Not at hlt
  set z := VzB (lzY x k) with hz
  have hzE : InE z := vz_omega_E hzω
  have hz1 : z < Om1 := hlt.trans ha1
  have hzT : z ∈ Tset x := vz_T_down hx hx1 haT ha1 hlt.le
  have hxz : x < z := hxw.trans hwz
  obtain ⟨ξ, hξT, hξ2, hξz⟩ := vt_rep hx hx1 hzT hxz.le hz1 (inE_indec hzE)
  have hΩξ : Om1 ≤ ξ := (vt_E_iff hx hx1 hξT hξ2).1 ⟨by rw [hξz]; exact hxz, by rw [hξz]; exact hzE⟩
  have hk1 := lz_natT hx hx1 (k + 1)
  have hξlt : ξ < Om1 * ω + ((k + 1 : ℕ) : Ordinal.{0}) :=
    lzLt_of_vt_lt_ww hx hx1 hξT hξ2 hk1.1 hk1.2
      (by rw [hξz]; exact (natCast_lt_omega0 _).trans (omega0_lt_inE hzE)) (by rw [hξz]; exact hlt)
  rcases lt_or_ge ξ (Om1 * ω) with hξw | hwξ
  · obtain ⟨hdec, hr1⟩ := vz_div_Om1 ξ
    set q := ξ / Om1 with hq
    set r := ξ % Om1 with hr
    have hqw : q < ω := by
      have h1 : Om1 * q < Om1 * ω := lt_of_le_of_lt (hdec ▸ le_self_add) hξw
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
    rw [e, hξz] at hnot
    exact hnot (vz_omega_P hzω q')
  · set j := ξ - Om1 * ω with hj
    have hξe : Om1 * ω + j = ξ := Ordinal.add_sub_cancel_of_le hwξ
    have hjk : j < ((k + 1 : ℕ) : Ordinal.{0}) := (add_lt_add_iff_left _).1 (by rw [hξe]; exact hξlt)
    obtain ⟨j', hj'⟩ := lt_omega0.1 (hjk.trans (natCast_lt_omega0 _))
    have hj'k : j' ≤ k := by
      have : (j' : Ordinal.{0}) < ((k + 1 : ℕ) : Ordinal.{0}) := hj' ▸ hjk
      exact Nat.lt_succ_iff.1 (by exact_mod_cast this)
    have hzle : z ≤ lzY x k := by
      rw [← hξz, ← hξe, hj']; exact lzY_mono hx hx1 hj'k
    exact absurd hwz (not_lt.2 hzle)

/-- **`y_1(x) = B₁(x) = B(B(x))`.** -/
theorem lzY_one : lzY x 1 = VzB1 x := by
  rw [lzY_succ hx hx1 0, lzY_zero hx hx1, lzB1_eq hx hx1]

/-- **`lh(y_k(x)) = y_k(x)·ω`** in `R₁⁺`. -/
theorem lzY_lh (k : ℕ) : IsLh1 (lzY x k) (lzY x k * ω) := by
  rcases k with _ | k
  · rw [lzY_zero hx hx1]; exact vz_lh_B hx hx1
  · obtain ⟨-, -, hw1, hwE, -⟩ := lzY_facts hx hx1 k
    rw [lzY_succ hx hx1 k]; exact vz_lh_B hwE hw1

/-- `y_k(x)` lies below every `<₁ ∞`-point above `x`. -/
theorem lzY_lt_next (k : ℕ) {u : Ordinal.{0}} (hxu : x < u) (hu : LtInf1 u) : lzY x k < u := by
  obtain ⟨m, -, -, hmin, hTm, -⟩ := T_next (Or.inr hx) hx1
  obtain ⟨hyT, -, hy1, -, -⟩ := lzY_facts hx hx1 k
  exact ((hTm _ hy1).1 hyT).trans_le (hmin u hxu hu)

end Facts

/-! ## Lemma EXACT -/

/-- **Lemma EXACT for `y_k`**: `y_k(ρ) ∈ Tᵖ[σ]` and `π_{σ,ρ}(y_k(ρ)) = y_k(σ)`. -/
theorem lzY_pi {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) (k : ℕ) :
    lzY ρ k ∈ TB ρ σ ∧ pi σ ρ (lzY ρ k) = lzY σ k := by
  have hρE := hB.2.1
  have hρ1 := hB.2.2.2
  obtain ⟨hO, hpO⟩ := xtOm1w_TB hB
  have hkσ : (k : Ordinal.{0}) < σ := lz_nat_lt_inE hB.1 k
  obtain ⟨h1, h2⟩ := pi_add hB hO (mem_TB_of_lt hB hkσ)
  rw [hpO, pi_lt hB hkσ] at h2
  obtain ⟨-, hγ2⟩ := lzY_arg hρE hρ1 k
  obtain ⟨hvT, -, -, -, hvP⟩ := vt_memTwo hρE hρ1 h1.1 hγ2
  unfold lzY
  refine ⟨⟨hvT, by rw [hvP]; exact h1.2⟩, ?_⟩
  rw [pi_vt_two hB h1 hγ2, h2]

/-! ## Lemma IMG for `y_k` -/

namespace LzK

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

theorem lzY_lt_δ (k : ℕ) : lzY ρ k < δ := lzY_lt_next h.ρE h.ρ1 k h.ρδ h.next.2.1.2

/-- **The witness sets of `y_k(ρ)`**: every covering copy `f` has `y_k(f(ρ)) ≤ f(y_k(ρ))`. -/
theorem lzWitY : ∀ k : ℕ, ∃ W Z : Finset Ordinal.{0}, WZ ρ δ W Z ∧ lzY ρ k ∈ W ∧ ρ ∈ W ∧
    ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → ImgCtx ρ A f →
      lzY (f ρ) k ≤ f (lzY ρ k) := by
  classical
  have hρE := h.ρE
  have hρ1 := h.ρ1
  intro k
  induction k with
  | zero =>
    obtain ⟨hw, -, hI⟩ := xtWitB h
    refine ⟨_, ∅, hw, by rw [lzY_zero hρE hρ1]; simp, by simp, fun A f hW hZ C => ?_⟩
    have hy := upsPt_inE C.ups
    have hy1 : f ρ < Om1 := (C.low ρ C.rho).trans hρ1
    rw [lzY_zero hρE hρ1, lzY_zero hy hy1]
    exact (hI A f hW hZ C).2
  | succ k ih =>
    obtain ⟨W0, Z0, hw0, hwW, hρW, hI0⟩ := ih
    set w := lzY ρ k with hwdef
    set v := lzY ρ (k + 1) with hv
    obtain ⟨-, hρw, -, -, -⟩ := lzY_facts hρE hρ1 k
    obtain ⟨-, hρv, -, hvE, hvI⟩ := lzY_facts hρE hρ1 (k + 1)
    have hwv : w < v := lzY_strict hρE hρ1 (Nat.lt_succ_self k)
    have hvδ : v < δ := lzY_lt_δ h (k + 1)
    have hvwδ : v * ω < δ := vz_mul_omega_lt h.δE hvδ
    have hvw : v ≤ v * ω := by
      calc v = v * 1 := (mul_one _).symm
        _ ≤ v * ω := mul_le_mul_right one_lt_omega0.le v
    have hsrc : le1 v (v * ω) := (h.lowδ _ _ hρv hvwδ.le).2 (lzY_lh hρE hρ1 (k + 1)).1
    have hwI : Indec (v * ω) := by
      have e : v * ω = ω ^ (v + 1) := by
        rw [opow_add, opow_one, show ω ^ v = v from hvE]
      rw [e]; exact indec_opow _
    have w2 : WZ ρ δ (insert v W0) Z0 := hw0.insW hρv.le hvδ (Or.inl hvI)
    have w3 : WZ ρ δ (insert (v * ω) (insert v W0)) Z0 := w2.insW (hρv.le.trans hvw) hvwδ (Or.inl hwI)
    refine ⟨_, _, w3, by simp, by simp [hρW], fun A f hW hZ C => ?_⟩
    have hvA : v ∈ A := hW (by simp)
    have hvwA : v * ω ∈ A := hW (by simp)
    have hW0 : ↑W0 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
    have hwA : w ∈ A := hW0 (Finset.mem_coe.2 hwW)
    have hfw := hI0 A f hW0 hZ C
    have hy := upsPt_inE C.ups
    have hy1 : f ρ < Om1 := (C.low ρ C.rho).trans hρ1
    obtain ⟨-, -, hyw1, hywE, -⟩ := lzY_facts hy hy1 k
    have hfwv : f w < f v := C.mono hwA hvA hwv
    have hywv : lzY (f ρ) k < f v := hfw.trans_lt hfwv
    rw [lzY_succ hy hy1 k]
    have hadd : f v + f (v * ω) = f (v * ω) :=
      C.add v hvA (v * ω) hvwA (v * ω) hvwA (add_eq_right_iff_mul_omega0_le.2 le_rfl)
    have hge : f v * ω ≤ f (v * ω) := add_eq_right_iff_mul_omega0_le.1 hadd
    have himg : le1 (f v) (f (v * ω)) := C.cov1 v hvA _ hvwA hsrc
    by_cases hU : UpsPt (f v)
    · exact vzB_le_next hywE hyw1 hywv hU.2
    · have hR := (C.sk _ (C.low _ hvA) hU _).1 himg
      have hfv0 : 0 < f v := lt_of_le_of_lt zero_le hywv
      have hfvw : f v ≤ f v * ω := by
        calc f v = f v * 1 := (mul_one _).symm
          _ ≤ f v * ω := mul_le_mul_right one_lt_omega0.le (f v)
      have hR' : le1R (f v) (f v * ω) := le1R_of_le hfvw hge hR
      exact (vzB_omega hywE hyw1).2.2 (f v) (vz_le1R_omega hfv0 hR') hywv

/-- **The IMG package of `y_k`.** -/
theorem lzY_pkg (k : ℕ) : ImgPkg ρ δ (fun x => lzY x k) := by
  obtain ⟨W, Z, hw, hyW, -, hI⟩ := lzWitY h k
  exact ⟨one_le_iff_pos.2 (lzY_facts h.ρE h.ρ1 k).2.2.2.1.pos, lzY_lt_δ h k, W, Z, hw,
    Finset.mem_union_left _ hyW, hI⟩

end LzK

end Googology.Trans.PoR.InaccPsi.R2.Lz
