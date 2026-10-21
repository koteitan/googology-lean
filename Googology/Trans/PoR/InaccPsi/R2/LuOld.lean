import Googology.Trans.PoR.InaccPsi.R2.LuTh

/-!
# The per-level cited axioms as corollaries of `R2.CitedLu`

Every per-level axiom of [W07a] Lemma 3.30 and [W07b] Def 4.1 in `R2.CitedEv` (`Ω₁ + η`), `R2.CitedVz` (`Ω₁·n + η`,
`Ω₁·ω`), `R2.CitedLz` (`Ω₁·ω + η`), `R2.CitedLt` (`Ω₁·ω + η`, `Ω₁·(ω+1)`), `R2.CitedXt` and `R2.Cited` (the base change
of `Ω₁·ω`, `Ω₁`) is proved here, with the same statement, from the axioms of `R2.CitedLu` (the general level `β`) and
the level-free axioms (`vt_memTwo`, `vt_E_iff`, `vzRem_T`, `vzT_add`, `lh_eq_lhT`, `le1R_thm22`, `le1R_two_iff`,
`T_inter_Om1`, …).  The old axioms are not deleted; `#print axioms` of each theorem below shows that it does not use
the axiom whose statement it proves.

`Om1_add_T` itself is now a theorem of `R2.CitedEv` (both clauses; here only its membership half is
`luOld_Om1_add_T_mem`).  Not covered: the axioms that are not facts of Lemma 3.30 / Def 4.1 (`vt_Om1_mem`,
`vt_Om1_succ` of `R2.CitedEps`; `vzT_add`, `vzRem_T`, which are level-free and used as they are).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Lu

open Ordinal Order Googology.Trans.PoR.InaccPsi.R2

theorem lu_log_omega : log ω (ω : Ordinal.{0}) = 1 := by
  have := log_opow one_lt_omega0 (1 : Ordinal.{0}); rwa [opow_one] at this

theorem lu_log_omega_one : log ω ((ω : Ordinal.{0}) + 1) = 1 := by
  refine (log_eq_iff one_lt_omega0 (lt_of_lt_of_le omega0_pos le_self_add).ne' 1).2 ⟨?_, ?_⟩
  · rw [opow_one]; exact le_self_add
  · rw [opow_add, opow_one]
    calc (ω : Ordinal.{0}) + 1 < ω + ω := (add_lt_add_iff_left _).2 one_lt_omega0
      _ = ω * 2 := (mul_two_eq _).symm
      _ < ω * ω := (mul_lt_mul_iff_right₀ omega0_pos).2 (by exact_mod_cast natCast_lt_omega0 2)

theorem lu_lg_one : lg (1 : Ordinal.{0}) = 0 := by
  have := lg_nat (n := 1) one_ne_zero; rwa [Nat.cast_one] at this

/-- `lhᵗ(α·ω) = α·ω` for `α = ϑᵗ(Ω₁·β + η)`, `1 ≤ β < τ`. -/
theorem lu_lhT_mul_omega {τ β η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hβ1 : 1 ≤ β) (hβ : β < τ)
    (hη : η ∈ Tset τ) (hη1 : η < Om1) :
    lhT τ (vt τ (Om1 * β + η) * ω) = vt τ (Om1 * β + η) * ω := by
  obtain ⟨-, -, hvT, hxv, hv1, hvE, -, -⟩ := lu_th_facts hτ hτ1 hβ1 hβ hη hη1
  have h := (lu_lhT_mul_opow hτ hτ1 hvT hxv hv1 hvE le_rfl (lu_one_lt_E hvE)).2
  rwa [opow_one, lu_lg_one, add_zero] at h

/-! ## `R2.CitedEv` (level `1`) -/

theorem lu_one_cast (η : Ordinal.{0}) : Om1 * 1 + η = Om1 + η := by rw [mul_one]

/-- The membership half of `Om1_add_T`. -/
theorem luOld_Om1_add_T_mem {τ η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hη : η ∈ Tset τ) :
    Om1 + η ∈ Tset τ := by
  rw [← lu_one_cast]; exact luOm1_mul_add_T hτ hτ1 (lu_one_lt_E hτ).le hη

/-- `vt_lt_Om1_add`. -/
theorem luOld_vt_lt_Om1_add {τ ξ η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hξ : ξ ∈ Tset τ)
    (hξ2 : ξ < OmTwo) (hη : η ∈ Tset τ) (hη1 : η < Om1) (hηξ : η < vt τ ξ)
    (h : vt τ ξ < vt τ (Om1 + η)) : ξ < Om1 + η := by
  rw [← lu_one_cast] at h ⊢
  exact luLt_of_vt_lt hτ hτ1 hξ hξ2 (lu_one_lt_E hτ) hη hη1 hηξ h

/-- `vt_Om1_add_lt`. -/
theorem luOld_vt_Om1_add_lt {τ η' η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hη' : η' ∈ Tset τ)
    (hη : η ∈ Tset τ) (hη1 : η < Om1) (hη'η : η' < η) (h : η' < vt τ (Om1 + η)) :
    vt τ (Om1 + η') < vt τ (Om1 + η) := by
  have h' : η' < vt τ (Om1 * 1 + η) := by rw [lu_one_cast]; exact h
  have := luVt_lt hτ hτ1 (lu_one_lt_E hτ) hη' (hη'η.trans hη1) (lu_one_lt_E hτ) hη hη1
    ((add_lt_add_iff_left _).2 hη'η) h'
  rwa [lu_one_cast, lu_one_cast] at this

/-- `lt_vt_Om1_add`. -/
theorem luOld_lt_vt_Om1_add {τ η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hη : η ∈ Tset τ) (hη1 : η < Om1) :
    η < vt τ (Om1 + η) := by
  rw [← lu_one_cast]; exact luLt_vt_self hτ hτ1 le_rfl (lu_one_lt_E hτ) hη hη1

/-- `lhT_Om1_add`. -/
theorem luOld_lhT_Om1_add {τ η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hη : η ∈ Tset τ) (hη1 : η < Om1)
    (_hη0 : η ≠ 0) (hlim : ∃ σ, σ < η ∧ η < vt τ (Om1 + σ)) :
    lhT τ (vt τ (Om1 + η)) = vt τ (Om1 + η) * 2 + lg η := by
  have hlim' : ∃ σ, σ < η ∧ η < vt τ (Om1 * 1 + σ) := by
    obtain ⟨σ, h1, h2⟩ := hlim; exact ⟨σ, h1, by rw [lu_one_cast]; exact h2⟩
  have h := luLhT_fin hτ hτ1 le_rfl one_lt_omega0 hη hη1
  rw [lu_zeta_lim hlim', lu_one_cast, mul_one, ← add_assoc, ← mul_two_eq] at h
  exact h

/-! ## `R2.CitedVz` (levels `n` and `ω`) -/

/-- `vzLt_of_vt_lt`. -/
theorem luOld_vzLt_of_vt_lt {τ ξ η : Ordinal.{0}} {n : ℕ} (hτ : InE τ) (hτ1 : τ < Om1) (hξ : ξ ∈ Tset τ)
    (hξ2 : ξ < OmTwo) (hη : η ∈ Tset τ) (hη1 : η < Om1) (hηξ : η < vt τ ξ)
    (h : vt τ ξ < vt τ (Om1 * (n : Ordinal.{0}) + η)) : ξ < Om1 * (n : Ordinal.{0}) + η :=
  luLt_of_vt_lt hτ hτ1 hξ hξ2 (lu_nat_lt_E hτ n) hη hη1 hηξ h

/-- `vzVt_lt`. -/
theorem luOld_vzVt_lt {τ η' η : Ordinal.{0}} {m n : ℕ} (hτ : InE τ) (hτ1 : τ < Om1) (hη' : η' ∈ Tset τ)
    (hη'1 : η' < Om1) (hη : η ∈ Tset τ) (hη1 : η < Om1)
    (hlt : Om1 * (m : Ordinal.{0}) + η' < Om1 * (n : Ordinal.{0}) + η)
    (h : η' < vt τ (Om1 * (n : Ordinal.{0}) + η)) :
    vt τ (Om1 * (m : Ordinal.{0}) + η') < vt τ (Om1 * (n : Ordinal.{0}) + η) :=
  luVt_lt hτ hτ1 (lu_nat_lt_E hτ m) hη' hη'1 (lu_nat_lt_E hτ n) hη hη1 hlt h

theorem lu_nat_one_le {n : ℕ} (hn : 1 ≤ n) : (1 : Ordinal.{0}) ≤ (n : Ordinal.{0}) := by exact_mod_cast hn

theorem lu_one_add_nat (n : ℕ) : (1 : Ordinal.{0}) + (n : Ordinal.{0}) = ((n + 1 : ℕ) : Ordinal.{0}) := by
  rw [← Nat.cast_one, ← Nat.cast_add, add_comm 1 n]

/-- `vzLhT_fix`. -/
theorem luOld_vzLhT_fix {τ η : Ordinal.{0}} {n : ℕ} (hτ : InE τ) (hτ1 : τ < Om1) (hn : 1 ≤ n) (hη : η ∈ Tset τ)
    (hη1 : η < Om1) (hfix : ∀ σ, σ < η → vt τ (Om1 * (n : Ordinal.{0}) + σ) ≤ η) :
    lhT τ (vt τ (Om1 * (n : Ordinal.{0}) + η)) =
      vt τ (Om1 * (n : Ordinal.{0}) + η) * ((n + 1 : ℕ) : Ordinal.{0}) := by
  rw [luLhT_fin hτ hτ1 (lu_nat_one_le hn) (natCast_lt_omega0 n) hη hη1, lu_zeta_fix hfix, add_zero,
    ← mul_one_add, lu_one_add_nat]

/-- `vzLt_vt_self`. -/
theorem luOld_vzLt_vt_self {τ η : Ordinal.{0}} {n : ℕ} (hτ : InE τ) (hτ1 : τ < Om1) (hn : 1 ≤ n) (hη : η ∈ Tset τ)
    (hη1 : η < Om1) : η < vt τ (Om1 * (n : Ordinal.{0}) + η) :=
  luLt_vt_self hτ hτ1 (lu_nat_one_le hn) (lu_nat_lt_E hτ n) hη hη1

/-- `vzLhT_lim`. -/
theorem luOld_vzLhT_lim {τ η : Ordinal.{0}} {n : ℕ} (hτ : InE τ) (hτ1 : τ < Om1) (hn : 1 ≤ n) (hη : η ∈ Tset τ)
    (hη1 : η < Om1) (_hη0 : η ≠ 0) (hlim : ∃ σ, σ < η ∧ η < vt τ (Om1 * (n : Ordinal.{0}) + σ)) :
    lhT τ (vt τ (Om1 * (n : Ordinal.{0}) + η)) =
      vt τ (Om1 * (n : Ordinal.{0}) + η) * ((n + 1 : ℕ) : Ordinal.{0}) + lg η := by
  rw [luLhT_fin hτ hτ1 (lu_nat_one_le hn) (natCast_lt_omega0 n) hη hη1, lu_zeta_lim hlim, ← add_assoc,
    ← mul_one_add, lu_one_add_nat]

/-- `vzFix_level` ([W07a] Lemma 4.4 `⇒` at `Δ = Ω₁·k`), from Lemma 3.30 alone: a fixed point `η` of
`σ ↦ ϑᵗ(Ω₁·k + σ)` is an `ε`-number (a limit of the `ε`-numbers `ϑᵗ(Ω₁·k + σ)`), so its argument is `Ω₁·q + s`,
`q ≥ 1`; `q ≤ k` would give `ϑᵗ(Ω₁·k + s) < η = ϑᵗ(Ω₁·q + s) ≤ ϑᵗ(Ω₁·k + s)`. -/
theorem luOld_vzFix_level {τ η ξ : Ordinal.{0}} {k : ℕ} (hτ : InE τ) (hτ1 : τ < Om1) (hk : 1 ≤ k)
    (hη : η ∈ Tset τ) (hη1 : η < Om1) (hη0 : 0 < η)
    (hfix : ∀ σ, σ < η → vt τ (Om1 * (k : Ordinal.{0}) + σ) < η)
    (hξ : ξ ∈ Tset τ) (hξ2 : ξ < OmTwo) (hv : vt τ ξ = η) : Om1 * ((k + 1 : ℕ) : Ordinal.{0}) ≤ ξ := by
  have hk1 := lu_nat_one_le hk
  have hkτ := lu_nat_lt_E hτ k
  have hηE : InE η := by
    refine lu_inE_of_cof hη0 (fun c hc => ?_)
    have hcT : c ∈ Tset τ := vz_T_down hτ hτ1 hη hη1 hc.le
    obtain ⟨-, -, -, -, -, hE, -, hcv⟩ := lu_th_facts hτ hτ1 hk1 hkτ hcT (hc.trans hη1)
    exact ⟨_, hE, hcv, hfix c hc⟩
  have hτη : τ < η := by
    obtain ⟨-, -, -, h1, -, -, -, -⟩ := lu_th_facts hτ hτ1 hk1 hkτ (lu_zero_T hτ hτ1) (Ordinal.omega_pos 1)
    exact h1.trans (hfix 0 hη0)
  have hΩξ : Om1 ≤ ξ := (vt_E_iff hτ hτ1 hξ hξ2).1 ⟨by rw [hv]; exact hτη, by rw [hv]; exact hηE⟩
  by_contra hlt
  push Not at hlt
  obtain ⟨hq1, hsT, hs1, hdec⟩ := lu_split hτ hτ1 hξ hξ2 hΩξ
  set q := ξ / Om1 with hq
  set s := ξ % Om1 with hs
  have hqk : q ≤ (k : Ordinal.{0}) := by
    have h1 : Om1 * q < Om1 * ((k + 1 : ℕ) : Ordinal.{0}) := lt_of_le_of_lt (hdec ▸ le_self_add) hlt
    have h2 := (mul_lt_mul_iff_right₀ (Ordinal.omega_pos 1)).1 h1
    rw [Nat.cast_succ] at h2
    exact Order.lt_add_one_iff.1 h2
  have hqτ : q < τ := lt_of_le_of_lt hqk hkτ
  have hsη : s < η := by rw [← hv, ← hdec]; exact luLt_vt_self hτ hτ1 hq1 hqτ hsT hs1
  have h1 := hfix s hsη
  rcases hqk.lt_or_eq with hqk' | hqk'
  · have h2 : vt τ (Om1 * q + s) < vt τ (Om1 * (k : Ordinal.{0}) + s) :=
      lu_lev_lt hτ hτ1 hqk' hkτ hsT hs1 hsT hs1 (luLt_vt_self hτ hτ1 hk1 hkτ hsT hs1)
    rw [hdec, hv] at h2
    exact lt_irrefl _ (h1.trans h2)
  · rw [← hqk', hdec, hv] at h1
    exact lt_irrefl _ h1

/-- `vzOm1w_T`. -/
theorem luOld_vzOm1w_T {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) : Om1 * ω ∈ Tset τ := by
  have := luOm1_opow_T hτ hτ1 (lu_one_lt_E hτ).le; rwa [opow_one] at this

/-- `vzLt_of_vt_lt_w`. -/
theorem luOld_vzLt_of_vt_lt_w {τ ξ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hξ : ξ ∈ Tset τ)
    (hξ2 : ξ < OmTwo) (h : vt τ ξ < vt τ (Om1 * ω)) : ξ < Om1 * ω := by
  have h0 : (0 : Ordinal.{0}) < vt τ ξ := hτ.pos.trans_le (vt_memTwo hτ hτ1 hξ hξ2).2.1
  rw [← add_zero (Om1 * ω)] at h ⊢
  exact luLt_of_vt_lt hτ hτ1 hξ hξ2 (lu_omega_lt_E hτ) (lu_zero_T hτ hτ1) (Ordinal.omega_pos 1) h0 h

/-- `vzVt_lt_w`. -/
theorem luOld_vzVt_lt_w {τ η' : Ordinal.{0}} {m : ℕ} (hτ : InE τ) (hτ1 : τ < Om1) (hη' : η' ∈ Tset τ)
    (hη'1 : η' < Om1) (h : η' < vt τ (Om1 * ω)) :
    vt τ (Om1 * (m : Ordinal.{0}) + η') < vt τ (Om1 * ω) := by
  rw [← add_zero (Om1 * ω)] at h ⊢
  refine luVt_lt hτ hτ1 (lu_nat_lt_E hτ m) hη' hη'1 (lu_omega_lt_E hτ) (lu_zero_T hτ hτ1) (Ordinal.omega_pos 1)
    ?_ h
  calc Om1 * (m : Ordinal.{0}) + η' < Om1 * (m : Ordinal.{0}) + Om1 := (add_lt_add_iff_left _).2 hη'1
    _ = Om1 * ((m : Ordinal.{0}) + 1) := by rw [mul_add_one]
    _ ≤ Om1 * ω := mul_le_mul_right (add_one_le_of_lt (natCast_lt_omega0 m)) Om1
    _ = Om1 * ω + 0 := (add_zero _).symm

/-- `vzLhT_w`. -/
theorem luOld_vzLhT_w {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) :
    lhT τ (vt τ (Om1 * ω)) = vt τ (Om1 * ω) * ω := by
  have h := luLhT_inf hτ hτ1 le_rfl (lu_omega_lt_E hτ) (lu_zero_T hτ hτ1) (Ordinal.omega_pos 1)
  have hm := lu_lhT_mul_omega hτ hτ1 one_lt_omega0.le (lu_omega_lt_E hτ) (lu_zero_T hτ hτ1) (Ordinal.omega_pos 1)
  simp only [lu_log_omega, opow_one, lu_zeta_zero, add_zero, Ordinal.sub_self] at h hm
  rw [hm] at h
  exact h

/-! ## `R2.CitedLz` (level `ω`) -/

/-- `lzVt_lt_w`. -/
theorem luOld_lzVt_lt_w {τ η' η : Ordinal.{0}} {m : ℕ} (hτ : InE τ) (hτ1 : τ < Om1) (hη' : η' ∈ Tset τ)
    (hη'1 : η' < Om1) (hη : η ∈ Tset τ) (hη1 : η < Om1) (h : η' < vt τ (Om1 * ω + η)) :
    vt τ (Om1 * (m : Ordinal.{0}) + η') < vt τ (Om1 * ω + η) :=
  lu_lev_lt hτ hτ1 (natCast_lt_omega0 m) (lu_omega_lt_E hτ) hη' hη'1 hη hη1 h

/-- `lzVt_lt_ww`. -/
theorem luOld_lzVt_lt_ww {τ η' η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hη' : η' ∈ Tset τ)
    (hη : η ∈ Tset τ) (hη1 : η < Om1) (hlt : η' < η) (h : η' < vt τ (Om1 * ω + η)) :
    vt τ (Om1 * ω + η') < vt τ (Om1 * ω + η) :=
  luVt_lt hτ hτ1 (lu_omega_lt_E hτ) hη' (hlt.trans hη1) (lu_omega_lt_E hτ) hη hη1
    ((add_lt_add_iff_left _).2 hlt) h

/-- `lzLt_of_vt_lt_ww`. -/
theorem luOld_lzLt_of_vt_lt_ww {τ ξ η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hξ : ξ ∈ Tset τ)
    (hξ2 : ξ < OmTwo) (hη : η ∈ Tset τ) (hη1 : η < Om1) (hηξ : η < vt τ ξ)
    (h : vt τ ξ < vt τ (Om1 * ω + η)) : ξ < Om1 * ω + η :=
  luLt_of_vt_lt hτ hτ1 hξ hξ2 (lu_omega_lt_E hτ) hη hη1 hηξ h

/-! ## `R2.CitedLt` (levels `ω` and `ω + 1`) -/

/-- `ltLhT_w_lim` (the hypothesis `hself` is not needed). -/
theorem luOld_ltLhT_w_lim {τ η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hη : η ∈ Tset τ) (hη1 : η < Om1)
    (_hη0 : η ≠ 0) (_hself : η < vt τ (Om1 * ω + η)) (hlim : ∃ σ, σ < η ∧ η < vt τ (Om1 * ω + σ)) :
    lhT τ (vt τ (Om1 * ω + η)) = vt τ (Om1 * ω + η) * ω + lg η := by
  have h := luLhT_inf hτ hτ1 le_rfl (lu_omega_lt_E hτ) hη hη1
  rw [lu_log_omega, opow_one, lu_zeta_lim hlim, Ordinal.add_sub_cancel,
    lu_lhT_mul_omega hτ hτ1 one_lt_omega0.le (lu_omega_lt_E hτ) hη hη1] at h
  exact h

/-- `ltLt_vt_self_w`. -/
theorem luOld_ltLt_vt_self_w {τ η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hη : η ∈ Tset τ)
    (hη1 : η < Om1) : η < vt τ (Om1 * ω + η) :=
  luLt_vt_self hτ hτ1 one_lt_omega0.le (lu_omega_lt_E hτ) hη hη1

/-- `ltVt_lt_w1`. -/
theorem luOld_ltVt_lt_w1 {τ η' : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hη' : η' ∈ Tset τ)
    (hη'1 : η' < Om1) (h : η' < vt τ (Om1 * (ω + 1))) : vt τ (Om1 * ω + η') < vt τ (Om1 * (ω + 1)) := by
  rw [← add_zero (Om1 * (ω + 1))] at h ⊢
  exact lu_lev_lt hτ hτ1 (lt_add_one ω) (lu_omega_one_lt_E hτ) hη' hη'1 (lu_zero_T hτ hτ1)
    (Ordinal.omega_pos 1) h

/-- `ltLt_of_vt_lt_w1`. -/
theorem luOld_ltLt_of_vt_lt_w1 {τ ξ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hξ : ξ ∈ Tset τ)
    (hξ2 : ξ < OmTwo) (h : vt τ ξ < vt τ (Om1 * (ω + 1))) : ξ < Om1 * (ω + 1) := by
  have h0 : (0 : Ordinal.{0}) < vt τ ξ := hτ.pos.trans_le (vt_memTwo hτ hτ1 hξ hξ2).2.1
  rw [← add_zero (Om1 * (ω + 1))] at h ⊢
  exact luLt_of_vt_lt hτ hτ1 hξ hξ2 (lu_omega_one_lt_E hτ) (lu_zero_T hτ hτ1) (Ordinal.omega_pos 1) h0 h

/-- `ltLhT_w1`. -/
theorem luOld_ltLhT_w1 {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) :
    lhT τ (vt τ (Om1 * (ω + 1))) = vt τ (Om1 * (ω + 1)) * ω + vt τ (Om1 * (ω + 1)) := by
  have hω1 : (ω : Ordinal.{0}) ≤ ω + 1 := le_self_add
  have h := luLhT_inf hτ hτ1 hω1 (lu_omega_one_lt_E hτ) (lu_zero_T hτ hτ1) (Ordinal.omega_pos 1)
  have hm := lu_lhT_mul_omega hτ hτ1 (one_lt_omega0.le.trans hω1) (lu_omega_one_lt_E hτ) (lu_zero_T hτ hτ1)
    (Ordinal.omega_pos 1)
  simp only [add_zero] at hm
  rw [lu_log_omega_one, opow_one, lu_zeta_zero, add_zero, hm] at h
  simp only [add_zero] at h
  set α := vt τ (Om1 * (ω + 1)) with hα
  rw [show α * (ω + 1) = α * ω + α from mul_add_one α ω, Ordinal.add_sub_cancel] at h
  exact h

/-! ## `R2.CitedXt`, `R2.Cited` (the base change of `Ω₁·ω` and `Ω₁`) -/

/-- `xtOm1w_TB`. -/
theorem luOld_xtOm1w_TB {σ τ : Ordinal.{0}} (h : Bases σ τ) : Om1 * ω ∈ TB τ σ ∧ pi σ τ (Om1 * ω) = Om1 * ω := by
  have := luOm1_opow_TB h (lu_one_lt_E h.1); rwa [opow_one] at this

/-- `pi_Om1`. -/
theorem luOld_pi_Om1 {σ τ : Ordinal.{0}} (h : Bases σ τ) : Om1 ∈ TB τ σ ∧ pi σ τ Om1 = Om1 := by
  have := luOm1_opow_TB h h.1.pos; rwa [opow_zero, mul_one] at this

end Googology.Trans.PoR.InaccPsi.R2.Lu
