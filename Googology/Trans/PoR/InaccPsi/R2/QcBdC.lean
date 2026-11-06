import Googology.Trans.PoR.InaccPsi.R2.QcBd

/-!
# QcBdC: THE BOUND `QcBd` IS CLOSED UNDER `+` AND `σ ↦ ϑˣ(Ω₁·Ω₁ + σ)`

* `qc_vt_mono` (**`ϑˣ(Ω₁·N) ≤ ϑˣ(Ω₁·N')`** for levels `N ≤ N'` with data below `x`; [W07a] Lemma 3.30 through
  `rjVt_lt`), `qcBd_up` (the level can be raised to `N ≥ Ω₁·2`), `qcBd_add` (**closed under `+`**), `qcBd_gq`
  (**closed under `σ ↦ gq σ x = ϑˣ(Ω₁·Ω₁ + σ)`**).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rj Googology.Trans.PoR.InaccPsi.R2.Gb

section Bd

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

/-- **`ϑˣ(Ω₁·N) ≤ ϑˣ(Ω₁·N')`** for levels `Ω₁ ≤ N ≤ N' < ε_{Ω₁+1}` with data below `x`. -/
theorem qc_vt_mono {N N' : Ordinal.{0}} (hN1 : Om1 ≤ N) (hNE : N < ggE) (hNx : rjDat N < x) (hN'E : N' < ggE)
    (hN'x : rjDat N' < x) (h : N ≤ N') : vt x (Om1 * N) ≤ vt x (Om1 * N') := by
  rcases h.lt_or_eq with hlt | rfl
  · have h0T : (0 : Ordinal.{0}) ∈ Tset x := mem_T_of_le hx hx1 zero_le
    have h0Ω : (0 : Ordinal.{0}) < Om1 := hx.pos.trans hx1
    have hN'1 : Om1 ≤ N' := hN1.trans hlt.le
    obtain ⟨hT', -⟩ := qc_bd_pt hx hx1 hN'1 hN'E hN'x
    have hpos : x ≤ vt x (Om1 * N') := by
      have hargT := rjArg_mem hx hx1 hN'1 hN'E (mem_T_of_le hx hx1 hN'x.le) h0T h0Ω
      rw [add_zero] at hargT
      exact (vt_memTwo hx hx1 hargT (by simpa using qc_arg_lt hN'E h0Ω)).2.1
    have h := rjVt_lt hx hx1 hNE (mem_T_of_le hx hx1 hNx.le) h0T h0Ω hN'1 hN'E (mem_T_of_le hx hx1 hN'x.le) h0T
      h0Ω (by rw [add_zero, add_zero]; exact (mul_lt_mul_iff_right₀ rj_Om1_pos).2 hlt)
      (by rw [add_zero]; exact hNx.trans_le hpos) (by rw [add_zero]; exact hx.pos.trans_le hpos)
    rw [add_zero, add_zero] at h
    exact h.le
  · exact le_rfl

omit hx hx1 in
theorem qc_O2_facts : Om1 ≤ Om1 * 2 ∧ Om1 * 2 < ggE ∧ rjDat (Om1 * 2) ≤ 2 := by
  have hgE : InE ggE := ggE_spec.1
  refine ⟨le_mul_of_one_le_right' (by norm_num), hgE.mul_lt (by rw [rj_Om1]; exact ggE_spec.2)
    ((natCast_lt_omega0 2).trans (omega0_lt_inE hgE)), ?_⟩
  have h2Ω : (2 : Ordinal.{0}) < Om1 := by
    have := (natCast_lt_omega0 2).trans (omega0_lt_inE (Low.opow_eq_self_of_SC qc_Om1_SC))
    exact_mod_cast this
  have := rjDat_OmL (β := 0) rj_Om1_pos 2 h2Ω
  rwa [add_zero, max_eq_left zero_le] at this

omit hx1 in
theorem qc_two_lt : (2 : Ordinal.{0}) < x := by
  have := natCast_lt_omega0 2
  exact_mod_cast this.trans (omega0_lt_inE hx)

/-- **The level can be raised to one `≥ Ω₁·2`.** -/
theorem qcBd_up {v : Ordinal.{0}} (h : QcBd x v) :
    ∃ N, Om1 * 2 ≤ N ∧ N < ggE ∧ rjDat N < x ∧ v < vt x (Om1 * N) := by
  obtain ⟨N, h1, h2, h3, h4⟩ := h
  obtain ⟨o1, o2, o3⟩ := qc_O2_facts
  have hd2 : rjDat (Om1 * 2) < x := o3.trans_lt (qc_two_lt hx)
  rcases le_total N (Om1 * 2) with hle | hle
  · exact ⟨Om1 * 2, le_rfl, o2, hd2, h4.trans_le (qc_vt_mono hx hx1 h1 h2 h3 o2 hd2 hle)⟩
  · exact ⟨N, hle, h2, h3, h4⟩

/-- **`QcBd` is closed under `+`.** -/
theorem qcBd_add {a b : Ordinal.{0}} (ha : QcBd x a) (hb : QcBd x b) : QcBd x (a + b) := by
  obtain ⟨N, h1, h2, h3, h4⟩ := ha
  obtain ⟨N', h1', h2', h3', h4'⟩ := hb
  have hI : ∀ M, Om1 ≤ M → M < ggE → rjDat M < x → Indec (vt x (Om1 * M)) := fun M hM1 hME hMx => by
    have h0T : (0 : Ordinal.{0}) ∈ Tset x := mem_T_of_le hx hx1 zero_le
    have h0Ω : (0 : Ordinal.{0}) < Om1 := hx.pos.trans hx1
    have hargT := rjArg_mem hx hx1 hM1 hME (mem_T_of_le hx hx1 hMx.le) h0T h0Ω
    rw [add_zero] at hargT
    exact (vt_memTwo hx hx1 hargT (by simpa using qc_arg_lt hME h0Ω)).2.2.2.1
  rcases le_total N N' with hle | hle
  · exact ⟨N', h1', h2', h3', (hI N' h1' h2' h3').add_lt (h4.trans_le (qc_vt_mono hx hx1 h1 h2 h3 h2' h3' hle)) h4'⟩
  · exact ⟨N, h1, h2, h3, (hI N h1 h2 h3).add_lt h4 (h4'.trans_le (qc_vt_mono hx hx1 h1' h2' h3' h2 h3 hle))⟩

/-- **`QcBd` is closed under `σ ↦ ϑˣ(Ω₁·Ω₁ + σ)`.** -/
theorem qcBd_gq {σ : Ordinal.{0}} (hσT : σ ∈ Tset x) (h : QcBd x σ) : QcBd x (gq σ x) := by
  obtain ⟨N, hN2, hNE, hNx, hσN⟩ := qcBd_up hx hx1 h
  obtain ⟨o1, -, -⟩ := qc_O2_facts
  have hN1 : Om1 ≤ N := o1.trans hN2
  have hσ1 : σ < Om1 := hσN.trans (qc_bd_pt hx hx1 hN1 hNE hNx).2
  have h0T : (0 : Ordinal.{0}) ∈ Tset x := mem_T_of_le hx hx1 zero_le
  have h0Ω : (0 : Ordinal.{0}) < Om1 := hx.pos.trans hx1
  have hO1E : Om1 < ggE := by rw [rj_Om1]; exact ggE_spec.2
  have harg : Om1 * Om1 + σ < Om1 * N + 0 := by
    rw [add_zero]
    calc Om1 * Om1 + σ < Om1 * Om1 + Om1 := (add_lt_add_iff_left _).2 hσ1
      _ = Om1 * (Om1 + 1) := (mul_add_one _ _).symm
      _ < Om1 * (Om1 * 2) := (mul_lt_mul_iff_right₀ rj_Om1_pos).2 (by
          rw [show (Om1 : Ordinal.{0}) * 2 = Om1 + Om1 by
            rw [show (2 : Ordinal.{0}) = 1 + 1 by norm_num, mul_add, mul_one]]
          exact (add_lt_add_iff_left _).2 (Lu.lu_one_lt_E (Low.opow_eq_self_of_SC qc_Om1_SC)))
      _ ≤ Om1 * N := mul_le_mul_right hN2 _
  have hpos : x ≤ vt x (Om1 * N + 0) := by
    have hargT := rjArg_mem hx hx1 hN1 hNE (mem_T_of_le hx hx1 hNx.le) h0T h0Ω
    exact (vt_memTwo hx hx1 hargT (qc_arg_lt hNE h0Ω)).2.1
  have hd0 : rjDat Om1 < vt x (Om1 * N + 0) := by rw [rjDat_Om1]; exact hx.pos.trans_le hpos
  have h1 := rjVt_lt hx hx1 hO1E (by rw [rjDat_Om1]; exact h0T) hσT hσ1 hN1 hNE (mem_T_of_le hx hx1 hNx.le)
    h0T h0Ω harg hd0 (by rw [add_zero]; exact hσN)
  refine ⟨N, hN1, hNE, hNx, ?_⟩
  rw [add_zero] at h1
  exact h1

end Bd

end Googology.Trans.PoR.InaccPsi.R2.Qc
