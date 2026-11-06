import Googology.Trans.PoR.InaccPsi.R2.QdGEq
import Googology.Trans.PoR.InaccPsi.R2.QcBdV

/-!
# QdBd: THE BOUND OF THE LAYER TOPS PAST `B₂` — BELOW A POINT OF A VEBLEN LEVEL, AND LEMMA IMG THERE AS A HYPOTHESIS

`Qc.QcBd x v` asks `v < ϑˣ(Ω₁·N)` for a level `Ω₁ ≤ N < ε_{Ω₁+1}` with its data below `x`; there Lemma IMG is a
theorem (`Qc.qc_img_bd`).  The readings `vD` of the codes in `[B₂, B₃)` are `ϑˣ(Ω₁·(Ω₁ + λ(x)) + c(x))` with Veblen
levels `λ(x) < Γ_{Ω₁+1}` (`Qd.qdLv_main`), so their bound is a point of a Veblen level:

* `QdBd x v` (**`v < ϑˣ(Ω₁·N)` for a level `Ω₁ ≤ N < Γ_{Ω₁+1}` with `tfDat N < x`**), `qdBd_of_qc` (every `QcBd`),
  `qdBd_mono`, `qd_bd_pt`, `qdBd_lt` (`v < Ω₁`), `qdBd_T` (`v ∈ Tˣ`);
* `qd_vt_mono`, `qdBd_up`, `qdBd_add` (**closed under `+`**), `qdBd_gq` (**closed under `σ ↦ ϑˣ(Ω₁·Ω₁ + σ)`**);
* `QdImgH` (**the hypothesis: Lemma IMG at every `v` with `QdBd ρ v`**, in every restart context), `qd_img_bd`.

Lemma IMG at the points of the levels `N ∈ [ε_{Ω₁+1}, Γ_{Ω₁+1})` is not proved here: the proof of `Qc.qc_img_atom`
needs the exact reach at those points ([W07b] Def 4.1 with `δ = (λ)^*` an `ε`-number, a nontrivial localization and
`cr`), which `R2.CitedRj` states only below `ε_{Ω₁+1}`, and the copy lemma `Qc.qc_copy` has no `φ` case.

No new axiom, no new definition (`QdBd`, `QdImgH` are in `R2.QcBdV`).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rj Googology.Trans.PoR.InaccPsi.R2.Gn
  Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu
  Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Yh
  Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Yw
  Googology.Trans.PoR.InaccPsi.R2.Qc

theorem qdBd_mono {x v w : Ordinal.{0}} (hwv : w ≤ v) (h : QdBd x v) : QdBd x w := by
  obtain ⟨N, h1, h2, h3, h4⟩ := h
  exact ⟨N, h1, h2, h3, hwv.trans_lt h4⟩

/-- **Every `QcBd` is a `QdBd`.** -/
theorem qdBd_of_qc {x v : Ordinal.{0}} (h : QcBd x v) : QdBd x v := by
  obtain ⟨N, h1, h2, h3, h4⟩ := h
  exact ⟨N, h1, h2.trans_le ggE_le_ggGam, by rw [Tf.tfDat_eq_rj N h2]; exact h3, h4⟩

section Bd

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem qdBd_T {v : Ordinal.{0}} (h : QdBd x v) : v ∈ Tset x := by
  obtain ⟨N, h1, h2, h3, h4⟩ := h
  obtain ⟨hT, h1', -, -⟩ := qd_bd_pt hx hx1 h1 h2 h3
  exact vz_T_down hx hx1 hT h1' h4.le

/-- **`ϑˣ(Ω₁·N) ≤ ϑˣ(Ω₁·N')`** for Veblen levels `Ω₁ ≤ N ≤ N'` with data below `x`. -/
theorem qd_vt_mono {N N' : Ordinal.{0}} (hN1 : Om1 ≤ N) (hNx : Tf.tfDat N < x) (hN'G : N' < ggGam)
    (hN'x : Tf.tfDat N' < x) (h : N ≤ N') : vt x (Om1 * N) ≤ vt x (Om1 * N') := by
  rcases h.lt_or_eq with hlt | rfl
  · have h0T : (0 : Ordinal.{0}) ∈ Tset x := mem_T_of_le hx hx1 zero_le
    have h0Ω : (0 : Ordinal.{0}) < Om1 := hx.pos.trans hx1
    have hN'1 : Om1 ≤ N' := hN1.trans hlt.le
    obtain ⟨-, -, hpos, -⟩ := qd_bd_pt hx hx1 hN'1 hN'G hN'x
    have h := tfVt_lt hx hx1 hN'1 (hN'G.trans Tf.tf_gg_lt_BG) hlt.le (mem_T_of_le hx hx1 hNx.le) h0T h0Ω
      (mem_T_of_le hx hx1 hN'x.le) h0T h0Ω
      (by rw [add_zero, add_zero]; exact (mul_lt_mul_iff_right₀ rj_Om1_pos).2 hlt)
      (by rw [add_zero]; exact hNx.trans_le hpos) (by rw [add_zero]; exact hx.pos.trans_le hpos)
    rw [add_zero, add_zero] at h
    exact h.le
  · exact le_rfl

/-- **The level can be raised to one `≥ Ω₁·2`.** -/
theorem qdBd_up {v : Ordinal.{0}} (h : QdBd x v) :
    ∃ N, Om1 * 2 ≤ N ∧ N < ggGam ∧ Tf.tfDat N < x ∧ v < vt x (Om1 * N) := by
  obtain ⟨N, h1, h2, h3, h4⟩ := h
  obtain ⟨o1, o2, o3⟩ := qc_O2_facts
  have hd2 : Tf.tfDat (Om1 * 2) < x := by rw [Tf.tfDat_eq_rj _ o2]; exact o3.trans_lt (qc_two_lt hx)
  have o2' : Om1 * 2 < ggGam := o2.trans_le ggE_le_ggGam
  rcases le_total N (Om1 * 2) with hle | hle
  · exact ⟨Om1 * 2, le_rfl, o2', hd2, h4.trans_le (qd_vt_mono hx hx1 h1 h3 o2' hd2 hle)⟩
  · exact ⟨N, hle, h2, h3, h4⟩

/-- **`QdBd` is closed under `+`.** -/
theorem qdBd_add {a b : Ordinal.{0}} (ha : QdBd x a) (hb : QdBd x b) : QdBd x (a + b) := by
  obtain ⟨N, h1, h2, h3, h4⟩ := ha
  obtain ⟨N', h1', h2', h3', h4'⟩ := hb
  rcases le_total N N' with hle | hle
  · exact ⟨N', h1', h2', h3', (qd_bd_pt hx hx1 h1' h2' h3').2.2.2.add_lt
      (h4.trans_le (qd_vt_mono hx hx1 h1 h3 h2' h3' hle)) h4'⟩
  · exact ⟨N, h1, h2, h3, (qd_bd_pt hx hx1 h1 h2 h3).2.2.2.add_lt h4
      (h4'.trans_le (qd_vt_mono hx hx1 h1' h3' h2 h3 hle))⟩

/-- **`QdBd` is closed under `σ ↦ ϑˣ(Ω₁·Ω₁ + σ)`.** -/
theorem qdBd_gq {σ : Ordinal.{0}} (hσT : σ ∈ Tset x) (h : QdBd x σ) : QdBd x (gq σ x) := by
  obtain ⟨N, hN2, hNG, hNx, hσN⟩ := qdBd_up hx hx1 h
  obtain ⟨o1, -, -⟩ := qc_O2_facts
  have hN1 : Om1 ≤ N := o1.trans hN2
  obtain ⟨-, hB1, hpos', -⟩ := qd_bd_pt hx hx1 hN1 hNG hNx
  have hσ1 : σ < Om1 := hσN.trans hB1
  have h0T : (0 : Ordinal.{0}) ∈ Tset x := mem_T_of_le hx hx1 zero_le
  have harg : Om1 * Om1 + σ < Om1 * N + 0 := by
    rw [add_zero]
    calc Om1 * Om1 + σ < Om1 * Om1 + Om1 := (add_lt_add_iff_left _).2 hσ1
      _ = Om1 * (Om1 + 1) := (mul_add_one _ _).symm
      _ < Om1 * (Om1 * 2) := (mul_lt_mul_iff_right₀ rj_Om1_pos).2 (by
          rw [show (Om1 : Ordinal.{0}) * 2 = Om1 + Om1 by
            rw [show (2 : Ordinal.{0}) = 1 + 1 by norm_num, mul_add, mul_one]]
          exact (add_lt_add_iff_left _).2 (Lu.lu_one_lt_E (Low.opow_eq_self_of_SC qc_Om1_SC)))
      _ ≤ Om1 * N := mul_le_mul_right hN2 _
  have hpos : x ≤ vt x (Om1 * N + 0) := by rw [add_zero]; exact hpos'
  have hd0 : Tf.tfDat Om1 < vt x (Om1 * N + 0) := by rw [Tf.tfDat_Om1]; exact hx.pos.trans_le hpos
  have h1 := tfVt_lt hx hx1 hN1 (hNG.trans Tf.tf_gg_lt_BG) hN1
    (by rw [Tf.tfDat_Om1]; exact h0T) hσT hσ1 (mem_T_of_le hx hx1 hNx.le) h0T (hx.pos.trans hx1) harg hd0
    (by rw [add_zero]; exact hσN)
  refine ⟨N, hN1, hNG, hNx, ?_⟩
  rw [add_zero] at h1
  exact h1

end Bd

end Googology.Trans.PoR.InaccPsi.R2.Qd
