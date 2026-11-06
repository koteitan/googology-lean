import Googology.Trans.PoR.InaccPsi.R2.QcMxG

/-!
# QcFxA: TOOLS FOR THE TOP AT A FIXED POINT OF `Γ` BELOW `B₂`

* `vQ_dec'` (**the Cantor clause of `vQ` on `[G, B₂)`**), `qcI_eq_vI`, `qcA_atom'`, `vQ_atom'` (**a base atom
  `Γ(i)`, `i < Γ(i)`, below `B₂` reads `gq(qcI i)`**), `qcI_noFix`;
* `qc_off_gate'` (the offset `j − (F+1)` keeps the gate of `j` on `[G, B₂)`), `qcLv_congr`;
* `qcBd_zero`, `qcBd_max`, `qcBd_fold` (**`QcBd` of the largest value on the components**);
* `qc_tower` (**every level below `ε_{Ω₁+1}` is below a tower `Ω₁+1, ω^{Ω₁+1}, …` of data `1`**), `qcBd_vt`
  (**a point `ϑˣ(Ω₁·N + K)` with its data and `K` below a generic-level point is one**).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Yw
  Googology.Trans.PoR.InaccPsi.R2.Yh Googology.Trans.PoR.InaccPsi.R2.Va Googology.Trans.PoR.InaccPsi.R2.Tl
  Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Yr
  Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Trans.PoR.InaccPsi.R2.Zm Googology.Trans.PoR.InaccPsi.R2.Tf
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Rj Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Si Googology.Trans.PoR.InaccPsi.R2.Gb

/-- **The Cantor clause of `vQ` on `[G, B₂)`.** -/
theorem vQ_dec' {c : Ordinal.{0}} (h : gcG 0 ≤ c) (hB : c < ucB) (x : Ordinal.{0}) :
    vQ c x = qcA (guE c) x ^ vQ (log (guE c) c) x * vQ (c / guE c ^ log (guE c) c) x +
      vQ (c % guE c ^ log (guE c) c) x := by
  rcases lt_or_ge c tlX with hX | hX
  · obtain ⟨-, -, -, -, -, hkc, hrc, hdc⟩ := gl_parts (yh_gfE_le h)
    have hec := gl_E_le (yh_gfE_le h)
    rw [vQ_low hX, vR_dec h x, qcA_low (hec.trans_lt hX), vQ_low (hkc.trans hX), vQ_low (hdc.trans hX),
      vQ_low (hrc.trans hX)]
  · exact vQ_dec hX hB x

/-- Below `X` the atom index reading is `Va.vI`. -/
theorem qcI_eq_vI {j : Ordinal.{0}} (hj : j < tlX) (x : Ordinal.{0}) : qcI j x = vI j x := by
  unfold qcI vI
  split_ifs
  · rw [vQ_low ((va_fpG_le j).trans_lt hj), vQ_low ((Ordinal.sub_le_self _ _).trans_lt hj)]
  · rw [vQ_low hj]

/-- **A base atom `Γ(j) < B₂`, `j < Γ(j)`, reads `gq(qcI j)` as a base.** -/
theorem qcA_atom' {e : Ordinal.{0}} (hB : e < ucB) (hA : YhAt e) (hi : yhJ e < e) (x : Ordinal.{0}) :
    qcA e x = gq (qcI (yhJ e) x) x := by
  rcases lt_or_ge e tlX with hX | hX
  · rw [qcA_low hX, vA_atom hA hi, qcI_eq_vI (hi.trans hX)]
  · unfold qcA; rw [if_pos ⟨hX, hB⟩, if_pos hA, if_pos hi]

/-- **A base atom `Γ(i) < B₂`, `i < Γ(i)`, reads `gq(qcI i)`.** -/
theorem vQ_atom' {i : Ordinal.{0}} (hi : i < gcG i) (hB : gcG i < ucB) (x : Ordinal.{0}) :
    vQ (gcG i) x = gq (qcI i x) x := by
  have hE : InE (gcG i) := Low.opow_eq_self_of_SC (gcG_SC i)
  have hi' : yhJ (gcG i) < gcG i := by rw [yhJ_gcG]; exact hi
  rw [vQ_base' hE (gcG_le zero_le) hB, qcA_atom' hB (yhAt_gcG i) hi', yhJ_gcG]

/-- Below the first fixed point of `Γ` above `Ω₁` an atom index reads itself. -/
theorem qcI_noFix {j : Ordinal.{0}} (hj : ¬ tfBG < j) (x : Ordinal.{0}) : qcI j x = vQ j x := by
  unfold qcI; rw [if_neg (va_noFixG hj)]

/-- **The offset `j − (F+1)` keeps the gate of `j` up to `ω`** on `[G, B₂)` (`F` an `ε`-number code). -/
theorem qc_off_gate' {F j : Ordinal.{0}} (hFE : InE F) (hFG : gcG 0 ≤ F) (hjB : j < ucB) (hj : F < j) :
    qcG (j - (F + 1)) ≤ max ω (qcG j) := by
  rcases lt_or_ge j tlX with hjX | hjX
  · rw [qcG_low hjX, qcG_low ((Ordinal.sub_le_self _ _).trans_lt hjX)]
    exact vs_off_gate hFE hFG hj
  rcases le_or_gt tlX F with hXF | hFX
  · exact qc_off_gate hFE hXF hjB hj
  · -- `F < X ≤ j`: the prefix is absorbed
    have hF1 : (F + 1) * ω ≤ j := by
      have h1 : F + 1 < tlX := (ev_isSuccLimit_of_inE qc_X_E).add_one_lt hFX
      exact (qc_X_E.mul_lt h1 (omega0_lt_inE qc_X_E)).le.trans hjX
    rw [Ordinal.sub_eq_of_add_eq (add_eq_right_iff_mul_omega0_le.2 hF1)]
    exact le_max_right _ _

/-- **`qcLv f λ` depends on `f` only at the components of `λ`.** -/
theorem qcLv_congr {f g : Ordinal.{0} → Ordinal.{0}} :
    ∀ γ : Ordinal.{0}, (∀ d ∈ ucComps γ, f d = g d) → qcLv f γ = qcLv g γ := by
  intro γ
  induction γ using WellFoundedLT.induction with
  | ind γ IH =>
  intro h
  rcases lt_or_ge γ OmTwo with h1 | h1
  · rw [qcLv_small f h1, qcLv_small g h1]
    exact h γ (by rw [ucComps_small h1]; exact mem_singleton _)
  rcases lt_or_ge γ ucE with h2 | h2
  · have hc := ucComps_big h1 h2
    rw [qcLv_big f h1 h2, qcLv_big g h1 h2,
      IH _ (uc_log_lt h1 h2) fun d hd => h d (by rw [hc]; exact Or.inl hd),
      IH _ (uc_mod_lt h1) fun d hd => h d (by rw [hc]; exact Or.inr (Or.inr hd)),
      h _ (by rw [hc]; exact Or.inr (Or.inl rfl))]
  · rw [qcLv, dif_neg (not_lt.2 h1), dif_neg (not_lt.2 h2), qcLv, dif_neg (not_lt.2 h1), dif_neg (not_lt.2 h2)]

section Bd

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem qcBd_zero : QcBd x 0 := qcBd_of_X hx (hx.pos.trans (ywX_facts hx hx1).2.1)

omit hx hx1 in
theorem qcBd_max {a b : Ordinal.{0}} (ha : QcBd x a) (hb : QcBd x b) : QcBd x (max a b) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h]; exact hb
  · rw [max_eq_left h]; exact ha

/-- **`QcBd` of the largest value on the components.** -/
theorem qcBd_fold (f : Ordinal.{0} → Ordinal.{0}) :
    ∀ γ : Ordinal.{0}, (∀ d ∈ ucComps γ, QcBd x (f d)) → QcBd x (ucFold f γ) := by
  intro γ
  induction γ using WellFoundedLT.induction with
  | ind γ IH =>
  intro h
  rcases lt_or_ge γ OmTwo with h1 | h1
  · rw [ucFold_small f h1]; exact h γ (by rw [ucComps_small h1]; exact mem_singleton _)
  rcases lt_or_ge γ ucE with h2 | h2
  · have hc := ucComps_big h1 h2
    rw [ucFold_big f h1 h2]
    exact qcBd_max (IH _ (uc_log_lt h1 h2) fun d hd => h d (by rw [hc]; exact Or.inl hd))
      (qcBd_max (h _ (by rw [hc]; exact Or.inr (Or.inl rfl)))
        (IH _ (uc_mod_lt h1) fun d hd => h d (by rw [hc]; exact Or.inr (Or.inr hd))))
  · rw [ucFold_out f h2]; exact qcBd_zero hx hx1

end Bd

/-- **Every level below `ε_{Ω₁+1}` is below a tower point of data `1`.** -/
theorem qc_tower {N : Ordinal.{0}} (hN : N < ggE) :
    ∃ N', N < N' ∧ Om1 ≤ N' ∧ N' < ggE ∧ rjDat N' ≤ 1 := by
  have hgE : InE ggE := ggE_spec.1
  have hOE : Om1 < ggE := by rw [rj_Om1]; exact ggE_spec.2
  set τ : ℕ → Ordinal.{0} := fun n => (fun a => ω ^ a)^[n] (Om1 + 1) with hτ
  have hτE : ∀ n, τ n < ggE := by
    intro n
    induction n with
    | zero => exact (ev_isSuccLimit_of_inE hgE).add_one_lt hOE
    | succ n ih =>
      show (fun a => ω ^ a)^[n + 1] (Om1 + 1) < ggE
      rw [Function.iterate_succ_apply']
      exact (opow_lt_opow_iff_right one_lt_omega0).2 ih |>.trans_eq hgE
  have hτO : ∀ n, Om1 + 1 ≤ τ n := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
      show Om1 + 1 ≤ (fun a => ω ^ a)^[n + 1] (Om1 + 1)
      rw [Function.iterate_succ_apply']
      exact ih.trans (right_le_opow _ one_lt_omega0)
  have hτd : ∀ n, rjDat (τ n) ≤ 1 := by
    intro n
    induction n with
    | zero =>
      show rjDat (Om1 + 1) ≤ 1
      rw [rjDat_Om1_add one_ne_zero (lu_one_lt_E (Low.opow_eq_self_of_SC qc_Om1_SC))]
    | succ n ih =>
      show rjDat ((fun a => ω ^ a)^[n + 1] (Om1 + 1)) ≤ 1
      rw [Function.iterate_succ_apply']
      have h1 : Om1 < ω ^ τ n := ((lt_add_one _).trans_le (hτO n)).trans_le (right_le_opow _ one_lt_omega0)
      have h2 : ω ^ τ n < ggE := (opow_lt_opow_iff_right one_lt_omega0).2 (hτE n) |>.trans_eq hgE
      rw [si_rjDat_opow h1 h2]; exact ih
  have hfix : ω ^ nfp (fun a => ω ^ a) (Om1 + 1) = nfp (fun a => ω ^ a) (Om1 + 1) :=
    nfp_fp (isNormal_opow one_lt_omega0) _
  have hle : ggE ≤ nfp (fun a => ω ^ a) (Om1 + 1) :=
    ggE_le hfix (by rw [← rj_Om1]; exact (lt_add_one _).trans_le (le_nfp _ _))
  obtain ⟨n, hn⟩ := lt_nfp_iff.1 (hN.trans_le hle)
  exact ⟨τ n, hn, le_self_add.trans (hτO n), hτE n, hτd n⟩

/-- **A point `ϑˣ(Ω₁·N + K)` with its data and `K` below a generic-level point is below one.** -/
theorem qcBd_vt {x N K : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hNE : N < ggE)
    (hNT : rjDat N ∈ Tset x) (hK : K ∈ Tset x) (hK1 : K < Om1) (hb : QcBd x (max (rjDat N) K)) :
    QcBd x (vt x (Om1 * N + K)) := by
  obtain ⟨N₀, hN₀2, hN₀E, hN₀x, hb₀⟩ := qcBd_up hx hx1 hb
  obtain ⟨N₁, hNN₁, hN₁O, hN₁E, hN₁d⟩ := qc_tower hNE
  obtain ⟨o1, -, -⟩ := qc_O2_facts
  have hN₀1 : Om1 ≤ N₀ := o1.trans hN₀2
  have hN₁x : rjDat N₁ < x := hN₁d.trans_lt (lu_one_lt_E hx)
  set N' := max N₀ N₁ with hN'
  have hN'1 : Om1 ≤ N' := hN₀1.trans (le_max_left _ _)
  have hN'E : N' < ggE := max_lt hN₀E hN₁E
  have hN'x : rjDat N' < x := by
    rcases le_total N₀ N₁ with h | h
    · rw [hN', max_eq_right h]; exact hN₁x
    · rw [hN', max_eq_left h]; exact hN₀x
  have hmono := qc_vt_mono hx hx1 hN₀1 hN₀E hN₀x hN'E hN'x (le_max_left _ _)
  have h0T : (0 : Ordinal.{0}) ∈ Tset x := mem_T_of_le hx hx1 zero_le
  have h0Ω : (0 : Ordinal.{0}) < Om1 := hx.pos.trans hx1
  refine ⟨N', hN'1, hN'E, hN'x, ?_⟩
  have harg : Om1 * N + K < Om1 * N' + 0 := by
    rw [add_zero]
    calc Om1 * N + K < Om1 * N + Om1 := (add_lt_add_iff_left _).2 hK1
      _ = Om1 * (N + 1) := (mul_add_one _ _).symm
      _ ≤ Om1 * N' := mul_le_mul_right (Order.add_one_le_of_lt (hNN₁.trans_le (le_max_right _ _))) _
  have h := rjVt_lt hx hx1 hNE hNT hK hK1 hN'1 hN'E (mem_T_of_le hx hx1 hN'x.le) h0T h0Ω harg
    (by rw [add_zero]; exact ((le_max_left _ _).trans_lt hb₀).trans_le hmono)
    (by rw [add_zero]; exact ((le_max_right _ _).trans_lt hb₀).trans_le hmono)
  rwa [add_zero] at h

end Googology.Trans.PoR.InaccPsi.R2.Qc
