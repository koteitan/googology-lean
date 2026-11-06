import Googology.Trans.PoR.InaccPsi.R2.QcEq

/-!
# QcGEq: THE CLAUSES OF THE GATE `qcG` FROM `X` ON

As `Yr.yrG_dec`, `Yr.yrG_cnf`, `Yr.yrG_base`, `Yr.yrG_atom`, `Yr.yrG_succ`, `Yr.yrG_le_succ` for `Yr.yrG`:

* `qcQ_le`, `qcG_of_Q`, `qcQ_nat`, `qcG_zero`, `qcG_nat`, `qcKQ` (the gate of the index of a fixed point of `H_λ`);
* `qcQE_atom`, `qcQE_fix` (**the gate of a fixed point `H_λ(y)` of `Γ` as a base**: the gates of the components of
  `λ` and of the parts of the index), `qcQE_fix0`, `qcQE_psi`;
* `qcG_dec` (**`qcG c = max (max (qcQE e) (qcQ j)) (max (qcQ d) (qcG r))`** on `c = e^j·d + r`), `qcG_cnf`, `qcG_base`
  (**an `ε`-number code reads its base gate**), `qcG_atom`, `qcG_succ`, `qcG_le_succ`.

No new axiom.  New definition: `qcKQ`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qc

open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2 Googology.Notation.InaccPsi
  Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu
  Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Yh
  Googology.Trans.PoR.InaccPsi.R2.Yr Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Uc
  Googology.Trans.PoR.InaccPsi.R2.Va Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gn
  Googology.Trans.PoR.InaccPsi.R2.Xu Googology.Trans.PoR.InaccPsi.R2.Tf Googology.Trans.PoR.InaccPsi.R2.Yw

theorem qcQ_le (a : Ordinal.{0}) : qcQ a ≤ qcG a := by
  unfold qcQ; split_ifs
  · exact zero_le
  · exact le_rfl

theorem qcG_nat (n : ℕ) : qcG n = n := by
  rw [qcG_low ((natCast_lt_omega0 n).trans (omega0_lt_inE qc_X_E)), yrG_low (yh_nat_lt_G n), glG_nat]

theorem qcG_zero : qcG 0 = 0 := by exact_mod_cast qcG_nat 0

theorem qcQ_nat (n : ℕ) : qcQ n = 0 := by unfold qcQ; rw [if_pos (natCast_lt_omega0 n)]

theorem qcQ_zero : qcQ 0 = 0 := by exact_mod_cast qcQ_nat 0

theorem qcQ_one : qcQ 1 = 0 := by exact_mod_cast qcQ_nat 1

theorem qcG_of_Q {a Z : Ordinal.{0}} (hωZ : ω < Z) (h : qcQ a < Z) : qcG a < Z := by
  unfold qcQ at h
  split_ifs at h with ha
  · obtain ⟨n, rfl⟩ := lt_omega0.1 ha
    rw [qcG_nat]; exact (natCast_lt_omega0 n).trans hωZ
  · exact h

theorem qcQ_low {a : Ordinal.{0}} (h : a < tlX) : qcQ a = yrQ a := by
  unfold qcQ yrQ; rw [qcG_low h]

open Classical in
/-- **The gate of the index of a fixed point of `H_λ`**: the gates of `p` and `y − (p+1)` past the largest fixed point
`p < y` of `H_λ`, the gate of `y` below the first. -/
noncomputable def qcKQ (l y : Ordinal.{0}) : Ordinal.{0} :=
  if QcFixH l y then max (qcQ (qcFpH l y)) (qcQ (y - (qcFpH l y + 1))) else qcQ y

section Base

variable {e : Ordinal.{0}} (hX : tlX ≤ e) (hB : e < ucB)
include hX hB

theorem qcQE_atom (hA : YhAt e) (hi : yhJ e < e) : qcQE e = qcQ (yhJ e) := by
  unfold qcQE; rw [if_pos ⟨hX, hB⟩, if_pos hA, if_pos hi]

/-- **The gate of a fixed point `H_λ(y)` of `Γ` as a base.** -/
theorem qcQE_fix (hA : YhAt e) (hi : ¬ yhJ e < e) (hN : ucI (ucLev e) e < e) :
    qcQE e = max (ucFold (fun d => if d < e then qcQ d else 0) (ucLev e))
      (qcKQ (ucLev e) (ucI (ucLev e) e)) := by
  unfold qcQE; rw [if_pos ⟨hX, hB⟩, if_pos hA, if_neg hi, if_pos hN]; rfl

theorem qcQE_fix0 (hA : YhAt e) (hi : ¬ yhJ e < e) (hN : ¬ ucI (ucLev e) e < e) : qcQE e = 0 := by
  unfold qcQE; rw [if_pos ⟨hX, hB⟩, if_pos hA, if_neg hi, if_neg hN]

theorem qcQE_psi (hA : ¬ YhAt e) : qcQE e = max (qcQ (yhK e)) (qcQ (yhI e)) := by
  unfold qcQE; rw [if_pos ⟨hX, hB⟩, if_neg hA]

end Base

/-- **The Cantor clause of `qcG`** from `X` on. -/
theorem qcG_dec {c : Ordinal.{0}} (hX : tlX ≤ c) (hB : c < ucB) :
    qcG c = max (max (qcQE (guE c)) (qcQ (log (guE c) c)))
      (max (qcQ (c / guE c ^ log (guE c) c)) (qcG (c % guE c ^ log (guE c) c))) := by
  obtain ⟨hEX, hEB⟩ := qc_guE_X hX hB
  rw [qcG, dif_pos ⟨hX, hB⟩]
  by_cases hA : YhAt (guE c)
  · rw [dif_pos hA]
    by_cases hi : yhJ (guE c) < guE c
    · rw [dif_pos hi, qcQE_atom hEX hEB hA hi]; rfl
    · rw [dif_neg hi]
      by_cases hN : ucI (ucLev (guE c)) (guE c) < guE c
      · rw [dif_pos hN, qcQE_fix hEX hEB hA hi hN]
        simp only [dite_eq_ite]; rfl
      · rw [dif_neg hN, qcQE_fix0 hEX hEB hA hi hN]; rfl
  · rw [dif_neg hA, qcQE_psi hEX hEB hA]; rfl

/-- **The Cantor clause on a normal form** `e^j·d + r` from `X` on. -/
theorem qcG_cnf {e j d r : Ordinal.{0}} (he : InE e) (hXe : tlX ≤ e) (hj : j ≠ 0) (hd0 : d ≠ 0) (hde : d < e)
    (hr : r < e ^ j) (hv : e ^ j * d + r < eN e) (hvB : e ^ j * d + r < ucB) :
    qcG (e ^ j * d + r) = max (max (qcQE e) (qcQ j)) (max (qcQ d) (qcG r)) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := gl_cnf he (qc_X_gt.trans_le hXe) hj hd0 hde hr hv
  have hXc : tlX ≤ e ^ j * d + r := hXe.trans (xu_le_cnf he hj hd0)
  rw [qcG_dec hXc hvB, h1, h2, h3, h4]

/-- **An `ε`-number code `e ∈ [X, B₂)` has the gate `qcQE e`.** -/
theorem qcG_base {e : Ordinal.{0}} (he : InE e) (hXe : tlX ≤ e) (heB : e < ucB) : qcG e = qcQE e := by
  obtain ⟨h1, h2⟩ := gl_base_nf he
  have hE1 : (1 : Ordinal.{0}) < e := lu_one_lt_E he
  have h := qcG_cnf he hXe one_ne_zero one_ne_zero hE1 (by rw [opow_one]; exact he.pos) h2
    (by rw [← h1]; exact heB)
  rw [← h1] at h
  rw [h, qcQ_one, qcG_zero]
  simp

/-- **A base atom `Γ(i)`, `i < Γ(i)`, in `[X, B₂)` has the gate of its index.** -/
theorem qcG_atom {i : Ordinal.{0}} (hi : i < gcG i) (hX : tlX ≤ gcG i) (hB : gcG i < ucB) : qcG (gcG i) = qcQ i := by
  have hE : InE (gcG i) := Low.opow_eq_self_of_SC (gcG_SC i)
  have hi' : yhJ (gcG i) < gcG i := by rw [yhJ_gcG]; exact hi
  rw [qcG_base hE hX hB, qcQE_atom hX hB (yhAt_gcG i) hi', yhJ_gcG]

/-- **The gate of every code `c ≥ B₂` is `yrG c`** (outside the range of `qcG`). -/
theorem qcG_out {c : Ordinal.{0}} (h : ucB ≤ c) : qcG c = yrG c := by
  rw [qcG, dif_neg (fun hX => absurd hX.2 (not_lt.2 h))]

theorem qcG_succ {Z : Ordinal.{0}} (hZ : IsSuccLimit Z) : ∀ b, qcG b < Z → qcG (b + 1) < Z := by
  intro b
  induction b using WellFoundedLT.induction with
  | ind b IH =>
  intro hg
  rcases lt_or_ge b tlX with hbX | hbX
  · have hb1 : b + 1 < tlX := (ev_isSuccLimit_of_inE qc_X_E).add_one_lt hbX
    rw [qcG_low hbX] at hg
    rw [qcG_low hb1]
    exact yrG_succ hZ b hg
  rcases lt_or_ge b ucB with hbB | hbB
  · have hb1B : b + 1 < ucB := ucB_SC.isSuccLimit.add_one_lt hbB
    have hbE := yh_gfE_le (qc_X_G0.trans hbX)
    obtain ⟨hk, hd0, hdE, -, -, -, hrb, -⟩ := gl_parts hbE
    obtain ⟨e, hr1, hv⟩ := gl_succ_nf hbE
    have hXE := (qc_guE_X hbX hbB).1
    rw [qcG_dec hbX hbB] at hg
    rw [e, qcG_cnf (guE_E b) hXE hk hd0 hdE hr1 hv (by rw [← e]; exact hb1B)]
    exact max_lt ((le_max_left _ _).trans_lt hg) (max_lt ((le_max_left _ _).trans_lt
      ((le_max_right _ _).trans_lt hg)) (IH _ hrb ((le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hg))))
  · rw [qcG_out hbB] at hg
    rw [qcG_out (hbB.trans le_self_add)]
    exact yrG_succ hZ b hg

theorem qcG_le_succ : ∀ b, qcG b ≤ qcG (b + 1) := by
  intro b
  induction b using WellFoundedLT.induction with
  | ind b IH =>
  rcases lt_or_ge b tlX with hbX | hbX
  · have hb1 : b + 1 < tlX := (ev_isSuccLimit_of_inE qc_X_E).add_one_lt hbX
    rw [qcG_low hbX, qcG_low hb1]; exact yrG_le_succ b
  rcases lt_or_ge b ucB with hbB | hbB
  · have hb1B : b + 1 < ucB := ucB_SC.isSuccLimit.add_one_lt hbB
    have hbE := yh_gfE_le (qc_X_G0.trans hbX)
    obtain ⟨hk, hd0, hdE, -, -, -, hrb, -⟩ := gl_parts hbE
    obtain ⟨e, hr1, hv⟩ := gl_succ_nf hbE
    have hXE := (qc_guE_X hbX hbB).1
    rw [qcG_dec hbX hbB, e, qcG_cnf (guE_E b) hXE hk hd0 hdE hr1 hv (by rw [← e]; exact hb1B)]
    exact max_le_max le_rfl (max_le_max le_rfl (IH _ hrb))
  · rw [qcG_out hbB, qcG_out (hbB.trans le_self_add)]; exact yrG_le_succ b

end Googology.Trans.PoR.InaccPsi.R2.Qc
