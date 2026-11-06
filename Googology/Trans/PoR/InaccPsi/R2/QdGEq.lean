import Googology.Trans.PoR.InaccPsi.R2.QdEq

/-!
# QdGEq: THE CLAUSES OF THE GATE `qdGt` FROM `B₂` ON

As `Qc.qcG_dec`, `Qc.qcG_cnf`, `Qc.qcG_base`, `Qc.qcG_atom`, `Qc.qcG_succ`, `Qc.qcG_le_succ` for `Qc.qcG`:

* `qdQt_le`, `qdGt_of_Q`, `qdQt_nat`, `qdGt_zero`, `qdGt_nat`, `qdQt_low`, `qdKQ` (the gate of the index of a fixed
  point of `Hᵛ_λ`);
* `qdQEt_atom`, `qdQEt_fix` (**the gate of a fixed point `Hᵛ_λ(y)` of `Γ` as a base**: the gates of the leaves of
  `λ` and of the parts of the index), `qdQEt_fix0`, `qdQEt_psi`;
* `qdGt_dec` (**`qdGt c = max (max (qdQEt e) (qdQt j)) (max (qdQt d) (qdGt r))`** on `c = e^j·d + r`), `qdGt_cnf`,
  `qdGt_base`, `qdGt_atom`, `qdGt_out`, `qdGt_succ`, `qdGt_le_succ`.

No new axiom.  New definition: `qdKQ`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qd

open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2 Googology.Notation.InaccPsi
  Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu
  Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Yh
  Googology.Trans.PoR.InaccPsi.R2.Yr Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Uc
  Googology.Trans.PoR.InaccPsi.R2.Va Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gn
  Googology.Trans.PoR.InaccPsi.R2.Xu Googology.Trans.PoR.InaccPsi.R2.Tf Googology.Trans.PoR.InaccPsi.R2.Yw
  Googology.Trans.PoR.InaccPsi.R2.Qc

theorem qdQt_le (a : Ordinal.{0}) : qdQt a ≤ qdGt a := by
  unfold qdQt; split_ifs
  · exact zero_le
  · exact le_rfl

theorem qdGt_nat (n : ℕ) : qdGt n = n := by
  rw [qdGt_low ((natCast_lt_omega0 n).trans (omega0_lt_inE qd_B2_E)), qcG_nat]

theorem qdGt_zero : qdGt 0 = 0 := by exact_mod_cast qdGt_nat 0

theorem qdQt_nat (n : ℕ) : qdQt n = 0 := by unfold qdQt; rw [if_pos (natCast_lt_omega0 n)]

theorem qdQt_zero : qdQt 0 = 0 := by exact_mod_cast qdQt_nat 0

theorem qdQt_one : qdQt 1 = 0 := by exact_mod_cast qdQt_nat 1

theorem qdGt_of_Q {a Z : Ordinal.{0}} (hωZ : ω < Z) (h : qdQt a < Z) : qdGt a < Z := by
  unfold qdQt at h
  split_ifs at h with ha
  · obtain ⟨n, rfl⟩ := lt_omega0.1 ha
    rw [qdGt_nat]; exact (natCast_lt_omega0 n).trans hωZ
  · exact h

theorem qdQt_low {a : Ordinal.{0}} (h : a < ucB) : qdQt a = qcQ a := by
  unfold qdQt qcQ; rw [qdGt_low h]

open Classical in
/-- **The gate of the index of a fixed point of `Hᵛ_λ`**: the gates of `p` and `y − (p+1)` past the largest fixed point
`p < y` of `Hᵛ_λ`, the gate of `y` below the first. -/
noncomputable def qdKQ (l y : Ordinal.{0}) : Ordinal.{0} :=
  if QdFixH l y then max (qdQt (qdFpH l y)) (qdQt (y - (qdFpH l y + 1))) else qdQt y

section Base

variable {e : Ordinal.{0}} (hX : ucB ≤ e) (hB : e < qdB)
include hX hB

theorem qdQEt_atom (hA : YhAt e) (hi : yhJ e < e) : qdQEt e = qdQt (yhJ e) := by
  unfold qdQEt; rw [if_pos ⟨hX, hB⟩, if_pos hA, if_pos hi]

/-- **The gate of a fixed point `Hᵛ_λ(y)` of `Γ` as a base.** -/
theorem qdQEt_fix (hA : YhAt e) (hi : ¬ yhJ e < e) (hN : qdI (qdLev e) e < e) :
    qdQEt e = max (qdFold (fun d => if d < e then qdQt d else 0) (qdLev e))
      (qdKQ (qdLev e) (qdI (qdLev e) e)) := by
  unfold qdQEt; rw [if_pos ⟨hX, hB⟩, if_pos hA, if_neg hi, if_pos hN]; rfl

theorem qdQEt_fix0 (hA : YhAt e) (hi : ¬ yhJ e < e) (hN : ¬ qdI (qdLev e) e < e) : qdQEt e = 0 := by
  unfold qdQEt; rw [if_pos ⟨hX, hB⟩, if_pos hA, if_neg hi, if_neg hN]

theorem qdQEt_psi (hA : ¬ YhAt e) : qdQEt e = max (qdQt (yhK e)) (qdQt (yhI e)) := by
  unfold qdQEt; rw [if_pos ⟨hX, hB⟩, if_neg hA]

end Base

/-- **The Cantor clause of `qdGt`** from `B₂` on. -/
theorem qdGt_dec {c : Ordinal.{0}} (hX : ucB ≤ c) (hB : c < qdB) :
    qdGt c = max (max (qdQEt (guE c)) (qdQt (log (guE c) c)))
      (max (qdQt (c / guE c ^ log (guE c) c)) (qdGt (c % guE c ^ log (guE c) c))) := by
  obtain ⟨hEX, hEB⟩ := qd_guE_B hX hB
  rw [qdGt, dif_pos ⟨hX, hB⟩]
  by_cases hA : YhAt (guE c)
  · rw [dif_pos hA]
    by_cases hi : yhJ (guE c) < guE c
    · rw [dif_pos hi, qdQEt_atom hEX hEB hA hi]; rfl
    · rw [dif_neg hi]
      by_cases hN : qdI (qdLev (guE c)) (guE c) < guE c
      · rw [dif_pos hN, qdQEt_fix hEX hEB hA hi hN]
        simp only [dite_eq_ite]; rfl
      · rw [dif_neg hN, qdQEt_fix0 hEX hEB hA hi hN]; rfl
  · rw [dif_neg hA, qdQEt_psi hEX hEB hA]; rfl

/-- **The Cantor clause on a normal form** `e^j·d + r` from `B₂` on. -/
theorem qdGt_cnf {e j d r : Ordinal.{0}} (he : InE e) (hXe : ucB ≤ e) (hj : j ≠ 0) (hd0 : d ≠ 0) (hde : d < e)
    (hr : r < e ^ j) (hv : e ^ j * d + r < eN e) (hvB : e ^ j * d + r < qdB) :
    qdGt (e ^ j * d + r) = max (max (qdQEt e) (qdQt j)) (max (qdQt d) (qdGt r)) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := gl_cnf he (qd_B2_gt.trans_le hXe) hj hd0 hde hr hv
  have hXc : ucB ≤ e ^ j * d + r := hXe.trans (xu_le_cnf he hj hd0)
  rw [qdGt_dec hXc hvB, h1, h2, h3, h4]

/-- **An `ε`-number code `e ∈ [B₂, B₃)` has the gate `qdQEt e`.** -/
theorem qdGt_base {e : Ordinal.{0}} (he : InE e) (hXe : ucB ≤ e) (heB : e < qdB) : qdGt e = qdQEt e := by
  obtain ⟨h1, h2⟩ := gl_base_nf he
  have hE1 : (1 : Ordinal.{0}) < e := lu_one_lt_E he
  have h := qdGt_cnf he hXe one_ne_zero one_ne_zero hE1 (by rw [opow_one]; exact he.pos) h2
    (by rw [← h1]; exact heB)
  rw [← h1] at h
  rw [h, qdQt_one, qdGt_zero]
  simp

/-- **A base atom `Γ(i)`, `i < Γ(i)`, in `[B₂, B₃)` has the gate of its index.** -/
theorem qdGt_atom {i : Ordinal.{0}} (hi : i < gcG i) (hX : ucB ≤ gcG i) (hB : gcG i < qdB) : qdGt (gcG i) = qdQt i := by
  have hE : InE (gcG i) := Low.opow_eq_self_of_SC (gcG_SC i)
  have hi' : yhJ (gcG i) < gcG i := by rw [yhJ_gcG]; exact hi
  rw [qdGt_base hE hX hB, qdQEt_atom hX hB (yhAt_gcG i) hi', yhJ_gcG]

/-- **The gate of every code `c ≥ B₃` is `qcG c`** (outside the range of `qdGt`). -/
theorem qdGt_out {c : Ordinal.{0}} (h : qdB ≤ c) : qdGt c = qcG c := by
  rw [qdGt, dif_neg (fun hX => absurd hX.2 (not_lt.2 h))]

theorem qdGt_succ {Z : Ordinal.{0}} (hZ : IsSuccLimit Z) : ∀ b, qdGt b < Z → qdGt (b + 1) < Z := by
  intro b
  induction b using WellFoundedLT.induction with
  | ind b IH =>
  intro hg
  rcases lt_or_ge b ucB with hbX | hbX
  · have hb1 : b + 1 < ucB := (ev_isSuccLimit_of_inE qd_B2_E).add_one_lt hbX
    rw [qdGt_low hbX] at hg
    rw [qdGt_low hb1]
    exact qcG_succ hZ b hg
  rcases lt_or_ge b qdB with hbB | hbB
  · have hb1B : b + 1 < qdB := qdB_SC.isSuccLimit.add_one_lt hbB
    have hbE := yh_gfE_le (qd_B2_G0.trans hbX)
    obtain ⟨hk, hd0, hdE, -, -, -, hrb, -⟩ := gl_parts hbE
    obtain ⟨e, hr1, hv⟩ := gl_succ_nf hbE
    have hXE := (qd_guE_B hbX hbB).1
    rw [qdGt_dec hbX hbB] at hg
    rw [e, qdGt_cnf (guE_E b) hXE hk hd0 hdE hr1 hv (by rw [← e]; exact hb1B)]
    exact max_lt ((le_max_left _ _).trans_lt hg) (max_lt ((le_max_left _ _).trans_lt
      ((le_max_right _ _).trans_lt hg)) (IH _ hrb ((le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hg))))
  · rw [qdGt_out hbB] at hg
    rw [qdGt_out (hbB.trans le_self_add)]
    exact qcG_succ hZ b hg

theorem qdGt_le_succ : ∀ b, qdGt b ≤ qdGt (b + 1) := by
  intro b
  induction b using WellFoundedLT.induction with
  | ind b IH =>
  rcases lt_or_ge b ucB with hbX | hbX
  · have hb1 : b + 1 < ucB := (ev_isSuccLimit_of_inE qd_B2_E).add_one_lt hbX
    rw [qdGt_low hbX, qdGt_low hb1]; exact qcG_le_succ b
  rcases lt_or_ge b qdB with hbB | hbB
  · have hb1B : b + 1 < qdB := qdB_SC.isSuccLimit.add_one_lt hbB
    have hbE := yh_gfE_le (qd_B2_G0.trans hbX)
    obtain ⟨hk, hd0, hdE, -, -, -, hrb, -⟩ := gl_parts hbE
    obtain ⟨e, hr1, hv⟩ := gl_succ_nf hbE
    have hXE := (qd_guE_B hbX hbB).1
    rw [qdGt_dec hbX hbB, e, qdGt_cnf (guE_E b) hXE hk hd0 hdE hr1 hv (by rw [← e]; exact hb1B)]
    exact max_le_max le_rfl (max_le_max le_rfl (IH _ hrb))
  · rw [qdGt_out hbB, qdGt_out (hbB.trans le_self_add)]; exact qcG_le_succ b

end Googology.Trans.PoR.InaccPsi.R2.Qd
