import Googology.Trans.PoR.InaccPsi.R2.QcG

/-!
# QcEq: THE CLAUSES OF THE READING `vQ` FROM `X` ON

As `Va.vR_dec`, `Va.vR_cnf`, `Va.vR_base`, `Va.vR_atom`, `Va.vR_succ` for `Va.vR`:

* `qc_guE_X` (the `ε`-bracket of a code `c ∈ [X, B₂)` is in `[X, B₂)`), `vQ_dec` (**`vQ c = qcA(e)^{vQ j}·vQ d + vQ r`**
  on the Cantor normal form `c = e^j·d + r` in the bracket `e = guE c`), `vQ_cnf`, `vQ_base` (**an `ε`-number code
  `e ∈ [X, B₂)` reads `qcA e`**), `vQ_atom` (**a base atom `Γ(i)`, `i < Γ(i)`, reads `gq(qcI i)`**), `vQ_fix`
  (**a fixed point `H_λ(y)` of `Γ` reads `ϑˣ(Ω₁·(Ω₁ + λ(x)) + qcK λ y x)`**), `vQ_psi`, `vQ_succ` (**`vQ (b+1) = vQ b + 1`**).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qc

open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2 Googology.Notation.InaccPsi
  Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu
  Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Yh
  Googology.Trans.PoR.InaccPsi.R2.Yr Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Uc
  Googology.Trans.PoR.InaccPsi.R2.Va Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gn
  Googology.Trans.PoR.InaccPsi.R2.Xu Googology.Trans.PoR.InaccPsi.R2.Tf Googology.Trans.PoR.InaccPsi.R2.Yw

theorem qc_X_E : InE (tlX : Ordinal.{0}) := Low.opow_eq_self_of_SC tlX_SC

theorem qc_X_gt : (Om1 : Ordinal.{0}) < tlX := tlX_gt

/-- **The `ε`-bracket of a code `c ∈ [X, B₂)` is in `[X, B₂)`.** -/
theorem qc_guE_X {c : Ordinal.{0}} (hX : tlX ≤ c) (hB : c < ucB) : tlX ≤ guE c ∧ guE c < ucB :=
  ⟨gl_E_max qc_X_E qc_X_gt hX, (gl_E_le (yh_gfE_le (qc_X_G0.trans hX))).trans_lt hB⟩

theorem qcLvx_eq (c l x : Ordinal.{0}) :
    qcLv (fun d => if hd : d < guE c then vQ d x else 0) l = qcLvx (guE c) l x := by
  unfold qcLvx; simp only [dite_eq_ite]

open Classical in
/-- **The Cantor clause of `vQ`** from `X` on. -/
theorem vQ_dec {c : Ordinal.{0}} (hX : tlX ≤ c) (hB : c < ucB) (x : Ordinal.{0}) :
    vQ c x = qcA (guE c) x ^ vQ (log (guE c) c) x * vQ (c / guE c ^ log (guE c) c) x +
      vQ (c % guE c ^ log (guE c) c) x := by
  obtain ⟨hEX, hEB⟩ := qc_guE_X hX hB
  have H : (if hA : YhAt (guE c) then (if hi : yhJ (guE c) < guE c then
        gq (if VaFixG (yhJ (guE c)) then vQ (vaFpG (yhJ (guE c))) x +
            vQ (yhJ (guE c) - (vaFpG (yhJ (guE c)) + 1)) x
          else vQ (yhJ (guE c)) x) x
        else (if hN : ucI (ucLev (guE c)) (guE c) < guE c then
          vt x (Om1 * (Om1 + qcLv (fun d => if hd : d < guE c then vQ d x else 0) (ucLev (guE c))) +
            (if QcFixH (ucLev (guE c)) (ucI (ucLev (guE c)) (guE c)) then
              vQ (qcFpH (ucLev (guE c)) (ucI (ucLev (guE c)) (guE c))) x +
              vQ (ucI (ucLev (guE c)) (guE c) - (qcFpH (ucLev (guE c)) (ucI (ucLev (guE c)) (guE c)) + 1)) x
            else vQ (ucI (ucLev (guE c)) (guE c)) x))
          else 0))
      else glA (vQ (yhK (guE c)) x) (vQ (yhI (guE c)) x) x) = qcA (guE c) x := by
    unfold qcA
    rw [if_pos (show tlX ≤ guE c ∧ guE c < ucB from ⟨hEX, hEB⟩)]
    by_cases hA : YhAt (guE c)
    · rw [dif_pos hA, if_pos hA]
      by_cases hi : yhJ (guE c) < guE c
      · rw [dif_pos hi, if_pos hi]; rfl
      · rw [dif_neg hi, if_neg hi]
        by_cases hN : ucI (ucLev (guE c)) (guE c) < guE c
        · rw [dif_pos hN, if_pos hN, qcLvx_eq]; rfl
        · rw [dif_neg hN, if_neg hN]
    · rw [dif_neg hA, if_neg hA]
  rw [vQ, dif_pos ⟨hX, hB⟩, H]

/-- **The Cantor clause on a normal form** `e^j·d + r` from `X` on. -/
theorem vQ_cnf {e j d r : Ordinal.{0}} (he : InE e) (hXe : tlX ≤ e) (hj : j ≠ 0) (hd0 : d ≠ 0) (hde : d < e)
    (hr : r < e ^ j) (hv : e ^ j * d + r < eN e) (hvB : e ^ j * d + r < ucB) (x : Ordinal.{0}) :
    vQ (e ^ j * d + r) x = qcA e x ^ vQ j x * vQ d x + vQ r x := by
  obtain ⟨h1, h2, h3, h4, -⟩ := gl_cnf he (qc_X_gt.trans_le hXe) hj hd0 hde hr hv
  have hXc : tlX ≤ e ^ j * d + r := hXe.trans (xu_le_cnf he hj hd0)
  rw [vQ_dec hXc hvB x, h1, h2, h3, h4]

theorem vQ_zero (x : Ordinal.{0}) : vQ 0 x = 0 := by rw [vQ_low qc_X_E.pos, vR_zero]

theorem vQ_one (x : Ordinal.{0}) : vQ 1 x = 1 := by
  rw [vQ_low ((lu_one_lt_E qc_X_E)), vR_one]

/-- **An `ε`-number code `e ∈ [X, B₂)` reads `qcA e`.** -/
theorem vQ_base {e : Ordinal.{0}} (he : InE e) (hXe : tlX ≤ e) (heB : e < ucB) (x : Ordinal.{0}) :
    vQ e x = qcA e x := by
  obtain ⟨h1, h2⟩ := gl_base_nf he
  have hE1 : (1 : Ordinal.{0}) < e := lu_one_lt_E he
  have h := vQ_cnf he hXe one_ne_zero one_ne_zero hE1 (by rw [opow_one]; exact he.pos) h2
    (by rw [← h1]; exact heB) x
  rw [← h1] at h
  rw [h, vQ_one, vQ_zero, opow_one, mul_one, add_zero]

/-- **A base atom `Γ(i)`, `i < Γ(i)`, in `[X, B₂)` reads `gq(qcI i)`.** -/
theorem vQ_atom {i : Ordinal.{0}} (hi : i < gcG i) (hX : tlX ≤ gcG i) (hB : gcG i < ucB) (x : Ordinal.{0}) :
    vQ (gcG i) x = gq (qcI i x) x := by
  have hE : InE (gcG i) := Low.opow_eq_self_of_SC (gcG_SC i)
  have hi' : yhJ (gcG i) < gcG i := by rw [yhJ_gcG]; exact hi
  rw [vQ_base hE hX hB]
  unfold qcA
  rw [if_pos ⟨hX, hB⟩, if_pos (yhAt_gcG i), if_pos hi', yhJ_gcG]

/-- **A fixed point `e = H_λ(y)` of `Γ` in `[X, B₂)` reads `ϑˣ(Ω₁·(Ω₁ + λ(x)) + c(x))`.** -/
theorem vQ_fix {e : Ordinal.{0}} (hA : YhAt e) (hi : ¬ yhJ e < e) (hN : ucI (ucLev e) e < e) (hX : tlX ≤ e)
    (hB : e < ucB) (x : Ordinal.{0}) :
    vQ e x = vt x (Om1 * (Om1 + qcLvx e (ucLev e) x) + qcK (ucLev e) (ucI (ucLev e) e) x) := by
  have hE : InE e := Low.opow_eq_self_of_SC hA.1
  rw [vQ_base hE hX hB]
  unfold qcA
  rw [if_pos ⟨hX, hB⟩, if_pos hA, if_neg hi, if_pos hN]

/-- **A non-atom `ε`-number code `e ∈ [X, B₂)` reads `ϑˣ(Ω₁·α(x) + η(x))`.** -/
theorem vQ_nonAt {e : Ordinal.{0}} (he : InE e) (hA : ¬ YhAt e) (hX : tlX ≤ e) (hB : e < ucB) (x : Ordinal.{0}) :
    vQ e x = glA (vQ (yhK e) x) (vQ (yhI e) x) x := by
  rw [vQ_base he hX hB]
  unfold qcA
  rw [if_pos ⟨hX, hB⟩, if_neg hA]

/-- **`vQ (b + 1) = vQ b + 1`.** -/
theorem vQ_succ : ∀ b x : Ordinal.{0}, vQ (b + 1) x = vQ b x + 1 := by
  intro b
  induction b using WellFoundedLT.induction with
  | ind b IH =>
  intro x
  rcases lt_or_ge b tlX with hbX | hbX
  · have hb1 : b + 1 < tlX := (ev_isSuccLimit_of_inE qc_X_E).add_one_lt hbX
    rw [vQ_low hbX, vQ_low hb1, vR_succ]
  rcases lt_or_ge b ucB with hbB | hbB
  · have hb1B : b + 1 < ucB := ucB_SC.isSuccLimit.add_one_lt hbB
    have hbE := yh_gfE_le (qc_X_G0.trans hbX)
    obtain ⟨hk, hd0, hdE, -, -, -, hrb, -⟩ := gl_parts hbE
    obtain ⟨e, hr1, hv⟩ := gl_succ_nf hbE
    have hXE := (qc_guE_X hbX hbB).1
    rw [e, vQ_cnf (guE_E b) hXE hk hd0 hdE hr1 hv (by rw [← e]; exact hb1B), IH _ hrb x, vQ_dec hbX hbB x,
      add_assoc]
  · have hb1 : ucB ≤ b + 1 := hbB.trans le_self_add
    have e1 : vQ b x = vR b x := by rw [vQ, dif_neg (fun h => absurd h.2 (not_lt.2 hbB))]
    have e2 : vQ (b + 1) x = vR (b + 1) x := by rw [vQ, dif_neg (fun h => absurd h.2 (not_lt.2 hb1))]
    rw [e1, e2, vR_succ]

end Googology.Trans.PoR.InaccPsi.R2.Qc
