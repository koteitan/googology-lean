import Googology.Trans.PoR.InaccPsi.R2.QdAgr

/-!
# QdEq: THE CLAUSES OF THE READING `vD` FROM `B₂` ON

As `Qc.vQ_dec`, `Qc.vQ_cnf`, `Qc.vQ_base`, `Qc.vQ_atom`, `Qc.vQ_fix`, `Qc.vQ_nonAt`, `Qc.vQ_succ` for `Qc.vQ`:

* `qd_B2_E`, `qd_B2_gt`, `qd_B3_lim`, `qd_guE_B` (the `ε`-bracket of a code `c ∈ [B₂, B₃)` is in `[B₂, B₃)`),
  `vD_dec` (**`vD c = qdA(e)^{vD j}·vD d + vD r`** on the Cantor normal form `c = e^j·d + r` in the bracket
  `e = guE c`), `vD_cnf`, `vD_base` (**an `ε`-number code `e ∈ [B₂, B₃)` reads `qdA e`**), `vD_atom` (**a base atom
  `Γ(i)`, `i < Γ(i)`, reads `gq(qdRI i)`**), `vD_fix` (**a fixed point `Hᵛ_λ(y)` of `Γ` reads `ϑˣ(Ω₁·(Ω₁ + λ(x)) +
  qdRK λ y x)`**), `vD_nonAt`, `vD_zero`, `vD_one`, `vD_succ` (**`vD (b+1) = vD b + 1`**).

No new axiom.  No new definition.
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

theorem qd_B2_E : InE (ucB : Ordinal.{0}) := Low.opow_eq_self_of_SC ucB_SC

theorem qd_B2_gt : (Om1 : Ordinal.{0}) < ucB := ucB_gt

theorem qd_B3_lim : IsSuccLimit (qdB : Ordinal.{0}) := qdB_SC.isSuccLimit

/-- **The `ε`-bracket of a code `c ∈ [B₂, B₃)` is in `[B₂, B₃)`.** -/
theorem qd_guE_B {c : Ordinal.{0}} (hX : ucB ≤ c) (hB : c < qdB) : ucB ≤ guE c ∧ guE c < qdB :=
  ⟨gl_E_max qd_B2_E qd_B2_gt hX, (gl_E_le (yh_gfE_le (qd_B2_G0.trans hX))).trans_lt hB⟩

theorem qdLvx_eq (c l x : Ordinal.{0}) :
    qdLv (fun d => if hd : d < guE c then vD d x else 0) l = qdLvx (guE c) l x := by
  unfold qdLvx; simp only [dite_eq_ite]

open Classical in
/-- **The Cantor clause of `vD`** from `B₂` on. -/
theorem vD_dec {c : Ordinal.{0}} (hX : ucB ≤ c) (hB : c < qdB) (x : Ordinal.{0}) :
    vD c x = qdA (guE c) x ^ vD (log (guE c) c) x * vD (c / guE c ^ log (guE c) c) x +
      vD (c % guE c ^ log (guE c) c) x := by
  obtain ⟨hEX, hEB⟩ := qd_guE_B hX hB
  have H : (if hA : YhAt (guE c) then (if hi : yhJ (guE c) < guE c then
        gq (if VaFixG (yhJ (guE c)) then vD (vaFpG (yhJ (guE c))) x +
            vD (yhJ (guE c) - (vaFpG (yhJ (guE c)) + 1)) x
          else vD (yhJ (guE c)) x) x
        else (if hN : qdI (qdLev (guE c)) (guE c) < guE c then
          vt x (Om1 * (Om1 + qdLv (fun d => if hd : d < guE c then vD d x else 0) (qdLev (guE c))) +
            (if QdFixH (qdLev (guE c)) (qdI (qdLev (guE c)) (guE c)) then
              vD (qdFpH (qdLev (guE c)) (qdI (qdLev (guE c)) (guE c))) x +
              vD (qdI (qdLev (guE c)) (guE c) - (qdFpH (qdLev (guE c)) (qdI (qdLev (guE c)) (guE c)) + 1)) x
            else vD (qdI (qdLev (guE c)) (guE c)) x))
          else 0))
      else glA (vD (yhK (guE c)) x) (vD (yhI (guE c)) x) x) = qdA (guE c) x := by
    unfold qdA
    rw [if_pos (show ucB ≤ guE c ∧ guE c < qdB from ⟨hEX, hEB⟩)]
    by_cases hA : YhAt (guE c)
    · rw [dif_pos hA, if_pos hA]
      by_cases hi : yhJ (guE c) < guE c
      · rw [dif_pos hi, if_pos hi]; rfl
      · rw [dif_neg hi, if_neg hi]
        by_cases hN : qdI (qdLev (guE c)) (guE c) < guE c
        · rw [dif_pos hN, if_pos hN, qdLvx_eq]; rfl
        · rw [dif_neg hN, if_neg hN]
    · rw [dif_neg hA, if_neg hA]
  rw [vD, dif_pos ⟨hX, hB⟩, H]

/-- **The Cantor clause on a normal form** `e^j·d + r` from `B₂` on. -/
theorem vD_cnf {e j d r : Ordinal.{0}} (he : InE e) (hXe : ucB ≤ e) (hj : j ≠ 0) (hd0 : d ≠ 0) (hde : d < e)
    (hr : r < e ^ j) (hv : e ^ j * d + r < eN e) (hvB : e ^ j * d + r < qdB) (x : Ordinal.{0}) :
    vD (e ^ j * d + r) x = qdA e x ^ vD j x * vD d x + vD r x := by
  obtain ⟨h1, h2, h3, h4, -⟩ := gl_cnf he (qd_B2_gt.trans_le hXe) hj hd0 hde hr hv
  have hXc : ucB ≤ e ^ j * d + r := hXe.trans (xu_le_cnf he hj hd0)
  rw [vD_dec hXc hvB x, h1, h2, h3, h4]

theorem vD_zero (x : Ordinal.{0}) : vD 0 x = 0 := by rw [vD_low qd_B2_E.pos, vQ_zero]

theorem vD_one (x : Ordinal.{0}) : vD 1 x = 1 := by
  rw [vD_low (lu_one_lt_E qd_B2_E), vQ_one]

/-- **An `ε`-number code `e ∈ [B₂, B₃)` reads `qdA e`.** -/
theorem vD_base {e : Ordinal.{0}} (he : InE e) (hXe : ucB ≤ e) (heB : e < qdB) (x : Ordinal.{0}) :
    vD e x = qdA e x := by
  obtain ⟨h1, h2⟩ := gl_base_nf he
  have hE1 : (1 : Ordinal.{0}) < e := lu_one_lt_E he
  have h := vD_cnf he hXe one_ne_zero one_ne_zero hE1 (by rw [opow_one]; exact he.pos) h2
    (by rw [← h1]; exact heB) x
  rw [← h1] at h
  rw [h, vD_one, vD_zero, opow_one, mul_one, add_zero]

/-- **A base atom `Γ(i)`, `i < Γ(i)`, in `[B₂, B₃)` reads `gq(qdRI i)`.** -/
theorem vD_atom {i : Ordinal.{0}} (hi : i < gcG i) (hX : ucB ≤ gcG i) (hB : gcG i < qdB) (x : Ordinal.{0}) :
    vD (gcG i) x = gq (qdRI i x) x := by
  have hE : InE (gcG i) := Low.opow_eq_self_of_SC (gcG_SC i)
  have hi' : yhJ (gcG i) < gcG i := by rw [yhJ_gcG]; exact hi
  rw [vD_base hE hX hB]
  unfold qdA
  rw [if_pos ⟨hX, hB⟩, if_pos (yhAt_gcG i), if_pos hi', yhJ_gcG]

/-- **A fixed point `e = Hᵛ_λ(y)` of `Γ` in `[B₂, B₃)` reads `ϑˣ(Ω₁·(Ω₁ + λ(x)) + c(x))`.** -/
theorem vD_fix {e : Ordinal.{0}} (hA : YhAt e) (hi : ¬ yhJ e < e) (hN : qdI (qdLev e) e < e) (hX : ucB ≤ e)
    (hB : e < qdB) (x : Ordinal.{0}) :
    vD e x = vt x (Om1 * (Om1 + qdLvx e (qdLev e) x) + qdRK (qdLev e) (qdI (qdLev e) e) x) := by
  have hE : InE e := Low.opow_eq_self_of_SC hA.1
  rw [vD_base hE hX hB]
  unfold qdA
  rw [if_pos ⟨hX, hB⟩, if_pos hA, if_neg hi, if_pos hN]

/-- **A non-atom `ε`-number code `e ∈ [B₂, B₃)` reads `ϑˣ(Ω₁·α(x) + η(x))`.** -/
theorem vD_nonAt {e : Ordinal.{0}} (he : InE e) (hA : ¬ YhAt e) (hX : ucB ≤ e) (hB : e < qdB) (x : Ordinal.{0}) :
    vD e x = glA (vD (yhK e) x) (vD (yhI e) x) x := by
  rw [vD_base he hX hB]
  unfold qdA
  rw [if_pos ⟨hX, hB⟩, if_neg hA]

/-- **`vD (b + 1) = vD b + 1`.** -/
theorem vD_succ : ∀ b x : Ordinal.{0}, vD (b + 1) x = vD b x + 1 := by
  intro b
  induction b using WellFoundedLT.induction with
  | ind b IH =>
  intro x
  rcases lt_or_ge b ucB with hbX | hbX
  · have hb1 : b + 1 < ucB := (ev_isSuccLimit_of_inE qd_B2_E).add_one_lt hbX
    rw [vD_low hbX, vD_low hb1, vQ_succ]
  rcases lt_or_ge b qdB with hbB | hbB
  · have hb1B : b + 1 < qdB := qdB_SC.isSuccLimit.add_one_lt hbB
    have hbE := yh_gfE_le (qd_B2_G0.trans hbX)
    obtain ⟨hk, hd0, hdE, -, -, -, hrb, -⟩ := gl_parts hbE
    obtain ⟨e, hr1, hv⟩ := gl_succ_nf hbE
    have hXE := (qd_guE_B hbX hbB).1
    rw [e, vD_cnf (guE_E b) hXE hk hd0 hdE hr1 hv (by rw [← e]; exact hb1B), IH _ hrb x, vD_dec hbX hbB x,
      add_assoc]
  · have hb1 : qdB ≤ b + 1 := hbB.trans le_self_add
    have e1 : vD b x = vQ b x := by rw [vD, dif_neg (fun h => absurd h.2 (not_lt.2 hbB))]
    have e2 : vD (b + 1) x = vQ (b + 1) x := by rw [vD, dif_neg (fun h => absurd h.2 (not_lt.2 hb1))]
    rw [e1, e2, vQ_succ]

end Googology.Trans.PoR.InaccPsi.R2.Qd
