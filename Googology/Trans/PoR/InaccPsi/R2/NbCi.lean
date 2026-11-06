import Googology.Trans.PoR.InaccPsi.R2.NbCg

/-!
# Nb: THE GLOBAL GATE BOUND ABOVE A PSEUDO-BASE (`Zm.zmHG_gate` over any `P`)

`P = φ(2, p)`, `M₀` the base of the chain (`Nb.NbBase`).

* `nbBase_Ei` (`M₀.Ei = P`), `nbP_cl` (**`P` is a code over every `Z` above the base gate**);
* `nbHG_gate` (**a code `c < Z_P = φ(2, p+1)` of `TlCl Z` (`Z ≤ Ω₁` strongly critical above the base gate) has global
  gate below `Z`**; `Zm.zm_cl_eps`, `Zm.zm_cl_veb1` are generic).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Nb

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Zm Googology.Trans.PoR.InaccPsi.R2.Tl

section Gate

variable {M₀ : ZmDS} {p : Ordinal.{0}} {b : Ordinal.{0} → Ordinal.{0}} (hM₀ : NbBase M₀ p b)
include hM₀

theorem nbBase_Ei : M₀.Ei = veblen 2 p := by
  have h : veblen 1 M₀.Ei = veblen 1 (veblen 2 p) := by rw [M₀.E_eq, hM₀.E_eq, nb_fixP]
  exact (isNormal_veblen 1).strictMono.injective h

theorem nbP_cl {Z : Ordinal.{0}} (hZ : SC Z) (hgZ : M₀.Eg < Z) : TlCl Z (veblen 2 p) := by
  have h := M₀.Ei_cl Z hZ hgZ; rwa [nbBase_Ei hM₀] at h

/-- **THE GLOBAL GATE BOUND ABOVE `P`.** -/
theorem nbHG_gate {Z : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om1) (hgZ : M₀.Eg < Z) :
    ∀ c, c < veblen 2 (p + 1) → TlCl Z c → nbHG p M₀.G c < Z := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hcZ hC
  rcases lt_or_ge c (veblen 2 p) with hcB | hcB
  · rw [nbHG_lt hcB]; exact M₀.gate c Z hZ hZ1 hgZ (hM₀.E_eq ▸ hcB) hC
  obtain ⟨b1, b2, b3⟩ := nb_bracket hcB hcZ
  set n := nbN p c with hn
  have hEeq := nbBE_eq b1 b2
  set E := nbBE p c with hEdef
  have hEE : InE E := by rw [hEeq]; exact zm_veb_E _
  have hEc : E ≤ c := hEeq ▸ b1
  have hcN : c < eN E := by rw [hEeq, Go.go_eN_veb, add_assoc]; exact b2
  have hEC : TlCl Z E := zm_cl_eps c hC E hEE hEc hcN
  -- the index
  have hnG : nbHG p M₀.G n < Z := by
    rcases eq_or_ne n 0 with h0 | h0
    · rw [h0, nbHG_lt (nbP_pos p), M₀.G0]; exact hZ.1
    · have hBE : veblen 2 p < E := by
        rw [hEeq]; conv_lhs => rw [← nb_fixP p]
        exact (isNormal_veblen 1).strictMono (lt_add_of_pos_right _ (pos_iff_ne_zero.2 h0))
      have hnf : veblen 1 E ≠ E := nb_noFix hBE (hEc.trans_lt hcZ)
      have h1 := zm_cl_veb1 E hEC hnf (veblen 2 p + n) hEeq.symm
      have h2 := (tlDec hZ _ h1).1 _ (nbP_cl hM₀ hZ hgZ) le_self_add
      rw [Ordinal.add_sub_cancel] at h2
      exact IH n b3 (b3.trans hcZ) h2
  -- the exponent, the digit and the rest
  obtain ⟨hk0, hd0, hdE, hrk, hdec⟩ := zm_dec hEE hEc
  have hko : log E c < c := zm_log_lt hEE hEc hcN
  have hro : c % E ^ log E c < c := zm_mod_lt hEE hEc
  have hdo : c / E ^ log E c < c := hdE.trans_le hEc
  set k := log E c with hkdef
  set d := c / E ^ k with hddef
  set r := c % E ^ k with hrdef
  have hEω : ω ^ E = E := hEE
  have hP : E ^ k = ω ^ (E * k) := zm_opow_eq hEE k
  have hlog : log ω c = E * k + log ω d := by
    rw [← hdec, hP]; exact log_opow_mul_add one_lt_omega0 hd0.ne' (hP ▸ hrk)
  have hlogC : TlCl Z (log ω c) := (tlDec hZ c hC).2
  have hld : log ω d < E := (log_le_self ω d).trans_lt hdE
  have hkC : TlCl Z k := by
    have h := (zm_cl_divOp hZ hEC (log ω c) hlogC).1
    rw [hlog, hEω, Ordinal.mul_add_div _ hEE.pos.ne', Ordinal.div_eq_zero_of_lt hld, add_zero] at h
    exact h
  have hPC : TlCl Z (E * k) := by
    have h := tl_cl_opow_mul hZ hEC _ hkC; rwa [hEω] at h
  obtain ⟨hdC, hrC⟩ := zm_cl_divOp hZ hPC c hC
  rw [← hP, ← hdec, Ordinal.mul_add_div _ (opow_pos _ hEE.pos).ne', Ordinal.div_eq_zero_of_lt hrk,
    add_zero] at hdC
  rw [← hP, ← hdec, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hrk] at hrC
  rw [nbHG_cnf hcB hcZ]
  exact max_lt hnG (max_lt (IH k hko (hko.trans hcZ) hkC)
    (max_lt (IH d hdo (hdo.trans hcZ) hdC) (IH r hro (hro.trans hcZ) hrC)))

end Gate

end Googology.Trans.PoR.InaccPsi.R2.Nb
