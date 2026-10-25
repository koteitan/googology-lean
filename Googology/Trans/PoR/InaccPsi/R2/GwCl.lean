import Googology.Trans.PoR.InaccPsi.R2.GwEx

/-!
# THE CODE-GATE CONDITION AT THE SECOND `Ω₁`-DIGIT: `φ(1, G + Ω₁·λ)` a code over `Z` ⇒ `λ < Z`

`Gv.gv_cl_tail` reads only the countable tail `r` of a code `Ω₁·q + r < Ω₁²`.  Here the coefficient `q` of `Ω₁` is
read too (`gw_cl_coef`: a code below `Ω₁²` over a strongly critical `Z ≤ Ω₁` has `q < Z`; the only new case is an atom
`ω^{Ω₁+t} = Ω₁·ω^t` with `Ω₁ + t` a code, where `t < Z` by `gv_cl_tail`).  With `gw_cl_of_G_add`: if `φ(1, G + Ω₁·λ)`
is a code over `Z` then `λ < Z` (`gw_cl_coefG`), the code-gate condition of a union whose index has a countable
coefficient `λ` of `Ω₁` (the condition asked by the gated union at the indices `G + Ω₁·λ`, `λ ≥ ε₀`).  In the
recursion `Gw.gwD` the same condition holds for every index through the gate of the index code (`gw_cl_gate`).

* `gw_one_lt_SC`, `gw_OmOm_lt_G`, `gw_cl_coef` (**the coefficient of `Ω₁` in a code below `Ω₁²` is below `Z`**),
  `gw_cl_coefG` (**`φ(1, G + Ω₁·λ)` a code over `Z` ⇒ `λ < Z`**).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gw

open Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Gv
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx

variable {Z : Ordinal.{0}}

theorem gw_one_lt_SC (hZ : SC Z) : 1 < Z := by
  have := hZ.2 0 hZ.1 0 hZ.1
  rwa [veblen_zero_apply, opow_zero] at this

theorem gw_Om_pos : (0 : Ordinal.{0}) < Om 1 := by rw [← Br.Om1_eq]; exact gv_Om1_pos

theorem gw_OmOm_lt_G : Om 1 * Om 1 < gcG 0 :=
  InE.mul_lt (Low.opow_eq_self_of_SC (gcG_SC 0)) (gcG_Om1_lt 0) (gcG_Om1_lt 0)

theorem gw_OmOm_eq : (Om 1 : Ordinal.{0}) * Om 1 = ω ^ (Om 1 + Om 1) := by
  rw [opow_add, Bt.Om1_opow]

/-- **The coefficient of `Ω₁` in a code below `Ω₁²` is below `Z`**: `y = Ω₁·q + r` a code over a strongly critical
`Z ≤ Ω₁` (atom `G`) ⇒ `q < Z`. -/
theorem gw_cl_coef (hZ : SC Z) (hZ1 : Z ≤ Om 1) {y : Ordinal.{0}} (h : GxCl Z {gcG 0} y)
    (hy : y < Om 1 * Om 1) : y / Om 1 < Z := by
  have hO := gw_Om_pos
  have hP : IsPrincipal (· + ·) (Om 1 : Ordinal.{0}) := Fx.fx_Om1_prin
  induction h with
  | @small x hx => rw [Ordinal.div_eq_zero_of_lt (hx.trans_le hZ1)]; exact hZ.1
  | om => rw [Ordinal.div_self hO.ne']; exact gw_one_lt_SC hZ
  | @atom s hs =>
    rw [Set.mem_singleton_iff] at hs
    rw [hs] at hy
    exact absurd (hy.trans gw_OmOm_lt_G) (lt_irrefl _)
  | @add x y _ _ ihx ihy =>
    have hx' : x < Om 1 * Om 1 := lt_of_le_of_lt le_self_add hy
    have hy' : y < Om 1 * Om 1 := lt_of_le_of_lt le_add_self hy
    have h1 := ihx hx'
    have h2 := ihy hy'
    have ex := Ordinal.div_add_mod x (Om 1)
    have ey := Ordinal.div_add_mod y (Om 1)
    have hr1 : x % Om 1 < Om 1 := Ordinal.mod_lt x hO.ne'
    have hr2 : y % Om 1 < Om 1 := Ordinal.mod_lt y hO.ne'
    rcases lt_or_ge y (Om 1) with hyO | hyO
    · have e : x + y = Om 1 * (x / Om 1) + (x % Om 1 + y) := by
        conv_lhs => rw [← ex]
        rw [add_assoc]
      rw [e, Ordinal.mul_add_div _ hO.ne', Ordinal.div_eq_zero_of_lt (hP hr1 hyO), add_zero]
      exact h1
    · have hq : 1 ≤ y / Om 1 := by
        rw [Order.one_le_iff_pos]; exact (Ordinal.div_pos hO.ne').2 hyO
      obtain ⟨b', hb'⟩ := exists_add_of_le hq
      have e1 : x % Om 1 + Om 1 * (1 + b') = Om 1 * (1 + b') := by
        rw [mul_add, mul_one, ← add_assoc, hP.add_eq_right hr1]
      have e : x + y = Om 1 * (x / Om 1 + y / Om 1) + y % Om 1 := by
        conv_lhs => rw [← ex, ← ey]
        rw [hb', ← add_assoc (Om 1 * (x / Om 1) + x % Om 1), add_assoc (Om 1 * (x / Om 1)) (x % Om 1), e1,
          ← mul_add]
      rw [e, Ordinal.mul_add_div _ hO.ne', Ordinal.div_eq_zero_of_lt hr2, add_zero]
      exact hZ.isPrincipal h1 h2
  | @phi a b _ hb _ _ =>
    rcases lt_or_ge (veblen a b) (Om 1) with hv | hv
    · rw [Ordinal.div_eq_zero_of_lt hv]; exact hZ.1
    rcases eq_or_ne a 0 with rfl | ha
    · rw [veblen_zero_apply] at hv hy ⊢
      have hOb : Om 1 ≤ b := by
        rw [← Bt.Om1_opow] at hv
        exact (opow_le_opow_iff_right one_lt_omega0).1 hv
      have hb2 : b < Om 1 + Om 1 := by
        rw [gw_OmOm_eq] at hy
        exact (opow_lt_opow_iff_right one_lt_omega0).1 hy
      obtain ⟨t, rfl⟩ := exists_add_of_le hOb
      have ht : t < Om 1 := (add_lt_add_iff_left _).1 hb2
      obtain ⟨q', r', hr', e⟩ := gv_cl_tail hZ hZ1 gr_GxAt hb
      have htr : t = r' := gv_tail_eq (q := 1) (p := q') ht (hr'.trans_le hZ1) (by rw [mul_one]; exact e)
      rw [opow_add, Bt.Om1_opow, Ordinal.mul_div_cancel _ hO.ne', htr]
      have := hZ.2 0 hZ.1 r' hr'
      rwa [veblen_zero_apply] at this
    · have hE : InE (veblen a b) := gg_veblen_eps ha
      rcases hv.lt_or_eq with hlt | heq
      · exact absurd (InE.mul_lt hE hlt hlt) (not_lt.2 hy.le)
      · rw [← heq, Ordinal.div_self hO.ne']; exact gw_one_lt_SC hZ

/-- **THE CODE-GATE CONDITION AT THE SECOND `Ω₁`-DIGIT**: if `φ(1, G + Ω₁·λ)` (`0 < λ < Ω₁`) is a code over a
strongly critical `Z ≤ Ω₁` (atom `G`), then `λ < Z`. -/
theorem gw_cl_coefG (hZ : SC Z) (hZ1 : Z ≤ Om 1) {l : Ordinal.{0}} (hl0 : 0 < l) (hl : l < Om 1)
    (h : GxCl Z {gcG 0} (veblen 1 (gcG 0 + Om 1 * l))) : l < Z := by
  have hO := gw_Om_pos
  have hlt : Om 1 * l < Om 1 * Om 1 := (mul_lt_mul_iff_right₀ hO).2 hl
  have hc : Om 1 * l < evZ (gcG 0) := (hlt.trans gw_OmOm_lt_G).trans gw_G_lt_Z
  have hc0 : 0 < Om 1 * l := mul_pos hO hl0
  have h1 := gr_cl_veb1 hZ1 ((gcG_Om1_lt 0).trans_le le_self_add) (gw_lt_veb hc0 hc) h
  have h2 := gw_cl_of_G_add hZ hZ1 h1
  have := gw_cl_coef hZ hZ1 h2 hlt
  rwa [Ordinal.mul_div_cancel _ hO.ne'] at this

end Googology.Trans.PoR.InaccPsi.R2.Gw
