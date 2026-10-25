import Googology.Trans.PoR.InaccPsi.R2.GsWall

/-!
# THE COUNTABLE TAIL OF A CODE: the code-gate condition for every index `P + j + l`

A code over a strongly critical `Z ≤ Ω₁` (atoms strongly critical above `Ω₁`) is `Ω₁·q + r` with `r < Z`
(`gv_cl_tail`): the countable members are below `Z` (`GxCl.lt_of_lt_Om1`), the atoms and every additive principal
member `≥ Ω₁` are multiples of `Ω₁`, and sums keep the form.  Hence: if `φ(1, P + j + l)` is a code over `Z` (atom
`G`), `Ω₁ ∣ P`, `Ω₁ ≤ P`, `j < Ω₁`, `0 < l < Ω₁`, then `l < Z` (`gv_cl_l`).  This is the code-gate condition
(`Gs.GsD.γ_cl`) of a union with base gate `l` at an index `P + j + l` (in `R2.GsLim` only `P + j = G`, `Gr.gr_cl_Bl`).

* `gv_Om1_dvd_opow`, `gv_cl_tail`, `gv_tail_eq`, `gv_cl_l`.

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gv

open Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gc
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx

variable {Z : Ordinal.{0}}

theorem gv_Om1_dvd_opow {e : Ordinal.{0}} (h : Om 1 ≤ ω ^ e) : Om 1 ∣ ω ^ e := by
  have he : Om 1 ≤ e := by
    by_contra hlt
    push Not at hlt
    have := (opow_lt_opow_iff_right one_lt_omega0).2 hlt
    rw [Bt.Om1_opow] at this
    exact absurd h (not_le.2 this)
  have := opow_dvd_opow ω he
  rwa [Bt.Om1_opow] at this

/-- **The countable tail of a code is below `Z`**: every code is `Ω₁·q + r`, `r < Z`. -/
theorem gv_cl_tail (hZ : SC Z) (hZ1 : Z ≤ Om 1) {At : Set Ordinal.{0}} (hAt : GxAt At) {c : Ordinal.{0}}
    (h : GxCl Z At c) : ∃ q r, r < Z ∧ c = Om 1 * q + r := by
  induction h with
  | @small x hx => exact ⟨0, x, hx, by rw [mul_zero, zero_add]⟩
  | om => exact ⟨1, 0, hZ.1, by rw [mul_one, add_zero]⟩
  | @atom s hs =>
    obtain ⟨hsS, hsO⟩ := hAt s hs
    have e : ω ^ s = s := Low.opow_eq_self_of_SC hsS
    obtain ⟨q, hq⟩ := gv_Om1_dvd_opow (e.symm ▸ hsO.le : Om 1 ≤ ω ^ s)
    exact ⟨q, 0, hZ.1, by rw [add_zero, ← hq, e]⟩
  | @add x y _ _ ihx ihy =>
    obtain ⟨a, r, hr, rfl⟩ := ihx
    obtain ⟨b, s, hs, rfl⟩ := ihy
    rcases eq_or_ne b 0 with rfl | hb
    · exact ⟨a, r + s, hZ.isPrincipal hr hs, by rw [mul_zero, zero_add, add_assoc]⟩
    · obtain ⟨b', rfl⟩ := exists_add_of_le (Order.one_le_iff_ne_zero.2 hb)
      have hrO : r < Om 1 := hr.trans_le hZ1
      refine ⟨a + (1 + b'), s, hs, ?_⟩
      have e1 : r + Om 1 * (1 + b') = Om 1 * (1 + b') := by
        rw [mul_add, mul_one, ← add_assoc, Fx.fx_Om1_prin.add_eq_right hrO]
      rw [mul_add (Om 1) a, ← add_assoc (Om 1 * a + r), add_assoc (Om 1 * a) r, e1]
  | @phi x y hx hy _ _ =>
    have hxy : GxCl Z At (veblen x y) := GxCl.phi hx hy
    rcases lt_or_ge (veblen x y) (Om 1) with hv | hv
    · exact ⟨0, veblen x y, GxCl.lt_of_lt_Om1 hZ hAt hxy hv, by rw [mul_zero, zero_add]⟩
    · obtain ⟨e, he⟩ := Bt.prin_eq_opow (gr_veb_prin x y) veblen_pos.ne'
      rw [he] at hv
      obtain ⟨q, hq⟩ := gv_Om1_dvd_opow hv
      exact ⟨q, 0, hZ.1, by rw [add_zero, he, hq]⟩

/-- `Ω₁·q + r = Ω₁·p + s` with `r, s < Ω₁` gives `r = s`. -/
theorem gv_tail_eq {q r p s : Ordinal.{0}} (hr : r < Om 1) (hs : s < Om 1) (h : Om 1 * q + r = Om 1 * p + s) :
    r = s := by
  have h1 := congrArg (· % Om 1) h
  simp only [Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hr, Ordinal.mod_eq_of_lt hs] at h1
  exact h1

/-- **THE CODE-GATE CONDITION AT AN INDEX `P + j + l`**: if `φ(1, P + j + l)` is a code over a strongly critical
`Z ≤ Ω₁` (atom `G`), `Ω₁ ∣ P`, `Ω₁ ≤ P`, `j < Ω₁` and `0 < l < Ω₁`, then `l < Z`. -/
theorem gv_cl_l (hZ : SC Z) (hZ1 : Z ≤ Om 1) {P j l : Ordinal.{0}} (hP : Om 1 ∣ P) (hPO : Om 1 ≤ P)
    (hj : j < Om 1) (hl0 : l ≠ 0) (hl : l < Om 1) (h : GxCl Z {gcG 0} (veblen 1 (P + j + l))) : l < Z := by
  have hjl : j + l < Om 1 := Fx.fx_Om1_prin hj hl
  have hlt : P < P + j + l := by
    rw [add_assoc]; exact lt_add_of_pos_right _ ((pos_iff_ne_zero.2 hl0).trans_le le_add_self)
  have hOt : Om 1 < P + j + l := hPO.trans_lt hlt
  have ht : P + j + l < veblen 1 (P + j + l) := by
    rcases (right_le_veblen 1 (P + j + l)).lt_or_eq with h1 | h1
    · exact h1
    · exfalso
      have hp := gr_veb_prin 1 (P + j + l)
      rw [← h1] at hp
      have := hp hlt ((hjl.trans_le hPO).trans hlt)
      rw [add_assoc] at this
      exact lt_irrefl _ this
  have hc := gr_cl_veb1 hZ1 hOt ht h
  obtain ⟨q, r, hr, e⟩ := gv_cl_tail hZ hZ1 gr_GxAt hc
  obtain ⟨p, rfl⟩ := hP
  rw [add_assoc] at e
  have := gv_tail_eq (hr.trans_le hZ1) hjl e.symm
  rw [this] at hr
  exact le_add_self.trans_lt hr

end Googology.Trans.PoR.InaccPsi.R2.Gv
