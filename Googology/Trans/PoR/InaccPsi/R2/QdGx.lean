import Googology.Trans.PoR.InaccPsi.R2.QdCg
import Googology.Trans.PoR.InaccPsi.R2.QcGx

/-!
# QdGx: THE GATES OF SUMS, POWERS AND VEBLEN VALUES BELOW `B₃`

`Qc.qc_add`, `Qc.qc_div`, `Qc.qc_opow_gate`, `Qc.qc_lam_gate`, `Qc.qc_phi_gate` for `Qd.qdGt`.  Below `B₂` the gate is
`Qc.qcG`; on `[G, B₃)` it has one Cantor clause in the bracket `e = guE c` (`qdGt_dec'`: `Qc.qcG_dec'` below `B₂`,
`Qd.qdGt_dec` from `B₂` on), so the arguments of `Qc.QcGx` go through with every code below `B₃`.

* `qd_G0_lt_B2`, `qdGt_glG`, `qdQEt_atom'`, `qdQEt_psi'`, `qdGt_dec'` (**one Cantor clause on `[G, B₃)`**), `qdGt_cnf'`,
  `qdGt_base'`, `qdGt_atom'`, `qdGt_psi'`, `qd_parts_Q`;
* `qd_add` (**the gate of a sum**), `qd_div`, `qd_opow_gate` (**the gate of `ω^y`**), `qd_lam_gate`, `qd_phi_gate`
  (**the gate of `φ(o, y) ≥ G`**).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Yh Googology.Trans.PoR.InaccPsi.R2.Yr
  Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Va
  Googology.Trans.PoR.InaccPsi.R2.Zm Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Tf
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gf
  Googology.Trans.PoR.InaccPsi.R2.Gn Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Xu
  Googology.Trans.PoR.InaccPsi.R2.Qc

/-! ## One Cantor clause on `[G, B₂)` -/

theorem qd_G0_lt_B2 : gcG 0 < (ucB : Ordinal.{0}) := qc_G0_lt_X.trans uc_X_lt_B

theorem qdGt_glG {c : Ordinal.{0}} (h : c < gcG 0) : qdGt c = glG c := by
  rw [qdGt_low (h.trans qd_G0_lt_B2), qcG_glG h]

theorem qdQEt_atom' {e : Ordinal.{0}} (hB : e < qdB) (hA : YhAt e) (hi : yhJ e < e) : qdQEt e = qdQt (yhJ e) := by
  rcases lt_or_ge e ucB with hX | hX
  · rw [qdQEt_low hX, qcQE_atom' hX hA hi, qdQt_low (hi.trans hX)]
  · exact qdQEt_atom hX hB hA hi

theorem qdQEt_psi' {e : Ordinal.{0}} (he : InE e) (hGe : gcG 0 < e) (hB : e < qdB) (hA : ¬ YhAt e) :
    qdQEt e = max (qdQt (yhK e)) (qdQt (yhI e)) := by
  rcases lt_or_ge e ucB with hX | hX
  · obtain ⟨-, hk, hi, -⟩ := yhData_spec he hGe hA
    rw [qdQEt_low hX, qcQE_psi' he hGe hX hA, qdQt_low (hk.trans hX), qdQt_low (hi.trans hX)]
  · exact qdQEt_psi hX hB hA

/-- **The Cantor clause of `qdGt` on `[G, B₃)`.** -/
theorem qdGt_dec' {c : Ordinal.{0}} (h : gcG 0 ≤ c) (hB : c < qdB) :
    qdGt c = max (max (qdQEt (guE c)) (qdQt (log (guE c) c)))
      (max (qdQt (c / guE c ^ log (guE c) c)) (qdGt (c % guE c ^ log (guE c) c))) := by
  rcases lt_or_ge c ucB with hX | hX
  · obtain ⟨-, -, -, -, -, hkc, hrc, hdc⟩ := gl_parts (yh_gfE_le h)
    have hec := gl_E_le (yh_gfE_le h)
    rw [qdGt_low hX, qcG_dec' h hX, qdQEt_low (hec.trans_lt hX), qdQt_low (hkc.trans hX), qdQt_low (hdc.trans hX),
      qdGt_low (hrc.trans hX)]
  · exact qdGt_dec hX hB

theorem qdGt_cnf' {e j d r : Ordinal.{0}} (he : InE e) (hGe : gcG 0 ≤ e) (hj : j ≠ 0) (hd0 : d ≠ 0) (hde : d < e)
    (hr : r < e ^ j) (hv : e ^ j * d + r < eN e) (hvB : e ^ j * d + r < qdB) :
    qdGt (e ^ j * d + r) = max (max (qdQEt e) (qdQt j)) (max (qdQt d) (qdGt r)) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := gl_cnf he (gl_Om1_lt_G0.trans_le hGe) hj hd0 hde hr hv
  rw [qdGt_dec' (yh_G_le_cnf he hGe hj hd0) hvB, h1, h2, h3, h4]

theorem qdGt_base' {e : Ordinal.{0}} (he : InE e) (hGe : gcG 0 ≤ e) (heB : e < qdB) : qdGt e = qdQEt e := by
  obtain ⟨h1, h2⟩ := gl_base_nf he
  have hE1 : (1 : Ordinal.{0}) < e := lu_one_lt_E he
  have h := qdGt_cnf' he hGe one_ne_zero one_ne_zero hE1 (by rw [opow_one]; exact he.pos) h2
    (by rw [← h1]; exact heB)
  rw [← h1] at h
  rw [h, qdQt_one, qdGt_zero]
  simp

theorem qdGt_atom' {i : Ordinal.{0}} (hi : i < gcG i) (hB : gcG i < qdB) : qdGt (gcG i) = qdQt i := by
  have hE : InE (gcG i) := Low.opow_eq_self_of_SC (gcG_SC i)
  have hi' : yhJ (gcG i) < gcG i := by rw [yhJ_gcG]; exact hi
  rw [qdGt_base' hE (gcG_le zero_le) hB, qdQEt_atom' hB (yhAt_gcG i) hi', yhJ_gcG]

theorem qdGt_psi' {α η : Ordinal.{0}} (hα : 1 ≤ α) (hGe : gcG 0 < yhPsi α η) (hB : yhPsi α η < qdB) :
    qdGt (yhPsi α η) = max (qdQt α) (qdQt η) := by
  obtain ⟨h1, h2⟩ := yhData_eq hα hGe
  rw [qdGt_base' (yhPsi_E hα η) hGe.le hB, qdQEt_psi' (yhPsi_E hα η) hGe hB (yhPsi_notAt hα), h1, h2]

theorem qd_parts_Q {x c : Ordinal.{0}} (h : gcG 0 ≤ c) (hB : c < qdB) (hg : qdGt c < x) :
    qdQEt (guE c) < x ∧ qdQt (log (guE c) c) < x ∧ qdQt (c / guE c ^ log (guE c) c) < x ∧
      qdGt (c % guE c ^ log (guE c) c) < x := by
  rw [qdGt_dec' h hB] at hg
  exact ⟨(le_max_left _ _).trans_lt ((le_max_left _ _).trans_lt hg),
    (le_max_right _ _).trans_lt ((le_max_left _ _).trans_lt hg),
    (le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hg),
    (le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hg)⟩

theorem qd_eN_le_B {e : Ordinal.{0}} (h : e < qdB) : eN e ≤ qdB := eN_le h (Low.opow_eq_self_of_SC qdB_SC)

/-! ## Sums, powers and Veblen values -/

/-- **The gate of a sum below `B₂`**, below every `Z > ω` closed under `+`. -/
theorem qd_add {Z : Ordinal.{0}} (hZ : ∀ u v, u < Z → v < Z → u + v < Z) (hωZ : ω < Z) :
    ∀ x y, x + y < qdB → qdGt x < Z → qdGt y < Z → qdGt (x + y) < Z := by
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro y hxyB hgx hgy
  have hxB : x < qdB := le_self_add.trans_lt hxyB
  have hyB : y < qdB := le_add_self.trans_lt hxyB
  rcases lt_or_ge x (gcG 0) with hxG | hxG
  · rcases lt_or_ge y (gcG 0) with hyG | hyG
    · have hs : x + y < gcG 0 := (inE_indec gl_G0_E).add_lt hxG hyG
      rw [qdGt_glG hxG] at hgx
      rw [qdGt_glG hyG] at hgy
      rw [qdGt_glG hs]
      exact gl_add hZ hωZ x y hs hgx hgy
    · have e : x + y = y := add_of_omega0_opow_le (b := gcG 0) (by rw [yr_G_om]; exact hxG)
        (by rw [yr_G_om]; exact hyG)
      rw [e]; exact hgy
  have hxE := yh_gfE_le hxG
  obtain ⟨hk, hd0, hdE, hr, hdec, -, hrx, hdx⟩ := gl_parts hxE
  obtain ⟨q0n, q0k, q0d, g0r⟩ := qd_parts_Q hxG hxB hgx
  set E := guE x with hEdef
  have hE : InE E := guE_E x
  have hGE : gcG 0 ≤ E := yh_G_le_E hxG
  have hOE : Om1 < E := gl_Om1_lt_G0.trans_le hGE
  have hE1 : (1 : Ordinal.{0}) < E := Lu.lu_one_lt_E hE
  have hnx : E ≤ x := gl_E_le hxE
  set k := log E x with hkdef
  set d := x / E ^ k with hddef
  set r := x % E ^ k with hrdef
  have hxN : x < eN E := gl_lt_eN hxE
  have hxk1 : x < E ^ (k + 1) := (lt_opow_iff_log_lt hE1 (hE.pos.trans_le hnx).ne').2 (lt_add_one _)
  have hk1N : k + 1 < eN E :=
    (ev_isSuccLimit_of_inE (eN_E E)).add_one_lt ((gl_parts hxE).2.2.2.2.2.1.trans hxN)
  have hk1E : E ^ (k + 1) < eN E := gu_pow_lt_eN hE hk1N
  rcases lt_or_ge y (E ^ k) with hyk | hyk
  · have hry : r + y < E ^ k := by
      rw [gu_pow_eq hE] at hr hyk ⊢; exact isPrincipal_add_omega0_opow _ hr hyk
    have e : x + y = E ^ k * d + (r + y) := by rw [← hdec, add_assoc]
    have hrE : r + E ^ k = E ^ k := by
      have := hr; rw [gu_pow_eq hE] at this ⊢; exact add_omega0_opow this
    have hv : E ^ k * d + (r + y) < eN E := by
      rw [← e]
      refine lt_of_lt_of_le ((add_lt_add_iff_left _).2 hyk) (le_trans ?_ hk1E.le)
      rw [← hdec, add_assoc, hrE, opow_add, opow_one, ← mul_add_one]
      exact mul_le_mul_right (add_one_le_of_lt hdE) _
    rw [e, qdGt_cnf' hE hGE hk hd0 hdE hry hv (e ▸ hxyB)]
    exact max_lt (max_lt q0n q0k) (max_lt q0d (IH r hrx y ((add_le_add hrx.le le_rfl).trans_lt hxyB) g0r hgy))
  rcases lt_or_ge y (E ^ (k + 1)) with hyk1 | hyk1
  · have hEk : E ≤ E ^ k := by
      calc E = E ^ (1 : Ordinal.{0}) := (opow_one _).symm
        _ ≤ E ^ k := opow_le_opow_right hE.pos (one_le_iff_ne_zero.2 hk)
    have hyN : y < eN E := hyk1.trans hk1E
    obtain ⟨hEy, hyE⟩ := gl_same hE hOE (hEk.trans hyk) hyN
    have hyG : gcG 0 ≤ y := hGE.trans (hEk.trans hyk)
    have hky : log E y = k := by
      refine le_antisymm ?_ (le_log_of_opow_le hE1 hyk)
      exact Order.lt_add_one_iff.1 ((lt_opow_iff_log_lt hE1 (hE.pos.trans_le (hEk.trans hyk)).ne').1 hyk1)
    obtain ⟨-, hd0', hdE', hr', hdec', -, -, -⟩ := gl_parts hyE
    obtain ⟨-, -, q0d', g0r'⟩ := qd_parts_Q hyG hyB hgy
    rw [hEy, hky] at hd0' hdE' hr' hdec' q0d' g0r'
    set d' := y / E ^ k with hd'def
    set r' := y % E ^ k with hr'def
    have hab : r + E ^ k * d' = E ^ k * d' := by
      rw [gu_pow_eq hE] at hr ⊢
      exact add_of_omega0_opow_le hr (le_mul_of_one_le_right' (one_le_iff_ne_zero.2 hd0'))
    have e : x + y = E ^ k * (d + d') + r' := by
      rw [← hdec, ← hdec', add_assoc, ← add_assoc r, hab, ← add_assoc, ← mul_add]
    have hdd : d + d' < E := (inE_indec hE).add_lt hdE hdE'
    have hv : E ^ k * (d + d') + r' < eN E := by
      rw [← e]
      have h1 : x + y < E ^ (k + 1) := by
        rw [gu_pow_eq hE] at hxk1 hyk1 ⊢; exact isPrincipal_add_omega0_opow _ hxk1 hyk1
      exact h1.trans hk1E
    have hgdd : qdGt (d + d') < Z := IH d hdx d' ((hdd.trans_le hnx).trans hxB) (qdGt_of_Q hωZ q0d)
      (qdGt_of_Q hωZ q0d')
    rw [e, qdGt_cnf' hE hGE hk (by intro h0; exact hd0 (Ordinal.add_eq_zero_iff.1 h0).1) hdd hr' hv (e ▸ hxyB)]
    exact max_lt (max_lt q0n q0k) (max_lt ((qdQt_le _).trans_lt hgdd) g0r')
  · have e : x + y = y := add_of_omega0_opow_le (b := E * (k + 1)) (by rw [← gu_pow_eq hE]; exact hxk1)
      (by rw [← gu_pow_eq hE]; exact hyk1)
    rw [e]; exact hgy

/-- **`y/e` and `y mod e` keep the gate** of a code `y ≥ G` (`e = guE y`), below every `Z > ω`. -/
theorem qd_div {Z : Ordinal.{0}} (hωZ : ω < Z) : ∀ y, gcG 0 ≤ y → y < qdB → qdGt y < Z →
    qdQt (y / guE y) < Z ∧ qdGt (y % guE y) < Z := by
  intro y
  induction y using WellFoundedLT.induction with
  | ind y IH =>
  intro hyG hyB hg
  have hyE := yh_gfE_le hyG
  obtain ⟨ha, hd0, hdE, hr, hdec, -, hry, -⟩ := gl_parts hyE
  obtain ⟨q0n, q0a, q0d, g0r⟩ := qd_parts_Q hyG hyB hg
  set E := guE y with hEdef
  have hE : InE E := guE_E y
  have hGE : gcG 0 ≤ E := yh_G_le_E hyG
  have hOE : Om1 < E := gl_Om1_lt_G0.trans_le hGE
  have hE0 : E ≠ 0 := hE.pos.ne'
  have hyn : y < eN E := gl_lt_eN hyE
  set a := log E y with hadef
  set d := y / E ^ a with hddef
  set r := y % E ^ a with hrdef
  have e1 : 1 + (a - 1) = a := Ordinal.add_sub_cancel_of_le (one_le_iff_ne_zero.2 ha)
  have hsp : E ^ a = E * E ^ (a - 1) := by
    calc E ^ a = E ^ (1 + (a - 1)) := by rw [e1]
      _ = E * E ^ (a - 1) := by rw [opow_add, opow_one]
  have hy : y = E * (E ^ (a - 1) * d) + r := by rw [← hdec, hsp, mul_assoc]
  have hrN : r < eN E := hry.trans hyn
  have hQ1 : ∀ a' : Ordinal.{0}, qdQt (1 + a') = qdQt a' := by
    intro a'
    rcases lt_or_ge a' ω with haω | haω
    · obtain ⟨n, rfl⟩ := lt_omega0.1 haω
      have : (1 : Ordinal.{0}) + n = ((1 + n : ℕ) : Ordinal.{0}) := by push_cast; rfl
      rw [this, qdQt_nat, qdQt_nat]
    · rw [one_add_of_omega0_le haω]
  constructor
  · have hdiv : y / E = E ^ (a - 1) * d + r / E := by rw [hy, Ordinal.mul_add_div _ hE0]
    rcases eq_or_ne (a - 1) 0 with ha1 | ha1
    · have hrE : r < E := by
        have := hr; rw [hsp, ha1, opow_zero, mul_one] at this; exact this
      rw [hdiv, ha1, opow_zero, one_mul, Ordinal.div_eq_zero_of_lt hrE, add_zero]
      exact q0d
    · have hrq : r / E < E ^ (a - 1) := by
        rw [← Ordinal.lt_mul_iff_div_lt hE0, ← hsp]; exact hr
      have hdB : y / E < eN E :=
        lt_of_le_of_lt (Ordinal.div_le_of_le_mul (le_mul_right y hE.pos)) hyn
      have hEq : E ≤ y / E := by
        rw [hdiv]
        calc E = E ^ (1 : Ordinal.{0}) := (opow_one _).symm
          _ ≤ E ^ (a - 1) := opow_le_opow_right hE.pos (one_le_iff_ne_zero.2 ha1)
          _ ≤ E ^ (a - 1) * d := le_mul_of_one_le_right' (one_le_iff_ne_zero.2 hd0)
          _ ≤ _ := le_self_add
      have hdB' : y / E < qdB := lt_of_le_of_lt (Ordinal.div_le_of_le_mul (le_mul_right y hE.pos)) hyB
      have hQ : qdQt (y / E) = qdGt (y / E) := by
        unfold qdQt
        rw [if_neg (not_lt.2 ((omega0_lt_inE hE).le.trans hEq))]
      rw [hQ, hdiv, qdGt_cnf' hE hGE ha1 hd0 hdE hrq (hdiv ▸ hdB) (hdiv ▸ hdB')]
      refine max_lt (max_lt q0n (by rw [← hQ1, e1]; exact q0a)) (max_lt q0d ?_)
      rcases lt_or_ge r E with hrE | hrE
      · rw [Ordinal.div_eq_zero_of_lt hrE, qdGt_zero]; exact (omega0_pos).trans hωZ
      · obtain ⟨hEr, -⟩ := gl_same hE hOE hrE hrN
        have := (IH r hry (hGE.trans hrE) (hry.trans hyB) g0r).1
        rw [hEr] at this
        exact qdGt_of_Q hωZ this
  · have hmod : y % E = r % E := by rw [hy, Ordinal.mul_add_mod_self]
    rw [hmod]
    rcases lt_or_ge r E with hrE | hrE
    · rw [Ordinal.mod_eq_of_lt hrE]; exact g0r
    · obtain ⟨hEr, -⟩ := gl_same hE hOE hrE hrN
      have := (IH r hry (hGE.trans hrE) (hry.trans hyB) g0r).2
      rwa [hEr] at this

/-- **The gate of `ω^y`**, below every `Z > ω` closed under `ω^·`. -/
theorem qd_opow_gate {Z : Ordinal.{0}} (hZw : ∀ u, u < Z → ω ^ u < Z) (hωZ : ω < Z) :
    ∀ y, ω ^ y < qdB → qdGt y < Z → qdGt (ω ^ y) < Z := by
  intro y
  induction y using WellFoundedLT.induction with
  | ind y IH =>
  intro hB hg
  have hyy : y ≤ ω ^ y := right_le_opow y one_lt_omega0
  rcases lt_or_ge (ω ^ y) (gcG 0) with hlt | hge
  · have hy : y < gcG 0 := hyy.trans_lt hlt
    rw [qdGt_glG hy] at hg
    rw [qdGt_glG hlt]
    exact gl_opow_gate hZw hωZ y hlt hg
  set E := guE (ω ^ y) with hEdef
  have hE : InE E := guE_E _
  have hGE : gcG 0 ≤ E := yh_G_le_E hge
  have hOE : Om1 < E := gl_Om1_lt_G0.trans_le hGE
  have hnc : E ≤ ω ^ y := gl_E_le (yh_gfE_le hge)
  have hcn : ω ^ y < eN E := gl_lt_eN (yh_gfE_le hge)
  have hEy : E ≤ y := by
    rw [← show ω ^ E = E from hE] at hnc
    exact (opow_le_opow_iff_right one_lt_omega0).1 hnc
  have hyN : y < eN E := hyy.trans_lt hcn
  obtain ⟨hEy', -⟩ := gl_same hE hOE hEy hyN
  have hyG : gcG 0 ≤ y := hGE.trans hEy
  have hyB : y < qdB := hyy.trans_lt hB
  obtain ⟨g1, g2⟩ := qd_div hωZ y hyG hyB hg
  rw [hEy'] at g1 g2
  obtain ⟨q0n, -, -, -⟩ := qd_parts_Q hyG hyB hg
  rw [hEy'] at q0n
  set q := y / E with hqdef
  set s := y % E with hsdef
  have hsE : s < E := Ordinal.mod_lt y hE.pos.ne'
  have hq0 : q ≠ 0 := ((Ordinal.div_pos hE.pos.ne').2 hEy).ne'
  have hws : ω ^ s < E := by rw [← show ω ^ E = E from hE]; exact (opow_lt_opow_iff_right one_lt_omega0).2 hsE
  have ew : ω ^ y = E ^ q * ω ^ s + 0 := by
    rw [add_zero, gu_pow_eq hE, ← opow_add, Ordinal.div_add_mod]
  have hsy : s < y := hsE.trans_le hEy
  have hgs : qdGt (ω ^ s) < Z := IH s hsy ((hws.trans_le hnc).trans hB) g2
  rw [ew, qdGt_cnf' hE hGE hq0 (opow_ne_zero _ omega0_ne_zero) hws (opow_pos _ hE.pos) (ew ▸ hcn) (ew ▸ hB), qdGt_zero]
  exact max_lt (max_lt q0n g1) (max_lt ((qdQt_le _).trans_lt hgs) (lt_of_le_of_lt zero_le (omega0_pos.trans hωZ)))

/-- The gate of an index from the gate of the argument: `glLam o η = y` gives `qdQt η ≤ qdGt y` (`η` infinite). -/
theorem qd_lam_gate {o η y : Ordinal.{0}} (hη : glLam o η = y) (hηω : ω ≤ η)
    (hlow : o < Om1 → η < Om1 * ω → False) : qdQt η ≤ qdGt y := by
  refine (qdQt_le η).trans ?_
  by_cases hF : glFw o η
  · rw [glLam_of hF] at hη
    rw [← hη]
    exact qdGt_le_succ η
  · rw [glLam_of_not hF] at hη
    have e1 : (1 : Ordinal.{0}) + η = η := one_add_of_omega0_le hηω
    rcases lt_trichotomy o Om1 with hα | hα | hα
    · rw [glY0_lt hα, add_assoc, e1] at hη
      rcases lt_or_ge η (Om1 * ω) with hηΩ | hηΩ
      · exact (hlow hα hηΩ).elim
      · rw [← hη, add_eq_right_iff_mul_omega0_le.2 hηΩ]
    · rw [hα, glY0_eq, e1] at hη
      rw [← hη]
    · rw [glY0_gt hα, zero_add] at hη
      rw [← hη]

/-- **The gate of a Veblen value `φ(o, y) ≥ G` (`1 ≤ o`)**, from the gates of `o` and `y` (every level, the base
atoms included). -/
theorem qd_phi_gate {Z o y : Ordinal.{0}} (hωZ : ω < Z) (ho : o ≠ 0) (hge : gcG 0 ≤ veblen o y)
    (hB : veblen o y < qdB) (hgo : qdGt o < Z) (hgy : qdGt y < Z) : qdGt (veblen o y) < Z := by
  by_cases hfix : veblen o y = y
  · rw [hfix]; exact hgy
  by_cases hAv : YhAt (veblen o y)
  · -- an atom value that is not a fixed point of `φ(o, ·)` is `o` itself
    have hov : o = veblen o y := by
      refine le_antisymm (left_le_veblen o y) (not_lt.1 fun hlt => ?_)
      have hyv : y < veblen o y := lt_of_le_of_ne (right_le_veblen o y) (Ne.symm hfix)
      have := hAv.1.2 o hlt y hyv
      exact lt_irrefl _ this
    rw [← hov]; exact hgo
  have hGv : gcG 0 < veblen o y := lt_of_le_of_ne hge (fun h => hAv (h ▸ yhAt_gcG 0))
  have hOv : Om1 < veblen o y := gl_Om1_lt_G0.trans hGv
  have ho1 : 1 ≤ o := one_le_iff_ne_zero.2 ho
  have hyP : ¬ LuP (o + 1) y := fun h => hfix (luP_succ.1 h)
  have hy0 : glY0 o ≤ y := by
    rcases lt_trichotomy o Om1 with hα | hα | hα
    · rw [glY0_lt hα]
      refine add_one_le_of_lt ?_
      by_contra hc
      push Not at hc
      have := (veblen_le_veblen_iff_right (o := o)).2 hc
      rw [gl_veb_Om1 hα] at this
      exact absurd hOv (not_lt.2 this)
    · rw [hα, glY0_eq, one_le_iff_ne_zero]
      intro h0
      rw [h0, hα, gl_veb_Om1_zero] at hOv
      exact lt_irrefl _ hOv
    · rw [glY0_gt hα]; exact zero_le
  obtain ⟨η, hη⟩ := glLam_surj hy0 hyP
  have hpsi : veblen o y = glPsi o η := by unfold glPsi; rw [hη]
  have hlow : o < Om1 → η < Om1 * ω → False := by
    intro hα hηΩ
    have hOω : Om1 * ω < gcG 0 := gl_G0_E.mul_lt gl_Om1_lt_G0 (omega_lt_Om1.trans gl_Om1_lt_G0)
    have hyG : y < gcG 0 := by
      rw [← hη]
      unfold glLam
      split_ifs
      · exact gl_G0_lim.add_one_lt (hηΩ.trans hOω)
      · rw [glY0_lt hα]
        exact (inE_indec gl_G0_E).add_lt (gl_G0_lim.add_one_lt gl_Om1_lt_G0) (hηΩ.trans hOω)
    exact absurd hGv (not_lt.2 (gl_veb_lt_G0 (hα.trans gl_Om1_lt_G0) hyG).le)
  have hQη : qdQt η ≤ qdGt y := by
    by_cases hηω : η < ω
    · unfold qdQt; rw [if_pos hηω]; exact zero_le
    · exact qd_lam_gate hη (not_lt.1 hηω) hlow
  by_cases hoA : YhAt o
  · -- a base-atom level: `η = 1 + η'`
    have hη0 : η ≠ 0 := by
      intro h0
      rw [h0] at hpsi
      have : glPsi o 0 = o := by
        unfold glPsi
        rw [glLam_of_not (glFw_zero _), glY0_gt hoA.2, add_zero, yhAt_veb0 hoA]
      rw [hpsi, this] at hAv
      exact hAv hoA
    have e1 : 1 + (η - 1) = η := Ordinal.add_sub_cancel_of_le (one_le_iff_ne_zero.2 hη0)
    have hp' : veblen o y = yhPsi o (η - 1) := by rw [yhPsi_at hoA, e1, hpsi]
    rw [hp', qdGt_psi' ho1 (hp' ▸ hGv) (hp' ▸ hB)]
    refine max_lt ((qdQt_le o).trans_lt hgo) ?_
    rcases lt_or_ge η ω with hηω | hηω
    · have : η - 1 < ω := (le_add_self.trans_eq e1).trans_lt hηω
      unfold qdQt; rw [if_pos this]; exact omega0_pos.trans hωZ
    · have : η - 1 = η := by
        have h2 : ω ≤ η - 1 := by
          by_contra hc
          push Not at hc
          obtain ⟨n, hn⟩ := lt_omega0.1 hc
          have : η < ω := by
            rw [← e1, hn]
            exact_mod_cast natCast_lt_omega0 (1 + n)
          exact absurd hηω (not_le.2 this)
        rw [← one_add_of_omega0_le h2, e1]
      rw [this]; exact hQη.trans_lt hgy
  · rw [hpsi, ← yhPsi_ne hoA, qdGt_psi' ho1 (by rw [yhPsi_ne hoA, ← hpsi]; exact hGv)
      (by rw [yhPsi_ne hoA, ← hpsi]; exact hB)]
    exact max_lt ((qdQt_le o).trans_lt hgo) (hQη.trans_lt hgy)

end Googology.Trans.PoR.InaccPsi.R2.Qd
