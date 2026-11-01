import Googology.Trans.PoR.InaccPsi.R2.XuPi

/-!
# XuGate: CODES BELOW `Γ(1)`: gates of sums, powers and Veblen values, the code gate, hulls

The argument of `R2.GlR5` with the brackets `e ≥ t₀`; below `t₀` the fields `g_add`, `g_opow`, `code_gate`, `mem` of
`Wt.wtD`.

* `xu_add` (**the gate of a sum**), `xu_div`, `xu_opow_gate` (**the gate of `ω^y`**), `xu_phi_gate` (**the gate of
  `φ(o, y) ≥ t₀`, `1 ≤ o`**, the level `G` included), `xu_code_gate` (**a code `c < Γ(1)` in the closure of a
  strongly critical `Z ≤ Ω₁` and the atom `G` has its gate below `Z`**);
* `xu_mem` (**every code lies in every hull `C(a, b)`, `0 < a`, containing its gate**, jointly with `ω^e·c`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Xu

open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2 Googology.Notation.InaccPsi
  Googology.Notation.InaccPsi.InaccSeq Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Gn
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Wt Googology.Trans.PoR.InaccPsi.R2.Gk
  Googology.Trans.PoR.InaccPsi.R2.Gh Googology.Trans.PoR.InaccPsi.R2.Gi Googology.Trans.PoR.InaccPsi.R2.Gm
  Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Hi Googology.Trans.PoR.InaccPsi.R2.Mx

theorem xu_t0_om : ω ^ Wj.wjT 0 = Wj.wjT 0 := xu_t0_E

theorem xu_t0_indec : ∀ u v, u < Wj.wjT 0 → v < Wj.wjT 0 → u + v < Wj.wjT 0 :=
  fun _ _ hu hv => (inE_indec xu_t0_E).add_lt hu hv

/-- **The gate of a sum** of codes below `Γ(1)`, below every `Z > ω` closed under `+`. -/
theorem xu_add {Z : Ordinal.{0}} (hZ : ∀ u v, u < Z → v < Z → u + v < Z) (hωZ : ω < Z) :
    ∀ x y, x + y < gcG 1 → xuG x < Z → xuG y < Z → xuG (x + y) < Z := by
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro y hxy hgx hgy
  have hxB : x < gcG 1 := lt_of_le_of_lt le_self_add hxy
  have hyB : y < gcG 1 := lt_of_le_of_lt le_add_self hxy
  rcases lt_or_ge x (Wj.wjT 0) with hxt | hxt
  · rcases lt_or_ge y (Wj.wjT 0) with hyt | hyt
    · rw [xuG_low hxt] at hgx
      rw [xuG_low hyt] at hgy
      rw [xuG_low (xu_t0_indec x y hxt hyt)]
      exact wtD.g_add Z hZ hωZ x y (xu_lt_wtB (xu_t0_indec x y hxt hyt)) hgx hgy
    · have e : x + y = y := add_of_omega0_opow_le (b := Wj.wjT 0) (by rw [xu_t0_om]; exact hxt)
        (by rw [xu_t0_om]; exact hyt)
      rw [e]; exact hgy
  have hxE := xu_gfE_le hxt
  obtain ⟨hk, hd0, hdE, hr, hdec, -, hrx, hdx⟩ := gl_parts hxE
  obtain ⟨q0n, q0k, q0d, g0r⟩ := xu_parts_Q hxt hxB hgx
  set E := guE x with hEdef
  have hE : InE E := guE_E x
  have hEt : Wj.wjT 0 ≤ E := xu_E_ge hxt
  have hOE : Om1 < E := xu_Om1_lt_t0.trans_le hEt
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
    have hrB : r + y < gcG 1 := lt_of_le_of_lt (add_le_add hrx.le le_rfl) hxy
    rw [e, xuG_cnf hE hEt hk hd0 hdE hry hv (e ▸ hxy)]
    exact max_lt (max_lt q0n q0k) (max_lt q0d (IH r hrx y hrB g0r hgy))
  rcases lt_or_ge y (E ^ (k + 1)) with hyk1 | hyk1
  · have hEk : E ≤ E ^ k := by
      calc E = E ^ (1 : Ordinal.{0}) := (opow_one _).symm
        _ ≤ E ^ k := opow_le_opow_right hE.pos (one_le_iff_ne_zero.2 hk)
    have hyN : y < eN E := hyk1.trans hk1E
    obtain ⟨hEy, hyE⟩ := gl_same hE hOE (hEk.trans hyk) hyN
    have hyt : Wj.wjT 0 ≤ y := hEt.trans (hEk.trans hyk)
    have hky : log E y = k := by
      refine le_antisymm ?_ (le_log_of_opow_le hE1 hyk)
      exact Order.lt_add_one_iff.1 ((lt_opow_iff_log_lt hE1 (hE.pos.trans_le (hEk.trans hyk)).ne').1 hyk1)
    obtain ⟨-, hd0', hdE', hr', hdec', -, -, -⟩ := gl_parts hyE
    obtain ⟨-, -, q0d', g0r'⟩ := xu_parts_Q hyt hyB hgy
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
    have hdB : d + d' < gcG 1 := hdd.trans ((gl_E_le hxE).trans_lt hxB)
    have hgdd : xuG (d + d') < Z :=
      IH d hdx d' hdB (xuG_of_Q hωZ q0d) (xuG_of_Q hωZ q0d')
    rw [e, xuG_cnf hE hEt hk (by intro h0; exact hd0 (Ordinal.add_eq_zero_iff.1 h0).1) hdd hr' hv (e ▸ hxy)]
    exact max_lt (max_lt q0n q0k) (max_lt ((xuQ_le _).trans_lt hgdd) g0r')
  · have e : x + y = y := add_of_omega0_opow_le (b := E * (k + 1)) (by rw [← gu_pow_eq hE]; exact hxk1)
      (by rw [← gu_pow_eq hE]; exact hyk1)
    rw [e]; exact hgy

/-- **`y/e` and `y mod e` keep the gate** of a code `y ≥ t₀` (`e = guE y`), below every `Z > ω`. -/
theorem xu_div {Z : Ordinal.{0}} (hωZ : ω < Z) : ∀ y, Wj.wjT 0 ≤ y → y < gcG 1 → xuG y < Z →
    xuQ (y / guE y) < Z ∧ xuG (y % guE y) < Z := by
  intro y
  induction y using WellFoundedLT.induction with
  | ind y IH =>
  intro hyt hyB hg
  have hyE := xu_gfE_le hyt
  obtain ⟨ha, hd0, hdE, hr, hdec, -, hry, -⟩ := gl_parts hyE
  obtain ⟨q0n, q0a, q0d, g0r⟩ := xu_parts_Q hyt hyB hg
  set E := guE y with hEdef
  have hE : InE E := guE_E y
  have hEt : Wj.wjT 0 ≤ E := xu_E_ge hyt
  have hOE : Om1 < E := xu_Om1_lt_t0.trans_le hEt
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
  have hrB : r < gcG 1 := hry.trans hyB
  have hrN : r < eN E := hry.trans hyn
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
      have hQ : xuQ (y / E) = xuG (y / E) := by
        unfold xuQ
        rw [if_neg (not_lt.2 ((omega0_lt_inE hE).le.trans hEq))]
      have hdivB : y / E < gcG 1 := hdB.trans_le (eN_le ((gl_E_le hyE).trans_lt hyB) xu_G1_E)
      rw [hQ, hdiv, xuG_cnf hE hEt ha1 hd0 hdE hrq (hdiv ▸ hdB) (hdiv ▸ hdivB)]
      refine max_lt (max_lt q0n (by rw [← xuQ_one_add, e1]; exact q0a)) (max_lt q0d ?_)
      rcases lt_or_ge r E with hrE | hrE
      · rw [Ordinal.div_eq_zero_of_lt hrE, xuG_zero]; exact (omega0_pos).trans hωZ
      · obtain ⟨hEr, -⟩ := gl_same hE hOE hrE hrN
        have := (IH r hry (hEt.trans hrE) hrB g0r).1
        rw [hEr] at this
        exact xuG_of_Q hωZ this
  · have hmod : y % E = r % E := by rw [hy, Ordinal.mul_add_mod_self]
    rw [hmod]
    rcases lt_or_ge r E with hrE | hrE
    · rw [Ordinal.mod_eq_of_lt hrE]; exact g0r
    · obtain ⟨hEr, -⟩ := gl_same hE hOE hrE hrN
      have := (IH r hry (hEt.trans hrE) hrB g0r).2
      rwa [hEr] at this

/-- **The gate of `ω^y`** for a code `y` with `ω^y < Γ(1)`, below every `Z > ω` closed under `ω^·`. -/
theorem xu_opow_gate {Z : Ordinal.{0}} (hZw : ∀ u, u < Z → ω ^ u < Z) (hωZ : ω < Z) :
    ∀ y, ω ^ y < gcG 1 → xuG y < Z → xuG (ω ^ y) < Z := by
  intro y
  induction y using WellFoundedLT.induction with
  | ind y IH =>
  intro hyB hg
  have hyy : y ≤ ω ^ y := right_le_opow y one_lt_omega0
  rcases lt_or_ge (ω ^ y) (Wj.wjT 0) with hlt | hge
  · have hy : y < Wj.wjT 0 := hyy.trans_lt hlt
    rw [xuG_low hy] at hg
    rw [xuG_low hlt]
    exact wtD.g_opow Z hZw hωZ y (xu_lt_wtB hlt) hg
  set E := guE (ω ^ y) with hEdef
  have hE : InE E := guE_E _
  have hEt : Wj.wjT 0 ≤ E := xu_E_ge hge
  have hOE : Om1 < E := xu_Om1_lt_t0.trans_le hEt
  have hnc : E ≤ ω ^ y := gl_E_le (xu_gfE_le hge)
  have hcn : ω ^ y < eN E := gl_lt_eN (xu_gfE_le hge)
  have hEy : E ≤ y := by
    rw [← show ω ^ E = E from hE] at hnc
    exact (opow_le_opow_iff_right one_lt_omega0).1 hnc
  have hyN : y < eN E := hyy.trans_lt hcn
  obtain ⟨hEy', -⟩ := gl_same hE hOE hEy hyN
  have hyt : Wj.wjT 0 ≤ y := hEt.trans hEy
  have hyB' : y < gcG 1 := hyy.trans_lt hyB
  obtain ⟨g1, g2⟩ := xu_div hωZ y hyt hyB' hg
  rw [hEy'] at g1 g2
  obtain ⟨q0n, -, -, -⟩ := xu_parts_Q hyt hyB' hg
  rw [hEy'] at q0n
  set q := y / E with hqdef
  set s := y % E with hsdef
  have hsE : s < E := Ordinal.mod_lt y hE.pos.ne'
  have hq0 : q ≠ 0 := ((Ordinal.div_pos hE.pos.ne').2 hEy).ne'
  have hws : ω ^ s < E := by rw [← show ω ^ E = E from hE]; exact (opow_lt_opow_iff_right one_lt_omega0).2 hsE
  have ew : ω ^ y = E ^ q * ω ^ s + 0 := by
    rw [add_zero, gu_pow_eq hE, ← opow_add, Ordinal.div_add_mod]
  have hsy : s < y := hsE.trans_le hEy
  have hEB : E < gcG 1 := hnc.trans_lt hyB
  have hgs : xuG (ω ^ s) < Z := IH s hsy (hws.trans hEB) g2
  rw [ew, xuG_cnf hE hEt hq0 (opow_ne_zero _ omega0_ne_zero) hws (opow_pos _ hE.pos) (ew ▸ hcn) (ew ▸ hyB),
    xuG_zero]
  exact max_lt (max_lt q0n g1) (max_lt ((xuQ_le _).trans_lt hgs) (lt_of_le_of_lt zero_le (omega0_pos.trans hωZ)))

/-- The gate of an index from the gate of the argument: `glLam o η = y` gives `xuQ η ≤ xuG y` (`η` infinite). -/
theorem xu_lam_gate {o η y : Ordinal.{0}} (hη : glLam o η = y) (hηω : ω ≤ η) (hyB : y < gcG 1)
    (hlow : o < Om1 → η < Om1 * ω → False) : xuQ η ≤ xuG y := by
  have hηB : η < gcG 1 := (glLam_ge o η).trans_lt (hη ▸ hyB)
  refine (xuQ_le η).trans ?_
  by_cases hF : glFw o η
  · rw [glLam_of hF] at hη
    rw [← hη]
    rcases lt_or_ge (η + 1) (gcG 1) with h | h
    · exact xuG_le_succ η h
    · exact absurd (hη ▸ hyB) (not_lt.2 h)
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

/-- **The gate of a Veblen value `φ(o, y) ≥ t₀` (`1 ≤ o`)** below `Γ(1)`, from the gates of `o` and `y`. -/
theorem xu_phi_gate {Z o y : Ordinal.{0}} (hωZ : ω < Z) (ho : o ≠ 0) (hge : Wj.wjT 0 ≤ veblen o y)
    (hB : veblen o y < gcG 1) (hgo : xuG o < Z) (hgy : xuG y < Z) : xuG (veblen o y) < Z := by
  have hyB : y < gcG 1 := lt_of_le_of_lt (right_le_veblen o y) hB
  have hoB : o < gcG 1 := lt_of_le_of_lt (left_le_veblen o y) hB
  have hOv : Om1 < veblen o y := xu_Om1_lt_t0.trans_le hge
  have hGv : gcG 0 < veblen o y := xu_G_lt_t0.trans_le hge
  by_cases hfix : veblen o y = y
  · rw [hfix]; exact hgy
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
  have hηB : η < gcG 1 := (glLam_ge o η).trans_lt (hη ▸ hyB)
  have hpsi : veblen o y = glPsi o η := by unfold glPsi; rw [hη]
  -- the low case of `Gl`: `o < Ω₁` and `η < Ω₁·ω` would put `φ(o, y)` below `G`
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
  have hQη : xuQ η ≤ xuG y := by
    by_cases hηω : η < ω
    · unfold xuQ; rw [if_pos hηω]; exact zero_le
    · exact xu_lam_gate hη (not_lt.1 hηω) hyB hlow
  by_cases hoG : o = gcG 0
  · -- the level `G`: `η = 1 + η'`
    have hη0 : η ≠ 0 := by
      intro h0
      rw [h0, hoG] at hpsi
      have : glPsi (gcG 0) 0 = gcG 0 := by
        unfold glPsi
        rw [glLam_of_not (glFw_zero _), glY0_gt gl_Om1_lt_G0, add_zero, Xf.xf_sc_veb0 (gcG_SC 0)]
      rw [hoG, hpsi, this] at hGv
      exact lt_irrefl _ hGv
    have e1 : 1 + (η - 1) = η := Ordinal.add_sub_cancel_of_le (one_le_iff_ne_zero.2 hη0)
    have hη'B : η - 1 < gcG 1 := (le_add_self.trans_eq e1).trans_lt hηB
    have hp' : veblen o y = xuPsi (gcG 0) (η - 1) := by rw [xuPsi_G, e1, hpsi, hoG]
    rw [hp', xuG_psi (by rw [← hoG]; exact ho1) xu_G0_lt_G1 hη'B (hp' ▸ hge)]
    refine max_lt ?_ ?_
    · unfold xuQ; rw [if_neg (not_lt.2 (omega0_lt_inE gl_G0_E).le), xuG_G]; exact omega0_pos.trans hωZ
    · rcases lt_or_ge η ω with hηω | hηω
      · have : η - 1 < ω := (le_add_self.trans_eq e1).trans_lt hηω
        unfold xuQ; rw [if_pos this]; exact omega0_pos.trans hωZ
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
  · rw [hpsi, ← xuPsi_ne hoG, xuG_psi ho1 hoB hηB (by rw [xuPsi_ne hoG, ← hpsi]; exact hge)]
    exact max_lt ((xuQ_le o).trans_lt hgo) (hQη.trans_lt hgy)

/-- **The gate of a code `c < Γ(1)` over a strongly critical `Z ≤ Ω₁` and the atom `G` is below `Z`.** -/
theorem xu_code_gate {Z : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om1) :
    ∀ c, GxCl Z {gcG 0} c → c < gcG 1 → xuG c < Z := by
  have hZa : ∀ u v, u < Z → v < Z → u + v < Z := fun u v hu hv => hZ.isPrincipal hu hv
  have hZp : ∀ u v, u < Z → v < Z → veblen u v < Z := fun u v hu hv => hZ.2 u hu v hv
  have hZw : ∀ u, u < Z → ω ^ u < Z := fun u hu => by
    have := hZp 0 u hZ.1 hu; rwa [veblen_zero_apply] at this
  have hωZ : ω < Z := by
    have h1 := hZw 0 hZ.1; rw [opow_zero] at h1
    have := hZw 1 h1; rwa [opow_one] at this
  have hlow : ∀ x, GxCl Z {gcG 0} x → x < Wj.wjT 0 → xuG x < Z := fun x hx h => by
    rw [xuG_low h]
    exact wtD.code_gate Z hZ1 hZ.1 hZa hZp {gcG 0} (fun s hs => Or.inl hs) x hx (xu_lt_wtB h)
  intro c hc
  induction hc with
  | @small x h => exact fun _ => hlow _ (GxCl.small h) ((h.trans_le hZ1).trans xu_Om1_lt_t0)
  | om => exact fun _ => hlow _ GxCl.om (by rw [← Br.Om1_eq]; exact xu_Om1_lt_t0)
  | @atom s hs => exact fun _ => hlow _ (GxCl.atom hs) (by rw [hs]; exact xu_G_lt_t0)
  | @add x y hx hy ihx ihy =>
    intro h
    exact xu_add hZa hωZ x y h (ihx (lt_of_le_of_lt le_self_add h)) (ihy (lt_of_le_of_lt le_add_self h))
  | @phi x y hx hy ihx ihy =>
    intro h
    rcases lt_or_ge (veblen x y) (Wj.wjT 0) with hlt | hge
    · exact hlow _ (GxCl.phi hx hy) hlt
    have hyB : y < gcG 1 := lt_of_le_of_lt (right_le_veblen x y) h
    have hxB : x < gcG 1 := lt_of_le_of_lt (left_le_veblen x y) h
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [veblen_zero_apply] at h ⊢
      exact xu_opow_gate hZw hωZ y h (ihy hyB)
    · exact xu_phi_gate hωZ hx0 hge h (ihx hxB) (ihy hyB)

/-- **Every code `c < Γ(1)` lies in every hull `C(a, b)` (`0 < a`) containing its gate**, and so does `ω^e·c` for
every `e` in the hull. -/
theorem xu_mem {S : InaccSeq.{0}} {a b : Ordinal.{0}} (ha : 0 < a) : ∀ c, c < gcG 1 → xuG c < b →
    c ∈ S.CSet a b ∧ ∀ e ∈ S.CSet a b, ω ^ e * c ∈ S.CSet a b := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hg
  rcases lt_or_ge c (Wj.wjT 0) with hct | hct
  · rw [xuG_low hct] at hg
    exact wtD.mem S a b ha c (xu_lt_wtB hct) hg
  have hnc := xu_idx_lt hct hc
  have hlc := xu_lev_lt hct hc
  obtain ⟨-, -, -, hce⟩ := xu_E_data hct hc
  have hcE := xu_gfE_le hct
  obtain ⟨hk, hd0, hdE, hr, hdec, hkc, hrc, hdc⟩ := gl_parts hcE
  obtain ⟨q0n, q0k, q0d, g0r⟩ := xu_parts_Q hct hc hg
  set E := guE c with hEdef
  have hE : InE E := guE_E c
  set k := log E c with hkdef
  set d := c / E ^ k with hddef
  set r := c % E ^ k with hrdef
  have hpart : ∀ p, p < c → xuQ p < b → (p ∈ S.CSet a b ∧ ∀ e ∈ S.CSet a b, ω ^ e * p ∈ S.CSet a b) := by
    intro p hpc hq
    by_cases hω : p < ω
    · obtain ⟨m, rfl⟩ := lt_omega0.1 hω
      exact ⟨gu_nat_mem m, fun e he => lg_cset_mul_nat (by
        have := CSet.phi_mem (CSet.zero_mem (S := S) a b) he; rwa [veblen_zero_apply] at this) m⟩
    · have hQ : xuQ p = xuG p := by unfold xuQ; rw [if_neg hω]
      exact IH p hpc (hpc.trans hc) (hQ ▸ hq)
  have hn := (hpart _ hnc ((xuQE_le_I E).trans_lt q0n)).1
  have hl := (hpart _ hlc ((xuQE_le_K E).trans_lt q0n)).1
  have hlam : ∀ η, η ∈ S.CSet a b → glLam (xuK E) η ∈ S.CSet a b := by
    intro η hη
    unfold glLam
    split_ifs
    · exact CSet.add_mem hη (CSet.one_mem _ _)
    · exact CSet.add_mem (gl_y0_mem _) hη
  have hEm : E ∈ S.CSet a b := by
    rw [← hce]
    unfold xuPsi glPsi
    split_ifs
    · exact CSet.phi_mem hl (hlam _ (CSet.add_mem (CSet.one_mem _ _) hn))
    · exact CSet.phi_mem hl (hlam _ hn)
  have hEk : E * k ∈ S.CSet a b := by
    have := (hpart k hkc q0k).2 E hEm
    rwa [show ω ^ E = E from hE] at this
  have hd := hpart d hdc q0d
  have hrr := IH r hrc (hrc.trans hc) g0r
  have hpow : E ^ k = ω ^ (E * k) := gu_pow_eq hE k
  refine ⟨?_, fun e he => ?_⟩
  · rw [← hdec, hpow]
    exact CSet.add_mem (hd.2 _ hEk) hrr.1
  · rw [← hdec, hpow, mul_add, ← mul_assoc, ← opow_add]
    exact CSet.add_mem (hd.2 _ (CSet.add_mem he hEk)) (hrr.2 e he)

end Googology.Trans.PoR.InaccPsi.R2.Xu
