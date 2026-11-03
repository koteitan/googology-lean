import Googology.Trans.PoR.InaccPsi.R2.YrPi
import Googology.Trans.PoR.InaccPsi.R2.YhGate
import Googology.Trans.PoR.InaccPsi.R2.TfPsi

/-!
# YrGate: CODES WITH READ ATOM INDICES: gates of sums, powers and Veblen values, the code gate, hulls

The argument of `Yh.YhGate` with the gate of an atom `Γ(i)` the gate of its index (`Yr.yrG_atom`).  A Veblen value
`φ(o, y)` that is an atom and not a fixed point of `φ(o, ·)` has `o = φ(o, y)` (strong criticality), so its gate is
the gate of `o`.  The hull lemma reads the atom `Γ(i)` as the collapse `ψ_{Ω₂}(i)` (`Tf.tf_psi`, `i ≤ B_Γ`), so it
asks only `i` in the hull and `i < a`, no constant index.

* `yrG_lt_Om1`, `yr_add`, `yr_div`, `yr_opow_gate`, `yr_lam_gate`, `yr_phi_gate` (**the gate of `φ(o, y) ≥ G`**);
* `yrCl_below`, `yr_code_gate` (**a code over a strongly critical `Z ≤ Ω₁` and atoms `Γ(i)` with `yrG i < Z` has its
  gate below `Z`**);
* `yr_mem` (**every code `c < B_Γ` with `c < a` lies in every hull `C(a, b)` containing its gate**).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yr

open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2 Googology.Notation.InaccPsi
  Googology.Notation.InaccPsi.InaccSeq Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Gn
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Xu
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Wt Googology.Trans.PoR.InaccPsi.R2.Hi
  Googology.Trans.PoR.InaccPsi.R2.Yh

theorem yr_G_om : ω ^ gcG 0 = gcG 0 := gl_G0_E

/-- **Every gate is countable.** -/
theorem yrG_lt_Om1 : ∀ c, yrG c < Om1 := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  rcases lt_or_ge c (gcG 0) with hcG | hcG
  · rw [yrG_low hcG]; exact glG_lt_Om1 c hcG
  have hQ : ∀ p, p < c → yrQ p < Om1 := fun p hp => by
    unfold yrQ; split_ifs
    · exact omega0_pos.trans omega_lt_Om1
    · exact IH p hp
  obtain ⟨-, -, -, -, -, hkc, hrc, hdc⟩ := gl_parts (yh_gfE_le hcG)
  rw [yrG_dec hcG]
  refine max_lt (max_lt ?_ (hQ _ hkc)) (max_lt (hQ _ hdc) (IH _ hrc))
  by_cases hA : YhAt (guE c)
  · by_cases hi : yhJ (guE c) < guE c
    · rw [yrQE_atom hA hi]; exact hQ _ (yr_ix_lt hcG hi)
    · rw [yrQE_atom_fix hA hi]; exact omega0_pos.trans omega_lt_Om1
  · rw [yrQE_psi hA]
    exact max_lt (hQ _ (yh_lev_lt hcG hA)) (hQ _ (yh_idx_lt hcG hA))

/-- **The gate of a sum**, below every `Z > ω` closed under `+`. -/
theorem yr_add {Z : Ordinal.{0}} (hZ : ∀ u v, u < Z → v < Z → u + v < Z) (hωZ : ω < Z) :
    ∀ x y, yrG x < Z → yrG y < Z → yrG (x + y) < Z := by
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro y hgx hgy
  rcases lt_or_ge x (gcG 0) with hxG | hxG
  · rcases lt_or_ge y (gcG 0) with hyG | hyG
    · have hs : x + y < gcG 0 := (inE_indec gl_G0_E).add_lt hxG hyG
      rw [yrG_low hxG] at hgx
      rw [yrG_low hyG] at hgy
      rw [yrG_low hs]
      exact gl_add hZ hωZ x y hs hgx hgy
    · have e : x + y = y := add_of_omega0_opow_le (b := gcG 0) (by rw [yr_G_om]; exact hxG)
        (by rw [yr_G_om]; exact hyG)
      rw [e]; exact hgy
  have hxE := yh_gfE_le hxG
  obtain ⟨hk, hd0, hdE, hr, hdec, -, hrx, hdx⟩ := gl_parts hxE
  obtain ⟨q0n, q0k, q0d, g0r⟩ := yr_parts_Q hxG hgx
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
    rw [e, yrG_cnf hE hGE hk hd0 hdE hry hv]
    exact max_lt (max_lt q0n q0k) (max_lt q0d (IH r hrx y g0r hgy))
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
    obtain ⟨-, -, q0d', g0r'⟩ := yr_parts_Q hyG hgy
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
    have hgdd : yrG (d + d') < Z := IH d hdx d' (yrG_of_Q hωZ q0d) (yrG_of_Q hωZ q0d')
    rw [e, yrG_cnf hE hGE hk (by intro h0; exact hd0 (Ordinal.add_eq_zero_iff.1 h0).1) hdd hr' hv]
    exact max_lt (max_lt q0n q0k) (max_lt ((yrQ_le _).trans_lt hgdd) g0r')
  · have e : x + y = y := add_of_omega0_opow_le (b := E * (k + 1)) (by rw [← gu_pow_eq hE]; exact hxk1)
      (by rw [← gu_pow_eq hE]; exact hyk1)
    rw [e]; exact hgy

/-- **`y/e` and `y mod e` keep the gate** of a code `y ≥ G` (`e = guE y`), below every `Z > ω`. -/
theorem yr_div {Z : Ordinal.{0}} (hωZ : ω < Z) : ∀ y, gcG 0 ≤ y → yrG y < Z →
    yrQ (y / guE y) < Z ∧ yrG (y % guE y) < Z := by
  intro y
  induction y using WellFoundedLT.induction with
  | ind y IH =>
  intro hyG hg
  have hyE := yh_gfE_le hyG
  obtain ⟨ha, hd0, hdE, hr, hdec, -, hry, -⟩ := gl_parts hyE
  obtain ⟨q0n, q0a, q0d, g0r⟩ := yr_parts_Q hyG hg
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
  have hQ1 : ∀ a' : Ordinal.{0}, yrQ (1 + a') = yrQ a' := by
    intro a'
    rcases lt_or_ge a' ω with haω | haω
    · obtain ⟨n, rfl⟩ := lt_omega0.1 haω
      have : (1 : Ordinal.{0}) + n = ((1 + n : ℕ) : Ordinal.{0}) := by push_cast; rfl
      rw [this, yrQ_nat, yrQ_nat]
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
      have hQ : yrQ (y / E) = yrG (y / E) := by
        unfold yrQ
        rw [if_neg (not_lt.2 ((omega0_lt_inE hE).le.trans hEq))]
      rw [hQ, hdiv, yrG_cnf hE hGE ha1 hd0 hdE hrq (hdiv ▸ hdB)]
      refine max_lt (max_lt q0n (by rw [← hQ1, e1]; exact q0a)) (max_lt q0d ?_)
      rcases lt_or_ge r E with hrE | hrE
      · rw [Ordinal.div_eq_zero_of_lt hrE, yrG_zero]; exact (omega0_pos).trans hωZ
      · obtain ⟨hEr, -⟩ := gl_same hE hOE hrE hrN
        have := (IH r hry (hGE.trans hrE) g0r).1
        rw [hEr] at this
        exact yrG_of_Q hωZ this
  · have hmod : y % E = r % E := by rw [hy, Ordinal.mul_add_mod_self]
    rw [hmod]
    rcases lt_or_ge r E with hrE | hrE
    · rw [Ordinal.mod_eq_of_lt hrE]; exact g0r
    · obtain ⟨hEr, -⟩ := gl_same hE hOE hrE hrN
      have := (IH r hry (hGE.trans hrE) g0r).2
      rwa [hEr] at this

/-- **The gate of `ω^y`**, below every `Z > ω` closed under `ω^·`. -/
theorem yr_opow_gate {Z : Ordinal.{0}} (hZw : ∀ u, u < Z → ω ^ u < Z) (hωZ : ω < Z) :
    ∀ y, yrG y < Z → yrG (ω ^ y) < Z := by
  intro y
  induction y using WellFoundedLT.induction with
  | ind y IH =>
  intro hg
  have hyy : y ≤ ω ^ y := right_le_opow y one_lt_omega0
  rcases lt_or_ge (ω ^ y) (gcG 0) with hlt | hge
  · have hy : y < gcG 0 := hyy.trans_lt hlt
    rw [yrG_low hy] at hg
    rw [yrG_low hlt]
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
  obtain ⟨g1, g2⟩ := yr_div hωZ y hyG hg
  rw [hEy'] at g1 g2
  obtain ⟨q0n, -, -, -⟩ := yr_parts_Q hyG hg
  rw [hEy'] at q0n
  set q := y / E with hqdef
  set s := y % E with hsdef
  have hsE : s < E := Ordinal.mod_lt y hE.pos.ne'
  have hq0 : q ≠ 0 := ((Ordinal.div_pos hE.pos.ne').2 hEy).ne'
  have hws : ω ^ s < E := by rw [← show ω ^ E = E from hE]; exact (opow_lt_opow_iff_right one_lt_omega0).2 hsE
  have ew : ω ^ y = E ^ q * ω ^ s + 0 := by
    rw [add_zero, gu_pow_eq hE, ← opow_add, Ordinal.div_add_mod]
  have hsy : s < y := hsE.trans_le hEy
  have hgs : yrG (ω ^ s) < Z := IH s hsy g2
  rw [ew, yrG_cnf hE hGE hq0 (opow_ne_zero _ omega0_ne_zero) hws (opow_pos _ hE.pos) (ew ▸ hcn), yrG_zero]
  exact max_lt (max_lt q0n g1) (max_lt ((yrQ_le _).trans_lt hgs) (lt_of_le_of_lt zero_le (omega0_pos.trans hωZ)))

/-- The gate of an index from the gate of the argument: `glLam o η = y` gives `yrQ η ≤ yrG y` (`η` infinite). -/
theorem yr_lam_gate {o η y : Ordinal.{0}} (hη : glLam o η = y) (hηω : ω ≤ η)
    (hlow : o < Om1 → η < Om1 * ω → False) : yrQ η ≤ yrG y := by
  refine (yrQ_le η).trans ?_
  by_cases hF : glFw o η
  · rw [glLam_of hF] at hη
    rw [← hη]
    exact yrG_le_succ η
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
theorem yr_phi_gate {Z o y : Ordinal.{0}} (hωZ : ω < Z) (ho : o ≠ 0) (hge : gcG 0 ≤ veblen o y)
    (hgo : yrG o < Z) (hgy : yrG y < Z) : yrG (veblen o y) < Z := by
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
  have hQη : yrQ η ≤ yrG y := by
    by_cases hηω : η < ω
    · unfold yrQ; rw [if_pos hηω]; exact zero_le
    · exact yr_lam_gate hη (not_lt.1 hηω) hlow
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
    rw [hp', yrG_psi ho1 (hp' ▸ hGv)]
    refine max_lt ((yrQ_le o).trans_lt hgo) ?_
    rcases lt_or_ge η ω with hηω | hηω
    · have : η - 1 < ω := (le_add_self.trans_eq e1).trans_lt hηω
      unfold yrQ; rw [if_pos this]; exact omega0_pos.trans hωZ
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
  · rw [hpsi, ← yhPsi_ne hoA, yrG_psi ho1 (by rw [yhPsi_ne hoA, ← hpsi]; exact hGv)]
    exact max_lt ((yrQ_le o).trans_lt hgo) (hQη.trans_lt hgy)

/-- **Below `V`, no atom `≥ V` is needed.** -/
theorem yrCl_below {Z V : Ordinal.{0}} {A : Set Ordinal.{0}} (hA : ∀ s ∈ A, V ≤ s) :
    ∀ c, GxCl Z A c → c < V → GxCl Z ∅ c := by
  intro c hc
  induction hc with
  | small h => exact fun _ => GxCl.small h
  | om => exact fun _ => GxCl.om
  | @atom s hs => exact fun h => absurd h (not_lt.2 (hA s hs))
  | @add x y _ _ ihx ihy =>
    intro h
    exact GxCl.add (ihx (lt_of_le_of_lt le_self_add h)) (ihy (lt_of_le_of_lt le_add_self h))
  | @phi x y _ _ ihx ihy =>
    intro h
    exact GxCl.phi (ihx (lt_of_le_of_lt (left_le_veblen x y) h)) (ihy (lt_of_le_of_lt (right_le_veblen x y) h))

/-- **The gate of a code over a strongly critical `Z ≤ Ω₁` and any base atoms is below `Z`.** -/
theorem yr_code_gate {Z : Ordinal.{0}} {A : Set Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om1)
    (hA : ∀ s ∈ A, ∃ i, s = gcG i ∧ i < gcG i ∧ yrG i < Z) : ∀ c, GxCl Z A c → yrG c < Z := by
  have hZa : ∀ u v, u < Z → v < Z → u + v < Z := fun u v hu hv => hZ.isPrincipal hu hv
  have hZp : ∀ u v, u < Z → v < Z → veblen u v < Z := fun u v hu hv => hZ.2 u hu v hv
  have hZw : ∀ u, u < Z → ω ^ u < Z := fun u hu => by
    have := hZp 0 u hZ.1 hu; rwa [veblen_zero_apply] at this
  have hωZ : ω < Z := by
    have h1 := hZw 0 hZ.1; rw [opow_zero] at h1
    have := hZw 1 h1; rwa [opow_one] at this
  have hAG : ∀ s ∈ A, gcG 0 ≤ s := fun s hs => by
    obtain ⟨i, rfl, -, -⟩ := hA s hs
    exact gcG_le zero_le
  have hlow : ∀ x, GxCl Z A x → x < gcG 0 → yrG x < Z := fun x hx h => by
    rw [yrG_low h]
    exact gl_code_gate le_rfl hZ1 hZ.1 hZa hZp (At := ∅) (fun s hs => absurd hs (Set.notMem_empty s))
      gfE_lt_G0.le (yrCl_below hAG x hx h) h
  intro c hc
  induction hc with
  | @small x h => exact hlow _ (GxCl.small h) ((h.trans_le hZ1).trans gl_Om1_lt_G0)
  | om => exact hlow _ GxCl.om (by rw [← Br.Om1_eq]; exact gl_Om1_lt_G0)
  | @atom s hs =>
    obtain ⟨i, rfl, hii, hgi⟩ := hA s hs
    rw [yrG_atom hii]; exact (yrQ_le i).trans_lt hgi
  | @add x y _ _ ihx ihy => exact yr_add hZa hωZ x y ihx ihy
  | @phi x y hx hy ihx ihy =>
    rcases lt_or_ge (veblen x y) (gcG 0) with hlt | hge
    · exact hlow _ (GxCl.phi hx hy) hlt
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [veblen_zero_apply]
      exact yr_opow_gate hZw hωZ y ihy
    · exact yr_phi_gate hωZ hx0 hge ihx ihy

/-- **Every code `c < B_Γ` with `c < a` lies in every hull `C(a, b)` containing its gate**, and so does
`ω^e·c` for every `e` in the hull. -/
theorem yr_mem {S : InaccSeq.{0}} {a b : Ordinal.{0}} : ∀ c, c < Tf.tfBG → c < a → yrG c < b →
    c ∈ S.CSet a b ∧ ∀ e ∈ S.CSet a b, ω ^ e * c ∈ S.CSet a b := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hca hg
  rcases lt_or_ge c (gcG 0) with hcG | hcG
  · rw [yrG_low hcG] at hg
    exact gl_mem c hcG hg
  have hcE := yh_gfE_le hcG
  obtain ⟨hk, hd0, hdE, hr, hdec, hkc, hrc, hdc⟩ := gl_parts hcE
  obtain ⟨q0n, q0k, q0d, g0r⟩ := yr_parts_Q hcG hg
  set E := guE c with hEdef
  have hE : InE E := guE_E c
  have hEc : E ≤ c := gl_E_le hcE
  set k := log E c with hkdef
  set d := c / E ^ k with hddef
  set r := c % E ^ k with hrdef
  have hpart : ∀ p, p < c → yrQ p < b → (p ∈ S.CSet a b ∧ ∀ e ∈ S.CSet a b, ω ^ e * p ∈ S.CSet a b) := by
    intro p hpc hq
    by_cases hω : p < ω
    · obtain ⟨m, rfl⟩ := lt_omega0.1 hω
      exact ⟨gu_nat_mem m, fun e he => lg_cset_mul_nat (by
        have := CSet.phi_mem (CSet.zero_mem (S := S) a b) he; rwa [veblen_zero_apply] at this) m⟩
    · have hQ : yrQ p = yrG p := by unfold yrQ; rw [if_neg hω]
      exact IH p hpc (hpc.trans hc) (hpc.trans hca) (hQ ▸ hq)
  have hEm : E ∈ S.CSet a b := by
    by_cases hA : YhAt E
    · obtain ⟨i, hi⟩ := yhAt_iff.1 hA
      obtain ⟨hii, hie⟩ := yr_atom_idx hi (hEc.trans_lt hc)
      have hia : i < a := (hie.trans_le hEc).trans hca
      have hiq : yrQ i < b := by rw [hi, yrQE_atom (hi ▸ hA) (by rw [yhJ_gcG]; exact hii), yhJ_gcG] at q0n; exact q0n
      have him := (hpart i (hie.trans_le hEc) hiq).1
      have hiBG : i ≤ Tf.tfBG := ((hie.trans_le hEc).trans hc).le
      have hpsi : gcG i = S.psi i (Om (1 + 1)) := by rw [Tf.tf_psi S i hiBG, Tf.tf_gcG]
      rw [hi, hpsi]
      exact CSet.psi_mem hia (InR_Om_succ 1) (Ga.ga_Om2_mem _ _) him
    · have hce : yhPsi (yhK E) (yhI E) = E := (yh_E_data hcG hA).2.2.2
      rw [yrQE_psi hA] at q0n
      have hn := (hpart _ (yh_idx_lt hcG hA) ((le_max_right _ _).trans_lt q0n)).1
      have hl := (hpart _ (yh_lev_lt hcG hA) ((le_max_left _ _).trans_lt q0n)).1
      have hlam : ∀ η, η ∈ S.CSet a b → glLam (yhK E) η ∈ S.CSet a b := by
        intro η hη
        unfold glLam
        split_ifs
        · exact CSet.add_mem hη (CSet.one_mem _ _)
        · exact CSet.add_mem (gl_y0_mem _) hη
      rw [← hce]
      unfold yhPsi glPsi
      split_ifs
      · exact CSet.phi_mem hl (hlam _ (CSet.add_mem (CSet.one_mem _ _) hn))
      · exact CSet.phi_mem hl (hlam _ hn)
  have hEk : E * k ∈ S.CSet a b := by
    have := (hpart k hkc q0k).2 E hEm
    rwa [show ω ^ E = E from hE] at this
  have hd := hpart d hdc q0d
  have hrr := IH r hrc (hrc.trans hc) (hrc.trans hca) g0r
  have hpow : E ^ k = ω ^ (E * k) := gu_pow_eq hE k
  refine ⟨?_, fun e he => ?_⟩
  · rw [← hdec, hpow]
    exact CSet.add_mem (hd.2 _ hEk) hrr.1
  · rw [← hdec, hpow, mul_add, ← mul_assoc, ← opow_add]
    exact CSet.add_mem (hd.2 _ (CSet.add_mem he hEk)) (hrr.2 e he)

end Googology.Trans.PoR.InaccPsi.R2.Yr
