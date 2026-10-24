import Googology.Trans.PoR.InaccPsi.R2.GlR4

/-!
# CODES BELOW `Γ_{Ω₁+1}`: gates of sums, powers and Veblen values, hulls

* `gl_add` (**the gate of a sum**), `gl_div` (`y/e` and `y mod e` keep the gate), `gl_opow_gate` (**the gate of
  `ω^y`**);
* `gl_phi_gate` (**the gate of `φ(o, y)`, `1 ≤ o`**: either `φ(o, y) = y`, or `y = Λ_o(η)` and `φ(o, y) =
  glPsi o η` has the gate of `o` and `η`, the latter at most that of `y = η + 1` or `y = y₀(o) + η`),
  `gl_code_gate` (**a code `c < B ≤ Γ_{Ω₁+1}` in the closure of `Z` and atoms above `B` has its gate below `Z`**);
* `gl_y0_mem`, `gl_mem` (**every code lies in every hull containing its gate**, jointly with `ω^e·c`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gl

open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu

open Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh Googology.Trans.PoR.InaccPsi.R2.Gi
  Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Mx
open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2 Googology.Notation.InaccPsi
  Googology.Notation.InaccPsi.InaccSeq

theorem glQ_one_add (a : Ordinal.{0}) : glQ (1 + a) = glQ a := by
  rcases lt_or_ge a ω with ha | ha
  · obtain ⟨n, rfl⟩ := lt_omega0.1 ha
    have : (1 : Ordinal.{0}) + n = ((1 + n : ℕ) : Ordinal.{0}) := by push_cast; rfl
    rw [this, glQ_nat, glQ_nat]
  · rw [one_add_of_omega0_le ha]

/-- The bracket data of a code above an `ε`-number `e`: `e ≤ y < ε_{e+1}` gives `guE y = e`, `gfE ≤ y`. -/
theorem gl_same {e y : Ordinal.{0}} (he : InE e) (hOe : Om1 < e) (h1 : e ≤ y) (h2 : y < eN e) :
    guE y = e ∧ gfE ≤ y :=
  ⟨gl_E_of_bracket he hOe h1 h2, (eN_le hOe he).trans h1⟩

/-- **The gate of a sum** of codes below `Γ_{Ω₁+1}`, below every `Z > ω` closed under `+`. -/
theorem gl_add {Z : Ordinal.{0}} (hZ : ∀ u v, u < Z → v < Z → u + v < Z) (hωZ : ω < Z) :
    ∀ x y, x + y < gcG 0 → glG x < Z → glG y < Z → glG (x + y) < Z := by
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro y hxy hgx hgy
  have hxB : x < gcG 0 := lt_of_le_of_lt le_self_add hxy
  have hyB : y < gcG 0 := lt_of_le_of_lt le_add_self hxy
  rcases lt_or_ge x gfE with hxE | hxE
  · rcases lt_or_ge y gfE with hyE | hyE
    · rw [glG_low hxE] at hgx
      rw [glG_low hyE] at hgy
      rw [glG_low (eW_indec.add_lt hxE hyE)]
      exact gtc_add hZ x y hxE hyE hgx hgy
    · have e : x + y = y := add_of_omega0_opow_le (b := gfE) (by rw [eW_E]; exact hxE) (by rw [eW_E]; exact hyE)
      rw [e]; exact hgy
  obtain ⟨hk, hd0, hdE, hr, hdec, -, hrx, hdx⟩ := gl_parts hxE
  obtain ⟨q0n, q0k, q0d, g0r⟩ := gl_parts_Q hxE hxB hgx
  set E := guE x with hEdef
  have hE : InE E := guE_E x
  have hOE : Om1 < E := gl_Om1_lt_E hxE
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
    have hrB : r + y < gcG 0 := lt_of_le_of_lt (add_le_add hrx.le le_rfl) hxy
    rw [e, glG_cnf hE hOE hk hd0 hdE hry hv (e ▸ hxy)]
    exact max_lt (max_lt q0n q0k) (max_lt q0d (IH r hrx y hrB g0r hgy))
  rcases lt_or_ge y (E ^ (k + 1)) with hyk1 | hyk1
  · have hEk : E ≤ E ^ k := by
      calc E = E ^ (1 : Ordinal.{0}) := (opow_one _).symm
        _ ≤ E ^ k := opow_le_opow_right hE.pos (one_le_iff_ne_zero.2 hk)
    have hyN : y < eN E := hyk1.trans hk1E
    obtain ⟨hEy, hyE⟩ := gl_same hE hOE (hEk.trans hyk) hyN
    have hky : log E y = k := by
      refine le_antisymm ?_ (le_log_of_opow_le hE1 hyk)
      exact Order.lt_add_one_iff.1 ((lt_opow_iff_log_lt hE1 (hE.pos.trans_le (hEk.trans hyk)).ne').1 hyk1)
    obtain ⟨-, hd0', hdE', hr', hdec', -, -, -⟩ := gl_parts hyE
    obtain ⟨-, -, q0d', g0r'⟩ := gl_parts_Q hyE hyB hgy
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
    have hdB : d + d' < gcG 0 := hdd.trans ((gl_E_le hxE).trans_lt hxB)
    have hgdd : glG (d + d') < Z :=
      IH d hdx d' hdB (glG_of_Q hωZ q0d) (glG_of_Q hωZ q0d')
    rw [e, glG_cnf hE hOE hk (by intro h0; exact hd0 (Ordinal.add_eq_zero_iff.1 h0).1) hdd hr' hv (e ▸ hxy)]
    exact max_lt (max_lt q0n q0k) (max_lt ((glQ_le _).trans_lt hgdd) g0r')
  · have e : x + y = y := add_of_omega0_opow_le (b := E * (k + 1)) (by rw [← gu_pow_eq hE]; exact hxk1)
      (by rw [← gu_pow_eq hE]; exact hyk1)
    rw [e]; exact hgy

/-- **`y/e` and `y mod e` keep the gate** of a code `y ≥ ε_{Ω₁+1}` (`e = guE y`), below every `Z > ω`. -/
theorem gl_div {Z : Ordinal.{0}} (hωZ : ω < Z) : ∀ y, gfE ≤ y → y < gcG 0 → glG y < Z →
    glQ (y / guE y) < Z ∧ glG (y % guE y) < Z := by
  intro y
  induction y using WellFoundedLT.induction with
  | ind y IH =>
  intro hyE hyB hg
  obtain ⟨ha, hd0, hdE, hr, hdec, -, hry, -⟩ := gl_parts hyE
  obtain ⟨q0n, q0a, q0d, g0r⟩ := gl_parts_Q hyE hyB hg
  set E := guE y with hEdef
  have hE : InE E := guE_E y
  have hOE : Om1 < E := gl_Om1_lt_E hyE
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
  have hrB : r < gcG 0 := hry.trans hyB
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
      have hQ : glQ (y / E) = glG (y / E) := by
        unfold glQ
        rw [if_neg (not_lt.2 ((omega0_lt_inE hE).le.trans hEq))]
      have hdivB : y / E < gcG 0 := hdB.trans_le (eN_le ((gl_E_le hyE).trans_lt hyB) gl_G0_E)
      rw [hQ, hdiv, glG_cnf hE hOE ha1 hd0 hdE hrq (hdiv ▸ hdB) (hdiv ▸ hdivB)]
      refine max_lt (max_lt q0n (by rw [← glQ_one_add, e1]; exact q0a)) (max_lt q0d ?_)
      rcases lt_or_ge r E with hrE | hrE
      · rw [Ordinal.div_eq_zero_of_lt hrE, glG_zero]; exact (omega0_pos).trans hωZ
      · obtain ⟨hEr, hgfr⟩ := gl_same hE hOE hrE hrN
        have := (IH r hry hgfr hrB g0r).1
        rw [hEr] at this
        exact glG_of_Q hωZ this
  · have hmod : y % E = r % E := by rw [hy, Ordinal.mul_add_mod_self]
    rw [hmod]
    rcases lt_or_ge r E with hrE | hrE
    · rw [Ordinal.mod_eq_of_lt hrE]; exact g0r
    · obtain ⟨hEr, hgfr⟩ := gl_same hE hOE hrE hrN
      have := (IH r hry hgfr hrB g0r).2
      rwa [hEr] at this

/-- **The gate of `ω^y`** for a code `y` with `ω^y < Γ_{Ω₁+1}`, below every `Z > ω` closed under `ω^·`. -/
theorem gl_opow_gate {Z : Ordinal.{0}} (hZw : ∀ u, u < Z → ω ^ u < Z) (hωZ : ω < Z) :
    ∀ y, ω ^ y < gcG 0 → glG y < Z → glG (ω ^ y) < Z := by
  intro y
  induction y using WellFoundedLT.induction with
  | ind y IH =>
  intro hyB hg
  have hyy : y ≤ ω ^ y := right_le_opow y one_lt_omega0
  rcases lt_or_ge (ω ^ y) gfE with hlt | hge
  · have hy : y < gfE := hyy.trans_lt hlt
    rw [glG_low hy] at hg
    rw [glG_low hlt]
    exact gtc_opow hZw hy hg
  set E := guE (ω ^ y) with hEdef
  have hE : InE E := guE_E _
  have hOE : Om1 < E := gl_Om1_lt_E hge
  have hnc : E ≤ ω ^ y := gl_E_le hge
  have hcn : ω ^ y < eN E := gl_lt_eN hge
  have hEy : E ≤ y := by
    rw [← show ω ^ E = E from hE] at hnc
    exact (opow_le_opow_iff_right one_lt_omega0).1 hnc
  have hyN : y < eN E := hyy.trans_lt hcn
  obtain ⟨hEy', hyE⟩ := gl_same hE hOE hEy hyN
  have hyB' : y < gcG 0 := hyy.trans_lt hyB
  obtain ⟨g1, g2⟩ := gl_div hωZ y hyE hyB' hg
  rw [hEy'] at g1 g2
  obtain ⟨q0n, -, -, -⟩ := gl_parts_Q hyE hyB' hg
  rw [hEy'] at q0n
  set q := y / E with hqdef
  set s := y % E with hsdef
  have hsE : s < E := Ordinal.mod_lt y hE.pos.ne'
  have hq0 : q ≠ 0 := ((Ordinal.div_pos hE.pos.ne').2 hEy).ne'
  have hws : ω ^ s < E := by rw [← show ω ^ E = E from hE]; exact (opow_lt_opow_iff_right one_lt_omega0).2 hsE
  have ew : ω ^ y = E ^ q * ω ^ s + 0 := by
    rw [add_zero, gu_pow_eq hE, ← opow_add, Ordinal.div_add_mod]
  have hsy : s < y := hsE.trans_le hEy
  have hEB : E < gcG 0 := hnc.trans_lt hyB
  have hgs : glG (ω ^ s) < Z := IH s hsy (hws.trans hEB) g2
  rw [ew, glG_cnf hE hOE hq0 (opow_ne_zero _ omega0_ne_zero) hws (opow_pos _ hE.pos) (ew ▸ hcn) (ew ▸ hyB),
    glG_zero]
  exact max_lt (max_lt q0n g1) (max_lt ((glQ_le _).trans_lt hgs) (lt_of_le_of_lt zero_le (omega0_pos.trans hωZ)))

/-- **The gate of a Veblen value `φ(o, y)` (`1 ≤ o`) above `ε_{Ω₁+1}`** below `Γ_{Ω₁+1}`, from the gates of `o`
and `y`. -/
theorem gl_phi_gate {Z o y : Ordinal.{0}} (hωZ : ω < Z) (ho : o ≠ 0) (hge : gfE ≤ veblen o y)
    (hB : veblen o y < gcG 0) (hgo : glG o < Z) (hgy : glG y < Z) : glG (veblen o y) < Z := by
  have hyB : y < gcG 0 := lt_of_le_of_lt (right_le_veblen o y) hB
  have hoB : o < gcG 0 := lt_of_le_of_lt (by simpa using left_le_veblen o y) hB
  have hOv : Om1 < veblen o y := Om1_lt_eW.trans_le hge
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
  have hηB : η < gcG 0 := (glLam_ge o η).trans_lt (hη ▸ hyB)
  have hpsi : veblen o y = glPsi o η := by unfold glPsi; rw [hη]
  rw [hpsi, glG_psi ho1 hoB hηB]
  refine max_lt ((glQ_le o).trans_lt hgo) ?_
  by_cases hηω : η < ω
  · unfold glQ; rw [if_pos hηω]; exact (omega0_pos).trans hωZ
  push Not at hηω
  refine lt_of_le_of_lt ?_ hgy
  refine (glQ_le η).trans ?_
  by_cases hF : glFw o η
  · rw [glLam_of hF] at hη
    rw [← hη]
    exact glG_le_succ_all η
  · rw [glLam_of_not hF] at hη
    have e1 : (1 : Ordinal.{0}) + η = η := one_add_of_omega0_le hηω
    rcases lt_trichotomy o Om1 with hα | hα | hα
    · rw [glY0_lt hα, add_assoc, e1] at hη
      rcases lt_or_ge η (Om1 * ω) with hηΩ | hηΩ
      · have hOω : Om1 * ω < gfE := eW_E.mul_lt Om1_lt_eW ((omega_lt_Om1).trans Om1_lt_eW)
        have hyW : y < gfE := by
          rw [← hη]
          calc Om1 + η < Om1 + Om1 * ω := (add_lt_add_iff_left _).2 hηΩ
            _ = Om1 * ω := by rw [← mul_one_add, one_add_of_omega0_le le_rfl]
            _ < gfE := hOω
        rw [glG_low (hηΩ.trans hOω), glG_low hyW, ← hη]
        exact gtc_le_Om1_add hηΩ
      · rw [← hη, add_eq_right_iff_mul_omega0_le.2 hηΩ]
    · rw [hα, glY0_eq, e1] at hη
      rw [← hη]
    · rw [glY0_gt hα, zero_add] at hη
      rw [← hη]

/-- **The gate of a code below a bound `B ≤ Γ_{Ω₁+1}` over `Z`** (atoms above `B`) is below `Z`. -/
theorem gl_code_gate {B Z : Ordinal.{0}} {At : Set Ordinal.{0}} (hBG : B ≤ gcG 0) (hZ1 : Z ≤ Om1) (hZ0 : 0 < Z)
    (hZa : ∀ u v, u < Z → v < Z → u + v < Z) (hZp : ∀ u v, u < Z → v < Z → veblen u v < Z)
    (hAt : ∀ s ∈ At, B < s) (hEB : gfE ≤ B) {c : Ordinal.{0}} (hc : GxCl Z At c) : c < B → glG c < Z := by
  have hAt' : ∀ s ∈ At, gfE < s := fun s hs => hEB.trans_lt (hAt s hs)
  have hZw : ∀ u, u < Z → ω ^ u < Z := fun u hu => by
    have := hZp 0 u hZ0 hu; rwa [veblen_zero_apply] at this
  have h1Z : (1 : Ordinal.{0}) < Z := by
    have := hZw 0 hZ0; rwa [opow_zero] at this
  have hωZ : ω < Z := by
    have := hZw 1 h1Z; rwa [opow_one] at this
  have hsmall : ∀ x, GxCl Z At x → x < gfE → glG x < Z := fun x hx h => by
    rw [glG_low h]; exact gfCode_gate hZ1 hZ0 hZa hZp hAt' hx h
  induction hc with
  | @small x h => exact fun _ => hsmall _ (GxCl.small h) ((h.trans_le hZ1).trans Om1_lt_eW)
  | om => exact fun _ => hsmall _ GxCl.om (by rw [← Br.Om1_eq]; exact Om1_lt_eW)
  | @atom s hs => exact fun h => absurd (hAt s hs) (not_lt.2 h.le)
  | @add x y hx hy ihx ihy =>
    intro h
    exact gl_add hZa hωZ x y (h.trans_le hBG) (ihx (lt_of_le_of_lt le_self_add h))
      (ihy (lt_of_le_of_lt le_add_self h))
  | @phi x y hx hy ihx ihy =>
    intro h
    rcases lt_or_ge (veblen x y) gfE with hlt | hge
    · exact hsmall _ (GxCl.phi hx hy) hlt
    have hyB : y < B := lt_of_le_of_lt (right_le_veblen x y) h
    have hxB : x < B := lt_of_le_of_lt (by simpa using left_le_veblen x y) h
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [veblen_zero_apply] at h ⊢
      exact gl_opow_gate hZw hωZ y (h.trans_le hBG) (ihy hyB)
    · exact gl_phi_gate hωZ hx0 hge (h.trans_le hBG) (ihx hxB) (ihy hyB)

theorem gl_y0_mem {S : InaccSeq.{0}} {a b : Ordinal.{0}} (α : Ordinal.{0}) : glY0 α ∈ S.CSet a b := by
  have hO : Om1 ∈ S.CSet a b := by rw [Br.Om1_eq]; exact CSet.Om_mem (CSet.one_mem _ _)
  unfold glY0
  split_ifs
  · exact CSet.add_mem hO (CSet.one_mem _ _)
  · exact CSet.one_mem _ _
  · exact CSet.zero_mem _ _

/-- **Every code `c < Γ_{Ω₁+1}` lies in every hull containing its gate**, and so does `ω^e·c` for every `e` in
the hull. -/
theorem gl_mem {S : InaccSeq.{0}} {a b : Ordinal.{0}} : ∀ c, c < gcG 0 → glG c < b →
    c ∈ S.CSet a b ∧ ∀ e ∈ S.CSet a b, ω ^ e * c ∈ S.CSet a b := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hg
  rcases lt_or_ge c gfE with hcE | hcE
  · rw [glG_low hcE] at hg
    exact ⟨gfW_mem' hcE hg, fun e he => gw_mulOm_mem he c hcE hg⟩
  have hnc := gl_idx_lt hcE hc
  have hlc := gl_lev_lt hcE hc
  obtain ⟨-, -, -, hce⟩ := gl_E_data hcE hc
  obtain ⟨hk, hd0, hdE, hr, hdec, hkc, hrc, hdc⟩ := gl_parts hcE
  obtain ⟨q0n, q0k, q0d, g0r⟩ := gl_parts_Q hcE hc hg
  set E := guE c with hEdef
  have hE : InE E := guE_E c
  set k := log E c with hkdef
  set d := c / E ^ k with hddef
  set r := c % E ^ k with hrdef
  -- a part `p < c` with gate (as a part) below `b`
  have hpart : ∀ p, p < c → glQ p < b → (p ∈ S.CSet a b ∧ ∀ e ∈ S.CSet a b, ω ^ e * p ∈ S.CSet a b) := by
    intro p hpc hq
    by_cases hω : p < ω
    · obtain ⟨m, rfl⟩ := lt_omega0.1 hω
      exact ⟨gu_nat_mem m, fun e he => lg_cset_mul_nat (by
        have := CSet.phi_mem (CSet.zero_mem (S := S) a b) he; rwa [veblen_zero_apply] at this) m⟩
    · have hQ : glQ p = glG p := by unfold glQ; rw [if_neg hω]
      exact IH p hpc (hpc.trans hc) (hQ ▸ hq)
  have hn := (hpart _ hnc ((glQE_le_I E).trans_lt q0n)).1
  have hl := (hpart _ hlc ((glQE_le_K E).trans_lt q0n)).1
  have hEm : E ∈ S.CSet a b := by
    rw [← hce]
    unfold glPsi
    refine CSet.phi_mem hl ?_
    by_cases hF : glFw (glK E) (glI E)
    · rw [glLam_of hF]; exact CSet.add_mem hn (CSet.one_mem _ _)
    · rw [glLam_of_not hF]; exact CSet.add_mem (gl_y0_mem _) hn
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

end Googology.Trans.PoR.InaccPsi.R2.Gl
