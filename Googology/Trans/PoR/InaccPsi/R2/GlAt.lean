import Googology.Trans.PoR.InaccPsi.R2.GlVb

/-!
# THE READING SIDE OF `φ(α, ·)`: the atoms `ϑˣ(Ω₁·β + t)` at every level `β ∈ Tˣ ∩ Ω₁`

The reading of the code `glPsi α η` at the base `x` is the atom `glA β t x = ϑˣ(Ω₁·β + t)` (`β` the reading of the
level `α`, `t` the reading of `η`).  From `R2.LvLev` (every level `β ∈ Tˣ`, `1 ≤ β < Ω₁`; [W07a] Lemma 3.30 through
`R2.CitedLu` and `R2.CitedLv`):

* `glA`, `glA_facts`, `glA_lt_of`, `glA_lt_iff`, `glA_le_iff`, `glA_lev` (**`β' < β`: `A_{β'}(t') < A_β(t) ↔
  t' < A_β(t)`**), `glA_lev'` (**`β < β'`: `A_{β'}(t') < A_β(t) ↔ A_{β'}(t') ≤ t`**) — the same comparisons as
  `glPsi_lt_lev`, `glPsi_lt_lev'` on the code side; `glA_min`, `glA_veb_le` (`φ_β(j) ≤ ϑˣ(Ω₁·β + j)`), `glA_P`,
  `glA_notP`;
* `glA_one_zero` (`ϑˣ(Ω₁) = ε_{x+1}`), `glA_eN_one`, `glA_eN_two` (the `ε`-number after an atom is again an atom);
* `gl_T_of_lt_G` (every ordinal below `Γ_{x+1}` is in `Tˣ ∩ Ω₁`), `glA_lt_G` (**atoms with level and argument below
  `Γ_{x+1}` stay below it**, [W07a] Lemma 3.30 at `Ω₁·Ω₁`);
* `gl_pi_mul` (`π(Ω₁·β) = Ω₁·π(β)`), `glA_pi` (**Lemma EXACT for the atom**), `glA_eN_pi`.

No new axiom.  New definition: `glA`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gl

open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gb
  Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Lu

/-- **The atom** `ϑˣ(Ω₁·β + t)`: the `t`-th ordinal above `x` and `β` of fixed-point level exactly `β`. -/
noncomputable def glA (β t x : Ordinal.{0}) : Ordinal.{0} := vt x (Om1 * β + t)

section Atom

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem glA_facts {β t : Ordinal.{0}} (hβ1 : 1 ≤ β) (hβT : β ∈ Tset x) (hβΩ : β < Om1) (ht : t ∈ Tset x)
    (ht1 : t < Om1) :
    glA β t x ∈ Tset x ∧ x < glA β t x ∧ glA β t x < Om1 ∧ InE (glA β t x) ∧ β < glA β t x ∧ t < glA β t x := by
  obtain ⟨-, -, h1, h2, h3, h4, h5, h6⟩ := ul_facts hx hx1 hβ1 hβT hβΩ ht ht1
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem glA_arg {β t : Ordinal.{0}} (hβ1 : 1 ≤ β) (hβT : β ∈ Tset x) (hβΩ : β < Om1) (ht : t ∈ Tset x)
    (ht1 : t < Om1) : Om1 * β + t ∈ Tset x ∧ Om1 * β + t < OmTwo := by
  obtain ⟨h1, h2, -⟩ := ul_facts hx hx1 hβ1 hβT hβΩ ht ht1
  exact ⟨h1, h2⟩

theorem glA_lt_of {β t t' : Ordinal.{0}} (hβ1 : 1 ≤ β) (hβT : β ∈ Tset x) (hβΩ : β < Om1) (ht : t ∈ Tset x)
    (ht' : t' ∈ Tset x) (ht'1 : t' < Om1) (h : t < t') : glA β t x < glA β t' x :=
  ul_eta_lt hx hx1 hβ1 hβT hβΩ ht ht' ht'1 h

theorem glA_lt_iff {β t t' : Ordinal.{0}} (hβ1 : 1 ≤ β) (hβT : β ∈ Tset x) (hβΩ : β < Om1)
    (ht : t ∈ Tset x) (ht1 : t < Om1) (ht' : t' ∈ Tset x) (ht'1 : t' < Om1) :
    glA β t x < glA β t' x ↔ t < t' := by
  refine ⟨fun h => ?_, glA_lt_of hx hx1 hβ1 hβT hβΩ ht ht' ht'1⟩
  by_contra hc
  push Not at hc
  rcases hc.lt_or_eq with hc | hc
  · exact absurd h (not_lt.2 (glA_lt_of hx hx1 hβ1 hβT hβΩ ht' ht ht1 hc).le)
  · rw [hc] at h; exact lt_irrefl _ h

theorem glA_le_iff {β t t' : Ordinal.{0}} (hβ1 : 1 ≤ β) (hβT : β ∈ Tset x) (hβΩ : β < Om1)
    (ht : t ∈ Tset x) (ht1 : t < Om1) (ht' : t' ∈ Tset x) (ht'1 : t' < Om1) :
    glA β t x ≤ glA β t' x ↔ t ≤ t' := by
  rw [← not_lt, ← not_lt, glA_lt_iff hx hx1 hβ1 hβT hβΩ ht' ht'1 ht ht1]

/-- **`β' < β`**: `ϑˣ(Ω₁·β' + t') < ϑˣ(Ω₁·β + t) ↔ t' < ϑˣ(Ω₁·β + t)`. -/
theorem glA_lev {β' β t t' : Ordinal.{0}} (hβ'1 : 1 ≤ β') (hβ'β : β' < β) (hβT : β ∈ Tset x)
    (hβΩ : β < Om1) (ht : t ∈ Tset x) (ht1 : t < Om1) (ht' : t' ∈ Tset x) (ht'1 : t' < Om1) :
    glA β' t' x < glA β t x ↔ t' < glA β t x := by
  have hβ'T := vz_T_down hx hx1 hβT hβΩ hβ'β.le
  refine ⟨fun h => (glA_facts hx hx1 hβ'1 hβ'T (hβ'β.trans hβΩ) ht' ht'1).2.2.2.2.2.trans h, fun h => ?_⟩
  exact ul_lev_lt hx hx1 (hβ'1.trans hβ'β.le) hβ'β hβT hβΩ ht' ht'1 ht ht1 h

/-- **`β < β'`**: `ϑˣ(Ω₁·β' + t') < ϑˣ(Ω₁·β + t) ↔ ϑˣ(Ω₁·β' + t') ≤ t`. -/
theorem glA_lev' {β' β t t' : Ordinal.{0}} (hβ1 : 1 ≤ β) (hββ' : β < β') (hβ'T : β' ∈ Tset x)
    (hβ'Ω : β' < Om1) (ht : t ∈ Tset x) (ht1 : t < Om1) (ht' : t' ∈ Tset x) (ht'1 : t' < Om1) :
    glA β' t' x < glA β t x ↔ glA β' t' x ≤ t := by
  have hβT := vz_T_down hx hx1 hβ'T hβ'Ω hββ'.le
  have hβΩ : β < Om1 := hββ'.trans hβ'Ω
  have hβ'1 : 1 ≤ β' := hβ1.trans hββ'.le
  refine ⟨fun h => ?_, fun h => h.trans_lt (glA_facts hx hx1 hβ1 hβT hβΩ ht ht1).2.2.2.2.2⟩
  by_contra hc
  push Not at hc
  obtain ⟨hξT, hξ2⟩ := glA_arg hx hx1 hβ'1 hβ'T hβ'Ω ht' ht'1
  have hββ'v : β < glA β' t' x := hββ'.trans (glA_facts hx hx1 hβ'1 hβ'T hβ'Ω ht' ht'1).2.2.2.2.1
  have := ul_lt_of_vt_lt hx hx1 hβT hβΩ hξT hξ2 ht ht1 hc hββ'v h
  have h2 : Om1 * β + t < Om1 * β' + t' := by
    calc Om1 * β + t < Om1 * β + Om1 := (add_lt_add_iff_left _).2 ht1
      _ = Om1 * (β + 1) := by rw [mul_add_one]
      _ ≤ Om1 * β' := mul_le_mul_right (add_one_le_of_lt hββ') _
      _ ≤ Om1 * β' + t' := le_self_add
  exact absurd this (not_lt.2 h2.le)

/-- **Minimality**: every `u ∈ P_β` above `x`, `t`, `β` and every `ϑˣ(Ω₁·β + σ)`, `σ < t`, is `≥ ϑˣ(Ω₁·β + t)`. -/
theorem glA_min {β t u : Ordinal.{0}} (hβ1 : 1 ≤ β) (hβT : β ∈ Tset x) (hβΩ : β < Om1) (ht : t ∈ Tset x)
    (ht1 : t < Om1) (hu : LuP β u) (hxu : x < u) (htu : t < u) (hβu : β < u)
    (hprev : ∀ σ, σ < t → glA β σ x < u) : glA β t x ≤ u :=
  lv_th_min hx hx1 hβ1 hβT hβΩ ht ht1 hu hxu htu hβu hprev

/-- `φ_β(j) ≤ ϑˣ(Ω₁·β + j)`. -/
theorem glA_veb_le {β : Ordinal.{0}} (hβ1 : 1 ≤ β) (hβT : β ∈ Tset x) (hβΩ : β < Om1) {j : Ordinal.{0}}
    (hj : j ∈ Tset x) (hj1 : j < Om1) : veblen β j ≤ glA β j x :=
  lv_veblen_le_th hx hx1 hβ1 hβT hβΩ j hj hj1

theorem glA_P {β t : Ordinal.{0}} (hβ1 : 1 ≤ β) (hβT : β ∈ Tset x) (hβΩ : β < Om1) (ht : t ∈ Tset x)
    (ht1 : t < Om1) : LuP β (glA β t x) :=
  lv_th_P hx hx1 β hβ1 hβT hβΩ t ht ht1

theorem glA_notP {β t : Ordinal.{0}} (hβ1 : 1 ≤ β) (hβT : β ∈ Tset x) (hβΩ : β < Om1) (ht : t ∈ Tset x)
    (ht1 : t < Om1) : ¬ LuP (β + 1) (glA β t x) :=
  lv_th_notP hx hx1 hβ1 hβT hβΩ ht ht1

/-- **`ϑˣ(Ω₁·1 + 0) = ε_{x+1}`.** -/
theorem glA_one_zero : glA 1 0 x = eN x := by
  have hZ : (0 : Ordinal.{0}) < evZ x := (evZ_E x).pos
  have h := vt_Om1_add_evZ hx hx1 hZ
  unfold glA
  rw [mul_one, h, add_zero, show (1 : Ordinal.{0}) = 0 + 1 by simp, evA_add_one, evA_zero hx]

theorem gl_one_T : (1 : Ordinal.{0}) ∈ Tset x ∧ (1 : Ordinal.{0}) < Om1 :=
  ⟨mem_T_of_le hx hx1 (one_lt_omega0.trans (omega0_lt_inE hx)).le, one_lt_omega0.trans omega_lt_Om1⟩

theorem gl_eN_le_glA {β t : Ordinal.{0}} (hβ1 : 1 ≤ β) (hβT : β ∈ Tset x) (hβΩ : β < Om1) (ht : t ∈ Tset x)
    (ht1 : t < Om1) : eN x ≤ glA β t x :=
  eN_le (glA_facts hx hx1 hβ1 hβT hβΩ ht ht1).2.1 (glA_facts hx hx1 hβ1 hβT hβΩ ht ht1).2.2.2.1

/-! ## Bounds -/

/-- **Every ordinal below `Γ_{x+1}` lies in `Tˣ ∩ Ω₁`.** -/
theorem gl_T_of_lt_G {v : Ordinal.{0}} (hv : v < lgG x) : v ∈ Tset x ∧ v < Om1 := by
  obtain ⟨hGT, -, hG1, -, -⟩ := lgG_facts hx hx1
  exact ⟨vz_T_down hx hx1 hGT hG1 hv.le, hv.trans hG1⟩

/-- **Atoms with level and argument below `Γ_{x+1}` stay below it.** -/
theorem glA_lt_G {β t : Ordinal.{0}} (hβ : β < lgG x) (ht : t < lgG x) : glA β t x < lgG x := by
  obtain ⟨hβT, hβ1⟩ := gl_T_of_lt_G hx hx1 hβ
  obtain ⟨htT, ht1⟩ := gl_T_of_lt_G hx hx1 ht
  have hG := Lx.lx_vt_OmOm hx hx1
  have h0T : (0 : Ordinal.{0}) ∈ Tset x := mem_T_of_le hx hx1 zero_le
  have h := lgVt_lt_low hx hx1 hβT hβ1 htT ht1 h0T (hx.pos.trans hx1) (by rw [hG]; exact hβ) (by rw [hG]; exact ht)
  rwa [hG] at h

/-! ## The next `ε`-number after an atom -/

theorem gl_T_succ {t : Ordinal.{0}} (ht : t ∈ Tset x) (ht1 : t < Om1) : t + 1 ∈ Tset x ∧ t + 1 < Om1 := by
  obtain ⟨m, -, -, -, hTm, hm1, hmE⟩ := vz_next hx hx1
  have htm : t < m := (hTm t ht1).1 ht
  have h1 : t + 1 < m := (ev_isSuccLimit_of_inE hmE).add_one_lt htm
  exact ⟨(hTm _ (h1.trans hm1)).2 h1, h1.trans hm1⟩

/-- **The `ε`-number after `ϑˣ(Ω₁ + t)` is `ϑˣ(Ω₁ + t + 1)`.** -/
theorem glA_eN_one {t : Ordinal.{0}} (ht : t ∈ Tset x) (ht1 : t < Om1) : eN (glA 1 t x) = glA 1 (t + 1) x := by
  obtain ⟨h1T, h11⟩ := gl_one_T hx hx1
  obtain ⟨hsT, hs1⟩ := gl_T_succ hx hx1 ht ht1
  obtain ⟨-, -, -, hE1, -, -⟩ := glA_facts hx hx1 le_rfl h1T h11 hsT hs1
  obtain ⟨-, hxa, -, -, h1a, hta⟩ := glA_facts hx hx1 le_rfl h1T h11 ht ht1
  refine le_antisymm (eN_le (glA_lt_of hx hx1 le_rfl h1T h11 ht hsT hs1 (lt_add_one t)) hE1) ?_
  have hP1 : LuP 1 (eN (glA 1 t x)) := by
    have h := vzP_one.2 (eN_E (glA 1 t x)); unfold VzP at h; rwa [Nat.cast_one] at h
  refine glA_min hx hx1 le_rfl h1T h11 hsT hs1 hP1
    (hxa.trans (lt_eN _)) ((ev_isSuccLimit_of_inE (eN_E _)).add_one_lt (hta.trans (lt_eN _)))
    (h1a.trans (lt_eN _)) (fun σ hσ => ?_)
  have hσT : σ ∈ Tset x := vz_T_down hx hx1 hsT hs1 hσ.le
  have hσt : σ ≤ t := Order.lt_add_one_iff.1 hσ
  exact ((glA_le_iff hx hx1 le_rfl h1T h11 hσT (hσt.trans_lt ht1) ht ht1).2 hσt).trans_lt (lt_eN _)

/-- **The `ε`-number after `a = ϑˣ(Ω₁·β + t)`, `β ≥ 2`, is `ϑˣ(Ω₁ + a)`** (`a` is a fixed point of `ε`). -/
theorem glA_eN_two {β t : Ordinal.{0}} (hβ2 : 2 ≤ β) (hβT : β ∈ Tset x) (hβΩ : β < Om1) (ht : t ∈ Tset x)
    (ht1 : t < Om1) : eN (glA β t x) = glA 1 (glA β t x) x := by
  have hβ1 : (1 : Ordinal.{0}) ≤ β := one_le_two.trans hβ2
  obtain ⟨h1T, h11⟩ := gl_one_T hx hx1
  obtain ⟨haT, hxa, ha1, haE, -, -⟩ := glA_facts hx hx1 hβ1 hβT hβΩ ht ht1
  set a := glA β t x with hadef
  obtain ⟨-, -, -, hE1, h1b, hab⟩ := glA_facts hx hx1 le_rfl h1T h11 haT ha1
  refine le_antisymm (eN_le hab hE1) ?_
  have hP1 : LuP 1 (eN a) := by
    have h := vzP_one.2 (eN_E a); unfold VzP at h; rwa [Nat.cast_one] at h
  refine glA_min hx hx1 le_rfl h1T h11 haT ha1 hP1 (hxa.trans (lt_eN _)) (lt_eN a)
    ((one_lt_omega0.trans (omega0_lt_inE haE)).trans (lt_eN a)) (fun σ hσ => ?_)
  have hσT : σ ∈ Tset x := vz_T_down hx hx1 haT ha1 hσ.le
  have h12 : (1 : Ordinal.{0}) < β := lt_of_lt_of_le one_lt_two hβ2
  exact ((glA_lev hx hx1 le_rfl h12 hβT hβΩ ht ht1 hσT (hσ.trans ha1)).2 hσ).trans (lt_eN a)

end Atom

/-! ## Lemma EXACT for the atoms -/

section Pi

variable {σ ρ : Ordinal.{0}} (hB : Bases σ ρ)
include hB

theorem gl_pi_T {t : Ordinal.{0}} (ht : t ∈ TB ρ σ) (ht1 : t < Om1) : pi σ ρ t ∈ Tset σ ∧ pi σ ρ t < Om1 := by
  obtain ⟨hOT, hpO⟩ := pi_Om1 hB
  refine ⟨(pi_bijOn hB).1.mapsTo ht, ?_⟩
  rw [← hpO]; exact (pi_bijOn hB).2 ht hOT ht1

/-- **`π(Ω₁·β) = Ω₁·π(β)`** for every level `β ∈ Tᵖ[σ] ∩ Ω₁`. -/
theorem gl_pi_mul {β : Ordinal.{0}} (hβ : β ∈ TB ρ σ) (hβ1 : β < Om1) :
    Om1 * β ∈ TB ρ σ ∧ pi σ ρ (Om1 * β) = Om1 * pi σ ρ β := by
  rcases lt_or_ge β ρ with hβρ | hρβ
  · have hβσ : β < σ := (TB_inter_lt hB hβρ).1 hβ
    obtain ⟨h1, h2⟩ := luOm1_mul_TB hB β hβσ
    rw [pi_lt hB hβσ]; exact ⟨h1, h2⟩
  · exact lvPi_mul hB hβ hρβ hβ1

/-- **Lemma EXACT for the atom**: `π(ϑᵖ(Ω₁·β + t)) = ϑ^σ(Ω₁·π(β) + π(t))` for `β, t ∈ Tᵖ[σ] ∩ Ω₁`. -/
theorem glA_pi {β t : Ordinal.{0}} (hβ : β ∈ TB ρ σ) (hβ1 : β < Om1) (ht : t ∈ TB ρ σ) (ht1 : t < Om1) :
    glA β t ρ ∈ TB ρ σ ∧ pi σ ρ (glA β t ρ) = glA (pi σ ρ β) (pi σ ρ t) σ := by
  unfold glA
  obtain ⟨m1, m2⟩ := gl_pi_mul hB hβ hβ1
  obtain ⟨hγTB, hpγ⟩ := pi_add hB m1 ht
  rw [m2] at hpγ
  have hγ2 := luOm1_mul_lt hβ1 ht1
  obtain ⟨hvT, -, -, -, hvP⟩ := vt_memTwo hB.2.1 hB.2.2.2 hγTB.1 hγ2
  refine ⟨⟨hvT, by rw [hvP]; exact hγTB.2⟩, ?_⟩
  rw [pi_vt_two hB hγTB hγ2, hpγ]

/-- **Lemma EXACT for the next `ε`-number after the atom.** -/
theorem glA_eN_pi {β t : Ordinal.{0}} (hβ1 : 1 ≤ β) (hβ : β ∈ TB ρ σ) (hβΩ : β < Om1) (ht : t ∈ TB ρ σ)
    (ht1 : t < Om1) :
    eN (glA β t ρ) ∈ TB ρ σ ∧ pi σ ρ (eN (glA β t ρ)) = eN (glA (pi σ ρ β) (pi σ ρ t) σ) := by
  have hρE := hB.2.1
  have hρ1 := hB.2.2.2
  have hσE := hB.1
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  obtain ⟨hpT, hp1⟩ := gl_pi_T hB ht ht1
  obtain ⟨hpβT, hpβ1⟩ := gl_pi_T hB hβ hβΩ
  obtain ⟨o1, o2⟩ := one_TB hB
  rcases (hβ1.lt_or_eq) with hβ2 | hβeq
  · have hβ2' : 2 ≤ β := by rw [← one_add_one_eq_two]; exact add_one_le_of_lt hβ2
    have hpβ2 : 2 ≤ pi σ ρ β := by
      have h1 : pi σ ρ 1 < pi σ ρ β := (pi_bijOn hB).2 o1 hβ hβ2
      rw [o2] at h1
      rw [← one_add_one_eq_two]; exact add_one_le_of_lt h1
    obtain ⟨a1, a2⟩ := glA_pi hB hβ hβΩ ht ht1
    have ha1 := (glA_facts hρE hρ1 hβ1 hβ.1 hβΩ ht.1 ht1).2.2.1
    rw [glA_eN_two hρE hρ1 hβ2' hβ.1 hβΩ ht.1 ht1, glA_eN_two hσE hσ1 hpβ2 hpβT hpβ1 hpT hp1, ← a2]
    have := glA_pi hB o1 (gl_one_T hρE hρ1).2 a1 ha1
    rwa [o2] at this
  · subst hβeq
    obtain ⟨s1, s2⟩ := pi_add hB ht o1
    rw [o2] at s2
    have hs1 := (gl_T_succ hρE hρ1 ht.1 ht1).2
    rw [o2, glA_eN_one hρE hρ1 ht.1 ht1, glA_eN_one hσE hσ1 hpT hp1, ← s2]
    have := glA_pi hB o1 (gl_one_T hρE hρ1).2 s1 hs1
    rwa [o2] at this

end Pi

end Googology.Trans.PoR.InaccPsi.R2.Gl
