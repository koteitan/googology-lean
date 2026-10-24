import Googology.Trans.PoR.InaccPsi.R2.GlR0

/-!
# CODES BELOW `Γ_{Ω₁+1}`: gates of the parts, the bound `Γ_{x+1}`, positivity, successors

* `glG_lt_Om1`, `gl_parts_g`, `gl_parts_Q`, `gl_parts_lev` (the parts of a code, its level included, have their
  gates below every `x > ω` above the gate of the code), `gl_E_g` (the bracket's `ε`-number too);
* `glBA_facts` (the atom at an `ε`-number base `x < Ω₁`), `glR_lt_G` (**every reading lies below `Γ_{x+1}`**, so in
  `Tˣ ∩ Ω₁`), `glR_T`, `glR_pos`, `gl_atom`, `gl_lead` (**`ϑˣ(Ω₁·α(x)+η(x)) ≤ c(x)`**);
* `glR_succ`, `glR_succ_all` (**`(b+1)(x) = b(x) + 1`**), `glG_succ`, `glG_le_succ`, `glG_le_succ_all`.

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gl

open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu
open Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh Googology.Trans.PoR.InaccPsi.R2.Gi
  Googology.Trans.PoR.InaccPsi.R2.Gk
open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2

theorem glQE_le_I (e : Ordinal.{0}) : glQ (glI e) ≤ glQE e := le_max_right _ _

theorem glQE_le_K (e : Ordinal.{0}) : glQ (glK e) ≤ glQE e := le_max_left _ _

theorem glG_lt_Om1 : ∀ c, c < gcG 0 → glG c < Om1 := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc
  rcases lt_or_ge c gfE with hcE | hcE
  · rw [glG_low hcE]; exact gtc_lt_Om1 c hcE
  have hnc := gl_idx_lt hcE hc
  have hlc := gl_lev_lt hcE hc
  obtain ⟨-, -, -, -, -, hkc, hrc, hdc⟩ := gl_parts hcE
  rw [glG_dec hcE hc]
  have hQ : ∀ a, a < c → glQ a < Om1 := fun a ha => (glQ_le a).trans_lt (IH a ha (ha.trans hc))
  exact max_lt (max_lt (max_lt (hQ _ hlc) (hQ _ hnc)) (hQ _ hkc)) (max_lt (hQ _ hdc) (IH _ hrc (hrc.trans hc)))

theorem gl_parts_Q {x c : Ordinal.{0}} (h1 : gfE ≤ c) (h2 : c < gcG 0) (hg : glG c < x) :
    glQE (guE c) < x ∧ glQ (log (guE c) c) < x ∧ glQ (c / guE c ^ log (guE c) c) < x ∧
      glG (c % guE c ^ log (guE c) c) < x := by
  rw [glG_dec h1 h2] at hg
  exact ⟨(le_max_left _ _).trans_lt ((le_max_left _ _).trans_lt hg),
    (le_max_right _ _).trans_lt ((le_max_left _ _).trans_lt hg),
    (le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hg),
    (le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hg)⟩

/-- **The parts have their gates below `x`** (`x > ω`) when the code has. -/
theorem gl_parts_g {x c : Ordinal.{0}} (hωx : ω < x) (h1 : gfE ≤ c) (h2 : c < gcG 0) (hg : glG c < x) :
    glG (glI (guE c)) < x ∧ glG (log (guE c) c) < x ∧ glG (c / guE c ^ log (guE c) c) < x ∧
      glG (c % guE c ^ log (guE c) c) < x := by
  obtain ⟨q0, q1, q2, g3⟩ := gl_parts_Q h1 h2 hg
  exact ⟨glG_of_Q hωx ((glQE_le_I _).trans_lt q0), glG_of_Q hωx q1, glG_of_Q hωx q2, g3⟩

/-- **The level has its gate below `x`** (`x > ω`) when the code has. -/
theorem gl_parts_lev {x c : Ordinal.{0}} (hωx : ω < x) (h1 : gfE ≤ c) (h2 : c < gcG 0) (hg : glG c < x) :
    glG (glK (guE c)) < x :=
  glG_of_Q hωx ((glQE_le_K _).trans_lt (gl_parts_Q h1 h2 hg).1)

/-- The bracket's `ε`-number has its gate below `x` when the code has. -/
theorem gl_E_g {x c : Ordinal.{0}} (h1 : gfE ≤ c) (h2 : c < gcG 0) (hg : glG c < x) : glG (guE c) < x := by
  rw [glG_base (guE_E c) (gl_Om1_lt_E h1) ((gl_E_le h1).trans_lt h2)]
  exact (gl_parts_Q h1 h2 hg).1

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

/-- **The atom of the base reading** at an `ε`-number base `x < Ω₁`, level and argument below `Γ_{x+1}`. -/
theorem glBA_facts {β t : Ordinal.{0}} (hβ1 : 1 ≤ β) (hβG : β < lgG x) (htG : t < lgG x) :
    glBA β t x = glA β t x ∧ InE (glBA β t x) ∧ x < glBA β t x ∧ t < glBA β t x ∧ β < glBA β t x ∧
      glBA β t x < lgG x ∧ eN x ≤ glBA β t x ∧ glBA β t x ∈ Tset x ∧ glBA β t x < Om1 := by
  obtain ⟨hβT, hβΩ⟩ := gl_T_of_lt_G hx hx1 hβG
  obtain ⟨htT, ht1⟩ := gl_T_of_lt_G hx hx1 htG
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := glA_facts hx hx1 hβ1 hβT hβΩ htT ht1
  rw [glBA_eq hx hx1]
  exact ⟨rfl, h4, h2, h6, h5, glA_lt_G hx hx1 hβG htG, gl_eN_le_glA hx hx1 hβ1 hβT hβΩ htT ht1, h1, h3⟩

theorem glR_pos0 : ∀ c, c ≠ 0 → c < gcG 0 → glG c < x → 0 < glR c x ∧ glR c x < lgG x := by
  have hωx := omega0_lt_inE hx
  obtain ⟨-, hxG, -, hGE, -⟩ := lgG_facts hx hx1
  have heG : eN x < lgG x := (gT_lt_lgG hx hx1 0)
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc0 hc hg
  rcases lt_or_ge c gfE with hcE | hcE
  · rw [glG_low hcE] at hg
    rw [glR_low hcE]
    exact ⟨rdc_pos hx hc0 hcE, (rdc_lt_eN hx c hg).trans heG⟩
  have hnc := gl_idx_lt hcE hc
  have hlc := gl_lev_lt hcE hc
  obtain ⟨hk1, -, -, -⟩ := gl_E_data hcE hc
  obtain ⟨hj0, hd0, -, -, -, hkc, hrc, hdc⟩ := gl_parts hcE
  obtain ⟨g0, g1, g2, g3⟩ := gl_parts_g hωx hcE hc hg
  have gl := gl_parts_lev hωx hcE hc hg
  have hα := IH _ hlc (lt_of_lt_of_le zero_lt_one hk1).ne' (hlc.trans hc) gl
  have hαR1 : 1 ≤ glR (glK (guE c)) x := one_le_iff_pos.2 hα.1
  have hηG : glR (glI (guE c)) x < lgG x := by
    rcases eq_or_ne (glI (guE c)) 0 with h0 | h0
    · rw [h0, glR_zero]; exact lgG_pos hx hx1
    · exact (IH _ hnc h0 (hnc.trans hc) g0).2
  obtain ⟨-, hAE, -, -, -, hAG, -⟩ := glBA_facts hx hx1 hαR1 hα.2 hηG
  have hj := IH _ hkc hj0 (hkc.trans hc) g1
  have hd := IH _ hdc hd0 (hdc.trans hc) g2
  have hr : glR (c % guE c ^ log (guE c) c) x < lgG x := by
    rcases eq_or_ne (c % guE c ^ log (guE c) c) 0 with h0 | h0
    · rw [h0, glR_zero]; exact lgG_pos hx hx1
    · exact (IH _ hrc h0 (hrc.trans hc) g3).2
  rw [glR_dec hcE hc]
  refine ⟨lt_of_lt_of_le (mul_pos (opow_pos _ hAE.pos) hd.1) le_self_add, ?_⟩
  rw [gu_pow_eq hAE]
  exact (inE_indec hGE).add_lt (hGE.mul_lt (hGE.opow_lt (hGE.mul_lt hAG hj.2)) hd.2) hr

/-- **Every reading lies below `Γ_{x+1}`.** -/
theorem glR_lt_G {c : Ordinal.{0}} (hc : c < gcG 0) (hg : glG c < x) : glR c x < lgG x := by
  rcases eq_or_ne c 0 with h0 | h0
  · rw [h0, glR_zero]; exact lgG_pos hx hx1
  · exact (glR_pos0 hx hx1 c h0 hc hg).2

theorem glR_T {c : Ordinal.{0}} (hc : c < gcG 0) (hg : glG c < x) : glR c x ∈ Tset x ∧ glR c x < Om1 :=
  gl_T_of_lt_G hx hx1 (glR_lt_G hx hx1 hc hg)

theorem glR_pos {c : Ordinal.{0}} (hc0 : c ≠ 0) (hc : c < gcG 0) (hg : glG c < x) : 0 < glR c x :=
  (glR_pos0 hx hx1 c hc0 hc hg).1

theorem glR_pos' {c : Ordinal.{0}} (hc0 : c ≠ 0) (hc : c < gcG 0) (hg : glG c < x) : 1 ≤ glR c x :=
  one_le_iff_pos.2 (glR_pos hx hx1 hc0 hc hg)

/-- The atom of the bracket of `c` at `x`. -/
theorem gl_atom {c : Ordinal.{0}} (h1 : gfE ≤ c) (h2 : c < gcG 0) (hg : glG c < x) :
    glBA (glR (glK (guE c)) x) (glR (glI (guE c)) x) x = glA (glR (glK (guE c)) x) (glR (glI (guE c)) x) x ∧
      InE (glBA (glR (glK (guE c)) x) (glR (glI (guE c)) x) x) ∧
      x < glBA (glR (glK (guE c)) x) (glR (glI (guE c)) x) x ∧
      glR (glI (guE c)) x < glBA (glR (glK (guE c)) x) (glR (glI (guE c)) x) x ∧
      glR (glK (guE c)) x < glBA (glR (glK (guE c)) x) (glR (glI (guE c)) x) x ∧
      glBA (glR (glK (guE c)) x) (glR (glI (guE c)) x) x < lgG x ∧
      eN x ≤ glBA (glR (glK (guE c)) x) (glR (glI (guE c)) x) x ∧
      glBA (glR (glK (guE c)) x) (glR (glI (guE c)) x) x ∈ Tset x ∧
      glBA (glR (glK (guE c)) x) (glR (glI (guE c)) x) x < Om1 := by
  have hωx := omega0_lt_inE hx
  have hnc := gl_idx_lt h1 h2
  have hlc := gl_lev_lt h1 h2
  obtain ⟨hk1, -, -, -⟩ := gl_E_data h1 h2
  obtain ⟨g0, -, -, -⟩ := gl_parts_g hωx h1 h2 hg
  have gl := gl_parts_lev hωx h1 h2 hg
  exact glBA_facts hx hx1 (glR_pos' hx hx1 (lt_of_lt_of_le zero_lt_one hk1).ne' (hlc.trans h2) gl)
    (glR_lt_G hx hx1 (hlc.trans h2) gl) (glR_lt_G hx hx1 (hnc.trans h2) g0)

/-- **A code is read above its atom**: `ϑˣ(Ω₁·α(x) + η(x)) ≤ c(x)`. -/
theorem gl_lead {c : Ordinal.{0}} (h1 : gfE ≤ c) (h2 : c < gcG 0) (hg : glG c < x) :
    glBA (glR (glK (guE c)) x) (glR (glI (guE c)) x) x ^ glR (log (guE c) c) x *
      glR (c / guE c ^ log (guE c) c) x ≤ glR c x ∧
      glBA (glR (glK (guE c)) x) (glR (glI (guE c)) x) x ≤ glR c x := by
  obtain ⟨hk, hd0, -, -, -, hkc, -, hdc⟩ := gl_parts h1
  obtain ⟨-, g1, g2, -⟩ := gl_parts_g (omega0_lt_inE hx) h1 h2 hg
  rw [glR_dec h1 h2]
  refine ⟨le_self_add, le_trans ?_ le_self_add⟩
  set B := glBA (glR (glK (guE c)) x) (glR (glI (guE c)) x) x
  have hB := (gl_atom hx hx1 h1 h2 hg).2.1
  calc B = B ^ (1 : Ordinal.{0}) * 1 := by rw [opow_one, mul_one]
    _ ≤ B ^ glR (log (guE c) c) x * 1 :=
        mul_le_mul_left (opow_le_opow_right hB.pos (glR_pos' hx hx1 hk (hkc.trans h2) g1)) _
    _ ≤ _ := mul_le_mul_right (glR_pos' hx hx1 hd0 (hdc.trans h2) g2) _

end Base

/-! ## Successors -/

/-- The successor of a code `b ≥ ε_{Ω₁+1}` in normal form: the rest goes up by one. -/
theorem gl_succ_nf {b : Ordinal.{0}} (h1 : gfE ≤ b) :
    b + 1 = guE b ^ log (guE b) b * (b / guE b ^ log (guE b) b) + (b % guE b ^ log (guE b) b + 1) ∧
      b % guE b ^ log (guE b) b + 1 < guE b ^ log (guE b) b ∧
      guE b ^ log (guE b) b * (b / guE b ^ log (guE b) b) + (b % guE b ^ log (guE b) b + 1) < eN (guE b) := by
  have hbN := gl_lt_eN h1
  obtain ⟨hk, -, -, hr, hdec, -, -, -⟩ := gl_parts h1
  have e : b + 1 = guE b ^ log (guE b) b * (b / guE b ^ log (guE b) b) + (b % guE b ^ log (guE b) b + 1) := by
    rw [← add_assoc]; exact congrArg (· + 1) hdec.symm
  refine ⟨e, gu_succ_lt (guE_E b) hk hr, ?_⟩
  rw [← e]
  exact (ev_isSuccLimit_of_inE (eN_E _)).add_one_lt hbN

theorem glR_succ : ∀ b, b + 1 < gcG 0 → ∀ x : Ordinal.{0}, glR (b + 1) x = glR b x + 1 := by
  intro b
  induction b using WellFoundedLT.induction with
  | ind b IH =>
  intro hb1 x
  have hbB : b < gcG 0 := (lt_add_one b).trans hb1
  rcases lt_or_ge b gfE with hbE | hbE
  · rw [glR_low hbE, glR_low (succ_lt_eW hbE), (rdc_succ b hbE x).1]
  obtain ⟨hk, hd0, hdE, -, -, -, hrb, -⟩ := gl_parts hbE
  obtain ⟨e, hr1, hv⟩ := gl_succ_nf hbE
  have hr1B : b % guE b ^ log (guE b) b + 1 < gcG 0 := lt_of_le_of_lt (by rw [e]; exact le_add_self) hb1
  rw [e, glR_cnf (guE_E b) (gl_Om1_lt_E hbE) hk hd0 hdE hr1 hv (e ▸ hb1), IH _ hrb hr1B x, glR_dec hbE hbB x,
    add_assoc]

theorem glR_succ_all (b x : Ordinal.{0}) : glR (b + 1) x = glR b x + 1 := by
  rcases lt_or_ge (b + 1) (gcG 0) with h | h
  · exact glR_succ b h x
  · have hb : gcG 0 ≤ b := by
      by_contra hb; push Not at hb; exact absurd (gl_G0_lim.add_one_lt hb) (not_lt.2 h)
    rw [glR_high h, glR_high hb]

theorem glG_succ {Z : Ordinal.{0}} (hZ : IsSuccLimit Z) : ∀ b, b + 1 < gcG 0 → glG b < Z → glG (b + 1) < Z := by
  intro b
  induction b using WellFoundedLT.induction with
  | ind b IH =>
  intro hb1 hg
  rcases lt_or_ge b gfE with hbE | hbE
  · rw [glG_low hbE] at hg
    rw [glG_low (succ_lt_eW hbE)]
    exact (rdc_succ b hbE 0).2.2.trans_lt (hZ.add_one_lt hg)
  have hbB : b < gcG 0 := (lt_add_one b).trans hb1
  obtain ⟨hk, hd0, hdE, -, -, -, hrb, -⟩ := gl_parts hbE
  obtain ⟨e, hr1, hv⟩ := gl_succ_nf hbE
  have hr1B : b % guE b ^ log (guE b) b + 1 < gcG 0 := lt_of_le_of_lt (by rw [e]; exact le_add_self) hb1
  rw [glG_dec hbE hbB] at hg
  rw [e, glG_cnf (guE_E b) (gl_Om1_lt_E hbE) hk hd0 hdE hr1 hv (e ▸ hb1)]
  exact max_lt ((le_max_left _ _).trans_lt hg) (max_lt ((le_max_left _ _).trans_lt
    ((le_max_right _ _).trans_lt hg)) (IH _ hrb hr1B ((le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hg))))

theorem glG_le_succ : ∀ b, b + 1 < gcG 0 → glG b ≤ glG (b + 1) := by
  intro b
  induction b using WellFoundedLT.induction with
  | ind b IH =>
  intro hb1
  rcases lt_or_ge b gfE with hbE | hbE
  · rw [glG_low hbE, glG_low (succ_lt_eW hbE)]; exact (rdc_succ b hbE 0).2.1
  have hbB : b < gcG 0 := (lt_add_one b).trans hb1
  obtain ⟨hk, hd0, hdE, -, -, -, hrb, -⟩ := gl_parts hbE
  obtain ⟨e, hr1, hv⟩ := gl_succ_nf hbE
  have hr1B : b % guE b ^ log (guE b) b + 1 < gcG 0 := lt_of_le_of_lt (by rw [e]; exact le_add_self) hb1
  rw [glG_dec hbE hbB, e, glG_cnf (guE_E b) (gl_Om1_lt_E hbE) hk hd0 hdE hr1 hv (e ▸ hb1)]
  exact max_le_max le_rfl (max_le_max le_rfl (IH _ hrb hr1B))

theorem glG_le_succ_all (b : Ordinal.{0}) : glG b ≤ glG (b + 1) := by
  rcases lt_or_ge (b + 1) (gcG 0) with h | h
  · exact glG_le_succ b h
  · have hb : gcG 0 ≤ b := by
      by_contra hb; push Not at hb; exact absurd (gl_G0_lim.add_one_lt hb) (not_lt.2 h)
    rw [glG_high h, glG_high hb]

end Googology.Trans.PoR.InaccPsi.R2.Gl
