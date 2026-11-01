import Googology.Trans.PoR.InaccPsi.R2.XuR

/-!
# XuR1: CODES BELOW `Γ(1)`: gates of the parts, the bound `Γ_{x+2}`, positivity, successors

* `xuG_lt_Om1`, `xu_parts_Q`, `xu_parts_g`, `xu_parts_lev` (the parts of a code, its level included, have their
  gates below every `x > ω` above the gate of the code), `xu_E_g` (the bracket's `ε`-number too);
* `xuA_facts` (the atom `ϑˣ(Ω₁·β + t)` at an `ε`-number base `x < Ω₁`, `β, t < Γ_{x+2}`), `xuR_pos0`, `xuR_lt1`
  (**every reading lies below `Γ_{x+2}`**, so in `Tˣ ∩ Ω₁`), `xuR_T`, `xuR_pos`, `xu_atom`, `xu_lead`
  (**`ϑˣ(Ω₁·α(x)+η(x)) ≤ c(x)`**);
* `xuR_succ` (**`(b+1)(x) = b(x) + 1`**), `xuG_succ`, `xuG_le_succ`.

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Xu

open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2 Googology.Notation.InaccPsi
  Googology.Notation.InaccPsi.InaccSeq Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Gn
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Wt Googology.Trans.PoR.InaccPsi.R2.Gk
  Googology.Trans.PoR.InaccPsi.R2.Gh Googology.Trans.PoR.InaccPsi.R2.Gi Googology.Trans.PoR.InaccPsi.R2.Gm
  Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Hi

theorem xuG_lt_Om1 : ∀ c, c < gcG 1 → xuG c < Om1 := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc
  rcases lt_or_ge c (Wj.wjT 0) with hct | hct
  · rw [xuG_low hct]; exact wtD.g_lt c (xu_lt_wtB hct)
  have hnc := xu_idx_lt hct hc
  have hlc := xu_lev_lt hct hc
  obtain ⟨-, -, -, -, -, hkc, hrc, hdc⟩ := gl_parts (xu_gfE_le hct)
  rw [xuG_dec hct hc]
  have hQ : ∀ a, a < c → xuQ a < Om1 := fun a ha => (xuQ_le a).trans_lt (IH a ha (ha.trans hc))
  exact max_lt (max_lt (max_lt (hQ _ hlc) (hQ _ hnc)) (hQ _ hkc)) (max_lt (hQ _ hdc) (IH _ hrc (hrc.trans hc)))

theorem xu_parts_Q {x c : Ordinal.{0}} (h1 : Wj.wjT 0 ≤ c) (h2 : c < gcG 1) (hg : xuG c < x) :
    xuQE (guE c) < x ∧ xuQ (log (guE c) c) < x ∧ xuQ (c / guE c ^ log (guE c) c) < x ∧
      xuG (c % guE c ^ log (guE c) c) < x := by
  rw [xuG_dec h1 h2] at hg
  exact ⟨(le_max_left _ _).trans_lt ((le_max_left _ _).trans_lt hg),
    (le_max_right _ _).trans_lt ((le_max_left _ _).trans_lt hg),
    (le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hg),
    (le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hg)⟩

/-- **The parts have their gates below `x`** (`x > ω`) when the code has. -/
theorem xu_parts_g {x c : Ordinal.{0}} (hωx : ω < x) (h1 : Wj.wjT 0 ≤ c) (h2 : c < gcG 1) (hg : xuG c < x) :
    xuG (xuI (guE c)) < x ∧ xuG (log (guE c) c) < x ∧ xuG (c / guE c ^ log (guE c) c) < x ∧
      xuG (c % guE c ^ log (guE c) c) < x := by
  obtain ⟨q0, q1, q2, g3⟩ := xu_parts_Q h1 h2 hg
  exact ⟨xuG_of_Q hωx ((xuQE_le_I _).trans_lt q0), xuG_of_Q hωx q1, xuG_of_Q hωx q2, g3⟩

theorem xu_parts_lev {x c : Ordinal.{0}} (hωx : ω < x) (h1 : Wj.wjT 0 ≤ c) (h2 : c < gcG 1) (hg : xuG c < x) :
    xuG (xuK (guE c)) < x :=
  xuG_of_Q hωx ((xuQE_le_K _).trans_lt (xu_parts_Q h1 h2 hg).1)

theorem xu_E_lt {c : Ordinal.{0}} (h1 : Wj.wjT 0 ≤ c) (h2 : c < gcG 1) : guE c < gcG 1 :=
  (gl_E_le (xu_gfE_le h1)).trans_lt h2

/-- The bracket's `ε`-number has its gate below `x` when the code has. -/
theorem xu_E_g {x c : Ordinal.{0}} (h1 : Wj.wjT 0 ≤ c) (h2 : c < gcG 1) (hg : xuG c < x) : xuG (guE c) < x := by
  rw [xuG_base (guE_E c) (xu_E_ge h1) (xu_E_lt h1 h2)]
  exact (xu_parts_Q h1 h2 hg).1

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

/-- **The atom** at an `ε`-number base `x < Ω₁`, level and argument below `Γ_{x+2}`. -/
theorem xuA_facts {β t : Ordinal.{0}} (hβ1 : 1 ≤ β) (hβG : β < gq 1 x) (htG : t < gq 1 x) :
    InE (glA β t x) ∧ x < glA β t x ∧ t < glA β t x ∧ β < glA β t x ∧
      glA β t x < gq 1 x ∧ eN x ≤ glA β t x ∧ glA β t x ∈ Tset x ∧ glA β t x < Om1 ∧
      β ∈ Tset x ∧ β < Om1 ∧ t ∈ Tset x ∧ t < Om1 := by
  obtain ⟨hβT, hβΩ⟩ := gm1_T hx hx1 hβG
  obtain ⟨htT, ht1⟩ := gm1_T hx hx1 htG
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := glA_facts hx hx1 hβ1 hβT hβΩ htT ht1
  exact ⟨h4, h2, h6, h5, hi_glA_lt1 hx hx1 hβG htG, gl_eN_le_glA hx hx1 hβ1 hβT hβΩ htT ht1, h1, h3,
    hβT, hβΩ, htT, ht1⟩

theorem xu_wt_lt1 {c : Ordinal.{0}} (hc : c < Wj.wjT 0) (hg : wtD.g c < x) : wtD.R c x < gq 1 x :=
  (wtD.R_lt_b x hx hx1 c (xu_lt_wtB hc) hg).trans (wtD.b_lt1 hx hx1)

theorem xuR_pos0 : ∀ c, c ≠ 0 → c < gcG 1 → xuG c < x → 0 < xuR c x ∧ xuR c x < gq 1 x := by
  have hωx := omega0_lt_inE hx
  obtain ⟨-, -, -, hGE⟩ := gm1_facts hx hx1
  have hq0 : 0 < gq 1 x := hGE.pos
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc0 hc hg
  rcases lt_or_ge c (Wj.wjT 0) with hct | hct
  · rw [xuG_low hct] at hg
    rw [xuR_low hct]
    exact ⟨wtD.R_pos x hx hx1 c hc0 (xu_lt_wtB hct) hg, xu_wt_lt1 hx hx1 hct hg⟩
  have hnc := xu_idx_lt hct hc
  have hlc := xu_lev_lt hct hc
  obtain ⟨hk1, -, -, -⟩ := xu_E_data hct hc
  obtain ⟨hj0, hd0, -, -, -, hkc, hrc, hdc⟩ := gl_parts (xu_gfE_le hct)
  obtain ⟨g0, g1, g2, g3⟩ := xu_parts_g hωx hct hc hg
  have gl := xu_parts_lev hωx hct hc hg
  have hα := IH _ hlc (lt_of_lt_of_le zero_lt_one hk1).ne' (hlc.trans hc) gl
  have hαR1 : 1 ≤ xuR (xuK (guE c)) x := one_le_iff_pos.2 hα.1
  have hηG : xuR (xuI (guE c)) x < gq 1 x := by
    rcases eq_or_ne (xuI (guE c)) 0 with h0 | h0
    · rw [h0, xuR_zero]; exact hq0
    · exact (IH _ hnc h0 (hnc.trans hc) g0).2
  obtain ⟨hAE, -, -, -, hAG, -⟩ := xuA_facts hx hx1 hαR1 hα.2 hηG
  have hj := IH _ hkc hj0 (hkc.trans hc) g1
  have hd := IH _ hdc hd0 (hdc.trans hc) g2
  have hr : xuR (c % guE c ^ log (guE c) c) x < gq 1 x := by
    rcases eq_or_ne (c % guE c ^ log (guE c) c) 0 with h0 | h0
    · rw [h0, xuR_zero]; exact hq0
    · exact (IH _ hrc h0 (hrc.trans hc) g3).2
  rw [xuR_dec hct hc]
  refine ⟨lt_of_lt_of_le (mul_pos (opow_pos _ hAE.pos) hd.1) le_self_add, ?_⟩
  rw [gu_pow_eq hAE]
  exact (inE_indec hGE).add_lt (hGE.mul_lt (hGE.opow_lt (hGE.mul_lt hAG hj.2)) hd.2) hr

/-- **Every reading lies below `Γ_{x+2}`.** -/
theorem xuR_lt1 {c : Ordinal.{0}} (hc : c < gcG 1) (hg : xuG c < x) : xuR c x < gq 1 x := by
  rcases eq_or_ne c 0 with h0 | h0
  · rw [h0, xuR_zero]; exact (gm1_facts hx hx1).2.2.2.pos
  · exact (xuR_pos0 hx hx1 c h0 hc hg).2

theorem xuR_T {c : Ordinal.{0}} (hc : c < gcG 1) (hg : xuG c < x) : xuR c x ∈ Tset x ∧ xuR c x < Om1 :=
  gm1_T hx hx1 (xuR_lt1 hx hx1 hc hg)

theorem xuR_pos {c : Ordinal.{0}} (hc0 : c ≠ 0) (hc : c < gcG 1) (hg : xuG c < x) : 0 < xuR c x :=
  (xuR_pos0 hx hx1 c hc0 hc hg).1

theorem xuR_pos' {c : Ordinal.{0}} (hc0 : c ≠ 0) (hc : c < gcG 1) (hg : xuG c < x) : 1 ≤ xuR c x :=
  one_le_iff_pos.2 (xuR_pos hx hx1 hc0 hc hg)

/-- The atom of the bracket of `c` at `x`. -/
theorem xu_atom {c : Ordinal.{0}} (h1 : Wj.wjT 0 ≤ c) (h2 : c < gcG 1) (hg : xuG c < x) :
    InE (glA (xuR (xuK (guE c)) x) (xuR (xuI (guE c)) x) x) ∧
      x < glA (xuR (xuK (guE c)) x) (xuR (xuI (guE c)) x) x ∧
      xuR (xuI (guE c)) x < glA (xuR (xuK (guE c)) x) (xuR (xuI (guE c)) x) x ∧
      xuR (xuK (guE c)) x < glA (xuR (xuK (guE c)) x) (xuR (xuI (guE c)) x) x ∧
      glA (xuR (xuK (guE c)) x) (xuR (xuI (guE c)) x) x < gq 1 x ∧
      eN x ≤ glA (xuR (xuK (guE c)) x) (xuR (xuI (guE c)) x) x ∧
      glA (xuR (xuK (guE c)) x) (xuR (xuI (guE c)) x) x ∈ Tset x ∧
      glA (xuR (xuK (guE c)) x) (xuR (xuI (guE c)) x) x < Om1 := by
  have hωx := omega0_lt_inE hx
  have hnc := xu_idx_lt h1 h2
  have hlc := xu_lev_lt h1 h2
  obtain ⟨hk1, -, -, -⟩ := xu_E_data h1 h2
  obtain ⟨g0, -, -, -⟩ := xu_parts_g hωx h1 h2 hg
  have gl := xu_parts_lev hωx h1 h2 hg
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, -⟩ :=
    xuA_facts hx hx1 (xuR_pos' hx hx1 (lt_of_lt_of_le zero_lt_one hk1).ne' (hlc.trans h2) gl)
      (xuR_lt1 hx hx1 (hlc.trans h2) gl) (xuR_lt1 hx hx1 (hnc.trans h2) g0)
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩

/-- **A code is read above its atom.** -/
theorem xu_lead {c : Ordinal.{0}} (h1 : Wj.wjT 0 ≤ c) (h2 : c < gcG 1) (hg : xuG c < x) :
    glA (xuR (xuK (guE c)) x) (xuR (xuI (guE c)) x) x ^ xuR (log (guE c) c) x *
      xuR (c / guE c ^ log (guE c) c) x ≤ xuR c x ∧
      glA (xuR (xuK (guE c)) x) (xuR (xuI (guE c)) x) x ≤ xuR c x := by
  obtain ⟨hk, hd0, -, -, -, hkc, -, hdc⟩ := gl_parts (xu_gfE_le h1)
  obtain ⟨-, g1, g2, -⟩ := xu_parts_g (omega0_lt_inE hx) h1 h2 hg
  rw [xuR_dec h1 h2]
  refine ⟨le_self_add, le_trans ?_ le_self_add⟩
  set B := glA (xuR (xuK (guE c)) x) (xuR (xuI (guE c)) x) x
  have hB := (xu_atom hx hx1 h1 h2 hg).1
  calc B = B ^ (1 : Ordinal.{0}) * 1 := by rw [opow_one, mul_one]
    _ ≤ B ^ xuR (log (guE c) c) x * 1 :=
        mul_le_mul_left (opow_le_opow_right hB.pos (xuR_pos' hx hx1 hk (hkc.trans h2) g1)) _
    _ ≤ _ := mul_le_mul_right (xuR_pos' hx hx1 hd0 (hdc.trans h2) g2) _

end Base

/-! ## Successors -/

theorem xuR_succ : ∀ b, b + 1 < gcG 1 → ∀ x : Ordinal.{0}, xuR (b + 1) x = xuR b x + 1 := by
  intro b
  induction b using WellFoundedLT.induction with
  | ind b IH =>
  intro hb1 x
  have hbB : b < gcG 1 := (lt_add_one b).trans hb1
  rcases lt_or_ge b (Wj.wjT 0) with hbt | hbt
  · have hb1t : b + 1 < Wj.wjT 0 := (ev_isSuccLimit_of_inE xu_t0_E).add_one_lt hbt
    rw [xuR_low hbt, xuR_low hb1t, wtD.R_succ]
  have hbE := xu_gfE_le hbt
  obtain ⟨hk, hd0, hdE, -, -, -, hrb, -⟩ := gl_parts hbE
  obtain ⟨e, hr1, hv⟩ := gl_succ_nf hbE
  have hr1B : b % guE b ^ log (guE b) b + 1 < gcG 1 := lt_of_le_of_lt (by rw [e]; exact le_add_self) hb1
  rw [e, xuR_cnf (guE_E b) (xu_E_ge hbt) hk hd0 hdE hr1 hv (e ▸ hb1), IH _ hrb hr1B x, xuR_dec hbt hbB x,
    add_assoc]

theorem xuG_succ {Z : Ordinal.{0}} (hZ : IsSuccLimit Z) : ∀ b, b + 1 < gcG 1 → xuG b < Z → xuG (b + 1) < Z := by
  intro b
  induction b using WellFoundedLT.induction with
  | ind b IH =>
  intro hb1 hg
  rcases lt_or_ge b (Wj.wjT 0) with hbt | hbt
  · have hb1t : b + 1 < Wj.wjT 0 := (ev_isSuccLimit_of_inE xu_t0_E).add_one_lt hbt
    rw [xuG_low hbt] at hg
    rw [xuG_low hb1t]
    exact wtD.g_succ Z hZ b (xu_lt_wtB hb1t) hg
  have hbB : b < gcG 1 := (lt_add_one b).trans hb1
  have hbE := xu_gfE_le hbt
  obtain ⟨hk, hd0, hdE, -, -, -, hrb, -⟩ := gl_parts hbE
  obtain ⟨e, hr1, hv⟩ := gl_succ_nf hbE
  have hr1B : b % guE b ^ log (guE b) b + 1 < gcG 1 := lt_of_le_of_lt (by rw [e]; exact le_add_self) hb1
  rw [xuG_dec hbt hbB] at hg
  rw [e, xuG_cnf (guE_E b) (xu_E_ge hbt) hk hd0 hdE hr1 hv (e ▸ hb1)]
  exact max_lt ((le_max_left _ _).trans_lt hg) (max_lt ((le_max_left _ _).trans_lt
    ((le_max_right _ _).trans_lt hg)) (IH _ hrb hr1B ((le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hg))))

theorem xuG_le_succ : ∀ b, b + 1 < gcG 1 → xuG b ≤ xuG (b + 1) := by
  intro b
  induction b using WellFoundedLT.induction with
  | ind b IH =>
  intro hb1
  rcases lt_or_ge b (Wj.wjT 0) with hbt | hbt
  · have hb1t : b + 1 < Wj.wjT 0 := (ev_isSuccLimit_of_inE xu_t0_E).add_one_lt hbt
    rw [xuG_low hbt, xuG_low hb1t]; exact wtD.g_le_succ b
  have hbB : b < gcG 1 := (lt_add_one b).trans hb1
  have hbE := xu_gfE_le hbt
  obtain ⟨hk, hd0, hdE, -, -, -, hrb, -⟩ := gl_parts hbE
  obtain ⟨e, hr1, hv⟩ := gl_succ_nf hbE
  have hr1B : b % guE b ^ log (guE b) b + 1 < gcG 1 := lt_of_le_of_lt (by rw [e]; exact le_add_self) hb1
  rw [xuG_dec hbt hbB, e, xuG_cnf (guE_E b) (xu_E_ge hbt) hk hd0 hdE hr1 hv (e ▸ hb1)]
  exact max_le_max le_rfl (max_le_max le_rfl (IH _ hrb hr1B))

end Googology.Trans.PoR.InaccPsi.R2.Xu
