import Googology.Trans.PoR.InaccPsi.R2.YcDirect
import Googology.Trans.PoR.InaccPsi.R2.YhR

/-!
# YhR1: EVERY CODE BELOW `Γ(N)` READS BELOW `Γ_{x+1+N}` (`N < ε₀`), gates of the parts, positivity

* `yh_parts_Q`, `yh_parts_g`, `yh_E_g` (**the parts of a code above `G` have their gates below every `x > ω` above the
  gate of the code**, the level and the index of a non-atom bracket included);
* `yhR_pos0` (**one induction: `0 < c(x) < Γ_{x+1+N}` for every code `0 < c < Γ(N)`, `N < ε₀`**, at every
  `ε`-number base `x < Ω₁` above the gate), `yhR_lt`, `yhR_T`, `yhR_pos`;
* `yhA_facts` (**the bracket's `ε`-number `e ∈ [G, Γ(N))` reads an `ε`-number `> x` below `Γ_{x+1+N}`**).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yh

open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2 Googology.Notation.InaccPsi
  Googology.Notation.InaccPsi.InaccSeq Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Gn
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Xu
  Googology.Trans.PoR.InaccPsi.R2.Xx Googology.Trans.PoR.InaccPsi.R2.Xk

/-! ## Gates of the parts -/

theorem yh_parts_Q {x c : Ordinal.{0}} (h : gcG 0 ≤ c) (hg : yhG c < x) :
    yhQE (guE c) < x ∧ yhQ (log (guE c) c) < x ∧ yhQ (c / guE c ^ log (guE c) c) < x ∧
      yhG (c % guE c ^ log (guE c) c) < x := by
  rw [yhG_dec h] at hg
  exact ⟨(le_max_left _ _).trans_lt ((le_max_left _ _).trans_lt hg),
    (le_max_right _ _).trans_lt ((le_max_left _ _).trans_lt hg),
    (le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hg),
    (le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hg)⟩

/-- **The parts have their gates below `x`** (`x > ω`) when the code has. -/
theorem yh_parts_g {x c : Ordinal.{0}} (hωx : ω < x) (h : gcG 0 ≤ c) (hg : yhG c < x) :
    yhG (log (guE c) c) < x ∧ yhG (c / guE c ^ log (guE c) c) < x ∧ yhG (c % guE c ^ log (guE c) c) < x := by
  obtain ⟨-, q1, q2, g3⟩ := yh_parts_Q h hg
  exact ⟨yhG_of_Q hωx q1, yhG_of_Q hωx q2, g3⟩

/-- **The level and the index of a non-atom bracket** have their gates below `x`. -/
theorem yh_E_parts {x e : Ordinal.{0}} (hωx : ω < x) (hA : ¬ YhAt e) (hg : yhQE e < x) :
    yhG (yhK e) < x ∧ yhG (yhI e) < x := by
  rw [yhQE_psi hA] at hg
  exact ⟨yhG_of_Q hωx ((le_max_left _ _).trans_lt hg), yhG_of_Q hωx ((le_max_right _ _).trans_lt hg)⟩

/-- The bracket's `ε`-number has its gate below `x`. -/
theorem yh_E_g {x c : Ordinal.{0}} (h : gcG 0 ≤ c) (hg : yhG c < x) : yhG (guE c) < x := by
  rw [yhG_base (guE_E c) (yh_G_le_E h)]; exact (yh_parts_Q h hg).1

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem yh_gqN {N : Ordinal.{0}} (hN : N < ε₀) :
    gq N x ∈ Tset x ∧ x < gq N x ∧ gq N x < Om1 ∧ InE (gq N x) ∧ N < gq N x ∧ N ∈ Tset x ∧ N < Om1 := by
  obtain ⟨h1, h2, h3, h4⟩ := xx_facts hx hx1 hN
  obtain ⟨hT, hN1, hNx⟩ := xxW_T hx hx1 hN
  exact ⟨h1, h2, h3, h4, hNx.trans h2, hT, hN1⟩

/-- **The base atom `Γ(i)`, `i < N < ε₀`, reads an `ε`-number below `Γ_{x+1+N}`.** -/
theorem yh_gq_lt {i N : Ordinal.{0}} (hN : N < ε₀) (hi : i < N) : InE (gq i x) ∧ gq i x < gq N x := by
  obtain ⟨-, -, -, hE, hNq, -, -⟩ := yh_gqN hx hx1 hN
  exact ⟨(xx_facts hx hx1 (hi.trans hN)).2.2.2, xx_lt hx hx1 hN hNq hi⟩

theorem yh_gq0_le {N : Ordinal.{0}} (hN : N < ε₀) : gq 0 x ≤ gq N x :=
  xx_mono hx hx1 hN (yh_gqN hx hx1 hN).2.2.2.2.1 zero_le

/-- **ONE INDUCTION: `0 < c(x) < Γ_{x+1+N}`** for every code `0 < c < Γ(N)` with gate below `x` (`N < ε₀`). -/
theorem yhR_pos0 {N : Ordinal.{0}} (hN : N < ε₀) :
    ∀ c, c ≠ 0 → c < gcG N → yhG c < x → 0 < yhR c x ∧ yhR c x < gq N x := by
  have hωx := omega0_lt_inE hx
  obtain ⟨-, -, -, hGE, hNq, hNT, hN1⟩ := yh_gqN hx hx1 hN
  have hq0 : 0 < gq N x := hGE.pos
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc0 hc hg
  rcases lt_or_ge c (gcG 0) with hcG | hcG
  · rw [yhG_low hcG] at hg
    rw [yhR_low hcG]
    obtain ⟨h1, h2⟩ := glR_pos0 hx hx1 c hc0 hcG hg
    exact ⟨h1, (h2.trans_le (Gm.mg_gq0 hx hx1).le).trans_le (yh_gq0_le hx hx1 hN)⟩
  obtain ⟨hj0, hd0, -, -, -, hkc, hrc, hdc⟩ := gl_parts (yh_gfE_le hcG)
  obtain ⟨g1, g2, g3⟩ := yh_parts_g hωx hcG hg
  have hEc : guE c ≤ c := gl_E_le (yh_gfE_le hcG)
  -- the bracket's `ε`-number reads an `ε`-number below `Γ_{x+1+N}`
  have hA : InE (yhA (guE c) x) ∧ yhA (guE c) x < gq N x := by
    by_cases hAt : YhAt (guE c)
    · obtain ⟨i, hi⟩ := yhAt_iff.1 hAt
      rw [yhA_atom hAt, hi, yhJ_gcG]
      have hiN : i < N := gcG_strictMono.lt_iff_lt.1 (hi ▸ hEc.trans_lt hc)
      exact yh_gq_lt hx hx1 hN hiN
    · rw [yhA_psi hAt]
      obtain ⟨hk1, hke, hie, -⟩ := yh_E_data hcG hAt
      obtain ⟨gk, gi⟩ := yh_E_parts hωx hAt (yh_parts_Q hcG hg).1
      have hlc : yhK (guE c) < c := hke.trans_le hEc
      have hα := IH _ hlc (lt_of_lt_of_le zero_lt_one hk1).ne' (hlc.trans hc) gk
      have hηG : yhR (yhI (guE c)) x < gq N x := by
        rcases eq_or_ne (yhI (guE c)) 0 with h0 | h0
        · rw [h0, yhR_zero]; exact hq0
        · exact (IH _ (hie.trans_le hEc) h0 ((hie.trans_le hEc).trans hc) gi).2
      obtain ⟨hβT, hβ1⟩ := xx_T hx hx1 hN hα.2
      obtain ⟨htT, ht1⟩ := xx_T hx hx1 hN hηG
      exact ⟨(glA_facts hx hx1 (one_le_iff_pos.2 hα.1) hβT hβ1 htT ht1).2.2.2.1,
        xkA_lt hx hx1 hNT hN1 hα.2 hηG⟩
  obtain ⟨hAE, hAG⟩ := hA
  have hj := IH _ hkc hj0 (hkc.trans hc) g1
  have hd := IH _ hdc hd0 (hdc.trans hc) g2
  have hr : yhR (c % guE c ^ log (guE c) c) x < gq N x := by
    rcases eq_or_ne (c % guE c ^ log (guE c) c) 0 with h0 | h0
    · rw [h0, yhR_zero]; exact hq0
    · exact (IH _ hrc h0 (hrc.trans hc) g3).2
  rw [yhR_dec hcG]
  refine ⟨lt_of_lt_of_le (mul_pos (opow_pos _ hAE.pos) hd.1) le_self_add, ?_⟩
  rw [gu_pow_eq hAE]
  exact (inE_indec hGE).add_lt (hGE.mul_lt (hGE.opow_lt (hGE.mul_lt hAG hj.2)) hd.2) hr

/-- **Every reading of a code below `Γ(N)` lies below `Γ_{x+1+N}`.** -/
theorem yhR_lt {N c : Ordinal.{0}} (hN : N < ε₀) (hc : c < gcG N) (hg : yhG c < x) : yhR c x < gq N x := by
  rcases eq_or_ne c 0 with h0 | h0
  · rw [h0, yhR_zero]; exact (yh_gqN hx hx1 hN).2.2.2.1.pos
  · exact (yhR_pos0 hx hx1 hN c h0 hc hg).2

theorem yhR_T {N c : Ordinal.{0}} (hN : N < ε₀) (hc : c < gcG N) (hg : yhG c < x) :
    yhR c x ∈ Tset x ∧ yhR c x < Om1 :=
  xx_T hx hx1 hN (yhR_lt hx hx1 hN hc hg)

theorem yhR_pos {N c : Ordinal.{0}} (hN : N < ε₀) (hc0 : c ≠ 0) (hc : c < gcG N) (hg : yhG c < x) :
    0 < yhR c x :=
  (yhR_pos0 hx hx1 hN c hc0 hc hg).1

/-- **The bracket's `ε`-number `e ∈ [G, Γ(N))` (gate below `x`) reads an `ε`-number above `x` below `Γ_{x+1+N}`.** -/
theorem yhA_facts {N e : Ordinal.{0}} (hN : N < ε₀) (he : InE e) (hGe : gcG 0 ≤ e) (heN : e < gcG N)
    (hg : yhG e < x) : InE (yhA e x) ∧ x < yhA e x ∧ yhA e x < gq N x ∧ yhA e x ∈ Tset x ∧ yhA e x < Om1 := by
  have hωx := omega0_lt_inE hx
  have hlt := yhR_lt hx hx1 hN heN hg
  rw [yhR_base he hGe] at hlt
  obtain ⟨hT, h1⟩ := xx_T hx hx1 hN hlt
  by_cases hAt : YhAt e
  · obtain ⟨i, rfl⟩ := yhAt_iff.1 hAt
    rw [yhA_atom hAt, yhJ_gcG] at hlt hT h1 ⊢
    have hiN : i < N := gcG_strictMono.lt_iff_lt.1 heN
    have hi := xx_facts hx hx1 (hiN.trans hN)
    exact ⟨hi.2.2.2, hi.2.1, hlt, hT, h1⟩
  · rw [yhA_psi hAt] at hlt hT h1 ⊢
    have hGe' : gcG 0 < e := lt_of_le_of_ne hGe (fun h => hAt (h ▸ yhAt_gcG 0))
    obtain ⟨hk1, hke, hie, -⟩ := yhData_spec he hGe' hAt
    have hge : yhQE e < x := by rw [← yhG_base he hGe]; exact hg
    obtain ⟨gk, gi⟩ := yh_E_parts hωx hAt hge
    have hα := yhR_pos0 hx hx1 hN _ (lt_of_lt_of_le zero_lt_one hk1).ne' (hke.trans heN) gk
    obtain ⟨hβT, hβ1⟩ := xx_T hx hx1 hN hα.2
    obtain ⟨htT, ht1⟩ := yhR_T hx hx1 hN (hie.trans heN) gi
    obtain ⟨-, a2, -, a4, -, -⟩ := glA_facts hx hx1 (one_le_iff_pos.2 hα.1) hβT hβ1 htT ht1
    exact ⟨a4, a2, hlt, hT, h1⟩

end Base

end Googology.Trans.PoR.InaccPsi.R2.Yh
