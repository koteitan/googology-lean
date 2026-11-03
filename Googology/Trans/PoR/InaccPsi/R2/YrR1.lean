import Googology.Trans.PoR.InaccPsi.R2.YrR
import Googology.Trans.PoR.InaccPsi.R2.YrGq
import Googology.Trans.PoR.InaccPsi.R2.YhR1

/-!
# YrR1: EVERY CODE BELOW `B_Γ` READS AN ADMISSIBLE OFFSET; gates of the parts, positivity

`Yh.yhR_pos0` bounds the readings of the codes below `Γ(N)` by the constant atom `Γ_{x+1+N}` (`N < ε₀`).  With read
atom indices there is no constant bound; instead every reading of a code `c < B_Γ` (gate below `x`) is an
admissible offset (`Yr.YrN`: in `Tˣ ∩ Ω₁`, no `Γ`-fixed limit below it), by one induction: an atom `Γ(i)` reads
`ϑˣ(Ω₁·Ω₁ + i(x))` with `i(x)` admissible (`Yr.yrN_gq`), a non-atom bracket reads `ϑˣ(Ω₁·α(x) + η(x))` below
`ϑˣ(Ω₁·Ω₁ + max(α(x), η(x)))` (`Xk.xkA_lt`), and the bracket form stays below the same atom.

* `yr_parts_Q`, `yr_parts_g`, `yr_E_parts` (non-atom), `yr_E_atom` (**the index of an atom bracket has its gate
  below `x`**), `yr_E_g`;
* `yrN_max`, `yr_lt_gqN`, `yrR_N0` (**ONE INDUCTION: `c(x)` admissible, and `0 < c(x)` for `c ≠ 0`**), `yrR_N`,
  `yrR_T`, `yrR_pos`;
* `yrA_facts` (**the bracket's `ε`-number `e ∈ [G, B_Γ)` reads an admissible `ε`-number above `x`**).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yr

open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2 Googology.Notation.InaccPsi
  Googology.Notation.InaccPsi.InaccSeq Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Gn
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Xu
  Googology.Trans.PoR.InaccPsi.R2.Xx Googology.Trans.PoR.InaccPsi.R2.Xk Googology.Trans.PoR.InaccPsi.R2.Yh

/-! ## Gates of the parts -/

theorem yr_parts_Q {x c : Ordinal.{0}} (h : gcG 0 ≤ c) (hg : yrG c < x) :
    yrQE (guE c) < x ∧ yrQ (log (guE c) c) < x ∧ yrQ (c / guE c ^ log (guE c) c) < x ∧
      yrG (c % guE c ^ log (guE c) c) < x := by
  rw [yrG_dec h] at hg
  exact ⟨(le_max_left _ _).trans_lt ((le_max_left _ _).trans_lt hg),
    (le_max_right _ _).trans_lt ((le_max_left _ _).trans_lt hg),
    (le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hg),
    (le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hg)⟩

theorem yr_parts_g {x c : Ordinal.{0}} (hωx : ω < x) (h : gcG 0 ≤ c) (hg : yrG c < x) :
    yrG (log (guE c) c) < x ∧ yrG (c / guE c ^ log (guE c) c) < x ∧ yrG (c % guE c ^ log (guE c) c) < x := by
  obtain ⟨-, q1, q2, g3⟩ := yr_parts_Q h hg
  exact ⟨yrG_of_Q hωx q1, yrG_of_Q hωx q2, g3⟩

theorem yr_E_parts {x e : Ordinal.{0}} (hωx : ω < x) (hA : ¬ YhAt e) (hg : yrQE e < x) :
    yrG (yhK e) < x ∧ yrG (yhI e) < x := by
  rw [yrQE_psi hA] at hg
  exact ⟨yrG_of_Q hωx ((le_max_left _ _).trans_lt hg), yrG_of_Q hωx ((le_max_right _ _).trans_lt hg)⟩

/-- **The index of an atom bracket `Γ(i)`, `i < Γ(i)`, has its gate below `x`.** -/
theorem yr_E_atom {x i : Ordinal.{0}} (hωx : ω < x) (hi : i < gcG i) (hg : yrG (gcG i) < x) : yrG i < x := by
  rw [yrG_atom hi] at hg; exact yrG_of_Q hωx hg

theorem yr_E_g {x c : Ordinal.{0}} (h : gcG 0 ≤ c) (hg : yrG c < x) : yrG (guE c) < x := by
  rw [yrG_base (guE_E c) (yh_G_le_E h)]; exact (yr_parts_Q h hg).1

/-- Below `B_Γ`, an atom bracket `e = Γ(i)` of a code has `i < Γ(i)` and `i < e`. -/
theorem yr_atom_idx {e i : Ordinal.{0}} (hi : e = gcG i) (heB : e < Tf.tfBG) : i < gcG i ∧ i < e := by
  have hiB : i < Tf.tfBG := ((gcG_strictMono.le_apply (x := i)).trans_eq hi.symm).trans_lt heB |>.trans_le' le_rfl
  exact ⟨yr_idx_BG hiB, hi ▸ yr_idx_BG hiB⟩

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

omit hx hx1 in
theorem yrN_max {a b : Ordinal.{0}} (ha : YrN x a) (hb : YrN x b) : YrN x (max a b) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h]; exact hb
  · rw [max_eq_left h]; exact ha

theorem yr_lt_gqN {W a : Ordinal.{0}} (hW : YrN x W) (ha : a ≤ W) : a < gq W x :=
  ha.trans_lt (Gm.gmq_gt hx hx1 hW.1 hW.2.1)

/-- **ONE INDUCTION: every code `c < B_Γ` with gate below `x` reads an admissible offset, positive for `c ≠ 0`.** -/
theorem yrR_N0 : ∀ c, c < Tf.tfBG → yrG c < x → YrN x (yrR c x) ∧ (c ≠ 0 → 0 < yrR c x) := by
  have hωx := omega0_lt_inE hx
  have hN0 : YrN x 0 := yrN_cst hx hx1 zero_le
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hg
  rcases lt_or_ge c (gcG 0) with hcG | hcG
  · rw [yrG_low hcG] at hg
    rw [yrR_low hcG]
    rcases eq_or_ne c 0 with h0 | h0
    · rw [h0, glR_zero]; exact ⟨hN0, fun h => absurd rfl h⟩
    obtain ⟨h1, h2⟩ := glR_pos0 hx hx1 c h0 hcG hg
    rw [Gm.mg_gq0 hx hx1] at h2
    exact ⟨yrN_lt_gq hx hx1 hN0 h2, fun _ => h1⟩
  obtain ⟨hj0, hd0, -, -, -, hkc, hrc, hdc⟩ := gl_parts (yh_gfE_le hcG)
  obtain ⟨g1, g2, g3⟩ := yr_parts_g hωx hcG hg
  have hEc : guE c ≤ c := gl_E_le (yh_gfE_le hcG)
  have hEB : guE c < Tf.tfBG := hEc.trans_lt hc
  -- the bracket's `ε`-number reads an admissible `ε`-number
  have hA : InE (yrA (guE c) x) ∧ YrN x (yrA (guE c) x) := by
    by_cases hAt : YhAt (guE c)
    · obtain ⟨i, hi⟩ := yhAt_iff.1 hAt
      obtain ⟨hii, hie⟩ := yr_atom_idx hi hEB
      have hi' : yhJ (guE c) < guE c := by rw [hi, yhJ_gcG]; exact hii
      rw [yrA_atom hAt hi', hi, yhJ_gcG]
      have hgi : yrG i < x := yr_E_atom hωx hii (by rw [← hi]; exact yr_E_g hcG hg)
      have hiN := (IH i (hie.trans_le hEc) (hie.trans hEB) hgi).1
      exact ⟨(yr_facts hx hx1 hiN).2.2.2.1, yrN_gq hx hx1 hiN⟩
    · rw [yrA_psi hAt]
      obtain ⟨hk1, hke, hie, -⟩ := yh_E_data hcG hAt
      obtain ⟨gk, gi⟩ := yr_E_parts hωx hAt (yr_parts_Q hcG hg).1
      have hlc : yhK (guE c) < c := hke.trans_le hEc
      have hα := IH _ hlc (hke.trans hEB) gk
      have hη := (IH _ (hie.trans_le hEc) (hie.trans hEB) gi).1
      have hαpos := hα.2 (lt_of_lt_of_le zero_lt_one hk1).ne'
      set W := max (yrR (yhK (guE c)) x) (yrR (yhI (guE c)) x) with hWdef
      have hWN : YrN x W := yrN_max hα.1 hη
      obtain ⟨hβT, hβ1⟩ := yr_T hα.1
      obtain ⟨htT, ht1⟩ := yr_T hη
      have hlt := xkA_lt hx hx1 hWN.1 hWN.2.1 (yr_lt_gqN hx hx1 hWN (le_max_left _ _))
        (yr_lt_gqN hx hx1 hWN (le_max_right _ _))
      exact ⟨(glA_facts hx hx1 (one_le_iff_pos.2 hαpos) hβT hβ1 htT ht1).2.2.2.1, yrN_lt_gq hx hx1 hWN hlt⟩
  obtain ⟨hAE, hAN⟩ := hA
  have hj := IH _ hkc (hkc.trans hc) g1
  have hd := IH _ hdc (hdc.trans hc) g2
  have hr := IH _ hrc (hrc.trans hc) g3
  set W := max (max (yrA (guE c) x) (yrR (log (guE c) c) x))
    (max (yrR (c / guE c ^ log (guE c) c) x) (yrR (c % guE c ^ log (guE c) c) x)) with hWdef
  have hWN : YrN x W := yrN_max (yrN_max hAN hj.1) (yrN_max hd.1 hr.1)
  obtain ⟨-, -, -, hGE, -⟩ := yr_facts hx hx1 hWN
  have hAW : yrA (guE c) x < gq W x := yr_lt_gqN hx hx1 hWN ((le_max_left _ _).trans (le_max_left _ _))
  have hjW : yrR (log (guE c) c) x < gq W x :=
    yr_lt_gqN hx hx1 hWN ((le_max_right _ _).trans (le_max_left _ _))
  have hdW : yrR (c / guE c ^ log (guE c) c) x < gq W x :=
    yr_lt_gqN hx hx1 hWN ((le_max_left _ _).trans (le_max_right _ _))
  have hrW : yrR (c % guE c ^ log (guE c) c) x < gq W x :=
    yr_lt_gqN hx hx1 hWN ((le_max_right _ _).trans (le_max_right _ _))
  rw [yrR_dec hcG]
  refine ⟨yrN_lt_gq hx hx1 hWN ?_, fun _ => lt_of_lt_of_le (mul_pos (opow_pos _ hAE.pos) (hd.2 hd0)) le_self_add⟩
  rw [gu_pow_eq hAE]
  exact (inE_indec hGE).add_lt (hGE.mul_lt (hGE.opow_lt (hGE.mul_lt hAW hjW)) hdW) hrW

theorem yrR_N {c : Ordinal.{0}} (hc : c < Tf.tfBG) (hg : yrG c < x) : YrN x (yrR c x) :=
  (yrR_N0 hx hx1 c hc hg).1

theorem yrR_T {c : Ordinal.{0}} (hc : c < Tf.tfBG) (hg : yrG c < x) : yrR c x ∈ Tset x ∧ yrR c x < Om1 :=
  yr_T (yrR_N hx hx1 hc hg)

theorem yrR_pos {c : Ordinal.{0}} (hc0 : c ≠ 0) (hc : c < Tf.tfBG) (hg : yrG c < x) : 0 < yrR c x :=
  (yrR_N0 hx hx1 c hc hg).2 hc0

/-- **The bracket's `ε`-number `e ∈ [G, B_Γ)` (gate below `x`) reads an admissible `ε`-number above `x`.** -/
theorem yrA_facts {e : Ordinal.{0}} (he : InE e) (hGe : gcG 0 ≤ e) (heB : e < Tf.tfBG) (hg : yrG e < x) :
    InE (yrA e x) ∧ x < yrA e x ∧ YrN x (yrA e x) ∧ yrA e x ∈ Tset x ∧ yrA e x < Om1 := by
  have hωx := omega0_lt_inE hx
  have hN := yrR_N hx hx1 heB hg
  rw [yrR_base he hGe] at hN
  obtain ⟨hT, h1⟩ := yr_T hN
  by_cases hAt : YhAt e
  · obtain ⟨i, rfl⟩ := yhAt_iff.1 hAt
    obtain ⟨hii, hie⟩ := yr_atom_idx rfl heB
    have hi' : yhJ (gcG i) < gcG i := by rw [yhJ_gcG]; exact hii
    rw [yrA_atom hAt hi', yhJ_gcG] at hN hT h1 ⊢
    have hiN := yrR_N hx hx1 (hie.trans heB) (yr_E_atom hωx hii hg)
    have hf := yr_facts hx hx1 hiN
    exact ⟨hf.2.2.2.1, hf.2.1, hN, hT, h1⟩
  · rw [yrA_psi hAt] at hN hT h1 ⊢
    have hGe' : gcG 0 < e := lt_of_le_of_ne hGe (fun h => hAt (h ▸ yhAt_gcG 0))
    obtain ⟨hk1, hke, hie, -⟩ := yhData_spec he hGe' hAt
    have hge : yrQE e < x := by rw [← yrG_base he hGe]; exact hg
    obtain ⟨gk, gi⟩ := yr_E_parts hωx hAt hge
    have hαpos := yrR_pos hx hx1 (lt_of_lt_of_le zero_lt_one hk1).ne' (hke.trans heB) gk
    obtain ⟨hβT, hβ1⟩ := yrR_T hx hx1 (hke.trans heB) gk
    obtain ⟨htT, ht1⟩ := yrR_T hx hx1 (hie.trans heB) gi
    obtain ⟨-, a2, -, a4, -, -⟩ := glA_facts hx hx1 (one_le_iff_pos.2 hαpos) hβT hβ1 htT ht1
    exact ⟨a4, a2, hN, hT, h1⟩

end Base

end Googology.Trans.PoR.InaccPsi.R2.Yr
