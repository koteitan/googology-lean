import Googology.Trans.PoR.InaccPsi.R2.QcLv

/-!
# QcCl: THE READING OF A FIXED POINT OF `Γ` FROM `X` ON IS A CLOSED POINT

`ϑˣ(Ω₁·N + K)` with a level `N ≥ Ω₁ + 1` (`N < ε_{Ω₁+1}`, data in `Tˣ`) and `K ∈ Tˣ ∩ Ω₁` is closed under
`σ ↦ gq σ x = ϑˣ(Ω₁·Ω₁ + σ)` ([W07a] Lemma 3.30 through `Rj.rjVt_lt`: `Ω₁·Ω₁ + σ < Ω₁·N + K` and `σ` below the
point).  A fixed point `H_λ(y)` of `Γ` in `[X, B₂)` reads `ϑˣ(Ω₁·(Ω₁ + λ(x)) + K(x))` (`Qc.vQ_fix`) with
`λ(x) ≥ 1`, `Ω₁ + λ(x) < ε_{Ω₁+1}` and its data in `Tˣ` (`Qc.qcLv_main`): a closed point.

* `qc_T_cut` (`Tˣ ∩ Ω₁` is an initial segment `[0, m)`), `qc_vt_closed` (**`ϑˣ(Ω₁·N + K)` is closed**);
* `qcA_fix` (the base reading of a fixed point), `qc_fix_lev` (**the level and index readings of a fixed point**),
  `qc_fix_cl` (**the reading of a fixed point of `Γ` from `X` on is closed**).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Rj Googology.Trans.PoR.InaccPsi.R2.Si
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Yw Googology.Trans.PoR.InaccPsi.R2.Yh
  Googology.Trans.PoR.InaccPsi.R2.Va Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Lu
  Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Yr

section Cl

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

/-- `Tˣ ∩ Ω₁` is an initial segment `[0, m)`. -/
theorem qc_T_cut : ∃ m, m ≤ Om1 ∧ ∀ a, a < Om1 → (a ∈ Tset x ↔ a < m) := by
  obtain ⟨m, -, -, -, hT, hm⟩ := T_next (Or.inr hx) hx1
  exact ⟨m, hm.le, hT⟩

/-- **`ϑˣ(Ω₁·N + K)` is closed** for a level `Ω₁ + 1 ≤ N < ε_{Ω₁+1}` with data in `Tˣ` and `K ∈ Tˣ ∩ Ω₁`. -/
theorem qc_vt_closed {N K : Ordinal.{0}} (hN1 : Om1 + 1 ≤ N) (hNE : N < ggE) (hNT : rjDat N ∈ Tset x)
    (hK : K ∈ Tset x) (hK1 : K < Om1) : YwClosed x (vt x (Om1 * N + K)) := by
  intro σ hσT hσ
  have hO1 : Om1 ≤ N := le_self_add.trans hN1
  have hargT := rjArg_mem hx hx1 hO1 hNE hNT hK hK1
  obtain ⟨-, hxv, hv1, -, -⟩ := vt_memTwo hx hx1 hargT (qc_arg_lt hNE hK1)
  have hσ1 : σ < Om1 := hσ.trans hv1
  have hO1E : Om1 < ggE := by rw [rj_Om1]; exact ggE_spec.2
  have harg : Om1 * Om1 + σ < Om1 * N + K := by
    calc Om1 * Om1 + σ < Om1 * Om1 + Om1 := (add_lt_add_iff_left _).2 hσ1
      _ = Om1 * (Om1 + 1) := (mul_add_one _ _).symm
      _ ≤ Om1 * N := mul_le_mul_right hN1 _
      _ ≤ Om1 * N + K := le_self_add
  exact rjVt_lt hx hx1 hO1E (by rw [rjDat_Om1]; exact mem_T_of_le hx hx1 zero_le) hσT hσ1 hO1 hNE hNT hK hK1 harg
    (by rw [rjDat_Om1]; exact hx.pos.trans_le hxv) hσ

end Cl

/-- **The base reading of a fixed point `H_λ(y)` of `Γ` in `[X, B₂)`.** -/
theorem qcA_fix {e : Ordinal.{0}} (hA : YhAt e) (hi : ¬ yhJ e < e) (hX : tlX ≤ e) (hB : e < ucB) (x : Ordinal.{0}) :
    qcA e x = vt x (Om1 * (Om1 + qcLvx e (ucLev e) x) + qcK (ucLev e) (ucI (ucLev e) e) x) := by
  have hE : InE e := Low.opow_eq_self_of_SC hA.1
  rw [← vQ_base hE hX hB, vQ_fix hA hi (qc_fix_data hA hi hX hB).2.2.2.1 hX hB]

section Fix

variable {e x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hA : YhAt e) (hi : ¬ yhJ e < e) (hX : tlX ≤ e)
  (hB : e < ucB) (hgx : max ω (qcQE e) < x)
  (hcode : ∀ c, c < e → qcG c < x → vQ c x ∈ Tset x ∧ vQ c x < Om1)
  (hmono : ∀ b c, b < c → c < e → qcG b < x → qcG c < x → vQ b x < vQ c x)
include hx hx1 hA hi hX hB hgx hcode hmono

/-- **The level and index readings of a fixed point `H_λ(y)` of `Γ` in `[X, B₂)`**: `1 ≤ λ(x)`,
`Ω₁ + λ(x) < ε_{Ω₁+1}` with data in `Tˣ`, `K(x) ∈ Tˣ ∩ Ω₁`. -/
theorem qc_fix_lev :
    1 ≤ qcLvx e (ucLev e) x ∧ Om1 + qcLvx e (ucLev e) x < ggE ∧ rjDat (Om1 + qcLvx e (ucLev e) x) ∈ Tset x ∧
      qcK (ucLev e) (ucI (ucLev e) e) x ∈ Tset x ∧ qcK (ucLev e) (ucI (ucLev e) e) x < Om1 := by
  obtain ⟨hl0, hlE, hlc, hyc, -, hne⟩ := qc_fix_data hA hi hX hB
  have hωx : ω < x := omega0_lt_inE hx
  have hQ := qcQE_fix hX hB hA hi hyc
  have hgQ : qcQE e < x := (le_max_right _ _).trans_lt hgx
  -- the components of the level have their gates below `x`
  have hcomp : ∀ d ∈ ucComps (ucLev e), d < e ∧ qcG d < x := fun d hd => by
    have hde : d < e := (le_ucC hd).trans_lt hlc
    refine ⟨hde, qcG_of_Q hωx ?_⟩
    have h1 : (if d < e then qcQ d else 0) ≤ ucFold (fun d => if d < e then qcQ d else 0) (ucLev e) :=
      ucFold_le_of_mem _ _ d hd
    rw [if_pos hde] at h1
    exact h1.trans_lt ((le_max_left _ _).trans_lt (hQ ▸ hgQ))
  set f : Ordinal.{0} → Ordinal.{0} := fun d => if d < e then vQ d x else 0 with hfdef
  have hE0 : (0 : Ordinal.{0}) < e := (show InE e from Low.opow_eq_self_of_SC hA.1).pos
  have hf0 : f 0 = 0 := by simp only [hfdef, if_pos hE0, vQ_zero]
  have hD0 : (fun d => d < e ∧ qcG d < x) 0 := ⟨hE0, by rw [qcG_zero]; exact hx.pos⟩
  have hfΩ : ∀ d, (fun d => d < e ∧ qcG d < x) d → f d < Om1 := fun d hd => by
    simp only [hfdef, if_pos hd.1]; exact (hcode d hd.1 hd.2).2
  have hfm : ∀ d d', (fun d => d < e ∧ qcG d < x) d → (fun d => d < e ∧ qcG d < x) d' → d < d' → f d < f d' :=
    fun d d' hd hd' hdd => by
      simp only [hfdef, if_pos hd.1, if_pos hd'.1]; exact hmono d d' hdd hd'.1 hd.2 hd'.2
  obtain ⟨hLE, hLdat, -, hLord⟩ := qcLv_main f (fun d => d < e ∧ qcG d < x) hf0 hD0 hfΩ hfm _ hlE hcomp
  have hlx : qcLvx e (ucLev e) x = qcLv f (ucLev e) := rfl
  have h0c : ∀ d ∈ ucComps 0, d < e ∧ qcG d < x := fun d hd => by
    rw [ucComps_small uc_SC_Om2.1, mem_singleton_iff] at hd; rw [hd]; exact hD0
  have hL1 : 1 ≤ qcLv f (ucLev e) := by
    have := hLord 0 (pos_iff_ne_zero.2 hl0) h0c
    rw [qcLv_small f uc_SC_Om2.1, hf0] at this; exact one_le_iff_ne_zero.2 this.ne'
  have hgE : InE ggE := ggE_spec.1
  have hOE : Om1 < ggE := by rw [rj_Om1]; exact ggE_spec.2
  obtain ⟨m, hmO, hT⟩ := qc_T_cut hx hx1
  -- the data of the level
  have hdatT : rjDat (Om1 + qcLv f (ucLev e)) ∈ Tset x := by
    have hfold : ucFold f (ucLev e) < m := by
      have hm0 : 0 < m := (hT 0 (hx.pos.trans hx1)).1 (mem_T_of_le hx hx1 zero_le)
      refine (ucFold_lt_iff f hm0 _).2 fun d hd => ?_
      obtain ⟨hde, hgd⟩ := hcomp d hd
      have := hcode d hde hgd
      simp only [hfdef, if_pos hde]
      exact (hT _ this.2).1 this.1
    have hle : rjDat (Om1 + qcLv f (ucLev e)) ≤ ucFold f (ucLev e) := by
      rcases lt_or_ge (qcLv f (ucLev e)) Om1 with hs | hs
      · rw [rjDat_Om1_add (one_le_iff_ne_zero.1 hL1) hs]; have h := hLdat; rwa [rjDat_small hs] at h
      · rw [si_rjDat_Om1_add hs hLE]; exact hLdat
    have hlt := hle.trans_lt hfold
    exact (hT _ (hlt.trans_le hmO)).2 hlt
  -- the index reading
  have hKT : qcK (ucLev e) (ucI (ucLev e) e) x ∈ Tset x ∧ qcK (ucLev e) (ucI (ucLev e) e) x < Om1 := by
    have hKQ : qcKQ (ucLev e) (ucI (ucLev e) e) < x := (le_max_right _ _).trans_lt (hQ ▸ hgQ)
    unfold qcK
    unfold qcKQ at hKQ
    split_ifs with hF
    · rw [if_pos hF] at hKQ
      obtain ⟨-, -, hpy⟩ := qc_fpH_mem hne hF
      obtain ⟨hpT, hp1⟩ := hcode _ (hpy.trans hyc) (qcG_of_Q hωx ((le_max_left _ _).trans_lt hKQ))
      obtain ⟨hoT, ho1⟩ := hcode _ ((Ordinal.sub_le_self _ _).trans_lt hyc)
        (qcG_of_Q hωx ((le_max_right _ _).trans_lt hKQ))
      exact ⟨vzT_add hx hx1 hpT hoT, (inE_indec Gl.gl_Om1_E).add_lt hp1 ho1⟩
    · rw [if_neg hF] at hKQ
      exact hcode _ hyc (qcG_of_Q hωx hKQ)
  exact ⟨hL1, hgE.add_lt hOE hLE, hdatT, hKT.1, hKT.2⟩

/-- **The reading of a fixed point of `Γ` from `X` on is a closed point.** -/
theorem qc_fix_cl : YwClosed x (qcA e x) := by
  obtain ⟨hL1, hNE, hNT, hKT, hK1⟩ := qc_fix_lev hx hx1 hA hi hX hB hgx hcode hmono
  rw [qcA_fix hA hi hX hB x]
  exact qc_vt_closed hx hx1 (add_le_add le_rfl hL1) hNE hNT hKT hK1

end Fix

end Googology.Trans.PoR.InaccPsi.R2.Qc
