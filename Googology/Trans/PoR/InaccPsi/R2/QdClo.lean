import Googology.Trans.PoR.InaccPsi.R2.QdGate
import Googology.Trans.PoR.InaccPsi.R2.QcCl

/-!
# QdClo: THE READING OF A FIXED POINT OF `Γ` FROM `B₂` ON IS A CLOSED POINT

As `Qc.QcCl` with the Veblen levels.  `ϑˣ(Ω₁·N + K)` with a Veblen level `Ω₁ + 1 ≤ N < Γ_{Ω₁+1}` (data in `Tˣ`) and
`K ∈ Tˣ ∩ Ω₁` is closed under `σ ↦ gq σ x = ϑˣ(Ω₁·Ω₁ + σ)` ([W07a] Lemma 3.30 through `R2.tfVt_lt`).  A fixed point
`Hᵛ_λ(y)` of `Γ` in `[B₂, B₃)` reads `ϑˣ(Ω₁·(Ω₁ + λ(x)) + K(x))` (`Qd.vD_fix`) with `λ(x) ≥ 1`, `Ω₁ + λ(x) <
Γ_{Ω₁+1}` and its data in `Tˣ` (`Qd.qdLv_main`): a closed point.

* `qd_ssDat_Om1_add` (**`ssDat(Ω₁ + L) = ssDat L`** for `1 ≤ L < Γ_{Ω₁+1}`), `qd_vt_closed` (**`ϑˣ(Ω₁·N + K)` is
  closed**);
* `qdA_fix` (the base reading of a fixed point), `qd_fix_lev` (**the level and index readings of a fixed point**),
  `qd_fix_cl` (**the reading of a fixed point of `Γ` from `B₂` on is closed**).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rj Googology.Trans.PoR.InaccPsi.R2.Yh
  Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Yw Googology.Trans.PoR.InaccPsi.R2.Gk
  Googology.Trans.PoR.InaccPsi.R2.Qc

/-- **`ssDat(Ω₁ + L) = ssDat L`** for `1 ≤ L < Γ_{Ω₁+1}`. -/
theorem qd_ssDat_Om1_add {L : Ordinal.{0}} (hL1 : 1 ≤ L) (hLG : L < ggGam) : Ss.ssDat (Om1 + L) = Ss.ssDat L := by
  have hgE : InE ggE := ggE_spec.1
  have hOE : Om1 < ggE := by rw [rj_Om1]; exact ggE_spec.2
  rcases lt_or_ge L ggE with hE | hE
  · have hOLE : Om1 + L < ggE := hgE.add_lt hOE hE
    rw [Ss.ssDat_eq_rj _ hOLE, Ss.ssDat_eq_rj _ hE]
    rcases lt_or_ge L Om1 with hs | hs
    · rw [rjDat_Om1_add (one_le_iff_ne_zero.1 hL1) hs, rjDat_small hs]
    · exact Si.si_rjDat_Om1_add hs hE
  · have e : Om1 + L = L := Ordinal.add_of_omega0_opow_le (by rw [hgE]; exact hOE) (by rw [hgE]; exact hE)
    rw [e]

section Cl

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

/-- **`ϑˣ(Ω₁·N + K)` is closed** for a Veblen level `Ω₁ + 1 ≤ N < Γ_{Ω₁+1}` with data in `Tˣ` and `K ∈ Tˣ ∩ Ω₁`. -/
theorem qd_vt_closed {N K : Ordinal.{0}} (hN1 : Om1 + 1 ≤ N) (hNG : N < ggGam) (hNT : Tf.tfDat N ∈ Tset x)
    (hK : K ∈ Tset x) (hK1 : K < Om1) : YwClosed x (vt x (Om1 * N + K)) := by
  intro σ hσT hσ
  have hO1 : Om1 ≤ N := le_self_add.trans hN1
  have hNB : N < Tf.tfBG := hNG.trans Tf.tf_gg_lt_BG
  have hargT := tfArg_mem hx hx1 hO1 hNB hNT hK hK1
  obtain ⟨-, hxv, hv1, -, -⟩ := vt_memTwo hx hx1 hargT (qd_arg_lt hNG hK1)
  have hσ1 : σ < Om1 := hσ.trans hv1
  have harg : Om1 * Om1 + σ < Om1 * N + K := by
    calc Om1 * Om1 + σ < Om1 * Om1 + Om1 := (add_lt_add_iff_left _).2 hσ1
      _ = Om1 * (Om1 + 1) := (mul_add_one _ _).symm
      _ ≤ Om1 * N := mul_le_mul_right hN1 _
      _ ≤ Om1 * N + K := le_self_add
  exact tfVt_lt hx hx1 hO1 hNB hO1
    (by rw [Tf.tfDat_Om1]; exact mem_T_of_le hx hx1 zero_le) hσT hσ1 hNT hK hK1 harg
    (by rw [Tf.tfDat_Om1]; exact hx.pos.trans_le hxv) hσ

end Cl

variable (S : InaccSeq.{0})
include S

/-- **The base reading of a fixed point `Hᵛ_λ(y)` of `Γ` in `[B₂, B₃)`.** -/
theorem qdA_fix {e : Ordinal.{0}} (hA : YhAt e) (hi : ¬ yhJ e < e) (hX : ucB ≤ e) (hB : e < qdB)
    (x : Ordinal.{0}) :
    qdA e x = vt x (Om1 * (Om1 + qdLvx e (qdLev e) x) + qdRK (qdLev e) (qdI (qdLev e) e) x) := by
  have hE : InE e := Low.opow_eq_self_of_SC hA.1
  rw [← vD_base hE hX hB, vD_fix hA hi (qd_fix_data S hA hi hX hB).2.2.2.1 hX hB]

section Fix

variable {e x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hA : YhAt e) (hi : ¬ yhJ e < e) (hX : ucB ≤ e)
  (hB : e < qdB) (hgx : max ω (qdQEt e) < x)
  (hcode : ∀ c, c < e → qdGt c < x → vD c x ∈ Tset x ∧ vD c x < Om1)
  (hmono : ∀ b c, b < c → c < e → qdGt b < x → qdGt c < x → vD b x < vD c x)
include hx hx1 hA hi hX hB hgx hcode hmono

/-- **The level and index readings of a fixed point `Hᵛ_λ(y)` of `Γ` in `[B₂, B₃)`**: `1 ≤ λ(x)`,
`Ω₁ + λ(x) < Γ_{Ω₁+1}` with data in `Tˣ`, `K(x) ∈ Tˣ ∩ Ω₁`. -/
theorem qd_fix_lev :
    1 ≤ qdLvx e (qdLev e) x ∧ Om1 + qdLvx e (qdLev e) x < ggGam ∧ Tf.tfDat (Om1 + qdLvx e (qdLev e) x) ∈ Tset x ∧
      qdRK (qdLev e) (qdI (qdLev e) e) x ∈ Tset x ∧ qdRK (qdLev e) (qdI (qdLev e) e) x < Om1 := by
  obtain ⟨hl0, hlG, hlc, hyc, -, hne⟩ := qd_fix_data S hA hi hX hB
  have hωx : ω < x := omega0_lt_inE hx
  have hQ := qdQEt_fix hX hB hA hi hyc
  have hgQ : qdQEt e < x := (le_max_right _ _).trans_lt hgx
  have he0 : (0 : Ordinal.{0}) < e := (show InE e from Low.opow_eq_self_of_SC hA.1).pos
  -- the leaves of the level have their gates below `x`
  have hcomp : ∀ d ∈ qdComps (qdLev e), d < e ∧ qdGt d < x := fun d hd => by
    have hde : d < e := (qdFold_lt_iff he0 _).1 hlc d hd
    refine ⟨hde, qdGt_of_Q hωx ?_⟩
    have h1 := (qdFold_lt_iff' (fun d => if d < e then qdQt d else 0) hx.pos (qdLev e)).1
      ((le_max_left _ _).trans_lt (hQ ▸ hgQ)) d hd
    simp only [if_pos hde] at h1
    exact h1
  set f : Ordinal.{0} → Ordinal.{0} := fun d => if d < e then vD d x else 0 with hfdef
  have hf0 : f 0 = 0 := by simp only [hfdef, if_pos he0, vD_zero]
  have hD0 : (fun d => d < e ∧ qdGt d < x) 0 := ⟨he0, by rw [qdGt_zero]; exact hx.pos⟩
  have hfΩ : ∀ d, (fun d => d < e ∧ qdGt d < x) d → f d < Om1 := fun d hd => by
    simp only [hfdef, if_pos hd.1]; exact (hcode d hd.1 hd.2).2
  have hfm : ∀ d d', (fun d => d < e ∧ qdGt d < x) d → (fun d => d < e ∧ qdGt d < x) d' → d < d' →
      f d < f d' := fun d d' hd hd' hdd => by
    simp only [hfdef, if_pos hd.1, if_pos hd'.1]; exact hmono d d' hdd hd'.1 hd.2 hd'.2
  obtain ⟨hLG, hLdat, -, -, -, hLord⟩ :=
    qdLv_main f (fun d => d < e ∧ qdGt d < x) hf0 hD0 hfΩ hfm _ hlG hcomp
  have hlx : qdLvx e (qdLev e) x = qdLv f (qdLev e) := rfl
  have h0c : ∀ d ∈ qdComps 0, d < e ∧ qdGt d < x := fun d hd => by
    rw [qdComps_small qd_Om2_pos, mem_singleton_iff] at hd; rw [hd]; exact hD0
  have hL1 : 1 ≤ qdLv f (qdLev e) := by
    have := hLord 0 (pos_iff_ne_zero.2 hl0) h0c
    rw [qdLv_small f qd_Om2_pos, hf0] at this; exact one_le_iff_ne_zero.2 this.ne'
  obtain ⟨m, hmO, hT⟩ := qc_T_cut hx hx1
  -- the data of the level
  have hdatT : Tf.tfDat (Om1 + qdLv f (qdLev e)) ∈ Tset x := by
    have hm0 : 0 < m := (hT 0 (hx.pos.trans hx1)).1 (mem_T_of_le hx hx1 zero_le)
    have hfold : qdFold f (qdLev e) < m := by
      refine (qdFold_lt_iff' f hm0 _).2 fun d hd => ?_
      obtain ⟨hde, hgd⟩ := hcomp d hd
      have := hcode d hde hgd
      simp only [hfdef, if_pos hde]
      exact (hT _ this.2).1 this.1
    have hOLG : Om1 + qdLv f (qdLev e) < ggGam := Tf.tf_Om1_add_lt_gg hLG
    rw [Tf.tfDat_eq_ss _ hOLG, qd_ssDat_Om1_add hL1 hLG]
    have hlt := hLdat.trans_lt hfold
    exact (hT _ (hlt.trans_le hmO)).2 hlt
  -- the index reading
  have hKT : qdRK (qdLev e) (qdI (qdLev e) e) x ∈ Tset x ∧ qdRK (qdLev e) (qdI (qdLev e) e) x < Om1 := by
    have hKQ : qdKQ (qdLev e) (qdI (qdLev e) e) < x := (le_max_right _ _).trans_lt (hQ ▸ hgQ)
    unfold qdRK
    unfold qdKQ at hKQ
    split_ifs with hF
    · rw [if_pos hF] at hKQ
      obtain ⟨-, -, hpy⟩ := qd_fpH_mem hne hF
      obtain ⟨hpT, hp1⟩ := hcode _ (hpy.trans hyc) (qdGt_of_Q hωx ((le_max_left _ _).trans_lt hKQ))
      obtain ⟨hoT, ho1⟩ := hcode _ ((Ordinal.sub_le_self _ _).trans_lt hyc)
        (qdGt_of_Q hωx ((le_max_right _ _).trans_lt hKQ))
      exact ⟨vzT_add hx hx1 hpT hoT, (inE_indec Gl.gl_Om1_E).add_lt hp1 ho1⟩
    · rw [if_neg hF] at hKQ
      exact hcode _ hyc (qdGt_of_Q hωx hKQ)
  exact ⟨hL1, Tf.tf_Om1_add_lt_gg hLG, hdatT, hKT.1, hKT.2⟩

/-- **The reading of a fixed point of `Γ` from `B₂` on is a closed point.** -/
theorem qd_fix_cl : YwClosed x (qdA e x) := by
  obtain ⟨hL1, hNG, hNT, hKT, hK1⟩ := qd_fix_lev S hx hx1 hA hi hX hB hgx hcode hmono
  rw [qdA_fix S hA hi hX hB x]
  exact qd_vt_closed hx hx1 (add_le_add le_rfl hL1) hNG hNT hKT hK1

end Fix

end Googology.Trans.PoR.InaccPsi.R2.Qd
