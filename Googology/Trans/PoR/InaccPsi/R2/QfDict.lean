import Googology.Trans.PoR.InaccPsi.R2.QfZeta

/-!
# QfDict: THE ϑ-TERM OF A VEBLEN POINT AT EVERY COUNTABLE LEVEL, STRONGLY CRITICAL LEVELS INCLUDED

`lvPhLev` gives `φ_β(b) = ϑʸ(Ω₁·β + ind(b))` for the levels `β` whose points above `y` lie above `β`.  At a strongly
critical level `β > y` the point `φ_β(0) = β` is not of the form `ϑʸ(Ω₁·β + η)`; here the index counts only the
arguments `x` with `max(y, β) < φ_β(x)`:

* `qfC' β y` (the arguments `x` off `P_{β+1}` with `y < φ_β(x)` and `β < φ_β(x)`), `qfInd β y b`;
* `qf_dict'` (**`φ_β(b) = ϑʸ(Ω₁·β + qfInd β y b)` for every countable level `1 ≤ β ∈ Tʸ`**), the proof of `lvPhLev`
  with the condition `β < φ_β(b)` in the set;
* `qfInd_P` (**`qfInd(p) = p`** for a fixed point `p > y` of `φ_β`).

No new axiom.  New definitions: `qfC'`, `qfInd`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qf

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Gg

/-- The arguments `x` off `P_{β+1}` with `y < φ_β(x)` and `β < φ_β(x)`. -/
def qfC' (β y : Ordinal.{0}) : Set Ordinal.{0} := {x | y < veblen β x ∧ β < veblen β x ∧ ¬ LuP (β + 1) x}

/-- The index of `b` in `qfC' β y`. -/
noncomputable def qfInd (β y b : Ordinal.{0}) : Ordinal.{0} := cdOtp (qfC' β y) b

/-- **THE ϑ-TERM OF A VEBLEN POINT AT EVERY COUNTABLE LEVEL** `1 ≤ β ∈ Tʸ ∩ Ω₁` over a strongly critical `y < Ω₁`:
`φ_β(b) = ϑʸ(Ω₁·β + qfInd β y b)` for `b ∈ qfC' β y` with the index in `Tʸ ∩ Ω₁`. -/
theorem qf_dict' {β y : Ordinal.{0}} (hy : SC y) (hy1 : y < Om1) (hβ1 : 1 ≤ β) (hβT : β ∈ Tset y)
    (hβΩ : β < Om1) :
    ∀ b, y < veblen β b → β < veblen β b → ¬ LuP (β + 1) b → qfInd β y b ∈ Tset y → qfInd β y b < Om1 →
      veblen β b = vt y (Om1 * β + qfInd β y b) := by
  have hyE : InE y := gg_SC_eps hy
  intro b
  induction b using WellFoundedLT.induction with
  | ind b IH =>
  intro hyb hβb hbP hT h1
  have hbv : b < veblen β b :=
    lt_of_le_of_ne (right_le_veblen _ _) (fun e => hbP (luP_succ.2 e.symm))
  apply le_antisymm
  · have hfacts := ul_facts hyE hy1 hβ1 hβT hβΩ hT h1
    have hnP := lv_th_notP hyE hy1 hβ1 hβT hβΩ hT h1
    obtain ⟨b', hb'⟩ := lv_th_P hyE hy1 β hβ1 hβT hβΩ _ hT h1
    have hyb' : y < veblen β b' := by rw [hb']; exact hfacts.2.2.2.1
    have hβb' : β < veblen β b' := by rw [hb']; exact hfacts.2.2.2.2.2.2.1
    have hb'P : ¬ LuP (β + 1) b' := by
      intro hP
      have hfx : veblen β b' = b' := luP_succ.1 hP
      apply hnP
      rw [← hb', hfx]; exact hP
    rcases lt_or_ge b' b with hlt | hge
    · exfalso
      have hmem : b' ∈ qfC' β y := ⟨hyb', hβb', hb'P⟩
      have hlt' : qfInd β y b' < qfInd β y b := cdOtp_lt_of_mem hmem hlt
      have hT' := vz_T_down hyE hy1 hT h1 hlt'.le
      have e := IH b' hlt hyb' hβb' hb'P hT' (hlt'.trans h1)
      have h3 := ul_eta_lt hyE hy1 hβ1 hβT hβΩ hT' hT h1 hlt'
      rw [← e, hb'] at h3
      exact lt_irrefl _ h3
    · rw [← hb']; exact veblen_le_veblen_iff_right.2 hge
  · refine lv_th_min hyE hy1 hβ1 hβT hβΩ hT h1 (luP_veblen β b) hyb
      ((cdOtp_le_self _ b).trans_lt hbv) hβb fun σ hσ => ?_
    obtain ⟨b', hb'C, hb'b, hσe⟩ := ggOtp_onto (qfC' β y) b σ hσ
    obtain ⟨hyb', hβb', hb'P⟩ := hb'C
    have hσe' : qfInd β y b' = σ := hσe
    have hT' : qfInd β y b' ∈ Tset y := by rw [hσe']; exact vz_T_down hyE hy1 hT h1 hσ.le
    rw [← hσe', ← IH b' hb'b hyb' hβb' hb'P hT' (by rw [hσe']; exact hσ.trans h1)]
    exact veblen_lt_veblen_iff_right.2 hb'b

/-- **`qfInd(p) = p`** for a fixed point `p > y` of `φ_β` (`p ∈ P_{β+1}`). -/
theorem qfInd_P {β y : Ordinal.{0}} : ∀ p, LuP (β + 1) p → y < p → qfInd β y p = p := by
  intro p
  induction p using WellFoundedLT.induction with
  | ind p IH =>
  intro hP hyp
  refine le_antisymm (cdOtp_le_self _ p) (le_of_forall_lt fun α hα => ?_)
  have hβp : β ≤ p := by rw [← luP_succ.1 hP]; exact left_le_veblen β p
  by_cases hex : ∃ p', LuP (β + 1) p' ∧ max α y < p' ∧ p' < p
  · obtain ⟨p', hP', hm, hp'⟩ := hex
    calc α < p' := (le_max_left α y).trans_lt hm
      _ = qfInd β y p' := (IH p' hp' hP' ((le_max_right α y).trans_lt hm)).symm
      _ ≤ qfInd β y p := cdOtp_mono _ hp'.le
  · push Not at hex
    have hmp : max α y < p := max_lt hα hyp
    have hm1 : max α y + 1 < p := by rw [← succ_eq_add_one]; exact (lu_P_lim hP).succ_lt hmp
    have hprin : IsPrincipal (· + ·) p := by
      have hE' : ω ^ p = p := lu_P_E hP
      rw [← hE']; exact isPrincipal_add_omega0_opow p
    have e : max α y + 1 + p = p := hprin.add_eq_right hm1
    have hsh := phOtp_shift (qfC' β y) (max α y + 1) p fun z hz => by
      have hyz : y < max α y + 1 + z := (le_max_right α y).trans_lt ((lt_add_one _).trans_le le_self_add)
      have hzP : ¬ LuP (β + 1) (max α y + 1 + z) := fun hz' => by
        have h1 := hex _ hz' ((lt_add_one _).trans_le le_self_add)
        have h2 : max α y + 1 + z < max α y + 1 + p := (add_lt_add_iff_left _).2 hz
        rw [e] at h2
        exact absurd h1 (not_le.2 h2)
      refine ⟨hyz.trans_le (right_le_veblen _ _), ?_, hzP⟩
      exact (left_le_veblen β 0).trans_lt ((veblen_lt_veblen_iff_right).2
        (lt_of_lt_of_le (lt_add_one _) le_self_add |>.trans_le' zero_le))
    rw [e] at hsh
    show α < cdOtp (qfC' β y) p
    rw [hsh]
    exact hα.trans_le le_add_self

end Googology.Trans.PoR.InaccPsi.R2.Qf
