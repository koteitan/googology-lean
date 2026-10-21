import Googology.Trans.PoR.InaccPsi.R2.LqPsi

/-!
# The level lemma at a strongly critical level `β > τ`

For a strongly critical base `y < Ω₁` and a strongly critical level `β ∈ Tʸ ∩ Ω₁` with `y < β` (so `φ_β(0) = β` and the
values `ϑʸ(Ω₁·β + η) > β` start at `φ_β(1)`), with the index `ind(b) = Mx.mxIx β 1 b` (the order type of the ordinals
`x ∈ [1, b)` off the fixed points of `φ_β`), from the cited `R2.CitedLv` through `R2.LvLev`:

* `lqPhLevSC` (**`φ_β(b) = ϑʸ(Ω₁·β + ind(b))`** for every `b ≥ 1` off `P_{β+1}` with `ind(b) ∈ Tʸ ∩ Ω₁`; as `lvPhLev`,
  whose index set `lvC β y` contains `0` at such a level);
* `lqFix_iffSC` (**the case split of [W07a] Def 4.11 at such a level**: `(∀ σ < η, ϑʸ(Ω₁·β + σ) ≤ η) ⇔ η = 0 ∨ (y < η
  ∧ φ_β(η) = η)`; as `Mx.mxFix_iff`).

No new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Lq

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mx

section Level

variable {β y : Ordinal.{0}} (hy : SC y) (hy1 : y < Om1) (hβ : SC β) (hyβ : y < β) (hβT : β ∈ Tset y)
  (hβΩ : β < Om1)
include hy hy1 hβ hyβ hβT hβΩ

/-- **THE LEVEL LEMMA at a strongly critical level `β > y`**: `φ_β(b) = ϑʸ(Ω₁·β + ind(b))`, `ind = Mx.mxIx β 1`, for
`b ≥ 1` off `P_{β+1}` with `ind(b) ∈ Tʸ ∩ Ω₁`. -/
theorem lqPhLevSC : ∀ b, 1 ≤ b → ¬ Lu.LuP (β + 1) b → mxIx β 1 b ∈ Tset y → mxIx β 1 b < Om1 →
    veblen β b = vt y (Om1 * β + mxIx β 1 b) := by
  have hyE : InE y := Gg.gg_SC_eps hy
  have hβ1 : 1 ≤ β := (Lu.lu_one_lt_E (Gg.gg_SC_eps hβ)).le
  intro b
  induction b using WellFoundedLT.induction with
  | ind b IH =>
  intro hb1 hbP hT h1
  have hbv : b < veblen β b :=
    lt_of_le_of_ne (right_le_veblen _ _) (fun e => hbP (Lu.luP_succ.2 e.symm))
  apply le_antisymm
  · have hfacts := ul_facts hyE hy1 hβ1 hβT hβΩ hT h1
    have hnP := lv_th_notP hyE hy1 hβ1 hβT hβΩ hT h1
    obtain ⟨b', hb'⟩ := lv_th_P hyE hy1 β hβ1 hβT hβΩ _ hT h1
    have hb'1 : 1 ≤ b' := by
      refine one_le_iff_ne_zero.2 fun h0 => ?_
      have h2 := hfacts.2.2.2.2.2.2.1
      rw [← hb', h0, hβ.veblen_zero] at h2
      exact lt_irrefl _ h2
    have hb'P : ¬ Lu.LuP (β + 1) b' := by
      intro hP
      have hfx : veblen β b' = b' := Lu.luP_succ.1 hP
      apply hnP
      rw [← hb', hfx]; exact hP
    rcases lt_or_ge b' b with hlt | hge
    · exfalso
      have hmem : b' ∈ mxC β 1 := ⟨hb'1, fun e => hb'P (Lu.luP_succ.2 e)⟩
      have hlt' : mxIx β 1 b' < mxIx β 1 b := Cd.cdOtp_lt_of_mem hmem hlt
      have hT' := vz_T_down hyE hy1 hT h1 hlt'.le
      have e := IH b' hlt hb'1 hb'P hT' (hlt'.trans h1)
      have h3 := ul_eta_lt hyE hy1 hβ1 hβT hβΩ hT' hT h1 hlt'
      rw [← e, hb'] at h3
      exact lt_irrefl _ h3
    · rw [← hb']; exact veblen_le_veblen_iff_right.2 hge
  · have hβb : β < veblen β b := by
      calc β = veblen β 0 := hβ.veblen_zero.symm
        _ < veblen β b := veblen_lt_veblen_iff_right.2 (lt_of_lt_of_le zero_lt_one hb1)
    refine lv_th_min hyE hy1 hβ1 hβT hβΩ hT h1 (Lu.luP_veblen β b) (hyβ.trans hβb)
      ((mxIx_le β 1 b).trans_lt hbv) hβb fun σ hσ => ?_
    obtain ⟨b', hb'C, hb'b, hσe⟩ := Gg.ggOtp_onto (mxC β 1) b σ hσ
    obtain ⟨hb'1, hb'n⟩ := hb'C
    have hσe' : mxIx β 1 b' = σ := hσe
    have hb'P : ¬ Lu.LuP (β + 1) b' := fun hP => hb'n (Lu.luP_succ.1 hP)
    have hT' : mxIx β 1 b' ∈ Tset y := by rw [hσe']; exact vz_T_down hyE hy1 hT h1 hσ.le
    rw [← hσe', ← IH b' hb'b hb'1 hb'P hT' (by rw [hσe']; exact hσ.trans h1)]
    exact veblen_lt_veblen_iff_right.2 hb'b

/-- **The case split of [W07a] Def 4.11 at a strongly critical level `β > y`**: `(∀ σ < η, ϑʸ(Ω₁·β + σ) ≤ η) ⇔
η = 0 ∨ (y < η ∧ φ_β(η) = η)`. -/
theorem lqFix_iffSC {η : Ordinal.{0}} (hη : η ∈ Tset y) (hη1 : η < Om1) :
    (∀ σ, σ < η → vt y (Om1 * β + σ) ≤ η) ↔ (η = 0 ∨ (y < η ∧ veblen β η = η)) := by
  have hyE : InE y := Gg.gg_SC_eps hy
  have hβ1 : 1 ≤ β := (Lu.lu_one_lt_E (Gg.gg_SC_eps hβ)).le
  constructor
  · intro hfix
    rcases eq_or_ne η 0 with h0 | h0
    · exact Or.inl h0
    right
    have h0T : (0 : Ordinal.{0}) ∈ Tset y := vz_T_down hyE hy1 hη hη1 zero_le
    obtain ⟨-, -, -, hyv, -, -, hβv, -⟩ := ul_facts hyE hy1 hβ1 hβT hβΩ h0T (lt_of_le_of_lt zero_le hη1)
    have hv0 := hfix 0 (pos_iff_ne_zero.2 h0)
    have hyη : y < η := hyv.trans_le hv0
    have hβη : β < η := hβv.trans_le hv0
    refine ⟨hyη, ?_⟩
    have hlim : IsSuccLimit η := by
      rcases zero_or_succ_or_isSuccLimit η with h | ⟨σ, hσ⟩ | h
      · exact absurd h h0
      · exfalso
        have hση : σ < η := hσ ▸ lt_succ σ
        have hσT := vz_T_down hyE hy1 hη hη1 hση.le
        obtain ⟨-, -, -, -, -, hvE, -, hσv⟩ := ul_facts hyE hy1 hβ1 hβT hβΩ hσT (hση.trans hη1)
        have heq : vt y (Om1 * β + σ) = η :=
          le_antisymm (hfix σ hση) (hσ ▸ Order.succ_le_of_lt hσv)
        have hvl : IsSuccLimit (vt y (Om1 * β + σ)) := ev_isSuccLimit_of_inE hvE
        rw [heq, ← hσ] at hvl
        exact not_isSuccLimit_succ σ hvl
      · exact h
    have hall : ∀ b < η, veblen β b ≤ η := by
      intro b hb
      rcases eq_or_ne b 0 with rfl | hb0
      · rw [hβ.veblen_zero]; exact hβη.le
      by_cases hP : Lu.LuP (β + 1) b
      · rw [Lu.luP_succ.1 hP]; exact hb.le
      · have hb1 : 1 ≤ b := one_le_iff_ne_zero.2 hb0
        have hmem : b ∈ mxC β 1 := ⟨hb1, fun e => hP (Lu.luP_succ.2 e)⟩
        have hlt : mxIx β 1 b < mxIx β 1 η := Cd.cdOtp_lt_of_mem hmem hb
        have hle : mxIx β 1 η ≤ η := mxIx_le β 1 η
        have hT' := vz_T_down hyE hy1 hη hη1 (hlt.trans_le hle).le
        rw [lqPhLevSC hy hy1 hβ hyβ hβT hβΩ b hb1 hP hT' ((hlt.trans_le hle).trans hη1)]
        exact hfix _ (hlt.trans_le hle)
    have hv : veblen β η ≤ η := ((isNormal_veblen _).le_iff_forall_le hlim).2 hall
    exact le_antisymm hv (right_le_veblen _ _)
  · rintro (h0 | ⟨hyη, hfix⟩)
    · intro σ hσ; rw [h0] at hσ; exact absurd hσ (not_lt.2 zero_le)
    · have hPη : Lu.LuP β η := ⟨η, hfix⟩
      have hβη : β < η := by
        refine lt_of_le_of_ne ?_ fun e => ?_
        · calc β = veblen β 0 := hβ.veblen_zero.symm
            _ ≤ veblen β η := veblen_le_veblen_iff_right.2 zero_le
            _ = η := hfix
        · rw [← e] at hfix
          exact absurd hfix (ne_of_gt (lt_veblen β))
      have hP1 : Lu.LuP (β + 1) η := Lu.luP_succ.2 hfix
      intro σ
      induction σ using WellFoundedLT.induction with
      | ind σ IH =>
      intro hσ
      have hσT := vz_T_down hyE hy1 hη hη1 hσ.le
      refine lv_th_min hyE hy1 hβ1 hβT hβΩ hσT (hσ.trans hη1) hPη hyη hσ hβη fun σ' hσ' => ?_
      refine lt_of_le_of_ne (IH σ' hσ' (hσ'.trans hσ)) fun e => ?_
      have hσ'T := vz_T_down hyE hy1 hη hη1 (hσ'.trans hσ).le
      exact lv_th_notP hyE hy1 hβ1 hβT hβΩ hσ'T ((hσ'.trans hσ).trans hη1) (e ▸ hP1)

end Level

end Googology.Trans.PoR.InaccPsi.R2.Lq
