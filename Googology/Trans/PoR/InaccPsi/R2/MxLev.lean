import Googology.Trans.PoR.InaccPsi.R2.MxArith
import Googology.Trans.PoR.InaccPsi.R2.LvPh

/-!
# The level of an ε-number below the next strongly critical point, and the cited `lhᵗ` at every level

`τ` strongly critical and countable, `ϑᵗ = vt τ`, `lhᵗ = lhT τ`, `P_β` the range of `φ_β` (`Lu.LuP β`), `lvC β τ`,
`lvInd β τ` the index set and index of `R2.LvPh` (`lvPhLev`: `φ_β(b) = ϑᵗ(Ω₁·β + lvInd β τ b)`).

* `mxDec` (**an ε-number `x` that is not strongly critical is `φ(a, b)` with `1 ≤ a < x`, `b < x`**);
* `mxLev_u` (a level `β ≥ 1` that is not strongly critical above `τ` lies below every `u ∈ P_β` above `τ`);
* `mxLvC_low`, `mxLvC_eq`, `mxLvC_high` (**`lvC β τ = mxC β s`** with `s = τ + 1` for `β < τ`, `s = 1` for `β = τ`,
  `s = 0` for `β > τ`);
* `mxFix_iff` (**the case split of [W07a] Def 4.11 at every level**: `(∀ σ < η, ϑᵗ(Ω₁·β + σ) ≤ η) ⇔ η = 0 ∨
  (τ < η ∧ φ_β(η) = η)`);
* `mxLhT` (**`lhᵗ(ϑᵗ(Ω₁·β + η)) = luL(ϑᵗ(Ω₁·β + η), β) + ζᵗ`** at every level `β ∈ Tᵗ`, `1 ≤ β < Ω₁`, from the
  cited `R2.CitedLu` (`β < τ`) and `R2.CitedLv` (`τ ≤ β`) through `Lu.lu_lh_th`, `Lv.lv_lh_gen`);
* `mxSC_ne_th` (**a strongly critical ordinal is never `ϑᵗ(Ω₁·β + η)`** with `β ∈ Tᵗ`, `1 ≤ β < Ω₁`: the points that
  `R2.CitedLu`, `R2.CitedLv` do not reach start at the least strongly critical point above `τ`).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Mx

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw Googology.Trans.PoR.InaccPsi.R2.Lu

/-- **An ε-number `x > 0` that is not strongly critical is `φ(a, b)` with `1 ≤ a < x` and `b < x`.** -/
theorem mxDec {x : Ordinal.{0}} (hE : InE x) (hx0 : 0 < x) (hnSC : ¬ SC x) :
    veblen (invVeblen₁ x) (invVeblen₂ x) = x ∧ invVeblen₁ x < x ∧ invVeblen₂ x < x ∧ 1 ≤ invVeblen₁ x := by
  have hE' : ω ^ x = x := hE
  have hdec : veblen (invVeblen₁ x) (invVeblen₂ x) = x := by rw [veblen_invVeblen₁_invVeblen₂, hE']
  have hb : invVeblen₂ x < x := by have := invVeblen₂_lt x; rwa [hE'] at this
  have hle : invVeblen₁ x ≤ x := by
    have := left_le_veblen (invVeblen₁ x) (invVeblen₂ x)
    rwa [hdec] at this
  have ha : invVeblen₁ x < x := by
    refine lt_of_le_of_ne hle fun e => hnSC (mwSC_of_fix hx0 ?_)
    apply le_antisymm
    · calc veblen x 0 ≤ veblen x (invVeblen₂ x) := veblen_le_veblen_iff_right.2 zero_le
        _ = x := by nth_rewrite 1 [← e]; exact hdec
    · exact left_le_veblen x 0
  refine ⟨hdec, ha, hb, one_le_iff_ne_zero.2 fun h0 => ?_⟩
  rw [h0, veblen_zero_apply] at hdec
  have : invVeblen₂ x = x := (opow_right_inj one_lt_omega0).1 (hdec.trans hE'.symm)
  exact hb.ne this

/-- A level `β ≥ 1` that is not strongly critical above `τ` lies below every `u ∈ P_β` above `τ`. -/
theorem mxLev_u {τ β : Ordinal.{0}} (hβ1 : 1 ≤ β) (h : τ < β → ¬ SC β) :
    ∀ u, LuP β u → τ < u → β < u := by
  intro u hu hτu
  obtain ⟨j, rfl⟩ := hu
  refine lt_of_le_of_ne (left_le_veblen _ _) fun e => ?_
  have hβ0 : 0 < β := lt_of_lt_of_le zero_lt_one hβ1
  have hfix : veblen β 0 = β := le_antisymm
    (by calc veblen β 0 ≤ veblen β j := veblen_le_veblen_iff_right.2 zero_le
      _ = β := e.symm) (left_le_veblen β 0)
  exact h (e ▸ hτu) (mwSC_of_fix hβ0 hfix)

/-! ## The index set `lvC β τ` as `mxC β s` -/

theorem mxLvC_low {β τ : Ordinal.{0}} (hτ : SC τ) (hβτ : β < τ) : lvC β τ = mxC β (τ + 1) := by
  ext x
  show (τ < veblen β x ∧ ¬ LuP (β + 1) x) ↔ (τ + 1 ≤ x ∧ veblen β x ≠ x)
  rw [luP_succ]
  refine and_congr ⟨fun h => Order.add_one_le_of_lt ?_, fun h => ?_⟩ Iff.rfl
  · by_contra hle
    push Not at hle
    have := (veblen_le_veblen_iff_right (o := β)).2 hle
    rw [hτ.veblen_right hβτ] at this
    exact absurd h (not_lt.2 this)
  · exact (Order.lt_add_one_iff.2 le_rfl).trans_le (h.trans (right_le_veblen _ _))

theorem mxLvC_eq {τ : Ordinal.{0}} (hτ : SC τ) : lvC τ τ = mxC τ 1 := by
  ext x
  show (τ < veblen τ x ∧ ¬ LuP (τ + 1) x) ↔ (1 ≤ x ∧ veblen τ x ≠ x)
  rw [luP_succ]
  refine and_congr ⟨fun h => one_le_iff_ne_zero.2 fun h0 => ?_, fun h => ?_⟩ Iff.rfl
  · rw [h0, hτ.veblen_zero] at h; exact lt_irrefl _ h
  · calc τ = veblen τ 0 := hτ.veblen_zero.symm
      _ < veblen τ x := veblen_lt_veblen_iff_right.2 (lt_of_lt_of_le zero_lt_one h)

theorem mxLvC_high {β τ : Ordinal.{0}} (hτ : SC τ) (hτβ : τ < β) : lvC β τ = mxC β 0 := by
  ext x
  show (τ < veblen β x ∧ ¬ LuP (β + 1) x) ↔ (0 ≤ x ∧ veblen β x ≠ x)
  rw [luP_succ]
  refine and_congr ⟨fun _ => zero_le, fun _ => ?_⟩ Iff.rfl
  calc τ = veblen τ 0 := hτ.veblen_zero.symm
    _ < veblen β 0 := veblen_zero_lt_veblen_zero.2 hτβ
    _ ≤ veblen β x := veblen_le_veblen_iff_right.2 zero_le

/-! ## The case split and the cited value at every level -/

/-- **The case split of [W07a] Def 4.11 at every level `β ∈ Tᵗ`, `1 ≤ β < Ω₁`** (`β` below the members of `P_β`
above `τ`): `(∀ σ < η, ϑᵗ(Ω₁·β + σ) ≤ η) ⇔ η = 0 ∨ (τ < η ∧ φ_β(η) = η)`. -/
theorem mxFix_iff {τ β η : Ordinal.{0}} (hτ : SC τ) (hτ1 : τ < Om1) (hβ1 : 1 ≤ β) (hβT : β ∈ Tset τ)
    (hβΩ : β < Om1) (hβu : ∀ u, LuP β u → τ < u → β < u) (hη : η ∈ Tset τ) (hη1 : η < Om1) :
    (∀ σ, σ < η → vt τ (Om1 * β + σ) ≤ η) ↔ (η = 0 ∨ (τ < η ∧ veblen β η = η)) := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  constructor
  · intro hfix
    rcases eq_or_ne η 0 with h0 | h0
    · exact Or.inl h0
    right
    have h0T : (0 : Ordinal.{0}) ∈ Tset τ := vz_T_down hτE hτ1 hη hη1 zero_le
    obtain ⟨-, -, -, hτv, -, -, -, -⟩ := ul_facts hτE hτ1 hβ1 hβT hβΩ h0T (lt_of_le_of_lt zero_le hη1)
    have hτη : τ < η := hτv.trans_le (hfix 0 (pos_iff_ne_zero.2 h0))
    refine ⟨hτη, ?_⟩
    have hlim : IsSuccLimit η := by
      rcases zero_or_succ_or_isSuccLimit η with h | ⟨σ, hσ⟩ | h
      · exact absurd h h0
      · exfalso
        have hση : σ < η := hσ ▸ lt_succ σ
        have hσT := vz_T_down hτE hτ1 hη hη1 hση.le
        obtain ⟨-, -, -, -, -, hvE, -, hσv⟩ := ul_facts hτE hτ1 hβ1 hβT hβΩ hσT (hση.trans hη1)
        have heq : vt τ (Om1 * β + σ) = η :=
          le_antisymm (hfix σ hση) (hσ ▸ Order.succ_le_of_lt hσv)
        have hvl : IsSuccLimit (vt τ (Om1 * β + σ)) := ev_isSuccLimit_of_inE hvE
        rw [heq, ← hσ] at hvl
        exact not_isSuccLimit_succ σ hvl
      · exact h
    have hall : ∀ b < η, veblen β b ≤ η := by
      intro b hb
      by_cases hbτ : veblen β b ≤ τ
      · exact hbτ.trans hτη.le
      push Not at hbτ
      by_cases hP : LuP (β + 1) b
      · rw [luP_succ.1 hP]; exact hb.le
      · have hmem : b ∈ lvC β τ := ⟨hbτ, hP⟩
        have hlt : lvInd β τ b < lvInd β τ η := Cd.cdOtp_lt_of_mem hmem hb
        have hle : lvInd β τ η ≤ η := Cd.cdOtp_le_self _ η
        have hT' := vz_T_down hτE hτ1 hη hη1 (hlt.trans_le hle).le
        rw [lvPhLev hτ hτ1 hβ1 hβT hβΩ hβu b hbτ hP hT' ((hlt.trans_le hle).trans hη1)]
        exact hfix _ (hlt.trans_le hle)
    have hv : veblen β η ≤ η := ((isNormal_veblen _).le_iff_forall_le hlim).2 hall
    exact le_antisymm hv (right_le_veblen _ _)
  · rintro (h0 | ⟨hτη, hfix⟩)
    · intro σ hσ; rw [h0] at hσ; exact absurd hσ (not_lt.2 zero_le)
    · have hPη : LuP β η := ⟨η, hfix⟩
      have hβη : β < η := hβu η hPη hτη
      have hP1 : LuP (β + 1) η := luP_succ.2 hfix
      intro σ
      induction σ using WellFoundedLT.induction with
      | ind σ IH =>
      intro hσ
      have hσT := vz_T_down hτE hτ1 hη hη1 hσ.le
      refine lv_th_min hτE hτ1 hβ1 hβT hβΩ hσT (hσ.trans hη1) hPη hτη hσ hβη fun σ' hσ' => ?_
      refine lt_of_le_of_ne (IH σ' hσ' (hσ'.trans hσ)) fun e => ?_
      have hσ'T := vz_T_down hτE hτ1 hη hη1 (hσ'.trans hσ).le
      exact lv_th_notP hτE hτ1 hβ1 hβT hβΩ hσ'T ((hσ'.trans hσ).trans hη1) (e ▸ hP1)

/-- **`lhᵗ(ϑᵗ(Ω₁·β + η)) = luL(ϑᵗ(Ω₁·β + η), β) + ζᵗ`** at every level `β ∈ Tᵗ`, `1 ≤ β < Ω₁`. -/
theorem mxLhT {τ β η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hβ1 : 1 ≤ β) (hβT : β ∈ Tset τ)
    (hβΩ : β < Om1) (hη : η ∈ Tset τ) (hη1 : η < Om1) :
    lhT τ (vt τ (Om1 * β + η)) = luL (vt τ (Om1 * β + η)) β + luZeta τ β η := by
  obtain ⟨-, -, haT, hτa, ha1, haE, -, -⟩ := ul_facts hτ hτ1 hβ1 hβT hβΩ hη hη1
  rcases lt_or_ge β τ with h | h
  · exact lu_lhT_eq hτ hτ1 haT hτa ha1 (inE_indec haE) (lu_lh_th hτ hτ1 hβ1 h hη hη1)
  · exact lu_lhT_eq hτ hτ1 haT hτa ha1 (inE_indec haE) (Lv.lv_lh_gen hτ hτ1 hβT h hβΩ hη hη1)

/-- **A strongly critical ordinal is never `ϑᵗ(Ω₁·β + η)`** (`β ∈ Tᵗ`, `1 ≤ β < Ω₁`, `η ∈ Tᵗ ∩ Ω₁`). -/
theorem mxSC_ne_th {τ β η s : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hβ1 : 1 ≤ β) (hβT : β ∈ Tset τ)
    (hβΩ : β < Om1) (hη : η ∈ Tset τ) (hη1 : η < Om1) (hs : SC s) : s ≠ vt τ (Om1 * β + η) := by
  intro e
  obtain ⟨-, -, -, -, -, -, hβv, -⟩ := ul_facts hτ hτ1 hβ1 hβT hβΩ hη hη1
  rw [← e] at hβv
  have hfix : veblen β s = s := hs.veblen_right hβv
  exact lv_th_notP hτ hτ1 hβ1 hβT hβΩ hη hη1 (e ▸ luP_succ.2 hfix)

end Googology.Trans.PoR.InaccPsi.R2.Mx
