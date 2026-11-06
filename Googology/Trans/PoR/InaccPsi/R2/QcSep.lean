import Googology.Trans.PoR.InaccPsi.R2.QcImg
import Googology.Trans.PoR.InaccPsi.R2.YwSep

/-!
# QcSep: THE SEPARATION AT A POINT OF A GENERIC LEVEL, AND LEMMA IMG THERE

For `E = ϑˣ(Ω₁·M + σ)`, `Ω₁ ≤ M < ε_{Ω₁+1}` (`Yw.ywRep`, `Yw.ywLB`, `Yw.ywSep` do the levels `M = Ω₁ + j`, `j < Ω₁`):

* `qc_rep` (**every `ε`-number `a ∈ (x, E)` above the data of `M` and `σ` is of Veblen level, or a point
  `ϑˣ(Ω₁·M' + σ')` of a level `Ω₁ ≤ M'` with `(M', σ') < (M, σ)` lexicographically**; [W07a] Lemma 3.30 through
  `rjLt_of_vt_lt`);
* `qc_LB` (**the lower bound `E'`**: above `L`, the data of `M` and `σ`, and above the earlier points of level `M`
  whose `ζ` is not below `ζ_E`);
* `qc_sep` (**THE SEPARATION** in the form of `Qc.qc_img_atom`: a Veblen point `a` has a reach below `a·a`
  (`Yw.ywLow`); a point of a lower level `M'` has the reach `Θ_a(rjL(Ω₁·M')) + ζ' < Θ_a(rjL(Ω₁·M))`
  (`Qc.qc_rjL_gap`, `ζ' < a`); a point of level `M` has the reach `Θ_a(rjL(Ω₁·M)) + ζ'` with `ζ' < ζ_E` by `E'`);
* `qc_img_lvl` (**LEMMA IMG AT EVERY POINT OF EVERY LEVEL `Ω₁ ≤ M < ε_{Ω₁+1}`** given it below, `ρ` strongly
  critical).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rj Googology.Trans.PoR.InaccPsi.R2.Lu
  Googology.Trans.PoR.InaccPsi.R2.Yw Googology.Trans.PoR.InaccPsi.R2.Gn

theorem qc_Om1_lt_Om2 : (Om1 : Ordinal.{0}) < OmTwo := omega_lt_omega.2 one_lt_two

/-- The argument `Ω₁·M + σ` of a level `M < ε_{Ω₁+1}` is below `Ω₂`. -/
theorem qc_arg_lt {M σ : Ordinal.{0}} (hME : M < ggE) (hσΩ : σ < Om1) : Om1 * M + σ < OmTwo := by
  have hS : SC (OmTwo : Ordinal.{0}) := by rw [Uc.uc_Om2_eq]; exact SC_Om (by simp)
  have hE2 : InE (OmTwo : Ordinal.{0}) := Low.opow_eq_self_of_SC hS
  have hgO : ggE < OmTwo := qc_ggE_lt_B.trans Uc.ucB_lt_Om2
  exact (Lq.lq_SC_indec hS).add_lt (hE2.mul_lt qc_Om1_lt_Om2 (hME.trans hgO)) (hσΩ.trans qc_Om1_lt_Om2)

section Sep

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

/-- **The `ε`-numbers below a point of level `M`** (above `x`, the data of `M` and `σ`). -/
theorem qc_rep {M σ a : Ordinal.{0}} (hM1 : Om1 ≤ M) (hME : M < ggE) (hMT : rjDat M ∈ Tset x)
    (hσT : σ ∈ Tset x) (hσΩ : σ < Om1) (haE : InE a) (hxa : x < a) (hda : rjDat M < a) (hσa : σ < a)
    (hae : a < vt x (Om1 * M + σ)) :
    (∃ q t, 1 ≤ q ∧ q ∈ Tset x ∧ q < Om1 ∧ t ∈ Tset x ∧ t < Om1 ∧ vt x (Om1 * q + t) = a) ∨
    (∃ M' σ', Om1 ≤ M' ∧ M' < ggE ∧ rjDat M' ∈ Tset x ∧ σ' ∈ Tset x ∧ σ' < Om1 ∧
      vt x (Om1 * M' + σ') = a ∧ (M' < M ∨ (M' = M ∧ σ' < σ))) := by
  have hargT := rjArg_mem hx hx1 hM1 hME hMT hσT hσΩ
  obtain ⟨hET, -, hE1, -, -⟩ := vt_memTwo hx hx1 hargT (qc_arg_lt hME hσΩ)
  have ha1 : a < Om1 := hae.trans hE1
  have haT : a ∈ Tset x := vz_T_down hx hx1 hET hE1 hae.le
  obtain ⟨ξ, hξT, hξ2, hξv⟩ := vt_rep hx hx1 haT hxa.le ha1 (inE_indec haE)
  have hΩξ : Om1 ≤ ξ := (vt_E_iff hx hx1 hξT hξ2).1 ⟨by rw [hξv]; exact hxa, by rw [hξv]; exact haE⟩
  have hξlt : ξ < Om1 * M + σ := rjLt_of_vt_lt hx hx1 hξT hξ2 hM1 hME hMT hσT hσΩ (by rw [hξv]; exact hda)
    (by rw [hξv]; exact hσa) (by rw [hξv]; exact hae)
  obtain ⟨hq1, hrT, hr1, hdec⟩ := lu_split hx hx1 hξT hξ2 hΩξ
  set M' := ξ / Om1 with hM'
  set σ' := ξ % Om1 with hσ'
  have hlex : M' < M ∨ (M' = M ∧ σ' < σ) := by
    rw [← hdec] at hξlt
    rcases lt_trichotomy M' M with hl | he | hg
    · exact Or.inl hl
    · refine Or.inr ⟨he, ?_⟩
      rw [he] at hξlt; exact (add_lt_add_iff_left _).1 hξlt
    · exfalso
      have : Om1 * M + σ < Om1 * M' + σ' :=
        calc Om1 * M + σ < Om1 * M + Om1 := (add_lt_add_iff_left _).2 hσΩ
          _ = Om1 * (M + 1) := (mul_add_one _ _).symm
          _ ≤ Om1 * M' := mul_le_mul_right (Order.add_one_le_of_lt hg) _
          _ ≤ Om1 * M' + σ' := le_self_add
      exact absurd (this.trans hξlt) (lt_irrefl _)
  rcases lt_or_ge M' Om1 with hM'Ω | hM'Ω
  · left
    have hξs : ξ < Om1 * Om1 := by
      rw [← hdec]
      calc Om1 * M' + σ' < Om1 * M' + Om1 := (add_lt_add_iff_left _).2 hr1
        _ = Om1 * (M' + 1) := (mul_add_one _ _).symm
        _ ≤ Om1 * Om1 := mul_le_mul_right (Order.add_one_le_of_lt hM'Ω) _
    refine ⟨M', σ', hq1, lgQuot_mem hx hx1 hξT hξs, hM'Ω, hrT, hr1, ?_⟩
    rw [hdec, hξv]
  · right
    have hM'M : M' ≤ M := by rcases hlex with h | ⟨h, -⟩ <;> [exact h.le; exact h.le]
    have hM'E : M' < ggE := hM'M.trans_lt hME
    have hM'T : rjDat M' ∈ Tset x := rkArg_dat hx hx1 hM'Ω hM'E hr1 (by rw [hdec]; exact hξT)
    exact ⟨M', σ', hM'Ω, hM'E, hM'T, hrT, hr1, by rw [hdec, hξv], hlex⟩

/-- **The lower bound exists** (for every `L < E`). -/
theorem qc_LB {M σ L : Ordinal.{0}} (hM1 : Om1 ≤ M) (hME : M < ggE) (hMT : rjDat M ∈ Tset x)
    (hσT : σ ∈ Tset x) (hσΩ : σ < Om1) (hL : L < vt x (Om1 * M + σ)) :
    ∃ E', L ≤ E' ∧ rjDat M ≤ E' ∧ σ ≤ E' ∧ E' < vt x (Om1 * M + σ) ∧
      ∀ σ', σ' ∈ Tset x → σ' < σ → E' < vt x (Om1 * M + σ') →
        lqZeta x (Om1 * M) σ' < lqZeta x (Om1 * M) σ := by
  obtain ⟨hje, hσe⟩ := rjLevel_lt_vt hx hx1 hM1 hME hMT hσT hσΩ
  have hlt_same : ∀ σ₀, σ₀ ∈ Tset x → σ₀ < σ → vt x (Om1 * M + σ₀) < vt x (Om1 * M + σ) := fun σ₀ hσ₀T hσ₀ =>
    rjVt_lt hx hx1 hME hMT hσ₀T (hσ₀.trans hσΩ) hM1 hME hMT hσT hσΩ ((add_lt_add_iff_left _).2 hσ₀) hje
      (hσ₀.trans hσe)
  have hle_same : ∀ σ₀ σ₁, σ₀ ∈ Tset x → σ₁ ∈ Tset x → σ₁ < Om1 → σ₀ ≤ σ₁ →
      vt x (Om1 * M + σ₀) ≤ vt x (Om1 * M + σ₁) := fun σ₀ σ₁ hσ₀T hσ₁T hσ₁Ω hle => by
    rcases hle.lt_or_eq with hlt | rfl
    · obtain ⟨hj1, hs1⟩ := rjLevel_lt_vt hx hx1 hM1 hME hMT hσ₁T hσ₁Ω
      exact (rjVt_lt hx hx1 hME hMT hσ₀T (hlt.trans hσ₁Ω) hM1 hME hMT hσ₁T hσ₁Ω ((add_lt_add_iff_left _).2 hlt)
        hj1 (hlt.trans hs1)).le
    · exact le_rfl
  by_cases hc : ∃ σ'', σ'' < σ ∧ σ < vt x (Om1 * M + σ'')
  · have hσ0 : σ ≠ 0 := by
      obtain ⟨σ'', h1, -⟩ := hc
      exact (lt_of_le_of_lt zero_le h1).ne'
    have hzσ : lqZeta x (Om1 * M) σ = lg σ := by unfold lqZeta; rw [if_pos hc]
    obtain ⟨σ0, hdec, hdvd, hσ0σ⟩ := lg_split hσ0
    have hσ0T : σ0 ∈ Tset x := vz_T_down hx hx1 hσT hσΩ hσ0σ.le
    have hP : vt x (Om1 * M + σ0) < vt x (Om1 * M + σ) := hlt_same σ0 hσ0T hσ0σ
    refine ⟨max (max L (rjDat M)) (max σ (vt x (Om1 * M + σ0))), (le_max_left _ _).trans (le_max_left _ _),
      (le_max_right _ _).trans (le_max_left _ _), (le_max_left _ _).trans (le_max_right _ _),
      max_lt (max_lt hL hje) (max_lt hσe hP), fun σ' hσ'T hσ'σ hE' => ?_⟩
    have hσ0σ' : σ0 < σ' := by
      by_contra hle
      push Not at hle
      have h1 := hle_same σ' σ0 hσ'T hσ0T (hσ0σ.trans hσΩ) hle
      have h2 : vt x (Om1 * M + σ0) ≤ max (max L (rjDat M)) (max σ (vt x (Om1 * M + σ0))) :=
        (le_max_right _ _).trans (le_max_right _ _)
      exact absurd (hE'.trans_le (h1.trans h2)) (lt_irrefl _)
    rw [hzσ]
    exact ywZeta_le_lg.trans_lt (Gc.gc_lg_lt hdec hdvd hσ0σ' hσ'σ)
  · push Not at hc
    refine ⟨max (max L (rjDat M)) σ, (le_max_left _ _).trans (le_max_left _ _),
      (le_max_right _ _).trans (le_max_left _ _), le_max_right _ _, max_lt (max_lt hL hje) hσe,
      fun σ' _ hσ'σ hE' => ?_⟩
    exact absurd (hE'.trans_le ((hc σ' hσ'σ).trans (le_max_right _ _))) (lt_irrefl _)

/-- **THE SEPARATION** (the hypothesis of `Qc.qc_img_atom`), for a strongly critical base `x`. -/
theorem qc_sep (hxS : SC x) {M σ E' : Ordinal.{0}} (hM1 : Om1 ≤ M) (hME : M < ggE) (hMT : rjDat M ∈ Tset x)
    (hσT : σ ∈ Tset x) (hσΩ : σ < Om1) (hxE' : x ≤ E') (hdE' : rjDat M ≤ E') (hσE' : σ ≤ E')
    (hJ : ∀ σ', σ' ∈ Tset x → σ' < σ → E' < vt x (Om1 * M + σ') →
      lqZeta x (Om1 * M) σ' < lqZeta x (Om1 * M) σ) :
    ∀ a, InE a → E' < a → a < vt x (Om1 * M + σ) →
      (SC a → ¬ le1R a (ggTh a (rjL (Om1 * M)) + lqZeta x (Om1 * M) σ)) ∧ (¬ SC a → ¬ le1R a (a * a)) := by
  intro a haE hE'a hae
  have hM0 : Om1 * M ≠ 0 := (mul_pos rj_Om1_pos (rj_Om1_pos.trans_le hM1)).ne'
  set z := lqZeta x (Om1 * M) σ with hz
  rcases qc_rep hx hx1 hM1 hME hMT hσT hσΩ haE (hxE'.trans_lt hE'a) (hdE'.trans_lt hE'a) (hσE'.trans_lt hE'a)
      hae with ⟨q, t, hq1, hqT, hqΩ, htT, ht1, hv⟩ | ⟨M', σ', hM'1, hM'E, hM'T, hσ'T, hσ'Ω, hv, hcase⟩
  · -- a Veblen point: its reach is below `a·a`
    refine ⟨fun haS => ?_, fun _ => by rw [← hv]; exact ywLow hx hx1 hq1 hqT hqΩ htT ht1 le_rfl⟩
    have ha1 : a < Om 1 := by
      rw [← rj_Om1]
      exact hae.trans (vt_memTwo hx hx1 (rjArg_mem hx hx1 hM1 hME hMT hσT hσΩ) (qc_arg_lt hME hσΩ)).2.2.1
    have haM : GgCl a M := rj_code haS.1 M hME (hdE'.trans_lt hE'a)
    have hOM : GgCl a (Om1 * M) := by rw [rj_Om1]; exact Rk.rk_cl_Om1_mul haS haM
    have hsq : a * a ≤ ggTh a (rjL (Om1 * M)) := by
      have h1 : ggTh a (Om1 * Om1) = a * a := by
        rw [rj_Th_mul haS (by rw [rj_Om1]; exact ha1) (by rw [rj_Om1]; exact GgCl.om), rj_Om1, ggTh_Om1 haS ha1]
      rw [← h1]
      exact ggTh_mono ((mul_le_mul_right hM1 _).trans (qc_rjL_ge hM0))
    have hlow := ywLow hx hx1 hq1 hqT hqΩ htT ht1 (L := ggTh a (rjL (Om1 * M)) + z)
      (by rw [hv]; exact hsq.trans le_self_add)
    rwa [hv] at hlow
  · -- a point of a level `M' ≥ Ω₁`: strongly critical
    have haS : SC a := by rw [← hv]; exact rjK_SC hxS hx1 hM'1 hM'E hM'T hσ'T hσ'Ω
    refine ⟨fun _ hR => ?_, fun hnS => absurd haS hnS⟩
    obtain ⟨hL, -⟩ := rj_lh hxS hx1 hM'1 hM'E hM'T hσ'T hσ'Ω
    rw [hv] at hL
    have ha1 : a < Om 1 := by
      rw [← rj_Om1, ← hv]; exact (rjK_facts hxS hx1 hM'1 hM'E hM'T hσ'T hσ'Ω).2.2.2.2.1
    have hle := hL.2 _ hR
    have hσ'a : σ' < a := by rw [← hv]; exact (rjLevel_lt_vt hx hx1 hM'1 hM'E hM'T hσ'T hσ'Ω).2
    set ζ := lqZeta x (Om1 * M') σ' with hζ
    have hζa : ζ < a := (rj_zeta_le x (Om1 * M') σ').trans_lt hσ'a
    have hM'0 : Om1 * M' ≠ 0 := (mul_pos rj_Om1_pos (rj_Om1_pos.trans_le hM'1)).ne'
    have haM' : GgCl a M' := by rw [← hv]; exact rj_code_of hxS hx1 hM'1 hM'E hM'T hσ'T hσ'Ω
    have hOM' : GgCl a (Om1 * M') := by rw [rj_Om1]; exact Rk.rk_cl_Om1_mul haS haM'
    obtain ⟨hΛ'C, hΛ'th⟩ := qc_th_rjL haS hOM' hM'0
    rw [← hΛ'th] at hle
    rcases hcase with hlt | ⟨rfl, hσσ⟩
    · -- a lower level
      have hgap : rjL (Om1 * M') + Om1 ≤ rjL (Om1 * M) := by
        rw [rj_Om1]; exact qc_rjL_gap (by rw [← rj_Om1]; exact hM'1) hlt
      have h1 : ggTh a (rjL (Om1 * M')) + a ≤ ggTh a (rjL (Om1 * M)) := by
        have hΩ : ggTh a Om1 = a := by rw [rj_Om1]; exact ggTh_Om1 haS ha1
        have := ggTh_mono (y := a) hgap
        rwa [ggTh_add haS hΛ'C, hΩ] at this
      have h2 : ggTh a (rjL (Om1 * M')) + ζ < ggTh a (rjL (Om1 * M)) + z :=
        ((add_lt_add_iff_left _).2 hζa).trans_le (h1.trans le_self_add)
      exact absurd (hle.trans_lt h2) (lt_irrefl _)
    · -- the same level
      have hz' : ζ < z := hJ σ' hσ'T hσσ (by rw [hv]; exact hE'a)
      exact absurd (hle.trans_lt ((add_lt_add_iff_left _).2 hz')) (lt_irrefl _)

end Sep

section Img

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

/-- **LEMMA IMG AT A POINT `ϑᵖ(Ω₁·M + σ)` OF A LEVEL `Ω₁ ≤ M < ε_{Ω₁+1}`**, given it below (`ρ` strongly
critical). -/
theorem qc_img_lvl (hρS : SC ρ) {M σ : Ordinal.{0}} (hM1 : Om1 ≤ M) (hME : M < ggE)
    (hMT : rjDat M ∈ Tset ρ) (hσT : σ ∈ Tset ρ) (hσΩ : σ < Om1)
    (IH : ∀ u, u < vt ρ (Om1 * M + σ) → GnI ρ δ u) : GnI ρ δ (vt ρ (Om1 * M + σ)) := by
  have hρE := h.ρE
  have hρ1 := h.ρ1
  obtain ⟨-, -, -, hρv, -, hvE, -, -, -⟩ := rjK_facts hρS hρ1 hM1 hME hMT hσT hσΩ
  obtain ⟨hje, -⟩ := rjLevel_lt_vt hρE hρ1 hM1 hME hMT hσT hσΩ
  have hvL : vt ρ (Om1 * M + σ) = ω ^ vt ρ (Om1 * M + σ) := hvE.symm
  have hL : max (ρ + 1) (rjDat M + 1) < vt ρ (Om1 * M + σ) := by
    have hlim := ev_isSuccLimit_of_inE hvE
    exact max_lt (hlim.add_one_lt hρv) (hlim.add_one_lt hje)
  obtain ⟨E', hLE', hdE', hσE', hE'E, hJ⟩ := qc_LB hρE hρ1 hM1 hME hMT hσT hσΩ hL
  have hρE' : ρ < E' := (lt_add_one ρ).trans_le ((le_max_left _ _).trans hLE')
  have hdE'' : rjDat M < E' := (lt_add_one _).trans_le ((le_max_right _ _).trans hLE')
  exact qc_img_atom h hρS hM1 hME hMT hσT hσΩ hρE' hE'E hdE''
    (qc_sep hρE hρ1 hρS hM1 hME hMT hσT hσΩ hρE'.le hdE' hσE' hJ) IH

end Img

end Googology.Trans.PoR.InaccPsi.R2.Qc
