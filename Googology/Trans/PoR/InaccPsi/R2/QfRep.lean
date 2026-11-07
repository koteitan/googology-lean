import Googology.Trans.PoR.InaccPsi.R2.QfGap
import Googology.Trans.PoR.InaccPsi.R2.QcSep

/-!
# QfRep: THE SEPARATION AT A POINT OF A VEBLEN LEVEL

For `E = ϑˣ(Ω₁·M + σ)`, `ε_{Ω₁+1} ≤ M < Γ_{Ω₁+1}` (the port of `R2.QcSep` with the data `Tf.tfDat` and the reach code
`qfLam M`):

* `qf_lam_code` (**`qfLam M` is a code over every strongly critical `q` over which `M` is, and `Ω₁·M ≤ qfLam M`**);
* `qf_rep` (**every `ε`-number `a ∈ (x, E)` above the data of `M` and `σ` is of Veblen level, or a point `ϑˣ(Ω₁·M' +
  σ')` of a level `Ω₁ ≤ M' < Γ_{Ω₁+1}` with `(M', σ') < (M, σ)` lexicographically**: [W07a] Lemma 3.30 through
  `R2.tfLt_of_vt_lt`);
* `qf_LB` (**the lower bound `E'`**, as `Qc.qc_LB`);
* `qf_sep_lvl` (**THE SEPARATION**: a Veblen point has a reach below `a·a` (`Yw.ywLow`); a point of a level `M' <
  ε_{Ω₁+1}` has the reach `rjL(Θ_a(Ω₁·M')) + ζ' < Θ_a(qfLam M)` (`rjL(Ω₁·M') + Ω₁ < ε_{Ω₁+1} ≤ qfLam M`); a point of a
  Veblen level `M' < M` has the reach `Θ_a(qfLam M') + ζ'` with `qfLam M' + Ω₁ ≤ qfLam M` (`Qf.qf_lam_gap`); a point
  of the level `M` has `ζ' < ζ_E` by `E'`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qf

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rj Googology.Trans.PoR.InaccPsi.R2.Lu
  Googology.Trans.PoR.InaccPsi.R2.Yw Googology.Trans.PoR.InaccPsi.R2.Gn

/-- **`qfLam M` is a code over `q`** (when `M` is), and `Ω₁·M ≤ qfLam M`. -/
theorem qf_lam_code {q M : Ordinal.{0}} (hq : SC q) (hq1 : q < Om1) (hM1 : ggE ≤ M) (hMC : GgCl q M) :
    GgCl q (qfLam M) ∧ Om1 * M ≤ qfLam M := by
  classical
  have hO0 : (0 : Ordinal.{0}) < Om1 := rj_Om1_pos
  have hM0 : M ≠ 0 := (lt_of_lt_of_le (show InE ggE from ggE_spec.1).pos hM1).ne'
  have hL0 : Om1 * M ≠ 0 := mul_ne_zero hO0.ne' hM0
  have hLC : GgCl q (Om1 * M) := by rw [rj_Om1]; exact Rk.rk_cl_Om1_mul hq hMC
  obtain ⟨hsubL, hlC⟩ := ggDec hq _ hLC
  set l := qfL M with hldef
  have hlC' : GgCl q l := hlC
  have hDC : GgCl q (ω ^ l) := GgCl.opow hq.1 hlC'
  have hDL : ω ^ l ≤ Om1 * M := opow_log_le_self ω hL0
  have hrC : GgCl q (Om1 * M - ω ^ l) := hsubL _ hDC hDL
  have hEl : ggE ≤ l := by
    have h1 : ggE ≤ Om1 * M := hM1.trans (Ordinal.le_mul_right M hO0)
    have h2 := log_mono_right ω h1
    rwa [qf_log_eps ggE_spec.1] at h2
  have hl1 : Om 1 < l := ggE_spec.2.trans_le hEl
  have hHC : GgCl q (qfH l) := by
    unfold qfH
    split_ifs with hC hlE
    · obtain ⟨-, hcE, -, -⟩ := hC
      have hcC : GgCl q (ω ^ log ω l) := GgCl.opow hq.1 (ggDec hq l hlC').2
      have hlogE : ggE ≤ log ω l := by
        have h := log_mono_right ω hEl
        rwa [qf_log_eps ggE_spec.1] at h
      have hc1 : Om 1 < ω ^ log ω l :=
        ggE_spec.2.trans_le (hlogE.trans (right_le_opow _ one_lt_omega0))
      exact GgCl.add (qf_re hq hq1 hcC hc1 hcE).1 hDC
    · exact (qf_re hq hq1 hlC' hl1 hlE).1
    · exact GgCl.add hDC (Qc.qc_lg_code hq hlC')
  rw [qf_lam_head hM0]
  refine ⟨GgCl.add hHC hrC, ?_⟩
  calc Om1 * M = ω ^ l + (Om1 * M - ω ^ l) := (Ordinal.add_sub_cancel_of_le hDL).symm
    _ ≤ qfH l + (Om1 * M - ω ^ l) := add_le_add (qf_head_ge l) le_rfl

section Sep

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

/-- **The `ε`-numbers below a point of a level `Ω₁ ≤ M < Γ_{Ω₁+1}`** (above `x`, the data of `M` and `σ`). -/
theorem qf_rep {M σ a : Ordinal.{0}} (hM1 : Om1 ≤ M) (hMG : M < ggGam) (hMT : Tf.tfDat M ∈ Tset x)
    (hσT : σ ∈ Tset x) (hσΩ : σ < Om1) (haE : InE a) (hxa : x < a) (hda : Tf.tfDat M < a) (hσa : σ < a)
    (hae : a < vt x (Om1 * M + σ)) :
    (∃ q t, 1 ≤ q ∧ q ∈ Tset x ∧ q < Om1 ∧ t ∈ Tset x ∧ t < Om1 ∧ vt x (Om1 * q + t) = a) ∨
    (∃ M' σ', Om1 ≤ M' ∧ M' < ggGam ∧ Tf.tfDat M' ∈ Tset x ∧ σ' ∈ Tset x ∧ σ' < Om1 ∧
      vt x (Om1 * M' + σ') = a ∧ (M' < M ∨ (M' = M ∧ σ' < σ))) := by
  have hMB : M < Tf.tfBG := hMG.trans qf_gg_lt_BG
  have hargT := tfArg_mem hx hx1 hM1 hMB hMT hσT hσΩ
  obtain ⟨hET, -, hE1, -, -⟩ := vt_memTwo hx hx1 hargT (Qd.qd_arg_lt hMG hσΩ)
  have ha1 : a < Om1 := hae.trans hE1
  have haT : a ∈ Tset x := vz_T_down hx hx1 hET hE1 hae.le
  obtain ⟨ξ, hξT, hξ2, hξv⟩ := vt_rep hx hx1 haT hxa.le ha1 (inE_indec haE)
  have hΩξ : Om1 ≤ ξ := (vt_E_iff hx hx1 hξT hξ2).1 ⟨by rw [hξv]; exact hxa, by rw [hξv]; exact haE⟩
  have hξlt : ξ < Om1 * M + σ := tfLt_of_vt_lt hx hx1 hM1 hMB hξT hξ2 hMT hσT hσΩ (by rw [hξv]; exact hda)
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
    have hM'G : M' < ggGam := hM'M.trans_lt hMG
    have hM'T : Tf.tfDat M' ∈ Tset x :=
      tfArg_dat hx hx1 hM'Ω (hM'G.trans qf_gg_lt_BG) hr1 (by rw [hdec]; exact hξT)
    exact ⟨M', σ', hM'Ω, hM'G, hM'T, hrT, hr1, by rw [hdec, hξv], hlex⟩

/-- **The lower bound exists** (for every `L < E`). -/
theorem qf_LB {M σ L : Ordinal.{0}} (hM1 : Om1 ≤ M) (hMG : M < ggGam) (hMT : Tf.tfDat M ∈ Tset x)
    (hσT : σ ∈ Tset x) (hσΩ : σ < Om1) (hL : L < vt x (Om1 * M + σ)) :
    ∃ E', L ≤ E' ∧ Tf.tfDat M ≤ E' ∧ σ ≤ E' ∧ E' < vt x (Om1 * M + σ) ∧
      ∀ σ', σ' ∈ Tset x → σ' < σ → E' < vt x (Om1 * M + σ') →
        lqZeta x (Om1 * M) σ' < lqZeta x (Om1 * M) σ := by
  have hMB : M < Tf.tfBG := hMG.trans qf_gg_lt_BG
  obtain ⟨hje, hσe⟩ := tfLevel_lt hx hx1 hM1 hMB hMT hσT hσΩ
  have hlt_same : ∀ σ₀, σ₀ ∈ Tset x → σ₀ < σ → vt x (Om1 * M + σ₀) < vt x (Om1 * M + σ) := fun σ₀ hσ₀T hσ₀ =>
    tfVt_lt hx hx1 hM1 hMB le_rfl hMT hσ₀T (hσ₀.trans hσΩ) hMT hσT hσΩ ((add_lt_add_iff_left _).2 hσ₀) hje
      (hσ₀.trans hσe)
  have hle_same : ∀ σ₀ σ₁, σ₀ ∈ Tset x → σ₁ ∈ Tset x → σ₁ < Om1 → σ₀ ≤ σ₁ →
      vt x (Om1 * M + σ₀) ≤ vt x (Om1 * M + σ₁) := fun σ₀ σ₁ hσ₀T hσ₁T hσ₁Ω hle => by
    rcases hle.lt_or_eq with hlt | rfl
    · obtain ⟨hj1, hs1⟩ := tfLevel_lt hx hx1 hM1 hMB hMT hσ₁T hσ₁Ω
      exact (tfVt_lt hx hx1 hM1 hMB le_rfl hMT hσ₀T (hlt.trans hσ₁Ω) hMT hσ₁T hσ₁Ω
        ((add_lt_add_iff_left _).2 hlt) hj1 (hlt.trans hs1)).le
    · exact le_rfl
  by_cases hc : ∃ σ'', σ'' < σ ∧ σ < vt x (Om1 * M + σ'')
  · have hσ0 : σ ≠ 0 := by
      obtain ⟨σ'', h1, -⟩ := hc
      exact (lt_of_le_of_lt zero_le h1).ne'
    have hzσ : lqZeta x (Om1 * M) σ = lg σ := by unfold lqZeta; rw [if_pos hc]
    obtain ⟨σ0, hdec, hdvd, hσ0σ⟩ := lg_split hσ0
    have hσ0T : σ0 ∈ Tset x := vz_T_down hx hx1 hσT hσΩ hσ0σ.le
    have hP : vt x (Om1 * M + σ0) < vt x (Om1 * M + σ) := hlt_same σ0 hσ0T hσ0σ
    refine ⟨max (max L (Tf.tfDat M)) (max σ (vt x (Om1 * M + σ0))), (le_max_left _ _).trans (le_max_left _ _),
      (le_max_right _ _).trans (le_max_left _ _), (le_max_left _ _).trans (le_max_right _ _),
      max_lt (max_lt hL hje) (max_lt hσe hP), fun σ' hσ'T hσ'σ hE' => ?_⟩
    have hσ0σ' : σ0 < σ' := by
      by_contra hle
      push Not at hle
      have h1 := hle_same σ' σ0 hσ'T hσ0T (hσ0σ.trans hσΩ) hle
      have h2 : vt x (Om1 * M + σ0) ≤ max (max L (Tf.tfDat M)) (max σ (vt x (Om1 * M + σ0))) :=
        (le_max_right _ _).trans (le_max_right _ _)
      exact absurd (hE'.trans_le (h1.trans h2)) (lt_irrefl _)
    rw [hzσ]
    exact ywZeta_le_lg.trans_lt (Gc.gc_lg_lt hdec hdvd hσ0σ' hσ'σ)
  · push Not at hc
    refine ⟨max (max L (Tf.tfDat M)) σ, (le_max_left _ _).trans (le_max_left _ _),
      (le_max_right _ _).trans (le_max_left _ _), le_max_right _ _, max_lt (max_lt hL hje) hσe,
      fun σ' _ hσ'σ hE' => ?_⟩
    exact absurd (hE'.trans_le ((hc σ' hσ'σ).trans (le_max_right _ _))) (lt_irrefl _)

omit hx hx1 in
/-- `rjL(l) < ε_{Ω₁+1}` for `l < ε_{Ω₁+1}`. -/
theorem qf_rjL_lt_E {l : Ordinal.{0}} (hl : l < ggE) : rjL l < ggE := by
  have hgE : InE ggE := ggE_spec.1
  have hgI : Indec ggE := inE_indec hgE
  have hlogE : log ω l < ggE := (log_le_self ω _).trans_lt hl
  unfold rjL
  have h1 : ω ^ log ω l < ggE := hgE.opow_lt hlogE
  have h2 : lg (log ω l) < ggE := by
    rcases eq_or_ne (log ω l) 0 with h0 | h0
    · rw [h0, Qc.qc_lg_zero]; exact hgE.pos
    · exact (lg_le h0).trans_lt hlogE
  exact hgI.add_lt (hgI.add_lt h1 h2) ((Ordinal.sub_le_self _ _).trans_lt hl)

/-- **THE SEPARATION AT A POINT OF A VEBLEN LEVEL** (the hypothesis of the image lemma), for a strongly critical base
`x`. -/
theorem qf_sep_lvl (hxS : SC x) {M σ E' : Ordinal.{0}} (hM1 : ggE ≤ M) (hMG : M < ggGam)
    (hMT : Tf.tfDat M ∈ Tset x) (hσT : σ ∈ Tset x) (hσΩ : σ < Om1) (hxE' : x ≤ E') (hdE' : Tf.tfDat M ≤ E')
    (hσE' : σ ≤ E')
    (hJ : ∀ σ', σ' ∈ Tset x → σ' < σ → E' < vt x (Om1 * M + σ') →
      lqZeta x (Om1 * M) σ' < lqZeta x (Om1 * M) σ) :
    ∀ a, InE a → E' < a → a < vt x (Om1 * M + σ) →
      (SC a → ¬ le1R a (ggTh a (qfLam M) + lqZeta x (Om1 * M) σ)) ∧ (¬ SC a → ¬ le1R a (a * a)) := by
  intro a haE hE'a hae
  have hM1' : Om1 ≤ M := rj_Om1_lt_E.le.trans hM1
  have hO0 : (0 : Ordinal.{0}) < Om1 := rj_Om1_pos
  set z := lqZeta x (Om1 * M) σ with hz
  have hMB : M < Tf.tfBG := hMG.trans qf_gg_lt_BG
  have hEO : vt x (Om1 * M + σ) < Om1 :=
    (vt_memTwo hx hx1 (tfArg_mem hx hx1 hM1' hMB hMT hσT hσΩ) (Qd.qd_arg_lt hMG hσΩ)).2.2.1
  have ha1 : a < Om1 := hae.trans hEO
  have haM : ∀ (haS : SC a), GgCl a M := fun haS =>
    Ss.ss_code haS.1 M hMG (by rw [← Tf.tfDat_eq_ss M hMG]; exact hdE'.trans_lt hE'a)
  rcases qf_rep hx hx1 hM1' hMG hMT hσT hσΩ haE (hxE'.trans_lt hE'a) (hdE'.trans_lt hE'a) (hσE'.trans_lt hE'a)
      hae with ⟨q, t, hq1, hqT, hqΩ, htT, ht1, hv⟩ | ⟨M', σ', hM'1, hM'G, hM'T, hσ'T, hσ'Ω, hv, hcase⟩
  · -- a Veblen point: its reach is below `a·a`
    refine ⟨fun haS => ?_, fun _ => by rw [← hv]; exact ywLow hx hx1 hq1 hqT hqΩ htT ht1 le_rfl⟩
    obtain ⟨hLamC, hLamL⟩ := qf_lam_code haS ha1 hM1 (haM haS)
    have ha1' : a < Om 1 := by rw [← rj_Om1]; exact ha1
    have hsq : a * a ≤ ggTh a (qfLam M) := by
      have h1 : ggTh a (Om1 * Om1) = a * a := by
        rw [rj_Th_mul haS ha1 (by rw [rj_Om1]; exact GgCl.om), rj_Om1, ggTh_Om1 haS ha1']
      rw [← h1]
      exact ggTh_mono ((mul_le_mul_right hM1' _).trans hLamL)
    have hlow := ywLow hx hx1 hq1 hqT hqΩ htT ht1 (L := ggTh a (qfLam M) + z)
      (by rw [hv]; exact hsq.trans le_self_add)
    rwa [hv] at hlow
  · -- a point of a level `M' ≥ Ω₁`: strongly critical
    have haS : SC a := by rw [← hv]; exact qfK_SC hxS hx1 hM'1 hM'G hM'T hσ'T hσ'Ω
    refine ⟨fun _ hR => ?_, fun hnS => absurd haS hnS⟩
    have ha1' : a < Om 1 := by rw [← rj_Om1]; exact ha1
    obtain ⟨hLamC, hLamL⟩ := qf_lam_code haS ha1 hM1 (haM haS)
    obtain ⟨-, -, -, -, -, -, -, -, hσ'a⟩ := qfK_facts hxS hx1 hM'1 hM'G hM'T hσ'T hσ'Ω
    rw [hv] at hσ'a
    set ζ := lqZeta x (Om1 * M') σ' with hζ
    have hζa : ζ < a := (rj_zeta_le x (Om1 * M') σ').trans_lt hσ'a
    have hΩa : ggTh a (Om 1) = a := ggTh_Om1 haS ha1'
    have hM'C : GgCl a M' := by rw [← hv]; exact qf_code_of hxS hx1 hM'1 hM'G hM'T hσ'T hσ'Ω
    rcases lt_or_ge M' ggE with hM'E | hM'E
    · -- a level below `ε_{Ω₁+1}`
      have hM'Tr : rjDat M' ∈ Tset x := by rw [← Tf.tfDat_eq_rj M' hM'E]; exact hM'T
      obtain ⟨hL, -⟩ := rj_lh hxS hx1 hM'1 hM'E hM'Tr hσ'T hσ'Ω
      rw [hv] at hL
      have hle := hL.2 _ hR
      have hM'0 : Om1 * M' ≠ 0 := (mul_pos hO0 (hO0.trans_le hM'1)).ne'
      have hOM' : GgCl a (Om1 * M') := by rw [rj_Om1]; exact Rk.rk_cl_Om1_mul haS hM'C
      obtain ⟨hΛ'C, hΛ'th⟩ := Qc.qc_th_rjL haS hOM' hM'0
      rw [← hΛ'th] at hle
      have hΛ'E : rjL (Om1 * M') < ggE := by
        have hgE : InE ggE := ggE_spec.1
        exact qf_rjL_lt_E (hgE.mul_lt rj_Om1_lt_E hM'E)
      have hgap : rjL (Om1 * M') + Om 1 ≤ qfLam M := by
        have h1 : rjL (Om1 * M') + Om 1 < ggE :=
          (inE_indec ggE_spec.1).add_lt hΛ'E ggE_spec.2
        exact h1.le.trans (hM1.trans ((Ordinal.le_mul_right M hO0).trans hLamL))
      have h1 : ggTh a (rjL (Om1 * M')) + a ≤ ggTh a (qfLam M) := by
        have := ggTh_mono (y := a) hgap
        rwa [ggTh_add haS hΛ'C, hΩa] at this
      have h2 : ggTh a (rjL (Om1 * M')) + ζ < ggTh a (qfLam M) + z :=
        ((add_lt_add_iff_left _).2 hζa).trans_le (h1.trans le_self_add)
      exact absurd (hle.trans_lt h2) (lt_irrefl _)
    · -- a Veblen level
      obtain ⟨hLam'C, hL⟩ := qf_lh_lvl hxS hx1 hM'E hM'G hM'T hσ'T hσ'Ω
      rw [hv] at hLam'C hL
      have hle := hL.2 _ hR
      rcases hcase with hlt | ⟨rfl, hσσ⟩
      · have hgap := qf_lam_gap hM'E hlt hMG
        rw [rj_Om1] at hgap
        have h1 : ggTh a (qfLam M') + a ≤ ggTh a (qfLam M) := by
          have := ggTh_mono (y := a) hgap
          rwa [ggTh_add haS hLam'C, hΩa] at this
        have h2 : ggTh a (qfLam M') + ζ < ggTh a (qfLam M) + z :=
          ((add_lt_add_iff_left _).2 hζa).trans_le (h1.trans le_self_add)
        exact absurd (hle.trans_lt h2) (lt_irrefl _)
      · have hz' : ζ < z := hJ σ' hσ'T hσσ (by rw [hv]; exact hE'a)
        exact absurd (hle.trans_lt ((add_lt_add_iff_left _).2 hz')) (lt_irrefl _)

end Sep

end Googology.Trans.PoR.InaccPsi.R2.Qf
