import Googology.Trans.PoR.InaccPsi.R2.QdFxD

/-!
# QdTopB2: THE READINGS OF THE CODES BELOW `B₂` ARE COFINAL IN `ϑˣ(Ω₁·ε_{Ω₁+1})`, THE READING OF `B₂`

As `Qc.qs_fx_top` at the top `B₂ = H_{E₂}(0)` itself, with the readings `Qc.vQ` of `R2.QcAll` below it.  The supremum
`u` of the readings of the codes below `B₂` is closed (an atom `Γ(F + 1 + b) < B₂` reads above every `b(x)`,
`qd_B2_atomAbove`), so `u = ϑˣ(Ω₁·M' + σ')` with `M' = Ω₁ + J < ε_{Ω₁+1}` (`Qd.qd_rep`).  The tower levels
`γ_n = Ω₂, Ω₂^{Ω₂}, …` of `Qc.qcTw` read `Ω₁, Ω₁^{Ω₁}, …` (`qd_tw_read`), cofinal in `ε_{Ω₁+1}` (`qd_tw_cof`); so
`J < γ_n(x)` for some `n`, and a fixed point `H_{γ_n}(z) < B₂` with an index reading above `σ'` and the data of `J`
reads above `u` (`qd_B2_codeAbove`).

* `qd_tw_read0`, `qd_tw_read`, `qd_tw_cof` (**the tower level readings are cofinal in `ε_{Ω₁+1}`**), `qd_low_T`;
* `qd_B2_atomAbove`, `qd_B2_codeAbove`, `qd_B2_top` (**THE READINGS BELOW `B₂` ARE COFINAL IN ITS READING**).

No new axiom.  No new definition.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Googology.Trans.PoR.InaccPsi.R2.Qd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Yw
  Googology.Trans.PoR.InaccPsi.R2.Yh Googology.Trans.PoR.InaccPsi.R2.Va Googology.Trans.PoR.InaccPsi.R2.Tl
  Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Yr
  Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Trans.PoR.InaccPsi.R2.Zm Googology.Trans.PoR.InaccPsi.R2.Tf
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Rj Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Si Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Xk
  Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Lq Googology.Trans.PoR.InaccPsi.R2.Ge
  Googology.Trans.PoR.InaccPsi.R2.Qc

/-! ## The tower levels -/

section Tw

variable (f : Ordinal.{0} → Ordinal.{0}) (hf0 : f 0 = 0) (hf1 : f 1 = 1)
include hf0 hf1

theorem qd_tw_read0 : qcLv f (qcTw 0) = Om1 := by
  show qcLv f OmTwo = Om1
  have h := qcLv_cnf f (e := 1) (d := 1) (r := 0) le_rfl one_ne_zero uc_one_lt_Om2 (opow_pos _ uc_SC_Om2.1)
    (by rw [opow_one, mul_one, add_zero]; exact ucE_gt)
  rw [opow_one, mul_one, add_zero] at h
  rw [h, hf1, mul_one, qcLv_small f uc_one_lt_Om2, hf1, opow_one, qcLv_small f uc_SC_Om2.1, hf0, add_zero]

/-- **`Ω₂^{γ_n} ↦ Ω₁^{γ_n(x)}`.** -/
theorem qd_tw_read (n : ℕ) : qcLv f (qcTw (n + 1)) = Om1 ^ qcLv f (qcTw n) := by
  obtain ⟨-, hE, -⟩ := qcTw_facts (n + 1)
  obtain ⟨h1', -, -⟩ := qcTw_facts n
  show qcLv f (OmTwo ^ qcTw n) = _
  have h := qcLv_cnf f (e := qcTw n) (d := 1) (r := 0) h1' one_ne_zero uc_one_lt_Om2 (opow_pos _ uc_SC_Om2.1)
    (by rw [mul_one, add_zero]; exact hE)
  rw [mul_one, add_zero] at h
  rw [h, hf1, mul_one, qcLv_small f uc_SC_Om2.1, hf0, add_zero]

/-- **The tower level readings are cofinal in `ε_{Ω₁+1}`.** -/
theorem qd_tw_cof {J : Ordinal.{0}} (hJ : J < ggE) : ∃ n, J < qcLv f (qcTw n) := by
  have hO1E : ω ^ (Om1 : Ordinal.{0}) = Om1 := rj_Om1_opow
  have hωO : (ω : Ordinal.{0}) ≤ Om1 := omega0_le_of_isSuccLimit (ev_isSuccLimit_of_inE hO1E)
  have hge : ∀ n : ℕ, (fun a => ω ^ a)^[n] (Om1 + 1) ≤ qcLv f (qcTw (n + 1)) := by
    intro n
    induction n with
    | zero =>
      show Om1 + 1 ≤ qcLv f (qcTw (0 + 1))
      rw [qd_tw_read f hf0 hf1 0, qd_tw_read0 f hf0 hf1]
      have h1 : Om1 + 1 ≤ Om1 * Om1 :=
        calc Om1 + 1 ≤ Om1 + Om1 := add_le_add le_rfl (lu_one_lt_E hO1E).le
          _ = Om1 * (1 + 1) := by rw [mul_add, mul_one]
          _ ≤ Om1 * Om1 := mul_le_mul_right (Order.add_one_le_of_lt (lu_one_lt_E hO1E)) _
      calc Om1 + 1 ≤ ω ^ (Om1 + 1) := right_le_opow _ one_lt_omega0
        _ ≤ ω ^ (Om1 * Om1) := opow_le_opow_right omega0_pos h1
        _ = Om1 ^ Om1 := by rw [opow_mul, hO1E]
    | succ n ih =>
      rw [Function.iterate_succ_apply', qd_tw_read f hf0 hf1 (n + 1)]
      calc ω ^ ((fun a => ω ^ a)^[n] (Om1 + 1)) ≤ ω ^ qcLv f (qcTw (n + 1)) := opow_le_opow_right omega0_pos ih
        _ ≤ Om1 ^ qcLv f (qcTw (n + 1)) := opow_le_opow_left _ hωO
  have hfix : ω ^ nfp (fun a => ω ^ a) (Om1 + 1) = nfp (fun a => ω ^ a) (Om1 + 1) :=
    nfp_fp (isNormal_opow one_lt_omega0) _
  have hle : ggE ≤ nfp (fun a => ω ^ a) (Om1 + 1) :=
    ggE_le hfix (by rw [← rj_Om1]; exact (lt_add_one _).trans_le (le_nfp _ _))
  obtain ⟨n, hn⟩ := lt_nfp_iff.1 (hJ.trans_le hle)
  exact ⟨n + 1, hn.trans_le (hge n)⟩

end Tw

variable (S : InaccSeq.{0})

include S in
/-- The readings below `B₂` are in `Tˣ ∩ Ω₁`. -/
theorem qd_low_T {x c : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hc : c < ucB) (hg : qcG c < x) :
    vQ c x ∈ Tset x ∧ vQ c x < Om1 := by
  have h := qdBd_of_qc (qd_low_bd S hx hx1 hc hg)
  exact ⟨qdBd_T hx hx1 h, qdBd_lt hx hx1 h⟩

section Top

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include S hx hx1

/-- **Above the reading of a code `b < B₂` is the reading of an atom `Γ(F + 1 + b) < B₂`.** -/
theorem qd_B2_atomAbove {b : Ordinal.{0}} (hb : b < ucB) (hgb : qcG b < x) :
    ∃ a, a < ucB ∧ qcG a < x ∧ gq (vQ b x) x ≤ vQ a x := by
  have hωx : ω < x := omega0_lt_inE hx
  have hxP : ∀ u v, u < x → v < x → u + v < x := fun u v hu hv => (inE_indec hx).add_lt hu hv
  have hgE : gcG ucB = ucB := vs_gcG_fix (qd_B2_fix S).2.2 ucB_gt
  have hE : InE (ucB : Ordinal.{0}) := qd_B2_E
  obtain ⟨hbT, hb1⟩ := qd_low_T S hx hx1 hb hgb
  by_cases hbB : tfBG ≤ b
  · have hFb : vaFB b ≤ b := vs_FB_le hbB
    have hFfix := vs_FB_fix hbB
    have hOF := vs_FB_gt hbB
    have hseg : vaFB (vaFB b + 1 + b) = vaFB b := by
      refine vs_FB_eq hFfix hOF (le_self_add.trans le_self_add) fun y' h1 h2 hy' => ?_
      rcases le_or_gt y' b with hyb | hyb
      · exact absurd (vs_FB_max hbB hy' (hOF.trans h1) hyb) (not_le.2 h1)
      · have hyE : InE y' := zm_fix_E (zm_fix_of_gamma hy')
        have h3 : vaFB b + 1 + b < y' :=
          (inE_indec hyE).add_lt ((inE_indec hyE).add_lt (hFb.trans_lt hyb) (lu_one_lt_E hyE)) hyb
        exact absurd h2 (not_le.2 h3)
    have hBj : tfBG ≤ vaFB b + 1 + b := hbB.trans le_add_self
    have hj : vaFB (vaFB b + 1 + b) < vaFB b + 1 + b := by rw [hseg]; exact (lt_add_one _).trans_le le_self_add
    have hjE : vaFB b + 1 + b < ucB :=
      (inE_indec hE).add_lt ((inE_indec hE).add_lt (hFb.trans_lt hb) (lu_one_lt_E hE)) hb
    have hj' : Om1 + 1 + (vaFB b + 1 + b) = vaFB b + 1 + b := by
      obtain ⟨d, hd⟩ := exists_add_of_le hBj
      rw [hd, ← add_assoc, gl_absorb (Low.opow_eq_self_of_SC tfBG_SC) tfBG_gt]
    have hjlt : vaFB b + 1 + b < gcG (vaFB b + 1 + b) := by
      rw [tf_gcG, hj']
      exact lt_of_le_of_ne isNormal_gamma.strictMono.le_apply fun h => vs_FB_nfx hBj hj le_rfl h.symm
    have hgF : qcG (vaFB b) < x := (qc_FB_gate' hbB hb).trans_lt (max_lt hωx hgb)
    have h1g : qcG (1 : Ordinal.{0}) < x := by
      rw [show (1 : Ordinal.{0}) = ((1 : ℕ) : Ordinal.{0}) by norm_num, qcG_nat]
      exact (natCast_lt_omega0 1).trans hωx
    have hgj : qcG (vaFB b + 1 + b) < x :=
      qc_add hxP hωx _ _ hjE (qc_add hxP hωx _ _ (le_self_add.trans_lt hjE) hgF h1g) hgb
    have haE : gcG (vaFB b + 1 + b) < ucB := (gcG_lt hjE).trans_eq hgE
    refine ⟨gcG (vaFB b + 1 + b), haE, by rw [qcG_atom' hjlt haE]; exact (qcQ_le _).trans_lt hgj, ?_⟩
    rw [vQ_atom' hjlt haE, qc_vI hBj hj le_rfl, hseg, Ordinal.add_sub_cancel]
    obtain ⟨hFT, hF1⟩ := qd_low_T S hx hx1 (hFb.trans_lt hb) hgF
    exact gmq_mono hx hx1 (vzT_add hx hx1 hFT hbT) ((inE_indec gl_Om1_E).add_lt hF1 hb1) le_add_self
  · have hbB' : b < tfBG := not_le.1 hbB
    have hbg : b < gcG b := by rw [tf_gcG]; exact tf_lt_gamma_shift hbB'
    have haE : gcG b < ucB := (gcG_lt hb).trans_eq hgE
    refine ⟨gcG b, haE, by rw [qcG_atom' hbg haE]; exact (qcQ_le _).trans_lt hgb, ?_⟩
    rw [vQ_atom' hbg haE, qcI_noFix (not_lt.2 hbB'.le)]

/-- **Above the reading of a code `b < B₂`, a fixed point `H_{γ_n}(z) < B₂` of a tower level** reads
`ϑˣ(Ω₁·(Ω₁+γ_n(x)) + η)` with `b(x) ≤ η`. -/
theorem qd_B2_codeAbove (n : ℕ) {b : Ordinal.{0}} (hb : b < ucB) (hgb : qcG b < x) :
    ∃ a η, a < ucB ∧ qcG a < x ∧
      vQ a x = vt x (Om1 * (Om1 + qcLv (fun d => if d < ucB then vQ d x else 0) (qcTw n)) + η) ∧
      vQ b x ≤ η ∧ η ∈ Tset x ∧ η < Om1 := by
  have hωx : ω < x := omega0_lt_inE hx
  have hxP : ∀ u v, u < x → v < x → u + v < x := fun u v hu hv => (inE_indec hx).add_lt hu hv
  have hxl : IsSuccLimit x := ev_isSuccLimit_of_inE hx
  have hE : InE (ucB : Ordinal.{0}) := qd_B2_E
  have hEl : IsSuccLimit (ucB : Ordinal.{0}) := ev_isSuccLimit_of_inE hE
  obtain ⟨h1, hμE, hcd⟩ := qcTw_facts n
  set μ := qcTw n with hμdef
  have hμ0 : μ ≠ 0 := one_le_iff_ne_zero.1 h1
  have hc1 : ∀ d ∈ ucComps μ, d < ucB := fun d hd => (hcd d hd).trans_lt qd_one_lt_B2
  have hCμ : ucC μ < ucB := (ucC_lt_iff hE.pos μ).2 hc1
  have hEμ : ucH μ ucB = ucB := ucB_spec hμE hCμ
  obtain ⟨hbT, hb1⟩ := qd_low_T S hx hx1 hb hgb
  have hgcomp : ∀ d ∈ ucComps μ, qcG d < x := fun d hd => by
    rcases (hcd d hd).lt_or_eq with h | h
    · rw [Order.lt_one_iff.1 h, qcG_zero]; exact hx.pos
    · rw [h, show (1 : Ordinal.{0}) = ((1 : ℕ) : Ordinal.{0}) by norm_num, qcG_nat]
      exact (natCast_lt_omega0 1).trans hωx
  -- the reading of `H_μ(z)` for `z < B₂`, `z < H_μ(z)`
  have hrd : ∀ z, z < ucB → z < ucH μ z →
      vQ (ucH μ z) x = vt x (Om1 * (Om1 + qcLv (fun d => if d < ucB then vQ d x else 0) μ) + qcK μ z x) := by
    intro z hzE hzr
    have haE : ucH μ z < ucB := by rw [← hEμ]; exact (ucH_lt_iff μ).2 hzE
    obtain ⟨hl', hi'⟩ := ucLev_H hμE hzr
    obtain ⟨-, hJ⟩ := qc_H_fixG (y := z) hμ0
    have hA' : YhAt (ucH μ z) := ⟨ucH_SC μ z, ucH_gt μ z⟩
    have hi'' : ¬ yhJ (ucH μ z) < ucH μ z := by rw [hJ]; exact lt_irrefl _
    have hlv : qcLvx (ucH μ z) μ x = qcLv (fun d => if d < ucB then vQ d x else 0) μ := by
      unfold qcLvx
      refine qcLv_congr _ fun d hd => ?_
      have hda : d < ucH μ z := (le_ucC hd).trans_lt (ucH_C_lt μ z)
      simp only [if_pos hda, if_pos (hc1 d hd)]
    rw [qs_fixRd hA' hi'' haE x, hl', hi', hlv]
  by_cases hex : ∃ f, ucH μ f = f ∧ Om1 < f ∧ f ≤ b
  · -- `z = f₀ + 1 + b`, `f₀` the largest fixed point of `H_μ` in `(Ω₁, b]`
    obtain ⟨hf₀S, hOf₀, hf₀b⟩ := qc_mx_SC hex
    have hf₀ := qc_fpH_closed μ b hex
    have hgf₀ : qcG (vsMx (fun f => ucH μ f = f) b) < x :=
      (qc_mx_gate hμ0 b hb hex).trans_lt (max_lt hωx hgb)
    set f₀ := vsMx (fun f => ucH μ f = f) b with hf₀def
    have hzf : f₀ < f₀ + 1 + b := (lt_add_one _).trans_le le_self_add
    have hbig : ∀ f', ucH μ f' = f' → b < f' → f₀ + 1 + b < f' := fun f' hf' hbf' => by
      have hE' : InE f' := Low.opow_eq_self_of_SC (by rw [← hf']; exact ucH_SC μ f')
      exact (inE_indec hE').add_lt ((inE_indec hE').add_lt (hf₀b.trans_lt hbf') (lu_one_lt_E hE')) hbf'
    have hzr : f₀ + 1 + b < ucH μ (f₀ + 1 + b) := by
      refine lt_of_le_of_ne (ucH_le_self μ _) fun h => ?_
      rcases le_or_gt (f₀ + 1 + b) b with hzb | hzb
      · exact absurd (vs_mx_ge (fun f => ucH μ f = f) h.symm (hOf₀.trans hzf) hzb) (not_le.2 hzf)
      · exact lt_irrefl _ (hbig _ h.symm hzb)
    have hne : ucH μ (f₀ + 1 + b) ≠ f₀ + 1 + b := ne_of_gt hzr
    have hFz : QcFixH μ (f₀ + 1 + b) := ⟨f₀, hf₀, hzf⟩
    have hpz : qcFpH μ (f₀ + 1 + b) = f₀ := by
      rw [qc_fpH_eq hne]
      exact (vs_mx_eq (fun f => ucH μ f = f) le_add_self fun f hf _ hfz => by
        by_contra h; push Not at h; exact absurd hfz (not_le.2 (hbig f hf h))).symm
    have hzE : f₀ + 1 + b < ucB :=
      (inE_indec hE).add_lt ((inE_indec hE).add_lt (hf₀b.trans_lt hb) (lu_one_lt_E hE)) hb
    have haE : ucH μ (f₀ + 1 + b) < ucB := by rw [← hEμ]; exact (ucH_lt_iff μ).2 hzE
    have h1g : qcG (1 : Ordinal.{0}) < x := by
      rw [show (1 : Ordinal.{0}) = ((1 : ℕ) : Ordinal.{0}) by norm_num, qcG_nat]
      exact (natCast_lt_omega0 1).trans hωx
    have hgz : qcG (f₀ + 1 + b) < x :=
      qc_add hxP hωx _ _ hzE (qc_add hxP hωx _ _ (le_self_add.trans_lt hzE) hgf₀ h1g) hgb
    have hK : qcK μ (f₀ + 1 + b) x = vQ f₀ x + vQ b x := by
      unfold qcK; rw [if_pos hFz, hpz, Ordinal.add_sub_cancel]
    obtain ⟨hf₀T, hf₀1⟩ := qd_low_T S hx hx1 (hf₀b.trans_lt hb) hgf₀
    exact ⟨ucH μ (f₀ + 1 + b), vQ f₀ x + vQ b x, haE, qc_H_gate hx hμ0 hμE hzr haE hgcomp hgz,
      by rw [hrd _ hzE hzr, hK], le_add_self, vzT_add hx hx1 hf₀T hbT, (inE_indec gl_Om1_E).add_lt hf₀1 hb1⟩
  · -- `z = b + 1`: no fixed point of `H_μ` below `z`
    have hnF : ¬ QcFixH μ (b + 1) := by
      rintro ⟨f, hf, hfz⟩
      have hOf : Om1 < f := by rw [← hf]; exact ucH_gt μ f
      exact hex ⟨f, hf, hOf, Order.lt_add_one_iff.1 hfz⟩
    have hzr : b + 1 < ucH μ (b + 1) := by
      refine lt_of_le_of_ne (ucH_le_self μ _) fun h => ?_
      have hl := ev_isSuccLimit_of_inE (Low.opow_eq_self_of_SC (ucH_SC μ (b + 1)))
      rw [← h] at hl
      have h' : IsSuccLimit (Order.succ b) := by rw [Order.succ_eq_add_one]; exact hl
      exact Order.not_isSuccLimit_succ _ h'
    have hzE : b + 1 < ucB := hEl.add_one_lt hb
    have haE : ucH μ (b + 1) < ucB := by rw [← hEμ]; exact (ucH_lt_iff μ).2 hzE
    have hK : qcK μ (b + 1) x = vQ b x + 1 := by unfold qcK; rw [if_neg hnF, vQ_succ]
    obtain ⟨hsT, hs1⟩ := gl_T_succ hx hx1 hbT hb1
    exact ⟨ucH μ (b + 1), vQ b x + 1, haE, qc_H_gate hx hμ0 hμE hzr haE hgcomp (qcG_succ hxl b hgb),
      by rw [hrd _ hzE hzr, hK], le_self_add, hsT, hs1⟩

/-- **THE READINGS OF THE CODES BELOW `B₂` ARE COFINAL IN ITS READING `ϑˣ(Ω₁·ε_{Ω₁+1})`.** -/
theorem qd_B2_top : ∀ ν, ν < vt x (Om1 * ggE) → ∃ b, b < ucB ∧ qcG b < x ∧ ν ≤ vQ b x := by
  have hωx : ω < x := omega0_lt_inE hx
  have hxl : IsSuccLimit x := ev_isSuccLimit_of_inE hx
  have hE : InE (ucB : Ordinal.{0}) := qd_B2_E
  have hEl : IsSuccLimit (ucB : Ordinal.{0}) := ev_isSuccLimit_of_inE hE
  have hOE : Om1 < ggE := by rw [rj_Om1]; exact ggE_spec.2
  have hEG : (ggE : Ordinal.{0}) < ggGam := qd_gE_lt_gg
  have h0T : (0 : Ordinal.{0}) ∈ Tset x := mem_T_of_le hx hx1 zero_le
  have h0Ω : (0 : Ordinal.{0}) < Om1 := hx.pos.trans hx1
  have hdE : tfDat ggE ∈ Tset x := by rw [tfDat_E]; exact mem_T_of_le hx hx1 (lu_one_lt_E hx).le
  have hargT := tfArg_mem hx hx1 hOE.le (hEG.trans tf_gg_lt_BG) hdE h0T h0Ω
  obtain ⟨hVT, -, hV1, -, -⟩ := vt_memTwo hx hx1 hargT (qd_arg_lt hEG h0Ω)
  rw [add_zero] at hVT hV1
  intro ν hν
  by_contra hcon
  push Not at hcon
  set St : Set Ordinal.{0} := {s | ∃ b, b < ucB ∧ qcG b < x ∧ s = vQ b x} with hStdef
  have hSne : St.Nonempty := ⟨vQ 0 x, 0, hE.pos, by rw [qcG_zero]; exact hx.pos, rfl⟩
  have hSbdd : BddAbove St := ⟨ν, fun s ⟨b, hb, hg, hs⟩ => hs ▸ (hcon b hb hg).le⟩
  set u := sSup St with hudef
  have hu1 : ∀ b, b < ucB → qcG b < x → vQ b x < u := by
    intro b hb hg
    have h1 : vQ (b + 1) x ≤ u := le_csSup hSbdd ⟨b + 1, hEl.add_one_lt hb, qcG_succ hxl b hg, rfl⟩
    rw [vQ_succ] at h1
    exact (lt_add_one _).trans_le h1
  have hu2 : u ≤ ν := csSup_le hSne fun s ⟨b, hb, hg, hs⟩ => hs ▸ (hcon b hb hg).le
  have hcof : ∀ ζ, ζ < u → ∃ b, b < ucB ∧ qcG b < x ∧ ζ < vQ b x := fun ζ hζ => by
    obtain ⟨s, ⟨b, hb, hgb, rfl⟩, hζb⟩ := exists_lt_of_lt_csSup hSne hζ
    exact ⟨b, hb, hgb, hζb⟩
  -- `x < u`
  have hBGX : tfBG < tlX := tl_BG_lt_X
  have hgB : qcG tfBG < x := by
    rw [qcG_low hBGX, yrG_base (Low.opow_eq_self_of_SC tfBG_SC) va_G_le_BG, va_QE_BG]; exact hx.pos
  have hDu : ywV 1 0 x < u := by
    have h := hu1 tfBG (hBGX.trans uc_X_lt_B) hgB; rwa [vQ_low hBGX, vR_BG] at h
  have hxu : x < u := (zmD_facts hx hx1).2.1.trans hDu
  have huV : u < vt x (Om1 * ggE) := hu2.trans_lt hν
  have huT : u ∈ Tset x := vz_T_down hx hx1 hVT hV1 huV.le
  have hu1' : u < Om1 := huV.trans hV1
  -- `u` is closed: above every reading is the reading of an atom
  have hucl : YwClosed x u := by
    intro σ hσT hσu
    obtain ⟨b, hb, hgb, hσb⟩ := hcof σ hσu
    obtain ⟨a, haE, hga, hra⟩ := qd_B2_atomAbove S hx hx1 hb hgb
    obtain ⟨hbT, hb1⟩ := qd_low_T S hx hx1 hb hgb
    exact ((gmq_lt hx hx1 hbT hb1 hσb).trans_le hra).trans (hu1 a haE hga)
  have huE : InE u := ywC_inE hx hx1 le_rfl huT hu1' hxu ((ywC_one_iff hx hx1).2 hucl)
  have hdu : tfDat ggE < u := by rw [tfDat_E]; exact (lu_one_lt_E hx).trans hxu
  rcases qd_rep hx hx1 hOE.le hEG hdE h0T h0Ω huE hxu hdu huE.pos (by rw [add_zero]; exact huV) with
    ⟨q, t, hq1, hqT, hqΩ, htT, htΩ, hqt⟩ | ⟨M', σ', hM'1, hM'G, hM'T, hσ'T, hσ'Ω, hM'v, hlex⟩
  · -- `u = ϑˣ(Ω₁·q + t)`, `q < Ω₁`: not closed
    obtain ⟨-, -, -, -, hqp, htp⟩ := glA_facts hx hx1 hq1 hqT hqΩ htT htΩ
    have hqu : q < u := by rw [← hqt]; exact hqp
    have htu : t < u := by rw [← hqt]; exact htp
    have hsT : max q t ∈ Tset x := vz_T_down hx hx1 huT hu1' (max_lt hqu htu).le
    have hs1 : max q t < Om1 := (max_lt hqu htu).trans hu1'
    have hcl' := hucl _ hsT (max_lt hqu htu)
    have hsG : max q t < vt x (Om1 * (Om1 * 1 + 0) + max q t) := by
      rw [mul_one, add_zero]; exact gmq_gt hx hx1 hsT hs1
    obtain ⟨h1T, h1Ω⟩ := yw_one hx hx1
    have harg : Om1 * (Om1 * 0 + q) + t < Om1 * (Om1 * 1 + 0) + max q t := by
      rw [mul_zero, zero_add, add_zero, mul_one]
      calc Om1 * q + t < Om1 * q + Om1 := (add_lt_add_iff_left _).2 htΩ
        _ = Om1 * (q + 1) := (mul_add_one _ _).symm
        _ ≤ Om1 * Om1 := mul_le_mul_right (Order.add_one_le_of_lt hqΩ) _
        _ ≤ _ := le_self_add
    have hlt := lqVt_lt hx hx1 h0T h0Ω hqT hqΩ htT htΩ le_rfl h1T h1Ω h0T h0Ω hsT hs1 harg
      (lt_of_le_of_lt zero_le hsG) ((le_max_left _ _).trans_lt hsG) ((le_max_right _ _).trans_lt hsG)
    rw [mul_zero, zero_add, hqt, mul_one, add_zero] at hlt
    exact absurd (hlt.trans hcl') (lt_irrefl _)
  -- `u = ϑˣ(Ω₁·M' + σ')`, `M' = Ω₁ + J < ε_{Ω₁+1}`
  have hM'E : M' < ggE := by
    rcases hlex with h | ⟨-, h⟩
    · exact h
    · exact absurd h (not_lt.2 zero_le)
  obtain ⟨hdM'u, hσ'u⟩ := tfLevel_lt hx hx1 hM'1 (hM'G.trans tf_gg_lt_BG) hM'T hσ'T hσ'Ω
  rw [hM'v] at hdM'u hσ'u
  obtain ⟨J, hJ⟩ := exists_add_of_le hM'1
  have hJ0 : J ≠ 0 := by
    intro h0
    rw [hJ, h0, add_zero] at hM'v
    have h := hucl σ' hσ'T hσ'u
    rw [← hM'v] at h
    exact lt_irrefl _ h
  have hJE : J < ggE := (le_add_self.trans_eq hJ.symm).trans_lt hM'E
  have hdM' : tfDat M' = rjDat J := by rw [tfDat_eq_rj M' hM'E, hJ, qc_rjDat_Om1_add' hJE]
  have hdatJ : rjDat J < u := by rw [← hdM']; exact hdM'u
  -- a tower level above `J`
  set fB : Ordinal.{0} → Ordinal.{0} := fun d => if d < ucB then vQ d x else 0 with hfBdef
  have hf0 : fB 0 = 0 := by simp only [hfBdef, if_pos hE.pos, vQ_zero]
  have hf1 : fB 1 = 1 := by simp only [hfBdef, if_pos qd_one_lt_B2, vQ_one]
  obtain ⟨n, hn⟩ := qd_tw_cof fB hf0 hf1 hJE
  obtain ⟨b, hb, hgb, hσb⟩ := hcof _ (max_lt hσ'u hdatJ)
  obtain ⟨a, η, haE, hga, hra, hbη, hηT, hη1⟩ := qd_B2_codeAbove S hx hx1 n hb hgb
  have hση : σ' < η := ((le_max_left _ _).trans_lt hσb).trans_le hbη
  have hdη : rjDat J < η := ((le_max_right _ _).trans_lt hσb).trans_le hbη
  -- the level facts of the tower level
  obtain ⟨-, hμE, hcd⟩ := qcTw_facts n
  have hD0 : (fun d : Ordinal.{0} => d ≤ 1) 0 := zero_le
  have hfΩ : ∀ d, (fun d : Ordinal.{0} => d ≤ 1) d → fB d < Om1 := fun d hd => by
    rcases hd.lt_or_eq with h | h
    · rw [Order.lt_one_iff.1 h, hf0]; exact h0Ω
    · rw [h, hf1]; exact (show (1 : Ordinal.{0}) < Om1 by rw [rj_Om1]; exact Nm.one_lt_Om1)
  have hfm : ∀ d d', (fun d : Ordinal.{0} => d ≤ 1) d → (fun d : Ordinal.{0} => d ≤ 1) d' → d < d' →
      fB d < fB d' := fun d d' hd hd' hdd => by
    have h0 : d = 0 := Order.lt_one_iff.1 (hdd.trans_le hd')
    have h1 : d' = 1 := le_antisymm hd' (Order.one_le_iff_pos.2 (h0 ▸ hdd))
    rw [h0, h1, hf0, hf1]; exact zero_lt_one
  obtain ⟨hLE, hLdat, -, -⟩ := qcLv_main fB (fun d => d ≤ 1) hf0 hD0 hfΩ hfm (qcTw n) hμE hcd
  have hfold : ucFold fB (qcTw n) < 1 + 1 := (ucFold_lt_iff fB (by norm_num) _).2 fun d hd => by
    rcases (hcd d hd).lt_or_eq with h | h
    · rw [Order.lt_one_iff.1 h, hf0]; norm_num
    · rw [h, hf1]; exact lt_add_one 1
  have hNμE : Om1 + qcLv fB (qcTw n) < ggE := (show InE ggE from ggE_spec.1).add_lt hOE hLE
  have hdat1 : rjDat (Om1 + qcLv fB (qcTw n)) < x := by
    rw [qc_rjDat_Om1_add' hLE]
    exact (hLdat.trans_lt hfold).trans_le (Order.add_one_le_of_lt (lu_one_lt_E hx))
  have hNμT : rjDat (Om1 + qcLv fB (qcTw n)) ∈ Tset x := mem_T_of_le hx hx1 hdat1.le
  have harg : Om1 * M' + σ' < Om1 * (Om1 + qcLv fB (qcTw n)) + η := by
    calc Om1 * M' + σ' < Om1 * M' + Om1 := (add_lt_add_iff_left _).2 hσ'Ω
      _ = Om1 * (M' + 1) := (mul_add_one _ _).symm
      _ ≤ Om1 * (Om1 + qcLv fB (qcTw n)) := mul_le_mul_right (Order.add_one_le_of_lt (by
          rw [hJ]; exact (add_lt_add_iff_left _).2 hn)) _
      _ ≤ _ := le_self_add
  obtain ⟨-, hηv⟩ := rjLevel_lt_vt hx hx1 le_self_add hNμE hNμT hηT hη1
  have hM'T' : rjDat M' ∈ Tset x := by rw [← tfDat_eq_rj M' hM'E]; exact hM'T
  have hlt := rjVt_lt hx hx1 hM'E hM'T' hσ'T hσ'Ω le_self_add hNμE hNμT hηT hη1 harg
    (by rw [← tfDat_eq_rj M' hM'E, hdM']; exact hdη.trans hηv) (hση.trans hηv)
  rw [hM'v, ← hra] at hlt
  exact absurd (hu1 a haE hga) (not_lt.2 hlt.le)

end Top

end Googology.Trans.PoR.InaccPsi.R2.Qd
