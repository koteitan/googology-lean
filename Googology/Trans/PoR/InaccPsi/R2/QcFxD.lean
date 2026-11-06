import Googology.Trans.PoR.InaccPsi.R2.QcCof

/-!
# QcFxD: THE READINGS OF THE CODES BELOW THE FIXED POINT `E = H_λ(y)` ARE COFINAL IN ITS READING

As `Va.vs_fx_atomAbove`, `Va.vs_fx_codeAbove`, `Va.vs_fx_top` from `X` on.  The supremum `u` of the readings of the
codes below `E` is closed (above every reading `b(x)` is the reading `gq(F(x) + b(x))` of the atom `Γ(F + 1 + b)`,
`qs_fx_atomAbove`), so `u = ϑˣ(Ω₁·M' + σ')` (`Qc.qc_rep`) with `M' = Ω₁ + J`, `J ≥ 1` (closedness), and either
`J < λ(x)` — a level `μ < λ` with `J ≤ μ(x)` (`Qc.qcLv_cof`) and a fixed point `H_μ(z) < E` reads above `u`
(`qs_fx_codeAbove`) — or `J = λ(x)`, `σ' < K(x)` — the largest fixed point `p < y` of `H_λ`, or `H_λ(z)` for a smaller
argument `z < y`, reads above `u`.

* `qc_H_gate` (**the gate of `H_μ(z)` from the gates of the components of `μ` and of `z`**);
* `qs_fx_atomAbove`, `qs_fx_codeAbove`, `qs_fx_top` (**the readings below `E` are cofinal in `qcA E x`**).

No new axiom.  No new definition.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Googology.Trans.PoR.InaccPsi.R2.Qc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Yw
  Googology.Trans.PoR.InaccPsi.R2.Yh Googology.Trans.PoR.InaccPsi.R2.Va Googology.Trans.PoR.InaccPsi.R2.Tl
  Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Yr
  Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Trans.PoR.InaccPsi.R2.Zm Googology.Trans.PoR.InaccPsi.R2.Tf
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Rj Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Si Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Xk
  Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Lq Googology.Trans.PoR.InaccPsi.R2.Ge

/-- **The gate of `H_μ(z)`** (`μ ≠ 0`, `z < H_μ(z) < B₂`) is below an `ε`-number `x` above the gates of the
components of `μ` and of `z`. -/
theorem qc_H_gate {μ z x : Ordinal.{0}} (hx : InE x) (hμ0 : μ ≠ 0) (hμE : μ < ucE) (hz : z < ucH μ z)
    (hB : ucH μ z < ucB) (hcomp : ∀ d ∈ ucComps μ, qcG d < x) (hgz : qcG z < x) : qcG (ucH μ z) < x := by
  have hωx : ω < x := omega0_lt_inE hx
  obtain ⟨hl, hi⟩ := ucLev_H hμE hz
  obtain ⟨-, hJ⟩ := qc_H_fixG (y := z) hμ0
  have hA : YhAt (ucH μ z) := ⟨ucH_SC μ z, ucH_gt μ z⟩
  have hi' : ¬ yhJ (ucH μ z) < ucH μ z := by rw [hJ]; exact lt_irrefl _
  have hE : InE (ucH μ z) := Low.opow_eq_self_of_SC (ucH_SC μ z)
  rcases lt_or_ge (ucH μ z) tlX with haX | haX
  · -- below `X`: `H_μ(z) = F_μ(y₀(μ) + z)`
    have hμ2 : μ < OmTwo := by
      by_contra h
      push Not at h
      have hmem : ucH μ z ∈ range (ucH OmTwo) := by
        rcases h.lt_or_eq with h' | h'
        · exact ⟨ucH μ z, ucG_fix_lower h' ⟨z, rfl⟩ (by rw [ucC_Om2]; exact lu_one_lt_E hE)⟩
        · rw [← h']; exact ⟨z, rfl⟩
      exact absurd (uc_X_le_H hmem) (not_le.2 haX)
    have hμc : μ < ucH μ z := by have h := ucH_C_lt μ z; rwa [ucC_small hμ2] at h
    have hμX : μ < tlX := hμc.trans haX
    have hS : ucS μ = glY0 μ := qc_ucS_low hμX
    have hF : ucH μ z = rhF μ (ucS μ + z) := ucH_eq_F hμ2 z
    have hSa : ucS μ < ucH μ z := ucS_lt (max_lt (ucH_gt μ z) hμc) (ucH_SC μ z)
    have hz'a : ucS μ + z < ucH μ z := (ucH_SC μ z).isPrincipal hSa hz
    rw [hF] at hz'a haX
    have hO : Om1 < rhF μ (ucS μ + z) := by rw [← hF]; exact ucH_gt μ z
    obtain ⟨-, hrg⟩ := vs_fx_rd (one_le_iff_ne_zero.2 hμ0) hz'a hO haX
    have hsub : ucS μ + z - glY0 μ = z := by rw [hS, Ordinal.add_sub_cancel]
    have hzX : z < tlX := (le_add_self.trans_lt hz'a).trans haX
    rw [hF, qcG_low haX, hrg, hsub]
    have hgμ : qcG μ < x := hcomp μ (by rw [ucComps_small hμ2]; exact mem_singleton _)
    rw [qcG_low hμX] at hgμ
    rw [qcG_low hzX] at hgz
    exact max_lt ((yrQ_le _).trans_lt hgμ) ((yrQ_le _).trans_lt hgz)
  · have hN : ucI (ucLev (ucH μ z)) (ucH μ z) < ucH μ z := by rw [hl, hi]; exact hz
    rw [qcG_base hE haX hB, qcQE_fix haX hB hA hi' hN, hl, hi]
    refine max_lt ((ucFold_lt_iff _ hx.pos μ).2 fun d hd => ?_) ?_
    · split_ifs with hdc
      · exact (qcQ_le d).trans_lt (hcomp d hd)
      · exact hx.pos
    · have hne : ucH μ z ≠ z := ne_of_gt hz
      unfold qcKQ
      split_ifs with hFz
      · obtain ⟨hpf, -, hpy⟩ := qc_fpH_mem hne hFz
        have hpSC : SC (qcFpH μ z) := by rw [← hpf]; exact ucH_SC _ _
        have hpE : InE (qcFpH μ z) := Low.opow_eq_self_of_SC hpSC
        have hzB : z < ucB := hz.trans hB
        have hgp := qc_fpH_gate hμ0 hzB hne hFz
        have hgo := qc_off_gate' hpE (gl_G0_le hpSC (by rw [← hpf]; exact ucH_gt _ _)) hzB hpy
        exact max_lt ((qcQ_le _).trans_lt (hgp.trans_lt (max_lt hωx hgz)))
          ((qcQ_le _).trans_lt (hgo.trans_lt (max_lt hωx hgz)))
      · exact (qcQ_le z).trans_lt hgz

section Fix

variable {E : Ordinal.{0}} (hE : InE E) (hBE : tfBG < E) (hEB : E < ucB) (hXE : tlX ≤ E)
  (hlim : ∀ e, InE e → e < E → eN e < E) (hIH : ∀ e, InE e → tfBG ≤ e → e < E → QsGood e)
  (hA : YhAt E) (hi : ¬ yhJ E < E)
  {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)

include hE hBE hEB hXE hlim hIH hA hi hx hx1

/-- **Above the reading of a code `b < E` is the reading of an atom `Γ(F + 1 + b) < E`**: `gq(b(x)) ≤ gq(F(x) + b(x))`
(`Γ(b)` below `B_Γ`). -/
theorem qs_fx_atomAbove {b : Ordinal.{0}} (hb : b < E) (hgb : qcG b < x) :
    ∃ a, a < E ∧ qcG a < x ∧ gq (vQ b x) x ≤ vQ a x := by
  have hωx : ω < x := omega0_lt_inE hx
  have hxP : ∀ u v, u < x → v < x → u + v < x := fun u v hu hv => (inE_indec hx).add_lt hu hv
  obtain ⟨hfixE, -⟩ := qs_fx_dat hEB hXE hA hi
  have hgE : gcG E = E := vs_gcG_fix hfixE hA.2
  obtain ⟨hbT, hb1, -⟩ := qs_T hE hBE hEB hlim hIH hx hx1 hb hgb
  by_cases hbB : tfBG ≤ b
  · have hFb : vaFB b ≤ b := vs_FB_le hbB
    have hFfix := vs_FB_fix hbB
    have hOF := vs_FB_gt hbB
    -- `F + 1 + b` lies in the segment of `F = vaFB b`
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
    have hjE : vaFB b + 1 + b < E :=
      (inE_indec hE).add_lt ((inE_indec hE).add_lt (hFb.trans_lt hb) (lu_one_lt_E hE)) hb
    have hj' : Om1 + 1 + (vaFB b + 1 + b) = vaFB b + 1 + b := by
      obtain ⟨d, hd⟩ := exists_add_of_le hBj
      rw [hd, ← add_assoc, gl_absorb (Low.opow_eq_self_of_SC tfBG_SC) tfBG_gt]
    have hjlt : vaFB b + 1 + b < gcG (vaFB b + 1 + b) := by
      rw [tf_gcG, hj']
      exact lt_of_le_of_ne isNormal_gamma.strictMono.le_apply fun h => vs_FB_nfx hBj hj le_rfl h.symm
    have hgF : qcG (vaFB b) < x := (qc_FB_gate' hbB (hb.trans hEB)).trans_lt (max_lt hωx hgb)
    have h1g : qcG (1 : Ordinal.{0}) < x := by
      rw [show (1 : Ordinal.{0}) = ((1 : ℕ) : Ordinal.{0}) by norm_num, qcG_nat]
      exact (natCast_lt_omega0 1).trans hωx
    have hjB : vaFB b + 1 + b < ucB := hjE.trans hEB
    have hgj : qcG (vaFB b + 1 + b) < x :=
      qc_add hxP hωx _ _ hjB (qc_add hxP hωx _ _ (le_self_add.trans_lt hjB) hgF h1g) hgb
    have haE : gcG (vaFB b + 1 + b) < E := (gcG_lt hjE).trans_eq hgE
    refine ⟨gcG (vaFB b + 1 + b), haE, by rw [qcG_atom' hjlt (haE.trans hEB)]; exact (qcQ_le _).trans_lt hgj, ?_⟩
    rw [vQ_atom' hjlt (haE.trans hEB), qc_vI hBj hj le_rfl, hseg, Ordinal.add_sub_cancel]
    obtain ⟨hFT, hF1, -⟩ := qs_T hE hBE hEB hlim hIH hx hx1 (hFb.trans_lt hb) hgF
    exact gmq_mono hx hx1 (vzT_add hx hx1 hFT hbT) ((inE_indec gl_Om1_E).add_lt hF1 hb1) le_add_self
  · have hbB' : b < tfBG := not_le.1 hbB
    have hbg : b < gcG b := by rw [tf_gcG]; exact tf_lt_gamma_shift hbB'
    have haE : gcG b < E := (gcG_lt hb).trans_eq hgE
    refine ⟨gcG b, haE, by rw [qcG_atom' hbg (haE.trans hEB)]; exact (qcQ_le _).trans_lt hgb, ?_⟩
    rw [vQ_atom' hbg (haE.trans hEB), qcI_noFix (not_lt.2 hbB'.le)]

/-- **Above the reading of a code `b < E`, a fixed point `H_μ(z) < E` of a lower level `μ < λ`** (components codes)
reads `ϑˣ(Ω₁·(Ω₁+μ(x)) + η)` with `b(x) ≤ η`. -/
theorem qs_fx_codeAbove {μ : Ordinal.{0}} (hμ0 : μ ≠ 0) (hμl : μ < ucLev E)
    (hcμ : ∀ d ∈ ucComps μ, d < E ∧ qcG d < x) {b : Ordinal.{0}} (hb : b < E) (hgb : qcG b < x) :
    ∃ a η, a < E ∧ qcG a < x ∧ vQ a x = vt x (Om1 * (Om1 + qcLvx E μ x) + η) ∧ vQ b x ≤ η ∧
      η ∈ Tset x ∧ η < Om1 := by
  have hωx : ω < x := omega0_lt_inE hx
  have hxP : ∀ u v, u < x → v < x → u + v < x := fun u v hu hv => (inE_indec hx).add_lt hu hv
  have hxl : IsSuccLimit x := ev_isSuccLimit_of_inE hx
  have hEl : IsSuccLimit E := ev_isSuccLimit_of_inE hE
  obtain ⟨-, -, hlE, -, -, -, -, -⟩ := qs_fx_dat hEB hXE hA hi
  have hμE : μ < ucE := hμl.trans hlE
  have hCμ : ucC μ < E := (ucC_lt_iff hE.pos μ).2 fun d hd => (hcμ d hd).1
  have hEμ : ucH μ E = E := by
    obtain ⟨-, -, -, hlow, -⟩ := ucLev_spec hA.1 hA.2 (uc_nf_of_lt hA.1 hA.2 hEB)
    exact hlow μ hμl hCμ
  obtain ⟨hbT, hb1, -⟩ := qs_T hE hBE hEB hlim hIH hx hx1 hb hgb
  have hgcomp : ∀ d ∈ ucComps μ, qcG d < x := fun d hd => (hcμ d hd).2
  -- the reading of `H_μ(z)` for `z < E`, `z < H_μ(z)`
  have hrd : ∀ z, z < E → z < ucH μ z →
      vQ (ucH μ z) x = vt x (Om1 * (Om1 + qcLvx E μ x) + qcK μ z x) := by
    intro z hzE hzr
    have haE : ucH μ z < E := by rw [← hEμ]; exact (ucH_lt_iff μ).2 hzE
    obtain ⟨hl', hi'⟩ := ucLev_H hμE hzr
    obtain ⟨-, hJ⟩ := qc_H_fixG (y := z) hμ0
    have hA' : YhAt (ucH μ z) := ⟨ucH_SC μ z, ucH_gt μ z⟩
    have hi'' : ¬ yhJ (ucH μ z) < ucH μ z := by rw [hJ]; exact lt_irrefl _
    have hlv : qcLvx (ucH μ z) μ x = qcLvx E μ x := by
      unfold qcLvx
      refine qcLv_congr _ fun d hd => ?_
      have hda : d < ucH μ z := (le_ucC hd).trans_lt (ucH_C_lt μ z)
      simp only [if_pos hda, if_pos (hcμ d hd).1]
    rw [qs_fixRd hA' hi'' (haE.trans hEB) x, hl', hi', hlv]
  by_cases hex : ∃ f, ucH μ f = f ∧ Om1 < f ∧ f ≤ b
  · -- `z = f₀ + 1 + b`, `f₀` the largest fixed point of `H_μ` in `(Ω₁, b]`
    obtain ⟨hf₀S, hOf₀, hf₀b⟩ := qc_mx_SC hex
    have hf₀ := qc_fpH_closed μ b hex
    have hgf₀ : qcG (vsMx (fun f => ucH μ f = f) b) < x :=
      (qc_mx_gate hμ0 b (hb.trans hEB) hex).trans_lt (max_lt hωx hgb)
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
    have hzE : f₀ + 1 + b < E :=
      (inE_indec hE).add_lt ((inE_indec hE).add_lt (hf₀b.trans_lt hb) (lu_one_lt_E hE)) hb
    have haE : ucH μ (f₀ + 1 + b) < E := by rw [← hEμ]; exact (ucH_lt_iff μ).2 hzE
    have h1g : qcG (1 : Ordinal.{0}) < x := by
      rw [show (1 : Ordinal.{0}) = ((1 : ℕ) : Ordinal.{0}) by norm_num, qcG_nat]
      exact (natCast_lt_omega0 1).trans hωx
    have hzB : f₀ + 1 + b < ucB := hzE.trans hEB
    have hgz : qcG (f₀ + 1 + b) < x :=
      qc_add hxP hωx _ _ hzB (qc_add hxP hωx _ _ (le_self_add.trans_lt hzB) hgf₀ h1g) hgb
    have hK : qcK μ (f₀ + 1 + b) x = vQ f₀ x + vQ b x := by
      unfold qcK; rw [if_pos hFz, hpz, Ordinal.add_sub_cancel]
    obtain ⟨hf₀T, hf₀1, -⟩ := qs_T hE hBE hEB hlim hIH hx hx1 (hf₀b.trans_lt hb) hgf₀
    refine ⟨ucH μ (f₀ + 1 + b), vQ f₀ x + vQ b x, haE,
      qc_H_gate hx hμ0 hμE hzr (haE.trans hEB) hgcomp hgz, by rw [hrd _ hzE hzr, hK], le_add_self,
      vzT_add hx hx1 hf₀T hbT, (inE_indec gl_Om1_E).add_lt hf₀1 hb1⟩
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
    have hzE : b + 1 < E := hEl.add_one_lt hb
    have haE : ucH μ (b + 1) < E := by rw [← hEμ]; exact (ucH_lt_iff μ).2 hzE
    have hK : qcK μ (b + 1) x = vQ b x + 1 := by unfold qcK; rw [if_neg hnF, vQ_succ]
    obtain ⟨hsT, hs1⟩ := gl_T_succ hx hx1 hbT hb1
    refine ⟨ucH μ (b + 1), vQ b x + 1, haE, qc_H_gate hx hμ0 hμE hzr (haE.trans hEB) hgcomp (qcG_succ hxl b hgb),
      by rw [hrd _ hzE hzr, hK], le_self_add, hsT, hs1⟩

/-- **The readings of the codes below the fixed point are cofinal in its reading.** -/
theorem qs_fx_top (hgx : max ω (qcQE E) < x) : ∀ ν, ν < qcA E x → ∃ b, b < E ∧ qcG b < x ∧ ν ≤ vQ b x := by
  have hωx : ω < x := omega0_lt_inE hx
  have hxl : IsSuccLimit x := ev_isSuccLimit_of_inE hx
  have hEl : IsSuccLimit E := ev_isSuccLimit_of_inE hE
  have hxP : ∀ u v, u < x → v < x → u + v < x := fun u v hu hv => (inE_indec hx).add_lt hu hv
  obtain ⟨-, hl0, hlE, -, hyE, hFy, hne, -⟩ := qs_fx_dat hEB hXE hA hi
  obtain ⟨hVeq, -, hVT, -, -, -, hV1⟩ := qs_fx_V hE hBE hEB hXE hlim hIH hA hi hx hx1 hgx
  obtain ⟨hcomp, -, hNE, hNT, hKT, hK1, -⟩ := qs_fx_parts hE hBE hEB hXE hlim hIH hA hi hx hx1 hgx
  obtain ⟨-, hgF, hg0y⟩ := qs_fix_gates hA hi hEB
  have hmono : ∀ b c, b < c → c < E → qcG b < x → qcG c < x → vQ b x < vQ c x := fun b c hbc hc hgb hgc =>
    qs_mono hE hBE hEB hlim hIH hx hx1 hbc hc hgb hgc
  have hcode : ∀ c, c < E → qcG c < x → vQ c x ∈ Tset x ∧ vQ c x < Om1 := fun c hc hgc =>
    ⟨(qs_T hE hBE hEB hlim hIH hx hx1 hc hgc).1, (qs_T hE hBE hEB hlim hIH hx hx1 hc hgc).2.1⟩
  obtain ⟨-, -, -, -, hdatle, -, -⟩ := qs_fix_lev_u hx hx1 hA hi hEB hgx hcode hmono
  have h1g : qcG (1 : Ordinal.{0}) < x := by
    rw [show (1 : Ordinal.{0}) = ((1 : ℕ) : Ordinal.{0}) by norm_num, qcG_nat]
    exact (natCast_lt_omega0 1).trans hωx
  have hO1N : Om1 ≤ Om1 + qcLvx E (ucLev E) x := le_self_add
  -- the components read by `fE`
  set fE : Ordinal.{0} → Ordinal.{0} := fun d => if d < E then vQ d x else 0 with hfEdef
  have hE0 : (0 : Ordinal.{0}) < E := hE.pos
  have hf0 : fE 0 = 0 := by simp only [hfEdef, if_pos hE0, vQ_zero]
  have hD0 : (fun d => d < E ∧ qcG d < x) 0 := ⟨hE0, by rw [qcG_zero]; exact hx.pos⟩
  have hfΩ : ∀ d, (fun d => d < E ∧ qcG d < x) d → fE d < Om1 := fun d hd => by
    simp only [hfEdef, if_pos hd.1]; exact (hcode d hd.1 hd.2).2
  have hfm : ∀ d d', (fun d => d < E ∧ qcG d < x) d → (fun d => d < E ∧ qcG d < x) d' → d < d' →
      fE d < fE d' := fun d d' hd hd' hdd => by
    simp only [hfEdef, if_pos hd.1, if_pos hd'.1]; exact hmono d d' hdd hd'.1 hd.2 hd'.2
  have hDm2 : ∀ d, (fun d => d < E ∧ qcG d < x) d → d < OmTwo := fun d hd => (hd.1.trans hEB).trans ucB_lt_Om2
  have hbelow : ∀ d, (fun d => d < E ∧ qcG d < x) d → ∀ ν, ν < fE d →
      ∃ d', d' < d ∧ (fun d => d < E ∧ qcG d < x) d' ∧ ν ≤ fE d' := by
    intro d hd ν hν
    simp only [hfEdef, if_pos hd.1] at hν
    rcases eq_or_ne d 0 with rfl | hd0
    · rw [vQ_zero] at hν; exact absurd hν (not_lt.2 zero_le)
    obtain ⟨d', hd'd, hgd', hνd'⟩ := qs_below hE hBE hEB hlim hIH hx hx1 hd.1 hd0 hd.2 ν hν
    exact ⟨d', hd'd, ⟨hd'd.trans hd.1, hgd'⟩, by simp only [hfEdef, if_pos (hd'd.trans hd.1)]; exact hνd'⟩
  -- the readings of `H_λ(z)` for `z < y`
  have hrdE : ∀ z, z < ucI (ucLev E) E → z < ucH (ucLev E) z →
      ucH (ucLev E) z < E ∧ vQ (ucH (ucLev E) z) x =
        vt x (Om1 * (Om1 + qcLvx E (ucLev E) x) + qcK (ucLev E) z x) := by
    intro z hzy hzr
    have haE : ucH (ucLev E) z < E := ((ucH_lt_iff _).2 hzy).trans_eq hFy
    obtain ⟨hl', hi'⟩ := ucLev_H hlE hzr
    obtain ⟨-, hJ⟩ := qc_H_fixG (y := z) hl0
    have hA' : YhAt (ucH (ucLev E) z) := ⟨ucH_SC _ z, ucH_gt _ z⟩
    have hi'' : ¬ yhJ (ucH (ucLev E) z) < ucH (ucLev E) z := by rw [hJ]; exact lt_irrefl _
    have hlv : qcLvx (ucH (ucLev E) z) (ucLev E) x = qcLvx E (ucLev E) x := by
      unfold qcLvx
      refine qcLv_congr _ fun d hd => ?_
      have hda : d < ucH (ucLev E) z := (le_ucC hd).trans_lt (ucH_C_lt _ z)
      simp only [if_pos hda, if_pos (hcomp d hd).1]
    refine ⟨haE, ?_⟩
    rw [qs_fixRd hA' hi'' (haE.trans hEB) x, hl', hi', hlv]
  intro ν hν
  by_contra hcon
  push Not at hcon
  set S : Set Ordinal.{0} := {s | ∃ b, b < E ∧ qcG b < x ∧ s = vQ b x} with hSdef
  have hSne : S.Nonempty := ⟨vQ 0 x, 0, hE.pos, by rw [qcG_zero]; exact hx.pos, rfl⟩
  have hSbdd : BddAbove S := ⟨ν, fun s ⟨b, hb, hg, hs⟩ => hs ▸ (hcon b hb hg).le⟩
  set u := sSup S with hudef
  have hu1 : ∀ b, b < E → qcG b < x → vQ b x < u := by
    intro b hb hg
    have h1 : vQ (b + 1) x ≤ u := le_csSup hSbdd ⟨b + 1, hEl.add_one_lt hb, qcG_succ hxl b hg, rfl⟩
    rw [vQ_succ] at h1
    exact (lt_add_one _).trans_le h1
  have hu2 : u ≤ ν := csSup_le hSne fun s ⟨b, hb, hg, hs⟩ => hs ▸ (hcon b hb hg).le
  have hcof : ∀ ζ, ζ < u → ∃ b, b < E ∧ qcG b < x ∧ ζ < vQ b x := fun ζ hζ => by
    obtain ⟨s, ⟨b, hb, hgb, rfl⟩, hζb⟩ := exists_lt_of_lt_csSup hSne hζ
    exact ⟨b, hb, hgb, hζb⟩
  have hU : ∀ ζ, ζ < u → ∃ d, (fun d => d < E ∧ qcG d < x) d ∧ ζ ≤ fE d := fun ζ hζ => by
    obtain ⟨b, hb, hgb, hζb⟩ := hcof ζ hζ
    exact ⟨b, ⟨hb, hgb⟩, by simp only [hfEdef, if_pos hb]; exact hζb.le⟩
  -- `x < u`
  have hBGX : tfBG < tlX := tl_BG_lt_X
  have hgB : qcG tfBG < x := by
    rw [qcG_low hBGX, yrG_base (Low.opow_eq_self_of_SC tfBG_SC) va_G_le_BG, va_QE_BG]; exact hx.pos
  have hDu : ywV 1 0 x < u := by
    have h := hu1 tfBG hBE hgB; rwa [vQ_low hBGX, vR_BG] at h
  have hxu : x < u := (zmD_facts hx hx1).2.1.trans hDu
  have huV : u < qcA E x := hu2.trans_lt hν
  have huT : u ∈ Tset x := vz_T_down hx hx1 hVT hV1 huV.le
  have hu1' : u < Om1 := huV.trans hV1
  -- `u` is closed: above every reading is the reading of an atom
  have hucl : YwClosed x u := by
    intro σ hσT hσu
    obtain ⟨b, hb, hgb, hσb⟩ := hcof σ hσu
    obtain ⟨a, haE, hga, hra⟩ := qs_fx_atomAbove hE hBE hEB hXE hlim hIH hA hi hx hx1 hb hgb
    obtain ⟨hbT, hb1, -⟩ := qs_T hE hBE hEB hlim hIH hx hx1 hb hgb
    exact ((gmq_lt hx hx1 hbT hb1 hσb).trans_le hra).trans (hu1 a haE hga)
  have huE : InE u := ywC_inE hx hx1 le_rfl huT hu1' hxu ((ywC_one_iff hx hx1).2 hucl)
  -- the parts of the reading are below `u`
  have hfold : ucFold fE (ucLev E) < u := (ucFold_lt_iff _ huE.pos _).2 fun d hd => by
    simp only [hfEdef, if_pos (hcomp d hd).1]; exact hu1 d (hcomp d hd).1 (hcomp d hd).2
  have hdatN : rjDat (Om1 + qcLvx E (ucLev E) x) < u := hdatle.trans_lt hfold
  have hKu : qcK (ucLev E) (ucI (ucLev E) E) x < u := by
    unfold qcK
    split_ifs with hF
    · obtain ⟨-, -, hpy⟩ := qc_fpH_mem hne hF
      obtain ⟨hgp, hgo⟩ := hgF hF
      exact (inE_indec huE).add_lt (hu1 _ (hpy.trans hyE) (hgp.trans_lt hgx))
        (hu1 _ ((Ordinal.sub_le_self _ _).trans_lt hyE) (hgo.trans_lt hgx))
    · exact hu1 _ hyE ((hg0y hF).trans_lt hgx)
  rw [hVeq] at huV
  rcases qc_rep hx hx1 hO1N hNE hNT hKT hK1 huE hxu hdatN hKu huV with
    ⟨q, t, hq1, hqT, hqΩ, htT, htΩ, hqt⟩ | ⟨M', σ', hM'1, hM'E, hM'T, hσ'T, hσ'Ω, hM'v, hlex⟩
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
    have h0T : (0 : Ordinal.{0}) ∈ Tset x := mem_T_of_le hx hx1 zero_le
    have h0Ω : (0 : Ordinal.{0}) < Om1 := hx.pos.trans hx1
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
  -- `u = ϑˣ(Ω₁·M' + σ')`, `M' = Ω₁ + J`
  obtain ⟨hdM'u, hσ'u⟩ := rjLevel_lt_vt hx hx1 hM'1 hM'E hM'T hσ'T hσ'Ω
  rw [hM'v] at hdM'u hσ'u
  obtain ⟨J, hJ⟩ := exists_add_of_le hM'1
  have hJ0 : J ≠ 0 := by
    intro h0
    rw [hJ, h0, add_zero] at hM'v
    have h := hucl σ' hσ'T hσ'u
    rw [← hM'v] at h
    exact lt_irrefl _ h
  have hJE : J < ggE := (le_add_self.trans_eq hJ.symm).trans_lt hM'E
  have hdatJ : rjDat J < u := by rw [← qc_rjDat_Om1_add' hJE, ← hJ]; exact hdM'u
  -- the same level, a larger index reading
  have hsame : ∀ η, η ∈ Tset x → η < Om1 → σ' ≤ η →
      vt x (Om1 * (Om1 + qcLvx E (ucLev E) x) + σ') ≤ vt x (Om1 * (Om1 + qcLvx E (ucLev E) x) + η) := by
    intro η hηT hη1 hση
    rcases hση.lt_or_eq with h | h
    · obtain ⟨hd, hηv⟩ := rjLevel_lt_vt hx hx1 hO1N hNE hNT hηT hη1
      exact (rjVt_lt hx hx1 hNE hNT hσ'T hσ'Ω hO1N hNE hNT hηT hη1 ((add_lt_add_iff_left _).2 h) hd
        (h.trans hηv)).le
    · rw [h]
  have key : ∃ a, a < E ∧ qcG a < x ∧ u ≤ vQ a x := by
    rcases hlex with hlt | ⟨heq, hσK⟩
    · -- a lower level `J < λ(x)`: a fixed point `H_μ(z) < E` of a level `μ < λ` reads above `u`
      have hJL : J < qcLv fE (ucLev E) := by rw [hJ] at hlt; exact (add_lt_add_iff_left _).1 hlt
      obtain ⟨μ, hμl, hμD, hJμ⟩ := qcLv_cof fE (fun d => d < E ∧ qcG d < x) hf0 hD0 hfΩ hfm hDm2 hbelow huE hU
        (ucLev E) hlE hcomp J hJL hdatJ
      have hμ0 : μ ≠ 0 := by
        rintro rfl
        rw [qcLv_small fE uc_SC_Om2.1, hf0] at hJμ
        exact hJ0 (le_antisymm hJμ zero_le)
      have hJμ' : J ≤ qcLvx E μ x := hJμ
      obtain ⟨b, hb, hgb, hσb⟩ := hcof _ (max_lt hσ'u hdatJ)
      obtain ⟨a, η, haE, hga, hra, hbη, hηT, hη1⟩ :=
        qs_fx_codeAbove hE hBE hEB hXE hlim hIH hA hi hx hx1 hμ0 hμl hμD hb hgb
      have hση : σ' < η := ((le_max_left _ _).trans_lt hσb).trans_le hbη
      have hdη : rjDat J < η := ((le_max_right _ _).trans_lt hσb).trans_le hbη
      obtain ⟨hcompμ, -, hNμE, hNμT, -, -, -⟩ : (∀ d ∈ ucComps μ, d < E ∧ qcG d < x) ∧ True ∧
          Om1 + qcLvx E μ x < ggE ∧ rjDat (Om1 + qcLvx E μ x) ∈ Tset x ∧ True ∧ True ∧ True := by
        obtain ⟨hLE, hLdat, -, -⟩ := qcLv_main fE (fun d => d < E ∧ qcG d < x) hf0 hD0 hfΩ hfm μ
          (hμl.trans hlE) hμD
        have hgE : InE ggE := ggE_spec.1
        have hOE : Om1 < ggE := by rw [rj_Om1]; exact ggE_spec.2
        obtain ⟨m, hmO, hT⟩ := qc_T_cut hx hx1
        have hm0 : 0 < m := (hT 0 (hx.pos.trans hx1)).1 (mem_T_of_le hx hx1 zero_le)
        have hfoldm : ucFold fE μ < m := (ucFold_lt_iff fE hm0 _).2 fun d hd => by
          have h := hcode d (hμD d hd).1 (hμD d hd).2
          simp only [hfEdef, if_pos (hμD d hd).1]
          exact (hT _ h.2).1 h.1
        have hle : rjDat (Om1 + qcLvx E μ x) ≤ ucFold fE μ := by
          show rjDat (Om1 + qcLv fE μ) ≤ ucFold fE μ
          have hL1 : 1 ≤ qcLv fE μ := hJμ.trans' (one_le_iff_ne_zero.2 hJ0)
          rcases lt_or_ge (qcLv fE μ) Om1 with hs | hs
          · rw [rjDat_Om1_add (one_le_iff_ne_zero.1 hL1) hs]; have h := hLdat; rwa [rjDat_small hs] at h
          · rw [si_rjDat_Om1_add hs hLE]; exact hLdat
        have hlt' := hle.trans_lt hfoldm
        exact ⟨hμD, trivial, hgE.add_lt hOE hLE, (hT _ (hlt'.trans_le hmO)).2 hlt', trivial, trivial, trivial⟩
      have harg : Om1 * M' + σ' < Om1 * (Om1 + qcLvx E μ x) + η := by
        rcases hJμ'.lt_or_eq with h | h
        · calc Om1 * M' + σ' < Om1 * M' + Om1 := (add_lt_add_iff_left _).2 hσ'Ω
            _ = Om1 * (M' + 1) := (mul_add_one _ _).symm
            _ ≤ Om1 * (Om1 + qcLvx E μ x) := mul_le_mul_right (Order.add_one_le_of_lt (by
                rw [hJ]; exact (add_lt_add_iff_left _).2 h)) _
            _ ≤ _ := le_self_add
        · rw [hJ, h]; exact (add_lt_add_iff_left _).2 hση
      obtain ⟨-, hηv⟩ := rjLevel_lt_vt hx hx1 le_self_add hNμE hNμT hηT hη1
      have hdM' : rjDat M' = rjDat J := by rw [hJ, qc_rjDat_Om1_add' hJE]
      refine ⟨a, haE, hga, ?_⟩
      rw [hra, ← hM'v]
      exact (rjVt_lt hx hx1 hM'E hM'T hσ'T hσ'Ω le_self_add hNμE hNμT hηT hη1 harg
        (by rw [hdM']; exact hdη.trans hηv) (hση.trans hηv)).le
    · -- the level of `E` and an index reading `σ' < K(x)`
      rw [heq] at hM'v
      by_cases hF : QcFixH (ucLev E) (ucI (ucLev E) E)
      · obtain ⟨hpf, hOp, hpy⟩ := qc_fpH_mem hne hF
        obtain ⟨hgp', hgo'⟩ := hgF hF
        have hgp := hgp'.trans_lt hgx
        have hgo := hgo'.trans_lt hgx
        unfold qcK at hσK
        rw [if_pos hF] at hσK
        have hpE : qcFpH (ucLev E) (ucI (ucLev E) E) < E := hpy.trans hyE
        have hpSC : SC (qcFpH (ucLev E) (ucI (ucLev E) E)) := by rw [← hpf]; exact ucH_SC _ _
        have hle_y : ∀ f', ucH (ucLev E) f' = f' → f' < ucI (ucLev E) E →
            f' ≤ qcFpH (ucLev E) (ucI (ucLev E) E) := fun f' h1 h2 => le_csSup ⟨_, fun _ h => h.2.le⟩ ⟨h1, h2⟩
        by_cases hσp : σ' < vQ (qcFpH (ucLev E) (ucI (ucLev E) E)) x
        · -- `p` is a fixed point of a higher level: it reads above `u`
          set p := qcFpH (ucLev E) (ucI (ucLev E) E) with hpdef
          have hAp : YhAt p := ⟨hpSC, hOp⟩
          have hip : ¬ yhJ p < p := by
            have hg := qc_P_gamma hl0 hpf
            have h := yhJ_gcG p; rw [vs_gcG_fix hg hOp] at h; rw [h]; exact lt_irrefl _
          have hpB : p < ucB := hpE.trans hEB
          have hGp : gcG 0 ≤ p := gl_G0_le hpSC hOp
          have hgxp : max ω (qcQE p) < x := by
            rw [← qcG_base' (Low.opow_eq_self_of_SC hpSC) hGp hpB]; exact max_lt hωx hgp
          obtain ⟨hcompe, -, hNeE, hNeT, -, hKeT, hKe1⟩ :=
            qs_fix_lev_u hx hx1 hAp hip hpB hgxp (fun c hc hgc => hcode c (hc.trans hpE) hgc)
              (fun b c hbc hc hgb hgc => hmono b c hbc (hc.trans hpE) hgb hgc)
          have hne' := uc_nf_of_lt hAp.1 hOp hpB
          obtain ⟨hlpE, hlpc, hlpne, -, -⟩ := ucLev_spec hAp.1 hOp hne'
          have hlev : ucLev E < ucLev p := by
            by_contra h
            push Not at h
            exact hlpne (ucG_fix_mono h hpf hlpc)
          have hcompμ : ∀ d ∈ ucComps (ucLev p), d < E ∧ qcG d < x := fun d hd =>
            ⟨(hcompe d hd).1.trans hpE, (hcompe d hd).2⟩
          have hord := (qcLv_main fE _ hf0 hD0 hfΩ hfm _ hlpE hcompμ).2.2.2 _ hlev hcomp
          have hlvx : qcLvx p (ucLev p) x = qcLv fE (ucLev p) := by
            unfold qcLvx
            refine qcLv_congr _ fun d hd => ?_
            have hde := (hcompe d hd).1
            simp only [hfEdef, if_pos hde, if_pos (hde.trans hpE)]
          have hNlt : Om1 + qcLvx E (ucLev E) x < Om1 + qcLvx p (ucLev p) x := by
            rw [hlvx]; exact (add_lt_add_iff_left _).2 hord
          have harg : Om1 * (Om1 + qcLvx E (ucLev E) x) + σ' <
              Om1 * (Om1 + qcLvx p (ucLev p) x) + qcK (ucLev p) (ucI (ucLev p) p) x := by
            calc _ < Om1 * (Om1 + qcLvx E (ucLev E) x) + Om1 := (add_lt_add_iff_left _).2 hσ'Ω
              _ = Om1 * (Om1 + qcLvx E (ucLev E) x + 1) := (mul_add_one _ _).symm
              _ ≤ Om1 * (Om1 + qcLvx p (ucLev p) x) := mul_le_mul_right (Order.add_one_le_of_lt hNlt) _
              _ ≤ _ := le_self_add
          have hCp : ucC (ucLev E) < p := by have h := ucH_C_lt (ucLev E) p; rwa [hpf] at h
          have hfoldp : ucFold fE (ucLev E) < vQ p x := by
            refine (ucFold_lt_iff _ (lt_of_le_of_lt zero_le hσp) _).2 fun d hd => ?_
            simp only [hfEdef, if_pos (hcomp d hd).1]
            exact hmono d p ((le_ucC hd).trans_lt hCp) hpE (hcomp d hd).2 hgp
          have hrdp := qs_fixRd hAp hip hpB x
          refine ⟨p, hpE, hgp, ?_⟩
          rw [← hM'v, hrdp]
          rw [hrdp] at hfoldp hσp
          exact (rjVt_lt hx hx1 hNE hNT hσ'T hσ'Ω (le_self_add) hNeE hNeT hKeT hKe1 harg
            (hdatle.trans_lt hfoldp) hσp).le
        · -- a smaller offset `t' < o = y − (p+1)`: the fixed point `H_λ(p + 1 + t')`
          push Not at hσp
          obtain ⟨δ, hδ⟩ := exists_add_of_le hσp
          rw [hδ] at hσK
          have hδo := (add_lt_add_iff_left _).1 hσK
          set p := qcFpH (ucLev E) (ucI (ucLev E) E) with hpdef
          set o := ucI (ucLev E) E - (p + 1) with hodef
          have ho0 : o ≠ 0 := by
            intro h; rw [h, vQ_zero] at hδo; exact absurd hδo (not_lt.2 zero_le)
          have hoE : o < E := (Ordinal.sub_le_self _ _).trans_lt hyE
          obtain ⟨t', ht'o, hgt', hδt'⟩ := qs_below hE hBE hEB hlim hIH hx hx1 hoE ho0 hgo δ hδo
          have hpy1 : p + 1 ≤ ucI (ucLev E) E := Order.add_one_le_of_lt hpy
          have hzy : p + 1 + t' < ucI (ucLev E) E := by
            have h := (add_lt_add_iff_left (p + 1)).2 ht'o
            rwa [hodef, Ordinal.add_sub_cancel_of_le hpy1] at h
          have hpz : p < p + 1 + t' := (lt_add_one p).trans_le le_self_add
          have hzr : p + 1 + t' < ucH (ucLev E) (p + 1 + t') := by
            refine lt_of_le_of_ne (ucH_le_self _ _) fun h => ?_
            exact absurd (hle_y _ h.symm hzy) (not_le.2 hpz)
          have hFz : QcFixH (ucLev E) (p + 1 + t') := ⟨p, hpf, hpz⟩
          have hpz' : qcFpH (ucLev E) (p + 1 + t') = p := by
            refine le_antisymm (csSup_le ⟨p, hpf, hpz⟩ fun f' hf' => hle_y f' hf'.1 (hf'.2.trans hzy)) ?_
            exact le_csSup ⟨_, fun _ h => h.2.le⟩ ⟨hpf, hpz⟩
          have hK : qcK (ucLev E) (p + 1 + t') x = vQ p x + vQ t' x := by
            unfold qcK; rw [if_pos hFz, hpz', Ordinal.add_sub_cancel]
          obtain ⟨haE, hrda⟩ := hrdE _ hzy hzr
          have hzB : p + 1 + t' < ucB := (hzy.trans hyE).trans hEB
          have hgz : qcG (p + 1 + t') < x :=
            qc_add hxP hωx _ _ hzB (qc_add hxP hωx _ _ (le_self_add.trans_lt hzB) hgp h1g) hgt'
          obtain ⟨hpT, hp1, -⟩ := qs_T hE hBE hEB hlim hIH hx hx1 hpE hgp
          obtain ⟨ht'T, ht'1, -⟩ := qs_T hE hBE hEB hlim hIH hx hx1 (ht'o.trans hoE) hgt'
          refine ⟨_, haE, qc_H_gate hx hl0 hlE hzr (haE.trans hEB) (fun d hd => (hcomp d hd).2) hgz, ?_⟩
          rw [hrda, hK, ← hM'v]
          exact hsame _ (vzT_add hx hx1 hpT ht'T) ((inE_indec gl_Om1_E).add_lt hp1 ht'1)
            (by rw [hδ]; exact (add_le_add_iff_left _).2 hδt')
      · -- no fixed point of `H_λ` below `y`: a smaller argument `s' < y`
        unfold qcK at hσK
        rw [if_neg hF] at hσK
        have hgy := (hg0y hF).trans_lt hgx
        have hy0 : ucI (ucLev E) E ≠ 0 := by
          intro h; rw [h, vQ_zero] at hσK; exact absurd hσK (not_lt.2 zero_le)
        obtain ⟨s', hs'y, hgs', hσs'⟩ := qs_below hE hBE hEB hlim hIH hx hx1 hyE hy0 hgy σ' hσK
        have hzr : s' < ucH (ucLev E) s' :=
          lt_of_le_of_ne (ucH_le_self _ _) fun h => hF ⟨s', h.symm, hs'y⟩
        have hnF : ¬ QcFixH (ucLev E) s' := fun ⟨f, h1, h2⟩ => hF ⟨f, h1, h2.trans hs'y⟩
        obtain ⟨haE, hrda⟩ := hrdE _ hs'y hzr
        obtain ⟨hs'T, hs'1, -⟩ := qs_T hE hBE hEB hlim hIH hx hx1 (hs'y.trans hyE) hgs'
        refine ⟨_, haE, qc_H_gate hx hl0 hlE hzr (haE.trans hEB) (fun d hd => (hcomp d hd).2) hgs', ?_⟩
        rw [hrda, ← hM'v]
        unfold qcK
        rw [if_neg hnF]
        exact hsame _ hs'T hs'1 hσs'
  obtain ⟨a, haE, hga, hua⟩ := key
  exact absurd (hu1 a haE hga) (not_lt.2 hua)

end Fix

end Googology.Trans.PoR.InaccPsi.R2.Qc
