import Googology.Trans.PoR.InaccPsi.R2.QdFxC

/-!
# QdFxD: THE READINGS OF THE CODES BELOW THE FIXED POINT `E = Hᵛ_λ(y) ∈ (B₂, B₃)` ARE COFINAL IN ITS READING

As `Qc.QcFxD` with the Veblen levels, for `E > B₂`.  The fixed points `Hᵛ_μ(z)` built here are at least `B₂`
(`qd_H_ge_B2`: the argument is at least `B₂`, or `Hᵛ_μ` does not fix `B₂`), so they read in the form of `Qd.vD_fix`.
The supremum `u` of the readings of the codes below `E` is closed (above every reading `b(x)` is the reading
`gq(F(x) + b(x))` of the atom `Γ(F + 1 + b)`, `qd_fx_atomAbove`), so `u = ϑˣ(Ω₁·M' + σ')` (`qd_rep`) with
`M' = Ω₁ + J`, `J ≥ 1`, and either `J < λ(x)` — a level `μ < λ` with `J ≤ μ(x)` (`Qd.qdLv_cof`) and a fixed point
`Hᵛ_μ(z) ∈ [B₂, E)` reads above `u` (`qd_fx_codeAbove`) — or `J = λ(x)`, `σ' < K(x)` — the largest fixed point
`p < y` of `Hᵛ_λ`, or `Hᵛ_λ(z)` for a smaller argument `z < y`, reads above `u`.

* `qd_rep` (as `Qc.qc_rep` at a Veblen level), `qd_H_J`, `qd_H_ge_B2`, `qd_H_gate` (**the gate of `Hᵛ_μ(z) ≥ B₂`**);
* `qd_fx_atomAbove`, `qd_fx_codeAbove`, `qd_fx_top` (**the readings below `E` are cofinal in `qdA E x`**).

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

section Rep

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

/-- **The `ε`-numbers below a point of a Veblen level `M`** (above `x`, the data of `M` and `σ`). -/
theorem qd_rep {M σ a : Ordinal.{0}} (hM1 : Om1 ≤ M) (hMG : M < ggGam) (hMT : tfDat M ∈ Tset x)
    (hσT : σ ∈ Tset x) (hσΩ : σ < Om1) (haE : InE a) (hxa : x < a) (hda : tfDat M < a) (hσa : σ < a)
    (hae : a < vt x (Om1 * M + σ)) :
    (∃ q t, 1 ≤ q ∧ q ∈ Tset x ∧ q < Om1 ∧ t ∈ Tset x ∧ t < Om1 ∧ vt x (Om1 * q + t) = a) ∨
    (∃ M' σ', Om1 ≤ M' ∧ M' < ggGam ∧ tfDat M' ∈ Tset x ∧ σ' ∈ Tset x ∧ σ' < Om1 ∧
      vt x (Om1 * M' + σ') = a ∧ (M' < M ∨ (M' = M ∧ σ' < σ))) := by
  have hMB : M < tfBG := hMG.trans tf_gg_lt_BG
  have hargT := tfArg_mem hx hx1 hM1 hMB hMT hσT hσΩ
  obtain ⟨hET, -, hE1, -, -⟩ := vt_memTwo hx hx1 hargT (qd_arg_lt hMG hσΩ)
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
    have hM'T : tfDat M' ∈ Tset x := tfArg_dat hx hx1 hM'Ω (hM'G.trans tf_gg_lt_BG) hr1 (by rw [hdec]; exact hξT)
    exact ⟨M', σ', hM'Ω, hM'G, hM'T, hrT, hr1, by rw [hdec, hξv], hlex⟩

end Rep

variable (S : InaccSeq.{0})

include S in
/-- **A value of `Hᵛ_μ`, `μ ≠ 0`, is its own atom index** (a fixed point of `Γ = Hᵛ_0`). -/
theorem qd_H_J {μ z : Ordinal.{0}} (hμ0 : μ ≠ 0) : yhJ (qdH μ z) = qdH μ z := by
  have h0 : qdH 0 (qdH μ z) = qdH μ z := ucG_fix_lower (pos_iff_ne_zero.2 hμ0) ⟨z, rfl⟩ (by
    rw [qdFold_small id qd_Om2_pos]; exact Rj.rj_Om1_pos.trans (qdH_gt μ z))
  rw [qd_uc_H S (uc_SC_Om2.1.trans ucE_gt), qc_H0] at h0
  have h := yhJ_gcG (qdH μ z)
  rwa [h0] at h

include S in
/-- **The values of `Hᵛ_μ` at an argument `≥ B₂`, or of a level that does not fix `B₂`, are `≥ B₂`.** -/
theorem qd_H_ge_B2 {μ z : Ordinal.{0}} (h : ucB ≤ z ∨ ¬ (μ < ucE ∧ qdFold id μ < ucB)) : ucB ≤ qdH μ z := by
  rcases h with h | h
  · exact h.trans (qdH_le_self μ z)
  by_cases hμE : μ < ucE
  · have hv : ¬ qdFold id μ < ucB := fun hv => h ⟨hμE, hv⟩
    exact (not_lt.1 hv).trans (qdH_D_lt μ z).le
  push Not at hμE
  have hle : qdH ucE 0 ≤ qdH ucE (qdH μ z) := (qdH_normal ucE).strictMono.monotone zero_le
  rcases hμE.lt_or_eq with hlt | heq
  · have hC : qdFold id ucE < qdH μ z := (qdFold_lt_iff (Rj.rj_Om1_pos.trans (qdH_gt μ z)) ucE).2 fun d hd => by
      rw [qdComps_E2 d hd]
      exact (show (1 : Ordinal.{0}) < Om1 by rw [Rj.rj_Om1]; exact Nm.one_lt_Om1).trans (qdH_gt μ z)
    have hfix : qdH ucE (qdH μ z) = qdH μ z := ucG_fix_lower hlt ⟨z, rfl⟩ hC
    rw [← qd_B2_H S]
    exact hle.trans_eq hfix
  · rw [← heq, ← qd_B2_H S]
    exact (qdH_normal ucE).strictMono.monotone zero_le

include S in
/-- **The gate of `Hᵛ_μ(z) ∈ [B₂, B₃)`** (`μ ≠ 0`, `z < Hᵛ_μ(z)`) is below an `ε`-number `x` above the gates of the
leaves of `μ` and of `z`. -/
theorem qd_H_gate {μ z x : Ordinal.{0}} (hx : InE x) (hμ0 : μ ≠ 0) (hμG : μ < qdG2) (hz : z < qdH μ z)
    (hX : ucB ≤ qdH μ z) (hB : qdH μ z < qdB) (hcomp : ∀ d ∈ qdComps μ, qdGt d < x) (hgz : qdGt z < x) :
    qdGt (qdH μ z) < x := by
  have hωx : ω < x := omega0_lt_inE hx
  obtain ⟨hl, hi⟩ := qdLev_H hμG hz
  have hJ := qd_H_J S (z := z) hμ0
  have hA : YhAt (qdH μ z) := ⟨qdH_SC μ z, qdH_gt μ z⟩
  have hi' : ¬ yhJ (qdH μ z) < qdH μ z := by rw [hJ]; exact lt_irrefl _
  have hE : InE (qdH μ z) := Low.opow_eq_self_of_SC (qdH_SC μ z)
  have hN : qdI (qdLev (qdH μ z)) (qdH μ z) < qdH μ z := by rw [hl, hi]; exact hz
  rw [qdGt_base hE hX hB, qdQEt_fix hX hB hA hi' hN, hl, hi]
  refine max_lt ((qdFold_lt_iff' _ hx.pos μ).2 fun d hd => ?_) ?_
  · split_ifs with hdc
    · exact (qdQt_le d).trans_lt (hcomp d hd)
    · exact hx.pos
  · have hne : qdH μ z ≠ z := ne_of_gt hz
    unfold qdKQ
    split_ifs with hFz
    · obtain ⟨hpf, hpO, hpy⟩ := qd_fpH_mem hne hFz
      have hpSC : SC (qdFpH μ z) := by rw [← hpf]; exact qdH_SC _ _
      have hpE : InE (qdFpH μ z) := Low.opow_eq_self_of_SC hpSC
      have hzB : z < qdB := hz.trans hB
      have hgp := qd_fpH_gate S hμ0 hzB hne hFz
      have hgo := qd_off_gate' hpE (gl_G0_le hpSC hpO) hzB hpy
      exact max_lt ((qdQt_le _).trans_lt (hgp.trans_lt (max_lt hωx hgz)))
        ((qdQt_le _).trans_lt (hgo.trans_lt (max_lt hωx hgz)))
    · exact (qdQt_le z).trans_lt hgz

section Fix

variable {E : Ordinal.{0}} (hE : InE E) (hBE : tfBG < E) (hEB : E < qdB) (hXE : ucB ≤ E)
  (hlim : ∀ e, InE e → e < E → eN e < E) (hIH : ∀ e, InE e → tfBG ≤ e → e < E → QdGood e)
  (hA : YhAt E) (hi : ¬ yhJ E < E)
  {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)

include S hE hBE hEB hXE hlim hIH hA hi hx hx1

/-- **Above the reading of a code `b < E` is the reading of an atom `Γ(F + 1 + b) < E`**: `gq(b(x)) ≤ gq(F(x) + b(x))`
(`Γ(b)` below `B_Γ`). -/
theorem qd_fx_atomAbove {b : Ordinal.{0}} (hb : b < E) (hgb : qdGt b < x) :
    ∃ a, a < E ∧ qdGt a < x ∧ gq (vD b x) x ≤ vD a x := by
  have hωx : ω < x := omega0_lt_inE hx
  have hxP : ∀ u v, u < x → v < x → u + v < x := fun u v hu hv => (inE_indec hx).add_lt hu hv
  obtain ⟨hfixE, -⟩ := qd_fx_dat S hEB hXE hA hi
  have hgE : gcG E = E := vs_gcG_fix hfixE hA.2
  obtain ⟨hbT, hb1, -⟩ := qd_T S hE hBE hEB hlim hIH hx hx1 hb hgb
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
    have hgF : qdGt (vaFB b) < x := (qd_FB_gate' hbB (hb.trans hEB)).trans_lt (max_lt hωx hgb)
    have h1g : qdGt (1 : Ordinal.{0}) < x := by
      rw [show (1 : Ordinal.{0}) = ((1 : ℕ) : Ordinal.{0}) by norm_num, qdGt_nat]
      exact (natCast_lt_omega0 1).trans hωx
    have hjB : vaFB b + 1 + b < qdB := hjE.trans hEB
    have hgj : qdGt (vaFB b + 1 + b) < x :=
      qd_add hxP hωx _ _ hjB (qd_add hxP hωx _ _ (le_self_add.trans_lt hjB) hgF h1g) hgb
    have haE : gcG (vaFB b + 1 + b) < E := (gcG_lt hjE).trans_eq hgE
    refine ⟨gcG (vaFB b + 1 + b), haE, by rw [qdGt_atom' hjlt (haE.trans hEB)]; exact (qdQt_le _).trans_lt hgj, ?_⟩
    rw [vD_atom' hjlt (haE.trans hEB), qd_vI hBj hj le_rfl, hseg, Ordinal.add_sub_cancel]
    obtain ⟨hFT, hF1, -⟩ := qd_T S hE hBE hEB hlim hIH hx hx1 (hFb.trans_lt hb) hgF
    exact gmq_mono hx hx1 (vzT_add hx hx1 hFT hbT) ((inE_indec gl_Om1_E).add_lt hF1 hb1) le_add_self
  · have hbB' : b < tfBG := not_le.1 hbB
    have hbg : b < gcG b := by rw [tf_gcG]; exact tf_lt_gamma_shift hbB'
    have haE : gcG b < E := (gcG_lt hb).trans_eq hgE
    refine ⟨gcG b, haE, by rw [qdGt_atom' hbg (haE.trans hEB)]; exact (qdQt_le _).trans_lt hgb, ?_⟩
    rw [vD_atom' hbg (haE.trans hEB), qdRI_noFix (not_lt.2 hbB'.le)]

/-- The core of `qd_fx_codeAbove`: a code `b ∈ [B₂, E)`. -/
theorem qd_fx_codeAbove' {μ : Ordinal.{0}} (hμ0 : μ ≠ 0) (hμl : μ < qdLev E)
    (hcμ : ∀ d ∈ qdComps μ, d < E ∧ qdGt d < x) {b : Ordinal.{0}} (hBb : ucB ≤ b) (hb : b < E)
    (hgb : qdGt b < x) :
    ∃ a η, a < E ∧ qdGt a < x ∧ vD a x = vt x (Om1 * (Om1 + qdLvx E μ x) + η) ∧ vD b x ≤ η ∧
      η ∈ Tset x ∧ η < Om1 := by
  have hωx : ω < x := omega0_lt_inE hx
  have hxP : ∀ u v, u < x → v < x → u + v < x := fun u v hu hv => (inE_indec hx).add_lt hu hv
  have hxl : IsSuccLimit x := ev_isSuccLimit_of_inE hx
  have hEl : IsSuccLimit E := ev_isSuccLimit_of_inE hE
  obtain ⟨-, -, hlG, -, -, -, -, -⟩ := qd_fx_dat S hEB hXE hA hi
  have hμG : μ < qdG2 := hμl.trans hlG
  have hCμ : qdFold id μ < E := (qdFold_lt_iff hE.pos μ).2 fun d hd => (hcμ d hd).1
  have hEμ : qdH μ E = E := (qdLev_spec hA.1 hA.2 (qd_nf_of_lt hA.1 hA.2 hEB)).2.2.2.1 μ hμl hCμ
  obtain ⟨hbT, hb1, -⟩ := qd_T S hE hBE hEB hlim hIH hx hx1 hb hgb
  have hgcomp : ∀ d ∈ qdComps μ, qdGt d < x := fun d hd => (hcμ d hd).2
  -- the reading of `Hᵛ_μ(z)` for `z ∈ [B₂, E)`, `z < Hᵛ_μ(z)`
  have hrd : ∀ z, z < E → z < qdH μ z → ucB ≤ z →
      vD (qdH μ z) x = vt x (Om1 * (Om1 + qdLvx E μ x) + qdRK μ z x) := by
    intro z hzE hzr hBz
    have haE : qdH μ z < E := by rw [← hEμ]; exact (qdH_lt_iff μ).2 hzE
    obtain ⟨hl', hi'⟩ := qdLev_H hμG hzr
    have hA' : YhAt (qdH μ z) := ⟨qdH_SC μ z, qdH_gt μ z⟩
    have hi'' : ¬ yhJ (qdH μ z) < qdH μ z := by rw [qd_H_J S hμ0]; exact lt_irrefl _
    have hlv : qdLvx (qdH μ z) μ x = qdLvx E μ x := by
      unfold qdLvx
      refine qdLv_congr _ fun d hd => ?_
      have hda : d < qdH μ z :=
        (qdFold_lt_iff (Rj.rj_Om1_pos.trans (qdH_gt μ z)) μ).1 (qdH_D_lt μ z) d hd
      simp only [if_pos hda, if_pos (hcμ d hd).1]
    have hN : qdI (qdLev (qdH μ z)) (qdH μ z) < qdH μ z := by rw [hl', hi']; exact hzr
    rw [vD_fix hA' hi'' hN (hBz.trans (qdH_le_self μ z)) (haE.trans hEB) x, hl', hi', hlv]
  by_cases hex : ∃ f, qdH μ f = f ∧ Om1 < f ∧ f ≤ b
  · -- `z = f₀ + 1 + b`, `f₀` the largest fixed point of `Hᵛ_μ` in `(Ω₁, b]`
    obtain ⟨hf₀S, hOf₀, hf₀b⟩ := qd_mx_SC hex
    have hf₀ := qd_fpH_closed μ b hex
    have hgf₀ : qdGt (vsMx (fun f => qdH μ f = f) b) < x :=
      (qd_mx_gate S hμ0 b (hb.trans hEB) hex).trans_lt (max_lt hωx hgb)
    set f₀ := vsMx (fun f => qdH μ f = f) b with hf₀def
    have hzf : f₀ < f₀ + 1 + b := (lt_add_one _).trans_le le_self_add
    have hbig : ∀ f', qdH μ f' = f' → b < f' → f₀ + 1 + b < f' := fun f' hf' hbf' => by
      have hE' : InE f' := Low.opow_eq_self_of_SC (by rw [← hf']; exact qdH_SC μ f')
      exact (inE_indec hE').add_lt ((inE_indec hE').add_lt (hf₀b.trans_lt hbf') (lu_one_lt_E hE')) hbf'
    have hzr : f₀ + 1 + b < qdH μ (f₀ + 1 + b) := by
      refine lt_of_le_of_ne (qdH_le_self μ _) fun h => ?_
      rcases le_or_gt (f₀ + 1 + b) b with hzb | hzb
      · exact absurd (vs_mx_ge (fun f => qdH μ f = f) h.symm (hOf₀.trans hzf) hzb) (not_le.2 hzf)
      · exact lt_irrefl _ (hbig _ h.symm hzb)
    have hne : qdH μ (f₀ + 1 + b) ≠ f₀ + 1 + b := ne_of_gt hzr
    have hFz : QdFixH μ (f₀ + 1 + b) := ⟨f₀, hf₀, hzf⟩
    have hpz : qdFpH μ (f₀ + 1 + b) = f₀ := by
      rw [qd_fpH_eq hne]
      exact (vs_mx_eq (fun f => qdH μ f = f) le_add_self fun f hf _ hfz => by
        by_contra h; push Not at h; exact absurd hfz (not_le.2 (hbig f hf h))).symm
    have hzE : f₀ + 1 + b < E :=
      (inE_indec hE).add_lt ((inE_indec hE).add_lt (hf₀b.trans_lt hb) (lu_one_lt_E hE)) hb
    have haE : qdH μ (f₀ + 1 + b) < E := by rw [← hEμ]; exact (qdH_lt_iff μ).2 hzE
    have h1g : qdGt (1 : Ordinal.{0}) < x := by
      rw [show (1 : Ordinal.{0}) = ((1 : ℕ) : Ordinal.{0}) by norm_num, qdGt_nat]
      exact (natCast_lt_omega0 1).trans hωx
    have hzB : f₀ + 1 + b < qdB := hzE.trans hEB
    have hgz : qdGt (f₀ + 1 + b) < x :=
      qd_add hxP hωx _ _ hzB (qd_add hxP hωx _ _ (le_self_add.trans_lt hzB) hgf₀ h1g) hgb
    have hBz : ucB ≤ f₀ + 1 + b := hBb.trans le_add_self
    have hK : qdRK μ (f₀ + 1 + b) x = vD f₀ x + vD b x := by
      unfold qdRK; rw [if_pos hFz, hpz, Ordinal.add_sub_cancel]
    obtain ⟨hf₀T, hf₀1, -⟩ := qd_T S hE hBE hEB hlim hIH hx hx1 (hf₀b.trans_lt hb) hgf₀
    refine ⟨qdH μ (f₀ + 1 + b), vD f₀ x + vD b x, haE,
      qd_H_gate S hx hμ0 hμG hzr (hBz.trans (qdH_le_self μ _)) (haE.trans hEB) hgcomp hgz,
      by rw [hrd _ hzE hzr hBz, hK], le_add_self, vzT_add hx hx1 hf₀T hbT, (inE_indec gl_Om1_E).add_lt hf₀1 hb1⟩
  · -- `z = b + 1`: no fixed point of `Hᵛ_μ` below `z`
    have hnF : ¬ QdFixH μ (b + 1) := by
      rintro ⟨f, hf, hfz⟩
      have hOf : Om1 < f := by rw [← hf]; exact qdH_gt μ f
      exact hex ⟨f, hf, hOf, Order.lt_add_one_iff.1 hfz⟩
    have hzr : b + 1 < qdH μ (b + 1) := by
      refine lt_of_le_of_ne (qdH_le_self μ _) fun h => ?_
      have hl := ev_isSuccLimit_of_inE (Low.opow_eq_self_of_SC (qdH_SC μ (b + 1)))
      rw [← h] at hl
      have h' : IsSuccLimit (Order.succ b) := by rw [Order.succ_eq_add_one]; exact hl
      exact Order.not_isSuccLimit_succ _ h'
    have hzE : b + 1 < E := hEl.add_one_lt hb
    have haE : qdH μ (b + 1) < E := by rw [← hEμ]; exact (qdH_lt_iff μ).2 hzE
    have hBz : ucB ≤ b + 1 := hBb.trans le_self_add
    have hK : qdRK μ (b + 1) x = vD b x + 1 := by unfold qdRK; rw [if_neg hnF, vD_succ]
    obtain ⟨hsT, hs1⟩ := gl_T_succ hx hx1 hbT hb1
    refine ⟨qdH μ (b + 1), vD b x + 1, haE,
      qd_H_gate S hx hμ0 hμG hzr (hBz.trans (qdH_le_self μ _)) (haE.trans hEB) hgcomp (qdGt_succ hxl b hgb),
      by rw [hrd _ hzE hzr hBz, hK], le_self_add, hsT, hs1⟩

/-- **Above the reading of a code `b < E`, a fixed point `Hᵛ_μ(z) ∈ [B₂, E)` of a lower level `μ < λ`** (leaves
codes) reads `ϑˣ(Ω₁·(Ω₁+μ(x)) + η)` with `b(x) ≤ η` (`E > B₂`). -/
theorem qd_fx_codeAbove (hBE2 : ucB < E) {μ : Ordinal.{0}} (hμ0 : μ ≠ 0) (hμl : μ < qdLev E)
    (hcμ : ∀ d ∈ qdComps μ, d < E ∧ qdGt d < x) {b : Ordinal.{0}} (hb : b < E) (hgb : qdGt b < x) :
    ∃ a η, a < E ∧ qdGt a < x ∧ vD a x = vt x (Om1 * (Om1 + qdLvx E μ x) + η) ∧ vD b x ≤ η ∧
      η ∈ Tset x ∧ η < Om1 := by
  rcases le_or_gt ucB b with hBb | hbB
  · exact qd_fx_codeAbove' S hE hBE hEB hXE hlim hIH hA hi hx hx1 hμ0 hμl hcμ hBb hb hgb
  · have hgB : qdGt ucB < x := by rw [qd_B2_gate S]; exact hx.pos
    obtain ⟨a, η, haE, hga, hra, hBη, hηT, hη1⟩ :=
      qd_fx_codeAbove' S hE hBE hEB hXE hlim hIH hA hi hx hx1 hμ0 hμl hcμ le_rfl hBE2 hgB
    exact ⟨a, η, haE, hga, hra,
      (qd_le_mono S hE hBE hEB hlim hIH hx hx1 hbB.le hBE2 hgb hgB).trans hBη, hηT, hη1⟩

/-- **The readings of the codes below the fixed point `E > B₂` are cofinal in its reading.** -/
theorem qd_fx_top (hBE2 : ucB < E) (hI : QdImgH) (hgx : max ω (qdQEt E) < x) :
    ∀ ν, ν < qdA E x → ∃ b, b < E ∧ qdGt b < x ∧ ν ≤ vD b x := by
  have hωx : ω < x := omega0_lt_inE hx
  have hxl : IsSuccLimit x := ev_isSuccLimit_of_inE hx
  have hEl : IsSuccLimit E := ev_isSuccLimit_of_inE hE
  have hxP : ∀ u v, u < x → v < x → u + v < x := fun u v hu hv => (inE_indec hx).add_lt hu hv
  obtain ⟨-, hl0, hlG, -, hyE, hFy, hne, -⟩ := qd_fx_dat S hEB hXE hA hi
  obtain ⟨hVeq, -, hVT, -, -, -, hV1⟩ := qd_fx_V S hE hBE hEB hXE hlim hIH hA hi hx hx1 hI hgx
  obtain ⟨hcomp, -, hNG, hNT, hKT, hK1, -⟩ := qd_fx_parts S hE hBE hEB hXE hlim hIH hA hi hx hx1 hgx
  obtain ⟨-, hgF, hg0y⟩ := qd_fix_gates S hA hi hXE hEB
  have hNB : Om1 + qdLvx E (qdLev E) x < tfBG := hNG.trans tf_gg_lt_BG
  have hmono : ∀ b c, b < c → c < E → qdGt b < x → qdGt c < x → vD b x < vD c x := fun b c hbc hc hgb hgc =>
    qd_mono S hE hBE hEB hlim hIH hx hx1 hbc hc hgb hgc
  have hcode : ∀ c, c < E → qdGt c < x → vD c x ∈ Tset x ∧ vD c x < Om1 := fun c hc hgc =>
    ⟨(qd_T S hE hBE hEB hlim hIH hx hx1 hc hgc).1, (qd_T S hE hBE hEB hlim hIH hx hx1 hc hgc).2.1⟩
  obtain ⟨-, -, -, -, hdatle, -, -⟩ := qd_fix_lev_u S hx hx1 hA hi hXE hEB hgx hcode hmono
  have h1g : qdGt (1 : Ordinal.{0}) < x := by
    rw [show (1 : Ordinal.{0}) = ((1 : ℕ) : Ordinal.{0}) by norm_num, qdGt_nat]
    exact (natCast_lt_omega0 1).trans hωx
  have hO1N : Om1 ≤ Om1 + qdLvx E (qdLev E) x := le_self_add
  have hB3O : qdB < (OmTwo : Ordinal.{0}) := by
    rw [uc_Om2_eq]; exact (qd_B3_le_th (S := S)).trans_lt Ui.ui_th_lt_Om2
  -- if `Hᵛ_λ` fixes `B₂`, then `B₂ < y`
  have hvisB : qdLev E < ucE ∧ qdFold id (qdLev E) < ucB →
      qdH (qdLev E) ucB = ucB ∧ ucB < qdI (qdLev E) E := fun ⟨hlt, hvis⟩ => by
    have hfixB := qd_low_fix S hlt hvis
    refine ⟨hfixB, ?_⟩
    by_contra h
    push Not at h
    rcases h.lt_or_eq with h' | h'
    · have h2 := (qdH_lt_iff (qdLev E)).2 h'
      rw [hFy, hfixB] at h2
      exact absurd hBE2 (not_lt.2 h2.le)
    · have h2 := hFy; rw [h', hfixB] at h2; exact absurd h2 hBE2.ne
  -- the leaves read by `fE`
  set fE : Ordinal.{0} → Ordinal.{0} := fun d => if d < E then vD d x else 0 with hfEdef
  have hE0 : (0 : Ordinal.{0}) < E := hE.pos
  have hf0 : fE 0 = 0 := by simp only [hfEdef, if_pos hE0, vD_zero]
  have hD0 : (fun d => d < E ∧ qdGt d < x) 0 := ⟨hE0, by rw [qdGt_zero]; exact hx.pos⟩
  have hfΩ : ∀ d, (fun d => d < E ∧ qdGt d < x) d → fE d < Om1 := fun d hd => by
    simp only [hfEdef, if_pos hd.1]; exact (hcode d hd.1 hd.2).2
  have hfm : ∀ d d', (fun d => d < E ∧ qdGt d < x) d → (fun d => d < E ∧ qdGt d < x) d' → d < d' →
      fE d < fE d' := fun d d' hd hd' hdd => by
    simp only [hfEdef, if_pos hd.1, if_pos hd'.1]; exact hmono d d' hdd hd'.1 hd.2 hd'.2
  have hDm2 : ∀ d, (fun d => d < E ∧ qdGt d < x) d → d < OmTwo := fun d hd => (hd.1.trans hEB).trans hB3O
  have hbelow : ∀ d, (fun d => d < E ∧ qdGt d < x) d → ∀ ν, ν < fE d →
      ∃ d', d' < d ∧ (fun d => d < E ∧ qdGt d < x) d' ∧ ν ≤ fE d' := by
    intro d hd ν hν
    simp only [hfEdef, if_pos hd.1] at hν
    rcases eq_or_ne d 0 with rfl | hd0
    · rw [vD_zero] at hν; exact absurd hν (not_lt.2 zero_le)
    obtain ⟨d', hd'd, hgd', hνd'⟩ := qd_below S hE hBE hEB hlim hIH hx hx1 hd.1 hd0 hd.2 ν hν
    exact ⟨d', hd'd, ⟨hd'd.trans hd.1, hgd'⟩, by simp only [hfEdef, if_pos (hd'd.trans hd.1)]; exact hνd'⟩
  -- the readings of `Hᵛ_λ(z) ≥ B₂` for `z < y`
  have hrdE : ∀ z, z < qdI (qdLev E) E → z < qdH (qdLev E) z → ucB ≤ qdH (qdLev E) z →
      qdH (qdLev E) z < E ∧ vD (qdH (qdLev E) z) x =
        vt x (Om1 * (Om1 + qdLvx E (qdLev E) x) + qdRK (qdLev E) z x) := by
    intro z hzy hzr hXa
    have haE : qdH (qdLev E) z < E := ((qdH_lt_iff _).2 hzy).trans_eq hFy
    obtain ⟨hl', hi'⟩ := qdLev_H hlG hzr
    have hA' : YhAt (qdH (qdLev E) z) := ⟨qdH_SC _ z, qdH_gt _ z⟩
    have hi'' : ¬ yhJ (qdH (qdLev E) z) < qdH (qdLev E) z := by rw [qd_H_J S hl0]; exact lt_irrefl _
    have hlv : qdLvx (qdH (qdLev E) z) (qdLev E) x = qdLvx E (qdLev E) x := by
      unfold qdLvx
      refine qdLv_congr _ fun d hd => ?_
      have hda : d < qdH (qdLev E) z :=
        (qdFold_lt_iff (Rj.rj_Om1_pos.trans (qdH_gt _ z)) _).1 (qdH_D_lt _ z) d hd
      simp only [if_pos hda, if_pos (hcomp d hd).1]
    have hN : qdI (qdLev (qdH (qdLev E) z)) (qdH (qdLev E) z) < qdH (qdLev E) z := by rw [hl', hi']; exact hzr
    refine ⟨haE, ?_⟩
    rw [vD_fix hA' hi'' hN hXa (haE.trans hEB) x, hl', hi', hlv]
  intro ν hν
  by_contra hcon
  push Not at hcon
  set St : Set Ordinal.{0} := {s | ∃ b, b < E ∧ qdGt b < x ∧ s = vD b x} with hStdef
  have hSne : St.Nonempty := ⟨vD 0 x, 0, hE.pos, by rw [qdGt_zero]; exact hx.pos, rfl⟩
  have hSbdd : BddAbove St := ⟨ν, fun s ⟨b, hb, hg, hs⟩ => hs ▸ (hcon b hb hg).le⟩
  set u := sSup St with hudef
  have hu1 : ∀ b, b < E → qdGt b < x → vD b x < u := by
    intro b hb hg
    have h1 : vD (b + 1) x ≤ u := le_csSup hSbdd ⟨b + 1, hEl.add_one_lt hb, qdGt_succ hxl b hg, rfl⟩
    rw [vD_succ] at h1
    exact (lt_add_one _).trans_le h1
  have hu2 : u ≤ ν := csSup_le hSne fun s ⟨b, hb, hg, hs⟩ => hs ▸ (hcon b hb hg).le
  have hcof : ∀ ζ, ζ < u → ∃ b, b < E ∧ qdGt b < x ∧ ζ < vD b x := fun ζ hζ => by
    obtain ⟨s, ⟨b, hb, hgb, rfl⟩, hζb⟩ := exists_lt_of_lt_csSup hSne hζ
    exact ⟨b, hb, hgb, hζb⟩
  have hU : ∀ ζ, ζ < u → ∃ d, (fun d => d < E ∧ qdGt d < x) d ∧ ζ ≤ fE d := fun ζ hζ => by
    obtain ⟨b, hb, hgb, hζb⟩ := hcof ζ hζ
    exact ⟨b, ⟨hb, hgb⟩, by simp only [hfEdef, if_pos hb]; exact hζb.le⟩
  -- `x < u`
  have hBGX : tfBG < tlX := tl_BG_lt_X
  have hBGB : tfBG < ucB := hBGX.trans uc_X_lt_B
  have hgB : qdGt tfBG < x := by
    rw [qdGt_low hBGB, qcG_low hBGX, yrG_base (Low.opow_eq_self_of_SC tfBG_SC) va_G_le_BG, va_QE_BG]
    exact hx.pos
  have hDu : ywV 1 0 x < u := by
    have h := hu1 tfBG hBE hgB; rwa [vD_low hBGB, vQ_low hBGX, vR_BG] at h
  have hxu : x < u := (zmD_facts hx hx1).2.1.trans hDu
  have huV : u < qdA E x := hu2.trans_lt hν
  have huT : u ∈ Tset x := vz_T_down hx hx1 hVT hV1 huV.le
  have hu1' : u < Om1 := huV.trans hV1
  -- `u` is closed: above every reading is the reading of an atom
  have hucl : YwClosed x u := by
    intro σ hσT hσu
    obtain ⟨b, hb, hgb, hσb⟩ := hcof σ hσu
    obtain ⟨a, haE, hga, hra⟩ := qd_fx_atomAbove S hE hBE hEB hXE hlim hIH hA hi hx hx1 hb hgb
    obtain ⟨hbT, hb1, -⟩ := qd_T S hE hBE hEB hlim hIH hx hx1 hb hgb
    exact ((gmq_lt hx hx1 hbT hb1 hσb).trans_le hra).trans (hu1 a haE hga)
  have huE : InE u := ywC_inE hx hx1 le_rfl huT hu1' hxu ((ywC_one_iff hx hx1).2 hucl)
  -- the parts of the reading are below `u`
  have hfold : qdFold fE (qdLev E) < u := (qdFold_lt_iff' _ huE.pos _).2 fun d hd => by
    simp only [hfEdef, if_pos (hcomp d hd).1]; exact hu1 d (hcomp d hd).1 (hcomp d hd).2
  have hdatN : tfDat (Om1 + qdLvx E (qdLev E) x) < u := hdatle.trans_lt hfold
  have hKu : qdRK (qdLev E) (qdI (qdLev E) E) x < u := by
    unfold qdRK
    split_ifs with hF
    · obtain ⟨-, -, hpy⟩ := qd_fpH_mem hne hF
      obtain ⟨hgp, hgo⟩ := hgF hF
      exact (inE_indec huE).add_lt (hu1 _ (hpy.trans hyE) (hgp.trans_lt hgx))
        (hu1 _ ((Ordinal.sub_le_self _ _).trans_lt hyE) (hgo.trans_lt hgx))
    · exact hu1 _ hyE ((hg0y hF).trans_lt hgx)
  rw [hVeq] at huV
  rcases qd_rep hx hx1 hO1N hNG hNT hKT hK1 huE hxu hdatN hKu huV with
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
  obtain ⟨hdM'u, hσ'u⟩ := tfLevel_lt hx hx1 hM'1 (hM'G.trans tf_gg_lt_BG) hM'T hσ'T hσ'Ω
  rw [hM'v] at hdM'u hσ'u
  obtain ⟨J, hJ⟩ := exists_add_of_le hM'1
  have hJ0 : J ≠ 0 := by
    intro h0
    rw [hJ, h0, add_zero] at hM'v
    have h := hucl σ' hσ'T hσ'u
    rw [← hM'v] at h
    exact lt_irrefl _ h
  have hJG : J < ggGam := (le_add_self.trans_eq hJ.symm).trans_lt hM'G
  have hdM' : tfDat M' = Ss.ssDat J := by
    rw [hJ, tfDat_eq_ss _ (hJ ▸ hM'G), qd_ssDat_Om1_add (one_le_iff_ne_zero.2 hJ0) hJG]
  have hdatJ : Ss.ssDat J < u := by rw [← hdM']; exact hdM'u
  -- the same level, a larger index reading
  have hsame : ∀ η, η ∈ Tset x → η < Om1 → σ' ≤ η →
      vt x (Om1 * (Om1 + qdLvx E (qdLev E) x) + σ') ≤ vt x (Om1 * (Om1 + qdLvx E (qdLev E) x) + η) := by
    intro η hηT hη1 hση
    rcases hση.lt_or_eq with h | h
    · obtain ⟨hd, hηv⟩ := tfLevel_lt hx hx1 hO1N hNB hNT hηT hη1
      exact (tfVt_lt hx hx1 hO1N hNB le_rfl hNT hσ'T hσ'Ω hNT hηT hη1 ((add_lt_add_iff_left _).2 h) hd
        (h.trans hηv)).le
    · rw [h]
  have key : ∃ a, a < E ∧ qdGt a < x ∧ u ≤ vD a x := by
    rcases hlex with hlt | ⟨heq, hσK⟩
    · -- a lower level `J < λ(x)`: a fixed point `Hᵛ_μ(z) < E` of a level `μ < λ` reads above `u`
      have hJL : J < qdLv fE (qdLev E) := by rw [hJ] at hlt; exact (add_lt_add_iff_left _).1 hlt
      obtain ⟨μ, hμl, hμD, hJμ⟩ := qdLv_cof fE (fun d => d < E ∧ qdGt d < x) hf0 hD0 hfΩ hfm hDm2 hbelow hU
        (qdLev E) hlG hcomp J hJL hdatJ
      have hμ0 : μ ≠ 0 := by
        rintro rfl
        rw [qdLv_small fE qd_Om2_pos, hf0] at hJμ
        exact hJ0 (le_antisymm hJμ zero_le)
      have hJμ' : J ≤ qdLvx E μ x := hJμ
      obtain ⟨b, hb, hgb, hσb⟩ := hcof _ (max_lt hσ'u hdatJ)
      obtain ⟨a, η, haE, hga, hra, hbη, hηT, hη1⟩ :=
        qd_fx_codeAbove S hE hBE hEB hXE hlim hIH hA hi hx hx1 hBE2 hμ0 hμl hμD hb hgb
      have hση : σ' < η := ((le_max_left _ _).trans_lt hσb).trans_le hbη
      have hdη : Ss.ssDat J < η := ((le_max_right _ _).trans_lt hσb).trans_le hbη
      obtain ⟨hLG, hLdat, -, -, -, -⟩ :=
        qdLv_main fE (fun d => d < E ∧ qdGt d < x) hf0 hD0 hfΩ hfm μ (hμl.trans hlG) hμD
      obtain ⟨m, hmO, hT⟩ := qc_T_cut hx hx1
      have hm0 : 0 < m := (hT 0 (hx.pos.trans hx1)).1 (mem_T_of_le hx hx1 zero_le)
      have hfoldm : qdFold fE μ < m := (qdFold_lt_iff' fE hm0 _).2 fun d hd => by
        have h := hcode d (hμD d hd).1 (hμD d hd).2
        simp only [hfEdef, if_pos (hμD d hd).1]
        exact (hT _ h.2).1 h.1
      have hL1 : 1 ≤ qdLv fE μ := hJμ.trans' (one_le_iff_ne_zero.2 hJ0)
      have hNμG : Om1 + qdLvx E μ x < ggGam := tf_Om1_add_lt_gg hLG
      have hle : tfDat (Om1 + qdLvx E μ x) ≤ qdFold fE μ := by
        show tfDat (Om1 + qdLv fE μ) ≤ qdFold fE μ
        rw [tfDat_eq_ss _ (tf_Om1_add_lt_gg hLG), qd_ssDat_Om1_add hL1 hLG]; exact hLdat
      have hlt' := hle.trans_lt hfoldm
      have hNμT : tfDat (Om1 + qdLvx E μ x) ∈ Tset x := (hT _ (hlt'.trans_le hmO)).2 hlt'
      have harg : Om1 * M' + σ' < Om1 * (Om1 + qdLvx E μ x) + η := by
        rcases hJμ'.lt_or_eq with h | h
        · calc Om1 * M' + σ' < Om1 * M' + Om1 := (add_lt_add_iff_left _).2 hσ'Ω
            _ = Om1 * (M' + 1) := (mul_add_one _ _).symm
            _ ≤ Om1 * (Om1 + qdLvx E μ x) := mul_le_mul_right (Order.add_one_le_of_lt (by
                rw [hJ]; exact (add_lt_add_iff_left _).2 h)) _
            _ ≤ _ := le_self_add
        · rw [hJ, h]; exact (add_lt_add_iff_left _).2 hση
      obtain ⟨-, hηv⟩ := tfLevel_lt hx hx1 le_self_add (hNμG.trans tf_gg_lt_BG) hNμT hηT hη1
      refine ⟨a, haE, hga, ?_⟩
      rw [hra, ← hM'v]
      exact (tfVt_lt hx hx1 le_self_add (hNμG.trans tf_gg_lt_BG) (tf_M_le hη1 harg) hM'T hσ'T hσ'Ω hNμT hηT hη1
        harg (by rw [hdM']; exact hdη.trans hηv) (hση.trans hηv)).le
    · -- the level of `E` and an index reading `σ' < K(x)`
      rw [heq] at hM'v
      by_cases hF : QdFixH (qdLev E) (qdI (qdLev E) E)
      · obtain ⟨hpf, hOp, hpy⟩ := qd_fpH_mem hne hF
        obtain ⟨hgp', hgo'⟩ := hgF hF
        have hgp := hgp'.trans_lt hgx
        have hgo := hgo'.trans_lt hgx
        unfold qdRK at hσK
        rw [if_pos hF] at hσK
        have hpE : qdFpH (qdLev E) (qdI (qdLev E) E) < E := hpy.trans hyE
        have hpSC : SC (qdFpH (qdLev E) (qdI (qdLev E) E)) := by rw [← hpf]; exact qdH_SC _ _
        have hle_y : ∀ f', qdH (qdLev E) f' = f' → f' < qdI (qdLev E) E →
            f' ≤ qdFpH (qdLev E) (qdI (qdLev E) E) := fun f' h1 h2 => le_csSup ⟨_, fun _ h => h.2.le⟩ ⟨h1, h2⟩
        -- the largest fixed point `p < y` is at least `B₂`
        have hpB2 : ucB ≤ qdFpH (qdLev E) (qdI (qdLev E) E) := by
          by_cases hv : qdLev E < ucE ∧ qdFold id (qdLev E) < ucB
          · obtain ⟨hfixB, hBy⟩ := hvisB hv
            exact hle_y _ hfixB hBy
          · have h := qd_H_ge_B2 S (μ := qdLev E) (z := qdFpH (qdLev E) (qdI (qdLev E) E)) (Or.inr hv)
            rwa [hpf] at h
        by_cases hσp : σ' < vD (qdFpH (qdLev E) (qdI (qdLev E) E)) x
        · -- `p` is a fixed point of a higher level: it reads above `u`
          set p := qdFpH (qdLev E) (qdI (qdLev E) E) with hpdef
          have hAp : YhAt p := ⟨hpSC, hOp⟩
          have hip : ¬ yhJ p < p := by
            have hg := qd_P_gamma S hl0 hpf
            have h := yhJ_gcG p; rw [vs_gcG_fix hg hOp] at h; rw [h]; exact lt_irrefl _
          have hpB : p < qdB := hpE.trans hEB
          have hGp : gcG 0 ≤ p := gl_G0_le hpSC hOp
          have hgxp : max ω (qdQEt p) < x := by
            rw [← qdGt_base' (Low.opow_eq_self_of_SC hpSC) hGp hpB]; exact max_lt hωx hgp
          obtain ⟨hcompe, -, hNeG, hNeT, -, hKeT, hKe1⟩ :=
            qd_fix_lev_u S hx hx1 hAp hip hpB2 hpB hgxp (fun c hc hgc => hcode c (hc.trans hpE) hgc)
              (fun b c hbc hc hgb hgc => hmono b c hbc (hc.trans hpE) hgb hgc)
          obtain ⟨-, -, -, hNp, -, -⟩ := qd_fix_data S hAp hip hpB2 hpB
          have hne' := qd_nf_of_lt hAp.1 hOp hpB
          obtain ⟨hlpG, hlpc, hlpne, -, -⟩ := qdLev_spec hAp.1 hOp hne'
          have hlev : qdLev E < qdLev p := by
            by_contra h
            push Not at h
            exact hlpne (ucG_fix_mono h hpf hlpc)
          have hcompμ : ∀ d ∈ qdComps (qdLev p), d < E ∧ qdGt d < x := fun d hd =>
            ⟨(hcompe d hd).1.trans hpE, (hcompe d hd).2⟩
          have hord := (qdLv_main fE _ hf0 hD0 hfΩ hfm _ hlpG hcompμ).2.2.2.2.2 _ hlev hcomp
          have hlvx : qdLvx p (qdLev p) x = qdLv fE (qdLev p) := by
            unfold qdLvx
            refine qdLv_congr _ fun d hd => ?_
            have hde := (hcompe d hd).1
            simp only [hfEdef, if_pos hde, if_pos (hde.trans hpE)]
          have hNlt : Om1 + qdLvx E (qdLev E) x < Om1 + qdLvx p (qdLev p) x := by
            rw [hlvx]; exact (add_lt_add_iff_left _).2 hord
          have harg : Om1 * (Om1 + qdLvx E (qdLev E) x) + σ' <
              Om1 * (Om1 + qdLvx p (qdLev p) x) + qdRK (qdLev p) (qdI (qdLev p) p) x := by
            calc _ < Om1 * (Om1 + qdLvx E (qdLev E) x) + Om1 := (add_lt_add_iff_left _).2 hσ'Ω
              _ = Om1 * (Om1 + qdLvx E (qdLev E) x + 1) := (mul_add_one _ _).symm
              _ ≤ Om1 * (Om1 + qdLvx p (qdLev p) x) := mul_le_mul_right (Order.add_one_le_of_lt hNlt) _
              _ ≤ _ := le_self_add
          have hCp : qdFold id (qdLev E) < p := by have h := qdH_D_lt (qdLev E) p; rwa [hpf] at h
          have hfoldp : qdFold fE (qdLev E) < vD p x := by
            refine (qdFold_lt_iff' _ (lt_of_le_of_lt zero_le hσp) _).2 fun d hd => ?_
            simp only [hfEdef, if_pos (hcomp d hd).1]
            exact hmono d p ((qdFold_lt_iff (Rj.rj_Om1_pos.trans hOp) _).1 hCp d hd) hpE (hcomp d hd).2 hgp
          have hrdp := vD_fix hAp hip hNp hpB2 hpB x
          refine ⟨p, hpE, hgp, ?_⟩
          rw [← hM'v, hrdp]
          rw [hrdp] at hfoldp hσp
          exact (tfVt_lt hx hx1 le_self_add (hNeG.trans tf_gg_lt_BG) (tf_M_le hKe1 harg) hNT hσ'T hσ'Ω hNeT hKeT
            hKe1 harg (hdatle.trans_lt hfoldp) hσp).le
        · -- a smaller offset `t' < o = y − (p+1)`: the fixed point `Hᵛ_λ(p + 1 + t')`
          push Not at hσp
          obtain ⟨δ, hδ⟩ := exists_add_of_le hσp
          rw [hδ] at hσK
          have hδo := (add_lt_add_iff_left _).1 hσK
          set p := qdFpH (qdLev E) (qdI (qdLev E) E) with hpdef
          set o := qdI (qdLev E) E - (p + 1) with hodef
          have ho0 : o ≠ 0 := by
            intro h; rw [h, vD_zero] at hδo; exact absurd hδo (not_lt.2 zero_le)
          have hoE : o < E := (Ordinal.sub_le_self _ _).trans_lt hyE
          obtain ⟨t', ht'o, hgt', hδt'⟩ := qd_below S hE hBE hEB hlim hIH hx hx1 hoE ho0 hgo δ hδo
          have hpy1 : p + 1 ≤ qdI (qdLev E) E := Order.add_one_le_of_lt hpy
          have hzy : p + 1 + t' < qdI (qdLev E) E := by
            have h := (add_lt_add_iff_left (p + 1)).2 ht'o
            rwa [hodef, Ordinal.add_sub_cancel_of_le hpy1] at h
          have hpz : p < p + 1 + t' := (lt_add_one p).trans_le le_self_add
          have hzr : p + 1 + t' < qdH (qdLev E) (p + 1 + t') := by
            refine lt_of_le_of_ne (qdH_le_self _ _) fun h => ?_
            exact absurd (hle_y _ h.symm hzy) (not_le.2 hpz)
          have hFz : QdFixH (qdLev E) (p + 1 + t') := ⟨p, hpf, hpz⟩
          have hpz' : qdFpH (qdLev E) (p + 1 + t') = p := by
            refine le_antisymm (csSup_le ⟨p, hpf, hpz⟩ fun f' hf' => hle_y f' hf'.1 (hf'.2.trans hzy)) ?_
            exact le_csSup ⟨_, fun _ h => h.2.le⟩ ⟨hpf, hpz⟩
          have hK : qdRK (qdLev E) (p + 1 + t') x = vD p x + vD t' x := by
            unfold qdRK; rw [if_pos hFz, hpz', Ordinal.add_sub_cancel]
          have hXa : ucB ≤ qdH (qdLev E) (p + 1 + t') :=
            (hpB2.trans hpz.le).trans (qdH_le_self _ _)
          obtain ⟨haE, hrda⟩ := hrdE _ hzy hzr hXa
          have hzB : p + 1 + t' < qdB := (hzy.trans hyE).trans hEB
          have hgz : qdGt (p + 1 + t') < x :=
            qd_add hxP hωx _ _ hzB (qd_add hxP hωx _ _ (le_self_add.trans_lt hzB) hgp h1g) hgt'
          obtain ⟨hpT, hp1, -⟩ := qd_T S hE hBE hEB hlim hIH hx hx1 hpE hgp
          obtain ⟨ht'T, ht'1, -⟩ := qd_T S hE hBE hEB hlim hIH hx hx1 (ht'o.trans hoE) hgt'
          refine ⟨_, haE, qd_H_gate S hx hl0 hlG hzr hXa (haE.trans hEB) (fun d hd => (hcomp d hd).2) hgz, ?_⟩
          rw [hrda, hK, ← hM'v]
          exact hsame _ (vzT_add hx hx1 hpT ht'T) ((inE_indec gl_Om1_E).add_lt hp1 ht'1)
            (by rw [hδ]; exact (add_le_add_iff_left _).2 hδt')
      · -- no fixed point of `Hᵛ_λ` below `y`: a smaller argument `s' < y`
        unfold qdRK at hσK
        rw [if_neg hF] at hσK
        have hgy := (hg0y hF).trans_lt hgx
        have hy0 : qdI (qdLev E) E ≠ 0 := by
          intro h; rw [h, vD_zero] at hσK; exact absurd hσK (not_lt.2 zero_le)
        obtain ⟨s', hs'y, hgs', hσs'⟩ := qd_below S hE hBE hEB hlim hIH hx hx1 hyE hy0 hgy σ' hσK
        have hzr : s' < qdH (qdLev E) s' :=
          lt_of_le_of_ne (qdH_le_self _ _) fun h => hF ⟨s', h.symm, hs'y⟩
        have hnF : ¬ QdFixH (qdLev E) s' := fun ⟨f, h1, h2⟩ => hF ⟨f, h1, h2.trans hs'y⟩
        have hXa : ucB ≤ qdH (qdLev E) s' := by
          refine qd_H_ge_B2 S (Or.inr fun hv => hF ?_)
          obtain ⟨hfixB, hBy⟩ := hvisB hv
          exact ⟨ucB, hfixB, hBy⟩
        obtain ⟨haE, hrda⟩ := hrdE _ hs'y hzr hXa
        obtain ⟨hs'T, hs'1, -⟩ := qd_T S hE hBE hEB hlim hIH hx hx1 (hs'y.trans hyE) hgs'
        refine ⟨_, haE, qd_H_gate S hx hl0 hlG hzr hXa (haE.trans hEB) (fun d hd => (hcomp d hd).2) hgs', ?_⟩
        rw [hrda, ← hM'v]
        unfold qdRK
        rw [if_neg hnF]
        exact hsame _ hs'T hs'1 hσs'
  obtain ⟨a, haE, hga, hua⟩ := key
  exact absurd (hu1 a haE hga) (not_lt.2 hua)

end Fix

end Googology.Trans.PoR.InaccPsi.R2.Qd
