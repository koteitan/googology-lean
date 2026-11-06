import Googology.Trans.PoR.InaccPsi.R2.VaAll
import Googology.Trans.PoR.InaccPsi.R2.ZmRS

/-!
# VaLay: THE LAYER AT A FIXED POINT OF `Γ` AND THE BASE LAYER ABOVE IT

A layer at a fixed point `F ∈ [B_Γ, X)` of `Γ` (`VsLay S F`: gate the gate of `F`, top reading `vR F`, reading `F` with
the atoms of `Zb.zbU`, terms for every code below `F`) gives the base layer of the segment of `F`: the ladder
`Yw.ywLadB` over it with `e(x) = F(x)` (a closed point), a `Zm.ZmBase` for every digit system over the segment base
`F` (`vsBase`).

* `vs_fix_lim`, `vs_DF` (**the facts of the reading `F(x)`**), `vs_DF_pi`, `vs_F_tl`, `vs_F_atom`;
* `VsLay`, `vsLay_BG` (**`B_Γ`**: `Yw.ywBGB`), `vs_ladH` (the ladder hypothesis), `vsBase` (**the base layer of the
  segment**).

No new axiom.  New definitions: `VsLay`, `vsBase`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Googology.Trans.PoR.InaccPsi.R2.Va

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Tf Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Yr Googology.Trans.PoR.InaccPsi.R2.Yw Googology.Trans.PoR.InaccPsi.R2.Gd
  Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Zb
  Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Yh Googology.Trans.PoR.InaccPsi.R2.Zm
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Xk Googology.Trans.PoR.InaccPsi.R2.Gm
  Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Trans.PoR.InaccPsi.R2.Gs

/-! ## The reading of a fixed point of `Γ` -/

/-- A fixed point of `Γ` is a limit of `ε`-numbers. -/
theorem vs_fix_lim {F : Ordinal.{0}} (hF : gamma F = F) : ∀ e, InE e → e < F → eN e < F :=
  fun _ _ he => zm_eN_lt_fix he (zm_fix_of_gamma hF)

section DF

variable {F : Ordinal.{0}} (hF : gamma F = F) (hBF : tfBG ≤ F) (hFX : F < tlX)
include hF hBF hFX

/-- **The facts of the reading `F(x)` of a fixed point `F ≥ B_Γ` of `Γ` above its gate**: a closed point of
`Tˣ ∩ (x, X^x)`. -/
theorem vs_DF {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hgx : max ω (yrQE F) < x) :
    vR F x ∈ Tset x ∧ InE (vR F x) ∧ x < vR F x ∧ vR F x < ywX x ∧ YwClosed x (vR F x) ∧ vR F x < Om1 := by
  rcases hBF.lt_or_eq with hlt | heq
  · have hOF : Om1 < F := tfBG_gt.trans hlt
    have hA : YhAt F := ⟨by rw [← hF]; exact Lq.lq_gamma_SC _, hOF⟩
    have hi : ¬ yhJ F < F := by
      have h := yhJ_gcG F; rw [vs_gcG_fix hF hOF] at h; rw [h]; exact lt_irrefl _
    have hFE : InE F := zm_fix_E (zm_fix_of_gamma hF)
    obtain ⟨-, hcl, hVT, hVE, hxV, hVX, hV1⟩ := vs_fx_V hFE hlt hFX (vs_fix_lim hF)
      (fun e he heB heE => vsGood_all3 e he heB (heE.trans hFX)) hA hi hx hx1 hgx
    rw [vR_base hFE (va_G_le_BG.trans hBF)]
    exact ⟨hVT, hVE, hxV, hVX, hcl, hV1⟩
  · subst heq
    rw [vR_BG]
    obtain ⟨hDT, hDE, hxD, hDX⟩ := zmD_T hx hx1
    exact ⟨hDT, hDE, hxD, hDX, (ywD_closed hx hx1).2.2, hDX.trans (ywX_facts hx hx1).2.2.1⟩

/-- **The reading of a fixed point is exact.** -/
theorem vs_DF_pi {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) (hgσ : max ω (yrQE F) < σ) :
    vR F ρ ∈ TB ρ σ ∧ R2.pi σ ρ (vR F ρ) = vR F σ := by
  rcases hBF.lt_or_eq with hlt | heq
  · have hOF : Om1 < F := tfBG_gt.trans hlt
    have hA : YhAt F := ⟨by rw [← hF]; exact Lq.lq_gamma_SC _, hOF⟩
    have hi : ¬ yhJ F < F := by
      have h := yhJ_gcG F; rw [vs_gcG_fix hF hOF] at h; rw [h]; exact lt_irrefl _
    have hFE : InE F := zm_fix_E (zm_fix_of_gamma hF)
    have hG : gcG 0 ≤ F := va_G_le_BG.trans hBF
    rw [vR_base hFE hG, vR_base hFE hG]
    exact vs_fx_pi hFE hlt hFX (vs_fix_lim hF) (fun e he heB heE => vsGood_all3 e he heB (heE.trans hFX)) hA hi
      hB hgσ
  · subst heq
    rw [vR_BG, vR_BG]
    exact zmD_pi hB

/-- **A fixed point is a code over every strongly critical `Z` above its gate.** -/
theorem vs_F_tl {Z : Ordinal.{0}} (hZ : SC Z) (hgZ : max ω (yrQE F) < Z) : TlCl Z F := by
  rcases hBF.lt_or_eq with hlt | heq
  · have hOF : Om1 < F := tfBG_gt.trans hlt
    have hA : YhAt F := ⟨by rw [← hF]; exact Lq.lq_gamma_SC _, hOF⟩
    have hi : ¬ yhJ F < F := by
      have h := yhJ_gcG F; rw [vs_gcG_fix hF hOF] at h; rw [h]; exact lt_irrefl _
    have hFE : InE F := zm_fix_E (zm_fix_of_gamma hF)
    exact vs_fx_cl hFE hlt hFX (vs_fix_lim hF) (fun e he heB heE => vsGood_all3 e he heB (heE.trans hFX)) hA hi hZ
      hgZ
  · subst heq; exact zbBG_tl hZ.1

/-- **A fixed point is an atom of `zbU` over every strongly critical `Z` above its gate.** -/
theorem vs_F_atom {Z : Ordinal.{0}} (hZ : SC Z) (hgZ : max ω (yrQE F) < Z) : GxCl Z (zbU.At Z) F := by
  have hSC : SC F := by rw [← hF]; exact Lq.lq_gamma_SC _
  have hOF : Om 1 < F := by rw [← Br.Om1_eq]; exact tfBG_gt.trans_le hBF
  exact GxCl.atom (Or.inl ⟨hSC, hOF, hFX, vs_F_tl hF hBF hFX hZ hgZ⟩)

end DF

/-! ## The layer at a fixed point -/

/-- **A layer at the fixed point `F`**: gate the gate of `F`, top reading `vR F`, reading `F` with the atoms of
`zbU`, terms for every code below `F`. -/
def VsLay (S : InaccSeq.{0}) (F : Ordinal.{0}) : Prop :=
  ∃ L : GdB, L.g = max ω (yrQE F) ∧ (∀ x, InE x → x < Om1 → L.g < x → L.K.E x = vR F x) ∧
    (∀ y, SC y → y < Om 1 → L.g < y → L.K.E y = gxTh y (zbU.At y) F) ∧ ZbPolyG zbU L.K.sys F

/-- **The layer at `B_Γ`** (`Yw.ywBGB`). -/
theorem vsLay_BG (S : InaccSeq.{0}) : VsLay S tfBG := by
  have h : ywBGB.g ≤ max ω (yrQE tfBG) := by rw [ywBGB_g]; exact zero_le
  exact ⟨ywBGB.mono h, rfl, fun x _ _ _ => by show ywV 1 0 x = vR tfBG x; exact (vR_BG x).symm,
    fun y hy hy1 _ => zbBG_top S hy hy1, (zbBG_poly S).mono h⟩

/-- **The ladder hypothesis over a layer at `F`** with `e(x) = F(x)`. -/
theorem vs_ladH {F : Ordinal.{0}} (hF : gamma F = F) (hBF : tfBG ≤ F) (hFX : F < tlX) (U : GdB)
    (hUg : U.g = max ω (yrQE F)) (hUE : ∀ x, InE x → x < Om1 → U.g < x → U.K.E x = vR F x) :
    YwLH U (fun x => vR F x) := by
  refine ⟨fun x hx hx1 hg => ?_, fun x hx hx1 hg => ?_, fun x hx hx1 hg j hjT hj => ?_, fun x hx hx1 hg => ?_,
    fun x hx hx1 hg => ?_, fun σ ρ hB hg => ?_⟩
  · obtain ⟨hT, -, -, -, -, h1⟩ := vs_DF hF hBF hFX hx hx1 (hUg ▸ hg); exact ⟨hT, h1⟩
  · rw [hUE x hx hx1 hg]
  · obtain ⟨-, -, -, -, hcl, -⟩ := vs_DF hF hBF hFX hx hx1 (hUg ▸ hg)
    rw [hUE x hx hx1 hg]; exact (hcl j hjT hj).le
  · obtain ⟨hT, -, -, -, -, h1⟩ := vs_DF hF hBF hFX hx hx1 (hUg ▸ hg)
    rw [hUE x hx hx1 hg]; exact gmq_gt hx hx1 hT h1
  · obtain ⟨hT, -, -, hX, -, h1⟩ := vs_DF hF hBF hFX hx hx1 (hUg ▸ hg)
    exact Qc.qcBd_of_X hx (zm_gq_lt_X hx hx1 hT h1 hX)
  · exact vs_DF_pi hF hBF hFX hB (hUg ▸ hg)

/-- **THE BASE LAYER OF THE SEGMENT OF `F`**: the ladder over a layer at `F`, for a digit system over the segment
base `F` read `vR F`. -/
noncomputable def vsBase (S : InaccSeq.{0}) {F : Ordinal.{0}} (hF : gamma F = F) (hBF : tfBG ≤ F) (hFX : F < tlX)
    (hL : VsLay S F) (M : ZmDS) (hMB : M.B = F) (hMD : M.Dv = vR F) (hEg : max ω (yrQE F) ≤ M.Eg) :
    ZmDS.ZmBase S M where
  L0 := ywLadB (Classical.choose hL) (fun x => vR F x)
    (vs_ladH hF hBF hFX _ (Classical.choose_spec hL).1 (Classical.choose_spec hL).2.1)
  L0_g := by rw [ywLadB_g, (Classical.choose_spec hL).1]; exact hEg
  L0_E := fun x _ _ => by rw [ywLadB_E, hMD]
  L0_top := fun y hy hy1 hgy => by
    obtain ⟨hUg, -, hUtop, -⟩ := Classical.choose_spec hL
    have hc : ∀ Z, SC Z → (Classical.choose hL).g < Z → GxCl Z (zbU.At Z) F := fun Z hZ hgZ =>
      vs_F_atom hF hBF hFX hZ (hUg ▸ hgZ)
    have hcQ : Ga.cQs F = gcG (F + 1) := by
      conv_lhs => rw [← vs_gcG_fix hF (tfBG_gt.trans_le hBF)]
      exact gc_cQs F
    rw [zbLad_top hc hUtop _ hy hy1 (hUg.trans_lt (hEg.trans_lt hgy)), hMB, hcQ]
  L0_poly := by
    obtain ⟨hUg, -, hUtop, hUP⟩ := Classical.choose_spec hL
    have hc : ∀ Z, SC Z → (Classical.choose hL).g < Z → GxCl Z (zbU.At Z) F := fun Z hZ hgZ =>
      vs_F_atom hF hBF hFX hZ (hUg ▸ hgZ)
    have hcO : Om 1 ≤ F := by rw [← Br.Om1_eq]; exact (tfBG_gt.trans_le hBF).le
    have h := zbLad_poly hc hcO hUtop (vs_ladH hF hBF hFX _ hUg (Classical.choose_spec hL).2.1) zbU_th hUP
    have hcQ : Ga.cQs F = gcG (F + 1) := by
      conv_lhs => rw [← vs_gcG_fix hF (tfBG_gt.trans_le hBF)]
      exact gc_cQs F
    rw [hMB]; rwa [hcQ] at h
  Dv_ge := fun x hx hx1 hgx => by
    obtain ⟨-, -, hxF, -, hcl, -⟩ := vs_DF hF hBF hFX hx hx1 (hEg.trans_lt hgx)
    rw [hMD]; exact (ywBG hx hx1).2.2 _ hxF hcl

/-! ## The layers at the atom indices of a segment -/

/-- **A layer at the atom index `c`** past its segment base `F = vaFB c`: reading `gq(F(x) + o(x))`, `o = c − (F+1)`,
top code `gcG c`; its gate is above the gates of `F` and `o`, and below every limit above the gate of `c`. -/
def VsAt (S : InaccSeq.{0}) (c : Ordinal.{0}) : Prop :=
  ∃ L : GdB, (∀ Z, IsSuccLimit Z → ω < Z → yrG c < Z → L.g < Z) ∧
    (∀ x, L.g < x → yrG (vaFB c) < x ∧ yrG (c - (vaFB c + 1)) < x) ∧
    (∀ x, InE x → x < Om1 → L.g < x → L.K.E x = gq (vR (vaFB c) x + vR (c - (vaFB c + 1)) x) x) ∧
    (∀ y, SC y → y < Om 1 → L.g < y → L.K.E y = gxTh y (zbU.At y) (gcG c)) ∧ ZbPolyG zbU L.K.sys (gcG c)

/-- **The layer at an atom index of a segment**, from the layer at its segment base: the reading system of the
digit system at `ε_{e+1}` (`e` the bracket of `c`) over the base `F` (`Zm.ZmDS.toRS` with `vsBase`). -/
theorem vsAt_of (S : InaccSeq.{0}) {c : Ordinal.{0}} (hBc : tfBG ≤ c) (hFc : vaFB c < c) (hcX : c < tlX)
    (hL : VsLay S (vaFB c)) : VsAt S c := by
  have hGc : gcG 0 ≤ c := va_G_le_BG.trans hBc
  have hFfix := vs_FB_fix hBc
  have hBF := vs_FB_ge hBc
  have hFX : vaFB c < tlX := hFc.trans hcX
  have heB : vaFB c ≤ guE c := gl_E_max (vs_FB_E hBc) (vs_FB_gt hBc) (vs_FB_le hBc)
  have hec : guE c ≤ c := gl_E_le (yh_gfE_le hGc)
  have hce : c < eN (guE c) := gl_lt_eN (yh_gfE_le hGc)
  have heE := guE_E c
  have hBe : tfBG ≤ guE c := hBF.trans heB
  have hE'X : eN (guE c) < tlX :=
    zm_eN_lt_fix (hec.trans_lt hcX) (zm_fix_of_gamma tl_gamma_X)
  have hBE' : tfBG ≤ eN (guE c) := hBe.trans (lt_eN _).le
  obtain ⟨M, hME, hEg, hV, hR, hG, hMB, hMD⟩ := vsGood_all3 _ (eN_E _) hBE' hE'X
  have hFB' : vaFB (eN (guE c)) = vaFB c := by
    rw [vs_FB_eN hBe]; exact vs_FB_of_le hBc heB hec
  rw [hFB'] at hMB hMD
  have hEgF : max ω (yrQE (vaFB c)) ≤ M.Eg := by
    rw [hEg]
    have h := vs_FB_gate (eN (guE c)) hBE'
    rw [hFB', yrG_base (vs_FB_E hBc) (va_G_le_BG.trans hBF),
      yrG_base (eN_E _) (va_G_le_BG.trans hBE')] at h
    exact max_le (le_max_left _ _) h
  have hBME : M.B < M.E := by rw [hMB, hME]; exact hFc.trans hce
  have hc0 : M.B + 1 ≤ c := by rw [hMB]; exact Order.add_one_le_of_lt hFc
  have hcBd : c < M.E := by rw [hME]; exact hce
  set RS := M.toRS S hBME (vsBase S hFfix hBF hFX hL M hMB hMD hEgF) with hRS
  obtain ⟨L, hLg, hLE, hLtop, hLP⟩ := RS.lay c hc0 hcBd
  have hgt : RS.gt c = max M.Eg (M.G (c - (vaFB c + 1))) := by
    show max M.Eg (M.G (c - (M.B + 1))) = _; rw [hMB]
  have hoE : c - (vaFB c + 1) < eN (guE c) := (Ordinal.sub_le_self _ _).trans_lt hce
  refine ⟨L, fun Z hZ hωZ hgZ => ?_, fun x hgx => ?_, fun x hx hx1 hgx => ?_, fun y hy hy1 hgy => ?_, hLP⟩
  · -- the gate is below every limit above the gate of `c`
    have hQ : yrQE (guE c) < Z := by
      rw [yrG_dec hGc] at hgZ; exact (le_max_left _ _).trans_lt ((le_max_left _ _).trans_lt hgZ)
    have hEgZ : M.Eg < Z := by rw [hEg]; exact max_lt hωZ (vs_QE_eN_lt heE hBe hZ hωZ hQ)
    rw [hLg, hgt]
    refine max_lt hEgZ ?_
    rcases eq_or_ne (c - (vaFB c + 1)) 0 with h0 | h0
    · rw [h0, M.G0]; exact hZ.bot_lt
    · rw [hG _ hoE h0]
      exact max_lt hEgZ ((vs_off_gate (vs_FB_E hBc) (va_G_le_BG.trans hBF) hFc).trans_lt (max_lt hωZ hgZ))
  · -- the gates of the base and of the offset are below the gate
    rw [hLg, hgt] at hgx
    have hEgx : M.Eg < x := (le_max_left _ _).trans_lt hgx
    refine ⟨?_, ?_⟩
    · rw [yrG_base (vs_FB_E hBc) (va_G_le_BG.trans hBF)]
      exact (le_max_right _ _).trans_lt (hEgF.trans_lt hEgx)
    · rcases eq_or_ne (c - (vaFB c + 1)) 0 with h0 | h0
      · rw [h0, yrG_zero]; exact (zero_le).trans_lt hEgx
      · have h := (le_max_right _ _).trans_lt hgx
        rw [hG _ hoE h0] at h
        exact (le_max_right _ _).trans_lt h
  · -- the reading
    have hgx' : RS.gt c < x := by rw [← hLg]; exact hgx
    rw [hLE x hx hx1 hgx']
    have hgo : M.G (c - (vaFB c + 1)) < x := by rw [hgt] at hgx'; exact (le_max_right _ _).trans_lt hgx'
    show gq (M.Dv x + M.R (c - (M.B + 1)) x) x = _
    rw [hMB, hMD, hR _ hoE x hx hx1 hgo]
  · exact hLtop y hy hy1 (by rw [← hLg]; exact hgy)

/-! ## The layer at a fixed point: the union of the atom layers below it -/

/-- **The atom index above a code `b`**: `F' + 1 + b'`, `b' = max b B_Γ`, `F' = vaFB b'`. -/
noncomputable def vsCb (b : Ordinal.{0}) : Ordinal.{0} := vaFB (max b tfBG) + 1 + max b tfBG

/-- `F + 1 + b` lies in the segment of `F = vaFB b`. -/
theorem vs_seg_shift {b : Ordinal.{0}} (hbB : tfBG ≤ b) : vaFB (vaFB b + 1 + b) = vaFB b := by
  have hFb : vaFB b ≤ b := vs_FB_le hbB
  refine vs_FB_eq (vs_FB_fix hbB) (vs_FB_gt hbB) (le_self_add.trans le_self_add) fun y' h1 h2 hy' => ?_
  rcases le_or_gt y' b with hyb | hyb
  · exact absurd (vs_FB_max hbB hy' ((vs_FB_gt hbB).trans h1) hyb) (not_le.2 h1)
  · have hyE : InE y' := zm_fix_E (zm_fix_of_gamma hy')
    have h3 : vaFB b + 1 + b < y' :=
      (inE_indec hyE).add_lt ((inE_indec hyE).add_lt (hFb.trans_lt hyb) (lu_one_lt_E hyE)) hyb
    exact absurd h2 (not_le.2 h3)

theorem vs_cb_facts {b F : Ordinal.{0}} (hF : gamma F = F) (hBF : tfBG < F) (hb : b < F) :
    tfBG ≤ vsCb b ∧ vaFB (vsCb b) = vaFB (max b tfBG) ∧ vaFB (vsCb b) < vsCb b ∧ vsCb b < F ∧
      vsCb b - (vaFB (vsCb b) + 1) = max b tfBG ∧ max b tfBG ≤ vsCb b ∧ vsCb b < gcG (vsCb b) := by
  have hbB : tfBG ≤ max b tfBG := le_max_right _ _
  have hb' : max b tfBG < F := max_lt hb hBF
  have hFE : InE F := zm_fix_E (zm_fix_of_gamma hF)
  have hseg := vs_seg_shift hbB
  have hlt : vaFB (vsCb b) < vsCb b := by
    unfold vsCb; rw [hseg]; exact (lt_add_one _).trans_le le_self_add
  have hBc : tfBG ≤ vsCb b := hbB.trans le_add_self
  refine ⟨hBc, hseg, hlt, ?_, by unfold vsCb; rw [hseg, Ordinal.add_sub_cancel], le_add_self, ?_⟩
  · exact (inE_indec hFE).add_lt ((inE_indec hFE).add_lt ((vs_FB_le hbB).trans_lt hb') (lu_one_lt_E hFE)) hb'
  · have hj' : Om1 + 1 + vsCb b = vsCb b := by
      obtain ⟨d, hd⟩ := exists_add_of_le hBc
      rw [hd, ← add_assoc, gl_absorb (Low.opow_eq_self_of_SC tfBG_SC) tfBG_gt]
    rw [tf_gcG, hj']
    exact lt_of_le_of_ne isNormal_gamma.strictMono.le_apply fun h => vs_FB_nfx hBc hlt le_rfl h.symm

/-- **The gate of `vsCb b`** stays below every `ε`-number above the gate of `b`. -/
theorem vs_cb_gate {b Z : Ordinal.{0}} (hZ : InE Z) (hgb : yrG b < Z) : yrG (vsCb b) < Z := by
  have hωZ : ω < Z := omega0_lt_inE hZ
  have hZP : ∀ u v, u < Z → v < Z → u + v < Z := fun u v hu hv => (inE_indec hZ).add_lt hu hv
  have hbB : tfBG ≤ max b tfBG := le_max_right _ _
  have hgb' : yrG (max b tfBG) < Z := by
    rcases le_total b tfBG with h | h
    · rw [max_eq_right h, yrG_base (Low.opow_eq_self_of_SC tfBG_SC) va_G_le_BG, va_QE_BG]; exact hZ.pos
    · rw [max_eq_left h]; exact hgb
  have hgF : yrG (vaFB (max b tfBG)) < Z := (vs_FB_gate _ hbB).trans_lt (max_lt hωZ hgb')
  have h1 : yrG (1 : Ordinal.{0}) < Z := by
    rw [show (1 : Ordinal.{0}) = ((1 : ℕ) : Ordinal.{0}) by norm_num, va_nat_gate]
    exact (natCast_lt_omega0 1).trans hωZ
  exact yr_add hZP hωZ _ _ (yr_add hZP hωZ _ _ hgF h1) hgb'

/-- **A code over the atoms of `zbU` is a code of `TlCl`.** -/
theorem vs_gx_tl {Z d : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om1) (hd : GxCl Z (zbU.At Z) d) : TlCl Z d := by
  induction hd with
  | small h => exact TlCl.small h
  | om => rw [← Br.Om1_eq]; exact TlCl.om
  | atom hs =>
    rcases hs with hs | ⟨c, hc, hg, rfl⟩
    · exact hs.2.2.2
    · have hcT : TlCl Z c := zmYr.cl c Z hZ hc hg
      have harg : TlCl Z (Om1 + 1 + c) := TlCl.add (TlCl.add TlCl.om (TlCl.one hZ.1)) hcT
      rw [tf_gcG]
      exact TlCl.gam hZ.1 harg ((lt_add_one _).trans_le le_self_add)
  | add _ _ ih1 ih2 => exact TlCl.add ih1 ih2
  | phi _ _ ih1 ih2 => exact TlCl.phi ih1 ih2

section Fix

variable {F : Ordinal.{0}} (hF : gamma F = F) (hBF : tfBG < F) (hFX : F < tlX)
include hF hBF hFX

theorem vs_F_data : InE F ∧ YhAt F ∧ ¬ yhJ F < F ∧ (∀ e, InE e → tfBG ≤ e → e < F → VsGood e) := by
  have hOF : Om1 < F := tfBG_gt.trans hBF
  refine ⟨zm_fix_E (zm_fix_of_gamma hF), ⟨by rw [← hF]; exact Lq.lq_gamma_SC _, hOF⟩, ?_,
    fun e he heB heE => vsGood_all3 e he heB (heE.trans hFX)⟩
  have h := yhJ_gcG F; rw [vs_gcG_fix hF hOF] at h; rw [h]; exact lt_irrefl _

theorem vs_F_T {x c : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hc : c < F) (hg : yrG c < x) :
    vR c x ∈ Tset x ∧ vR c x < Om1 ∧ vR c x < ywX x := by
  obtain ⟨hFE, -, -, hIH⟩ := vs_F_data hF hBF hFX
  exact vs_T hFE hBF (vs_fix_lim hF) hIH hx hx1 hc hg

theorem vs_F_lt {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hgx : max ω (yrQE F) < x) :
    ∀ c, c < F → yrG c < x → vR c x < vR F x := by
  obtain ⟨hFE, hA, hi, hIH⟩ := vs_F_data hF hBF hFX
  intro c hc hg
  rw [vR_base hFE (va_G_le_BG.trans hBF.le)]
  exact vs_fx_lt hFE hBF hFX (vs_fix_lim hF) hIH hA hi hx hx1 hgx c hc hg

theorem vs_F_top {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hgx : max ω (yrQE F) < x) :
    ∀ ν, ν < vR F x → ∃ b, b < F ∧ yrG b < x ∧ ν ≤ vR b x := by
  obtain ⟨hFE, hA, hi, hIH⟩ := vs_F_data hF hBF hFX
  intro ν hν
  rw [vR_base hFE (va_G_le_BG.trans hBF.le)] at hν
  exact vs_fx_top hFE hBF hFX (vs_fix_lim hF) hIH hA hi hx hx1 hgx ν hν

variable (S : InaccSeq.{0}) (hAt : ∀ b, b < F → VsAt S (vsCb b))

/-- **The union data at a fixed point**: the atom layers `vsCb b`, `b < F`, and the layer of `B_Γ` for the
constants; target `F(x)`. -/
noncomputable def vsLayF : YwUF (max ω (yrQE F)) where
  I := Option {b : Ordinal.{0} // b < F}
  K := fun i => Option.elim i ywBGB fun b => Classical.choose (hAt b.1 b.2)
  gi := fun i => Option.elim i 0 fun b => (Classical.choose (hAt b.1 b.2)).g
  i0 := none
  g_le := fun i => by
    cases i with
    | none => exact le_of_eq ywBGB_g
    | some b => exact le_rfl
  gi0 := rfl
  T := fun x => vR F x
  T_E := fun x hx hx1 hg => (vs_DF hF hBF.le hFX hx hx1 hg).2.1
  T_mem := fun x hx hx1 hg => (vs_DF hF hBF.le hFX hx hx1 hg).1
  T_gt := fun x hx hx1 hg => (vs_DF hF hBF.le hFX hx hx1 hg).2.2.1
  T_X := fun x hx hx1 hg => Qc.qcBd_of_X hx (vs_DF hF hBF.le hFX hx hx1 hg).2.2.2.1
  E_lt := fun i x hx hx1 hg hgi => by
    cases i with
    | none =>
      show ywBGB.K.E x < vR F x
      rw [ywBGB_E, ← vR_BG x]
      refine vs_F_lt hF hBF hFX hx hx1 hg _ hBF ?_
      rw [yrG_base (Low.opow_eq_self_of_SC tfBG_SC) va_G_le_BG, va_QE_BG]; exact hx.pos
    | some b =>
      obtain ⟨-, hgo, hE, -, -⟩ := Classical.choose_spec (hAt b.1 b.2)
      obtain ⟨-, -, hlt, hcF, -, -, -⟩ := vs_cb_facts hF hBF b.2
      obtain ⟨hgF', hgo'⟩ := hgo x hgi
      show (Classical.choose (hAt b.1 b.2)).K.E x < vR F x
      rw [hE x hx hx1 hgi]
      obtain ⟨hDT, -, -, -, hcl, hD1⟩ := vs_DF hF hBF.le hFX hx hx1 hg
      have h1 := vs_F_lt hF hBF hFX hx hx1 hg _ (hlt.trans hcF) hgF'
      have h2 := vs_F_lt hF hBF hFX hx hx1 hg _ ((Ordinal.sub_le_self _ _).trans_lt hcF) hgo'
      have hsum := (inE_indec (vs_DF hF hBF.le hFX hx hx1 hg).2.1).add_lt h1 h2
      exact hcl _ (vz_T_down hx hx1 hDT hD1 hsum.le) hsum
  cof := fun x hx hx1 hg v hv => by
    obtain ⟨b, hb, hgb, hvb⟩ := vs_F_top hF hBF hFX hx hx1 hg v hv
    obtain ⟨hgate, hgo, hE, -, -⟩ := Classical.choose_spec (hAt b hb)
    obtain ⟨-, hseg, -, -, hsub, -, -⟩ := vs_cb_facts hF hBF hb
    have hgL : (Classical.choose (hAt b hb)).g < x :=
      hgate x (ev_isSuccLimit_of_inE hx) (omega0_lt_inE hx) (vs_cb_gate hx hgb)
    refine ⟨some ⟨b, hb⟩, hgL, ?_⟩
    show v < (Classical.choose (hAt b hb)).K.E x
    rw [hE x hx hx1 hgL, hsub, hseg]
    obtain ⟨hgF', hgb'⟩ := hgo x hgL
    rw [hsub] at hgb'
    rw [hseg] at hgF'
    have hb'F : max b tfBG < F := max_lt hb hBF
    obtain ⟨hb'T, hb'1, -⟩ := vs_F_T hF hBF hFX hx hx1 hb'F hgb'
    obtain ⟨hFT, hF1, -⟩ := vs_F_T hF hBF hFX hx hx1 ((vs_FB_le (le_max_right _ _)).trans_lt hb'F) hgF'
    have hvb' : v ≤ vR (max b tfBG) x := by
      rcases lt_or_ge b tfBG with h | h
      · rw [max_eq_right h.le]
        refine hvb.trans (le_of_lt ?_)
        rw [vR_yr b h x, vR_BG]; exact zmYr.lt b x hx hx1 h hgb
      · rw [max_eq_left h]; exact hvb
    exact hvb'.trans_lt ((gmq_gt hx hx1 hb'T hb'1).trans_le
      (gmq_mono hx hx1 (vzT_add hx hx1 hFT hb'T) ((inE_indec gl_Om1_E).add_lt hF1 hb'1) le_add_self))
  pi := fun σ ρ _ _ hB hg => vs_DF_pi hF hBF.le hFX hB hg

end Fix

/-- **THE LAYER AT A FIXED POINT OF `Γ` ABOVE `B_Γ`**: the union of the atom layers below it. -/
theorem vsLay_union (S : InaccSeq.{0}) {F : Ordinal.{0}} (hF : gamma F = F) (hBF : tfBG < F) (hFX : F < tlX)
    (hAt : ∀ b, b < F → VsAt S (vsCb b)) : VsLay S F := by
  set Fu := vsLayF hF hBF hFX S hAt with hFu
  have hres := zbUnion_codes (A := zbU) Fu (fun i => Option.elim i tfBG fun b => gcG (vsCb b.1)) (Tc := F)
    (fun i y hy hy1 hi => by
      cases i with
      | none => exact zbBG_top S hy hy1
      | some b => exact (Classical.choose_spec (hAt b.1 b.2)).2.2.2.1 y hy hy1 hi)
    (fun i => by
      cases i with
      | none => exact zbBG_poly S
      | some b => exact (Classical.choose_spec (hAt b.1 b.2)).2.2.2.2)
    (fun i => by
      cases i with
      | none => exact hBF.le
      | some b =>
        obtain ⟨-, -, -, hcF, -, -, -⟩ := vs_cb_facts hF hBF b.2
        exact (gcG_lt hcF).le.trans (vs_gcG_fix hF (tfBG_gt.trans hBF)).le)
    (fun Z hZ hZ1 hgZ d hd hdT => by
      have hZ1' : Z ≤ Om1 := by rw [Br.Om1_eq]; exact hZ1.le
      have hZE : InE Z := Low.opow_eq_self_of_SC hZ
      have hgd : yrG d < Z := vs_gate hZ hZ1' d (vs_gx_tl hZ hZ1' hd) (hdT.trans hFX)
      obtain ⟨hgate, -⟩ := Classical.choose_spec (hAt d hdT)
      obtain ⟨-, -, -, -, -, hdc, hcg⟩ := vs_cb_facts hF hBF hdT
      refine ⟨some ⟨d, hdT⟩, hgate Z (ev_isSuccLimit_of_inE hZE) (omega0_lt_inE hZE) (vs_cb_gate hZE hgd), ?_⟩
      show d < gcG (vsCb d)
      exact ((le_max_left d tfBG).trans hdc).trans_lt hcg)
  exact ⟨ywLimB Fu, rfl, fun x _ _ _ => rfl, hres.1, hres.2⟩

/-- **A LAYER AT EVERY FIXED POINT `B_Γ ≤ F < X` OF `Γ`**: one induction over the fixed points (the layers at the
atom indices below `F` from the layers at their segment bases, `vsAt_of`). -/
theorem vsLay_all (S : InaccSeq.{0}) : ∀ F, gamma F = F → tfBG ≤ F → F < tlX → VsLay S F := by
  intro F
  induction F using WellFoundedLT.induction with
  | ind F IH =>
  intro hF hBF hFX
  rcases hBF.lt_or_eq with hlt | heq
  · refine vsLay_union S hF hlt hFX fun b hb => ?_
    obtain ⟨hBc, -, hlt', hcF, -, -, -⟩ := vs_cb_facts hF hlt hb
    exact vsAt_of S hBc hlt' (hcF.trans hFX)
      (IH _ (hlt'.trans hcF) (vs_FB_fix hBc) (vs_FB_ge hBc) ((hlt'.trans hcF).trans hFX))
  · rw [← heq]; exact vsLay_BG S

/-! ## `ZbDirect S X` -/

/-- **The layer for the index `F`**, a fixed point of `Γ` with gate below `K`. -/
theorem vs_layAt (S : InaccSeq.{0}) {F : Ordinal.{0}} (hF : gamma F = F) (hBF : tfBG ≤ F) (hFX : F < tlX)
    (hK : max ω (yrQE F) < Td.tdK S) : ZbLayAt S F := by
  obtain ⟨L, hLg, hLE, hLtop, hLP⟩ := vsLay_all S F hF hBF hFX
  have hOF : Om1 < F := tfBG_gt.trans_le hBF
  refine ⟨L, F, (vs_gcG_fix hF hOF).le, by rw [hLg]; exact hK, hFX.le, by rw [← Br.Om1_eq]; exact hOF.le,
    zm_fix_E (zm_fix_of_gamma hF), hLtop, hLP, fun Z hZ hKZ => vs_F_atom hF hBF hFX hZ (hK.trans_le hKZ),
    fun x hx hx1 hgx => ?_⟩
  rw [hLE x hx hx1 hgx]
  obtain ⟨-, -, hxF, -, hcl, -⟩ := vs_DF hF hBF hFX hx hx1 (hLg ▸ hgx)
  have hD := (ywBG hx hx1).2.2 _ hxF hcl
  have h0T : (0 : Ordinal.{0}) ∈ Tset x := mem_T_of_le hx hx1 zero_le
  obtain ⟨-, hDT, hDcl⟩ := ywD_closed hx hx1
  have h1 : eN x < gq 0 x := gmq_eN_lt hx hx1 h0T (hx.pos.trans hx1)
  have h2 : gq 0 x < ywV 1 0 x := hDcl 0 h0T (hx.pos.trans (ywD_closed hx hx1).1)
  exact (h1.trans h2).trans_le hD

/-- **The tower `B_Γ, F_{B_Γ}(0), F_{F_{B_Γ}(0)}(0), …`** (`Tl.tlG`). -/
noncomputable def vsTw : ℕ → Ordinal.{0}
  | 0 => tfBG
  | n + 1 => tlG (vsTw n)

/-- **The tower consists of fixed points of `Γ` in `[B_Γ, X)` with gate `0`.** -/
theorem vsTw_facts : ∀ n, gamma (vsTw n) = vsTw n ∧ tfBG ≤ vsTw n ∧ vsTw n < tlX ∧ yrQE (vsTw n) = 0
  | 0 => ⟨tfBG_fix, le_rfl, tl_BG_lt_X, va_QE_BG⟩
  | n + 1 => by
    obtain ⟨hf, hb, hx, hq⟩ := vsTw_facts n
    have hτ0 : vsTw n ≠ 0 := ((show InE tfBG from Low.opow_eq_self_of_SC tfBG_SC).pos.trans_le hb).ne'
    have hOτ : Om1 < vsTw n := tfBG_gt.trans_le hb
    show gamma (tlG (vsTw n)) = tlG (vsTw n) ∧ tfBG ≤ tlG (vsTw n) ∧ tlG (vsTw n) < tlX ∧
      yrQE (tlG (vsTw n)) = 0
    have hlt : vsTw n < tlG (vsTw n) := tl_lt_G hOτ hx
    refine ⟨rhF_gamma hτ0 0, hb.trans hlt.le, (tlG_normal.strictMono hx).trans_eq tlX_fix, ?_⟩
    have hSC : SC (tlG (vsTw n)) := rhF_SC _ 0
    have hO : Om1 < tlG (vsTw n) := hOτ.trans hlt
    have hA : YhAt (tlG (vsTw n)) := ⟨hSC, hO⟩
    have hfix : gamma (tlG (vsTw n)) = tlG (vsTw n) := rhF_gamma hτ0 0
    have hi : ¬ yhJ (tlG (vsTw n)) < tlG (vsTw n) := by
      have h := yhJ_gcG (tlG (vsTw n)); rw [vs_gcG_fix hfix hO] at h; rw [h]; exact lt_irrefl _
    have h0 : (0 : Ordinal.{0}) < rhF (vsTw n) 0 := lt_of_le_of_lt zero_le hlt
    have hlev : tlLev (tlG (vsTw n)) = vsTw n := tlLev_F h0
    have hidx : tlI (vsTw n) (tlG (vsTw n)) = 0 := tlI_rhF _ 0
    have hL : tlLev (tlG (vsTw n)) < tlG (vsTw n) ∧ tlI (tlLev (tlG (vsTw n))) (tlG (vsTw n)) < tlG (vsTw n) := by
      rw [hlev, hidx]; exact ⟨hlt, h0⟩
    have hyQ : yrQ (vsTw n) = 0 := by
      refine le_antisymm ((yrQ_le _).trans ?_) zero_le
      rw [yrG_base (zm_fix_E (zm_fix_of_gamma hf)) (va_G_le_BG.trans hb), hq]
    rw [yrQE_atom_fixL hA hi hL, hlev, hidx, Ordinal.zero_sub, hyQ, yrQ_zero, max_self]

theorem vsTw_iter : ∀ n : ℕ, tlG^[n] tfBG = vsTw n
  | 0 => rfl
  | n + 1 => by rw [Function.iterate_succ_apply', vsTw_iter n]; rfl

/-- **The tower is cofinal in `X`.** -/
theorem vsTw_cof {B : Ordinal.{0}} (hB : B < tlX) : ∃ n, B < vsTw n := by
  unfold tlX at hB
  obtain ⟨n, hn⟩ := lt_nfp_iff.1 hB
  refine ⟨n, hn.trans_le ?_⟩
  rw [← vsTw_iter]
  exact tlG_normal.strictMono.monotone.iterate n tl_Om1_succ_lt_BG.le

/-- **`ZbDirect S X`, UNCONDITIONAL**: a layer for every atom index `B_Γ ≤ B < X` (the layer at a fixed point of the
tower above `B`, `Zg.zbLayAt_mono`). -/
theorem vsDirectX (S : InaccSeq.{0}) : ZbDirect S tlX := by
  intro B _ hB2
  obtain ⟨n, hn⟩ := vsTw_cof hB2
  obtain ⟨hf, hb, hx, hq⟩ := vsTw_facts n
  have hK : max ω (yrQE (vsTw n)) < Td.tdK S := by
    rw [hq, max_eq_left zero_le]; exact omega0_lt_inE (Low.opow_eq_self_of_SC Td.tdK_SC)
  exact Zg.zbLayAt_mono hn.le (vs_layAt S hf hb hx hK)

end Googology.Trans.PoR.InaccPsi.R2.Va
