import Googology.Trans.PoR.InaccPsi.R2.QcAll
import Googology.Trans.PoR.InaccPsi.R2.QcConv
import Googology.Trans.PoR.InaccPsi.R2.VaLay

/-!
# QcLay: THE LAYER AT EVERY FIXED POINT OF `Γ` BELOW `B₂`, WITH THE ATOMS OF `qcU`

As `Va.VaLay` up to `B₂`.  A layer at a fixed point `F ∈ [B_Γ, B₂)` of `Γ` (`QsLay S F`: gate the gate of `F`, top
reading `vQ F`, reading `F` with the atoms of `Qc.qcU`, terms for every code below `F`) gives the base layer
`Qc.QDS.QBase` of the segment of `F` (the ladder over it with `e(x) = F(x)`, a closed point, `qsBase`), so the reading
system `Qc.QDS.toRS` of every digit system over the segment base `F` gives the layers at the atom indices of the
segment (`qsAt_of`).  Below `X` the layers of `Va` with the same readings (`Qc.qc_th_conv`, `Qc.qc_poly_conv`); from `X`
on the layer at a fixed point is the union of the atom layers below it (`qsLay_union`).

* `qs_F_data`, `qs_DF` (**the facts of the reading `F(x)`**), `qs_DF_pi`, `qs_Fx_cl`, `qs_F_atom`;
* `QsLay`, `qsLay_low`, `qcBG_top`, `qcBG_poly`, `qs_ladH`, `qsBase` (**the base layer of the segment**);
* `QsAt`, `qsAt_of` (**the layer at an atom index**), `qs_cb_gate`, `qs_F_lt`, `qs_F_top`, `qsLayF`, `qsLay_union`,
  `qsLay_all` (**A LAYER AT EVERY FIXED POINT `B_Γ ≤ F < B₂` OF `Γ`**), `qs_layAt` (**`ZmLayA qcU S F`**).

No new axiom.  New definitions: `QsLay`, `qsBase`, `QsAt`, `qsLayF`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Googology.Trans.PoR.InaccPsi.R2.Qc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Tf Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Yr Googology.Trans.PoR.InaccPsi.R2.Yw Googology.Trans.PoR.InaccPsi.R2.Gd
  Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Zb
  Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Yh Googology.Trans.PoR.InaccPsi.R2.Zm
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Xk Googology.Trans.PoR.InaccPsi.R2.Gm
  Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Trans.PoR.InaccPsi.R2.Gs
  Googology.Trans.PoR.InaccPsi.R2.Va Googology.Trans.PoR.InaccPsi.R2.Uc

/-! ## The reading of a fixed point of `Γ` below `B₂` -/

section DF

variable {F : Ordinal.{0}} (hF : gamma F = F) (hBF : tfBG ≤ F) (hFB : F < ucB)
include hF hBF hFB

/-- The data of a fixed point `F > B_Γ`: an atom, a limit of `ε`-numbers, the systems below it. -/
theorem qs_F_data (hBF' : tfBG < F) :
    InE F ∧ YhAt F ∧ ¬ yhJ F < F ∧ (∀ e, InE e → e < F → eN e < F) ∧
      (∀ e, InE e → tfBG ≤ e → e < F → QsGood e) := by
  have hOF : Om1 < F := tfBG_gt.trans hBF'
  refine ⟨zm_fix_E (zm_fix_of_gamma hF), ⟨by rw [← hF]; exact Lq.lq_gamma_SC _, hOF⟩, ?_, vs_fix_lim hF,
    fun e he heB heE => qsGood_all e he heB (heE.trans hFB)⟩
  have h := yhJ_gcG F; rw [vs_gcG_fix hF hOF] at h; rw [h]; exact lt_irrefl _

/-- **The facts of the reading `F(x)` of a fixed point `F ≥ B_Γ` of `Γ` above its gate**: a closed point of
`Tˣ ∩ (x, Ω₁)` below a generic-level point. -/
theorem qs_DF {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hgx : max ω (qcQE F) < x) :
    vQ F x ∈ Tset x ∧ InE (vQ F x) ∧ x < vQ F x ∧ QcBd x (vQ F x) ∧ YwClosed x (vQ F x) ∧ vQ F x < Om1 := by
  rcases lt_or_ge F tlX with hFX | hXF
  · rw [qcQE_low hFX] at hgx
    obtain ⟨hT, hE, hxF, hX, hcl, h1⟩ := vs_DF hF hBF hFX hx hx1 hgx
    rw [vQ_low hFX]
    exact ⟨hT, hE, hxF, qcBd_of_X hx hX, hcl, h1⟩
  · have hBF' : tfBG < F := tl_BG_lt_X.trans_le hXF
    obtain ⟨hFE, hA, hi, hlim, hIH⟩ := qs_F_data hF hBF hFB hBF'
    obtain ⟨-, hcl, hVT, hVE, hxV, hVX, hV1⟩ := qs_fx_V hFE hBF' hFB hXF hlim hIH hA hi hx hx1 hgx
    rw [vQ_base' hFE (va_G_le_BG.trans hBF) hFB]
    exact ⟨hVT, hVE, hxV, hVX, hcl, hV1⟩

/-- **The reading of a fixed point is exact.** -/
theorem qs_DF_pi {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) (hgσ : max ω (qcQE F) < σ) :
    vQ F ρ ∈ TB ρ σ ∧ R2.pi σ ρ (vQ F ρ) = vQ F σ := by
  rcases lt_or_ge F tlX with hFX | hXF
  · rw [qcQE_low hFX] at hgσ
    rw [vQ_low hFX, vQ_low hFX]
    exact vs_DF_pi hF hBF hFX hB hgσ
  · have hBF' : tfBG < F := tl_BG_lt_X.trans_le hXF
    obtain ⟨hFE, hA, hi, hlim, hIH⟩ := qs_F_data hF hBF hFB hBF'
    have hG : gcG 0 ≤ F := va_G_le_BG.trans hBF
    rw [vQ_base' hFE hG hFB, vQ_base' hFE hG hFB]
    exact qs_fx_pi hFE hBF' hFB hXF hlim hIH hA hi hB hgσ

/-- **A fixed point is a code over every strongly critical `Z` above its gate.** -/
theorem qs_Fx_cl {Z : Ordinal.{0}} (hZ : SC Z) (hgZ : max ω (qcQE F) < Z) : UcCl Z F := by
  rcases lt_or_ge F tlX with hFX | hXF
  · rw [qcQE_low hFX] at hgZ
    exact UcCl.tl (vs_F_tl hF hBF hFX hZ hgZ)
  · have hBF' : tfBG < F := tl_BG_lt_X.trans_le hXF
    obtain ⟨hFE, hA, hi, hlim, hIH⟩ := qs_F_data hF hBF hFB hBF'
    exact qs_fx_cl hFE hBF' hFB hXF hlim hIH hA hi hZ hgZ

/-- **A fixed point is an atom of `qcU` over every strongly critical `Z` above its gate.** -/
theorem qs_F_atom {Z : Ordinal.{0}} (hZ : SC Z) (hgZ : max ω (qcQE F) < Z) : GxCl Z (qcU.At Z) F := by
  have hSC : SC F := by rw [← hF]; exact Lq.lq_gamma_SC _
  have hOF : Om 1 < F := by rw [← Br.Om1_eq]; exact tfBG_gt.trans_le hBF
  exact GxCl.atom ⟨hSC, hOF, hFB, qs_Fx_cl hF hBF hFB hZ hgZ⟩

end DF

/-! ## The layer at a fixed point -/

/-- **A layer at the fixed point `F`**: gate the gate of `F`, top reading `vQ F`, reading `F` with the atoms of
`qcU`, terms for every code below `F`. -/
def QsLay (_S : InaccSeq.{0}) (F : Ordinal.{0}) : Prop :=
  ∃ L : GdB, L.g = max ω (qcQE F) ∧ (∀ x, InE x → x < Om1 → L.g < x → L.K.E x = vQ F x) ∧
    (∀ y, SC y → y < Om 1 → L.g < y → L.K.E y = gxTh y (qcU.At y) F) ∧ ZbPolyG qcU L.K.sys F

/-- **Below `X` the layers of `Va`.** -/
theorem qsLay_low (S : InaccSeq.{0}) {F : Ordinal.{0}} (hF : gamma F = F) (hBF : tfBG ≤ F) (hFX : F < tlX) :
    QsLay S F := by
  obtain ⟨L, hLg, hLE, hLtop, hLP⟩ := vsLay_all S F hF hBF hFX
  refine ⟨L, by rw [hLg, qcQE_low hFX], fun x hx hx1 hg => by rw [hLE x hx hx1 hg, vQ_low hFX],
    fun y hy hy1 hg => by rw [hLtop y hy hy1 hg, qc_th_conv hy.1 hFX.le], qc_poly_conv hFX.le hLP⟩

theorem qcBG_top (S : InaccSeq.{0}) {y : Ordinal.{0}} (hy : SC y) (hy1 : y < Om 1) :
    ywBGB.K.E y = gxTh y (qcU.At y) tfBG := by
  rw [zbBG_top S hy hy1, qc_th_conv hy.1 tl_BG_lt_X.le]

theorem qcBG_poly (S : InaccSeq.{0}) : ZbPolyG qcU ywBGB.K.sys tfBG := qc_poly_conv tl_BG_lt_X.le (zbBG_poly S)

/-- **The ladder hypothesis over a layer at `F`** with `e(x) = F(x)`. -/
theorem qs_ladH {F : Ordinal.{0}} (hF : gamma F = F) (hBF : tfBG ≤ F) (hFB : F < ucB) (U : GdB)
    (hUg : U.g = max ω (qcQE F)) (hUE : ∀ x, InE x → x < Om1 → U.g < x → U.K.E x = vQ F x) :
    YwLH U (fun x => vQ F x) := by
  refine ⟨fun x hx hx1 hg => ?_, fun x hx hx1 hg => ?_, fun x hx hx1 hg j hjT hj => ?_, fun x hx hx1 hg => ?_,
    fun x hx hx1 hg => ?_, fun σ ρ hB hg => ?_⟩
  · obtain ⟨hT, -, -, -, -, h1⟩ := qs_DF hF hBF hFB hx hx1 (hUg ▸ hg); exact ⟨hT, h1⟩
  · rw [hUE x hx hx1 hg]
  · obtain ⟨-, -, -, -, hcl, -⟩ := qs_DF hF hBF hFB hx hx1 (hUg ▸ hg)
    rw [hUE x hx hx1 hg]; exact (hcl j hjT hj).le
  · obtain ⟨hT, -, -, -, -, h1⟩ := qs_DF hF hBF hFB hx hx1 (hUg ▸ hg)
    rw [hUE x hx hx1 hg]; exact gmq_gt hx hx1 hT h1
  · obtain ⟨hT, -, -, hX, -, -⟩ := qs_DF hF hBF hFB hx hx1 (hUg ▸ hg)
    exact yBd_of_qc (qcBd_gq hx hx1 hT hX)
  · exact qs_DF_pi hF hBF hFB hB (hUg ▸ hg)

/-- **THE BASE LAYER OF THE SEGMENT OF `F`**: the ladder over a layer at `F`, for a digit system over the segment
base `F` read `vQ F`. -/
noncomputable def qsBase (S : InaccSeq.{0}) {F : Ordinal.{0}} (hF : gamma F = F) (hBF : tfBG ≤ F) (hFB : F < ucB)
    (hL : QsLay S F) (M : QDS) (hMB : M.B = F) (hMD : M.Dv = vQ F) (hEg : max ω (qcQE F) ≤ M.Eg) :
    QDS.QBase S M where
  L0 := ywLadB (Classical.choose hL) (fun x => vQ F x)
    (qs_ladH hF hBF hFB _ (Classical.choose_spec hL).1 (Classical.choose_spec hL).2.1)
  L0_g := by rw [ywLadB_g, (Classical.choose_spec hL).1]; exact hEg
  L0_E := fun x _ _ => by rw [ywLadB_E, hMD]
  L0_top := fun y hy hy1 hgy => by
    obtain ⟨hUg, -, hUtop, -⟩ := Classical.choose_spec hL
    have hc : ∀ Z, SC Z → (Classical.choose hL).g < Z → GxCl Z (qcU.At Z) F := fun Z hZ hgZ =>
      qs_F_atom hF hBF hFB hZ (hUg ▸ hgZ)
    have hcQ : Ga.cQs F = gcG (F + 1) := by
      conv_lhs => rw [← vs_gcG_fix hF (tfBG_gt.trans_le hBF)]
      exact gc_cQs F
    rw [zbLad_top hc hUtop _ hy hy1 (hUg.trans_lt (hEg.trans_lt hgy)), hMB, hcQ]
  L0_poly := by
    obtain ⟨hUg, -, hUtop, hUP⟩ := Classical.choose_spec hL
    have hc : ∀ Z, SC Z → (Classical.choose hL).g < Z → GxCl Z (qcU.At Z) F := fun Z hZ hgZ =>
      qs_F_atom hF hBF hFB hZ (hUg ▸ hgZ)
    have hcO : Om 1 ≤ F := by rw [← Br.Om1_eq]; exact (tfBG_gt.trans_le hBF).le
    have h := zbLad_poly hc hcO hUtop (qs_ladH hF hBF hFB _ hUg (Classical.choose_spec hL).2.1) qcU_th hUP
    have hcQ : Ga.cQs F = gcG (F + 1) := by
      conv_lhs => rw [← vs_gcG_fix hF (tfBG_gt.trans_le hBF)]
      exact gc_cQs F
    rw [hMB]; rwa [hcQ] at h
  Dv_ge := fun x hx hx1 hgx => by
    obtain ⟨-, -, hxF, -, hcl, -⟩ := qs_DF hF hBF hFB hx hx1 (hEg.trans_lt hgx)
    rw [hMD]; exact (ywBG hx hx1).2.2 _ hxF hcl

/-! ## The layers at the atom indices of a segment -/

/-- **A layer at the atom index `c`** past its segment base `F = vaFB c`: reading `gq(F(x) + o(x))`, `o = c − (F+1)`,
top code `gcG c`; its gate is above the gates of `F` and `o`, and below every limit above the gate of `c`. -/
def QsAt (_S : InaccSeq.{0}) (c : Ordinal.{0}) : Prop :=
  ∃ L : GdB, (∀ Z, IsSuccLimit Z → ω < Z → qcG c < Z → L.g < Z) ∧
    (∀ x, L.g < x → qcG (vaFB c) < x ∧ qcG (c - (vaFB c + 1)) < x) ∧
    (∀ x, InE x → x < Om1 → L.g < x → L.K.E x = gq (vQ (vaFB c) x + vQ (c - (vaFB c + 1)) x) x) ∧
    (∀ y, SC y → y < Om 1 → L.g < y → L.K.E y = gxTh y (qcU.At y) (gcG c)) ∧ ZbPolyG qcU L.K.sys (gcG c)

/-- **The layer at an atom index of a segment**, from the layer at its segment base: the reading system of the
digit system at `ε_{e+1}` (`e` the bracket of `c`) over the base `F` (`Qc.QDS.toRS` with `qsBase`). -/
theorem qsAt_of (S : InaccSeq.{0}) {c : Ordinal.{0}} (hBc : tfBG ≤ c) (hFc : vaFB c < c) (hcB : c < ucB)
    (hL : QsLay S (vaFB c)) : QsAt S c := by
  have hGc : gcG 0 ≤ c := va_G_le_BG.trans hBc
  have hFfix := vs_FB_fix hBc
  have hBF := vs_FB_ge hBc
  have hFB : vaFB c < ucB := hFc.trans hcB
  have heB : vaFB c ≤ guE c := gl_E_max (vs_FB_E hBc) (vs_FB_gt hBc) (vs_FB_le hBc)
  have hec : guE c ≤ c := gl_E_le (yh_gfE_le hGc)
  have hce : c < eN (guE c) := gl_lt_eN (yh_gfE_le hGc)
  have heE := guE_E c
  have hBe : tfBG ≤ guE c := hBF.trans heB
  have hE'B : eN (guE c) < ucB := qc_eN_lt_B (hec.trans_lt hcB)
  have hBE' : tfBG ≤ eN (guE c) := hBe.trans (lt_eN _).le
  obtain ⟨M, hME, hEg, -, hR, hG, hMB, hMD⟩ := qsGood_all _ (eN_E _) hBE' hE'B
  have hFB' : vaFB (eN (guE c)) = vaFB c := by
    rw [vs_FB_eN hBe]; exact vs_FB_of_le hBc heB hec
  rw [hFB'] at hMB hMD
  have hEgF : max ω (qcQE (vaFB c)) ≤ M.Eg := by
    rw [hEg]
    have h := qc_FB_gate' hBE' hE'B
    rw [hFB', qcG_base' (vs_FB_E hBc) (va_G_le_BG.trans hBF) hFB,
      qcG_base' (eN_E _) (va_G_le_BG.trans hBE') hE'B] at h
    exact max_le (le_max_left _ _) h
  have hBME : M.B < M.E := by rw [hMB, hME]; exact hFc.trans hce
  have hc0 : M.B + 1 ≤ c := by rw [hMB]; exact Order.add_one_le_of_lt hFc
  have hcBd : c < M.E := by rw [hME]; exact hce
  set RS := M.toRS S hBME (qsBase S hFfix hBF hFB hL M hMB hMD hEgF) with hRS
  obtain ⟨L, hLg, hLE, hLtop, hLP⟩ := RS.lay c hc0 hcBd
  have hgt : RS.gt c = max M.Eg (M.G (c - (vaFB c + 1))) := by
    show max M.Eg (M.G (c - (M.B + 1))) = _; rw [hMB]
  have hoE : c - (vaFB c + 1) < eN (guE c) := (Ordinal.sub_le_self _ _).trans_lt hce
  refine ⟨L, fun Z hZ hωZ hgZ => ?_, fun x hgx => ?_, fun x hx hx1 hgx => ?_, fun y hy hy1 hgy => ?_, hLP⟩
  · -- the gate is below every limit above the gate of `c`
    have hQ : qcQE (guE c) < Z := by
      rw [qcG_dec' hGc hcB] at hgZ; exact (le_max_left _ _).trans_lt ((le_max_left _ _).trans_lt hgZ)
    have hEgZ : M.Eg < Z := by rw [hEg]; exact max_lt hωZ (qc_QE_eN_lt heE hBe (hec.trans_lt hcB) hZ hωZ hQ)
    rw [hLg, hgt]
    refine max_lt hEgZ ?_
    rcases eq_or_ne (c - (vaFB c + 1)) 0 with h0 | h0
    · rw [h0, M.G0]; exact hZ.bot_lt
    · rw [hG _ hoE h0]
      exact max_lt hEgZ ((qc_off_gate' (vs_FB_E hBc) (va_G_le_BG.trans hBF) hcB hFc).trans_lt (max_lt hωZ hgZ))
  · -- the gates of the base and of the offset are below the gate
    rw [hLg, hgt] at hgx
    have hEgx : M.Eg < x := (le_max_left _ _).trans_lt hgx
    refine ⟨?_, ?_⟩
    · rw [qcG_base' (vs_FB_E hBc) (va_G_le_BG.trans hBF) hFB]
      exact (le_max_right _ _).trans_lt (hEgF.trans_lt hEgx)
    · rcases eq_or_ne (c - (vaFB c + 1)) 0 with h0 | h0
      · rw [h0, qcG_zero]; exact (zero_le).trans_lt hEgx
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

/-- **The gate of `vsCb b`** stays below every `ε`-number above the gate of `b`. -/
theorem qs_cb_gate {b Z : Ordinal.{0}} (hZ : InE Z) (hbB : vsCb b < ucB) (hgb : qcG b < Z) :
    qcG (vsCb b) < Z := by
  have hωZ : ω < Z := omega0_lt_inE hZ
  have hZP : ∀ u v, u < Z → v < Z → u + v < Z := fun u v hu hv => (inE_indec hZ).add_lt hu hv
  have hb'B : tfBG ≤ max b tfBG := le_max_right _ _
  have hmB : max b tfBG < ucB := le_add_self.trans_lt hbB
  have hgb' : qcG (max b tfBG) < Z := by
    rcases le_total b tfBG with h | h
    · rw [max_eq_right h, qcG_low tl_BG_lt_X, yrG_base (Low.opow_eq_self_of_SC tfBG_SC) va_G_le_BG, va_QE_BG]
      exact hZ.pos
    · rw [max_eq_left h]; exact hgb
  have hgF : qcG (vaFB (max b tfBG)) < Z := (qc_FB_gate' hb'B hmB).trans_lt (max_lt hωZ hgb')
  have h1 : qcG (1 : Ordinal.{0}) < Z := by
    rw [show (1 : Ordinal.{0}) = ((1 : ℕ) : Ordinal.{0}) by norm_num, qcG_nat]
    exact (natCast_lt_omega0 1).trans hωZ
  unfold vsCb at hbB ⊢
  exact qc_add hZP hωZ _ _ hbB (qc_add hZP hωZ _ _ (le_self_add.trans_lt hbB) hgF h1) hgb'

/-! ## The layer at a fixed point from `X` on: the union of the atom layers below it -/

section Fix

variable {F : Ordinal.{0}} (hF : gamma F = F) (hXF : tlX ≤ F) (hFB : F < ucB)
include hF hXF hFB

theorem qs_F_lt {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hgx : max ω (qcQE F) < x) :
    ∀ c, c < F → qcG c < x → vQ c x < vQ F x := by
  have hBF' : tfBG < F := tl_BG_lt_X.trans_le hXF
  obtain ⟨hFE, hA, hi, hlim, hIH⟩ := qs_F_data hF hBF'.le hFB hBF'
  intro c hc hg
  rw [vQ_base' hFE (va_G_le_BG.trans hBF'.le) hFB]
  exact qs_fx_lt hFE hBF' hFB hXF hlim hIH hA hi hx hx1 hgx c hc hg

theorem qs_F_top {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hgx : max ω (qcQE F) < x) :
    ∀ ν, ν < vQ F x → ∃ b, b < F ∧ qcG b < x ∧ ν ≤ vQ b x := by
  have hBF' : tfBG < F := tl_BG_lt_X.trans_le hXF
  obtain ⟨hFE, hA, hi, hlim, hIH⟩ := qs_F_data hF hBF'.le hFB hBF'
  intro ν hν
  rw [vQ_base' hFE (va_G_le_BG.trans hBF'.le) hFB] at hν
  exact qs_fx_top hFE hBF' hFB hXF hlim hIH hA hi hx hx1 hgx ν hν

variable (S : InaccSeq.{0}) (hAt : ∀ b, b < F → QsAt S (vsCb b))

/-- **The union data at a fixed point**: the atom layers `vsCb b`, `b < F`, and the layer of `B_Γ` for the
constants; target `F(x)`. -/
noncomputable def qsLayF : YwUF (max ω (qcQE F)) where
  I := Option {b : Ordinal.{0} // b < F}
  K := fun i => Option.elim i ywBGB fun b => Classical.choose (hAt b.1 b.2)
  gi := fun i => Option.elim i 0 fun b => (Classical.choose (hAt b.1 b.2)).g
  i0 := none
  g_le := fun i => by
    cases i with
    | none => exact le_of_eq ywBGB_g
    | some b => exact le_rfl
  gi0 := rfl
  T := fun x => vQ F x
  T_E := fun x hx hx1 hg => (qs_DF hF (tl_BG_lt_X.le.trans hXF) hFB hx hx1 hg).2.1
  T_mem := fun x hx hx1 hg => (qs_DF hF (tl_BG_lt_X.le.trans hXF) hFB hx hx1 hg).1
  T_gt := fun x hx hx1 hg => (qs_DF hF (tl_BG_lt_X.le.trans hXF) hFB hx hx1 hg).2.2.1
  T_X := fun x hx hx1 hg => yBd_of_qc (qs_DF hF (tl_BG_lt_X.le.trans hXF) hFB hx hx1 hg).2.2.2.1
  E_lt := fun i x hx hx1 hg hgi => by
    have hBF' : tfBG < F := tl_BG_lt_X.trans_le hXF
    cases i with
    | none =>
      show ywBGB.K.E x < vQ F x
      rw [ywBGB_E, ← vR_BG x, ← vQ_low tl_BG_lt_X]
      refine qs_F_lt hF hXF hFB hx hx1 hg _ hBF' ?_
      rw [qcG_low tl_BG_lt_X, yrG_base (Low.opow_eq_self_of_SC tfBG_SC) va_G_le_BG, va_QE_BG]; exact hx.pos
    | some b =>
      obtain ⟨-, hgo, hE, -, -⟩ := Classical.choose_spec (hAt b.1 b.2)
      obtain ⟨-, -, hlt, hcF, -, -, -⟩ := vs_cb_facts hF hBF' b.2
      obtain ⟨hgF', hgo'⟩ := hgo x hgi
      show (Classical.choose (hAt b.1 b.2)).K.E x < vQ F x
      rw [hE x hx hx1 hgi]
      obtain ⟨hDT, hDE, -, -, hcl, hD1⟩ := qs_DF hF hBF'.le hFB hx hx1 hg
      have h1 := qs_F_lt hF hXF hFB hx hx1 hg _ (hlt.trans hcF) hgF'
      have h2 := qs_F_lt hF hXF hFB hx hx1 hg _ ((Ordinal.sub_le_self _ _).trans_lt hcF) hgo'
      have hsum := (inE_indec hDE).add_lt h1 h2
      exact hcl _ (vz_T_down hx hx1 hDT hD1 hsum.le) hsum
  cof := fun x hx hx1 hg v hv => by
    have hBF' : tfBG < F := tl_BG_lt_X.trans_le hXF
    obtain ⟨hFE, -, -, hlim, hIH⟩ := qs_F_data hF hBF'.le hFB hBF'
    obtain ⟨b, hb, hgb, hvb⟩ := qs_F_top hF hXF hFB hx hx1 hg v hv
    obtain ⟨hgate, hgo, hE, -, -⟩ := Classical.choose_spec (hAt b hb)
    obtain ⟨-, hseg, -, hcF, hsub, -, -⟩ := vs_cb_facts hF hBF' hb
    have hgL : (Classical.choose (hAt b hb)).g < x :=
      hgate x (ev_isSuccLimit_of_inE hx) (omega0_lt_inE hx) (qs_cb_gate hx (hcF.trans hFB) hgb)
    refine ⟨some ⟨b, hb⟩, hgL, ?_⟩
    show v < (Classical.choose (hAt b hb)).K.E x
    rw [hE x hx hx1 hgL, hsub, hseg]
    obtain ⟨hgF', hgb'⟩ := hgo x hgL
    rw [hsub] at hgb'
    rw [hseg] at hgF'
    have hb'F : max b tfBG < F := max_lt hb hBF'
    obtain ⟨hb'T, hb'1, -⟩ := qs_T hFE hBF' hFB hlim hIH hx hx1 hb'F hgb'
    obtain ⟨hFT, hF1, -⟩ := qs_T hFE hBF' hFB hlim hIH hx hx1 ((vs_FB_le (le_max_right _ _)).trans_lt hb'F) hgF'
    have hvb' : v ≤ vQ (max b tfBG) x := by
      rcases lt_or_ge b tfBG with h | h
      · rw [max_eq_right h.le]
        have hgB : qcG tfBG < x := by
          rw [qcG_low tl_BG_lt_X, yrG_base (Low.opow_eq_self_of_SC tfBG_SC) va_G_le_BG, va_QE_BG]; exact hx.pos
        exact hvb.trans (qs_mono hFE hBF' hFB hlim hIH hx hx1 h hBF' hgb hgB).le
      · rw [max_eq_left h]; exact hvb
    exact hvb'.trans_lt ((gmq_gt hx hx1 hb'T hb'1).trans_le
      (gmq_mono hx hx1 (vzT_add hx hx1 hFT hb'T) ((inE_indec gl_Om1_E).add_lt hF1 hb'1) le_add_self))
  pi := fun σ ρ _ _ hB hg => qs_DF_pi hF (tl_BG_lt_X.le.trans hXF) hFB hB hg

end Fix

/-- **THE LAYER AT A FIXED POINT OF `Γ` FROM `X` ON**: the union of the atom layers below it. -/
theorem qsLay_union (S : InaccSeq.{0}) {F : Ordinal.{0}} (hF : gamma F = F) (hXF : tlX ≤ F) (hFB : F < ucB)
    (hAt : ∀ b, b < F → QsAt S (vsCb b)) : QsLay S F := by
  have hBF' : tfBG < F := tl_BG_lt_X.trans_le hXF
  set Fu := qsLayF hF hXF hFB S hAt with hFu
  have hres := zbUnion_codes (A := qcU) Fu (fun i => Option.elim i tfBG fun b => gcG (vsCb b.1)) (Tc := F)
    (fun i y hy hy1 hi => by
      cases i with
      | none => exact qcBG_top S hy hy1
      | some b => exact (Classical.choose_spec (hAt b.1 b.2)).2.2.2.1 y hy hy1 hi)
    (fun i => by
      cases i with
      | none => exact qcBG_poly S
      | some b => exact (Classical.choose_spec (hAt b.1 b.2)).2.2.2.2)
    (fun i => by
      cases i with
      | none => exact hBF'.le
      | some b =>
        obtain ⟨-, -, -, hcF, -, -, -⟩ := vs_cb_facts hF hBF' b.2
        exact (gcG_lt hcF).le.trans (vs_gcG_fix hF (tfBG_gt.trans hBF')).le)
    (fun Z hZ hZ1 _ d hd hdT => by
      have hZ1' : Z ≤ Om1 := by rw [Br.Om1_eq]; exact hZ1.le
      have hZE : InE Z := Low.opow_eq_self_of_SC hZ
      have hgd : qcG d < Z := qc_gate hZ hZ1' d (qc_of_gx hd) (hdT.trans hFB)
      obtain ⟨hgate, -⟩ := Classical.choose_spec (hAt d hdT)
      obtain ⟨-, -, -, hcF, -, hdc, hcg⟩ := vs_cb_facts hF hBF' hdT
      refine ⟨some ⟨d, hdT⟩, hgate Z (ev_isSuccLimit_of_inE hZE) (omega0_lt_inE hZE)
        (qs_cb_gate hZE (hcF.trans hFB) hgd), ?_⟩
      show d < gcG (vsCb d)
      exact ((le_max_left d tfBG).trans hdc).trans_lt hcg)
  exact ⟨ywLimB Fu, rfl, fun x _ _ _ => rfl, hres.1, hres.2⟩

/-- **A LAYER AT EVERY FIXED POINT `B_Γ ≤ F < B₂` OF `Γ`**: below `X` the layers of `Va`; from `X` on one induction
over the fixed points (the layers at the atom indices below `F` from the layers at their segment bases, `qsAt_of`). -/
theorem qsLay_all (S : InaccSeq.{0}) : ∀ F, gamma F = F → tfBG ≤ F → F < ucB → QsLay S F := by
  intro F
  induction F using WellFoundedLT.induction with
  | ind F IH =>
  intro hF hBF hFB
  rcases lt_or_ge F tlX with hFX | hXF
  · exact qsLay_low S hF hBF hFX
  have hBF' : tfBG < F := tl_BG_lt_X.trans_le hXF
  refine qsLay_union S hF hXF hFB fun b hb => ?_
  obtain ⟨hBc, -, hlt', hcF, -, -, -⟩ := vs_cb_facts hF hBF' hb
  exact qsAt_of S hBc hlt' (hcF.trans hFB)
    (IH _ (hlt'.trans hcF) (vs_FB_fix hBc) (vs_FB_ge hBc) ((hlt'.trans hcF).trans hFB))

/-- **The layer for the index `F`**, a fixed point of `Γ` below `B₂` with gate below `K`, with the atoms of `qcU`. -/
theorem qs_layAt (S : InaccSeq.{0}) {F : Ordinal.{0}} (hF : gamma F = F) (hBF : tfBG ≤ F) (hFB : F < ucB)
    (hK : max ω (qcQE F) < Td.tdK S) : ZmLayA qcU S F := by
  obtain ⟨L, hLg, hLE, hLtop, hLP⟩ := qsLay_all S F hF hBF hFB
  have hOF : Om1 < F := tfBG_gt.trans_le hBF
  refine ⟨L, F, (vs_gcG_fix hF hOF).le, by rw [hLg]; exact hK, hFB.le, by rw [← Br.Om1_eq]; exact hOF.le,
    zm_fix_E (zm_fix_of_gamma hF), hLtop, hLP, fun Z hZ hKZ => qs_F_atom hF hBF hFB hZ (hK.trans_le hKZ),
    fun x hx hx1 hgx => ?_⟩
  rw [hLE x hx hx1 hgx]
  obtain ⟨-, -, hxF, -, hcl, -⟩ := qs_DF hF hBF hFB hx hx1 (hLg ▸ hgx)
  have hD := (ywBG hx hx1).2.2 _ hxF hcl
  have h0T : (0 : Ordinal.{0}) ∈ Tset x := mem_T_of_le hx hx1 zero_le
  obtain ⟨-, -, hDcl⟩ := ywD_closed hx hx1
  have h1 : eN x < gq 0 x := gmq_eN_lt hx hx1 h0T (hx.pos.trans hx1)
  have h2 : gq 0 x < ywV 1 0 x := hDcl 0 h0T (hx.pos.trans (ywD_closed hx hx1).1)
  exact (h1.trans h2).trans_le hD

end Googology.Trans.PoR.InaccPsi.R2.Qc
