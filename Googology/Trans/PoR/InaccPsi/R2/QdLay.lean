import Googology.Trans.PoR.InaccPsi.R2.QdAll
import Googology.Trans.PoR.InaccPsi.R2.QtLay

/-!
# QdLay: THE LAYER AT EVERY FIXED POINT OF `Γ` BELOW `B₃`, WITH THE ATOMS OF `qtU S` (WITH LEMMA IMG AT THE VEBLEN
LEVELS)

As `Qc.QcLay` up to `B₃`, with the atom system `Qt.qtU S`.  A layer at a fixed point `F ∈ [B_Γ, B₃)` of `Γ`
(`QdLay S F`: gate the gate of `F`, top reading `vD F`, reading `F` with the atoms of `qtU S`, terms for every code
below `F`) gives the base layer `Qd.QdDS.QBase` of the segment of `F` (`qdBase`), so the reading system
`Qd.QdDS.toRS` of every digit system over the segment base `F` gives the layers at the atom indices of the segment
(`qdAt_of`).  Below `B₂` the layers of `Qc` with the same readings (`Qt.qt_qc_th`, `Qt.qt_poly_of_qc`); from `B₂` on
the layer at a fixed point is the union of the atom layers below it (`qdLay_union`).

* `qd_F_data`, `qd_DF` (**the facts of the reading `F(x)`**), `qd_DF_pi`, `qd_Fx_cl`, `qd_F_atom`;
* `QdLay`, `qdLay_low`, `qd_ladH`, `qdBase` (**the base layer of the segment**);
* `QdAt`, `qdAt_of` (**the layer at an atom index**), `qd_cb_gate`, `qd_F_lt`, `qd_F_top`, `qdLayF`, `qdLay_union`,
  `qdLay_all` (**A LAYER AT EVERY FIXED POINT `B_Γ ≤ F < B₃` OF `Γ`**), `qd_layAt` (**`ZmLayA (qtU S) S F`**).

No new axiom.  New definitions: `QdLay`, `qdBase`, `QdAt`, `qdLayF`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Googology.Trans.PoR.InaccPsi.R2.Qd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Tf Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Yr Googology.Trans.PoR.InaccPsi.R2.Yw Googology.Trans.PoR.InaccPsi.R2.Gd
  Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Zb
  Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Yh Googology.Trans.PoR.InaccPsi.R2.Zm
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Xk Googology.Trans.PoR.InaccPsi.R2.Gm
  Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Trans.PoR.InaccPsi.R2.Gs
  Googology.Trans.PoR.InaccPsi.R2.Va Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Qc
  Googology.Trans.PoR.InaccPsi.R2.Qt

variable (S : InaccSeq.{0}) (hI : QdImgH)

/-! ## The reading of a fixed point of `Γ` below `B₃` -/

section DF

variable {F : Ordinal.{0}} (hF : gamma F = F) (hBF : tfBG ≤ F) (hFB : F < qdB)
include S hI hF hBF hFB

/-- The data of a fixed point `F > B_Γ`: an atom, a limit of `ε`-numbers, the systems below it. -/
theorem qd_F_data (hBF' : tfBG < F) :
    InE F ∧ YhAt F ∧ ¬ yhJ F < F ∧ (∀ e, InE e → e < F → eN e < F) ∧
      (∀ e, InE e → tfBG ≤ e → e < F → QdGood e) := by
  have hOF : Om1 < F := tfBG_gt.trans hBF'
  refine ⟨zm_fix_E (zm_fix_of_gamma hF), ⟨by rw [← hF]; exact Lq.lq_gamma_SC _, hOF⟩, ?_, vs_fix_lim hF,
    fun e he heB heE => qdGood_all S hI e he heB (heE.trans hFB)⟩
  have h := yhJ_gcG F; rw [vs_gcG_fix hF hOF] at h; rw [h]; exact lt_irrefl _

/-- **The facts of the reading `F(x)` of a fixed point `F ≥ B_Γ` of `Γ` above its gate**: a closed point of
`Tˣ ∩ (x, Ω₁)` under `YBd`. -/
theorem qd_DF {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hgx : max ω (qdQEt F) < x) :
    vD F x ∈ Tset x ∧ InE (vD F x) ∧ x < vD F x ∧ YBd x (vD F x) ∧ YwClosed x (vD F x) ∧ vD F x < Om1 := by
  rcases lt_or_ge F ucB with hFX | hXF
  · rw [qdQEt_low hFX] at hgx
    obtain ⟨hT, hE, hxF, hX, hcl, h1⟩ := qs_DF hF hBF hFX hx hx1 hgx
    rw [vD_low hFX]
    exact ⟨hT, hE, hxF, yBd_of_qc hX, hcl, h1⟩
  · have hBF' : tfBG < F := (tl_BG_lt_X.trans uc_X_lt_B).trans_le hXF
    obtain ⟨hFE, hA, hi, hlim, hIH⟩ := qd_F_data S hI hF hBF hFB hBF'
    obtain ⟨-, hcl, hVT, hVE, hxV, hVX, hV1⟩ := qd_fx_V S hFE hBF' hFB hXF hlim hIH hA hi hx hx1 hI hgx
    rw [vD_base' hFE (va_G_le_BG.trans hBF) hFB]
    exact ⟨hVT, hVE, hxV, hVX, hcl, hV1⟩

/-- **The reading of a fixed point is exact.** -/
theorem qd_DF_pi {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) (hgσ : max ω (qdQEt F) < σ) :
    vD F ρ ∈ TB ρ σ ∧ R2.pi σ ρ (vD F ρ) = vD F σ := by
  rcases lt_or_ge F ucB with hFX | hXF
  · rw [qdQEt_low hFX] at hgσ
    rw [vD_low hFX, vD_low hFX]
    exact qs_DF_pi hF hBF hFX hB hgσ
  · have hBF' : tfBG < F := (tl_BG_lt_X.trans uc_X_lt_B).trans_le hXF
    obtain ⟨hFE, hA, hi, hlim, hIH⟩ := qd_F_data S hI hF hBF hFB hBF'
    have hG : gcG 0 ≤ F := va_G_le_BG.trans hBF
    rw [vD_base' hFE hG hFB, vD_base' hFE hG hFB]
    exact qd_fx_pi S hFE hBF' hFB hXF hlim hIH hA hi hB hgσ

/-- **A fixed point is a code over every strongly critical `Z` above its gate.** -/
theorem qd_Fx_cl {Z : Ordinal.{0}} (hZ : SC Z) (hgZ : max ω (qdQEt F) < Z) : QdCl Z F := by
  rcases lt_or_ge F ucB with hFX | hXF
  · rw [qdQEt_low hFX] at hgZ
    exact QdCl.uc (qs_Fx_cl hF hBF hFX hZ hgZ)
  · have hBF' : tfBG < F := (tl_BG_lt_X.trans uc_X_lt_B).trans_le hXF
    obtain ⟨hFE, hA, hi, hlim, hIH⟩ := qd_F_data S hI hF hBF hFB hBF'
    exact qd_fx_cl S hFE hBF' hFB hXF hlim hIH hA hi hZ hgZ

/-- **A fixed point is an atom of `qtU S` over every strongly critical `Z` above its gate.** -/
theorem qd_F_atom {Z : Ordinal.{0}} (hZ : SC Z) (hgZ : max ω (qdQEt F) < Z) : GxCl Z ((qtU S).At Z) F := by
  have hSC : SC F := by rw [← hF]; exact Lq.lq_gamma_SC _
  have hOF : Om 1 < F := by rw [← Br.Om1_eq]; exact tfBG_gt.trans_le hBF
  have hFθ : F < ConjT.th S := hFB.trans_le qd_B3_le_th
  refine GxCl.atom (show F ∈ qtAt S Z from ⟨hSC, hOF, hFθ, ?_⟩)
  rcases le_or_gt Z Om1 with hZ1 | hZ1
  · exact qd_cl_K0 hZ hZ1 F (qd_Fx_cl S hI hF hBF hFB hZ hgZ) hFB
  · exact (Vd.vd_K_th _ hFθ).mono (by rw [← Rj.rj_Om1]; exact hZ1.le)

end DF

/-! ## The layer at a fixed point -/

/-- **A layer at the fixed point `F`**: gate the gate of `F`, top reading `vD F`, reading `F` with the atoms of
`qtU S`, terms for every code below `F`. -/
def QdLay (S : InaccSeq.{0}) (F : Ordinal.{0}) : Prop :=
  ∃ L : GdB, L.g = max ω (qdQEt F) ∧ (∀ x, InE x → x < Om1 → L.g < x → L.K.E x = vD F x) ∧
    (∀ y, SC y → y < Om 1 → L.g < y → L.K.E y = gxTh y ((qtU S).At y) F) ∧ ZbPolyG (qtU S) L.K.sys F

/-- **Below `B₂` the layers of `Qc`.** -/
theorem qdLay_low {F : Ordinal.{0}} (hF : gamma F = F) (hBF : tfBG ≤ F) (hFB : F < ucB) : QdLay S F := by
  obtain ⟨L, hLg, hLE, hLtop, hLP⟩ := qsLay_all S F hF hBF hFB
  refine ⟨L, by rw [hLg, qdQEt_low hFB], fun x hx hx1 hg => by rw [hLE x hx hx1 hg, vD_low hFB],
    fun y hy hy1 hg => by rw [hLtop y hy hy1 hg]; exact (qt_qc_th hy hy1.le hFB.le).symm, qt_poly_of_qc hFB.le hLP⟩

include S hI in
/-- **The ladder hypothesis over a layer at `F`** with `e(x) = F(x)`. -/
theorem qd_ladH {F : Ordinal.{0}} (hF : gamma F = F) (hBF : tfBG ≤ F) (hFB : F < qdB) (U : GdB)
    (hUg : U.g = max ω (qdQEt F)) (hUE : ∀ x, InE x → x < Om1 → U.g < x → U.K.E x = vD F x) :
    YwLH U (fun x => vD F x) := by
  refine ⟨fun x hx hx1 hg => ?_, fun x hx hx1 hg => ?_, fun x hx hx1 hg j hjT hj => ?_, fun x hx hx1 hg => ?_,
    fun x hx hx1 hg => ?_, fun σ ρ hB hg => ?_⟩
  · obtain ⟨hT, -, -, -, -, h1⟩ := qd_DF S hI hF hBF hFB hx hx1 (hUg ▸ hg); exact ⟨hT, h1⟩
  · rw [hUE x hx hx1 hg]
  · obtain ⟨-, -, -, -, hcl, -⟩ := qd_DF S hI hF hBF hFB hx hx1 (hUg ▸ hg)
    rw [hUE x hx hx1 hg]; exact (hcl j hjT hj).le
  · obtain ⟨hT, -, -, -, -, h1⟩ := qd_DF S hI hF hBF hFB hx hx1 (hUg ▸ hg)
    rw [hUE x hx hx1 hg]; exact gmq_gt hx hx1 hT h1
  · obtain ⟨hT, -, -, hX, -, -⟩ := qd_DF S hI hF hBF hFB hx hx1 (hUg ▸ hg)
    exact yBd_gq hx hx1 hT hX
  · exact qd_DF_pi S hI hF hBF hFB hB (hUg ▸ hg)

/-- **THE BASE LAYER OF THE SEGMENT OF `F`**: the ladder over a layer at `F`, for a digit system over the segment
base `F` read `vD F`. -/
noncomputable def qdBase {F : Ordinal.{0}} (hF : gamma F = F) (hBF : tfBG ≤ F) (hFB : F < qdB)
    (hL : QdLay S F) (M : QdDS) (hMB : M.B = F) (hMD : M.Dv = vD F) (hEg : max ω (qdQEt F) ≤ M.Eg) :
    QdDS.QBase S M where
  L0 := ywLadB (Classical.choose hL) (fun x => vD F x)
    (qd_ladH S hI hF hBF hFB _ (Classical.choose_spec hL).1 (Classical.choose_spec hL).2.1)
  L0_g := by rw [ywLadB_g, (Classical.choose_spec hL).1]; exact hEg
  L0_E := fun x _ _ => by rw [ywLadB_E, hMD]
  L0_top := fun y hy hy1 hgy => by
    obtain ⟨hUg, -, hUtop, -⟩ := Classical.choose_spec hL
    have hc : ∀ Z, SC Z → (Classical.choose hL).g < Z → GxCl Z ((qtU S).At Z) F := fun Z hZ hgZ =>
      qd_F_atom S hI hF hBF hFB hZ (hUg ▸ hgZ)
    have hcQ : Ga.cQs F = gcG (F + 1) := by
      conv_lhs => rw [← vs_gcG_fix hF (tfBG_gt.trans_le hBF)]
      exact gc_cQs F
    rw [zbLad_top hc hUtop _ hy hy1 (hUg.trans_lt (hEg.trans_lt hgy)), hMB, hcQ]
  L0_poly := by
    obtain ⟨hUg, -, hUtop, hUP⟩ := Classical.choose_spec hL
    have hc : ∀ Z, SC Z → (Classical.choose hL).g < Z → GxCl Z ((qtU S).At Z) F := fun Z hZ hgZ =>
      qd_F_atom S hI hF hBF hFB hZ (hUg ▸ hgZ)
    have hcO : Om 1 ≤ F := by rw [← Br.Om1_eq]; exact (tfBG_gt.trans_le hBF).le
    have h := zbLad_poly hc hcO hUtop (qd_ladH S hI hF hBF hFB _ hUg (Classical.choose_spec hL).2.1) qtU_th hUP
    have hcQ : Ga.cQs F = gcG (F + 1) := by
      conv_lhs => rw [← vs_gcG_fix hF (tfBG_gt.trans_le hBF)]
      exact gc_cQs F
    rw [hMB]; rwa [hcQ] at h
  Dv_ge := fun x hx hx1 hgx => by
    obtain ⟨-, -, hxF, -, hcl, -⟩ := qd_DF S hI hF hBF hFB hx hx1 (hEg.trans_lt hgx)
    rw [hMD]; exact (ywBG hx hx1).2.2 _ hxF hcl

/-! ## The layers at the atom indices of a segment -/

/-- **A layer at the atom index `c`** past its segment base `F = vaFB c`: reading `gq(F(x) + o(x))`, `o = c − (F+1)`,
top code `gcG c`; its gate is above the gates of `F` and `o`, and below every limit above the gate of `c`. -/
def QdAt (S : InaccSeq.{0}) (c : Ordinal.{0}) : Prop :=
  ∃ L : GdB, (∀ Z, IsSuccLimit Z → ω < Z → qdGt c < Z → L.g < Z) ∧
    (∀ x, L.g < x → qdGt (vaFB c) < x ∧ qdGt (c - (vaFB c + 1)) < x) ∧
    (∀ x, InE x → x < Om1 → L.g < x → L.K.E x = gq (vD (vaFB c) x + vD (c - (vaFB c + 1)) x) x) ∧
    (∀ y, SC y → y < Om 1 → L.g < y → L.K.E y = gxTh y ((qtU S).At y) (gcG c)) ∧ ZbPolyG (qtU S) L.K.sys (gcG c)

include hI in
/-- **The layer at an atom index of a segment**, from the layer at its segment base. -/
theorem qdAt_of {c : Ordinal.{0}} (hBc : tfBG ≤ c) (hFc : vaFB c < c) (hcB : c < qdB)
    (hL : QdLay S (vaFB c)) : QdAt S c := by
  have hGc : gcG 0 ≤ c := va_G_le_BG.trans hBc
  have hFfix := vs_FB_fix hBc
  have hBF := vs_FB_ge hBc
  have hFB : vaFB c < qdB := hFc.trans hcB
  have heB : vaFB c ≤ guE c := gl_E_max (vs_FB_E hBc) (vs_FB_gt hBc) (vs_FB_le hBc)
  have hec : guE c ≤ c := gl_E_le (yh_gfE_le hGc)
  have hce : c < eN (guE c) := gl_lt_eN (yh_gfE_le hGc)
  have heE := guE_E c
  have hBe : tfBG ≤ guE c := hBF.trans heB
  have hE'B : eN (guE c) < qdB := qd_eN_lt_B3 (hec.trans_lt hcB)
  have hBE' : tfBG ≤ eN (guE c) := hBe.trans (lt_eN _).le
  obtain ⟨M, hME, hEg, -, hR, hG, hMB, hMD⟩ := qdGood_all S hI _ (eN_E _) hBE' hE'B
  have hFB' : vaFB (eN (guE c)) = vaFB c := by
    rw [vs_FB_eN hBe]; exact vs_FB_of_le hBc heB hec
  rw [hFB'] at hMB hMD
  have hEgF : max ω (qdQEt (vaFB c)) ≤ M.Eg := by
    rw [hEg]
    have h := qd_FB_gate' hBE' hE'B
    rw [hFB', qdGt_base' (vs_FB_E hBc) (va_G_le_BG.trans hBF) hFB,
      qdGt_base' (eN_E _) (va_G_le_BG.trans hBE') hE'B] at h
    exact max_le (le_max_left _ _) h
  have hBME : M.B < M.E := by rw [hMB, hME]; exact hFc.trans hce
  have hc0 : M.B + 1 ≤ c := by rw [hMB]; exact Order.add_one_le_of_lt hFc
  have hcBd : c < M.E := by rw [hME]; exact hce
  set RS := M.toRS S hBME (qdBase S hI hFfix hBF hFB hL M hMB hMD hEgF) with hRS
  obtain ⟨L, hLg, hLE, hLtop, hLP⟩ := RS.lay c hc0 hcBd
  have hgt : RS.gt c = max M.Eg (M.G (c - (vaFB c + 1))) := by
    show max M.Eg (M.G (c - (M.B + 1))) = _; rw [hMB]
  have hoE : c - (vaFB c + 1) < eN (guE c) := (Ordinal.sub_le_self _ _).trans_lt hce
  refine ⟨L, fun Z hZ hωZ hgZ => ?_, fun x hgx => ?_, fun x hx hx1 hgx => ?_, fun y hy hy1 hgy => ?_, hLP⟩
  · -- the gate is below every limit above the gate of `c`
    have hQ : qdQEt (guE c) < Z := by
      rw [qdGt_dec' hGc hcB] at hgZ; exact (le_max_left _ _).trans_lt ((le_max_left _ _).trans_lt hgZ)
    have hEgZ : M.Eg < Z := by rw [hEg]; exact max_lt hωZ (qd_QE_eN_lt heE hBe (hec.trans_lt hcB) hZ hωZ hQ)
    rw [hLg, hgt]
    refine max_lt hEgZ ?_
    rcases eq_or_ne (c - (vaFB c + 1)) 0 with h0 | h0
    · rw [h0, M.G0]; exact hZ.bot_lt
    · rw [hG _ hoE h0]
      exact max_lt hEgZ ((qd_off_gate' (vs_FB_E hBc) (va_G_le_BG.trans hBF) hcB hFc).trans_lt (max_lt hωZ hgZ))
  · -- the gates of the base and of the offset are below the gate
    rw [hLg, hgt] at hgx
    have hEgx : M.Eg < x := (le_max_left _ _).trans_lt hgx
    refine ⟨?_, ?_⟩
    · rw [qdGt_base' (vs_FB_E hBc) (va_G_le_BG.trans hBF) hFB]
      exact (le_max_right _ _).trans_lt (hEgF.trans_lt hEgx)
    · rcases eq_or_ne (c - (vaFB c + 1)) 0 with h0 | h0
      · rw [h0, qdGt_zero]; exact (zero_le).trans_lt hEgx
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
theorem qd_cb_gate {b Z : Ordinal.{0}} (hZ : InE Z) (hbB : vsCb b < qdB) (hgb : qdGt b < Z) :
    qdGt (vsCb b) < Z := by
  have hωZ : ω < Z := omega0_lt_inE hZ
  have hZP : ∀ u v, u < Z → v < Z → u + v < Z := fun u v hu hv => (inE_indec hZ).add_lt hu hv
  have hb'B : tfBG ≤ max b tfBG := le_max_right _ _
  have hmB : max b tfBG < qdB := le_add_self.trans_lt hbB
  have hBGB : tfBG < ucB := tl_BG_lt_X.trans uc_X_lt_B
  have hgb' : qdGt (max b tfBG) < Z := by
    rcases le_total b tfBG with h | h
    · rw [max_eq_right h, qdGt_low hBGB, qcG_low tl_BG_lt_X, yrG_base (Low.opow_eq_self_of_SC tfBG_SC) va_G_le_BG,
        va_QE_BG]
      exact hZ.pos
    · rw [max_eq_left h]; exact hgb
  have hgF : qdGt (vaFB (max b tfBG)) < Z := (qd_FB_gate' hb'B hmB).trans_lt (max_lt hωZ hgb')
  have h1 : qdGt (1 : Ordinal.{0}) < Z := by
    rw [show (1 : Ordinal.{0}) = ((1 : ℕ) : Ordinal.{0}) by norm_num, qdGt_nat]
    exact (natCast_lt_omega0 1).trans hωZ
  unfold vsCb at hbB ⊢
  exact qd_add hZP hωZ _ _ hbB (qd_add hZP hωZ _ _ (le_self_add.trans_lt hbB) hgF h1) hgb'

/-! ## The layer at a fixed point from `B₂` on: the union of the atom layers below it -/

section Fix

variable {F : Ordinal.{0}} (hF : gamma F = F) (hXF : ucB ≤ F) (hFB : F < qdB)
include S hI hF hXF hFB

theorem qd_F_lt {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hgx : max ω (qdQEt F) < x) :
    ∀ c, c < F → qdGt c < x → vD c x < vD F x := by
  have hBF' : tfBG < F := (tl_BG_lt_X.trans uc_X_lt_B).trans_le hXF
  obtain ⟨hFE, hA, hi, hlim, hIH⟩ := qd_F_data S hI hF hBF'.le hFB hBF'
  intro c hc hg
  rw [vD_base' hFE (va_G_le_BG.trans hBF'.le) hFB]
  exact qd_fx_lt S hFE hBF' hFB hXF hlim hIH hA hi hx hx1 hI hgx c hc hg

theorem qd_F_top {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hgx : max ω (qdQEt F) < x) :
    ∀ ν, ν < vD F x → ∃ b, b < F ∧ qdGt b < x ∧ ν ≤ vD b x := by
  have hBF' : tfBG < F := (tl_BG_lt_X.trans uc_X_lt_B).trans_le hXF
  obtain ⟨hFE, hA, hi, hlim, hIH⟩ := qd_F_data S hI hF hBF'.le hFB hBF'
  intro ν hν
  rw [vD_base' hFE (va_G_le_BG.trans hBF'.le) hFB] at hν
  exact (qdTopFix S hFE hBF' hFB hXF hlim hIH hA hi hI).top x hx hx1 hgx ν hν

variable (hAt : ∀ b, b < F → QdAt S (vsCb b))

/-- **The union data at a fixed point**: the atom layers `vsCb b`, `b < F`, and the layer of `B_Γ` for the
constants; target `F(x)`. -/
noncomputable def qdLayF : YwUF (max ω (qdQEt F)) where
  I := Option {b : Ordinal.{0} // b < F}
  K := fun i => Option.elim i ywBGB fun b => Classical.choose (hAt b.1 b.2)
  gi := fun i => Option.elim i 0 fun b => (Classical.choose (hAt b.1 b.2)).g
  i0 := none
  g_le := fun i => by
    cases i with
    | none => exact le_of_eq ywBGB_g
    | some b => exact le_rfl
  gi0 := rfl
  T := fun x => vD F x
  T_E := fun x hx hx1 hg => (qd_DF S hI hF ((tl_BG_lt_X.trans uc_X_lt_B).le.trans hXF) hFB hx hx1 hg).2.1
  T_mem := fun x hx hx1 hg => (qd_DF S hI hF ((tl_BG_lt_X.trans uc_X_lt_B).le.trans hXF) hFB hx hx1 hg).1
  T_gt := fun x hx hx1 hg => (qd_DF S hI hF ((tl_BG_lt_X.trans uc_X_lt_B).le.trans hXF) hFB hx hx1 hg).2.2.1
  T_X := fun x hx hx1 hg => (qd_DF S hI hF ((tl_BG_lt_X.trans uc_X_lt_B).le.trans hXF) hFB hx hx1 hg).2.2.2.1
  E_lt := fun i x hx hx1 hg hgi => by
    have hBF' : tfBG < F := (tl_BG_lt_X.trans uc_X_lt_B).trans_le hXF
    have hBGB : tfBG < ucB := tl_BG_lt_X.trans uc_X_lt_B
    cases i with
    | none =>
      show ywBGB.K.E x < vD F x
      rw [ywBGB_E, ← vR_BG x, ← vQ_low tl_BG_lt_X, ← vD_low hBGB]
      refine qd_F_lt S hI hF hXF hFB hx hx1 hg _ hBF' ?_
      rw [qdGt_low hBGB, qcG_low tl_BG_lt_X, yrG_base (Low.opow_eq_self_of_SC tfBG_SC) va_G_le_BG, va_QE_BG]
      exact hx.pos
    | some b =>
      obtain ⟨-, hgo, hE, -, -⟩ := Classical.choose_spec (hAt b.1 b.2)
      obtain ⟨-, -, hlt, hcF, -, -, -⟩ := vs_cb_facts hF hBF' b.2
      obtain ⟨hgF', hgo'⟩ := hgo x hgi
      show (Classical.choose (hAt b.1 b.2)).K.E x < vD F x
      rw [hE x hx hx1 hgi]
      obtain ⟨hDT, hDE, -, -, hcl, hD1⟩ := qd_DF S hI hF hBF'.le hFB hx hx1 hg
      have h1 := qd_F_lt S hI hF hXF hFB hx hx1 hg _ (hlt.trans hcF) hgF'
      have h2 := qd_F_lt S hI hF hXF hFB hx hx1 hg _ ((Ordinal.sub_le_self _ _).trans_lt hcF) hgo'
      have hsum := (inE_indec hDE).add_lt h1 h2
      exact hcl _ (vz_T_down hx hx1 hDT hD1 hsum.le) hsum
  cof := fun x hx hx1 hg v hv => by
    have hBF' : tfBG < F := (tl_BG_lt_X.trans uc_X_lt_B).trans_le hXF
    have hBGB : tfBG < ucB := tl_BG_lt_X.trans uc_X_lt_B
    obtain ⟨hFE, -, -, hlim, hIH⟩ := qd_F_data S hI hF hBF'.le hFB hBF'
    obtain ⟨b, hb, hgb, hvb⟩ := qd_F_top S hI hF hXF hFB hx hx1 hg v hv
    obtain ⟨hgate, hgo, hE, -, -⟩ := Classical.choose_spec (hAt b hb)
    obtain ⟨-, hseg, -, hcF, hsub, -, -⟩ := vs_cb_facts hF hBF' hb
    have hgL : (Classical.choose (hAt b hb)).g < x :=
      hgate x (ev_isSuccLimit_of_inE hx) (omega0_lt_inE hx) (qd_cb_gate hx (hcF.trans hFB) hgb)
    refine ⟨some ⟨b, hb⟩, hgL, ?_⟩
    show v < (Classical.choose (hAt b hb)).K.E x
    rw [hE x hx hx1 hgL, hsub, hseg]
    obtain ⟨hgF', hgb'⟩ := hgo x hgL
    rw [hsub] at hgb'
    rw [hseg] at hgF'
    have hb'F : max b tfBG < F := max_lt hb hBF'
    obtain ⟨hb'T, hb'1, -⟩ := qd_T S hFE hBF' hFB hlim hIH hx hx1 hb'F hgb'
    obtain ⟨hFT, hF1, -⟩ := qd_T S hFE hBF' hFB hlim hIH hx hx1 ((vs_FB_le (le_max_right _ _)).trans_lt hb'F) hgF'
    have hvb' : v ≤ vD (max b tfBG) x := by
      rcases lt_or_ge b tfBG with h | h
      · rw [max_eq_right h.le]
        have hgB : qdGt tfBG < x := by
          rw [qdGt_low hBGB, qcG_low tl_BG_lt_X, yrG_base (Low.opow_eq_self_of_SC tfBG_SC) va_G_le_BG, va_QE_BG]
          exact hx.pos
        exact hvb.trans (qd_mono S hFE hBF' hFB hlim hIH hx hx1 h hBF' hgb hgB).le
      · rw [max_eq_left h]; exact hvb
    exact hvb'.trans_lt ((gmq_gt hx hx1 hb'T hb'1).trans_le
      (gmq_mono hx hx1 (vzT_add hx hx1 hFT hb'T) ((inE_indec gl_Om1_E).add_lt hF1 hb'1) le_add_self))
  pi := fun σ ρ _ _ hB hg => qd_DF_pi S hI hF ((tl_BG_lt_X.trans uc_X_lt_B).le.trans hXF) hFB hB hg

end Fix

include hI in
/-- **THE LAYER AT A FIXED POINT OF `Γ` FROM `B₂` ON**: the union of the atom layers below it. -/
theorem qdLay_union {F : Ordinal.{0}} (hF : gamma F = F) (hXF : ucB ≤ F) (hFB : F < qdB)
    (hAt : ∀ b, b < F → QdAt S (vsCb b)) : QdLay S F := by
  have hBF' : tfBG < F := (tl_BG_lt_X.trans uc_X_lt_B).trans_le hXF
  set Fu := qdLayF S hI hF hXF hFB hAt with hFu
  have hres := zbUnion_codes (A := qtU S) Fu (fun i => Option.elim i tfBG fun b => gcG (vsCb b.1)) (Tc := F)
    (fun i y hy hy1 hi => by
      cases i with
      | none =>
        show ywBGB.K.E y = gxTh y ((qtU S).At y) tfBG
        rw [qcBG_top S hy hy1]; exact (qt_qc_th hy hy1.le (tl_BG_lt_X.trans uc_X_lt_B).le).symm
      | some b => exact (Classical.choose_spec (hAt b.1 b.2)).2.2.2.1 y hy hy1 hi)
    (fun i => by
      cases i with
      | none => exact qt_poly_of_qc (tl_BG_lt_X.trans uc_X_lt_B).le (qcBG_poly S)
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
      have hgd : qdGt d < Z := qd_gate S hZ hZ1' d ((qd_cl_qt hZ hZ1' (hdT.trans hFB)).1 hd) (hdT.trans hFB)
      obtain ⟨hgate, -⟩ := Classical.choose_spec (hAt d hdT)
      obtain ⟨-, -, -, hcF, -, hdc, hcg⟩ := vs_cb_facts hF hBF' hdT
      refine ⟨some ⟨d, hdT⟩, hgate Z (ev_isSuccLimit_of_inE hZE) (omega0_lt_inE hZE)
        (qd_cb_gate hZE (hcF.trans hFB) hgd), ?_⟩
      show d < gcG (vsCb d)
      exact ((le_max_left d tfBG).trans hdc).trans_lt hcg)
  exact ⟨ywLimB Fu, rfl, fun x _ _ _ => rfl, hres.1, hres.2⟩

include hI in
/-- **A LAYER AT EVERY FIXED POINT `B_Γ ≤ F < B₃` OF `Γ`**: below `B₂` the layers of `Qc`; from `B₂` on one induction
over the fixed points. -/
theorem qdLay_all : ∀ F, gamma F = F → tfBG ≤ F → F < qdB → QdLay S F := by
  intro F
  induction F using WellFoundedLT.induction with
  | ind F IH =>
  intro hF hBF hFB
  rcases lt_or_ge F ucB with hFX | hXF
  · exact qdLay_low S hF hBF hFX
  have hBF' : tfBG < F := (tl_BG_lt_X.trans uc_X_lt_B).trans_le hXF
  refine qdLay_union S hI hF hXF hFB fun b hb => ?_
  obtain ⟨hBc, -, hlt', hcF, -, -, -⟩ := vs_cb_facts hF hBF' hb
  exact qdAt_of S hI hBc hlt' (hcF.trans hFB)
    (IH _ (hlt'.trans hcF) (vs_FB_fix hBc) (vs_FB_ge hBc) ((hlt'.trans hcF).trans hFB))

include hI in
/-- **The layer for the index `F`**, a fixed point of `Γ` below `B₃` with gate below `K`, with the atoms of
`qtU S`. -/
theorem qd_layAt {F : Ordinal.{0}} (hF : gamma F = F) (hBF : tfBG ≤ F) (hFB : F < qdB)
    (hK : max ω (qdQEt F) < Td.tdK S) : ZmLayA (qtU S) S F := by
  obtain ⟨L, hLg, hLE, hLtop, hLP⟩ := qdLay_all S hI F hF hBF hFB
  have hOF : Om1 < F := tfBG_gt.trans_le hBF
  refine ⟨L, F, (vs_gcG_fix hF hOF).le, by rw [hLg]; exact hK, hFB.le.trans qd_B3_le_th,
    by rw [← Br.Om1_eq]; exact hOF.le, zm_fix_E (zm_fix_of_gamma hF), hLtop, hLP,
    fun Z hZ hKZ => qd_F_atom S hI hF hBF hFB hZ (hK.trans_le hKZ), fun x hx hx1 hgx => ?_⟩
  rw [hLE x hx hx1 hgx]
  obtain ⟨-, -, hxF, -, hcl, -⟩ := qd_DF S hI hF hBF hFB hx hx1 (hLg ▸ hgx)
  have hD := (ywBG hx hx1).2.2 _ hxF hcl
  have h0T : (0 : Ordinal.{0}) ∈ Tset x := mem_T_of_le hx hx1 zero_le
  obtain ⟨-, -, hDcl⟩ := ywD_closed hx hx1
  have h1 : eN x < gq 0 x := gmq_eN_lt hx hx1 h0T (hx.pos.trans hx1)
  have h2 : gq 0 x < ywV 1 0 x := hDcl 0 h0T (hx.pos.trans (ywD_closed hx hx1).1)
  exact (h1.trans h2).trans_le hD

end Googology.Trans.PoR.InaccPsi.R2.Qd
