import Googology.Trans.PoR.InaccPsi.R2.QcCnt
import Googology.Trans.PoR.InaccPsi.R2.ZmPast
import Googology.Trans.PoR.InaccPsi.R2.ZgTl

/-!
# QcConv: BELOW `X` THE ATOM SYSTEMS `zbU` AND `qcU` HAVE THE SAME CODES, READINGS AND LAYERS

`Zb.zbU` (the codes of `TlCl` below `X` with the `Yr` atoms) and `Qc.qcU` (the codes of `UcCl` below `B₂`) agree below
`X`: every atom of `zbU` is a code of `TlCl` (`Zg.zgYr` for the `Yr` atoms), and below `X` the codes of `UcCl` are those
of `TlCl` (`Uc.uc_cl_lt_X`).  So every layer with the atoms of `zbU` and its top at most `X` is one with the atoms of
`qcU`.

* `qc_zbU_tl` (**a code over the atoms of `zbU` is a code of `TlCl`**), `qc_tl_qcU`, `qc_qcU_zbU`, `qc_zbU_qcU`
  (**below `X` the two atom systems have the same codes**), `qc_th_conv` (**the same readings `Θ_y` up to `X`**),
  `qc_poly_conv`, `qc_lay_conv` (**`ZbLayAt S B` with a top `< X` ⇒ `ZmLayA qcU S B`**).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Zb
  Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Tf
  Googology.Trans.PoR.InaccPsi.R2.Gd Googology.Trans.PoR.InaccPsi.R2.Zm

/-- **A code over the atoms of `zbU` is a code of `TlCl`.** -/
theorem qc_zbU_tl {Z d : Ordinal.{0}} (hZ : 0 < Z) (hd : GxCl Z (zbU.At Z) d) : TlCl Z d := by
  induction hd with
  | small h => exact TlCl.small h
  | om => rw [← Br.Om1_eq]; exact TlCl.om
  | atom hs =>
    rcases hs with hs | ⟨c, hc, hg, rfl⟩
    · exact hs.2.2.2
    · have hcT : TlCl Z c := (Zg.zgYr hZ c hc hg).1
      have hTa : TlCl Z (Om1 + 1 + c) := TlCl.add (TlCl.add TlCl.om (TlCl.one hZ)) hcT
      rw [tf_gcG]
      exact TlCl.gam hZ hTa ((lt_add_one _).trans_le le_self_add)
  | add _ _ ihx ihy => exact TlCl.add ihx ihy
  | phi _ _ ihx ihy => exact TlCl.phi ihx ihy

/-- **A code of `TlCl` below `X` is a code over the atoms of `qcU`.** -/
theorem qc_tl_qcU {Z d : Ordinal.{0}} (hd : TlCl Z d) (hdX : d < tlX) : GxCl Z (qcU.At Z) d :=
  (zbTl_gx hd hdX).mono le_rfl (qc_tl_sub Z)

/-- **Below `X` a code over the atoms of `qcU` is one over the atoms of `zbU`.** -/
theorem qc_qcU_zbU {Z d : Ordinal.{0}} (hd : GxCl Z (qcU.At Z) d) (hdX : d < tlX) : GxCl Z (zbU.At Z) d :=
  (zbTl_gx (uc_cl_lt_X (qc_of_gx hd) hdX) hdX).mono le_rfl fun _ hs => Or.inl hs

/-- **Below `X` a code over the atoms of `zbU` is one over the atoms of `qcU`.** -/
theorem qc_zbU_qcU {Z d : Ordinal.{0}} (hZ : 0 < Z) (hd : GxCl Z (zbU.At Z) d) (hdX : d < tlX) :
    GxCl Z (qcU.At Z) d :=
  qc_tl_qcU (qc_zbU_tl hZ hd) hdX

/-- **The same readings up to `X`.** -/
theorem qc_th_conv {y m : Ordinal.{0}} (hy : 0 < y) (hm : m ≤ tlX) : gxTh y (qcU.At y) m = gxTh y (zbU.At y) m :=
  Gg.ggOtp_congr m fun d hd => ⟨fun h => qc_qcU_zbU h (hd.trans_le hm), fun h => qc_zbU_qcU hy h (hd.trans_le hm)⟩

/-- **Terms for the codes below `E ≤ X` with the atoms of `zbU` are terms with the atoms of `qcU`.** -/
theorem qc_poly_conv {g : Ordinal.{0}} {K : GdSys g} {E : Ordinal.{0}} (hE : E ≤ tlX) (hP : ZbPolyG zbU K E) :
    ZbPolyG qcU K E := by
  intro Z c hg hc hcE
  obtain ⟨s, hs⟩ := hP Z c hg (qc_qcU_zbU hc (hcE.trans_le hE)) hcE
  refine ⟨s, fun y hy hy1 hZy => ⟨(hs y hy hy1 hZy).1, ?_⟩⟩
  rw [(hs y hy hy1 hZy).2, qc_th_conv hy.1 ((hcE.trans_le hE).le)]

/-- **A layer with the atoms of `zbU` and its top below `X` is one with the atoms of `qcU`.** -/
theorem qc_lay_conv {S : InaccSeq.{0}} {B : Ordinal.{0}} (h : ZbLayAt S B) : ZmLayA qcU S B := by
  obtain ⟨L, T, hBT, hg, hTV, hTO, hTE, htop, hP, hcl, htopE⟩ := h
  have hTX : T ≤ tlX := hTV
  have hTlt : T < tlX := by
    rcases hTX.lt_or_eq with h1 | h1
    · exact h1
    · exfalso
      have hK := hcl (Td.tdK S) Td.tdK_SC le_rfl
      have := zbU.cl_lt_V Td.tdK_lt_Om1.le hK
      rw [h1] at this
      exact lt_irrefl _ this
  refine ⟨L, T, hBT, hg, hTX.trans uc_X_lt_B.le, hTO, hTE, fun y hy hy1 hgy => ?_, qc_poly_conv hTX hP,
    fun Z hZ hKZ => qc_zbU_qcU hZ.1 (hcl Z hZ hKZ) hTlt, htopE⟩
  rw [htop y hy hy1 hgy, qc_th_conv hy.1 hTX]

end Googology.Trans.PoR.InaccPsi.R2.Qc
