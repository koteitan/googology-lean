import Googology.Trans.PoR.InaccPsi.R2.QtK
import Googology.Trans.PoR.InaccPsi.R2.QcPast

/-!
# QtLay: THE LAYERS OF `qcU` BELOW `B₂` ARE LAYERS OF `qtU`

`B₂ = Uc.ucB < θ`.  The atoms of `Qc.qcU` over a strongly critical `Z` are atoms of `Qt.qtU S` (`Uo.uo_cl_iffK` for
`Z ≤ Ω₁`, `Uo.uo_K_big` above), and below `B₂` the codes and the readings over `Z ≤ Ω₁` agree (`Qt.qt_qc_codes`,
`Qt.qt_qc_th`).  So terms for the codes of `qcU` below `E ≤ B₂` are terms for those of `qtU` (a code over `Z` is a
code over the least strongly critical `Z' ≥ Z`), and every layer `Zm.ZmLayA qcU S B` is a layer `ZmLayA (qtU S) S B`;
in particular `Zm.ZmPastAt S c` holds with `qtU` for every `c < B₂`.

* `qt_qc_sub` (**`qcAt Z ⊆ qtAt S Z`**), `qt_SC_above`, `qt_poly_of_qc`, `qt_layA_of_qc` (**the layers of `qcU`
  below `B₂` are layers of `qtU`**), `qt_layA_mono`, `qt_past_lt_B2`.

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qt

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Zb
  Googology.Trans.PoR.InaccPsi.R2.Zm Googology.Trans.PoR.InaccPsi.R2.Gd Googology.Trans.PoR.InaccPsi.R2.Gc

variable {S : InaccSeq.{0}}

/-- **The atoms of `qcU` over a strongly critical `Z` are atoms of `qtU`.** -/
theorem qt_qc_sub {Z : Ordinal.{0}} (hZ : SC Z) : Qc.qcAt Z ⊆ qtAt S Z := fun s hs => by
  refine ⟨hs.1, hs.2.1, hs.2.2.1.trans Vd.vd_B_lt_th, ?_⟩
  rcases le_or_gt Z Om1 with hZ1 | hZ1
  · exact (Uo.uo_cl_iffK hZ hZ1 hs.2.2.1).1 hs.2.2.2
  · exact Uo.uo_K_big hZ1 hs.2.2.1

/-- The least strongly critical ordinal `≥ Z`, for `Z ≤ Ω₁`. -/
theorem qt_SC_above {Z : Ordinal.{0}} (hZ1 : Z ≤ Om 1) :
    ∃ Z', SC Z' ∧ Z ≤ Z' ∧ Z' ≤ Om 1 ∧ ∀ y, SC y → Z ≤ y → Z' ≤ y := by
  have hO : SC (Om 1 : Ordinal.{0}) := SC_Om one_ne_zero
  have hne : {w : Ordinal.{0} | SC w ∧ Z ≤ w}.Nonempty := ⟨Om 1, hO, hZ1⟩
  exact ⟨sInf _, (csInf_mem hne).1, (csInf_mem hne).2, csInf_le' ⟨hO, hZ1⟩,
    fun y hy hZy => csInf_le' ⟨hy, hZy⟩⟩

/-- **Terms for the codes of `qcU` below `E ≤ B₂` are terms for the codes of `qtU`.** -/
theorem qt_poly_of_qc {g E : Ordinal.{0}} {X : GdSys g} (hE : E ≤ Uc.ucB) (hP : ZbPolyG Qc.qcU X E) :
    ZbPolyG (qtU S) X E := by
  intro Z c hgZ hc hcE
  rcases le_or_gt Z (Om 1) with hZ1 | hZ1
  · obtain ⟨Z', hZ'S, hZZ', hZ'1, hmin⟩ := qt_SC_above hZ1
    have hc' : GxCl Z' (qtAt S Z') c := GxCl.mono hZZ' ((qtU S).mono Z Z' hZZ') hc
    have hcq : GxCl Z' (Qc.qcAt Z') c := (qt_qc_codes hZ'S hZ'1 (hcE.trans_le hE)).1 hc'
    obtain ⟨s, hs⟩ := hP Z' c (hgZ.trans_le hZZ') hcq hcE
    refine ⟨s, fun y hy hy1 hZy => ?_⟩
    obtain ⟨h1, h2⟩ := hs y hy hy1 (hmin y hy hZy)
    exact ⟨h1, by rw [h2]; exact (qt_qc_th hy hy1.le (hcE.le.trans hE)).symm⟩
  · have hZ0 : (0 : Ordinal.{0}) < Z := (zero_lt_one.trans Nm.one_lt_Om1).trans hZ1
    obtain ⟨s, -⟩ := hP Z 0 hgZ (GxCl.small hZ0) (lt_of_le_of_lt zero_le hcE)
    exact ⟨s, fun y _ hy1 hZy => absurd (hZ1.trans_le hZy) (not_lt.2 hy1.le)⟩

/-- **The layers of `qcU` (below `B₂`) are layers of `qtU`.** -/
theorem qt_layA_of_qc {B : Ordinal.{0}} (h : ZmLayA Qc.qcU S B) : ZmLayA (qtU S) S B := by
  obtain ⟨L, T, hBT, hg, hTV, hTO, hTE, htop, hP, hcl, hE⟩ := h
  have hTB : T ≤ Uc.ucB := hTV
  refine ⟨L, T, hBT, hg, hTB.trans Vd.vd_B_lt_th.le, hTO, hTE, fun y hy hy1 hgy => ?_, qt_poly_of_qc hTB hP,
    fun Z hZ hKZ => GxCl.mono le_rfl (qt_qc_sub hZ) (hcl Z hZ hKZ), hE⟩
  rw [htop y hy hy1 hgy]
  exact (qt_qc_th hy hy1.le hTB).symm

theorem qt_layA_mono {B B' : Ordinal.{0}} (h : B ≤ B') (hL : ZmLayA (qtU S) S B') : ZmLayA (qtU S) S B :=
  Qc.qc_layA_mono h hL

variable (S) in
/-- **`Zm.ZmPastAt S c` with the atom system `qtU` for every `c < B₂`.** -/
theorem qt_past_lt_B2 : ∀ c, c < Uc.ucB → ∀ B, B < gcG (c + 1) → ZmLayA (qtU S) S B := by
  intro c hc B hB
  have hBB : B < Uc.ucB := hB.trans (Qc.qc_gcG_lt_B (Uc.ucB_SC.isSuccLimit.add_one_lt hc))
  obtain ⟨n, hn⟩ := Qc.qcF_cof hBB
  obtain ⟨hf, hb, hFB, hK⟩ := Qc.qcF_facts S n
  exact qt_layA_mono hn.le (qt_layA_of_qc (Qc.qs_layAt S hf hb hFB hK))

end Googology.Trans.PoR.InaccPsi.R2.Qt
