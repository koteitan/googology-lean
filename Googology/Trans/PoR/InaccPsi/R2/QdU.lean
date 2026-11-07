import Googology.Trans.PoR.InaccPsi.R2.QdStp
import Googology.Trans.PoR.InaccPsi.R2.QcAll

/-!
# QdU: THE CLAUSES OF `vD`, `qdA`, `qdGt` ON ALL OF `[G, B₃)`, AND EVERY DIGIT SYSTEM BELOW `B₂` AS A `QdGood`

Below `B₂` the readings `vD`, `qdA` and the gates `qdGt`, `qdQEt` are `Qc.vQ`, `Qc.qcA`, `Qc.qcG`, `Qc.qcQE`; from `B₂`
on they have the same Cantor clause.  One statement on `[G, B₃)` for each:

* `vD_cnf'`, `vD_base'`, `vD_psi'`, `qdA_psi''`, `qd_FB_gate'`, `qd_QE_eN'`, `qd_QE_eN_lt`, `qd_sG'`, `qd_sR'`
  (**the step reads `vD` with the gates `qdGt`**);
* `qdGood_low` (**every `ε`-number `B_Γ ≤ e < B₂` carries a `QdGood`**, from `Qc.qsGood_all`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Yw
  Googology.Trans.PoR.InaccPsi.R2.Yh Googology.Trans.PoR.InaccPsi.R2.Va Googology.Trans.PoR.InaccPsi.R2.Tl
  Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Yr
  Googology.Trans.PoR.InaccPsi.R2.Zm Googology.Trans.PoR.InaccPsi.R2.Tf Googology.Trans.PoR.InaccPsi.R2.Gk
  Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gn Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Qc

/-- **The Cantor clause of `vD` on `[G, B₃)`.** -/
theorem vD_cnf' {e j d r : Ordinal.{0}} (he : InE e) (hGe : gcG 0 ≤ e) (hj : j ≠ 0) (hd0 : d ≠ 0) (hde : d < e)
    (hr : r < e ^ j) (hv : e ^ j * d + r < eN e) (hvB : e ^ j * d + r < qdB) (x : Ordinal.{0}) :
    vD (e ^ j * d + r) x = qdA e x ^ vD j x * vD d x + vD r x := by
  rcases lt_or_ge e ucB with hX | hX
  · have hvX : e ^ j * d + r < ucB := hv.trans (qc_eN_lt_B hX)
    have hjX : j < ucB := (((right_le_opow j (lu_one_lt_E he)).trans
      (le_mul_of_one_le_right' (one_le_iff_ne_zero.2 hd0))).trans le_self_add).trans_lt hvX
    have hrX : r < ucB := (hr.trans_le (le_mul_of_one_le_right' (one_le_iff_ne_zero.2 hd0))).trans_le le_self_add
      |>.trans hvX
    rw [vD_low hvX, vQ_cnf' he hGe hj hd0 hde hr hv hvX, qdA_low hX, vD_low hjX, vD_low (hde.trans hX), vD_low hrX]
  · exact vD_cnf he hX hj hd0 hde hr hv hvB x

/-- **An `ε`-number code `e ∈ [G, B₃)` reads `qdA e`.** -/
theorem vD_base' {e : Ordinal.{0}} (he : InE e) (hGe : gcG 0 ≤ e) (heB : e < qdB) (x : Ordinal.{0}) :
    vD e x = qdA e x := by
  rcases lt_or_ge e ucB with hX | hX
  · rw [vD_low hX, vQ_base' he hGe hX, qdA_low hX]
  · exact vD_base he hX heB x

/-- **A non-atom `ε`-number code `e ∈ (G, B₃)` reads `ϑˣ(Ω₁·(yhK e)(x) + (yhI e)(x))`.** -/
theorem qdA_psi'' {e : Ordinal.{0}} (he : InE e) (hGe : gcG 0 < e) (heB : e < qdB) (hA : ¬ YhAt e)
    (x : Ordinal.{0}) : qdA e x = glA (vD (yhK e) x) (vD (yhI e) x) x := by
  rcases lt_or_ge e ucB with hX | hX
  · obtain ⟨-, hk, hi, -⟩ := yhData_spec he hGe hA
    rw [qdA_low hX, qcA_psi'' he hGe hX hA, vD_low (hk.trans hX), vD_low (hi.trans hX)]
  · unfold qdA; rw [if_pos ⟨hX, heB⟩, if_neg hA]

theorem vD_psi' {α η : Ordinal.{0}} (hα : 1 ≤ α) (hGe : gcG 0 < yhPsi α η) (hB : yhPsi α η < qdB)
    (x : Ordinal.{0}) : vD (yhPsi α η) x = glA (vD α x) (vD η x) x := by
  obtain ⟨h1, h2⟩ := yhData_eq hα hGe
  rw [vD_base' (yhPsi_E hα η) hGe.le hB, qdA_psi'' (yhPsi_E hα η) hGe hB (yhPsi_notAt hα), h1, h2]

/-- **The segment base keeps the gate of the code up to `ω`** on `[B_Γ, B₃)`. -/
theorem qd_FB_gate' {c : Ordinal.{0}} (hBc : tfBG ≤ c) (hcB : c < qdB) : qdGt (vaFB c) ≤ max ω (qdGt c) := by
  rcases lt_or_ge c ucB with hX | hX
  · rw [qdGt_low hX, qdGt_low ((vs_FB_le hBc).trans_lt hX)]; exact qc_FB_gate' hBc hX
  · exact qd_FB_gate c hX hcB

/-- **The base gate does not drop at the next `ε`-number** on `[B_Γ, B₃)`. -/
theorem qd_QE_eN' {e : Ordinal.{0}} (he : InE e) (hBe : tfBG ≤ e) (hB : e < qdB) :
    qdQEt e ≤ max ω (qdQEt (eN e)) := by
  rcases lt_or_ge e ucB with hX | hX
  · rw [qdQEt_low hX, qdQEt_low (qc_eN_lt_B hX)]; exact qc_QE_eN' he hBe hX
  · exact qd_QE_eN he hX hB

/-- **The gate of the next base** stays below every limit above the gate of the base. -/
theorem qd_QE_eN_lt {e Z : Ordinal.{0}} (he : InE e) (hBe : tfBG ≤ e) (hB : e < qdB) (hZ : IsSuccLimit Z)
    (hωZ : ω < Z) (hg : qdQEt e < Z) : qdQEt (eN e) < Z := by
  have hGe' : gcG 0 ≤ e := va_G_le_BG.trans hBe
  have hNB : eN e < qdB := qd_eN_lt_B3 hB
  rcases vs_eN_code he hBe with ⟨-, hN⟩ | ⟨hnA, hk, hN⟩
  · have hG : gcG 0 < yhPsi 1 e := hN ▸ va_G_lt_eN hGe'
    obtain ⟨d1, d2⟩ := yhData_eq le_rfl hG
    rw [hN, qdQEt_psi' (yhPsi_E le_rfl e) hG (hN ▸ hNB) (yhPsi_notAt le_rfl), d1, d2, qdQt_one]
    refine max_lt (lt_of_le_of_lt zero_le hωZ) ?_
    refine (qdQt_le e).trans_lt ?_
    rw [qdGt_base' he hGe' hB]; exact hg
  · have hG : gcG 0 < yhPsi 1 (yhI e + 1) := hN ▸ va_G_lt_eN hGe'
    have hGe : gcG 0 < e := lt_of_le_of_ne hGe' fun h => hnA (h ▸ yhAt_gcG 0)
    obtain ⟨d1, d2⟩ := yhData_eq le_rfl hG
    rw [hN, qdQEt_psi' (yhPsi_E le_rfl _) hG (hN ▸ hNB) (yhPsi_notAt le_rfl), d1, d2, qdQt_one]
    refine max_lt (lt_of_le_of_lt zero_le hωZ) ((qdQt_le _).trans_lt (qdGt_succ hZ _ ?_))
    rw [qdQEt_psi' he hGe hB hnA] at hg
    exact qdGt_of_Q hωZ ((le_max_right _ _).trans_lt hg)

/-- **Every `ε`-number `B_Γ ≤ e < B₂` carries a `QdGood`** (`Qc.qsGood_all`, through `S`). -/
theorem qdGood_low (S : InaccSeq.{0}) {e : Ordinal.{0}} (he : InE e) (hBe : tfBG ≤ e) (heB : e < ucB) : QdGood e :=
  qdGood_of_qs S heB (qsGood_all e he hBe heB)

section StepU

variable (M : QdDS) (hω : ω ≤ M.Eg) (hQ : qdQEt M.E ≤ M.Eg) (hGe : gcG 0 ≤ M.E)
  (hV : ∀ x, InE x → x < Om1 → M.Eg < x → M.V x = qdA M.E x)
  (hR : ∀ c, c < M.E → ∀ x, InE x → x < Om1 → M.G c < x → M.R c x = vD c x)
  (hG : ∀ c, c < M.E → c ≠ 0 → M.G c = max M.Eg (qdGt c))

include hω hQ hGe hG in
/-- **The gates of the step are `max Eg (qdGt c)`** (every base `E ∈ [G, B₃)`). -/
theorem qd_sG' : ∀ c, c < eN M.E → c ≠ 0 → M.sG c = max M.Eg (qdGt c) := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hcN hc0
  rcases lt_or_ge c M.E with hcE | hcE
  · rw [M.sG_lt hcE]; exact hG c hcE hc0
  obtain ⟨hk0, hd0, hdE, hrk, hdec⟩ := zm_dec M.E_E hcE
  obtain ⟨hko, hro⟩ := M.parts_lt hcE hcN
  set k := log M.E c
  set d := c / M.E ^ k
  set r := c % M.E ^ k
  have hv : M.E ^ k * d + r < eN M.E := hdec ▸ hcN
  have hsG := M.sG_eq hk0 hd0.ne' hdE hrk hv
  have hyG := qdGt_cnf' M.E_E hGe hk0.ne' hd0.ne' hdE hrk hv (hv.trans M.eN_lt_B3)
  rw [hdec] at hsG hyG
  rw [hsG, hyG, IH k hko (hko.trans hcN) hk0.ne', hG d hdE hd0.ne', qd_maxQ hω k, qd_maxQ hω d]
  rcases eq_or_ne r 0 with hr0 | hr0
  · rw [hr0, M.sG_zero, qdGt_zero]
    exact va_max3 hQ
  · rw [IH r hro (hro.trans hcN) hr0]
    exact va_max4 hQ

include hGe hV hR in
/-- **The step reads `vD`** (every base `E ∈ [G, B₃)`). -/
theorem qd_sR' : ∀ c, c < eN M.E → ∀ x, InE x → x < Om1 → M.Eg < x → M.sG c < x → M.sR c x = vD c x := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hcN x hx hx1 hgx hg
  rcases lt_or_ge c M.E with hcE | hcE
  · rw [M.sR_lt hcE]; rw [M.sG_lt hcE] at hg; exact hR c hcE x hx hx1 hg
  obtain ⟨hk0, hd0, hdE, hrk, hdec⟩ := zm_dec M.E_E hcE
  obtain ⟨hko, hro⟩ := M.parts_lt hcE hcN
  set k := log M.E c
  set d := c / M.E ^ k
  set r := c % M.E ^ k
  have hv : M.E ^ k * d + r < eN M.E := hdec ▸ hcN
  have hsG := M.sG_eq hk0 hd0.ne' hdE hrk hv
  rw [hdec] at hsG
  rw [hsG] at hg
  have hgk : M.sG k < x := (le_max_left _ _).trans_lt hg
  have hgd : M.G d < x := (le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hg)
  have hgr : M.sG r < x := (le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hg)
  have hsR := M.sR_eq hk0 hd0.ne' hdE hrk hv x
  have hvR := vD_cnf' M.E_E hGe hk0.ne' hd0.ne' hdE hrk hv (hv.trans M.eN_lt_B3) x
  rw [hdec] at hsR hvR
  rw [hsR, hvR, hV x hx hx1 hgx, IH k hko (hko.trans hcN) x hx hx1 hgx hgk, hR d hdE x hx hx1 hgd,
    IH r hro (hro.trans hcN) x hx hx1 hgx hgr]

end StepU

end Googology.Trans.PoR.InaccPsi.R2.Qd
