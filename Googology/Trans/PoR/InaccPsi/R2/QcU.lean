import Googology.Trans.PoR.InaccPsi.R2.QcStp
import Googology.Trans.PoR.InaccPsi.R2.VaAll

/-!
# QcU: THE CLAUSES OF `vQ`, `qcA`, `qcG` ON ALL OF `[G, B₂)`, AND EVERY DIGIT SYSTEM BELOW `X` AS A `QsGood`

Below `X` the readings `vQ`, `qcA` and the gates `qcG`, `qcQE` are `Va.vR`, `Va.vA`, `Yr.yrG`, `Yr.yrQE`; from `X` on
they have the same Cantor clause.  One statement on `[G, B₂)` for each:

* `vQ_cnf'`, `vQ_base'`, `vQ_psi'`, `qcA_psi''`, `qc_FB_gate'`, `qc_QE_eN'`, `qc_QE_eN_lt`, `qc_sG'`, `qc_sR'`
  (**the step reads `vQ` with the gates `qcG`**);
* `qc_eN_low` (**`ε_{vA(e)(x)+1} = vA(ε_{e+1})(x)` below `X`**, from `Va.vsGood_all3`), `qsGood_low` (**every
  `ε`-number `B_Γ ≤ e < X` carries a `QsGood`**).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Yw
  Googology.Trans.PoR.InaccPsi.R2.Yh Googology.Trans.PoR.InaccPsi.R2.Va Googology.Trans.PoR.InaccPsi.R2.Tl
  Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Yr
  Googology.Trans.PoR.InaccPsi.R2.Zm Googology.Trans.PoR.InaccPsi.R2.Tf Googology.Trans.PoR.InaccPsi.R2.Gk
  Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gn Googology.Trans.PoR.InaccPsi.R2.Gg

theorem qc_eN_lt_X {e : Ordinal.{0}} (h : e < tlX) : eN e < tlX :=
  zm_eN_lt_fix h (tlX_SC.veblen_right (gg_one_lt_of_SC tlX_SC))

/-- **The Cantor clause of `vQ` on `[G, B₂)`.** -/
theorem vQ_cnf' {e j d r : Ordinal.{0}} (he : InE e) (hGe : gcG 0 ≤ e) (hj : j ≠ 0) (hd0 : d ≠ 0) (hde : d < e)
    (hr : r < e ^ j) (hv : e ^ j * d + r < eN e) (hvB : e ^ j * d + r < ucB) (x : Ordinal.{0}) :
    vQ (e ^ j * d + r) x = qcA e x ^ vQ j x * vQ d x + vQ r x := by
  rcases lt_or_ge e tlX with hX | hX
  · have hvX : e ^ j * d + r < tlX := hv.trans (qc_eN_lt_X hX)
    have hjX : j < tlX := (((right_le_opow j (lu_one_lt_E he)).trans
      (le_mul_of_one_le_right' (one_le_iff_ne_zero.2 hd0))).trans le_self_add).trans_lt hvX
    have hrX : r < tlX := (hr.trans_le (le_mul_of_one_le_right' (one_le_iff_ne_zero.2 hd0))).trans_le le_self_add
      |>.trans hvX
    rw [vQ_low hvX, vR_cnf he hGe hj hd0 hde hr hv, qcA_low hX, vQ_low hjX, vQ_low (hde.trans hX), vQ_low hrX]
  · exact vQ_cnf he hX hj hd0 hde hr hv hvB x

/-- **An `ε`-number code `e ∈ [G, B₂)` reads `qcA e`.** -/
theorem vQ_base' {e : Ordinal.{0}} (he : InE e) (hGe : gcG 0 ≤ e) (heB : e < ucB) (x : Ordinal.{0}) :
    vQ e x = qcA e x := by
  rcases lt_or_ge e tlX with hX | hX
  · rw [vQ_low hX, vR_base he hGe, qcA_low hX]
  · exact vQ_base he hX heB x

/-- **A non-atom `ε`-number code `e ∈ (G, B₂)` reads `ϑˣ(Ω₁·(yhK e)(x) + (yhI e)(x))`.** -/
theorem qcA_psi'' {e : Ordinal.{0}} (he : InE e) (hGe : gcG 0 < e) (heB : e < ucB) (hA : ¬ YhAt e)
    (x : Ordinal.{0}) : qcA e x = glA (vQ (yhK e) x) (vQ (yhI e) x) x := by
  rcases lt_or_ge e tlX with hX | hX
  · obtain ⟨-, hk, hi, -⟩ := yhData_spec he hGe hA
    rw [qcA_low hX, vA_psi hA, vQ_low (hk.trans hX), vQ_low (hi.trans hX)]
  · unfold qcA; rw [if_pos ⟨hX, heB⟩, if_neg hA]

theorem vQ_psi' {α η : Ordinal.{0}} (hα : 1 ≤ α) (hGe : gcG 0 < yhPsi α η) (hB : yhPsi α η < ucB)
    (x : Ordinal.{0}) : vQ (yhPsi α η) x = glA (vQ α x) (vQ η x) x := by
  obtain ⟨h1, h2⟩ := yhData_eq hα hGe
  rw [vQ_base' (yhPsi_E hα η) hGe.le hB, qcA_psi'' (yhPsi_E hα η) hGe hB (yhPsi_notAt hα), h1, h2]

/-- **The segment base keeps the gate of the code up to `ω`** on `[B_Γ, B₂)`. -/
theorem qc_FB_gate' {c : Ordinal.{0}} (hBc : tfBG ≤ c) (hcB : c < ucB) : qcG (vaFB c) ≤ max ω (qcG c) := by
  rcases lt_or_ge c tlX with hX | hX
  · rw [qcG_low hX, qcG_low ((vs_FB_le hBc).trans_lt hX)]; exact vs_FB_gate c hBc
  · exact qc_FB_gate c hX hcB

/-- **The base gate does not drop at the next `ε`-number** on `[B_Γ, B₂)`. -/
theorem qc_QE_eN' {e : Ordinal.{0}} (he : InE e) (hBe : tfBG ≤ e) (hB : e < ucB) :
    qcQE e ≤ max ω (qcQE (eN e)) := by
  rcases lt_or_ge e tlX with hX | hX
  · rw [qcQE_low hX, qcQE_low (qc_eN_lt_X hX)]; exact vs_QE_eN he hBe
  · exact qc_QE_eN he hX hB

/-- **The gate of the next base** stays below every limit above the gate of the base. -/
theorem qc_QE_eN_lt {e Z : Ordinal.{0}} (he : InE e) (hBe : tfBG ≤ e) (hB : e < ucB) (hZ : IsSuccLimit Z)
    (hωZ : ω < Z) (hg : qcQE e < Z) : qcQE (eN e) < Z := by
  have hGe' : gcG 0 ≤ e := va_G_le_BG.trans hBe
  have hNB : eN e < ucB := qc_eN_lt_B hB
  rcases vs_eN_code he hBe with ⟨-, hN⟩ | ⟨hnA, hk, hN⟩
  · have hG : gcG 0 < yhPsi 1 e := hN ▸ va_G_lt_eN hGe'
    obtain ⟨d1, d2⟩ := yhData_eq le_rfl hG
    rw [hN, qcQE_psi' (yhPsi_E le_rfl e) hG (hN ▸ hNB) (yhPsi_notAt le_rfl), d1, d2, qcQ_one]
    refine max_lt (lt_of_le_of_lt zero_le hωZ) ?_
    refine (qcQ_le e).trans_lt ?_
    rw [qcG_base' he hGe' hB]; exact hg
  · have hG : gcG 0 < yhPsi 1 (yhI e + 1) := hN ▸ va_G_lt_eN hGe'
    have hGe : gcG 0 < e := lt_of_le_of_ne hGe' fun h => hnA (h ▸ yhAt_gcG 0)
    obtain ⟨d1, d2⟩ := yhData_eq le_rfl hG
    rw [hN, qcQE_psi' (yhPsi_E le_rfl _) hG (hN ▸ hNB) (yhPsi_notAt le_rfl), d1, d2, qcQ_one]
    refine max_lt (lt_of_le_of_lt zero_le hωZ) ((qcQ_le _).trans_lt (qcG_succ hZ _ ?_))
    rw [qcQE_psi' he hGe hB hnA] at hg
    exact qcG_of_Q hωZ ((le_max_right _ _).trans_lt hg)

/-- **`ε_{vA(e)(x)+1} = vA(ε_{e+1})(x)` below `X`** (the system `Va.vsGood_all3` at `e`). -/
theorem qc_eN_low {e : Ordinal.{0}} (he : InE e) (hBe : tfBG ≤ e) (heX : e < tlX) {x : Ordinal.{0}} (hx : InE x)
    (hx1 : x < Om1) (hgx : max ω (qcQE e) < x) : eN (qcA e x) = qcA (eN e) x := by
  obtain ⟨M, hME, hEg, hV, hR, hG, -, -⟩ := vsGood_all3 e he hBe heX
  subst hME
  rw [qcQE_low heX] at hgx
  have hω : ω ≤ M.Eg := hEg ▸ le_max_left _ _
  have hQ : yrQE M.E ≤ M.Eg := hEg ▸ le_max_right _ _
  rw [qcA_low heX, qcA_low (qc_eN_lt_X heX)]
  exact vs_eN M hω hQ hV hR hG hx hx1 (hEg ▸ hgx)

/-- **Every `ε`-number `B_Γ ≤ e < X` carries a `QsGood`.** -/
theorem qsGood_low {e : Ordinal.{0}} (he : InE e) (hBe : tfBG ≤ e) (heX : e < tlX) : QsGood e :=
  qsGood_of_vs hBe heX (vsGood_all3 e he hBe heX)

section StepU

variable (M : QDS) (hω : ω ≤ M.Eg) (hQ : qcQE M.E ≤ M.Eg) (hGe : gcG 0 ≤ M.E)
  (hV : ∀ x, InE x → x < Om1 → M.Eg < x → M.V x = qcA M.E x)
  (hR : ∀ c, c < M.E → ∀ x, InE x → x < Om1 → M.G c < x → M.R c x = vQ c x)
  (hG : ∀ c, c < M.E → c ≠ 0 → M.G c = max M.Eg (qcG c))

include hω hQ hGe hG in
/-- **The gates of the step are `max Eg (qcG c)`** (every base `E ∈ [G, B₂)`). -/
theorem qc_sG' : ∀ c, c < eN M.E → c ≠ 0 → M.sG c = max M.Eg (qcG c) := by
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
  have hyG := qcG_cnf' M.E_E hGe hk0.ne' hd0.ne' hdE hrk hv (hv.trans M.eN_lt_B)
  rw [hdec] at hsG hyG
  rw [hsG, hyG, IH k hko (hko.trans hcN) hk0.ne', hG d hdE hd0.ne', qc_maxQ hω k, qc_maxQ hω d]
  rcases eq_or_ne r 0 with hr0 | hr0
  · rw [hr0, M.sG_zero, qcG_zero]
    exact va_max3 hQ
  · rw [IH r hro (hro.trans hcN) hr0]
    exact va_max4 hQ

include hGe hV hR in
/-- **The step reads `vQ`** (every base `E ∈ [G, B₂)`). -/
theorem qc_sR' : ∀ c, c < eN M.E → ∀ x, InE x → x < Om1 → M.Eg < x → M.sG c < x → M.sR c x = vQ c x := by
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
  have hvR := vQ_cnf' M.E_E hGe hk0.ne' hd0.ne' hdE hrk hv (hv.trans M.eN_lt_B) x
  rw [hdec] at hsR hvR
  rw [hsR, hvR, hV x hx hx1 hgx, IH k hko (hko.trans hcN) x hx hx1 hgx hgk, hR d hdE x hx hx1 hgd,
    IH r hro (hro.trans hcN) x hx hx1 hgx hgr]

end StepU

end Googology.Trans.PoR.InaccPsi.R2.Qc
