import Googology.Trans.PoR.InaccPsi.R2.VaStep

/-!
# VaLimS: THE READING AT A LIMIT `ε`-NUMBER BASE INSIDE A SEGMENT — ORDER, COFINALITY AND BOUNDS FROM THE MEMBERS

`E` is an `ε`-number past its segment base `F = vaFB E < E` (`Va.vaFB`), a limit of `ε`-numbers, and every
`ε`-number `e ∈ [F, E)` carries a system `Va.VsGood e` (base `F`).  As `Va.VaLim` with `B_Γ` replaced by `F`
(gates above the gate of `F`): a member at every code below `E`, the order and cofinality of the readings below
`E`, and at a non-atom `E = yhPsi α η`: `F(x) < vA E x`, every code below `E` reads below `vA E x`, cofinally.

* `vs_QE_eN_lt`, `vs_QF_le`, `vs_mem` (**a member**: the step of the system at the bracket of a code), `vs_memG`;
* `vs_T`, `vs_mono`, `vs_le_mono`, `vs_below`, `vs_xF`;
* `vs_dat`, `vs_datx`, `vs_D_lt` (**`F(x) < vA E x`**), `vs_lt_top`, `vs_ltT`, `vs_top`.

No new axiom, no new definition.
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
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Xk

/-- **The gate of the next base** stays below every limit above the gate of the base. -/
theorem vs_QE_eN_lt {e Z : Ordinal.{0}} (he : InE e) (hBe : tfBG ≤ e) (hZ : IsSuccLimit Z)
    (hωZ : ω < Z) (hg : yrQE e < Z) : yrQE (eN e) < Z := by
  have hGe' : gcG 0 ≤ e := va_G_le_BG.trans hBe
  rcases vs_eN_code he hBe with ⟨-, hN⟩ | ⟨hnA, hk, hN⟩
  · have hG : gcG 0 < yhPsi 1 e := hN ▸ va_G_lt_eN hGe'
    obtain ⟨d1, d2⟩ := yhData_eq le_rfl hG
    rw [hN, yrQE_psi (yhPsi_notAt le_rfl), d1, d2, yrQ_one]
    refine max_lt (lt_of_le_of_lt zero_le hωZ) ?_
    refine (yrQ_le e).trans_lt ?_
    rw [yrG_base he hGe']; exact hg
  · have hG : gcG 0 < yhPsi 1 (yhI e + 1) := hN ▸ va_G_lt_eN hGe'
    obtain ⟨d1, d2⟩ := yhData_eq le_rfl hG
    rw [hN, yrQE_psi (yhPsi_notAt le_rfl), d1, d2, yrQ_one]
    refine max_lt (lt_of_le_of_lt zero_le hωZ) ((yrQ_le _).trans_lt (yrG_succ hZ _ ?_))
    rw [yrQE_psi hnA] at hg
    exact yrG_of_Q hωZ ((le_max_right _ _).trans_lt hg)

/-- **The gate of the segment base** is at most the gate of the base. -/
theorem vs_QF_le {E : Ordinal.{0}} (hE : InE E) (hBE : tfBG ≤ E) : max ω (yrQE (vaFB E)) ≤ max ω (yrQE E) := by
  have hGE : gcG 0 ≤ E := va_G_le_BG.trans hBE
  have hGF : gcG 0 ≤ vaFB E := va_G_le_BG.trans (vs_FB_ge hBE)
  have h := vs_FB_gate E hBE
  rw [yrG_base (vs_FB_E hBE) hGF, yrG_base hE hGE] at h
  exact max_le (le_max_left _ _) h

/-- **A member**: the step of the system at the bracket of `c` (at `B_Γ` below `B_Γ`). -/
theorem vs_mem {E c : Ordinal.{0}} (hlim : ∀ e, InE e → e < E → eN e < E)
    (hIH : ∀ e, InE e → tfBG ≤ e → e < E → VsGood e) (hBE : tfBG < E) (hc : c < E) :
    ∃ e : Ordinal.{0}, ∃ M : ZmDS, InE e ∧ tfBG ≤ e ∧ (tfBG ≤ c → e = guE c) ∧ e ≤ max c tfBG ∧
      M.E = eN e ∧ c < M.E ∧ M.E < E ∧ ω ≤ M.Eg ∧ M.Eg = max ω (yrQE e) ∧ M.Eg ≤ max ω (yrG c) ∧
      (∀ x, InE x → x < Om1 → M.Eg < x → M.V x = eN (vA e x) ∧ M.V x = vA M.E x) ∧
      (∀ c', c' < M.E → ∀ x, InE x → x < Om1 → M.G c' < x → M.R c' x = vR c' x) ∧
      (∀ c', c' < M.E → c' ≠ 0 → M.G c' = max M.Eg (yrG c')) ∧ M.B = vaFB e ∧ M.Dv = vR (vaFB e) := by
  have hBE' : InE tfBG := Low.opow_eq_self_of_SC tfBG_SC
  have key : ∀ e, InE e → tfBG ≤ e → e < E → c < eN e → yrQE e ≤ yrG c →
      ∃ M : ZmDS, M.E = eN e ∧ c < M.E ∧ M.E < E ∧ ω ≤ M.Eg ∧ M.Eg = max ω (yrQE e) ∧
        M.Eg ≤ max ω (yrG c) ∧
        (∀ x, InE x → x < Om1 → M.Eg < x → M.V x = eN (vA e x) ∧ M.V x = vA M.E x) ∧
        (∀ c', c' < M.E → ∀ x, InE x → x < Om1 → M.G c' < x → M.R c' x = vR c' x) ∧
        (∀ c', c' < M.E → c' ≠ 0 → M.G c' = max M.Eg (yrG c')) ∧ M.B = vaFB e ∧ M.Dv = vR (vaFB e) := by
    intro e he hBe heE hce hQc
    obtain ⟨M₀, hE₀, hEg₀, hV₀, hR₀, hG₀, hB₀, hD₀⟩ := hIH e he hBe heE
    subst hE₀
    have hω : ω ≤ M₀.Eg := hEg₀ ▸ le_max_left _ _
    have hQ : yrQE M₀.E ≤ M₀.Eg := hEg₀ ▸ le_max_right _ _
    have hGe : gcG 0 ≤ M₀.E := va_G_le_BG.trans hBe
    refine ⟨M₀.step, rfl, hce, hlim _ he heE, hω, by rw [ZmDS.step_Eg, hEg₀],
      by rw [ZmDS.step_Eg, hEg₀]; exact max_le_max le_rfl hQc,
      fun x hx hx1 hgx => ?_, fun c' hc' x hx hx1 hgc => ?_, fun c' hc' hc0 => ?_, hB₀, hD₀⟩
    · have h1 : M₀.step.V x = eN (vA M₀.E x) := by show eN (M₀.V x) = _; rw [hV₀ x hx hx1 hgx]
      exact ⟨h1, h1.trans (vs_eN M₀ hω hQ hV₀ hR₀ hG₀ hx hx1 hgx)⟩
    · show M₀.sR c' x = vR c' x
      rcases eq_or_ne c' 0 with rfl | h0
      · rw [M₀.sR_zero, vR_zero]
      exact va_sR M₀ hGe hV₀ hR₀ c' hc' x hx hx1 ((M₀.sG_Eg c' h0).trans_lt hgc) hgc
    · exact va_sG M₀ hω hQ hGe hG₀ c' hc' hc0
  by_cases hcB : tfBG ≤ c
  · have hGc : gcG 0 ≤ c := va_G_le_BG.trans hcB
    have heB : tfBG ≤ guE c := gl_E_max hBE' tfBG_gt hcB
    have hec : guE c ≤ c := gl_E_le (yh_gfE_le hGc)
    have hQc : yrQE (guE c) ≤ yrG c := by
      rw [yrG_dec hGc]; exact (le_max_left _ _).trans (le_max_left _ _)
    obtain ⟨M, h1⟩ := key (guE c) (guE_E c) heB (hec.trans_lt hc) (gl_lt_eN (yh_gfE_le hGc)) hQc
    exact ⟨guE c, M, guE_E c, heB, fun _ => rfl, hec.trans (le_max_left _ _), h1⟩
  · have hcB' : c < tfBG := not_le.1 hcB
    obtain ⟨M, h1⟩ := key tfBG hBE' le_rfl hBE (hcB'.trans (lt_eN _)) (by rw [va_QE_BG]; exact zero_le)
    exact ⟨tfBG, M, hBE', le_rfl, fun h => absurd h hcB, le_max_right _ _, h1⟩

section Lim

variable {E : Ordinal.{0}} (hE : InE E) (hBE : tfBG < E)
  (hlim : ∀ e, InE e → e < E → eN e < E) (hIH : ∀ e, InE e → tfBG ≤ e → e < E → VsGood e)
  {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)

/-- The gate of a member at a code with its own gate below `x`. -/
theorem vs_memG {M : ZmDS} {c : Ordinal.{0}} (hωx : ω < x) (hEg : M.Eg ≤ max ω (yrG c)) (hg : yrG c < x)
    (hG : ∀ c', c' < M.E → c' ≠ 0 → M.G c' = max M.Eg (yrG c')) {c' : Ordinal.{0}} (hc' : c' < M.E)
    (hg' : yrG c' < x) : M.G c' < x := by
  rcases eq_or_ne c' 0 with rfl | h0
  · rw [M.G0]; exact (lt_of_le_of_lt zero_le hωx)
  · rw [hG c' hc' h0]; exact max_lt (hEg.trans_lt (max_lt hωx hg)) hg'

include hE hBE hlim hIH hx hx1

/-- **The readings of the codes below `E`** lie in `Tˣ ∩ gq(D(x)+1)`. -/
theorem vs_T {c : Ordinal.{0}} (hc : c < E) (hg : yrG c < x) :
    vR c x ∈ Tset x ∧ vR c x < Om1 ∧ vR c x < ywX x := by
  have hωx : ω < x := omega0_lt_inE hx
  obtain ⟨e, M, -, -, -, -, -, hcM, -, -, -, hEg, -, hR, hG, -, -⟩ := vs_mem hlim hIH hBE hc
  have hgM : M.Eg < x := hEg.trans_lt (max_lt hωx hg)
  have hGc := vs_memG hωx hEg hg hG hcM hg
  obtain ⟨hVT, -, -, hVX⟩ := M.V_T x hx hx1 hgM
  have hV1 : M.V x < Om1 := hVX.trans (ywX_facts hx hx1).2.2.1
  have hlt := M.lt c x hx hx1 hcM hGc
  rw [hR c hcM x hx hx1 hGc] at hlt
  exact ⟨vz_T_down hx hx1 hVT hV1 hlt.le, hlt.trans hV1, hlt.trans hVX⟩

theorem vs_mono {b c : Ordinal.{0}} (hbc : b < c) (hc : c < E) (hgb : yrG b < x) (hgc : yrG c < x) :
    vR b x < vR c x := by
  have hωx : ω < x := omega0_lt_inE hx
  obtain ⟨e, M, -, -, -, -, -, hcM, -, -, -, hEg, -, hR, hG, -, -⟩ := vs_mem hlim hIH hBE hc
  have hbM := hbc.trans hcM
  have hGc := vs_memG hωx hEg hgc hG hcM hgc
  have hGb := vs_memG hωx hEg hgc hG hbM hgb
  have h := M.mono b c x hx hx1 hbc hcM hGb hGc
  rwa [hR b hbM x hx hx1 hGb, hR c hcM x hx hx1 hGc] at h

theorem vs_le_mono {b c : Ordinal.{0}} (hbc : b ≤ c) (hc : c < E) (hgb : yrG b < x) (hgc : yrG c < x) :
    vR b x ≤ vR c x := by
  rcases hbc.lt_or_eq with h | rfl
  · exact (vs_mono hE hBE hlim hIH hx hx1 h hc hgb hgc).le
  · exact le_rfl

/-- **Below the reading of a nonzero code is the reading of a smaller code.** -/
theorem vs_below {c : Ordinal.{0}} (hc : c < E) (hc0 : c ≠ 0) (hg : yrG c < x) :
    ∀ ν, ν < vR c x → ∃ b, b < c ∧ yrG b < x ∧ ν ≤ vR b x := by
  have hωx : ω < x := omega0_lt_inE hx
  intro ν hν
  rcases zero_or_succ_or_isSuccLimit c with h0 | ⟨b, rfl⟩ | hl
  · exact absurd h0 hc0
  · rw [Order.succ_eq_add_one] at hν hg ⊢
    rw [vR_succ] at hν
    exact ⟨b, lt_add_one b, (yrG_le_succ b).trans_lt hg, Order.lt_add_one_iff.1 hν⟩
  · obtain ⟨e, M, -, -, -, -, -, hcM, -, -, -, hEg, -, hR, hG, -, -⟩ := vs_mem hlim hIH hBE hc
    have hGc := vs_memG hωx hEg hg hG hcM hg
    rw [← hR c hcM x hx hx1 hGc] at hν
    obtain ⟨b, hbc, hgb, hνb⟩ := M.cof c x hx hx1 hl hcM hGc ν hν
    have hbM := hbc.trans hcM
    have hyb : yrG b < x := by
      rcases eq_or_ne b 0 with rfl | h0
      · rw [yrG_zero]; exact hx.pos
      · rw [hG b hbM h0] at hgb; exact (le_max_right _ _).trans_lt hgb
    exact ⟨b, hbc, hyb, by rw [← hR b hbM x hx hx1 hgb]; exact hνb⟩

variable (hFE : vaFB E < E)
include hFE

/-- **The segment base reads above `x`**, in `Tˣ ∩ Ω₁`. -/
theorem vs_xF (hgx : max ω (yrQE E) < x) :
    vR (vaFB E) x ∈ Tset x ∧ InE (vR (vaFB E) x) ∧ x < vR (vaFB E) x ∧ vR (vaFB E) x < ywX x := by
  have hωx : ω < x := omega0_lt_inE hx
  have hgF : yrG (vaFB E) < x :=
    (vs_FB_gate E hBE.le).trans_lt (by rw [yrG_base hE (va_G_le_BG.trans hBE.le)]; exact hgx)
  have hFF : vaFB (vaFB E) = vaFB E := vs_FB_self (vs_FB_fix hBE.le) (vs_FB_gt hBE.le)
  have hgu : guE (vaFB E) = vaFB E := le_antisymm (gl_E_le (yh_gfE_le (va_G_le_BG.trans (vs_FB_ge hBE.le))))
    (gl_E_max (vs_FB_E hBE.le) (vs_FB_gt hBE.le) le_rfl)
  obtain ⟨e, M, -, -, he, -, -, -, -, -, -, hEg, -, -, -, -, hD⟩ := vs_mem hlim hIH hBE hFE
  have heF : e = vaFB E := (he (vs_FB_ge hBE.le)).trans hgu
  rw [heF, hFF] at hD
  have hgM : M.Eg < x := hEg.trans_lt (max_lt hωx hgF)
  have h := M.Dv_T x hx hx1 hgM
  rwa [hD] at h

omit hlim hIH hx hx1 in
/-- **The data of `E`.** -/
theorem vs_dat (hnA : ¬ YhAt E) :
    ¬ YhAt E ∧ gcG 0 < E ∧ 1 ≤ yhK E ∧ yhK E < E ∧ yhI E < E ∧ yhPsi (yhK E) (yhI E) = E := by
  have hGE : gcG 0 < E := va_G_le_BG.trans_lt hBE
  exact ⟨hnA, hGE, va_data hE hGE hnA⟩

/-- **The readings of the level and the index of `E`.** -/
theorem vs_datx (hnA : ¬ YhAt E) (hgx : max ω (yrQE E) < x) :
    yrG (yhK E) < x ∧ yrG (yhI E) < x ∧ 1 ≤ vR (yhK E) x ∧ vR (yhK E) x ∈ Tset x ∧ vR (yhK E) x < Om1 ∧
      vR (yhI E) x ∈ Tset x ∧ vR (yhI E) x < Om1 ∧ vA E x = glA (vR (yhK E) x) (vR (yhI E) x) x := by
  have hωx : ω < x := omega0_lt_inE hx
  obtain ⟨hnA, hGE, hk1, hkE, hiE, -⟩ := vs_dat hE hBE hFE hnA
  have hQ : yrQE E = max (yrQ (yhK E)) (yrQ (yhI E)) := yrQE_psi hnA
  have hQle : max (yrQ (yhK E)) (yrQ (yhI E)) < x := by rw [← hQ]; exact (le_max_right _ _).trans_lt hgx
  have hgk : yrG (yhK E) < x := yrG_of_Q hωx ((le_max_left _ _).trans_lt hQle)
  have hgi : yrG (yhI E) < x := yrG_of_Q hωx ((le_max_right _ _).trans_lt hQle)
  obtain ⟨hkT, hk1', -⟩ := vs_T hE hBE hlim hIH hx hx1 hkE hgk
  obtain ⟨hiT, hi1, -⟩ := vs_T hE hBE hlim hIH hx hx1 hiE hgi
  have hv1 : 1 ≤ vR (yhK E) x := by
    have h := vs_le_mono hE hBE hlim hIH hx hx1 hk1 hkE
      (by rw [show (1 : Ordinal.{0}) = ((1 : ℕ) : Ordinal.{0}) by norm_num, yrG_low (yh_nat_lt_G 1), glG_nat];
          exact (natCast_lt_omega0 1).trans hωx) hgk
    rwa [vR_one] at h
  exact ⟨hgk, hgi, hv1, hkT, hk1', hiT, hi1, vA_psi hnA x⟩

/-- **`F(x) < vA E x`** for the segment base `F`. -/
theorem vs_D_lt (hnA : ¬ YhAt E) (hgx : max ω (yrQE E) < x) : vR (vaFB E) x < vA E x := by
  obtain ⟨-, -, hk1, hkE, hiE, hpsi⟩ := vs_dat hE hBE hFE hnA
  obtain ⟨hgk, hgi, hv1, hkT, hk1', hiT, hi1, hA⟩ := vs_datx hE hBE hlim hIH hx hx1 hFE hnA hgx
  obtain ⟨-, -, -, -, hka, hta⟩ := glA_facts hx hx1 hv1 hkT hk1' hiT hi1
  have hgB : yrG (vaFB E) < x := by
    exact (vs_FB_gate E hBE.le).trans_lt (by rw [yrG_base hE (va_G_le_BG.trans hBE.le)]; exact hgx)
  rw [hA]
  by_cases hη : vaFB E ≤ yhI E
  · exact (vs_le_mono hE hBE hlim hIH hx hx1 hη hiE hgB hgi).trans_lt hta
  by_cases hα : vaFB E ≤ yhK E
  · exact (vs_le_mono hE hBE hlim hIH hx hx1 hα hkE hgB hgk).trans_lt hka
  exfalso
  have h := yhPsi_lt_SC (vs_FB_SC hBE.le) (vs_FB_gt hBE.le) (not_le.1 hα) (not_le.1 hη)
  rw [hpsi] at h
  exact absurd hFE (not_lt.2 h.le)

/-- **Every code below `E` reads below `vA E x`.** -/
theorem vs_lt_top (hnA : ¬ YhAt E) (hgx : max ω (yrQE E) < x) : ∀ c, c < E → yrG c < x → vR c x < vA E x := by
  have hωx : ω < x := omega0_lt_inE hx
  obtain ⟨-, -, hk1, hkE, hiE, hpsi⟩ := vs_dat hE hBE hFE hnA
  obtain ⟨hgk, hgi, hv1, hkT, hk1', hiT, hi1, hA⟩ := vs_datx hE hBE hlim hIH hx hx1 hFE hnA hgx
  obtain ⟨-, -, -, hVE, -, -⟩ := glA_facts hx hx1 hv1 hkT hk1' hiT hi1
  have hD := vs_D_lt hE hBE hlim hIH hx hx1 hFE hnA hgx
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hg
  have hgF : yrG (vaFB E) < x := by
    exact (vs_FB_gate E hBE.le).trans_lt (by rw [yrG_base hE (va_G_le_BG.trans hBE.le)]; exact hgx)
  by_cases hcB : c < vaFB E
  · exact (vs_mono hE hBE hlim hIH hx hx1 hcB hFE hg hgF).trans hD
  have hcB' : vaFB E ≤ c := not_lt.1 hcB
  have hGc : gcG 0 ≤ c := va_G_le_BG.trans ((vs_FB_ge hBE.le).trans hcB')
  have heB : vaFB E ≤ guE c := gl_E_max (vs_FB_E hBE.le) (vs_FB_gt hBE.le) hcB'
  have hec : guE c ≤ c := gl_E_le (yh_gfE_le hGc)
  have heE := guE_E c
  have hGe : gcG 0 ≤ guE c := va_G_le_BG.trans ((vs_FB_ge hBE.le).trans heB)
  have hge : yrG (guE c) < x := by
    rw [yrG_base heE hGe]
    rw [yrG_dec hGc] at hg
    exact (le_max_left _ _).trans_lt ((le_max_left _ _).trans_lt hg)
  rcases hec.lt_or_eq with hlt | heq
  · -- inside the bracket of a smaller base
    have h1 := IH _ hlt (hlt.trans hc) hge
    rw [vR_base heE hGe] at h1
    obtain ⟨e, M, -, -, he, -, hME, hcM, -, -, -, hEg, hV, hR, hG, -, -⟩ := vs_mem hlim hIH hBE hc
    rw [he ((vs_FB_ge hBE.le).trans hcB')] at hME hV
    have hgM : M.Eg < x := hEg.trans_lt (max_lt hωx hg)
    have hGcM := vs_memG hωx hEg hg hG hcM hg
    have hlt' := M.lt c x hx hx1 hcM hGcM
    rw [hR c hcM x hx hx1 hGcM, (hV x hx hx1 hgM).1] at hlt'
    exact hlt'.trans_le (eN_le h1 (by rw [hA]; exact hVE))
  · -- `c` is itself an `ε`-number base
    have hcE' : InE c := by rw [← heq]; exact heE
    rw [vR_base hcE' hGc]
    rcases vs_atom_cases ((vs_FB_ge hBE.le).trans hcB') with hB | ⟨hAc, -, -⟩ | hnA
    · have hcF : c = vaFB E := hB.trans (vs_FB_of_le hBE.le hcB' hc.le)
      rw [← vR_base hcE' hGc, hcF]; exact hD
    · -- an atom base `c < E = yhPsi α η`: `c ≤ α` or `c ≤ η`
      rw [← vR_base hcE' hGc]
      have hcle : c ≤ yhK E ∨ c ≤ yhI E := by
        by_contra hcon
        push Not at hcon
        have h := yhPsi_lt_SC hAc.1 hAc.2 hcon.1 hcon.2
        rw [hpsi] at h; exact absurd hc (not_lt.2 h.le)
      obtain ⟨-, -, -, -, hka, hta⟩ := glA_facts hx hx1 hv1 hkT hk1' hiT hi1
      rw [hA]
      rcases hcle with h | h
      · exact (vs_le_mono hE hBE hlim hIH hx hx1 h hkE hg hgk).trans_lt hka
      · exact (vs_le_mono hE hBE hlim hIH hx hx1 h hiE hg hgi).trans_lt hta
    have hGc' : gcG 0 < c := lt_of_le_of_ne hGc fun h => hnA (h ▸ yhAt_gcG 0)
    obtain ⟨hkc1, hkc, hic, hpsi'⟩ := va_data hcE' hGc' hnA
    have hQ := yrQE_psi hnA
    have hge' : max (yrQ (yhK c)) (yrQ (yhI c)) < x := by rw [← hQ, ← yrG_base hcE' hGc]; exact hg
    have hgk' : yrG (yhK c) < x := yrG_of_Q hωx ((le_max_left _ _).trans_lt hge')
    have hgi' : yrG (yhI c) < x := yrG_of_Q hωx ((le_max_right _ _).trans_lt hge')
    obtain ⟨hk'T, hk'1, -⟩ := vs_T hE hBE hlim hIH hx hx1 (hkc.trans hc) hgk'
    obtain ⟨hi'T, hi'1, -⟩ := vs_T hE hBE hlim hIH hx hx1 (hic.trans hc) hgi'
    have hv1' : 1 ≤ vR (yhK c) x := by
      have h := vs_le_mono hE hBE hlim hIH hx hx1 hkc1 (hkc.trans hc)
        (by rw [show (1 : Ordinal.{0}) = ((1 : ℕ) : Ordinal.{0}) by norm_num, yrG_low (yh_nat_lt_G 1),
          glG_nat]; exact (natCast_lt_omega0 1).trans hωx) hgk'
      rwa [vR_one] at h
    rw [vA_psi hnA, hA]
    have hcE2 : yhPsi (yhK c) (yhI c) < yhPsi (yhK E) (yhI E) := by rw [hpsi', hpsi]; exact hc
    rcases lt_trichotomy (yhK c) (yhK E) with hlt | heqk | hgt
    · have hη' : yhI c < yhPsi (yhK E) (yhI E) := (yhPsi_lt_lev hlt hk1).1 hcE2
      rw [hpsi] at hη'
      have hIHi := IH _ hic hη' hgi'
      rw [hA] at hIHi
      exact (glA_lev hx hx1 hv1' (vs_mono hE hBE hlim hIH hx hx1 hlt hkE hgk' hgk) hkT hk1' hiT hi1
        hi'T hi'1).2 hIHi
    · rw [heqk] at hcE2 ⊢
      have hη' : yhI c < yhI E := yhPsi_lt_iff.1 hcE2
      exact glA_lt_of hx hx1 hv1 hkT hk1' hi'T hiT hi1 (vs_mono hE hBE hlim hIH hx hx1 hη' hiE hgi' hgi)
    · have hle : yhPsi (yhK c) (yhI c) ≤ yhI E := (yhPsi_lt_lev' hgt hkc1).1 hcE2
      rw [hpsi'] at hle
      have h2 := vs_le_mono hE hBE hlim hIH hx hx1 hle hiE hg hgi
      rw [vR_base hcE' hGc, vA_psi hnA] at h2
      exact (glA_lev' hx hx1 hv1 (vs_mono hE hBE hlim hIH hx hx1 hgt (hkc.trans hc) hgk hgk') hk'T hk'1
        hiT hi1 hi'T hi'1).2 h2

omit hx hx1 in
/-- **The top bound as a function of the base** (for the union). -/
theorem vs_ltT (hnA : ¬ YhAt E) : ∀ y, InE y → y < Om1 → max ω (yrQE E) < y → ∀ c, c < E → yrG c < y →
    vR c y < vA E y := by
  intro y hy hy1 hgy
  exact vs_lt_top hE hBE hlim hIH hy hy1 hFE hnA hgy

/-- **The readings of the codes below `E` are cofinal in `vA E x`.** -/
theorem vs_top (hnA : ¬ YhAt E) (hgx : max ω (yrQE E) < x) :
    ∀ ν, ν < vA E x → ∃ b, b < E ∧ yrG b < x ∧ ν ≤ vR b x := by
  have hωx : ω < x := omega0_lt_inE hx
  have hxl : IsSuccLimit x := ev_isSuccLimit_of_inE hx
  have hEl : IsSuccLimit E := ev_isSuccLimit_of_inE hE
  obtain ⟨hnA, hGE, hk1, hkE, hiE, hpsi⟩ := vs_dat hE hBE hFE hnA
  obtain ⟨hgk, hgi, hv1, hkT, hk1', hiT, hi1, hA⟩ := vs_datx hE hBE hlim hIH hx hx1 hFE hnA hgx
  intro ν hν
  by_contra hcon
  push Not at hcon
  set S : Set Ordinal.{0} := {s | ∃ b, b < E ∧ yrG b < x ∧ s = vR b x} with hSdef
  have hSne : S.Nonempty := ⟨vR 0 x, 0, hE.pos, by rw [yrG_zero]; exact hx.pos, rfl⟩
  have hSbdd : BddAbove S := ⟨ν, fun s ⟨b, hb, hg, hs⟩ => hs ▸ (hcon b hb hg).le⟩
  set u := sSup S with hudef
  have hu1 : ∀ b, b < E → yrG b < x → vR b x < u := by
    intro b hb hg
    have hb1 : b + 1 < E := hEl.add_one_lt hb
    have hg1 : yrG (b + 1) < x := yrG_succ hxl b hg
    have h1 : vR (b + 1) x ≤ u := le_csSup hSbdd ⟨b + 1, hb1, hg1, rfl⟩
    rw [vR_succ] at h1
    exact (lt_add_one _).trans_le h1
  have hu2 : u ≤ ν := csSup_le hSne fun s ⟨b, hb, hg, hs⟩ => hs ▸ (hcon b hb hg).le
  have hu5 : ∀ y, y < u → ∃ b, b < E ∧ yrG b < x ∧ y < vR b x := by
    intro y hy
    obtain ⟨s, ⟨b, hb, hg, rfl⟩, hys⟩ := exists_lt_of_lt_csSup hSne hy
    exact ⟨b, hb, hg, hys⟩
  have hgB : yrG (vaFB E) < x := by
    exact (vs_FB_gate E hBE.le).trans_lt (by rw [yrG_base hE (va_G_le_BG.trans hBE.le)]; exact hgx)
  have hxu : x < u := by
    exact (vs_xF hE hBE hlim hIH hx hx1 hFE hgx).2.2.1.trans (hu1 (vaFB E) hFE hgB)
  -- codes above `G` suffice
  have hbig : ∀ y, y < u → ∃ b, b < E ∧ gcG 0 ≤ b ∧ yrG b < x ∧ y < vR b x := by
    intro y hy
    obtain ⟨b, hb, hg, hyb⟩ := hu5 y hy
    have hgG : yrG (gcG 0) < x := by rw [yrG_G0]; exact hx.pos
    refine ⟨max b (gcG 0), max_lt hb hGE, le_max_right _ _, ?_, ?_⟩
    · rcases le_total b (gcG 0) with h | h
      · rw [max_eq_right h]; exact hgG
      · rw [max_eq_left h]; exact hg
    · refine hyb.trans_le (vs_le_mono hE hBE hlim hIH hx hx1 (le_max_left _ _) (max_lt hb hGE) hg ?_)
      rcases le_total b (gcG 0) with h | h
      · rw [max_eq_right h]; exact hgG
      · rw [max_eq_left h]; exact hg
  have hul : IsSuccLimit u := by
    rw [isSuccLimit_iff_of_orderBot]
    refine ⟨by rw [Ordinal.bot_eq_zero]; exact (hx.pos.trans hxu).ne', isSuccPrelimit_of_succ_lt fun y hy => ?_⟩
    obtain ⟨b, hb, hg, hyb⟩ := hu5 y hy
    rw [Order.succ_eq_add_one]
    exact (Order.add_one_le_of_lt hyb).trans_lt (hu1 b hb hg)
  -- `u` is a value of `φ(α(x), ·)`
  have hPu : LuP (vR (yhK E) x) u := by
    refine (mem_range_veblen (zero_lt_one.trans_le hv1).ne').2 fun a' ha' => ?_
    refine le_antisymm (((isNormal_veblen a').le_iff_forall_le hul).2 fun y hy => ?_) (right_le_veblen _ _)
    obtain ⟨b, hb, hGb, hgb, hyb⟩ := hbig y hy
    obtain ⟨hbT, hb1, -⟩ := vs_T hE hBE hlim hIH hx hx1 hb hgb
    obtain ⟨α'', hα''k, hgα'', ha'α''⟩ := vs_below hE hBE hlim hIH hx hx1 hkE
      (zero_lt_one.trans_le hk1).ne' hgk a' ha'
    rcases eq_or_ne α'' 0 with h0 | h0
    · -- `a' = 0`: below the next base reading
      rw [h0, vR_zero] at ha'α''
      rw [le_antisymm ha'α'' zero_le, veblen_zero_apply]
      obtain ⟨e, M, he, heB, -, hemax, hME, hbM, hMlt, -, hEgeq, hEg, hV, hR, hG, -, -⟩ := vs_mem hlim hIH hBE hb
      have hgM : M.Eg < x := hEg.trans_lt (max_lt hωx hgb)
      have hGbM := vs_memG hωx hEg hgb hG hbM hgb
      have hlt := M.lt b x hx hx1 hbM hGbM
      rw [hR b hbM x hx hx1 hGbM, (hV x hx hx1 hgM).2] at hlt
      have hMEE : InE M.E := by rw [hME]; exact eN_E e
      have hBe : tfBG ≤ e := heB
      have hGME : gcG 0 ≤ M.E := (va_G_le_BG.trans hBe).trans (hME ▸ (lt_eN e).le)
      have hgME : yrG M.E < x := by
        rw [yrG_base hMEE hGME, hME]
        exact vs_QE_eN_lt he hBe hxl hωx ((le_max_right _ _).trans_lt (hEgeq ▸ hgM))
      have hVu := hu1 M.E hMlt hgME
      rw [vR_base hMEE hGME] at hVu
      have hVE : InE (vA M.E x) := by rw [← (hV x hx hx1 hgM).2]; exact (M.V_T x hx hx1 hgM).2.1
      exact (((opow_lt_opow_iff_right one_lt_omega0).2 (hyb.trans hlt)).trans_le (by rw [hVE]) |>.trans hVu).le
    · -- `a' ≤ α''(x)`, `1 ≤ α''`
      have hα''1 : 1 ≤ α'' := one_le_iff_ne_zero.2 h0
      have hα''E : α'' < E := hα''k.trans hkE
      obtain ⟨hα''T, hα''Ω, -⟩ := vs_T hE hBE hlim hIH hx hx1 hα''E hgα''
      have hv1'' : 1 ≤ vR α'' x := by
        have h := vs_le_mono hE hBE hlim hIH hx hx1 hα''1 hα''E
          (by rw [show (1 : Ordinal.{0}) = ((1 : ℕ) : Ordinal.{0}) by norm_num, yrG_low (yh_nat_lt_G 1),
            glG_nat]; exact (natCast_lt_omega0 1).trans hωx) hgα''
        rwa [vR_one] at h
      have hGp : gcG 0 < yhPsi α'' b := hGb.trans_lt (lt_yhPsi α'' b)
      have hPE : LuP (α'' + 1) E := by
        have := yhPsi_P (yhK E) (yhI E); rw [hpsi] at this
        exact luP_mono le_add_self (add_one_le_of_lt hα''k) this
      have hpE : yhPsi α'' b < E := yhPsi_lt_of hPE (tfBG_gt.trans hBE) hb
      have hgp : yrG (yhPsi α'' b) < x := by
        rw [yrG_psi hα''1 hGp]
        exact max_lt ((yrQ_le _).trans_lt hgα'') ((yrQ_le _).trans_lt hgb)
      have h1 : veblen a' y ≤ veblen (vR α'' x) y := veblen_left_monotone y ha'α''
      have h2 : veblen (vR α'' x) y < veblen (vR α'' x) (vR b x) := veblen_lt_veblen_iff_right.2 hyb
      have h3 : veblen (vR α'' x) (vR b x) ≤ glA (vR α'' x) (vR b x) x :=
        glA_veb_le hx hx1 hv1'' hα''T hα''Ω hbT hb1
      rw [← vR_psi hα''1 hGp] at h3
      exact (h1.trans_lt (h2.trans_le h3)).trans (hu1 _ hpE hgp) |>.le
  -- the earlier atoms of the level
  have hprev : ∀ σ, σ < vR (yhI E) x → glA (vR (yhK E) x) σ x < u := by
    intro σ hσ
    have hη0 : yhI E ≠ 0 := by
      rintro h0; rw [h0, vR_zero] at hσ; exact absurd hσ (not_lt.2 zero_le)
    obtain ⟨η'', hη'', hgη'', hση''⟩ := vs_below hE hBE hlim hIH hx hx1 hiE hη0 hgi σ hσ
    have hgG : yrG (gcG 0) < x := by rw [yrG_G0]; exact hx.pos
    -- a smaller index whose atom is above `G`
    have hG0B : gcG 0 < vaFB E := by
      have h : gcG 0 < tfBG := by rw [← zb_gcG_BG]; exact gcG_lt (Rj.rj_Om1_pos.trans tfBG_gt)
      exact h.trans_le (vs_FB_ge hBE.le)
    obtain ⟨η₃, hη₃, hgη₃, hση₃, hGη₃⟩ : ∃ η₃, η₃ < yhI E ∧ yrG η₃ < x ∧ σ ≤ vR η₃ x ∧
        gcG 0 < yhPsi (yhK E) η₃ := by
      by_cases hη : vaFB E ≤ yhI E
      · have hGη : gcG 0 < yhI E := hG0B.trans_le hη
        have hm : max η'' (gcG 0) < yhI E := max_lt hη'' hGη
        have hgm : yrG (max η'' (gcG 0)) < x := by
          rcases le_total η'' (gcG 0) with h | h
          · rw [max_eq_right h]; exact hgG
          · rw [max_eq_left h]; exact hgη''
        refine ⟨max η'' (gcG 0), hm, hgm, hση''.trans (vs_le_mono hE hBE hlim hIH hx hx1 (le_max_left _ _)
          (hm.trans hiE) hgη'' hgm), (le_max_right _ _).trans_lt (lt_yhPsi _ _)⟩
      · have hα : vaFB E ≤ yhK E := by
          by_contra hα
          have h := yhPsi_lt_SC (vs_FB_SC hBE.le) (vs_FB_gt hBE.le) (not_le.1 hα) (not_le.1 hη)
          rw [hpsi] at h
          exact absurd hFE (not_lt.2 h.le)
        exact ⟨η'', hη'', hgη'', hση'', (hG0B.trans_le hα).trans (yhPsi_gt hk1 η'').2⟩
    have hpE : yhPsi (yhK E) η₃ < E := by
      have := (yhPsi_lt_iff (α := yhK E)).2 hη₃; rwa [hpsi] at this
    have hgp : yrG (yhPsi (yhK E) η₃) < x := by
      rw [yrG_psi hk1 hGη₃]
      exact max_lt ((yrQ_le _).trans_lt hgk) ((yrQ_le _).trans_lt hgη₃)
    obtain ⟨hη₃T, hη₃1, -⟩ := vs_T hE hBE hlim hIH hx hx1 (hη₃.trans hiE) hgη₃
    have hσT : σ ∈ Tset x := vz_T_down hx hx1 hη₃T hη₃1 hση₃
    have h1 := (glA_le_iff hx hx1 hv1 hkT hk1' hσT (hση₃.trans_lt hη₃1) hη₃T hη₃1).2 hση₃
    rw [← vR_psi hk1 hGη₃] at h1
    exact h1.trans_lt (hu1 _ hpE hgp)
  have hmin := glA_min hx hx1 hv1 hkT hk1' hiT hi1 hPu hxu (hu1 _ hiE hgi) (hu1 _ hkE hgk) hprev
  rw [← hA] at hmin
  exact absurd (hmin.trans hu2) (not_le.2 hν)

end Lim

end Googology.Trans.PoR.InaccPsi.R2.Va
