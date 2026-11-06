import Googology.Trans.PoR.InaccPsi.R2.VaCg

/-!
# VaLim: THE READING AT A LIMIT `ε`-NUMBER BASE — ORDER, COFINALITY AND BOUNDS FROM THE MEMBERS

`E` is an `ε`-number with `B_Γ < E < Γ_{B_Γ+1}`, a limit of `ε`-numbers (`ε_{e+1} < E` for `e < E`), and every
`ε`-number `e ∈ [B_Γ, E)` carries a system `VaGood e`.  Then `E = yhPsi α η` (not an atom) reads
`vA E x = ϑˣ(Ω₁·α(x) + η(x))`, and above the gate `max ω (yrQE E)`:

* `va_mem` (**a member**: the step of the system at the bracket of a code `c < E`, base gate `≤ max ω (yrG c)`),
  `va_QE_BG`, `va_QE_eN_lt`;
* `va_T`, `va_mono`, `va_le_mono`, `va_below` (the readings of the codes below `E`: in `Tˣ ∩ gq(D(x)+1)`, ordered,
  every reading below a nonzero code's reading is below the reading of a smaller code);
* `va_dat`, `va_datx`, `va_D_lt` (**`D(x) < vA E x`**), `va_lt_top` (**every code below `E` reads below `vA E x`**),
  `va_top` (**the readings of the codes below `E` are cofinal in `vA E x`**: `Gl.glA_min` at their supremum, which is
  a value of `φ(α(x), ·)` by `mem_range_veblen`), `va_V_lt_gq` (**`vA E x < gq(D(x)+1) x`**).

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
theorem va_QE_eN_lt {e Z : Ordinal.{0}} (he : InE e) (hBe : tfBG ≤ e) (heU : e < vaB2) (hZ : IsSuccLimit Z)
    (hωZ : ω < Z) (hg : yrQE e < Z) : yrQE (eN e) < Z := by
  have hGe' : gcG 0 ≤ e := va_G_le_BG.trans hBe
  rcases va_eN_code he hBe heU with ⟨-, hN⟩ | ⟨hnA, hk, hN⟩
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

/-- **A member**: the step of the system at the bracket of `c`. -/
theorem va_mem {E c : Ordinal.{0}} (hEU : E < vaU) (hlim : ∀ e, InE e → e < E → eN e < E)
    (hIH : ∀ e, InE e → tfBG ≤ e → e < E → VaGood e) (hBE : tfBG < E) (hc : c < E) :
    ∃ e : Ordinal.{0}, ∃ M : ZmDS, InE e ∧ tfBG ≤ e ∧ (tfBG ≤ c → e = guE c) ∧ e ≤ max c tfBG ∧
      M.E = eN e ∧ c < M.E ∧ M.E < E ∧ ω ≤ M.Eg ∧ M.Eg = max ω (yrQE e) ∧ M.Eg ≤ max ω (yrG c) ∧
      (∀ x, InE x → x < Om1 → M.Eg < x → M.V x = eN (vA e x) ∧ M.V x = vA M.E x) ∧
      (∀ c', c' < M.E → ∀ x, InE x → x < Om1 → M.G c' < x → M.R c' x = vR c' x) ∧
      (∀ c', c' < M.E → c' ≠ 0 → M.G c' = max M.Eg (yrG c')) ∧ M.Dv = ywV 1 0 := by
  have hBE' : InE tfBG := Low.opow_eq_self_of_SC tfBG_SC
  have key : ∀ e, InE e → tfBG ≤ e → e < E → c < eN e → yrQE e ≤ yrG c →
      ∃ M : ZmDS, M.E = eN e ∧ c < M.E ∧ M.E < E ∧ ω ≤ M.Eg ∧ M.Eg = max ω (yrQE e) ∧
        M.Eg ≤ max ω (yrG c) ∧
        (∀ x, InE x → x < Om1 → M.Eg < x → M.V x = eN (vA e x) ∧ M.V x = vA M.E x) ∧
        (∀ c', c' < M.E → ∀ x, InE x → x < Om1 → M.G c' < x → M.R c' x = vR c' x) ∧
        (∀ c', c' < M.E → c' ≠ 0 → M.G c' = max M.Eg (yrG c')) ∧ M.Dv = ywV 1 0 := by
    intro e he hBe heE hce hQc
    obtain ⟨M₀, hE₀, hEg₀, hV₀, hR₀, hG₀, -, hD₀⟩ := hIH e he hBe heE
    subst hE₀
    have hω : ω ≤ M₀.Eg := hEg₀ ▸ le_max_left _ _
    have hQ : yrQE M₀.E ≤ M₀.Eg := hEg₀ ▸ le_max_right _ _
    have hGe : gcG 0 ≤ M₀.E := va_G_le_BG.trans hBe
    refine ⟨M₀.step, rfl, hce, hlim _ he heE, hω, by rw [ZmDS.step_Eg, hEg₀],
      by rw [ZmDS.step_Eg, hEg₀]; exact max_le_max le_rfl hQc,
      fun x hx hx1 hgx => ?_, fun c' hc' x hx hx1 hgc => ?_, fun c' hc' hc0 => ?_, hD₀⟩
    · have h1 : M₀.step.V x = eN (vA M₀.E x) := by show eN (M₀.V x) = _; rw [hV₀ x hx hx1 hgx]
      exact ⟨h1, h1.trans (va_eN M₀ hω hQ hBe ((heE.trans hEU).trans_le va_U_le_B2) hR₀ hG₀ hx hx1 hgx)⟩
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

/-- **Every code below `Γ_{B_Γ+1}` reads below `gq(D(x)+1)`.** -/
theorem va_lt_gq {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    ∀ c, c < vaU → yrG c < x → vR c x < gq (ywV 1 0 x + 1) x := by
  obtain ⟨hDq, -, -, hqfix, -⟩ := zm_gq_facts hx hx1
  have hQE : InE (gq (ywV 1 0 x + 1) x) := zm_fix_E hqfix
  obtain ⟨hDT, -, hD1, -⟩ := zmD_facts hx hx1
  obtain ⟨hD1T, hD11⟩ := gl_T_succ hx hx1 hDT hD1
  have hωx : ω < x := omega0_lt_inE hx
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hg
  by_cases hcB : c < tfBG
  · rw [vR_yr c hcB x]; exact (zmYr.lt c x hx hx1 hcB hg).trans hDq
  have hcB' : tfBG ≤ c := not_lt.1 hcB
  have hGc : gcG 0 ≤ c := va_G_le_BG.trans hcB'
  obtain ⟨-, -, -, -, -, hlog, hmod, hdiv⟩ := gl_parts (yh_gfE_le hGc)
  rw [yrG_dec hGc] at hg
  have hgQE : yrQE (guE c) < x := (le_max_left _ _).trans_lt ((le_max_left _ _).trans_lt hg)
  have hgk : yrG (log (guE c) c) < x :=
    yrG_of_Q hωx ((le_max_right _ _).trans_lt ((le_max_left _ _).trans_lt hg))
  have hgd : yrG (c / guE c ^ log (guE c) c) < x :=
    yrG_of_Q hωx ((le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hg))
  have hgr : yrG (c % guE c ^ log (guE c) c) < x := (le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hg)
  have heB : tfBG ≤ guE c := gl_E_max (Low.opow_eq_self_of_SC tfBG_SC) tfBG_gt hcB'
  have hec : guE c ≤ c := gl_E_le (yh_gfE_le hGc)
  have hA : vA (guE c) x < gq (ywV 1 0 x + 1) x := by
    rcases va_atom_cases heB (hec.trans_lt hc) with hB | hnA
    · rw [hB, vA_BG]; exact hDq
    have hK := yh_lev_lt hGc hnA
    have hI := yh_idx_lt hGc hnA
    rw [yrQE_psi hnA] at hgQE
    rw [vA_psi hnA]
    exact xkA_lt hx hx1 hD1T hD11 (IH _ hK (hK.trans hc) (yrG_of_Q hωx ((le_max_left _ _).trans_lt hgQE)))
      (IH _ hI (hI.trans hc) (yrG_of_Q hωx ((le_max_right _ _).trans_lt hgQE)))
  rw [vR_dec hGc]
  exact (inE_indec hQE).add_lt (InE.mul_lt hQE (zm_opow_lt hQE hA (IH _ hlog (hlog.trans hc) hgk))
    (IH _ hdiv (hdiv.trans hc) hgd)) (IH _ hmod (hmod.trans hc) hgr)

section Lim

variable {E : Ordinal.{0}} (hE : InE E) (hBE : tfBG < E) (hEU : E < vaU)
  (hlim : ∀ e, InE e → e < E → eN e < E) (hIH : ∀ e, InE e → tfBG ≤ e → e < E → VaGood e)
  {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)

/-- The gate of a member at a code with its own gate below `x`. -/
theorem va_memG {M : ZmDS} {c : Ordinal.{0}} (hωx : ω < x) (hEg : M.Eg ≤ max ω (yrG c)) (hg : yrG c < x)
    (hG : ∀ c', c' < M.E → c' ≠ 0 → M.G c' = max M.Eg (yrG c')) {c' : Ordinal.{0}} (hc' : c' < M.E)
    (hg' : yrG c' < x) : M.G c' < x := by
  rcases eq_or_ne c' 0 with rfl | h0
  · rw [M.G0]; exact (lt_of_le_of_lt zero_le hωx)
  · rw [hG c' hc' h0]; exact max_lt (hEg.trans_lt (max_lt hωx hg)) hg'

include hE hBE hEU hlim hIH hx hx1

/-- **The readings of the codes below `E`** lie in `Tˣ ∩ gq(D(x)+1)`. -/
theorem va_T {c : Ordinal.{0}} (hc : c < E) (hg : yrG c < x) :
    vR c x ∈ Tset x ∧ vR c x < Om1 ∧ vR c x < gq (ywV 1 0 x + 1) x := by
  have hωx : ω < x := omega0_lt_inE hx
  obtain ⟨e, M, -, -, -, -, -, hcM, -, -, -, hEg, -, hR, hG, -⟩ := va_mem hEU hlim hIH hBE hc
  have hgM : M.Eg < x := hEg.trans_lt (max_lt hωx hg)
  have hGc := va_memG hωx hEg hg hG hcM hg
  obtain ⟨hVT, -, -, hVX⟩ := M.V_T x hx hx1 hgM
  have hV1 : M.V x < Om1 := hVX.trans (ywX_facts hx hx1).2.2.1
  have hlt := M.lt c x hx hx1 hcM hGc
  rw [hR c hcM x hx hx1 hGc] at hlt
  exact ⟨vz_T_down hx hx1 hVT hV1 hlt.le, hlt.trans hV1, va_lt_gq hx hx1 c (hc.trans hEU) hg⟩

theorem va_mono {b c : Ordinal.{0}} (hbc : b < c) (hc : c < E) (hgb : yrG b < x) (hgc : yrG c < x) :
    vR b x < vR c x := by
  have hωx : ω < x := omega0_lt_inE hx
  obtain ⟨e, M, -, -, -, -, -, hcM, -, -, -, hEg, -, hR, hG, -⟩ := va_mem hEU hlim hIH hBE hc
  have hbM := hbc.trans hcM
  have hGc := va_memG hωx hEg hgc hG hcM hgc
  have hGb := va_memG hωx hEg hgc hG hbM hgb
  have h := M.mono b c x hx hx1 hbc hcM hGb hGc
  rwa [hR b hbM x hx hx1 hGb, hR c hcM x hx hx1 hGc] at h

theorem va_le_mono {b c : Ordinal.{0}} (hbc : b ≤ c) (hc : c < E) (hgb : yrG b < x) (hgc : yrG c < x) :
    vR b x ≤ vR c x := by
  rcases hbc.lt_or_eq with h | rfl
  · exact (va_mono hE hBE hEU hlim hIH hx hx1 h hc hgb hgc).le
  · exact le_rfl

/-- **Below the reading of a nonzero code is the reading of a smaller code.** -/
theorem va_below {c : Ordinal.{0}} (hc : c < E) (hc0 : c ≠ 0) (hg : yrG c < x) :
    ∀ ν, ν < vR c x → ∃ b, b < c ∧ yrG b < x ∧ ν ≤ vR b x := by
  have hωx : ω < x := omega0_lt_inE hx
  intro ν hν
  rcases zero_or_succ_or_isSuccLimit c with h0 | ⟨b, rfl⟩ | hl
  · exact absurd h0 hc0
  · rw [Order.succ_eq_add_one] at hν hg ⊢
    rw [vR_succ] at hν
    exact ⟨b, lt_add_one b, (yrG_le_succ b).trans_lt hg, Order.lt_add_one_iff.1 hν⟩
  · obtain ⟨e, M, -, -, -, -, -, hcM, -, -, -, hEg, -, hR, hG, -⟩ := va_mem hEU hlim hIH hBE hc
    have hGc := va_memG hωx hEg hg hG hcM hg
    rw [← hR c hcM x hx hx1 hGc] at hν
    obtain ⟨b, hbc, hgb, hνb⟩ := M.cof c x hx hx1 hl hcM hGc ν hν
    have hbM := hbc.trans hcM
    have hyb : yrG b < x := by
      rcases eq_or_ne b 0 with rfl | h0
      · rw [yrG_zero]; exact hx.pos
      · rw [hG b hbM h0] at hgb; exact (le_max_right _ _).trans_lt hgb
    exact ⟨b, hbc, hyb, by rw [← hR b hbM x hx hx1 hgb]; exact hνb⟩

omit hlim hIH hx hx1 in
/-- **The data of `E`.** -/
theorem va_dat : ¬ YhAt E ∧ gcG 0 < E ∧ 1 ≤ yhK E ∧ yhK E < E ∧ yhI E < E ∧ yhPsi (yhK E) (yhI E) = E := by
  have hnA : ¬ YhAt E := by
    rcases va_atom_cases hBE.le hEU with h | h
    · exact absurd h hBE.ne'
    · exact h
  have hGE : gcG 0 < E := va_G_le_BG.trans_lt hBE
  exact ⟨hnA, hGE, va_data hE hGE hnA⟩

/-- **The readings of the level and the index of `E`.** -/
theorem va_datx (hgx : max ω (yrQE E) < x) :
    yrG (yhK E) < x ∧ yrG (yhI E) < x ∧ 1 ≤ vR (yhK E) x ∧ vR (yhK E) x ∈ Tset x ∧ vR (yhK E) x < Om1 ∧
      vR (yhI E) x ∈ Tset x ∧ vR (yhI E) x < Om1 ∧ vA E x = glA (vR (yhK E) x) (vR (yhI E) x) x := by
  have hωx : ω < x := omega0_lt_inE hx
  obtain ⟨hnA, hGE, hk1, hkE, hiE, -⟩ := va_dat hE hBE hEU
  have hQ : yrQE E = max (yrQ (yhK E)) (yrQ (yhI E)) := yrQE_psi hnA
  have hQle : max (yrQ (yhK E)) (yrQ (yhI E)) < x := by rw [← hQ]; exact (le_max_right _ _).trans_lt hgx
  have hgk : yrG (yhK E) < x := yrG_of_Q hωx ((le_max_left _ _).trans_lt hQle)
  have hgi : yrG (yhI E) < x := yrG_of_Q hωx ((le_max_right _ _).trans_lt hQle)
  obtain ⟨hkT, hk1', -⟩ := va_T hE hBE hEU hlim hIH hx hx1 hkE hgk
  obtain ⟨hiT, hi1, -⟩ := va_T hE hBE hEU hlim hIH hx hx1 hiE hgi
  have hv1 : 1 ≤ vR (yhK E) x := by
    have h := va_le_mono hE hBE hEU hlim hIH hx hx1 hk1 hkE
      (by rw [show (1 : Ordinal.{0}) = ((1 : ℕ) : Ordinal.{0}) by norm_num, yrG_low (yh_nat_lt_G 1), glG_nat];
          exact (natCast_lt_omega0 1).trans hωx) hgk
    rwa [vR_one] at h
  exact ⟨hgk, hgi, hv1, hkT, hk1', hiT, hi1, vA_psi hnA x⟩

/-- **`D(x) < vA E x`.** -/
theorem va_D_lt (hgx : max ω (yrQE E) < x) : ywV 1 0 x < vA E x := by
  obtain ⟨-, -, hk1, hkE, hiE, hpsi⟩ := va_dat hE hBE hEU
  obtain ⟨hgk, hgi, hv1, hkT, hk1', hiT, hi1, hA⟩ := va_datx hE hBE hEU hlim hIH hx hx1 hgx
  obtain ⟨-, -, -, -, hka, hta⟩ := glA_facts hx hx1 hv1 hkT hk1' hiT hi1
  have hgB : yrG tfBG < x := by
    rw [yrG_base (Low.opow_eq_self_of_SC tfBG_SC) va_G_le_BG, va_QE_BG]; exact hx.pos
  rw [hA, ← vR_BG x]
  by_cases hη : tfBG ≤ yhI E
  · exact (va_le_mono hE hBE hEU hlim hIH hx hx1 hη hiE hgB hgi).trans_lt hta
  by_cases hα : tfBG ≤ yhK E
  · exact (va_le_mono hE hBE hEU hlim hIH hx hx1 hα hkE hgB hgk).trans_lt hka
  exfalso
  have h := yhPsi_lt_SC tfBG_SC tfBG_gt (not_le.1 hα) (not_le.1 hη)
  rw [hpsi] at h
  exact absurd hBE (not_lt.2 h.le)

/-- **Every code below `E` reads below `vA E x`.** -/
theorem va_lt_top (hgx : max ω (yrQE E) < x) : ∀ c, c < E → yrG c < x → vR c x < vA E x := by
  have hωx : ω < x := omega0_lt_inE hx
  obtain ⟨-, -, hk1, hkE, hiE, hpsi⟩ := va_dat hE hBE hEU
  obtain ⟨hgk, hgi, hv1, hkT, hk1', hiT, hi1, hA⟩ := va_datx hE hBE hEU hlim hIH hx hx1 hgx
  obtain ⟨-, -, -, hVE, -, -⟩ := glA_facts hx hx1 hv1 hkT hk1' hiT hi1
  have hD := va_D_lt hE hBE hEU hlim hIH hx hx1 hgx
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hg
  by_cases hcB : c < tfBG
  · rw [vR_yr c hcB x]
    exact (zmYr.lt c x hx hx1 hcB hg).trans hD
  have hcB' : tfBG ≤ c := not_lt.1 hcB
  have hGc : gcG 0 ≤ c := va_G_le_BG.trans hcB'
  have heB : tfBG ≤ guE c := gl_E_max (Low.opow_eq_self_of_SC tfBG_SC) tfBG_gt hcB'
  have hec : guE c ≤ c := gl_E_le (yh_gfE_le hGc)
  have heE := guE_E c
  have hGe : gcG 0 ≤ guE c := va_G_le_BG.trans heB
  have hge : yrG (guE c) < x := by
    rw [yrG_base heE hGe]
    rw [yrG_dec hGc] at hg
    exact (le_max_left _ _).trans_lt ((le_max_left _ _).trans_lt hg)
  rcases hec.lt_or_eq with hlt | heq
  · -- inside the bracket of a smaller base
    have h1 := IH _ hlt (hlt.trans hc) hge
    rw [vR_base heE hGe] at h1
    obtain ⟨e, M, -, -, he, -, hME, hcM, -, -, -, hEg, hV, hR, hG, -⟩ := va_mem hEU hlim hIH hBE hc
    rw [he hcB'] at hME hV
    have hgM : M.Eg < x := hEg.trans_lt (max_lt hωx hg)
    have hGcM := va_memG hωx hEg hg hG hcM hg
    have hlt' := M.lt c x hx hx1 hcM hGcM
    rw [hR c hcM x hx hx1 hGcM, (hV x hx hx1 hgM).1] at hlt'
    exact hlt'.trans_le (eN_le h1 (by rw [hA]; exact hVE))
  · -- `c` is itself an `ε`-number base
    have hcE' : InE c := by rw [← heq]; exact heE
    rw [vR_base hcE' hGc]
    rcases va_atom_cases hcB' (hc.trans hEU) with hB | hnA
    · rw [hB, vA_BG]; exact hD
    have hGc' : gcG 0 < c := lt_of_le_of_ne hGc fun h => hnA (h ▸ yhAt_gcG 0)
    obtain ⟨hkc1, hkc, hic, hpsi'⟩ := va_data hcE' hGc' hnA
    have hQ := yrQE_psi hnA
    have hge' : max (yrQ (yhK c)) (yrQ (yhI c)) < x := by rw [← hQ, ← yrG_base hcE' hGc]; exact hg
    have hgk' : yrG (yhK c) < x := yrG_of_Q hωx ((le_max_left _ _).trans_lt hge')
    have hgi' : yrG (yhI c) < x := yrG_of_Q hωx ((le_max_right _ _).trans_lt hge')
    obtain ⟨hk'T, hk'1, -⟩ := va_T hE hBE hEU hlim hIH hx hx1 (hkc.trans hc) hgk'
    obtain ⟨hi'T, hi'1, -⟩ := va_T hE hBE hEU hlim hIH hx hx1 (hic.trans hc) hgi'
    have hv1' : 1 ≤ vR (yhK c) x := by
      have h := va_le_mono hE hBE hEU hlim hIH hx hx1 hkc1 (hkc.trans hc)
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
      exact (glA_lev hx hx1 hv1' (va_mono hE hBE hEU hlim hIH hx hx1 hlt hkE hgk' hgk) hkT hk1' hiT hi1
        hi'T hi'1).2 hIHi
    · rw [heqk] at hcE2 ⊢
      have hη' : yhI c < yhI E := yhPsi_lt_iff.1 hcE2
      exact glA_lt_of hx hx1 hv1 hkT hk1' hi'T hiT hi1 (va_mono hE hBE hEU hlim hIH hx hx1 hη' hiE hgi' hgi)
    · have hle : yhPsi (yhK c) (yhI c) ≤ yhI E := (yhPsi_lt_lev' hgt hkc1).1 hcE2
      rw [hpsi'] at hle
      have h2 := va_le_mono hE hBE hEU hlim hIH hx hx1 hle hiE hg hgi
      rw [vR_base hcE' hGc, vA_psi hnA] at h2
      exact (glA_lev' hx hx1 hv1 (va_mono hE hBE hEU hlim hIH hx hx1 hgt (hkc.trans hc) hgk hgk') hk'T hk'1
        hiT hi1 hi'T hi'1).2 h2

/-- **`vA E x < gq(D(x)+1) x`.** -/
theorem va_V_lt_gq (hgx : max ω (yrQE E) < x) : vA E x < gq (ywV 1 0 x + 1) x := by
  obtain ⟨-, -, -, hkE, hiE, -⟩ := va_dat hE hBE hEU
  obtain ⟨hgk, hgi, -, -, -, -, -, hA⟩ := va_datx hE hBE hEU hlim hIH hx hx1 hgx
  obtain ⟨hDT, -, hD1, -⟩ := zmD_facts hx hx1
  obtain ⟨hD1T, hD11⟩ := gl_T_succ hx hx1 hDT hD1
  rw [hA]
  exact xkA_lt hx hx1 hD1T hD11 (va_T hE hBE hEU hlim hIH hx hx1 hkE hgk).2.2
    (va_T hE hBE hEU hlim hIH hx hx1 hiE hgi).2.2

/-- **The readings of the codes below `E` are cofinal in `vA E x`.** -/
theorem va_top (hgx : max ω (yrQE E) < x) : ∀ ν, ν < vA E x → ∃ b, b < E ∧ yrG b < x ∧ ν ≤ vR b x := by
  have hωx : ω < x := omega0_lt_inE hx
  have hxl : IsSuccLimit x := ev_isSuccLimit_of_inE hx
  have hEl : IsSuccLimit E := ev_isSuccLimit_of_inE hE
  obtain ⟨hnA, hGE, hk1, hkE, hiE, hpsi⟩ := va_dat hE hBE hEU
  obtain ⟨hgk, hgi, hv1, hkT, hk1', hiT, hi1, hA⟩ := va_datx hE hBE hEU hlim hIH hx hx1 hgx
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
  have hgB : yrG tfBG < x := by
    rw [yrG_base (Low.opow_eq_self_of_SC tfBG_SC) va_G_le_BG, va_QE_BG]; exact hx.pos
  have hxu : x < u := by
    have h := hu1 tfBG hBE hgB
    rw [vR_BG] at h
    exact (zmD_facts hx hx1).2.1.trans h
  -- codes above `G` suffice
  have hbig : ∀ y, y < u → ∃ b, b < E ∧ gcG 0 ≤ b ∧ yrG b < x ∧ y < vR b x := by
    intro y hy
    obtain ⟨b, hb, hg, hyb⟩ := hu5 y hy
    have hgG : yrG (gcG 0) < x := by rw [yrG_G0]; exact hx.pos
    refine ⟨max b (gcG 0), max_lt hb hGE, le_max_right _ _, ?_, ?_⟩
    · rcases le_total b (gcG 0) with h | h
      · rw [max_eq_right h]; exact hgG
      · rw [max_eq_left h]; exact hg
    · refine hyb.trans_le (va_le_mono hE hBE hEU hlim hIH hx hx1 (le_max_left _ _) (max_lt hb hGE) hg ?_)
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
    obtain ⟨hbT, hb1, -⟩ := va_T hE hBE hEU hlim hIH hx hx1 hb hgb
    obtain ⟨α'', hα''k, hgα'', ha'α''⟩ := va_below hE hBE hEU hlim hIH hx hx1 hkE
      (zero_lt_one.trans_le hk1).ne' hgk a' ha'
    rcases eq_or_ne α'' 0 with h0 | h0
    · -- `a' = 0`: below the next base reading
      rw [h0, vR_zero] at ha'α''
      rw [le_antisymm ha'α'' zero_le, veblen_zero_apply]
      obtain ⟨e, M, he, heB, -, hemax, hME, hbM, hMlt, -, hEgeq, hEg, hV, hR, hG, -⟩ := va_mem hEU hlim hIH hBE hb
      have hgM : M.Eg < x := hEg.trans_lt (max_lt hωx hgb)
      have hGbM := va_memG hωx hEg hgb hG hbM hgb
      have hlt := M.lt b x hx hx1 hbM hGbM
      rw [hR b hbM x hx hx1 hGbM, (hV x hx hx1 hgM).2] at hlt
      have hMEE : InE M.E := by rw [hME]; exact eN_E e
      have hGME : gcG 0 ≤ M.E := (va_G_le_BG.trans heB).trans (hME ▸ (lt_eN e).le)
      have heU : e < vaU := (hemax.trans_lt (max_lt hb hBE)).trans hEU
      have hgME : yrG M.E < x := by
        rw [yrG_base hMEE hGME, hME]
        exact va_QE_eN_lt he heB (heU.trans_le va_U_le_B2) hxl hωx ((le_max_right _ _).trans_lt (hEgeq ▸ hgM))
      have hVu := hu1 M.E hMlt hgME
      rw [vR_base hMEE hGME] at hVu
      have hVE : InE (vA M.E x) := by rw [← (hV x hx hx1 hgM).2]; exact (M.V_T x hx hx1 hgM).2.1
      exact (((opow_lt_opow_iff_right one_lt_omega0).2 (hyb.trans hlt)).trans_le (by rw [hVE]) |>.trans hVu).le
    · -- `a' ≤ α''(x)`, `1 ≤ α''`
      have hα''1 : 1 ≤ α'' := one_le_iff_ne_zero.2 h0
      have hα''E : α'' < E := hα''k.trans hkE
      obtain ⟨hα''T, hα''Ω, -⟩ := va_T hE hBE hEU hlim hIH hx hx1 hα''E hgα''
      have hv1'' : 1 ≤ vR α'' x := by
        have h := va_le_mono hE hBE hEU hlim hIH hx hx1 hα''1 hα''E
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
    obtain ⟨η'', hη'', hgη'', hση''⟩ := va_below hE hBE hEU hlim hIH hx hx1 hiE hη0 hgi σ hσ
    have hgG : yrG (gcG 0) < x := by rw [yrG_G0]; exact hx.pos
    -- a smaller index whose atom is above `G`
    have hG0B : gcG 0 < tfBG := by
      rw [← zb_gcG_BG] at hBE ⊢; exact gcG_lt (Rj.rj_Om1_pos.trans tfBG_gt)
    obtain ⟨η₃, hη₃, hgη₃, hση₃, hGη₃⟩ : ∃ η₃, η₃ < yhI E ∧ yrG η₃ < x ∧ σ ≤ vR η₃ x ∧
        gcG 0 < yhPsi (yhK E) η₃ := by
      by_cases hη : tfBG ≤ yhI E
      · have hGη : gcG 0 < yhI E := hG0B.trans_le hη
        have hm : max η'' (gcG 0) < yhI E := max_lt hη'' hGη
        have hgm : yrG (max η'' (gcG 0)) < x := by
          rcases le_total η'' (gcG 0) with h | h
          · rw [max_eq_right h]; exact hgG
          · rw [max_eq_left h]; exact hgη''
        refine ⟨max η'' (gcG 0), hm, hgm, hση''.trans (va_le_mono hE hBE hEU hlim hIH hx hx1 (le_max_left _ _)
          (hm.trans hiE) hgη'' hgm), (le_max_right _ _).trans_lt (lt_yhPsi _ _)⟩
      · have hα : tfBG ≤ yhK E := by
          by_contra hα
          have h := yhPsi_lt_SC tfBG_SC tfBG_gt (not_le.1 hα) (not_le.1 hη)
          rw [hpsi] at h
          exact absurd hBE (not_lt.2 h.le)
        exact ⟨η'', hη'', hgη'', hση'', (hG0B.trans_le hα).trans (yhPsi_gt hk1 η'').2⟩
    have hpE : yhPsi (yhK E) η₃ < E := by
      have := (yhPsi_lt_iff (α := yhK E)).2 hη₃; rwa [hpsi] at this
    have hgp : yrG (yhPsi (yhK E) η₃) < x := by
      rw [yrG_psi hk1 hGη₃]
      exact max_lt ((yrQ_le _).trans_lt hgk) ((yrQ_le _).trans_lt hgη₃)
    obtain ⟨hη₃T, hη₃1, -⟩ := va_T hE hBE hEU hlim hIH hx hx1 (hη₃.trans hiE) hgη₃
    have hσT : σ ∈ Tset x := vz_T_down hx hx1 hη₃T hη₃1 hση₃
    have h1 := (glA_le_iff hx hx1 hv1 hkT hk1' hσT (hση₃.trans_lt hη₃1) hη₃T hη₃1).2 hση₃
    rw [← vR_psi hk1 hGη₃] at h1
    exact h1.trans_lt (hu1 _ hpE hgp)
  have hmin := glA_min hx hx1 hv1 hkT hk1' hiT hi1 hPu hxu (hu1 _ hiE hgi) (hu1 _ hkE hgk) hprev
  rw [← hA] at hmin
  exact absurd (hmin.trans hu2) (not_le.2 hν)

end Lim

end Googology.Trans.PoR.InaccPsi.R2.Va
