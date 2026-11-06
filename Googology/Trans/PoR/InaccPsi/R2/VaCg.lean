import Googology.Trans.PoR.InaccPsi.R2.VaB2
import Googology.Trans.PoR.InaccPsi.R2.ZmNx
import Googology.Trans.PoR.InaccPsi.R2.ZmRa

/-!
# VaCg: DIGIT SYSTEMS READ BY `vR` — THE BASE `B_Γ` AND THE STEP TO THE NEXT `ε`-NUMBER

`VaGood E`: a digit system `Zm.ZmDS` at the `ε`-number base `E` whose base reading is `vA E`, whose readings are
`vR` and whose gates are `max Eg (yrG c)` (`c ≠ 0`) with base gate `Eg = max ω (yrQE E)` (the `ω` absorbs the
finite gates of finite parts, where `Zm.ZmDS.sG` and `Yr.yrG` differ).  Below `Γ_{B_Γ+1}` (`vaU`) the only atom
`≥ B_Γ` is `B_Γ` (`va_atom_cases`).

* `vaU`, `va_atom_cases`, `va_maxQ`, `va_QE_eN` (**the base gate does not drop at the next `ε`-number**);
* `va_sG`, `va_sR` (**the step reads `vR` with gates `max Eg (yrG c)`**), `va_eN` (**`ε_{vA(E)(x)+1} =
  vA(ε_{E+1})(x)`**);
* `VaGood`, `vaGood_BG` (**`B_Γ`: `Zm.zmYr` raised by `ω`**), `vaGood_succ` (**`E ↦ ε_{E+1}` by
  `Zm.ZmDS.step` raised to the gate of the new base**).

No new axiom.  New definitions: `vaU`, `VaGood`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Va

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Tf Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Yr Googology.Trans.PoR.InaccPsi.R2.Yw Googology.Trans.PoR.InaccPsi.R2.Gd
  Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Zb
  Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Yh Googology.Trans.PoR.InaccPsi.R2.Zm
  Googology.Trans.PoR.InaccPsi.R2.Gk

/-! ## The bound `Γ_{B_Γ+1}` and the atoms below it -/

/-- **The gate of a part up to the finite ones**: `max g (yrG a) = max g (yrQ a)` for `ω ≤ g`. -/
theorem va_maxQ {g : Ordinal.{0}} (hω : ω ≤ g) (a : Ordinal.{0}) : max g (yrG a) = max g (yrQ a) := by
  unfold yrQ
  split_ifs with ha
  · obtain ⟨n, rfl⟩ := lt_omega0.1 ha
    rw [yrG_low (yh_nat_lt_G n), glG_nat, max_eq_left ((natCast_lt_omega0 n).le.trans hω),
      max_eq_left zero_le]
  · rfl

theorem va_one_notAt : ¬ YhAt (1 : Ordinal.{0}) :=
  fun h => absurd h.2 (not_lt.2 (le_of_lt (one_lt_omega0.trans Gf.omega_lt_Om1)))

/-- The data of a non-atom `ε`-number code `e > G`. -/
theorem va_data {e : Ordinal.{0}} (he : InE e) (hGe : gcG 0 < e) (hnA : ¬ YhAt e) :
    1 ≤ yhK e ∧ yhK e < e ∧ yhI e < e ∧ yhPsi (yhK e) (yhI e) = e := yhData_spec he hGe hnA

theorem va_G_lt_eN {e : Ordinal.{0}} (hGe : gcG 0 ≤ e) : gcG 0 < eN e := hGe.trans_lt (lt_eN e)

/-- **The next `ε`-number on the code side**: `ε_{e+1} = yhPsi 1 e` at a fixed point of `φ(1, ·)`,
`yhPsi 1 (η+1)` at `e = yhPsi 1 η`. -/
theorem va_eN_code {e : Ordinal.{0}} (he : InE e) (hBe : tfBG ≤ e) (heU : e < vaU) :
    (veblen 1 e = e ∧ eN e = yhPsi 1 e) ∨
      (¬ YhAt e ∧ yhK e = 1 ∧ eN e = yhPsi 1 (yhI e + 1)) := by
  have hOe : Om1 < e := tfBG_gt.trans_le hBe
  rcases va_atom_cases hBe heU with rfl | hnA
  · exact Or.inl ⟨zm_BG_fix, (va_psi1_fix zm_BG_fix tfBG_gt).symm⟩
  have hGe : gcG 0 < e := by
    refine lt_of_le_of_ne (va_G_le_BG.trans hBe) fun h => hnA (h ▸ yhAt_gcG 0)
  obtain ⟨hk1, -, -, hpsi⟩ := va_data he hGe hnA
  rcases hk1.lt_or_eq with hk2 | hk2
  · have hPe : LuP (yhK e) e := by have := yhPsi_P (yhK e) (yhI e); rwa [hpsi] at this
    have hP : LuP (1 + 1) e := luP_mono le_add_self (add_one_le_of_lt hk2) hPe
    exact Or.inl ⟨luP_succ.1 hP, (va_psi1_fix (luP_succ.1 hP) hOe).symm⟩
  · refine Or.inr ⟨hnA, hk2.symm, ?_⟩
    have h := va_psi1_succ (yhI e)
    rw [← hk2] at hpsi
    rw [hpsi] at h
    exact h.symm

/-- **The base gate does not drop at the next `ε`-number.** -/
theorem va_QE_eN {e : Ordinal.{0}} (he : InE e) (hBe : tfBG ≤ e) (heU : e < vaU) :
    yrQE e ≤ max ω (yrQE (eN e)) := by
  have hGe' : gcG 0 ≤ e := va_G_le_BG.trans hBe
  rcases va_eN_code he hBe heU with ⟨hfix, hN⟩ | ⟨hnA, hk, hN⟩
  · have h1 : yrQE (eN e) = max (yrQ 1) (yrQ e) := by
      have hG : gcG 0 < yhPsi 1 e := hN ▸ va_G_lt_eN hGe'
      obtain ⟨d1, d2⟩ := yhData_eq le_rfl hG
      rw [hN, yrQE_psi (yhPsi_notAt le_rfl), d1, d2]
    rw [h1, yrQ_one, max_eq_right zero_le]
    have h2 : yrQ e = yrQE e := by
      unfold yrQ; rw [if_neg (not_lt.2 (omega0_le_of_isSuccLimit (ev_isSuccLimit_of_inE he))), yrG_base he hGe']
    rw [h2]; exact le_max_right _ _
  · have hGe : gcG 0 < e := lt_of_le_of_ne hGe' fun h => hnA (h ▸ yhAt_gcG 0)
    have h1 : yrQE (eN e) = max (yrQ 1) (yrQ (yhI e + 1)) := by
      have hG : gcG 0 < yhPsi 1 (yhI e + 1) := hN ▸ va_G_lt_eN hGe'
      obtain ⟨d1, d2⟩ := yhData_eq le_rfl hG
      rw [hN, yrQE_psi (yhPsi_notAt le_rfl), d1, d2]
    rw [h1, yrQ_one, max_eq_right zero_le, yrQE_psi hnA, hk, yrQ_one, max_eq_right zero_le,
      ← va_maxQ le_rfl]
    exact (yrQ_le _).trans ((yrG_le_succ _).trans (le_max_right _ _))

/-! ## The step reads `vR` -/

theorem va_max4 {A Q k d r : Ordinal.{0}} (hQ : Q ≤ A) :
    max (max A k) (max (max A d) (max A r)) = max A (max (max Q k) (max d r)) := by
  apply le_antisymm
  · refine max_le (max_le (le_max_left _ _) ?_) (max_le (max_le (le_max_left _ _) ?_) (max_le (le_max_left _ _) ?_))
    · exact (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_right _ _))
    · exact (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
    · exact (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  · refine max_le ((le_max_left _ _).trans (le_max_left _ _)) (max_le (max_le ?_ ?_) (max_le ?_ ?_))
    · exact hQ.trans ((le_max_left _ _).trans (le_max_left _ _))
    · exact (le_max_right _ _).trans (le_max_left _ _)
    · exact (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_right _ _))
    · exact (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))

theorem va_max3 {A Q k d : Ordinal.{0}} (hQ : Q ≤ A) :
    max (max A k) (max (max A d) 0) = max A (max (max Q k) (max d 0)) := by
  rw [max_eq_left (zero_le : (0 : Ordinal.{0}) ≤ max A d), max_eq_left (zero_le : (0 : Ordinal.{0}) ≤ d)]
  apply le_antisymm
  · refine max_le (max_le (le_max_left _ _) ?_) (max_le (le_max_left _ _) ?_)
    · exact (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_right _ _))
    · exact (le_max_right _ _).trans (le_max_right _ _)
  · refine max_le ((le_max_left _ _).trans (le_max_left _ _)) (max_le (max_le ?_ ?_) ?_)
    · exact hQ.trans ((le_max_left _ _).trans (le_max_left _ _))
    · exact (le_max_right _ _).trans (le_max_left _ _)
    · exact (le_max_right _ _).trans (le_max_right _ _)

section Step

variable (M : ZmDS) (hω : ω ≤ M.Eg) (hQ : yrQE M.E ≤ M.Eg) (hGe : gcG 0 ≤ M.E)
  (hV : ∀ x, InE x → x < Om1 → M.Eg < x → M.V x = vA M.E x)
  (hR : ∀ c, c < M.E → ∀ x, InE x → x < Om1 → M.G c < x → M.R c x = vR c x)
  (hG : ∀ c, c < M.E → c ≠ 0 → M.G c = max M.Eg (yrG c))

include hω hQ hGe hG in
/-- **The gates of the step are `max Eg (yrG c)`.** -/
theorem va_sG : ∀ c, c < eN M.E → c ≠ 0 → M.sG c = max M.Eg (yrG c) := by
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
  have hyG := yrG_cnf M.E_E hGe hk0.ne' hd0.ne' hdE hrk hv
  rw [hdec] at hsG hyG
  rw [hsG, hyG, IH k hko (hko.trans hcN) hk0.ne', hG d hdE hd0.ne', va_maxQ hω k, va_maxQ hω d]
  rcases eq_or_ne r 0 with hr0 | hr0
  · rw [hr0, M.sG_zero, yrG_zero]
    exact va_max3 hQ
  · rw [IH r hro (hro.trans hcN) hr0]
    exact va_max4 hQ

include hGe hV hR in
/-- **The step reads `vR`.** -/
theorem va_sR : ∀ c, c < eN M.E → ∀ x, InE x → x < Om1 → M.Eg < x → M.sG c < x → M.sR c x = vR c x := by
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
  have hvR := vR_cnf M.E_E hGe hk0.ne' hd0.ne' hdE hrk hv x
  rw [hdec] at hsR hvR
  rw [hsR, hvR, hV x hx hx1 hgx, IH k hko (hko.trans hcN) x hx hx1 hgx hgk, hR d hdE x hx hx1 hgd,
    IH r hro (hro.trans hcN) x hx hx1 hgx hgr]

end Step

/-! ## The next base reading -/

section ENext

variable (M : ZmDS) (hω : ω ≤ M.Eg) (hQ : yrQE M.E ≤ M.Eg) (hBE : tfBG ≤ M.E) (hEU : M.E < vaU)
  (hV : ∀ x, InE x → x < Om1 → M.Eg < x → M.V x = vA M.E x)
  (hR : ∀ c, c < M.E → ∀ x, InE x → x < Om1 → M.G c < x → M.R c x = vR c x)
  (hG : ∀ c, c < M.E → c ≠ 0 → M.G c = max M.Eg (yrG c))

include hω hQ hBE hEU hR hG in
/-- **`ε_{vA(E)(x)+1} = vA(ε_{E+1})(x)`.** -/
theorem va_eN {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hgx : M.Eg < x) :
    eN (vA M.E x) = vA (eN M.E) x := by
  have hE := M.E_E
  have hGe' : gcG 0 ≤ M.E := va_G_le_BG.trans hBE
  obtain ⟨hVT, -, -, hVq⟩ := M.V_T x hx hx1 hgx
  have hV1 : M.V x < Om1 := hVq.trans (ywX_facts hx hx1).2.2.1
  -- the readings of the codes below `E` are in `Tˣ ∩ Ω₁`
  have hcode : ∀ c, c < M.E → max M.Eg (yrG c) < x → vR c x ∈ Tset x ∧ vR c x < Om1 := by
    intro c hc hgc
    have hGc : M.G c < x := by
      rcases eq_or_ne c 0 with rfl | h0
      · rw [M.G0]; exact hx.pos
      · rw [hG c hc h0]; exact hgc
    rw [← hR c hc x hx hx1 hGc]
    have hlt := M.lt c x hx hx1 hc hGc
    exact ⟨vz_T_down hx hx1 hVT hV1 hlt.le, hlt.trans hV1⟩
  rcases va_atom_cases hBE hEU with hB | hnA
  · rw [hB, vA_BG, ← va_psi1_fix zm_BG_fix tfBG_gt,
      vA_psi' le_rfl (va_psi1_fix zm_BG_fix tfBG_gt ▸ va_G_lt_eN va_G_le_BG), vR_one, vR_BG]
    exact zmD_eN hx hx1
  have hGe : gcG 0 < M.E := lt_of_le_of_ne hGe' fun h => hnA (h ▸ yhAt_gcG 0)
  obtain ⟨hk1, hkE, hiE, hpsi⟩ := va_data hE hGe hnA
  have hQE : yrQE M.E = max (yrQ (yhK M.E)) (yrQ (yhI M.E)) := yrQE_psi hnA
  have hgk : max M.Eg (yrG (yhK M.E)) < x := by
    rw [va_maxQ hω, max_eq_left ((le_max_left _ _).trans (hQE ▸ hQ))]; exact hgx
  have hgi : max M.Eg (yrG (yhI M.E)) < x := by
    rw [va_maxQ hω, max_eq_left ((le_max_right _ _).trans (hQE ▸ hQ))]; exact hgx
  obtain ⟨hkT, hk1'⟩ := hcode _ hkE hgk
  obtain ⟨hiT, hi1⟩ := hcode _ hiE hgi
  have hvk1 : 1 ≤ vR (yhK M.E) x := by
    rcases hk1.lt_or_eq with h | h
    · have hG1 : M.G 1 < x := M.G1.trans_lt (max_lt hgx (lu_one_lt_E hx))
      have hGk : M.G (yhK M.E) < x := by
        rw [hG _ hkE (zero_lt_one.trans_le hk1).ne']; exact hgk
      have hm := M.mono 1 (yhK M.E) x hx hx1 h hkE hG1 hGk
      rw [hR _ hkE x hx hx1 hGk, hR 1 ((lu_one_lt_E hE).trans_le' le_rfl |>.trans_le' le_rfl) x hx hx1 hG1,
        vR_one] at hm
      exact hm.le
    · rw [← h, vR_one]
  have hA : vA M.E x = glA (vR (yhK M.E) x) (vR (yhI M.E) x) x := vA_psi hnA x
  rcases va_eN_code hE hBE hEU with ⟨hfix, hN⟩ | ⟨-, hk, hN⟩
  · -- a fixed point of `φ(1, ·)`: the level is at least `2`
    have hk2 : 2 ≤ yhK M.E := by
      by_contra hc
      push Not at hc
      have hk1e : yhK M.E = 1 := le_antisymm (Order.lt_add_one_iff.1 (by rw [one_add_one_eq_two]; exact hc)) hk1
      have hnP := yhPsi_notP (yhK M.E) (yhI M.E)
      rw [hpsi, hk1e] at hnP
      exact hnP (luP_succ.2 hfix)
    have hvk2 : 2 ≤ vR (yhK M.E) x := by
      rcases hk2.lt_or_eq with h | h
      · have e2 : ((2 : ℕ) : Ordinal.{0}) = 2 := by norm_num
        have hvR2 : vR 2 x = 2 := by have := vR_nat 2 x; rwa [e2] at this
        have hyG2 : yrG 2 = 2 := by
          have := yrG_low (yh_nat_lt_G 2); rw [glG_nat, e2] at this; exact this
        have h2ω : (2 : Ordinal.{0}) < ω := by rw [← e2]; exact natCast_lt_omega0 2
        have h2E : (2 : Ordinal.{0}) < M.E := h.trans hkE
        have hG2 : M.G 2 < x := by
          rw [hG 2 h2E two_ne_zero, hyG2]
          exact max_lt hgx (h2ω.trans (omega0_lt_inE hx))
        have hGk : M.G (yhK M.E) < x := by
          rw [hG _ hkE (zero_lt_one.trans_le hk1).ne']; exact hgk
        have hm := M.mono 2 (yhK M.E) x hx hx1 h hkE hG2 hGk
        rw [hR _ hkE x hx hx1 hGk, hR 2 h2E x hx hx1 hG2, hvR2] at hm
        exact hm.le
      · have e2 : ((2 : ℕ) : Ordinal.{0}) = 2 := by norm_num
        have hvR2 : vR 2 x = 2 := by have := vR_nat 2 x; rwa [e2] at this
        rw [← h, hvR2]
    rw [hN, vA_psi' le_rfl (hN ▸ va_G_lt_eN hGe'), vR_one, vR_base hE hGe', hA]
    exact glA_eN_two hx hx1 hvk2 hkT hk1' hiT hi1
  · rw [hN, vA_psi' le_rfl (hN ▸ va_G_lt_eN hGe'), vR_one, vR_succ, hA, hk, vR_one]
    exact glA_eN_one hx hx1 hiT hi1

end ENext

/-! ## The systems -/

/-- **A digit system at the `ε`-number base `E` read by `vR`.** -/
def VaGood (E : Ordinal.{0}) : Prop :=
  ∃ M : ZmDS, M.E = E ∧ M.Eg = max ω (yrQE E) ∧
    (∀ x, InE x → x < Om1 → M.Eg < x → M.V x = vA E x) ∧
    (∀ c, c < E → ∀ x, InE x → x < Om1 → M.G c < x → M.R c x = vR c x) ∧
    (∀ c, c < E → c ≠ 0 → M.G c = max M.Eg (yrG c)) ∧ M.B = tfBG ∧ M.Dv = ywV 1 0

/-- **The base `B_Γ`**: `Zm.zmYr` raised by `ω`. -/
theorem vaGood_BG : VaGood tfBG := by
  have hQ : yrQE tfBG = 0 := by
    have hA : YhAt tfBG := by rw [← zb_gcG_BG]; exact yhAt_gcG _
    have hJ : yhJ tfBG = tfBG := by have h := yhJ_gcG tfBG; rwa [zb_gcG_BG] at h
    exact yrQE_atom_fix hA (by rw [hJ]; exact lt_irrefl _)
  have hEg : (zmYr.raise ω).Eg = ω := by
    rw [ZmDS.raise_Eg]; exact max_eq_right zero_le
  refine ⟨zmYr.raise ω, rfl, by rw [hEg, hQ, max_eq_left zero_le], fun x _ _ _ => (vA_BG x).symm,
    fun c hc x _ _ _ => (vR_yr c hc x).symm, fun c _ hc0 => ?_, rfl, rfl⟩
  rw [ZmDS.raise_G _ _ hc0, hEg]; rfl

/-- **The step to the next `ε`-number**, raised to the gate of the new base. -/
theorem vaGood_succ {e : Ordinal.{0}} (he : InE e) (hBe : tfBG ≤ e) (heU : e < vaU) (h : VaGood e) :
    VaGood (eN e) := by
  obtain ⟨M, hE, hEg, hV, hR, hG, hBB, hDD⟩ := h
  subst hE
  have hω : ω ≤ M.Eg := hEg ▸ le_max_left _ _
  have hQ : yrQE M.E ≤ M.Eg := hEg ▸ le_max_right _ _
  have hGe : gcG 0 ≤ M.E := va_G_le_BG.trans hBe
  set g := max ω (yrQE (eN M.E)) with hgdef
  have hEg' : (M.step.raise g).Eg = g := by
    rw [ZmDS.raise_Eg, ZmDS.step_Eg, hEg]
    exact max_eq_right (max_le (le_max_left _ _) (va_QE_eN he hBe heU))
  refine ⟨M.step.raise g, rfl, hEg', fun x hx hx1 hgx => ?_, fun c hc x hx hx1 hgc => ?_, fun c hc hc0 => ?_,
    hBB, hDD⟩
  · have hgx' : M.Eg < x := (hEg ▸ max_le (le_max_left _ _) (va_QE_eN he hBe heU) : M.Eg ≤ g).trans_lt
      (hEg' ▸ hgx)
    show eN (M.V x) = _
    rw [hV x hx hx1 hgx']
    exact va_eN M hω hQ hBe heU hR hG hx hx1 hgx'
  · have hle : M.Eg ≤ g := hEg ▸ max_le (le_max_left _ _) (va_QE_eN he hBe heU)
    show M.sR c x = vR c x
    rcases eq_or_ne c 0 with rfl | hc0
    · rw [M.sR_zero, vR_zero]
    have hgc' : M.sG c < x := by
      have h1 := hgc
      rw [ZmDS.raise_G _ _ hc0] at h1
      exact (le_max_right _ _).trans_lt h1
    have hgx : M.Eg < x := (M.sG_Eg c hc0).trans_lt hgc'
    exact va_sR M hGe hV hR c hc x hx hx1 hgx hgc'
  · rw [ZmDS.raise_G _ _ hc0, hEg']
    show max g (M.sG c) = max g (yrG c)
    rw [va_sG M hω hQ hGe hG c hc hc0]
    have hle : M.Eg ≤ g := hEg ▸ max_le (le_max_left _ _) (va_QE_eN he hBe heU)
    rw [← max_assoc, max_eq_left hle]

end Googology.Trans.PoR.InaccPsi.R2.Va
