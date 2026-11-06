import Googology.Trans.PoR.InaccPsi.R2.VsFx

/-!
# VsCg: DIGIT SYSTEMS OVER THE SEGMENT BASE — THE STEP TO THE NEXT `ε`-NUMBER

`VsGood E`: a digit system `Zm.ZmDS` at the `ε`-number base `E ≥ B_Γ` read by `vR`, as `Va.VaGood`, over the
segment base `B = vaFB E` (the largest fixed point of `Γ` in `(Ω₁, E]`) read `vR B`.  Below `B₂` it is
`Va.VaGood` (`vsGood_of_va`).  The step `E ↦ ε_{E+1}` (`Zm.ZmDS.step` raised to the gate of the new base) keeps it
in every segment: at the segment base `E = F` the reading `vA F x = ϑˣ(Ω₁·(Ω₁+λ(x)) + K(x))` is a closed point, so
`ε_{vA F x + 1} = ϑˣ(Ω₁ + vA F x)` (`Va.vs_eN_cl`); at an atom `Γ(j)` past `F` the index reads
`F(x) + (j − (F+1))(x)` with the gates of `j` (`Va.vs_vI`, `Va.vs_FB_gate`, `Va.vs_off_gate`).

* `vs_eN_code`, `vs_QE_eN` (**the base gate does not drop at the next `ε`-number**);
* `vs_fix_cl` (**the reading of a fixed point of `Γ` is a closed point**, from the facts of its parts);
* `vs_eN` (**`ε_{vA(E)(x)+1} = vA(ε_{E+1})(x)`**);
* `VsGood`, `vsGood_of_va` (**below `B₂`**), `vsGood_succ`.

No new axiom.  New definition: `VsGood`.
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
  Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Rh

/-! ## The next `ε`-number on the code side -/

/-- **The next `ε`-number**: `ε_{e+1} = yhPsi 1 e` at a fixed point of `φ(1, ·)` (every atom), `yhPsi 1 (η+1)` at
`e = yhPsi 1 η`. -/
theorem vs_eN_code {e : Ordinal.{0}} (he : InE e) (hBe : tfBG ≤ e) :
    (veblen 1 e = e ∧ eN e = yhPsi 1 e) ∨ (¬ YhAt e ∧ yhK e = 1 ∧ eN e = yhPsi 1 (yhI e + 1)) := by
  have hOe : Om1 < e := tfBG_gt.trans_le hBe
  by_cases hA : YhAt e
  · have hfix : veblen 1 e = e := hA.1.veblen_right (gg_one_lt_of_SC hA.1)
    exact Or.inl ⟨hfix, (va_psi1_fix hfix hOe).symm⟩
  have hGe : gcG 0 < e := lt_of_le_of_ne (va_G_le_BG.trans hBe) fun h => hA (h ▸ yhAt_gcG 0)
  obtain ⟨hk1, -, -, hpsi⟩ := va_data he hGe hA
  rcases hk1.lt_or_eq with hk2 | hk2
  · have hPe : LuP (yhK e) e := by have := yhPsi_P (yhK e) (yhI e); rwa [hpsi] at this
    have hP : LuP (1 + 1) e := luP_mono le_add_self (add_one_le_of_lt hk2) hPe
    exact Or.inl ⟨luP_succ.1 hP, (va_psi1_fix (luP_succ.1 hP) hOe).symm⟩
  · refine Or.inr ⟨hA, hk2.symm, ?_⟩
    have h := va_psi1_succ (yhI e)
    rw [← hk2] at hpsi
    rw [hpsi] at h
    exact h.symm

/-- **The base gate does not drop at the next `ε`-number.** -/
theorem vs_QE_eN {e : Ordinal.{0}} (he : InE e) (hBe : tfBG ≤ e) : yrQE e ≤ max ω (yrQE (eN e)) := by
  have hGe' : gcG 0 ≤ e := va_G_le_BG.trans hBe
  rcases vs_eN_code he hBe with ⟨hfix, hN⟩ | ⟨hnA, hk, hN⟩
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

/-! ## The reading of a fixed point of `Γ` is a closed point -/

/-- **The reading of a fixed point `F_λ(y)` of `Γ` is a closed point**, once the readings of its parts below the
gate are in `Tˣ ∩ Ω₁` and `λ(x) ≥ 1`. -/
theorem vs_fix_cl {e x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hA : YhAt e) (hi : ¬ yhJ e < e)
    (heX : e < tlX) (hgx : max ω (yrQE e) < x)
    (hcode : ∀ c, c < e → yrG c < x → vR c x ∈ Tset x ∧ vR c x < Om1)
    (hl1 : 1 ≤ vR (tlLev e) x) :
    YwClosed x (vA e x) ∧ vR (tlLev e) x ∈ Tset x ∧ vR (tlLev e) x < Om1 ∧
      vK (tlLev e) (tlI (tlLev e) e) x ∈ Tset x ∧ vK (tlLev e) (tlI (tlLev e) e) x < Om1 := by
  obtain ⟨-, hlc, hyc, -, hne⟩ := vs_fix_data hA hi heX
  have hL : tlLev e < e ∧ tlI (tlLev e) e < e := ⟨hlc, hyc⟩
  obtain ⟨hlT, hl1'⟩ := hcode _ hlc ((vs_fix_gate_l hA hi heX).trans_lt hgx)
  have hK : vK (tlLev e) (tlI (tlLev e) e) x ∈ Tset x ∧ vK (tlLev e) (tlI (tlLev e) e) x < Om1 := by
    unfold vK
    split_ifs with hF
    · obtain ⟨hgf, hgo⟩ := vs_fix_gate_f hA hi heX hF
      obtain ⟨-, -, hfy⟩ := vs_fpL_mem hne hF
      obtain ⟨hfT, hf1⟩ := hcode _ (hfy.trans hyc) (hgf.trans_lt hgx)
      obtain ⟨hoT, ho1⟩ := hcode _ ((Ordinal.sub_le_self _ _).trans_lt hyc) (hgo.trans_lt hgx)
      have hO : IsSuccLimit Om1 := gl_Om1_lim
      exact ⟨vzT_add hx hx1 hfT hoT, (inE_indec gl_Om1_E).add_lt hf1 ho1⟩
    · exact hcode _ ((Ordinal.sub_le_self _ _).trans_lt hyc) ((vs_fix_gate_0 hA hi heX).trans_lt hgx)
  rw [vA_atom_fix hA hi hL]
  exact ⟨ywV_closed hx hx1 (zero_lt_one.trans_le hl1) hlT hl1' hK.1 hK.2, hlT, hl1', hK.1, hK.2⟩

/-! ## The next base reading -/

section ENext

variable (M : ZmDS) (hω : ω ≤ M.Eg) (hQ : yrQE M.E ≤ M.Eg)
  (hV : ∀ x, InE x → x < Om1 → M.Eg < x → M.V x = vA M.E x)
  (hR : ∀ c, c < M.E → ∀ x, InE x → x < Om1 → M.G c < x → M.R c x = vR c x)
  (hG : ∀ c, c < M.E → c ≠ 0 → M.G c = max M.Eg (yrG c))

include hω hQ hV hR hG in
/-- **`ε_{vA(E)(x)+1} = vA(ε_{E+1})(x)`** for a system at any `ε`-number base `E ≥ B_Γ`. -/
theorem vs_eN {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hgx : M.Eg < x) :
    eN (vA M.E x) = vA (eN M.E) x := by
  have hE := M.E_E
  have hBE : tfBG ≤ M.E := M.BG_le
  have hGe' : gcG 0 ≤ M.E := va_G_le_BG.trans hBE
  have hOE : Om1 < M.E := tfBG_gt.trans_le hBE
  obtain ⟨hVT, -, -, hVq⟩ := M.V_T x hx hx1 hgx
  have hV1 : M.V x < Om1 := hVq.trans (ywX_facts hx hx1).2.2.1
  have hωx : ω < x := omega0_lt_inE hx
  -- the readings of the codes below `E` with gates up to the base gate are in `Tˣ ∩ Ω₁`
  have hcode : ∀ c, c < M.E → yrG c < x → max M.Eg (yrG c) < x → vR c x ∈ Tset x ∧ vR c x < Om1 := by
    intro c hc _ hgc
    have hGc : M.G c < x := by
      rcases eq_or_ne c 0 with rfl | h0
      · rw [M.G0]; exact hx.pos
      · rw [hG c hc h0]; exact hgc
    rw [← hR c hc x hx hx1 hGc]
    have hlt := M.lt c x hx hx1 hc hGc
    exact ⟨vz_T_down hx hx1 hVT hV1 hlt.le, hlt.trans hV1⟩
  have hcodeE : ∀ c, c < M.E → yrG c ≤ max ω (yrQE M.E) → vR c x ∈ Tset x ∧ vR c x < Om1 := by
    intro c hc hgc
    have hle : yrG c ≤ M.Eg := hgc.trans (max_le hω hQ)
    exact hcode c hc (hle.trans_lt hgx) (by rw [max_eq_left hle]; exact hgx)
  have hQx : max ω (yrQE M.E) < x := (max_le hω hQ).trans_lt hgx
  rcases vs_atom_cases hBE with hB | ⟨hA, hjB, hjE⟩ | hnA
  · -- the segment base: a fixed point of `Γ`, read at a closed point
    have hfixG : gamma M.E = M.E := by rw [hB]; exact vs_FB_fix hBE
    have hA : YhAt M.E := ⟨by rw [← hfixG]; exact Lq.lq_gamma_SC _, hOE⟩
    have hi : ¬ yhJ M.E < M.E := by
      have h := yhJ_gcG M.E; rw [vs_gcG_fix hfixG hOE] at h; rw [h]; exact lt_irrefl _
    have hfixE : veblen 1 M.E = M.E := zm_fix_of_gamma hfixG
    have hN : eN M.E = yhPsi 1 M.E := (va_psi1_fix hfixE hOE).symm
    rw [hN, vA_psi' le_rfl (hN ▸ va_G_lt_eN hGe'), vR_one, vR_base hE hGe']
    obtain ⟨h1l, hlE, -, -, -⟩ := vs_fix_data hA hi M.E_X
    have hgl := vs_fix_gate_l hA hi M.E_X
    have hl1 : 1 ≤ vR (tlLev M.E) x := by
      rcases h1l.lt_or_eq with h | h
      · have hG1 : M.G 1 < x := M.G1.trans_lt (max_lt hgx (lu_one_lt_E hx))
        have hGl : M.G (tlLev M.E) < x := by
          rw [hG _ hlE (zero_lt_one.trans_le h1l).ne']
          exact max_lt hgx ((hgl.trans (max_le hω hQ)).trans_lt hgx)
        have hm := M.mono 1 (tlLev M.E) x hx hx1 h hlE hG1 hGl
        rw [hR _ hlE x hx hx1 hGl, hR 1 (M.one_lt_E) x hx hx1 hG1, vR_one] at hm
        exact hm.le
      · rw [← h, vR_one]
    obtain ⟨hcl, -⟩ := vs_fix_cl hx hx1 hA hi M.E_X hQx (fun c hc hgc => by
      by_cases hle : yrG c ≤ max ω (yrQE M.E)
      · exact hcodeE c hc hle
      · exact hcode c hc hgc (max_lt hgx hgc)) hl1
    have hVA : M.V x = vA M.E x := hV x hx hx1 hgx
    have hxV : x < vA M.E x := by
      rw [← hVA]; exact (M.Dv_T x hx hx1 hgx).2.2.1.trans_le (M.V_T x hx hx1 hgx).2.2.1
    rw [← hVA] at hcl hxV ⊢
    exact vs_eN_cl hx hx1 hVT hV1 hxV hcl
  · -- an atom `Γ(j)` past the segment base: the index reading is in `Tˣ ∩ Ω₁`
    have hfixE : veblen 1 M.E = M.E := hA.1.veblen_right (gg_one_lt_of_SC hA.1)
    have hN : eN M.E = yhPsi 1 M.E := (va_psi1_fix hfixE hOE).symm
    rw [hN, vA_psi' le_rfl (hN ▸ va_G_lt_eN hGe'), vR_one, vR_base hE hGe', vA_atom hA hjE,
      vs_vI hBE hjB hjE.le]
    have hFE : InE (vaFB M.E) := vs_FB_E hBE
    have hGF : gcG 0 ≤ vaFB M.E := va_G_le_BG.trans (vs_FB_ge hBE)
    have hQj : max ω (yrG (yhJ M.E)) = max ω (yrQE M.E) := by rw [va_maxQ le_rfl, yrQE_atom hA hjE]
    have hgF : yrG (vaFB M.E) ≤ max ω (yrQE M.E) := by
      have h := vs_FB_gate M.E hBE; rwa [yrG_base hE hGe'] at h
    have hgo : yrG (yhJ M.E - (vaFB M.E + 1)) ≤ max ω (yrQE M.E) :=
      (vs_off_gate hFE hGF hjB).trans hQj.le
    obtain ⟨hFT, hF1⟩ := hcodeE _ (hjB.trans hjE) hgF
    obtain ⟨hoT, ho1⟩ := hcodeE _ ((Ordinal.sub_le_self _ _).trans_lt hjE) hgo
    exact va_eN_gq hx hx1 (vzT_add hx hx1 hFT hoT) ((inE_indec gl_Om1_E).add_lt hF1 ho1)
  have hGe : gcG 0 < M.E := lt_of_le_of_ne hGe' fun h => hnA (h ▸ yhAt_gcG 0)
  obtain ⟨hk1, hkE, hiE, hpsi⟩ := va_data hE hGe hnA
  have hQE : yrQE M.E = max (yrQ (yhK M.E)) (yrQ (yhI M.E)) := yrQE_psi hnA
  have hgk : max M.Eg (yrG (yhK M.E)) < x := by
    rw [va_maxQ hω, max_eq_left ((le_max_left _ _).trans (hQE ▸ hQ))]; exact hgx
  have hgi : max M.Eg (yrG (yhI M.E)) < x := by
    rw [va_maxQ hω, max_eq_left ((le_max_right _ _).trans (hQE ▸ hQ))]; exact hgx
  obtain ⟨hkT, hk1'⟩ := hcode _ hkE ((le_max_right _ _).trans_lt hgk) hgk
  obtain ⟨hiT, hi1⟩ := hcode _ hiE ((le_max_right _ _).trans_lt hgi) hgi
  have hvk1 : 1 ≤ vR (yhK M.E) x := by
    rcases hk1.lt_or_eq with h | h
    · have hG1 : M.G 1 < x := M.G1.trans_lt (max_lt hgx (lu_one_lt_E hx))
      have hGk : M.G (yhK M.E) < x := by
        rw [hG _ hkE (zero_lt_one.trans_le hk1).ne']; exact hgk
      have hm := M.mono 1 (yhK M.E) x hx hx1 h hkE hG1 hGk
      rw [hR _ hkE x hx hx1 hGk, hR 1 M.one_lt_E x hx hx1 hG1, vR_one] at hm
      exact hm.le
    · rw [← h, vR_one]
  have hA : vA M.E x = glA (vR (yhK M.E) x) (vR (yhI M.E) x) x := vA_psi hnA x
  rcases vs_eN_code hE hBE with ⟨hfix, hN⟩ | ⟨-, hk, hN⟩
  · -- a fixed point of `φ(1, ·)`: the level is at least `2`
    have hk2 : 2 ≤ yhK M.E := by
      by_contra hc
      push Not at hc
      have hk1e : yhK M.E = 1 := le_antisymm (Order.lt_add_one_iff.1 (by rw [one_add_one_eq_two]; exact hc)) hk1
      have hnP := yhPsi_notP (yhK M.E) (yhI M.E)
      rw [hpsi, hk1e] at hnP
      exact hnP (luP_succ.2 hfix)
    have hvk2 : 2 ≤ vR (yhK M.E) x := by
      have e2 : ((2 : ℕ) : Ordinal.{0}) = 2 := by norm_num
      have hvR2 : vR 2 x = 2 := by have := vR_nat 2 x; rwa [e2] at this
      rcases hk2.lt_or_eq with h | h
      · have hyG2 : yrG 2 = 2 := by
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
      · rw [← h, hvR2]
    rw [hN, vA_psi' le_rfl (hN ▸ va_G_lt_eN hGe'), vR_one, vR_base hE hGe', hA]
    exact glA_eN_two hx hx1 hvk2 hkT hk1' hiT hi1
  · rw [hN, vA_psi' le_rfl (hN ▸ va_G_lt_eN hGe'), vR_one, vR_succ, hA, hk, vR_one]
    exact glA_eN_one hx hx1 hiT hi1

end ENext

/-! ## The systems -/

/-- **A digit system at the `ε`-number base `E ≥ B_Γ` read by `vR`, over the segment base `vaFB E` read
`vR (vaFB E)`.** -/
def VsGood (E : Ordinal.{0}) : Prop :=
  ∃ M : ZmDS, M.E = E ∧ M.Eg = max ω (yrQE E) ∧
    (∀ x, InE x → x < Om1 → M.Eg < x → M.V x = vA E x) ∧
    (∀ c, c < E → ∀ x, InE x → x < Om1 → M.G c < x → M.R c x = vR c x) ∧
    (∀ c, c < E → c ≠ 0 → M.G c = max M.Eg (yrG c)) ∧ M.B = vaFB E ∧ M.Dv = vR (vaFB E)

/-- **Below `B₂` it is `Va.VaGood`.** -/
theorem vsGood_of_va {E : Ordinal.{0}} (hBE : tfBG ≤ E) (hE : E < vaB2) (h : VaGood E) : VsGood E := by
  obtain ⟨M, hME, hEg, hV, hR, hG, hB, hD⟩ := h
  refine ⟨M, hME, hEg, hV, hR, hG, by rw [hB, vs_FB_B2 hBE hE], ?_⟩
  rw [hD, vs_FB_B2 hBE hE]
  funext x; exact (vR_BG x).symm

/-- **The step to the next `ε`-number**, raised to the gate of the new base. -/
theorem vsGood_succ {e : Ordinal.{0}} (he : InE e) (hBe : tfBG ≤ e) (h : VsGood e) : VsGood (eN e) := by
  obtain ⟨M, hE, hEg, hV, hR, hG, hBB, hDD⟩ := h
  subst hE
  have hω : ω ≤ M.Eg := hEg ▸ le_max_left _ _
  have hQ : yrQE M.E ≤ M.Eg := hEg ▸ le_max_right _ _
  have hGe : gcG 0 ≤ M.E := va_G_le_BG.trans hBe
  set g := max ω (yrQE (eN M.E)) with hgdef
  have hle : M.Eg ≤ g := hEg ▸ max_le (le_max_left _ _) (vs_QE_eN he hBe)
  have hEg' : (M.step.raise g).Eg = g := by
    rw [ZmDS.raise_Eg, ZmDS.step_Eg]
    exact max_eq_right hle
  refine ⟨M.step.raise g, rfl, hEg', fun x hx hx1 hgx => ?_, fun c hc x hx hx1 hgc => ?_, fun c hc hc0 => ?_,
    ?_, ?_⟩
  · have hgx' : M.Eg < x := hle.trans_lt (hEg' ▸ hgx)
    show eN (M.V x) = _
    rw [hV x hx hx1 hgx']
    exact vs_eN M hω hQ hV hR hG hx hx1 hgx'
  · show M.sR c x = vR c x
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
    rw [← max_assoc, max_eq_left hle]
  · show M.B = vaFB (eN M.E)
    rw [hBB, vs_FB_eN hBe]
  · show M.Dv = vR (vaFB (eN M.E))
    rw [hDD, vs_FB_eN hBe]

end Googology.Trans.PoR.InaccPsi.R2.Va
