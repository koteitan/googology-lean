import Googology.Trans.PoR.InaccPsi.R2.QcCl
import Googology.Trans.PoR.InaccPsi.R2.VaStep

/-!
# QcStp: DIGIT SYSTEMS FROM `X` ON — THE STEP TO THE NEXT `ε`-NUMBER

`QsGood E`: a digit system `Qc.QDS` at the `ε`-number base `E ∈ [B_Γ, B₂)` read by `vQ` with the gates
`max Eg (qcG c)`, base reading `qcA E`, over the segment base `vaFB E` read `vQ (vaFB E)` (as `Va.VsGood`).  Below `X`
it is `Va.VsGood` (`qsGood_of_vs`).  The step `E ↦ ε_{E+1}` (`QDS.step` raised to the gate of the new base) keeps it
from `X` on (`qsGood_succ`): at the segment base `E = F` the reading `ϑˣ(Ω₁·(Ω₁+λ(x)) + K(x))` is a closed point
(`Qc.qc_fix_cl`), so `ε_{V(x)+1} = ϑˣ(Ω₁ + V(x))`; at an atom `Γ(j)` past `F` the index reads
`F(x) + (j − (F+1))(x)`.

* `qc_eN_lt_B`, `qcA_psi'`, `qc_QE_eN` (**the base gate does not drop at the next `ε`-number**), `qc_eN`
  (**`ε_{qcA(E)(x)+1} = qcA(ε_{E+1})(x)`**);
* `QsGood`, `qsGood_of_vs` (**below `X`**), `qsGood_succ`.

No new axiom.  New definition: `QsGood`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Yw
  Googology.Trans.PoR.InaccPsi.R2.Yh Googology.Trans.PoR.InaccPsi.R2.Va Googology.Trans.PoR.InaccPsi.R2.Tl
  Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Yr
  Googology.Trans.PoR.InaccPsi.R2.Zm Googology.Trans.PoR.InaccPsi.R2.Tf Googology.Trans.PoR.InaccPsi.R2.Gk
  Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gn Googology.Trans.PoR.InaccPsi.R2.Gg

theorem qc_eN_lt_B {e : Ordinal.{0}} (h : e < ucB) : eN e < ucB :=
  lt_of_le_of_ne (qc_eN_le_B h) fun h' => zm_eN_nfix e (by rw [h']; exact ucB_SC.veblen_right (gg_one_lt_of_SC ucB_SC))

/-- **A non-atom `ε`-number code `yhPsi α η ∈ [X, B₂)` reads `ϑˣ(Ω₁·α(x) + η(x))`.** -/
theorem qcA_psi' {α η : Ordinal.{0}} (hα : 1 ≤ α) (hGe : gcG 0 < yhPsi α η) (hX : tlX ≤ yhPsi α η)
    (hB : yhPsi α η < ucB) (x : Ordinal.{0}) : qcA (yhPsi α η) x = glA (vQ α x) (vQ η x) x := by
  obtain ⟨h1, h2⟩ := yhData_eq hα hGe
  rw [← vQ_base (yhPsi_E hα η) hX hB, vQ_nonAt (yhPsi_E hα η) (yhPsi_notAt hα) hX hB, h1, h2]

/-- **The base gate does not drop at the next `ε`-number.** -/
theorem qc_QE_eN {e : Ordinal.{0}} (he : InE e) (hX : tlX ≤ e) (hB : e < ucB) : qcQE e ≤ max ω (qcQE (eN e)) := by
  have hBe : tfBG ≤ e := tl_BG_lt_X.le.trans hX
  have hGe' : gcG 0 ≤ e := va_G_le_BG.trans hBe
  have hNB : eN e < ucB := qc_eN_lt_B hB
  have hXN : tlX ≤ eN e := hX.trans (lt_eN e).le
  rcases vs_eN_code he hBe with ⟨hfix, hN⟩ | ⟨hnA, hk, hN⟩
  · have h1 : qcQE (eN e) = max (qcQ 1) (qcQ e) := by
      have hG : gcG 0 < yhPsi 1 e := hN ▸ va_G_lt_eN hGe'
      obtain ⟨d1, d2⟩ := yhData_eq le_rfl hG
      rw [hN, qcQE_psi (hN ▸ hXN) (hN ▸ hNB) (yhPsi_notAt le_rfl), d1, d2]
    rw [h1, qcQ_one, max_eq_right zero_le]
    have h2 : qcQ e = qcQE e := by
      unfold qcQ; rw [if_neg (not_lt.2 (omega0_le_of_isSuccLimit (ev_isSuccLimit_of_inE he))), qcG_base he hX hB]
    rw [h2]; exact le_max_right _ _
  · have h1 : qcQE (eN e) = max (qcQ 1) (qcQ (yhI e + 1)) := by
      have hG : gcG 0 < yhPsi 1 (yhI e + 1) := hN ▸ va_G_lt_eN hGe'
      obtain ⟨d1, d2⟩ := yhData_eq le_rfl hG
      rw [hN, qcQE_psi (hN ▸ hXN) (hN ▸ hNB) (yhPsi_notAt le_rfl), d1, d2]
    rw [h1, qcQ_one, max_eq_right zero_le, qcQE_psi hX hB hnA, hk, qcQ_one, max_eq_right zero_le,
      ← qc_maxQ le_rfl]
    exact (qcQ_le _).trans ((qcG_le_succ _).trans (le_max_right _ _))

/-! ## The next base reading -/

section ENext

variable (M : QDS) (hω : ω ≤ M.Eg) (hQ : qcQE M.E ≤ M.Eg) (hXE : tlX ≤ M.E)
  (hV : ∀ x, InE x → x < Om1 → M.Eg < x → M.V x = qcA M.E x)
  (hR : ∀ c, c < M.E → ∀ x, InE x → x < Om1 → M.G c < x → M.R c x = vQ c x)
  (hG : ∀ c, c < M.E → c ≠ 0 → M.G c = max M.Eg (qcG c))

include hω hQ hXE hV hR hG in
/-- **`ε_{qcA(E)(x)+1} = qcA(ε_{E+1})(x)`** for a system at an `ε`-number base `E ∈ [X, B₂)`. -/
theorem qc_eN {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hgx : M.Eg < x) :
    eN (qcA M.E x) = qcA (eN M.E) x := by
  have hE := M.E_E
  have hBE : tfBG ≤ M.E := tl_BG_lt_X.le.trans hXE
  have hGe' : gcG 0 ≤ M.E := va_G_le_BG.trans hBE
  have hOE : Om1 < M.E := tfBG_gt.trans_le hBE
  have hEB : M.E < ucB := M.E_X
  have hNB : eN M.E < ucB := qc_eN_lt_B hEB
  have hXN : tlX ≤ eN M.E := hXE.trans (lt_eN _).le
  obtain ⟨hVT, -, -, -⟩ := M.V_T x hx hx1 hgx
  have hV1 : M.V x < Om1 := M.V_lt x hx hx1 hgx
  have hωx : ω < x := omega0_lt_inE hx
  have hGx : ∀ c, c < M.E → qcG c < x → M.G c < x := fun c hc hgc => by
    rcases eq_or_ne c 0 with rfl | h0
    · rw [M.G0]; exact hx.pos
    · rw [hG c hc h0]; exact max_lt hgx hgc
  -- the readings of the codes below `E` with gates below `x` are in `Tˣ ∩ Ω₁`
  have hcode : ∀ c, c < M.E → qcG c < x → vQ c x ∈ Tset x ∧ vQ c x < Om1 := by
    intro c hc hgc
    have hGc := hGx c hc hgc
    rw [← hR c hc x hx hx1 hGc]
    have hlt := M.lt c x hx hx1 hc hGc
    exact ⟨vz_T_down hx hx1 hVT hV1 hlt.le, hlt.trans hV1⟩
  have hmono : ∀ b c, b < c → c < M.E → qcG b < x → qcG c < x → vQ b x < vQ c x := by
    intro b c hbc hc hgb hgc
    have hb := hbc.trans hc
    rw [← hR b hb x hx hx1 (hGx b hb hgb), ← hR c hc x hx hx1 (hGx c hc hgc)]
    exact M.mono b c x hx hx1 hbc hc (hGx b hb hgb) (hGx c hc hgc)
  have hQx : max ω (qcQE M.E) < x := (max_le hω hQ).trans_lt hgx
  rcases vs_atom_cases hBE with hB | ⟨hA, hjB, hjE⟩ | hnA
  · -- the segment base: a fixed point of `Γ`, read at a closed point
    have hfixG : gamma M.E = M.E := by rw [hB]; exact vs_FB_fix hBE
    have hA : YhAt M.E := ⟨by rw [← hfixG]; exact Lq.lq_gamma_SC _, hOE⟩
    have hi : ¬ yhJ M.E < M.E := by
      have h := yhJ_gcG M.E; rw [vs_gcG_fix hfixG hOE] at h; rw [h]; exact lt_irrefl _
    have hfixE : veblen 1 M.E = M.E := zm_fix_of_gamma hfixG
    have hN : eN M.E = yhPsi 1 M.E := (va_psi1_fix hfixE hOE).symm
    rw [hN, qcA_psi' le_rfl (hN ▸ va_G_lt_eN hGe') (hN ▸ hXN) (hN ▸ hNB), vQ_one, vQ_base hE hXE hEB]
    have hcl := qc_fix_cl hx hx1 hA hi hXE hEB hQx hcode hmono
    have hVA : M.V x = qcA M.E x := hV x hx hx1 hgx
    have hxV : x < qcA M.E x := by
      rw [← hVA]; exact (M.Dv_T x hx hx1 hgx).2.2.1.trans_le (M.V_T x hx hx1 hgx).2.2.1
    rw [← hVA] at hcl hxV ⊢
    exact vs_eN_cl hx hx1 hVT hV1 hxV hcl
  · -- an atom `Γ(j)` past the segment base: the index reading is in `Tˣ ∩ Ω₁`
    have hfixE : veblen 1 M.E = M.E := hA.1.veblen_right (gg_one_lt_of_SC hA.1)
    have hN : eN M.E = yhPsi 1 M.E := (va_psi1_fix hfixE hOE).symm
    have hAq : qcA M.E x = gq (qcI (yhJ M.E) x) x := by
      unfold qcA; rw [if_pos ⟨hXE, hEB⟩, if_pos hA, if_pos hjE]
    rw [hN, qcA_psi' le_rfl (hN ▸ va_G_lt_eN hGe') (hN ▸ hXN) (hN ▸ hNB), vQ_one, vQ_base hE hXE hEB, hAq,
      qc_vI hBE hjB hjE.le]
    have hFE : InE (vaFB M.E) := vs_FB_E hBE
    have hXF : tlX ≤ vaFB M.E := qc_FB_ge_X hXE
    have hQj : max ω (qcG (yhJ M.E)) = max ω (qcQE M.E) := by
      rw [qc_maxQ le_rfl, qcQE_atom hXE hEB hA hjE]
    have hgF : qcG (vaFB M.E) ≤ max ω (qcQE M.E) := by
      have h := qc_FB_gate M.E hXE hEB; rwa [qcG_base hE hXE hEB] at h
    have hgo : qcG (yhJ M.E - (vaFB M.E + 1)) ≤ max ω (qcQE M.E) :=
      (qc_off_gate hFE hXF (hjE.trans hEB) hjB).trans hQj.le
    obtain ⟨hFT, hF1⟩ := hcode _ (hjB.trans hjE) (hgF.trans_lt hQx)
    obtain ⟨hoT, ho1⟩ := hcode _ ((Ordinal.sub_le_self _ _).trans_lt hjE) (hgo.trans_lt hQx)
    exact va_eN_gq hx hx1 (vzT_add hx hx1 hFT hoT) ((inE_indec Gl.gl_Om1_E).add_lt hF1 ho1)
  have hGe : gcG 0 < M.E := lt_of_le_of_ne hGe' fun h => hnA (h ▸ yhAt_gcG 0)
  obtain ⟨hk1, hkE, hiE, hpsi⟩ := va_data hE hGe hnA
  have hQE : qcQE M.E = max (qcQ (yhK M.E)) (qcQ (yhI M.E)) := qcQE_psi hXE hEB hnA
  have hgk : qcG (yhK M.E) < x := qcG_of_Q hωx (((le_max_left _ _).trans (hQE ▸ hQ)).trans_lt hgx)
  have hgi : qcG (yhI M.E) < x := qcG_of_Q hωx (((le_max_right _ _).trans (hQE ▸ hQ)).trans_lt hgx)
  obtain ⟨hkT, hk1'⟩ := hcode _ hkE hgk
  obtain ⟨hiT, hi1⟩ := hcode _ hiE hgi
  have hvk1 : 1 ≤ vQ (yhK M.E) x := by
    rcases hk1.lt_or_eq with h | h
    · have h1g : qcG 1 < x := by
        have := qcG_nat 1; rw [Nat.cast_one] at this; rw [this]; exact lu_one_lt_E hx
      have hm := hmono 1 (yhK M.E) h hkE h1g hgk
      rw [vQ_one] at hm; exact hm.le
    · rw [← h, vQ_one]
  have hA : qcA M.E x = glA (vQ (yhK M.E) x) (vQ (yhI M.E) x) x := by
    unfold qcA; rw [if_pos ⟨hXE, hEB⟩, if_neg hnA]
  rcases vs_eN_code hE hBE with ⟨hfix, hN⟩ | ⟨-, hk, hN⟩
  · -- a fixed point of `φ(1, ·)`: the level is at least `2`
    have hk2 : 2 ≤ yhK M.E := by
      by_contra hc
      push Not at hc
      have hk1e : yhK M.E = 1 := le_antisymm (Order.lt_add_one_iff.1 (by rw [one_add_one_eq_two]; exact hc)) hk1
      have hnP := yhPsi_notP (yhK M.E) (yhI M.E)
      rw [hpsi, hk1e] at hnP
      exact hnP (luP_succ.2 hfix)
    have e2 : ((2 : ℕ) : Ordinal.{0}) = 2 := by norm_num
    have h2X : (2 : Ordinal.{0}) < tlX := by
      have := (natCast_lt_omega0 2).trans (omega0_lt_inE qc_X_E); rwa [e2] at this
    have hvR2 : vQ 2 x = 2 := by
      rw [vQ_low h2X]
      have := vR_nat 2 x; rwa [e2] at this
    have hvk2 : 2 ≤ vQ (yhK M.E) x := by
      rcases hk2.lt_or_eq with h | h
      · have hG2 : qcG 2 < x := by
          have := qcG_nat 2; rw [e2] at this; rw [this]
          exact (show (2 : Ordinal.{0}) < ω by rw [← e2]; exact natCast_lt_omega0 2).trans hωx
        have hm := hmono 2 (yhK M.E) h hkE hG2 hgk
        rw [hvR2] at hm; exact hm.le
      · rw [← h, hvR2]
    rw [hN, qcA_psi' le_rfl (hN ▸ va_G_lt_eN hGe') (hN ▸ hXN) (hN ▸ hNB), vQ_one, vQ_base hE hXE hEB, hA]
    exact glA_eN_two hx hx1 hvk2 hkT hk1' hiT hi1
  · rw [hN, qcA_psi' le_rfl (hN ▸ va_G_lt_eN hGe') (hN ▸ hXN) (hN ▸ hNB), vQ_one, vQ_succ, hA, hk, vQ_one]
    exact glA_eN_one hx hx1 hiT hi1

end ENext

/-! ## The systems -/

/-- **A digit system at the `ε`-number base `E ∈ [B_Γ, B₂)` read by `vQ`, over the segment base `vaFB E` read
`vQ (vaFB E)`.** -/
def QsGood (E : Ordinal.{0}) : Prop :=
  ∃ M : QDS, M.E = E ∧ M.Eg = max ω (qcQE E) ∧
    (∀ x, InE x → x < Om1 → M.Eg < x → M.V x = qcA E x) ∧
    (∀ c, c < E → ∀ x, InE x → x < Om1 → M.G c < x → M.R c x = vQ c x) ∧
    (∀ c, c < E → c ≠ 0 → M.G c = max M.Eg (qcG c)) ∧ M.B = vaFB E ∧ M.Dv = vQ (vaFB E)

/-- **Below `X` it is `Va.VsGood`.** -/
theorem qsGood_of_vs {E : Ordinal.{0}} (hBE : tfBG ≤ E) (hEX : E < tlX) (h : VsGood E) : QsGood E := by
  obtain ⟨M, hME, hEg, hV, hR, hG, hB, hD⟩ := h
  have hFX : vaFB E < tlX := (vs_FB_le hBE).trans_lt hEX
  refine ⟨M.toQ, hME, by rw [qcQE_low hEX]; exact hEg, fun x hx hx1 hg => ?_, fun c hc x hx hx1 hg => ?_,
    fun c hc hc0 => ?_, hB, ?_⟩
  · show M.V x = qcA E x; rw [qcA_low hEX]; exact hV x hx hx1 hg
  · show M.R c x = vQ c x; rw [vQ_low (hc.trans hEX)]; exact hR c hc x hx hx1 hg
  · show M.G c = max M.Eg (qcG c); rw [qcG_low (hc.trans hEX)]; exact hG c hc hc0
  · show M.Dv = vQ (vaFB E); rw [hD]; funext x; exact (vQ_low hFX x).symm

/-- **The step to the next `ε`-number from `X` on**, raised to the gate of the new base. -/
theorem qsGood_succ {e : Ordinal.{0}} (he : InE e) (hXe : tlX ≤ e) (h : QsGood e) : QsGood (eN e) := by
  obtain ⟨M, hE, hEg, hV, hR, hG, hBB, hDD⟩ := h
  subst hE
  have hBe : tfBG ≤ M.E := tl_BG_lt_X.le.trans hXe
  have hω : ω ≤ M.Eg := hEg ▸ le_max_left _ _
  have hQ : qcQE M.E ≤ M.Eg := hEg ▸ le_max_right _ _
  set g := max ω (qcQE (eN M.E)) with hgdef
  have hle : M.Eg ≤ g := hEg ▸ max_le (le_max_left _ _) (qc_QE_eN he hXe M.E_X)
  have hEg' : (M.step.raise g).Eg = g := by
    rw [QDS.raise_Eg, QDS.step_Eg]
    exact max_eq_right hle
  refine ⟨M.step.raise g, rfl, hEg', fun x hx hx1 hgx => ?_, fun c hc x hx hx1 hgc => ?_, fun c hc hc0 => ?_,
    ?_, ?_⟩
  · have hgx' : M.Eg < x := hle.trans_lt (hEg' ▸ hgx)
    show eN (M.V x) = _
    rw [hV x hx hx1 hgx']
    exact qc_eN M hω hQ hXe hV hR hG hx hx1 hgx'
  · show M.sR c x = vQ c x
    rcases eq_or_ne c 0 with rfl | hc0
    · rw [M.sR_zero, vQ_zero]
    have hgc' : M.sG c < x := by
      have h1 := hgc
      rw [QDS.raise_G _ _ hc0] at h1
      exact (le_max_right _ _).trans_lt h1
    have hgx : M.Eg < x := (M.sG_Eg c hc0).trans_lt hgc'
    exact qc_sR M hXe hV hR c hc x hx hx1 hgx hgc'
  · rw [QDS.raise_G _ _ hc0, hEg']
    show max g (M.sG c) = max g (qcG c)
    rw [qc_sG M hω hQ hXe hG c hc hc0]
    rw [← max_assoc, max_eq_left hle]
  · show M.B = vaFB (eN M.E)
    rw [hBB, vs_FB_eN hBe]
  · show M.Dv = vQ (vaFB (eN M.E))
    rw [hDD, vs_FB_eN hBe]

end Googology.Trans.PoR.InaccPsi.R2.Qc
