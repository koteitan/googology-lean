import Googology.Trans.PoR.InaccPsi.R2.QdLimS
import Googology.Trans.PoR.InaccPsi.R2.QdGate

/-!
# QdCuS: THE UNION AT A LIMIT `ε`-NUMBER BASE BELOW `B₃` OVER ITS SEGMENT BASE

As `Qc.QcCuS` with `vD`, `qdA`, `qdGt`, the codes of `Qd.QdCl` and the systems `Qd.QdGood`: the members
(`Qd.qd_mem`) give one digit system `Qd.QdDS` with base reading `qdA E`, readings `vD`, gates `max Eg (qdGt c)`,
segment base `vaFB E` read `vD (vaFB E)`, every reading under the bound `Qc.YBd`.  The data at the top (`QdTop`) come
from `Qd.QdLimS` at a non-atom (`qdTopNA`); the atoms come in the next files.  A code has its gate below `Z` by
`Qd.qd_gate`.

* `qd_cl_y0`, `qd_cl_lam`, `qd_cl_psi` (the codes of `QdCl` under `glLam` and `yhPsi`);
* `qd_cl_code` (**a code below `E` with gate below `Z` is a code over `Z`**), `qd_memV`, `qd_Dpi`, `qd_ncE`;
* `QdTop`, `qdTopNA`, `qdCU` (**THE UNION**), `qdGood_lim`.

No new axiom.  New definitions: `QdTop`, `qdTopNA S`, `qdCU S`.
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
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Xk Googology.Trans.PoR.InaccPsi.R2.Rh
  Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Va
  Googology.Trans.PoR.InaccPsi.R2.Uc
  Googology.Trans.PoR.InaccPsi.R2.Qc

/-! ## Codes -/

/-- `y₀(β)` is a code over every `Z > 0`. -/
theorem qd_cl_y0 {Z : Ordinal.{0}} (hZ : 0 < Z) (β : Ordinal.{0}) : QdCl Z (glY0 β) := by
  unfold glY0
  split_ifs
  · exact QdCl.add QdCl.om (QdCl.one hZ)
  · exact QdCl.one hZ
  · exact QdCl.zero hZ

theorem qd_cl_lam {Z : Ordinal.{0}} (hZ : 0 < Z) (α : Ordinal.{0}) {η : Ordinal.{0}} (h : QdCl Z η) :
    QdCl Z (glLam α η) := by
  by_cases hF : glFw α η
  · rw [glLam_of hF]; exact QdCl.add h (QdCl.one hZ)
  · rw [glLam_of_not hF]; exact QdCl.add (qd_cl_y0 hZ α) h

theorem qd_cl_psi {Z : Ordinal.{0}} (hZ : 0 < Z) {α η : Ordinal.{0}} (hα : QdCl Z α) (hη : QdCl Z η) :
    QdCl Z (yhPsi α η) := by
  unfold yhPsi
  split_ifs
  · exact QdCl.phi hα (qd_cl_lam hZ α (QdCl.add (QdCl.one hZ) hη))
  · exact QdCl.phi hα (qd_cl_lam hZ α hη)


section Union

variable (S : InaccSeq.{0}) {E : Ordinal.{0}} (hE : InE E) (hBE : tfBG < E) (hEB : E < qdB)
  (hlim : ∀ e, InE e → e < E → eN e < E) (hIH : ∀ e, InE e → tfBG ≤ e → e < E → QdGood e)

include S hE hBE hEB hlim hIH

/-- A code below `E` with gate below a strongly critical `Z` above the base gate is a code over `Z`. -/
theorem qd_cl_code {Z : Ordinal.{0}} (hZ : SC Z) {c : Ordinal.{0}} (hc : c < E) (hg : qdGt c < Z) : QdCl Z c := by
  have hωZ : ω < Z := omega0_lt_inE (Low.opow_eq_self_of_SC hZ)
  obtain ⟨e, M, -, -, -, -, -, hcM, -, -, -, hEg, -, -, hG, -, -⟩ := qd_mem S hEB hlim hIH hBE hc
  exact M.cl c Z hZ hcM (qd_memG hωZ hEg hg hG hcM hg)

/-- **A member whose base reading is below `qdA E`** at every base above the gates. -/
theorem qd_memV (htop : ∀ y, InE y → y < Om1 → max ω (qdQEt E) < y → ∀ c, c < E → qdGt c < y →
      vD c y < qdA E y) {c : Ordinal.{0}} (hc : c < E) :
    ∃ M : QdDS, c < M.E ∧ M.E < E ∧ M.Eg ≤ max ω (qdGt c) ∧
      (∀ y, InE y → y < Om1 → max ω (qdQEt E) < y → qdGt c < y → M.V y ≤ qdA E y) ∧
      (∀ c', c' < M.E → ∀ y, InE y → y < Om1 → M.G c' < y → M.R c' y = vD c' y) ∧
      (∀ c', c' < M.E → c' ≠ 0 → M.G c' = max M.Eg (qdGt c')) := by
  obtain ⟨e, M, he, heB, -, hemax, hME, hcM, hMlt, -, hEgeq, hEg, hV, hR, hG, -, -⟩ := qd_mem S hEB hlim hIH hBE hc
  refine ⟨M, hcM, hMlt, hEg, fun y hy hy1 hgy hg => ?_, hR, hG⟩
  have hωy : ω < y := omega0_lt_inE hy
  have hyl : IsSuccLimit y := ev_isSuccLimit_of_inE hy
  have hgM : M.Eg < y := hEg.trans_lt (max_lt hωy hg)
  have hMEE : InE M.E := by rw [hME]; exact eN_E e
  have hGME : gcG 0 ≤ M.E := (va_G_le_BG.trans heB).trans (hME ▸ (lt_eN e).le)
  have hgME : qdGt M.E < y := by
    rw [qdGt_base' hMEE hGME (hMlt.trans hEB), hME]
    exact qd_QE_eN_lt he heB ((lt_eN e).trans (hME ▸ hMlt) |>.trans hEB) hyl hωy
      ((le_max_right _ _).trans_lt (hEgeq ▸ hgM))
  have hlt := htop y hy hy1 hgy M.E hMlt hgME
  rw [vD_base' hMEE hGME (hMlt.trans hEB), ← (hV y hy hy1 hgM).2] at hlt
  exact hlt.le

/-- **The segment base is exact**, from the system at it. -/
theorem qd_Dpi (hFE : vaFB E < E) {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) (hgσ : max ω (qdQEt E) < σ) :
    vD (vaFB E) ρ ∈ TB ρ σ ∧ R2.pi σ ρ (vD (vaFB E) ρ) = vD (vaFB E) σ := by
  have hωσ : ω < σ := omega0_lt_inE hB.1
  have hgF : qdGt (vaFB E) < σ :=
    (qd_FB_gate' hBE.le hEB).trans_lt (by rw [qdGt_base' hE (va_G_le_BG.trans hBE.le) hEB]; exact hgσ)
  have hFF : vaFB (vaFB E) = vaFB E := vs_FB_self (vs_FB_fix hBE.le) (vs_FB_gt hBE.le)
  have hgu : guE (vaFB E) = vaFB E := le_antisymm (gl_E_le (yh_gfE_le (va_G_le_BG.trans (vs_FB_ge hBE.le))))
    (gl_E_max (vs_FB_E hBE.le) (vs_FB_gt hBE.le) le_rfl)
  obtain ⟨e, M, -, -, he, -, -, -, -, -, -, hEg, -, -, -, -, hD⟩ := qd_mem S hEB hlim hIH hBE hFE
  have heF : e = vaFB E := (he (vs_FB_ge hBE.le)).trans hgu
  rw [heF, hFF] at hD
  have h := M.Dv_pi σ ρ hB (hEg.trans_lt (max_lt hωσ hgF))
  rwa [hD] at h

/-- **The index readings are not closed**: `F(x) + c(x)` for a limit code `c < E` past the segment base `F < E`
(below `F` by `Va.vs_nc_lt`, from the member at the bracket of `c` above `F`). -/
theorem qd_ncE (hFE : vaFB E < E) : ∀ c x, InE x → x < Om1 → IsSuccLimit c → c < E →
    max (max ω (qdQEt E)) (qdGt c) < x →
    ∃ σ, σ ∈ Tset x ∧ σ < Om1 ∧ σ < vD (vaFB E) x + vD c x ∧ vD (vaFB E) x + vD c x < gq σ x := by
  intro c x hx hx1 hl hc hg
  have hgx : max ω (qdQEt E) < x := (le_max_left _ _).trans_lt hg
  have hgc : qdGt c < x := (le_max_right _ _).trans_lt hg
  have hc0 : c ≠ 0 := hl.bot_lt.ne'
  have hgF : qdGt (vaFB E) < x :=
    (qd_FB_gate' hBE.le hEB).trans_lt (by rw [qdGt_base' hE (va_G_le_BG.trans hBE.le) hEB]; exact hgx)
  by_cases hcF : c < vaFB E
  · obtain ⟨hDT, -, -, hDX⟩ := qd_xF S hE hBE hEB hlim hIH hx hx1 hFE hgx
    have h0 : vD 0 x < vD c x := qd_mono S hE hBE hEB hlim hIH hx hx1 (pos_iff_ne_zero.2 hc0) hc
      (by rw [qdGt_zero]; exact hx.pos) hgc
    rw [vD_zero] at h0
    exact vs_nc_lt hx hx1 hDT (yBd_lt hx hx1 hDX) h0
      (qd_mono S hE hBE hEB hlim hIH hx hx1 hcF hFE hgc hgF)
  · have hcF' : vaFB E ≤ c := not_lt.1 hcF
    have hGc : gcG 0 ≤ c := va_G_le_BG.trans ((vs_FB_ge hBE.le).trans hcF')
    obtain ⟨e, M, -, -, he, -, -, hcM, -, -, -, hEg, -, hR, hG, -, hD⟩ := qd_mem S hEB hlim hIH hBE hc
    have heF : vaFB e = vaFB E := by
      rw [he ((vs_FB_ge hBE.le).trans hcF')]
      exact vs_FB_of_le hBE.le (gl_E_max (vs_FB_E hBE.le) (vs_FB_gt hBE.le) hcF')
        ((gl_E_le (yh_gfE_le hGc)).trans hc.le)
    have hGcM := qd_memG (omega0_lt_inE hx) hEg hgc hG hcM hgc
    have h := M.nc c x hx hx1 hl hcM hGcM
    rw [hD, heF, hR c hcM x hx hx1 hGcM] at h
    exact h

/-- **The data of the top `E`** for the union: the base reading `qdA E` with its facts, the order and cofinality of
the readings below it. -/
structure QdTop (E : Ordinal.{0}) where
  Ei : Ordinal.{0}
  W : Ordinal.{0} → Ordinal.{0}
  E_eq : veblen 1 Ei = E
  Ei_cl : ∀ Z, SC Z → max ω (qdQEt E) < Z → QdCl Z Ei
  V_T : ∀ x, InE x → x < Om1 → max ω (qdQEt E) < x →
    qdA E x ∈ Tset x ∧ InE (qdA E x) ∧ vD (vaFB E) x ≤ qdA E x ∧ YBd x (qdA E x)
  Vq : ∀ x, InE x → x < Om1 → max ω (qdQEt E) < x →
    ∃ σ, σ ∈ Tset x ∧ σ < Om1 ∧ σ < vD (vaFB E) x + qdA E x ∧ qdA E x < gq σ x
  W_T : ∀ x, InE x → x < Om1 → max ω (qdQEt E) < x → W x ∈ Tset x ∧ W x < Om1 ∧ eN (qdA E x) = glA 1 (W x) x
  V_pi : ∀ σ ρ, Bases σ ρ → max ω (qdQEt E) < σ → qdA E ρ ∈ TB ρ σ ∧ R2.pi σ ρ (qdA E ρ) = qdA E σ
  W_pi : ∀ σ ρ, Bases σ ρ → max ω (qdQEt E) < σ → W ρ ∈ TB ρ σ ∧ R2.pi σ ρ (W ρ) = W σ
  lt : ∀ x, InE x → x < Om1 → max ω (qdQEt E) < x → ∀ c, c < E → qdGt c < x → vD c x < qdA E x
  top : ∀ x, InE x → x < Om1 → max ω (qdQEt E) < x → ∀ ν, ν < qdA E x → ∃ b, b < E ∧ qdGt b < x ∧ ν ≤ vD b x
  B_cl : ∀ Z, SC Z → max ω (qdQEt E) < Z → QdCl Z (vaFB E)
  D_T : ∀ x, InE x → x < Om1 → max ω (qdQEt E) < x →
    vD (vaFB E) x ∈ Tset x ∧ InE (vD (vaFB E) x) ∧ x < vD (vaFB E) x ∧ YBd x (vD (vaFB E) x)
  D_pi : ∀ σ ρ, Bases σ ρ → max ω (qdQEt E) < σ →
    vD (vaFB E) ρ ∈ TB ρ σ ∧ R2.pi σ ρ (vD (vaFB E) ρ) = vD (vaFB E) σ
  nc : ∀ c x, InE x → x < Om1 → IsSuccLimit c → c < E → max (max ω (qdQEt E)) (qdGt c) < x →
    ∃ σ, σ ∈ Tset x ∧ σ < Om1 ∧ σ < vD (vaFB E) x + vD c x ∧ vD (vaFB E) x + vD c x < gq σ x

open Classical in
/-- **The top data at a non-atom `E`.** -/
noncomputable def qdTopNA (hFE : vaFB E < E) (hnA : ¬ YhAt E) : QdTop E where
  Ei := if yhK E = 1 then glLam 1 (yhI E) else E
  W := fun x => if yhK E = 1 then vD (yhI E) x + 1 else qdA E x
  E_eq := by
    obtain ⟨-, -, hk1, -, -, hpsi⟩ := qd_dat S hE hBE hFE hnA
    split_ifs with h1
    · have h := hpsi
      rw [h1, yhPsi_ne va_one_notAt] at h
      exact h
    · have hk2 : 1 < yhK E := lt_of_le_of_ne hk1 (Ne.symm h1)
      have hPe : LuP (yhK E) E := by have := yhPsi_P (yhK E) (yhI E); rwa [hpsi] at this
      exact luP_succ.1 (luP_mono le_add_self (add_one_le_of_lt hk2) hPe)
  Ei_cl := fun Z hZ hgZ => by
    obtain ⟨hnA, -, hk1, hkE, hiE, hpsi⟩ := qd_dat S hE hBE hFE hnA
    have hωZ : ω < Z := omega0_lt_inE (Low.opow_eq_self_of_SC hZ)
    have hQ := qdQEt_psi' hE (va_G_le_BG.trans_lt hBE) hEB hnA
    have hQle : max (qdQt (yhK E)) (qdQt (yhI E)) < Z := by rw [← hQ]; exact (le_max_right _ _).trans_lt hgZ
    have hk := qd_cl_code S hE hBE hEB hlim hIH hZ hkE (qdGt_of_Q hωZ ((le_max_left _ _).trans_lt hQle))
    have hi := qd_cl_code S hE hBE hEB hlim hIH hZ hiE (qdGt_of_Q hωZ ((le_max_right _ _).trans_lt hQle))
    split_ifs with h1
    · exact qd_cl_lam hZ.1 1 hi
    · have h := qd_cl_psi hZ.1 hk hi; rwa [hpsi] at h
  V_T := fun x hx hx1 hgx => by
    obtain ⟨-, -, -, hkE, hiE, -⟩ := qd_dat S hE hBE hFE hnA
    obtain ⟨hgk, hgi, hv1, hkT, hk1', hiT, hi1, hA⟩ := qd_datx S hE hBE hEB hlim hIH hx hx1 hFE hnA hgx
    obtain ⟨-, -, hkX⟩ := qd_T S hE hBE hEB hlim hIH hx hx1 hkE hgk
    obtain ⟨-, -, hiX⟩ := qd_T S hE hBE hEB hlim hIH hx hx1 hiE hgi
    obtain ⟨hVT, -, -, hVE, -, -⟩ := glA_facts hx hx1 hv1 hkT hk1' hiT hi1
    have hmT : max (vD (yhK E) x) (vD (yhI E) x) ∈ Tset x := by
      rcases le_total (vD (yhK E) x) (vD (yhI E) x) with h | h
      · rw [max_eq_right h]; exact hiT
      · rw [max_eq_left h]; exact hkT
    have hm1 : max (vD (yhK E) x) (vD (yhI E) x) < Om1 := max_lt hk1' hi1
    have hq := gmq_gt hx hx1 hmT hm1
    have hlt := xkA_lt hx hx1 hmT hm1 ((le_max_left _ _).trans_lt hq) ((le_max_right _ _).trans_lt hq)
    rw [← hA] at hVT hVE hlt
    have hmX : YBd x (max (vD (yhK E) x) (vD (yhI E) x)) := by
      rcases le_total (vD (yhK E) x) (vD (yhI E) x) with h | h
      · rw [max_eq_right h]; exact hiX
      · rw [max_eq_left h]; exact hkX
    exact ⟨hVT, hVE, (qd_D_lt S hE hBE hEB hlim hIH hx hx1 hFE hnA hgx).le,
      yBd_mono hlt.le (yBd_gq hx hx1 hmT hmX)⟩
  Vq := fun x hx hx1 hgx => by
    obtain ⟨-, -, hv1, hkT, hk1', hiT, hi1, hA⟩ := qd_datx S hE hBE hEB hlim hIH hx hx1 hFE hnA hgx
    obtain ⟨-, -, -, -, hka, hta⟩ := glA_facts hx hx1 hv1 hkT hk1' hiT hi1
    have hmT : max (vD (yhK E) x) (vD (yhI E) x) ∈ Tset x := by
      rcases le_total (vD (yhK E) x) (vD (yhI E) x) with h | h
      · rw [max_eq_right h]; exact hiT
      · rw [max_eq_left h]; exact hkT
    have hm1 : max (vD (yhK E) x) (vD (yhI E) x) < Om1 := max_lt hk1' hi1
    have hq := gmq_gt hx hx1 hmT hm1
    refine ⟨_, hmT, hm1, ?_, ?_⟩
    · rw [hA]; exact (max_lt hka hta).trans_le le_add_self
    · rw [hA]; exact xkA_lt hx hx1 hmT hm1 ((le_max_left _ _).trans_lt hq) ((le_max_right _ _).trans_lt hq)
  W_T := fun x hx hx1 hgx => by
    obtain ⟨-, -, hk1, hkE, -, -⟩ := qd_dat S hE hBE hFE hnA
    obtain ⟨hgk, -, hv1, hkT, hk1', hiT, hi1, hA⟩ := qd_datx S hE hBE hEB hlim hIH hx hx1 hFE hnA hgx
    show (if yhK E = 1 then vD (yhI E) x + 1 else qdA E x) ∈ Tset x ∧
      (if yhK E = 1 then vD (yhI E) x + 1 else qdA E x) < Om1 ∧
      eN (qdA E x) = glA 1 (if yhK E = 1 then vD (yhI E) x + 1 else qdA E x) x
    split_ifs with h1
    · obtain ⟨hsT, hs1⟩ := gl_T_succ hx hx1 hiT hi1
      refine ⟨hsT, hs1, ?_⟩
      rw [hA, h1, vD_one]; exact glA_eN_one hx hx1 hiT hi1
    · have hk2 : 2 ≤ yhK E := by
        rw [← one_add_one_eq_two]; exact add_one_le_of_lt (lt_of_le_of_ne hk1 (Ne.symm h1))
      have e2 : ((2 : ℕ) : Ordinal.{0}) = 2 := by norm_num
      have hg2 : qdGt 2 < x := by
        have := qdGt_nat 2; rw [e2] at this
        rw [this, ← e2]; exact (natCast_lt_omega0 2).trans (omega0_lt_inE hx)
      have hv2 : 2 ≤ vD (yhK E) x := by
        have h := qd_le_mono S hE hBE hEB hlim hIH hx hx1 hk2 hkE hg2 hgk
        have hv : vD 2 x = 2 := by
          have h2X : (2 : Ordinal.{0}) < ucB := by
            have := (natCast_lt_omega0 2).trans (omega0_lt_inE qd_B2_E); rwa [e2] at this
          have h2T : (2 : Ordinal.{0}) < tlX := by
            have := (natCast_lt_omega0 2).trans (omega0_lt_inE qc_X_E); rwa [e2] at this
          rw [vD_low h2X, vQ_low h2T]; have := vR_nat 2 x; rwa [e2] at this
        rwa [hv] at h
      obtain ⟨hVT, -, hV1, -, -, -⟩ := glA_facts hx hx1 hv1 hkT hk1' hiT hi1
      rw [← hA] at hVT hV1
      refine ⟨hVT, hV1, ?_⟩
      rw [hA]; exact glA_eN_two hx hx1 hv2 hkT hk1' hiT hi1
  V_pi := fun σ ρ hB hgσ => by
    obtain ⟨-, -, -, hkE, hiE, -⟩ := qd_dat S hE hBE hFE hnA
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
    have hgρ := hgσ.trans hB.2.2.1
    obtain ⟨hgk, hgi, -, -, hk1', -, hi1, hA⟩ := qd_datx S hE hBE hEB hlim hIH hB.2.1 hρ1 hFE hnA hgρ
    obtain ⟨hgkσ, hgiσ, -, -, -, -, -, hAσ⟩ := qd_datx S hE hBE hEB hlim hIH hB.1 hσ1 hFE hnA hgσ
    have hex : ∀ c, c < E → qdGt c < σ → vD c ρ ∈ TB ρ σ ∧ R2.pi σ ρ (vD c ρ) = vD c σ := by
      intro c hc hgc
      obtain ⟨M, hcM, -, hEg, -, hR, hG⟩ := qd_memV S hE hBE hEB hlim hIH (qd_ltT S hE hBE hEB hlim hIH hFE hnA) hc
      have hGc := qd_memG (omega0_lt_inE hB.1) hEg hgc hG hcM hgc
      rw [← hR c hcM ρ hB.2.1 hρ1 (hGc.trans hB.2.2.1), ← hR c hcM σ hB.1 hσ1 hGc]
      exact M.ex σ ρ c hB hcM hGc
    obtain ⟨k1, k2⟩ := hex _ hkE hgkσ
    obtain ⟨i1, i2⟩ := hex _ hiE hgiσ
    obtain ⟨a1, a2⟩ := glA_pi hB k1 hk1' i1 hi1
    rw [k2, i2, ← hAσ] at a2
    rw [hA]; exact ⟨a1, a2⟩
  W_pi := fun σ ρ hB hgσ => by
    obtain ⟨-, -, -, hkE, hiE, -⟩ := qd_dat S hE hBE hFE hnA
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
    have hgρ := hgσ.trans hB.2.2.1
    obtain ⟨hgk, hgi, -, -, hk1', -, hi1, hA⟩ := qd_datx S hE hBE hEB hlim hIH hB.2.1 hρ1 hFE hnA hgρ
    obtain ⟨hgkσ, hgiσ, -, -, -, -, -, hAσ⟩ := qd_datx S hE hBE hEB hlim hIH hB.1 hσ1 hFE hnA hgσ
    have hex : ∀ c, c < E → qdGt c < σ → vD c ρ ∈ TB ρ σ ∧ R2.pi σ ρ (vD c ρ) = vD c σ := by
      intro c hc hgc
      obtain ⟨M, hcM, -, hEg, -, hR, hG⟩ := qd_memV S hE hBE hEB hlim hIH (qd_ltT S hE hBE hEB hlim hIH hFE hnA) hc
      have hGc := qd_memG (omega0_lt_inE hB.1) hEg hgc hG hcM hgc
      rw [← hR c hcM ρ hB.2.1 hρ1 (hGc.trans hB.2.2.1), ← hR c hcM σ hB.1 hσ1 hGc]
      exact M.ex σ ρ c hB hcM hGc
    show (if yhK E = 1 then vD (yhI E) ρ + 1 else qdA E ρ) ∈ TB ρ σ ∧
      R2.pi σ ρ (if yhK E = 1 then vD (yhI E) ρ + 1 else qdA E ρ) =
        (if yhK E = 1 then vD (yhI E) σ + 1 else qdA E σ)
    obtain ⟨i1, i2⟩ := hex _ hiE hgiσ
    split_ifs with h1
    · obtain ⟨o1, o2⟩ := one_TB hB
      obtain ⟨s1, s2⟩ := pi_add hB i1 o1
      rw [i2, o2] at s2
      exact ⟨s1, s2⟩
    · obtain ⟨k1, k2⟩ := hex _ hkE hgkσ
      obtain ⟨a1, a2⟩ := glA_pi hB k1 hk1' i1 hi1
      rw [k2, i2, ← hAσ] at a2
      rw [hA]; exact ⟨a1, a2⟩
  lt := fun x hx hx1 hgx c hc hg => qd_lt_top S hE hBE hEB hlim hIH hx hx1 hFE hnA hgx c hc hg
  top := fun x hx hx1 hgx ν hν => qd_top S hE hBE hEB hlim hIH hx hx1 hFE hnA hgx ν hν
  B_cl := fun Z hZ hgZ => by
    have hgF : qdGt (vaFB E) < Z :=
      (qd_FB_gate' hBE.le hEB).trans_lt (by rw [qdGt_base' hE (va_G_le_BG.trans hBE.le) hEB]; exact hgZ)
    exact qd_cl_code S hE hBE hEB hlim hIH hZ hFE hgF
  D_T := fun x hx hx1 hgx => qd_xF S hE hBE hEB hlim hIH hx hx1 hFE hgx
  D_pi := fun σ ρ hB hgσ => qd_Dpi S hE hBE hEB hlim hIH hFE hB hgσ
  nc := fun c x hx hx1 hl hc hg => qd_ncE S hE hBE hEB hlim hIH hFE c x hx hx1 hl hc hg

open Classical in
/-- **THE UNION AT A LIMIT `ε`-NUMBER BASE** from the top data. -/
noncomputable def qdCU (T : QdTop E) : QdDS where
  E := E
  Ei := T.Ei
  V := fun x => if max ω (qdQEt E) < x then qdA E x else 1
  W := T.W
  R := vD
  G := fun c => if c = 0 then 0 else max (max ω (qdQEt E)) (qdGt c)
  Eg := max ω (qdQEt E)
  B := vaFB E
  Dv := vD (vaFB E)
  E_eq := T.E_eq
  BG_le := hBE.le
  B_le := vs_FB_le hBE.le
  BG_B := vs_FB_ge hBE.le
  B_cl := T.B_cl
  Dv_T := T.D_T
  Dv_pi := T.D_pi
  E_X := hEB
  Ei_cl := T.Ei_cl
  nfx := fun _ h1 h2 => vs_FB_nfx hBE.le h1 h2
  Eg_le := fun c hc0 => by
    show max ω (qdQEt E) ≤ (if c = 0 then 0 else max (max ω (qdQEt E)) (qdGt c))
    rw [if_neg hc0]; exact le_max_left _ _
  V_T := fun x hx hx1 hgx => by
    show (if max ω (qdQEt E) < x then qdA E x else 1) ∈ Tset x ∧ _
    rw [if_pos hgx]; exact T.V_T x hx hx1 hgx
  Vq := fun x hx hx1 hgx => by
    show ∃ σ, σ ∈ Tset x ∧ σ < Om1 ∧ σ < vD (vaFB E) x + (if max ω (qdQEt E) < x then qdA E x else 1) ∧
      (if max ω (qdQEt E) < x then qdA E x else 1) < gq σ x
    rw [if_pos hgx]; exact T.Vq x hx hx1 hgx
  W_T := fun x hx hx1 hgx => by
    show T.W x ∈ Tset x ∧ T.W x < Om1 ∧ eN (if max ω (qdQEt E) < x then qdA E x else 1) = glA 1 (T.W x) x
    rw [if_pos hgx]; exact T.W_T x hx hx1 hgx
  V_pi := fun σ ρ hB hgσ => by
    show (if max ω (qdQEt E) < ρ then qdA E ρ else 1) ∈ TB ρ σ ∧
      R2.pi σ ρ (if max ω (qdQEt E) < ρ then qdA E ρ else 1) = (if max ω (qdQEt E) < σ then qdA E σ else 1)
    rw [if_pos (hgσ.trans hB.2.2.1), if_pos hgσ]; exact T.V_pi σ ρ hB hgσ
  W_pi := T.W_pi
  R0 := vD_zero
  G0 := by simp
  G1 := by
    show (if (1 : Ordinal.{0}) = 0 then 0 else max (max ω (qdQEt E)) (qdGt 1)) ≤ max (max ω (qdQEt E)) 1
    rw [if_neg one_ne_zero]
    have e1 : ((1 : ℕ) : Ordinal.{0}) = 1 := by norm_num
    have := qdGt_nat 1; rw [e1] at this
    rw [this]
  lt := fun c x hx hx1 hc hg => by
    change (if c = 0 then 0 else max (max ω (qdQEt E)) (qdGt c)) < x at hg
    show vD c x < (if max ω (qdQEt E) < x then qdA E x else 1)
    rcases eq_or_ne c 0 with rfl | hc0
    · rw [vD_zero]
      split_ifs with hgx
      · exact (T.V_T x hx hx1 hgx).2.1.pos
      · exact zero_lt_one
    · rw [if_neg hc0] at hg
      rw [if_pos ((le_max_left _ _).trans_lt hg)]
      exact T.lt x hx hx1 ((le_max_left _ _).trans_lt hg) c hc ((le_max_right _ _).trans_lt hg)
  pos := fun c x hx hx1 hc0 hc hg => by
    change (if c = 0 then 0 else max (max ω (qdQEt E)) (qdGt c)) < x at hg
    rw [if_neg hc0] at hg
    have h := qd_mono S hE hBE hEB hlim hIH hx hx1 (pos_iff_ne_zero.2 hc0) hc (by rw [qdGt_zero]; exact hx.pos)
      ((le_max_right _ _).trans_lt hg)
    rwa [vD_zero] at h
  mono := fun b c x hx hx1 hbc hc hgb hgc => by
    change (if b = 0 then 0 else max (max ω (qdQEt E)) (qdGt b)) < x at hgb
    change (if c = 0 then 0 else max (max ω (qdQEt E)) (qdGt c)) < x at hgc
    have hc0 : c ≠ 0 := (lt_of_le_of_lt zero_le hbc).ne'
    rw [if_neg hc0] at hgc
    have hgb' : qdGt b < x := by
      rcases eq_or_ne b 0 with rfl | h0
      · rw [qdGt_zero]; exact hx.pos
      · rw [if_neg h0] at hgb; exact (le_max_right _ _).trans_lt hgb
    exact qd_mono S hE hBE hEB hlim hIH hx hx1 hbc hc hgb' ((le_max_right _ _).trans_lt hgc)
  succ := vD_succ
  g_le := fun c => by
    show (if c = 0 then 0 else max (max ω (qdQEt E)) (qdGt c)) ≤
      (if c + 1 = 0 then 0 else max (max ω (qdQEt E)) (qdGt (c + 1)))
    rw [if_neg (lt_of_le_of_lt zero_le (lt_add_one c)).ne']
    split_ifs
    · exact zero_le
    · exact max_le_max le_rfl (qdGt_le_succ c)
  g_succ := fun c Z hZ hgZ hg => by
    change (if c = 0 then 0 else max (max ω (qdQEt E)) (qdGt c)) < Z at hg
    show (if c + 1 = 0 then 0 else max (max ω (qdQEt E)) (qdGt (c + 1))) < Z
    rw [if_neg (lt_of_le_of_lt zero_le (lt_add_one c)).ne']
    refine max_lt hgZ (qdGt_succ hZ c ?_)
    rcases eq_or_ne c 0 with rfl | h0
    · rw [qdGt_zero]; exact hZ.bot_lt
    · rw [if_neg h0] at hg; exact (le_max_right _ _).trans_lt hg
  lim := fun c x hx hx1 hl hc hg => by
    change (if c = 0 then 0 else max (max ω (qdQEt E)) (qdGt c)) < x at hg
    rw [if_neg (show c ≠ 0 from hl.bot_lt.ne')] at hg
    obtain ⟨M, hcM, -, hEg, -, hR, hG⟩ := qd_memV S hE hBE hEB hlim hIH T.lt hc
    have hGc := qd_memG (omega0_lt_inE hx) hEg ((le_max_right _ _).trans_lt hg) hG hcM ((le_max_right _ _).trans_lt hg)
    rw [← hR c hcM x hx hx1 hGc]
    exact M.lim c x hx hx1 hl hcM hGc
  nc := fun c x hx hx1 hl hc hg => by
    change (if c = 0 then 0 else max (max ω (qdQEt E)) (qdGt c)) < x at hg
    rw [if_neg (show c ≠ 0 from hl.bot_lt.ne')] at hg
    exact T.nc c x hx hx1 hl hc hg
  cof := fun c x hx hx1 hl hc hg ν hν => by
    change (if c = 0 then 0 else max (max ω (qdQEt E)) (qdGt c)) < x at hg
    rw [if_neg (show c ≠ 0 from hl.bot_lt.ne')] at hg
    obtain ⟨b, hbc, hgb, hνb⟩ := qd_below S hE hBE hEB hlim hIH hx hx1 hc (show c ≠ 0 from hl.bot_lt.ne')
      ((le_max_right _ _).trans_lt hg) ν hν
    refine ⟨b, hbc, ?_, hνb⟩
    show (if b = 0 then 0 else max (max ω (qdQEt E)) (qdGt b)) < x
    split_ifs
    · exact hx.pos
    · exact max_lt ((le_max_left _ _).trans_lt hg) hgb
  top := fun x hx hx1 hgx ν hν => by
    change ν < (if max ω (qdQEt E) < x then qdA E x else 1) at hν
    rw [if_pos hgx] at hν
    obtain ⟨b, hb, hgb, hνb⟩ := T.top x hx hx1 hgx ν hν
    refine ⟨b, hb, ?_, hνb⟩
    show (if b = 0 then 0 else max (max ω (qdQEt E)) (qdGt b)) < x
    split_ifs
    · exact hx.pos
    · exact max_lt hgx hgb
  ex := fun σ ρ c hB hc hg => by
    change (if c = 0 then 0 else max (max ω (qdQEt E)) (qdGt c)) < σ at hg
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
    rcases eq_or_ne c 0 with rfl | hc0
    · show vD 0 ρ ∈ TB ρ σ ∧ R2.pi σ ρ (vD 0 ρ) = vD 0 σ
      rw [vD_zero, vD_zero]; exact ⟨mem_TB_of_lt hB hB.1.pos, pi_lt hB hB.1.pos⟩
    rw [if_neg hc0] at hg
    obtain ⟨M, hcM, -, hEg, -, hR, hG⟩ := qd_memV S hE hBE hEB hlim hIH T.lt hc
    have hGc := qd_memG (omega0_lt_inE hB.1) hEg ((le_max_right _ _).trans_lt hg) hG hcM
      ((le_max_right _ _).trans_lt hg)
    show vD c ρ ∈ TB ρ σ ∧ R2.pi σ ρ (vD c ρ) = vD c σ
    rw [← hR c hcM ρ hB.2.1 hρ1 (hGc.trans hB.2.2.1), ← hR c hcM σ hB.1 hσ1 hGc]
    exact M.ex σ ρ c hB hcM hGc
  dig := fun σ ρ d hB hd hg P P' hP => by
    change (if d = 0 then 0 else max (max ω (qdQEt E)) (qdGt d)) < σ at hg
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
    show ω ^ P * vD d ρ ∈ TB ρ σ ∧ R2.pi σ ρ (ω ^ P * vD d ρ) = ω ^ P' * vD d σ
    rcases eq_or_ne d 0 with rfl | hd0
    · rw [vD_zero, vD_zero, mul_zero, mul_zero]
      exact ⟨mem_TB_of_lt hB hB.1.pos, pi_lt hB hB.1.pos⟩
    rw [if_neg hd0] at hg
    have hgσ : max ω (qdQEt E) < σ := (le_max_left _ _).trans_lt hg
    have hgρ : max ω (qdQEt E) < ρ := hgσ.trans hB.2.2.1
    obtain ⟨M, hdM, -, hEg, hVle, hR, hG⟩ := qd_memV S hE hBE hEB hlim hIH T.lt hd
    have hGd := qd_memG (omega0_lt_inE hB.1) hEg ((le_max_right _ _).trans_lt hg) hG hdM
      ((le_max_right _ _).trans_lt hg)
    have hGdρ : qdGt d < ρ := ((le_max_right _ _).trans_lt hg).trans hB.2.2.1
    rw [← hR d hdM ρ hB.2.1 hρ1 (hGd.trans hB.2.2.1), ← hR d hdM σ hB.1 hσ1 hGd]
    refine M.dig σ ρ d hB hdM hGd P P' (fun β hβT hβ => hP β hβT (hβ.trans_le ?_))
    show M.V ρ ≤ (if max ω (qdQEt E) < ρ then qdA E ρ else 1)
    rw [if_pos hgρ]
    exact hVle ρ hB.2.1 hρ1 hgρ hGdρ
  cl := fun c Z hZ hc hg => by
    change (if c = 0 then 0 else max (max ω (qdQEt E)) (qdGt c)) < Z at hg
    rcases eq_or_ne c 0 with rfl | hc0
    · exact QdCl.zero hZ.1
    rw [if_neg hc0] at hg
    exact qd_cl_code S hE hBE hEB hlim hIH hZ hc ((le_max_right _ _).trans_lt hg)
  gate := fun c Z hZ hZ1 hgZ hc h => by
    show (if c = 0 then 0 else max (max ω (qdQEt E)) (qdGt c)) < Z
    split_ifs
    · exact hZ.1
    · exact max_lt hgZ (qd_gate S hZ hZ1 c h (hc.trans hEB))

/-- **The union is a system read by `vD`.** -/
theorem qdGood_lim (T : QdTop E) : QdGood E := by
  refine ⟨qdCU S hE hBE hEB hlim hIH T, rfl, rfl, fun x _ _ hgx => ?_, fun c _ x _ _ _ => rfl, fun c _ hc0 => ?_, rfl,
    rfl⟩
  · have hgx' : max ω (qdQEt E) < x := hgx
    show (if max ω (qdQEt E) < x then qdA E x else 1) = qdA E x
    rw [if_pos hgx']
  · show (if c = 0 then 0 else max (max ω (qdQEt E)) (qdGt c)) = max (max ω (qdQEt E)) (qdGt c)
    rw [if_neg hc0]

end Union

end Googology.Trans.PoR.InaccPsi.R2.Qd
