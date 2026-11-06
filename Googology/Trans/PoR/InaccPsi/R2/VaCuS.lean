import Googology.Trans.PoR.InaccPsi.R2.VaLimS

/-!
# VaCuS: THE UNION AT A LIMIT `ε`-NUMBER BASE OVER ITS SEGMENT BASE

As `Va.VaCu` for every limit `ε`-number `E ∈ (B_Γ, X)`: the members (`Va.vs_mem`, the systems at the brackets of the
codes below `E`) give one digit system with base reading `vA E`, readings `vR`, gates `max Eg (yrG c)`, segment base
`vaFB E` read `vR (vaFB E)`.  The data at the top (`VsTop`: the base reading and its facts, the segment base and its
facts, the order and cofinality below the top, and the non-closure of the index readings) come from `Va.VaLimS` at a
non-atom (`vsTopNA`); the atoms come in the next files.

* `vs_gate` (**a code `c < X` over a strongly critical `Z ≤ Ω₁` has gate below `Z`**: the gate of a fixed point
  `F_β(y)` is that of `β` and of `y − y₀(β)`);
* `vs_cl_code`, `vs_memV`, `vs_Dpi`, `vs_nc_lt` (**`D + r < gq(D)` for `r < D`**);
* `VsTop`, `vsTopNA`, `vsCU` (**THE UNION**), `vsGood_lim`.

No new axiom.  New definitions: `VsTop`, `vsTopNA`, `vsCU`.
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
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Xk Googology.Trans.PoR.InaccPsi.R2.Rh
  Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Ge

/-! ## Gates and codes -/

/-- `y₀(β)` is a code over every `Z > 0`. -/
theorem vs_cl_y0 {Z : Ordinal.{0}} (hZ : 0 < Z) (β : Ordinal.{0}) : TlCl Z (glY0 β) := by
  unfold glY0
  split_ifs
  · exact TlCl.add TlCl.om (TlCl.one hZ)
  · exact TlCl.one hZ
  · exact TlCl.zero hZ

/-- **A code `c < X` over a strongly critical `Z ≤ Ω₁` has gate below `Z`.** -/
theorem vs_gate {Z : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om1) : ∀ c, TlCl Z c → c < tlX → yrG c < Z := by
  have hZa : ∀ u v, u < Z → v < Z → u + v < Z := fun u v hu hv => hZ.isPrincipal hu hv
  have hZp : ∀ u v, u < Z → v < Z → veblen u v < Z := fun u v hu hv => hZ.2 u hu v hv
  have hZw : ∀ u, u < Z → ω ^ u < Z := fun u hu => by
    have := hZp 0 u hZ.1 hu; rwa [veblen_zero_apply] at this
  have hωZ : ω < Z := omega0_lt_inE (Low.opow_eq_self_of_SC hZ)
  have hlow : ∀ c, TlCl Z c → c < tfBG → yrG c < Z := fun c hc hcB =>
    zmYr.gate c Z hZ hZ1 hZ.1 hcB hc
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc
  revert IH
  induction hc with
  | @small x h => exact fun _ _ => hlow _ (TlCl.small h) ((h.trans_le hZ1).trans tfBG_gt)
  | om => exact fun _ _ => hlow _ TlCl.om tfBG_gt
  | @add x y hx hy ihx ihy =>
    intro IH h
    exact yr_add hZa hωZ x y (ihx (fun c' hc' => IH c' (hc'.trans_le le_self_add)) (lt_of_le_of_lt le_self_add h))
      (ihy (fun c' hc' => IH c' (hc'.trans_le le_add_self)) (lt_of_le_of_lt le_add_self h))
  | @phi x y hx hy ihx ihy =>
    intro IH h
    rcases lt_or_ge (veblen x y) tfBG with hlt | hge
    · exact hlow _ (TlCl.phi hx hy) hlt
    have hgy := ihy (fun c' hc' => IH c' (hc'.trans_le (right_le_veblen x y)))
      (lt_of_le_of_lt (right_le_veblen x y) h)
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [veblen_zero_apply]
      exact yr_opow_gate hZw hωZ y hgy
    · exact yr_phi_gate hωZ hx0 (va_G_le_BG.trans hge)
        (ihx (fun c' hc' => IH c' (hc'.trans_le (left_le_veblen x y))) (lt_of_le_of_lt (left_le_veblen x y) h)) hgy
  | @atom β y hβ hy h1 ihβ ihy =>
    intro IH h
    rcases lt_or_ge (rhF β y) tfBG with hlt | hge
    · exact hlow _ (TlCl.atom hβ hy h1) hlt
    have hyc : y ≤ rhF β y := rhF_le_self β y
    have hgy := ihy (fun c' hc' => IH c' (hc'.trans_le hyc)) (hyc.trans_lt h)
    rcases hyc.lt_or_eq with hyc' | hyc'
    swap
    · rw [← hyc']; exact hgy
    have hA : YhAt (rhF β y) := ⟨rhF_SC β y, h1⟩
    rcases eq_or_ne β 0 with rfl | hβ0
    · -- an atom `Γ(y)`, `y < Γ(y)`: the index is `y`
      have hge' : tfBG ≤ gamma y := by rw [← rhF_zero]; exact hge
      have hA' : YhAt (gamma y) := by rw [← rhF_zero]; exact hA
      have hyc'' : y < gamma y := by rw [← rhF_zero]; exact hyc'
      obtain ⟨j, hj⟩ := yhAt_iff.1 hA'
      have hBE' : InE tfBG := Low.opow_eq_self_of_SC tfBG_SC
      have hyB : tfBG ≤ y := by
        by_contra hy'
        push Not at hy'
        have h2 := gamma_lt_gamma.2 hy'
        rw [tfBG_fix] at h2
        exact absurd hge' (not_le.2 h2)
      have hjy : y = j := by
        have e1 : gamma y = gamma (Om1 + 1 + j) := by rw [← tf_gcG, ← hj]
        have e2 := gamma_inj.1 e1
        have hjB : tfBG ≤ j := by
          by_contra hj'
          push Not at hj'
          have h3 : Om1 + 1 + j < tfBG := gl_sum_lt hBE' tfBG_gt hj'
          rw [← e2] at h3
          exact absurd hyB (not_le.2 h3)
        obtain ⟨d, hd⟩ := exists_add_of_le hjB
        rw [e2, hd, ← add_assoc, gl_absorb hBE' tfBG_gt]
      have hjg : j < gcG j := by rw [← hj, ← hjy]; exact hyc''
      rw [rhF_zero, hj, yrG_atom hjg, ← hjy]
      exact (yrQ_le y).trans_lt hgy
    · -- a fixed point `F_β(y)` of `Γ`: the gates of `β` and of `y − y₀(β)`
      have hfix : gamma (rhF β y) = rhF β y := rhF_gamma hβ0 y
      have hE : InE (rhF β y) := Low.opow_eq_self_of_SC (rhF_SC β y)
      have hGc : gcG 0 ≤ rhF β y := va_G_le_BG.trans hge
      have hi : ¬ yhJ (rhF β y) < rhF β y := by
        have h' := yhJ_gcG (rhF β y); rw [vs_gcG_fix hfix h1] at h'; rw [h']; exact lt_irrefl _
      have hlev : tlLev (rhF β y) = β := tlLev_F hyc'
      have hidx : tlI β (rhF β y) = y := tlI_rhF β y
      obtain ⟨-, -, hlc⟩ := tl_nf hA.1 hA.2 h
      have hL : tlLev (rhF β y) < rhF β y ∧ tlI (tlLev (rhF β y)) (rhF β y) < rhF β y := by
        rw [hlev] at hlc ⊢; rw [hidx]; exact ⟨hlc, hyc'⟩
      rw [yrG_base hE hGc, yrQE_atom_fixL hA hi hL, hlev, hidx]
      rw [hlev] at hlc
      refine max_lt ((yrQ_le β).trans_lt (ihβ (fun c' hc' => IH c' (hc'.trans hlc)) (hlc.trans h))) ?_
      have hsy : y - glY0 β < rhF β y := (Ordinal.sub_le_self _ _).trans_lt hyc'
      have hsC : TlCl Z (y - glY0 β) := by
        rcases le_or_gt (glY0 β) y with hle | hlt
        · exact (tlDec hZ y hy).1 _ (vs_cl_y0 hZ.1 β) hle
        · rw [Ordinal.sub_eq_zero_iff_le.2 hlt.le]; exact TlCl.zero hZ.1
      exact (yrQ_le _).trans_lt (IH _ hsy hsC (hsy.trans h))

theorem vs_cl_lam {Z : Ordinal.{0}} (hZ : 0 < Z) (α : Ordinal.{0}) {η : Ordinal.{0}} (h : TlCl Z η) :
    TlCl Z (glLam α η) := by
  by_cases hF : glFw α η
  · rw [glLam_of hF]; exact TlCl.add h (TlCl.one hZ)
  · rw [glLam_of_not hF]; exact TlCl.add (vs_cl_y0 hZ α) h

theorem vs_cl_psi {Z : Ordinal.{0}} (hZ : 0 < Z) {α η : Ordinal.{0}} (hα : TlCl Z α) (hη : TlCl Z η) :
    TlCl Z (yhPsi α η) := by
  unfold yhPsi
  split_ifs
  · exact TlCl.phi hα (vs_cl_lam hZ α (TlCl.add (TlCl.one hZ) hη))
  · exact TlCl.phi hα (vs_cl_lam hZ α hη)

/-- **`D + r < gq(D)` for `0 < r < D`** (`σ = D`). -/
theorem vs_nc_lt {x D r : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hDT : D ∈ Tset x) (hD1 : D < Om1)
    (hr0 : 0 < r) (hrD : r < D) :
    ∃ σ, σ ∈ Tset x ∧ σ < Om1 ∧ σ < D + r ∧ D + r < gq σ x := by
  obtain ⟨-, -, -, hqE, -⟩ := geq_facts hx hx1 hDT hD1
  have hDq := gmq_gt hx hx1 hDT hD1
  exact ⟨D, hDT, hD1, lt_add_of_pos_right D hr0, (inE_indec hqE).add_lt hDq (hrD.trans hDq)⟩

/-! ## The union -/

section Union

variable {E : Ordinal.{0}} (hE : InE E) (hBE : tfBG < E) (hEX : E < tlX)
  (hlim : ∀ e, InE e → e < E → eN e < E) (hIH : ∀ e, InE e → tfBG ≤ e → e < E → VsGood e)

include hE hBE hEX hlim hIH

/-- A code below `E` with gate below a strongly critical `Z` above the base gate is a code over `Z`. -/
theorem vs_cl_code {Z : Ordinal.{0}} (hZ : SC Z) {c : Ordinal.{0}} (hc : c < E) (hg : yrG c < Z) : TlCl Z c := by
  have hωZ : ω < Z := omega0_lt_inE (Low.opow_eq_self_of_SC hZ)
  obtain ⟨e, M, -, -, -, -, -, hcM, -, -, -, hEg, -, -, hG, -, -⟩ := vs_mem hlim hIH hBE hc
  exact M.cl c Z hZ hcM (vs_memG hωZ hEg hg hG hcM hg)

/-- **A member whose base reading is below `vA E`** at every base above the gates. -/
theorem vs_memV (htop : ∀ y, InE y → y < Om1 → max ω (yrQE E) < y → ∀ c, c < E → yrG c < y →
      vR c y < vA E y) {c : Ordinal.{0}} (hc : c < E) :
    ∃ M : ZmDS, c < M.E ∧ M.E < E ∧ M.Eg ≤ max ω (yrG c) ∧
      (∀ y, InE y → y < Om1 → max ω (yrQE E) < y → yrG c < y → M.V y ≤ vA E y) ∧
      (∀ c', c' < M.E → ∀ y, InE y → y < Om1 → M.G c' < y → M.R c' y = vR c' y) ∧
      (∀ c', c' < M.E → c' ≠ 0 → M.G c' = max M.Eg (yrG c')) := by
  obtain ⟨e, M, he, heB, -, hemax, hME, hcM, hMlt, -, hEgeq, hEg, hV, hR, hG, -, -⟩ := vs_mem hlim hIH hBE hc
  refine ⟨M, hcM, hMlt, hEg, fun y hy hy1 hgy hg => ?_, hR, hG⟩
  have hωy : ω < y := omega0_lt_inE hy
  have hyl : IsSuccLimit y := ev_isSuccLimit_of_inE hy
  have hgM : M.Eg < y := hEg.trans_lt (max_lt hωy hg)
  have hMEE : InE M.E := by rw [hME]; exact eN_E e
  have hGME : gcG 0 ≤ M.E := (va_G_le_BG.trans heB).trans (hME ▸ (lt_eN e).le)
  have hgME : yrG M.E < y := by
    rw [yrG_base hMEE hGME, hME]
    exact vs_QE_eN_lt he heB hyl hωy ((le_max_right _ _).trans_lt (hEgeq ▸ hgM))
  have hlt := htop y hy hy1 hgy M.E hMlt hgME
  rw [vR_base hMEE hGME, ← (hV y hy hy1 hgM).2] at hlt
  exact hlt.le

omit hEX in
/-- **The segment base is exact**, from the system at it. -/
theorem vs_Dpi (hFE : vaFB E < E) {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) (hgσ : max ω (yrQE E) < σ) :
    vR (vaFB E) ρ ∈ TB ρ σ ∧ R2.pi σ ρ (vR (vaFB E) ρ) = vR (vaFB E) σ := by
  have hωσ : ω < σ := omega0_lt_inE hB.1
  have hgF : yrG (vaFB E) < σ :=
    (vs_FB_gate E hBE.le).trans_lt (by rw [yrG_base hE (va_G_le_BG.trans hBE.le)]; exact hgσ)
  have hFF : vaFB (vaFB E) = vaFB E := vs_FB_self (vs_FB_fix hBE.le) (vs_FB_gt hBE.le)
  have hgu : guE (vaFB E) = vaFB E := le_antisymm (gl_E_le (yh_gfE_le (va_G_le_BG.trans (vs_FB_ge hBE.le))))
    (gl_E_max (vs_FB_E hBE.le) (vs_FB_gt hBE.le) le_rfl)
  obtain ⟨e, M, -, -, he, -, -, -, -, -, -, hEg, -, -, -, -, hD⟩ := vs_mem hlim hIH hBE hFE
  have heF : e = vaFB E := (he (vs_FB_ge hBE.le)).trans hgu
  rw [heF, hFF] at hD
  have h := M.Dv_pi σ ρ hB (hEg.trans_lt (max_lt hωσ hgF))
  rwa [hD] at h

omit hEX in
/-- **The index readings are not closed**: `F(x) + c(x)` for a limit code `c < E` past the segment base `F < E`
(below `F` by `Va.vs_nc_lt`, from the member at the bracket of `c` above `F`). -/
theorem vs_ncE (hFE : vaFB E < E) : ∀ c x, InE x → x < Om1 → IsSuccLimit c → c < E →
    max (max ω (yrQE E)) (yrG c) < x →
    ∃ σ, σ ∈ Tset x ∧ σ < Om1 ∧ σ < vR (vaFB E) x + vR c x ∧ vR (vaFB E) x + vR c x < gq σ x := by
  intro c x hx hx1 hl hc hg
  have hgx : max ω (yrQE E) < x := (le_max_left _ _).trans_lt hg
  have hgc : yrG c < x := (le_max_right _ _).trans_lt hg
  have hc0 : c ≠ 0 := hl.bot_lt.ne'
  have hgF : yrG (vaFB E) < x :=
    (vs_FB_gate E hBE.le).trans_lt (by rw [yrG_base hE (va_G_le_BG.trans hBE.le)]; exact hgx)
  by_cases hcF : c < vaFB E
  · obtain ⟨hDT, -, -, hDX⟩ := vs_xF hE hBE hlim hIH hx hx1 hFE hgx
    have h0 : vR 0 x < vR c x := vs_mono hE hBE hlim hIH hx hx1 (pos_iff_ne_zero.2 hc0) hc
      (by rw [yrG_zero]; exact hx.pos) hgc
    rw [vR_zero] at h0
    exact vs_nc_lt hx hx1 hDT (hDX.trans (ywX_facts hx hx1).2.2.1) h0
      (vs_mono hE hBE hlim hIH hx hx1 hcF hFE hgc hgF)
  · have hcF' : vaFB E ≤ c := not_lt.1 hcF
    have hGc : gcG 0 ≤ c := va_G_le_BG.trans ((vs_FB_ge hBE.le).trans hcF')
    obtain ⟨e, M, -, -, he, -, -, hcM, -, -, -, hEg, -, hR, hG, -, hD⟩ := vs_mem hlim hIH hBE hc
    have heF : vaFB e = vaFB E := by
      rw [he ((vs_FB_ge hBE.le).trans hcF')]
      exact vs_FB_of_le hBE.le (gl_E_max (vs_FB_E hBE.le) (vs_FB_gt hBE.le) hcF')
        ((gl_E_le (yh_gfE_le hGc)).trans hc.le)
    have hGcM := vs_memG (omega0_lt_inE hx) hEg hgc hG hcM hgc
    have h := M.nc c x hx hx1 hl hcM hGcM
    rw [hD, heF, hR c hcM x hx hx1 hGcM] at h
    exact h

/-- **The data of the top `E`** for the union: the base reading `vA E` with its facts, the order and cofinality of
the readings below it. -/
structure VsTop (E : Ordinal.{0}) where
  Ei : Ordinal.{0}
  W : Ordinal.{0} → Ordinal.{0}
  E_eq : veblen 1 Ei = E
  Ei_cl : ∀ Z, SC Z → max ω (yrQE E) < Z → TlCl Z Ei
  V_T : ∀ x, InE x → x < Om1 → max ω (yrQE E) < x →
    vA E x ∈ Tset x ∧ InE (vA E x) ∧ vR (vaFB E) x ≤ vA E x ∧ vA E x < ywX x
  Vq : ∀ x, InE x → x < Om1 → max ω (yrQE E) < x →
    ∃ σ, σ ∈ Tset x ∧ σ < Om1 ∧ σ < vR (vaFB E) x + vA E x ∧ vA E x < gq σ x
  W_T : ∀ x, InE x → x < Om1 → max ω (yrQE E) < x → W x ∈ Tset x ∧ W x < Om1 ∧ eN (vA E x) = glA 1 (W x) x
  V_pi : ∀ σ ρ, Bases σ ρ → max ω (yrQE E) < σ → vA E ρ ∈ TB ρ σ ∧ R2.pi σ ρ (vA E ρ) = vA E σ
  W_pi : ∀ σ ρ, Bases σ ρ → max ω (yrQE E) < σ → W ρ ∈ TB ρ σ ∧ R2.pi σ ρ (W ρ) = W σ
  lt : ∀ x, InE x → x < Om1 → max ω (yrQE E) < x → ∀ c, c < E → yrG c < x → vR c x < vA E x
  top : ∀ x, InE x → x < Om1 → max ω (yrQE E) < x → ∀ ν, ν < vA E x → ∃ b, b < E ∧ yrG b < x ∧ ν ≤ vR b x
  B_cl : ∀ Z, SC Z → max ω (yrQE E) < Z → TlCl Z (vaFB E)
  D_T : ∀ x, InE x → x < Om1 → max ω (yrQE E) < x →
    vR (vaFB E) x ∈ Tset x ∧ InE (vR (vaFB E) x) ∧ x < vR (vaFB E) x ∧ vR (vaFB E) x < ywX x
  D_pi : ∀ σ ρ, Bases σ ρ → max ω (yrQE E) < σ →
    vR (vaFB E) ρ ∈ TB ρ σ ∧ R2.pi σ ρ (vR (vaFB E) ρ) = vR (vaFB E) σ
  nc : ∀ c x, InE x → x < Om1 → IsSuccLimit c → c < E → max (max ω (yrQE E)) (yrG c) < x →
    ∃ σ, σ ∈ Tset x ∧ σ < Om1 ∧ σ < vR (vaFB E) x + vR c x ∧ vR (vaFB E) x + vR c x < gq σ x

open Classical in
/-- **The top data at a non-atom `E`.** -/
noncomputable def vsTopNA (hFE : vaFB E < E) (hnA : ¬ YhAt E) : VsTop E where
  Ei := if yhK E = 1 then glLam 1 (yhI E) else E
  W := fun x => if yhK E = 1 then vR (yhI E) x + 1 else vA E x
  E_eq := by
    obtain ⟨-, -, hk1, -, -, hpsi⟩ := vs_dat hE hBE hFE hnA
    split_ifs with h1
    · have h := hpsi
      rw [h1, yhPsi_ne va_one_notAt] at h
      exact h
    · have hk2 : 1 < yhK E := lt_of_le_of_ne hk1 (Ne.symm h1)
      have hPe : LuP (yhK E) E := by have := yhPsi_P (yhK E) (yhI E); rwa [hpsi] at this
      exact luP_succ.1 (luP_mono le_add_self (add_one_le_of_lt hk2) hPe)
  Ei_cl := fun Z hZ hgZ => by
    obtain ⟨hnA, -, hk1, hkE, hiE, hpsi⟩ := vs_dat hE hBE hFE hnA
    have hωZ : ω < Z := omega0_lt_inE (Low.opow_eq_self_of_SC hZ)
    have hQ := yrQE_psi hnA
    have hQle : max (yrQ (yhK E)) (yrQ (yhI E)) < Z := by rw [← hQ]; exact (le_max_right _ _).trans_lt hgZ
    have hk := vs_cl_code hE hBE hEX hlim hIH hZ hkE (yrG_of_Q hωZ ((le_max_left _ _).trans_lt hQle))
    have hi := vs_cl_code hE hBE hEX hlim hIH hZ hiE (yrG_of_Q hωZ ((le_max_right _ _).trans_lt hQle))
    split_ifs with h1
    · exact vs_cl_lam hZ.1 1 hi
    · have h := vs_cl_psi hZ.1 hk hi; rwa [hpsi] at h
  V_T := fun x hx hx1 hgx => by
    obtain ⟨-, -, -, hkE, hiE, -⟩ := vs_dat hE hBE hFE hnA
    obtain ⟨hgk, hgi, hv1, hkT, hk1', hiT, hi1, hA⟩ := vs_datx hE hBE hlim hIH hx hx1 hFE hnA hgx
    obtain ⟨-, -, hkX⟩ := vs_T hE hBE hlim hIH hx hx1 hkE hgk
    obtain ⟨-, -, hiX⟩ := vs_T hE hBE hlim hIH hx hx1 hiE hgi
    obtain ⟨hVT, -, -, hVE, -, -⟩ := glA_facts hx hx1 hv1 hkT hk1' hiT hi1
    have hmT : max (vR (yhK E) x) (vR (yhI E) x) ∈ Tset x := by
      rcases le_total (vR (yhK E) x) (vR (yhI E) x) with h | h
      · rw [max_eq_right h]; exact hiT
      · rw [max_eq_left h]; exact hkT
    have hm1 : max (vR (yhK E) x) (vR (yhI E) x) < Om1 := max_lt hk1' hi1
    have hq := gmq_gt hx hx1 hmT hm1
    have hlt := xkA_lt hx hx1 hmT hm1 ((le_max_left _ _).trans_lt hq) ((le_max_right _ _).trans_lt hq)
    rw [← hA] at hVT hVE hlt
    exact ⟨hVT, hVE, (vs_D_lt hE hBE hlim hIH hx hx1 hFE hnA hgx).le,
      hlt.trans (zm_gq_lt_X hx hx1 hmT hm1 (max_lt hkX hiX))⟩
  Vq := fun x hx hx1 hgx => by
    obtain ⟨-, -, hv1, hkT, hk1', hiT, hi1, hA⟩ := vs_datx hE hBE hlim hIH hx hx1 hFE hnA hgx
    obtain ⟨-, -, -, -, hka, hta⟩ := glA_facts hx hx1 hv1 hkT hk1' hiT hi1
    have hmT : max (vR (yhK E) x) (vR (yhI E) x) ∈ Tset x := by
      rcases le_total (vR (yhK E) x) (vR (yhI E) x) with h | h
      · rw [max_eq_right h]; exact hiT
      · rw [max_eq_left h]; exact hkT
    have hm1 : max (vR (yhK E) x) (vR (yhI E) x) < Om1 := max_lt hk1' hi1
    have hq := gmq_gt hx hx1 hmT hm1
    refine ⟨_, hmT, hm1, ?_, ?_⟩
    · rw [hA]; exact (max_lt hka hta).trans_le le_add_self
    · rw [hA]; exact xkA_lt hx hx1 hmT hm1 ((le_max_left _ _).trans_lt hq) ((le_max_right _ _).trans_lt hq)
  W_T := fun x hx hx1 hgx => by
    obtain ⟨-, -, hk1, hkE, -, -⟩ := vs_dat hE hBE hFE hnA
    obtain ⟨hgk, -, hv1, hkT, hk1', hiT, hi1, hA⟩ := vs_datx hE hBE hlim hIH hx hx1 hFE hnA hgx
    show (if yhK E = 1 then vR (yhI E) x + 1 else vA E x) ∈ Tset x ∧
      (if yhK E = 1 then vR (yhI E) x + 1 else vA E x) < Om1 ∧
      eN (vA E x) = glA 1 (if yhK E = 1 then vR (yhI E) x + 1 else vA E x) x
    split_ifs with h1
    · obtain ⟨hsT, hs1⟩ := gl_T_succ hx hx1 hiT hi1
      refine ⟨hsT, hs1, ?_⟩
      rw [hA, h1, vR_one]; exact glA_eN_one hx hx1 hiT hi1
    · have hk2 : 2 ≤ yhK E := by
        rw [← one_add_one_eq_two]; exact add_one_le_of_lt (lt_of_le_of_ne hk1 (Ne.symm h1))
      have e2 : ((2 : ℕ) : Ordinal.{0}) = 2 := by norm_num
      have hg2 : yrG 2 < x := by
        have := yrG_low (yh_nat_lt_G 2); rw [glG_nat, e2] at this
        rw [this, ← e2]; exact (natCast_lt_omega0 2).trans (omega0_lt_inE hx)
      have hv2 : 2 ≤ vR (yhK E) x := by
        have h := vs_le_mono hE hBE hlim hIH hx hx1 hk2 hkE hg2 hgk
        have hv : vR 2 x = 2 := by have := vR_nat 2 x; rwa [e2] at this
        rwa [hv] at h
      obtain ⟨hVT, -, hV1, -, -, -⟩ := glA_facts hx hx1 hv1 hkT hk1' hiT hi1
      rw [← hA] at hVT hV1
      refine ⟨hVT, hV1, ?_⟩
      rw [hA]; exact glA_eN_two hx hx1 hv2 hkT hk1' hiT hi1
  V_pi := fun σ ρ hB hgσ => by
    obtain ⟨-, -, -, hkE, hiE, -⟩ := vs_dat hE hBE hFE hnA
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
    have hgρ := hgσ.trans hB.2.2.1
    obtain ⟨hgk, hgi, -, -, hk1', -, hi1, hA⟩ := vs_datx hE hBE hlim hIH hB.2.1 hρ1 hFE hnA hgρ
    obtain ⟨hgkσ, hgiσ, -, -, -, -, -, hAσ⟩ := vs_datx hE hBE hlim hIH hB.1 hσ1 hFE hnA hgσ
    have hex : ∀ c, c < E → yrG c < σ → vR c ρ ∈ TB ρ σ ∧ R2.pi σ ρ (vR c ρ) = vR c σ := by
      intro c hc hgc
      obtain ⟨M, hcM, -, hEg, -, hR, hG⟩ := vs_memV hE hBE hEX hlim hIH (vs_ltT hE hBE hlim hIH hFE hnA) hc
      have hGc := vs_memG (omega0_lt_inE hB.1) hEg hgc hG hcM hgc
      rw [← hR c hcM ρ hB.2.1 hρ1 (hGc.trans hB.2.2.1), ← hR c hcM σ hB.1 hσ1 hGc]
      exact M.ex σ ρ c hB hcM hGc
    obtain ⟨k1, k2⟩ := hex _ hkE hgkσ
    obtain ⟨i1, i2⟩ := hex _ hiE hgiσ
    obtain ⟨a1, a2⟩ := glA_pi hB k1 hk1' i1 hi1
    rw [k2, i2, ← hAσ] at a2
    rw [hA]; exact ⟨a1, a2⟩
  W_pi := fun σ ρ hB hgσ => by
    obtain ⟨-, -, -, hkE, hiE, -⟩ := vs_dat hE hBE hFE hnA
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
    have hgρ := hgσ.trans hB.2.2.1
    obtain ⟨hgk, hgi, -, -, hk1', -, hi1, hA⟩ := vs_datx hE hBE hlim hIH hB.2.1 hρ1 hFE hnA hgρ
    obtain ⟨hgkσ, hgiσ, -, -, -, -, -, hAσ⟩ := vs_datx hE hBE hlim hIH hB.1 hσ1 hFE hnA hgσ
    have hex : ∀ c, c < E → yrG c < σ → vR c ρ ∈ TB ρ σ ∧ R2.pi σ ρ (vR c ρ) = vR c σ := by
      intro c hc hgc
      obtain ⟨M, hcM, -, hEg, -, hR, hG⟩ := vs_memV hE hBE hEX hlim hIH (vs_ltT hE hBE hlim hIH hFE hnA) hc
      have hGc := vs_memG (omega0_lt_inE hB.1) hEg hgc hG hcM hgc
      rw [← hR c hcM ρ hB.2.1 hρ1 (hGc.trans hB.2.2.1), ← hR c hcM σ hB.1 hσ1 hGc]
      exact M.ex σ ρ c hB hcM hGc
    show (if yhK E = 1 then vR (yhI E) ρ + 1 else vA E ρ) ∈ TB ρ σ ∧
      R2.pi σ ρ (if yhK E = 1 then vR (yhI E) ρ + 1 else vA E ρ) =
        (if yhK E = 1 then vR (yhI E) σ + 1 else vA E σ)
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
  lt := fun x hx hx1 hgx c hc hg => vs_lt_top hE hBE hlim hIH hx hx1 hFE hnA hgx c hc hg
  top := fun x hx hx1 hgx ν hν => vs_top hE hBE hlim hIH hx hx1 hFE hnA hgx ν hν
  B_cl := fun Z hZ hgZ => by
    have hgF : yrG (vaFB E) < Z :=
      (vs_FB_gate E hBE.le).trans_lt (by rw [yrG_base hE (va_G_le_BG.trans hBE.le)]; exact hgZ)
    exact vs_cl_code hE hBE hEX hlim hIH hZ hFE hgF
  D_T := fun x hx hx1 hgx => vs_xF hE hBE hlim hIH hx hx1 hFE hgx
  D_pi := fun σ ρ hB hgσ => vs_Dpi hE hBE hlim hIH hFE hB hgσ
  nc := fun c x hx hx1 hl hc hg => vs_ncE hE hBE hlim hIH hFE c x hx hx1 hl hc hg

open Classical in
/-- **THE UNION AT A LIMIT `ε`-NUMBER BASE** from the top data. -/
noncomputable def vsCU (T : VsTop E) : ZmDS where
  E := E
  Ei := T.Ei
  V := fun x => if max ω (yrQE E) < x then vA E x else 1
  W := T.W
  R := vR
  G := fun c => if c = 0 then 0 else max (max ω (yrQE E)) (yrG c)
  Eg := max ω (yrQE E)
  B := vaFB E
  Dv := vR (vaFB E)
  E_eq := T.E_eq
  BG_le := hBE.le
  B_le := vs_FB_le hBE.le
  BG_B := vs_FB_ge hBE.le
  B_cl := T.B_cl
  Dv_T := T.D_T
  Dv_pi := T.D_pi
  E_X := hEX
  Ei_cl := T.Ei_cl
  nfx := fun _ h1 h2 => vs_FB_nfx hBE.le h1 h2
  Eg_le := fun c hc0 => by
    show max ω (yrQE E) ≤ (if c = 0 then 0 else max (max ω (yrQE E)) (yrG c))
    rw [if_neg hc0]; exact le_max_left _ _
  V_T := fun x hx hx1 hgx => by
    show (if max ω (yrQE E) < x then vA E x else 1) ∈ Tset x ∧ _
    rw [if_pos hgx]; exact T.V_T x hx hx1 hgx
  Vq := fun x hx hx1 hgx => by
    show ∃ σ, σ ∈ Tset x ∧ σ < Om1 ∧ σ < vR (vaFB E) x + (if max ω (yrQE E) < x then vA E x else 1) ∧
      (if max ω (yrQE E) < x then vA E x else 1) < gq σ x
    rw [if_pos hgx]; exact T.Vq x hx hx1 hgx
  W_T := fun x hx hx1 hgx => by
    show T.W x ∈ Tset x ∧ T.W x < Om1 ∧ eN (if max ω (yrQE E) < x then vA E x else 1) = glA 1 (T.W x) x
    rw [if_pos hgx]; exact T.W_T x hx hx1 hgx
  V_pi := fun σ ρ hB hgσ => by
    show (if max ω (yrQE E) < ρ then vA E ρ else 1) ∈ TB ρ σ ∧
      R2.pi σ ρ (if max ω (yrQE E) < ρ then vA E ρ else 1) = (if max ω (yrQE E) < σ then vA E σ else 1)
    rw [if_pos (hgσ.trans hB.2.2.1), if_pos hgσ]; exact T.V_pi σ ρ hB hgσ
  W_pi := T.W_pi
  R0 := vR_zero
  G0 := by simp
  G1 := by
    show (if (1 : Ordinal.{0}) = 0 then 0 else max (max ω (yrQE E)) (yrG 1)) ≤ max (max ω (yrQE E)) 1
    rw [if_neg one_ne_zero]
    have e1 : ((1 : ℕ) : Ordinal.{0}) = 1 := by norm_num
    have := yrG_low (yh_nat_lt_G 1); rw [glG_nat, e1] at this
    rw [this]
  lt := fun c x hx hx1 hc hg => by
    change (if c = 0 then 0 else max (max ω (yrQE E)) (yrG c)) < x at hg
    show vR c x < (if max ω (yrQE E) < x then vA E x else 1)
    rcases eq_or_ne c 0 with rfl | hc0
    · rw [vR_zero]
      split_ifs with hgx
      · exact (T.V_T x hx hx1 hgx).2.1.pos
      · exact zero_lt_one
    · rw [if_neg hc0] at hg
      rw [if_pos ((le_max_left _ _).trans_lt hg)]
      exact T.lt x hx hx1 ((le_max_left _ _).trans_lt hg) c hc ((le_max_right _ _).trans_lt hg)
  pos := fun c x hx hx1 hc0 hc hg => by
    change (if c = 0 then 0 else max (max ω (yrQE E)) (yrG c)) < x at hg
    rw [if_neg hc0] at hg
    have h := vs_mono hE hBE hlim hIH hx hx1 (pos_iff_ne_zero.2 hc0) hc (by rw [yrG_zero]; exact hx.pos)
      ((le_max_right _ _).trans_lt hg)
    rwa [vR_zero] at h
  mono := fun b c x hx hx1 hbc hc hgb hgc => by
    change (if b = 0 then 0 else max (max ω (yrQE E)) (yrG b)) < x at hgb
    change (if c = 0 then 0 else max (max ω (yrQE E)) (yrG c)) < x at hgc
    have hc0 : c ≠ 0 := (lt_of_le_of_lt zero_le hbc).ne'
    rw [if_neg hc0] at hgc
    have hgb' : yrG b < x := by
      rcases eq_or_ne b 0 with rfl | h0
      · rw [yrG_zero]; exact hx.pos
      · rw [if_neg h0] at hgb; exact (le_max_right _ _).trans_lt hgb
    exact vs_mono hE hBE hlim hIH hx hx1 hbc hc hgb' ((le_max_right _ _).trans_lt hgc)
  succ := vR_succ
  g_le := fun c => by
    show (if c = 0 then 0 else max (max ω (yrQE E)) (yrG c)) ≤
      (if c + 1 = 0 then 0 else max (max ω (yrQE E)) (yrG (c + 1)))
    rw [if_neg (lt_of_le_of_lt zero_le (lt_add_one c)).ne']
    split_ifs
    · exact zero_le
    · exact max_le_max le_rfl (yrG_le_succ c)
  g_succ := fun c Z hZ hgZ hg => by
    change (if c = 0 then 0 else max (max ω (yrQE E)) (yrG c)) < Z at hg
    show (if c + 1 = 0 then 0 else max (max ω (yrQE E)) (yrG (c + 1))) < Z
    rw [if_neg (lt_of_le_of_lt zero_le (lt_add_one c)).ne']
    refine max_lt hgZ (yrG_succ hZ c ?_)
    rcases eq_or_ne c 0 with rfl | h0
    · rw [yrG_zero]; exact hZ.bot_lt
    · rw [if_neg h0] at hg; exact (le_max_right _ _).trans_lt hg
  lim := fun c x hx hx1 hl hc hg => by
    change (if c = 0 then 0 else max (max ω (yrQE E)) (yrG c)) < x at hg
    rw [if_neg (show c ≠ 0 from hl.bot_lt.ne')] at hg
    obtain ⟨M, hcM, -, hEg, -, hR, hG⟩ := vs_memV hE hBE hEX hlim hIH T.lt hc
    have hGc := vs_memG (omega0_lt_inE hx) hEg ((le_max_right _ _).trans_lt hg) hG hcM ((le_max_right _ _).trans_lt hg)
    rw [← hR c hcM x hx hx1 hGc]
    exact M.lim c x hx hx1 hl hcM hGc
  nc := fun c x hx hx1 hl hc hg => by
    change (if c = 0 then 0 else max (max ω (yrQE E)) (yrG c)) < x at hg
    rw [if_neg (show c ≠ 0 from hl.bot_lt.ne')] at hg
    exact T.nc c x hx hx1 hl hc hg
  cof := fun c x hx hx1 hl hc hg ν hν => by
    change (if c = 0 then 0 else max (max ω (yrQE E)) (yrG c)) < x at hg
    rw [if_neg (show c ≠ 0 from hl.bot_lt.ne')] at hg
    obtain ⟨b, hbc, hgb, hνb⟩ := vs_below hE hBE hlim hIH hx hx1 hc (show c ≠ 0 from hl.bot_lt.ne')
      ((le_max_right _ _).trans_lt hg) ν hν
    refine ⟨b, hbc, ?_, hνb⟩
    show (if b = 0 then 0 else max (max ω (yrQE E)) (yrG b)) < x
    split_ifs
    · exact hx.pos
    · exact max_lt ((le_max_left _ _).trans_lt hg) hgb
  top := fun x hx hx1 hgx ν hν => by
    change ν < (if max ω (yrQE E) < x then vA E x else 1) at hν
    rw [if_pos hgx] at hν
    obtain ⟨b, hb, hgb, hνb⟩ := T.top x hx hx1 hgx ν hν
    refine ⟨b, hb, ?_, hνb⟩
    show (if b = 0 then 0 else max (max ω (yrQE E)) (yrG b)) < x
    split_ifs
    · exact hx.pos
    · exact max_lt hgx hgb
  ex := fun σ ρ c hB hc hg => by
    change (if c = 0 then 0 else max (max ω (yrQE E)) (yrG c)) < σ at hg
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
    rcases eq_or_ne c 0 with rfl | hc0
    · show vR 0 ρ ∈ TB ρ σ ∧ R2.pi σ ρ (vR 0 ρ) = vR 0 σ
      rw [vR_zero, vR_zero]; exact ⟨mem_TB_of_lt hB hB.1.pos, pi_lt hB hB.1.pos⟩
    rw [if_neg hc0] at hg
    obtain ⟨M, hcM, -, hEg, -, hR, hG⟩ := vs_memV hE hBE hEX hlim hIH T.lt hc
    have hGc := vs_memG (omega0_lt_inE hB.1) hEg ((le_max_right _ _).trans_lt hg) hG hcM
      ((le_max_right _ _).trans_lt hg)
    show vR c ρ ∈ TB ρ σ ∧ R2.pi σ ρ (vR c ρ) = vR c σ
    rw [← hR c hcM ρ hB.2.1 hρ1 (hGc.trans hB.2.2.1), ← hR c hcM σ hB.1 hσ1 hGc]
    exact M.ex σ ρ c hB hcM hGc
  dig := fun σ ρ d hB hd hg P P' hP => by
    change (if d = 0 then 0 else max (max ω (yrQE E)) (yrG d)) < σ at hg
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
    show ω ^ P * vR d ρ ∈ TB ρ σ ∧ R2.pi σ ρ (ω ^ P * vR d ρ) = ω ^ P' * vR d σ
    rcases eq_or_ne d 0 with rfl | hd0
    · rw [vR_zero, vR_zero, mul_zero, mul_zero]
      exact ⟨mem_TB_of_lt hB hB.1.pos, pi_lt hB hB.1.pos⟩
    rw [if_neg hd0] at hg
    have hgσ : max ω (yrQE E) < σ := (le_max_left _ _).trans_lt hg
    have hgρ : max ω (yrQE E) < ρ := hgσ.trans hB.2.2.1
    obtain ⟨M, hdM, -, hEg, hVle, hR, hG⟩ := vs_memV hE hBE hEX hlim hIH T.lt hd
    have hGd := vs_memG (omega0_lt_inE hB.1) hEg ((le_max_right _ _).trans_lt hg) hG hdM
      ((le_max_right _ _).trans_lt hg)
    have hGdρ : yrG d < ρ := ((le_max_right _ _).trans_lt hg).trans hB.2.2.1
    rw [← hR d hdM ρ hB.2.1 hρ1 (hGd.trans hB.2.2.1), ← hR d hdM σ hB.1 hσ1 hGd]
    refine M.dig σ ρ d hB hdM hGd P P' (fun β hβT hβ => hP β hβT (hβ.trans_le ?_))
    show M.V ρ ≤ (if max ω (yrQE E) < ρ then vA E ρ else 1)
    rw [if_pos hgρ]
    exact hVle ρ hB.2.1 hρ1 hgρ hGdρ
  cl := fun c Z hZ hc hg => by
    change (if c = 0 then 0 else max (max ω (yrQE E)) (yrG c)) < Z at hg
    rcases eq_or_ne c 0 with rfl | hc0
    · exact TlCl.zero hZ.1
    rw [if_neg hc0] at hg
    exact vs_cl_code hE hBE hEX hlim hIH hZ hc ((le_max_right _ _).trans_lt hg)
  gate := fun c Z hZ hZ1 hgZ hc h => by
    show (if c = 0 then 0 else max (max ω (yrQE E)) (yrG c)) < Z
    split_ifs
    · exact hZ.1
    · exact max_lt hgZ (vs_gate hZ hZ1 c h (hc.trans hEX))

/-- **The union is a system read by `vR`.** -/
theorem vsGood_lim (T : VsTop E) : VsGood E := by
  refine ⟨vsCU hE hBE hEX hlim hIH T, rfl, rfl, fun x _ _ hgx => ?_, fun c _ x _ _ _ => rfl, fun c _ hc0 => ?_, rfl,
    rfl⟩
  · have hgx' : max ω (yrQE E) < x := hgx
    show (if max ω (yrQE E) < x then vA E x else 1) = vA E x
    rw [if_pos hgx']
  · show (if c = 0 then 0 else max (max ω (yrQE E)) (yrG c)) = max (max ω (yrQE E)) (yrG c)
    rw [if_neg hc0]

end Union

end Googology.Trans.PoR.InaccPsi.R2.Va
