import Googology.Trans.PoR.InaccPsi.R2.VaLim

/-!
# VaCu: THE UNION AT A LIMIT `ε`-NUMBER BASE, AND A DIGIT SYSTEM AT EVERY `ε`-NUMBER BASE BELOW `Γ_{B_Γ+1}`

At a limit `ε`-number `E ∈ (B_Γ, Γ_{B_Γ+1})` the members (`Va.va_mem`) give one digit system with base reading
`vA E = ϑˣ(Ω₁·α(x) + η(x))`, readings `vR`, gates `max Eg (yrG c)`: the fields at the codes from the members, the
fields at the top from `Va.VaLim` (order, cofinality, bounds), Lemma EXACT for the top by `Gl.glA_pi`, and
`ε_{V(x)+1} = ϑˣ(Ω₁ + W(x))` with `W = V` (level `≥ 2`, `Gl.glA_eN_two`) or `W = η(x) + 1` (level `1`).

* `va_gate` (**a code `c < Γ_{B_Γ+1}` over a strongly critical `Z ≤ Ω₁` has gate below `Z`**), `va_cl_lam`,
  `va_cl_psi`, `va_U_lt_X`;
* `vaCU` (**THE UNION**), `vaGood_lim`, `vaGood_all` (**`VaGood E` for every `ε`-number `B_Γ ≤ E < Γ_{B_Γ+1}`**,
  one transfinite induction: `Va.vaGood_BG`, `Va.vaGood_succ`, `vaGood_lim`).

No new axiom.  New definition: `vaCU`.
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

/-! ## Gates and codes -/

/-- **A code `c < Γ_{B_Γ+1}` over a strongly critical `Z ≤ Ω₁` has gate below `Z`.** -/
theorem va_gate {Z : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om1) : ∀ c, TlCl Z c → c < vaB2 → yrG c < Z := by
  have hZa : ∀ u v, u < Z → v < Z → u + v < Z := fun u v hu hv => hZ.isPrincipal hu hv
  have hZp : ∀ u v, u < Z → v < Z → veblen u v < Z := fun u v hu hv => hZ.2 u hu v hv
  have hZw : ∀ u, u < Z → ω ^ u < Z := fun u hu => by
    have := hZp 0 u hZ.1 hu; rwa [veblen_zero_apply] at this
  have hωZ : ω < Z := omega0_lt_inE (Low.opow_eq_self_of_SC hZ)
  have hlow : ∀ c, TlCl Z c → c < tfBG → yrG c < Z := fun c hc hcB =>
    zmYr.gate c Z hZ hZ1 hZ.1 hcB hc
  intro c hc
  induction hc with
  | @small x h => exact fun _ => hlow _ (TlCl.small h) ((h.trans_le hZ1).trans tfBG_gt)
  | om => exact fun _ => hlow _ TlCl.om tfBG_gt
  | @add x y hx hy ihx ihy =>
    intro h
    exact yr_add hZa hωZ x y (ihx (lt_of_le_of_lt le_self_add h)) (ihy (lt_of_le_of_lt le_add_self h))
  | @phi x y hx hy ihx ihy =>
    intro h
    rcases lt_or_ge (veblen x y) tfBG with hlt | hge
    · exact hlow _ (TlCl.phi hx hy) hlt
    have hgy := ihy (lt_of_le_of_lt (right_le_veblen x y) h)
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [veblen_zero_apply]
      exact yr_opow_gate hZw hωZ y hgy
    · exact yr_phi_gate hωZ hx0 (va_G_le_BG.trans hge) (ihx (lt_of_le_of_lt (left_le_veblen x y) h)) hgy
  | @atom β y hβ hy h1 _ ihy =>
    intro h
    rcases lt_or_ge (rhF β y) tfBG with hlt | hge
    · exact hlow _ (TlCl.atom hβ hy h1) hlt
    have hA : YhAt (rhF β y) := ⟨rhF_SC β y, h1⟩
    rcases va_atom_cases2 hge h with heq | ⟨-, hjB, hjE⟩ | hnA
    · rw [heq, yrG_base (Low.opow_eq_self_of_SC tfBG_SC) va_G_le_BG, va_QE_BG]; exact hZ.1
    · -- an atom `Γ(j)`: `β = 0` and the index is `y`
      obtain ⟨j, hj⟩ := yhAt_iff.1 hA
      have hJ : yhJ (rhF β y) = j := by rw [hj, yhJ_gcG]
      rw [hJ] at hjB hjE
      have hjg : j < gcG j := by rw [← hj]; exact hjE
      have hβ0 : β = 0 := by
        by_contra hβ
        have hfix : gamma (rhF β y) = rhF β y := by
          have := rhF_fix_lower (pos_iff_ne_zero.2 hβ) y; rwa [rhF_zero] at this
        exact absurd h (not_lt.2 (va_B2_min (hjB.trans hjE) hfix))
      subst hβ0
      have hBE : InE tfBG := Low.opow_eq_self_of_SC tfBG_SC
      have hjy : y = j := by
        have e1 : gamma y = gamma (Om1 + 1 + j) := by rw [← tf_gcG, ← hj, rhF_zero]
        have e2 := gamma_inj.1 e1
        obtain ⟨d, hd⟩ := exists_add_of_le hjB.le
        rw [e2, hd, ← add_assoc, gl_absorb hBE tfBG_gt]
      have hyB : y < vaB2 := (rhF_le_self 0 y).trans_lt h
      rw [hj, yrG_atom hjg]
      rw [hjy] at hyB ihy
      exact (yrQ_le j).trans_lt (ihy hyB)
    · exact absurd hA hnA

theorem va_cl_lam {Z : Ordinal.{0}} (hZ : 0 < Z) (α : Ordinal.{0}) {η : Ordinal.{0}} (h : TlCl Z η) :
    TlCl Z (glLam α η) := by
  by_cases hF : glFw α η
  · rw [glLam_of hF]; exact TlCl.add h (TlCl.one hZ)
  · rw [glLam_of_not hF]
    refine TlCl.add ?_ h
    unfold glY0
    split_ifs
    · exact TlCl.add TlCl.om (TlCl.one hZ)
    · exact TlCl.one hZ
    · exact TlCl.zero hZ

theorem va_cl_psi {Z : Ordinal.{0}} (hZ : 0 < Z) {α η : Ordinal.{0}} (hα : TlCl Z α) (hη : TlCl Z η) :
    TlCl Z (yhPsi α η) := by
  unfold yhPsi
  split_ifs
  · exact TlCl.phi hα (va_cl_lam hZ α (TlCl.add (TlCl.one hZ) hη))
  · exact TlCl.phi hα (va_cl_lam hZ α hη)

/-- **`Γ_{B_Γ+1} < X`.** -/
theorem va_U_lt_X : vaU < tlX := by
  have hBE : InE tfBG := Low.opow_eq_self_of_SC tfBG_SC
  have e : Om1 + 1 + (tfBG + 1) = tfBG + 1 := by rw [← add_assoc, gl_absorb hBE tfBG_gt]
  unfold vaU
  rw [tf_gcG, e]
  have h1 : tfBG + 1 < tlX := (ev_isSuccLimit_of_inE (Low.opow_eq_self_of_SC tlX_SC)).add_one_lt tl_BG_lt_X
  have h2 := gamma_lt_gamma.2 h1
  rwa [tl_gamma_X] at h2

/-! ## The union -/

section Union

variable {E : Ordinal.{0}} (hE : InE E) (hBE : tfBG < E) (hEU : E < vaB2)
  (hlim : ∀ e, InE e → e < E → eN e < E) (hIH : ∀ e, InE e → tfBG ≤ e → e < E → VaGood e)

include hE hBE hEU hlim hIH

/-- A code below `E` with gate below a strongly critical `Z` above the base gate is a code over `Z`. -/
theorem va_cl_code {Z : Ordinal.{0}} (hZ : SC Z) {c : Ordinal.{0}} (hc : c < E) (hg : yrG c < Z) : TlCl Z c := by
  have hωZ : ω < Z := omega0_lt_inE (Low.opow_eq_self_of_SC hZ)
  obtain ⟨e, M, -, -, -, -, -, hcM, -, -, -, hEg, -, -, hG, -⟩ := va_mem hEU hlim hIH hBE hc
  exact M.cl c Z hZ hcM (va_memG hωZ hEg hg hG hcM hg)

/-- **A member whose base reading is below `vA E`** at every base above the gates. -/
theorem va_memV (htop : ∀ y, InE y → y < Om1 → max ω (yrQE E) < y → ∀ c, c < E → yrG c < y →
      vR c y < vA E y) {c : Ordinal.{0}} (hc : c < E) :
    ∃ M : ZmDS, c < M.E ∧ M.E < E ∧ M.Eg ≤ max ω (yrG c) ∧
      (∀ y, InE y → y < Om1 → max ω (yrQE E) < y → yrG c < y → M.V y ≤ vA E y) ∧
      (∀ c', c' < M.E → ∀ y, InE y → y < Om1 → M.G c' < y → M.R c' y = vR c' y) ∧
      (∀ c', c' < M.E → c' ≠ 0 → M.G c' = max M.Eg (yrG c')) ∧ M.Dv = ywV 1 0 := by
  obtain ⟨e, M, he, heB, -, hemax, hME, hcM, hMlt, -, hEgeq, hEg, hV, hR, hG, hDv⟩ := va_mem hEU hlim hIH hBE hc
  refine ⟨M, hcM, hMlt, hEg, fun y hy hy1 hgy hg => ?_, hR, hG, hDv⟩
  have hωy : ω < y := omega0_lt_inE hy
  have hyl : IsSuccLimit y := ev_isSuccLimit_of_inE hy
  have hgM : M.Eg < y := hEg.trans_lt (max_lt hωy hg)
  have hMEE : InE M.E := by rw [hME]; exact eN_E e
  have hGME : gcG 0 ≤ M.E := (va_G_le_BG.trans heB).trans (hME ▸ (lt_eN e).le)
  have heU : e < vaB2 := (hemax.trans_lt (max_lt hc hBE)).trans hEU
  have hgME : yrG M.E < y := by
    rw [yrG_base hMEE hGME, hME]
    exact va_QE_eN_lt he heB heU hyl hωy ((le_max_right _ _).trans_lt (hEgeq ▸ hgM))
  have hlt := htop y hy hy1 hgy M.E hMlt hgME
  rw [vR_base hMEE hGME, ← (hV y hy hy1 hgM).2] at hlt
  exact hlt.le

open Classical in
/-- **THE UNION AT A LIMIT `ε`-NUMBER BASE.** -/
noncomputable def vaCU (hnA : ¬ YhAt E) : ZmDS where
  E := E
  Ei := if yhK E = 1 then glLam 1 (yhI E) else E
  V := fun x => if max ω (yrQE E) < x then vA E x else 1
  W := fun x => if yhK E = 1 then vR (yhI E) x + 1 else vA E x
  R := vR
  G := fun c => if c = 0 then 0 else max (max ω (yrQE E)) (yrG c)
  Eg := max ω (yrQE E)
  B := tfBG
  Dv := ywV 1 0
  E_eq := by
    obtain ⟨-, -, hk1, -, -, hpsi⟩ := va_dat hE hBE hEU hnA
    split_ifs with h1
    · have h := hpsi
      rw [h1, yhPsi_ne va_one_notAt] at h
      exact h
    · have hk2 : 1 < yhK E := lt_of_le_of_ne hk1 (Ne.symm h1)
      have hPe : LuP (yhK E) E := by have := yhPsi_P (yhK E) (yhI E); rwa [hpsi] at this
      exact luP_succ.1 (luP_mono le_add_self (add_one_le_of_lt hk2) hPe)
  BG_le := hBE.le
  B_le := hBE.le
  BG_B := le_rfl
  B_cl := fun _ hZ => zbBG_tl hZ.1
  Dv_T := fun x hx hx1 => zmD_T hx hx1
  Dv_pi := fun _ _ hB => zmD_pi hB
  E_X := hEU.trans va_B2_lt_X
  Ei_cl := fun Z hZ hgZ => by
    obtain ⟨hnA, -, hk1, hkE, hiE, hpsi⟩ := va_dat hE hBE hEU hnA
    have hωZ : ω < Z := omega0_lt_inE (Low.opow_eq_self_of_SC hZ)
    have hQ := yrQE_psi hnA
    have hQle : max (yrQ (yhK E)) (yrQ (yhI E)) < Z := by rw [← hQ]; exact (le_max_right _ _).trans_lt hgZ
    have hk := va_cl_code hE hBE hEU hlim hIH hZ hkE (yrG_of_Q hωZ ((le_max_left _ _).trans_lt hQle))
    have hi := va_cl_code hE hBE hEU hlim hIH hZ hiE (yrG_of_Q hωZ ((le_max_right _ _).trans_lt hQle))
    split_ifs with h1
    · exact va_cl_lam hZ.1 1 hi
    · have h := va_cl_psi hZ.1 hk hi; rwa [hpsi] at h
  nfx := fun y h1 h2 hΓ => absurd (h2.trans_lt hEU) (not_lt.2 (va_B2_min h1 hΓ))
  Eg_le := fun c hc0 => by
    show max ω (yrQE E) ≤ (if c = 0 then 0 else max (max ω (yrQE E)) (yrG c))
    rw [if_neg hc0]; exact le_max_left _ _
  V_T := fun x hx hx1 hgx => by
    show (if max ω (yrQE E) < x then vA E x else 1) ∈ Tset x ∧ _
    rw [if_pos hgx]
    obtain ⟨-, -, hv1, hkT, hk1', hiT, hi1, hA⟩ := va_datx hE hBE hEU hlim hIH hx hx1 hnA hgx
    obtain ⟨hVT, -, -, hVE, -, -⟩ := glA_facts hx hx1 hv1 hkT hk1' hiT hi1
    rw [← hA] at hVT hVE
    exact ⟨hVT, hVE, (va_D_lt hE hBE hEU hlim hIH hx hx1 hnA hgx).le,
      (va_V_lt_D2 hE hBE hEU hlim hIH hx hx1 hnA hgx).trans (va_D2_facts hx hx1).2.2.2.2⟩
  Vq := fun x hx hx1 hgx => by
    show ∃ σ, σ ∈ Tset x ∧ σ < Om1 ∧ σ < ywV 1 0 x + (if max ω (yrQE E) < x then vA E x else 1) ∧
      (if max ω (yrQE E) < x then vA E x else 1) < gq σ x
    rw [if_pos hgx]
    obtain ⟨-, -, hv1, hkT, hk1', hiT, hi1, hA⟩ := va_datx hE hBE hEU hlim hIH hx hx1 hnA hgx
    obtain ⟨hVT, -, -, -, -, -⟩ := glA_facts hx hx1 hv1 hkT hk1' hiT hi1
    rw [← hA] at hVT
    obtain ⟨σ, hσT, hσ1, hσV, hVσ⟩ := va_nonclosed hx hx1 hVT (va_D_lt hE hBE hEU hlim hIH hx hx1 hnA hgx)
      (va_V_lt_D2 hE hBE hEU hlim hIH hx hx1 hnA hgx)
    exact ⟨σ, hσT, hσ1, hσV.trans_le le_add_self, hVσ⟩
  W_T := fun x hx hx1 hgx => by
    obtain ⟨-, -, hk1, hkE, -, -⟩ := va_dat hE hBE hEU hnA
    obtain ⟨hgk, -, hv1, hkT, hk1', hiT, hi1, hA⟩ := va_datx hE hBE hEU hlim hIH hx hx1 hnA hgx
    show (if yhK E = 1 then vR (yhI E) x + 1 else vA E x) ∈ Tset x ∧
      (if yhK E = 1 then vR (yhI E) x + 1 else vA E x) < Om1 ∧
      eN (if max ω (yrQE E) < x then vA E x else 1) = glA 1 (if yhK E = 1 then vR (yhI E) x + 1 else vA E x) x
    rw [if_pos hgx]
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
        have h := va_le_mono hE hBE hEU hlim hIH hx hx1 hk2 hkE hg2 hgk
        have hv : vR 2 x = 2 := by have := vR_nat 2 x; rwa [e2] at this
        rwa [hv] at h
      obtain ⟨hVT, -, hV1, -, -, -⟩ := glA_facts hx hx1 hv1 hkT hk1' hiT hi1
      rw [← hA] at hVT hV1
      refine ⟨hVT, hV1, ?_⟩
      rw [hA]; exact glA_eN_two hx hx1 hv2 hkT hk1' hiT hi1
  V_pi := fun σ ρ hB hgσ => by
    obtain ⟨-, -, -, hkE, hiE, -⟩ := va_dat hE hBE hEU hnA
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
    have hgρ := hgσ.trans hB.2.2.1
    obtain ⟨hgk, hgi, -, -, hk1', -, hi1, hA⟩ := va_datx hE hBE hEU hlim hIH hB.2.1 hρ1 hnA hgρ
    obtain ⟨hgkσ, hgiσ, -, -, -, -, -, hAσ⟩ := va_datx hE hBE hEU hlim hIH hB.1 hσ1 hnA hgσ
    have hex : ∀ c, c < E → yrG c < σ → vR c ρ ∈ TB ρ σ ∧ R2.pi σ ρ (vR c ρ) = vR c σ := by
      intro c hc hgc
      obtain ⟨M, hcM, -, hEg, -, hR, hG, -⟩ := va_memV hE hBE hEU hlim hIH (va_ltT hE hBE hEU hlim hIH hnA) hc
      have hGc := va_memG (omega0_lt_inE hB.1) hEg hgc hG hcM hgc
      rw [← hR c hcM ρ hB.2.1 hρ1 (hGc.trans hB.2.2.1), ← hR c hcM σ hB.1 hσ1 hGc]
      exact M.ex σ ρ c hB hcM hGc
    obtain ⟨k1, k2⟩ := hex _ hkE hgkσ
    obtain ⟨i1, i2⟩ := hex _ hiE hgiσ
    obtain ⟨a1, a2⟩ := glA_pi hB k1 hk1' i1 hi1
    rw [k2, i2, ← hAσ] at a2
    show (if max ω (yrQE E) < ρ then vA E ρ else 1) ∈ TB ρ σ ∧
      R2.pi σ ρ (if max ω (yrQE E) < ρ then vA E ρ else 1) = (if max ω (yrQE E) < σ then vA E σ else 1)
    rw [if_pos hgρ, if_pos hgσ, hA]; exact ⟨a1, a2⟩
  W_pi := fun σ ρ hB hgσ => by
    obtain ⟨-, -, -, hkE, hiE, -⟩ := va_dat hE hBE hEU hnA
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
    have hgρ := hgσ.trans hB.2.2.1
    obtain ⟨hgk, hgi, -, -, hk1', -, hi1, hA⟩ := va_datx hE hBE hEU hlim hIH hB.2.1 hρ1 hnA hgρ
    obtain ⟨hgkσ, hgiσ, -, -, -, -, -, hAσ⟩ := va_datx hE hBE hEU hlim hIH hB.1 hσ1 hnA hgσ
    have hex : ∀ c, c < E → yrG c < σ → vR c ρ ∈ TB ρ σ ∧ R2.pi σ ρ (vR c ρ) = vR c σ := by
      intro c hc hgc
      obtain ⟨M, hcM, -, hEg, -, hR, hG, -⟩ := va_memV hE hBE hEU hlim hIH (va_ltT hE hBE hEU hlim hIH hnA) hc
      have hGc := va_memG (omega0_lt_inE hB.1) hEg hgc hG hcM hgc
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
      · exact lt_of_le_of_lt zero_le (va_D_lt hE hBE hEU hlim hIH hx hx1 hnA hgx)
      · exact zero_lt_one
    · rw [if_neg hc0] at hg
      rw [if_pos ((le_max_left _ _).trans_lt hg)]
      exact va_lt_top hE hBE hEU hlim hIH hx hx1 hnA ((le_max_left _ _).trans_lt hg) c hc
        ((le_max_right _ _).trans_lt hg)
  pos := fun c x hx hx1 hc0 hc hg => by
    change (if c = 0 then 0 else max (max ω (yrQE E)) (yrG c)) < x at hg
    rw [if_neg hc0] at hg
    have h := va_mono hE hBE hEU hlim hIH hx hx1 (pos_iff_ne_zero.2 hc0) hc (by rw [yrG_zero]; exact hx.pos)
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
    exact va_mono hE hBE hEU hlim hIH hx hx1 hbc hc hgb' ((le_max_right _ _).trans_lt hgc)
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
    obtain ⟨M, hcM, -, hEg, -, hR, hG, -⟩ := va_memV hE hBE hEU hlim hIH (va_ltT hE hBE hEU hlim hIH hnA) hc
    have hGc := va_memG (omega0_lt_inE hx) hEg ((le_max_right _ _).trans_lt hg) hG hcM ((le_max_right _ _).trans_lt hg)
    rw [← hR c hcM x hx hx1 hGc]
    exact M.lim c x hx hx1 hl hcM hGc
  nc := fun c x hx hx1 hl hc hg => by
    change (if c = 0 then 0 else max (max ω (yrQE E)) (yrG c)) < x at hg
    rw [if_neg (show c ≠ 0 from hl.bot_lt.ne')] at hg
    obtain ⟨M, hcM, -, hEg, -, hR, hG, hDv⟩ := va_memV hE hBE hEU hlim hIH (va_ltT hE hBE hEU hlim hIH hnA) hc
    have hGc := va_memG (omega0_lt_inE hx) hEg ((le_max_right _ _).trans_lt hg) hG hcM ((le_max_right _ _).trans_lt hg)
    show ∃ σ, σ ∈ Tset x ∧ σ < Om1 ∧ σ < ywV 1 0 x + vR c x ∧ ywV 1 0 x + vR c x < gq σ x
    rw [← hR c hcM x hx hx1 hGc]
    have h := M.nc c x hx hx1 hl hcM hGc
    rw [hDv] at h
    exact h
  cof := fun c x hx hx1 hl hc hg ν hν => by
    change (if c = 0 then 0 else max (max ω (yrQE E)) (yrG c)) < x at hg
    rw [if_neg (show c ≠ 0 from hl.bot_lt.ne')] at hg
    obtain ⟨b, hbc, hgb, hνb⟩ := va_below hE hBE hEU hlim hIH hx hx1 hc (show c ≠ 0 from hl.bot_lt.ne')
      ((le_max_right _ _).trans_lt hg) ν hν
    refine ⟨b, hbc, ?_, hνb⟩
    show (if b = 0 then 0 else max (max ω (yrQE E)) (yrG b)) < x
    split_ifs
    · exact hx.pos
    · exact max_lt ((le_max_left _ _).trans_lt hg) hgb
  top := fun x hx hx1 hgx ν hν => by
    change ν < (if max ω (yrQE E) < x then vA E x else 1) at hν
    rw [if_pos hgx] at hν
    obtain ⟨b, hb, hgb, hνb⟩ := va_top hE hBE hEU hlim hIH hx hx1 hnA hgx ν hν
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
    obtain ⟨M, hcM, -, hEg, -, hR, hG, -⟩ := va_memV hE hBE hEU hlim hIH (va_ltT hE hBE hEU hlim hIH hnA) hc
    have hGc := va_memG (omega0_lt_inE hB.1) hEg ((le_max_right _ _).trans_lt hg) hG hcM
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
    obtain ⟨M, hdM, -, hEg, hVle, hR, hG, -⟩ := va_memV hE hBE hEU hlim hIH (va_ltT hE hBE hEU hlim hIH hnA) hd
    have hGd := va_memG (omega0_lt_inE hB.1) hEg ((le_max_right _ _).trans_lt hg) hG hdM
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
    exact va_cl_code hE hBE hEU hlim hIH hZ hc ((le_max_right _ _).trans_lt hg)
  gate := fun c Z hZ hZ1 hgZ hc h => by
    show (if c = 0 then 0 else max (max ω (yrQE E)) (yrG c)) < Z
    split_ifs
    · exact hZ.1
    · exact max_lt hgZ (va_gate hZ hZ1 c h (hc.trans hEU))

/-- **The union is a system read by `vR`.** -/
theorem vaGood_lim (hnA : ¬ YhAt E) : VaGood E := by
  refine ⟨vaCU hE hBE hEU hlim hIH hnA, rfl, rfl, fun x _ _ hgx => ?_, fun c _ x _ _ _ => rfl, fun c _ hc0 => ?_, rfl,
    rfl⟩
  · have hgx' : max ω (yrQE E) < x := hgx
    show (if max ω (yrQE E) < x then vA E x else 1) = vA E x
    rw [if_pos hgx']
  · show (if c = 0 then 0 else max (max ω (yrQE E)) (yrG c)) = max (max ω (yrQE E)) (yrG c)
    rw [if_neg hc0]

end Union

/-- **A DIGIT SYSTEM READ BY `vR` AT EVERY `ε`-NUMBER BASE `B_Γ ≤ E < Γ_{B_Γ+1}`.** -/
theorem vaGood_all : ∀ E, InE E → tfBG ≤ E → E < vaU → VaGood E := by
  intro E
  induction E using WellFoundedLT.induction with
  | ind E IH =>
  intro hE hBE hEU
  rcases hBE.lt_or_eq with hlt | heq
  swap
  · rw [← heq]; exact vaGood_BG
  by_cases hs : ∃ e, InE e ∧ tfBG ≤ e ∧ e < E ∧ eN e = E
  · obtain ⟨e, he, heB, heE, rfl⟩ := hs
    exact vaGood_succ he heB ((heE.trans hEU).trans_le va_U_le_B2) (IH e heE he heB (heE.trans hEU))
  · have hlim : ∀ e, InE e → e < E → eN e < E := by
      intro e he heE
      refine lt_of_le_of_ne (eN_le heE hE) fun h => ?_
      rcases lt_or_ge e tfBG with heB | heB
      · have h1 : eN e ≤ tfBG := eN_le heB (Low.opow_eq_self_of_SC tfBG_SC)
        rw [h] at h1
        exact absurd hlt (not_lt.2 h1)
      · exact hs ⟨e, he, heB, heE, h⟩
    have hnA : ¬ YhAt E := by
      rcases va_atom_cases hlt.le hEU with h | h
      · exact absurd h hlt.ne'
      · exact h
    exact vaGood_lim hE hlt (hEU.trans_le va_U_le_B2) hlim (fun e he heB heE => IH e heE he heB (heE.trans hEU)) hnA

end Googology.Trans.PoR.InaccPsi.R2.Va
