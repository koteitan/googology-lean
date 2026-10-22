import Googology.Trans.PoR.InaccPsi.R2.LxZS
import Googology.Trans.PoR.InaccPsi.R2.LxFam

/-!
# The layer `lxZ = lxZLay lgLay` (top `ε_{Γ(x)+x}`, code `ε_{Γ_{Ω₁+1}+Ω₁}`): codes, frontier, ENUM-REACH, road

The instance `K = lgLay` (`E_K = Γ`, `lxZK_lg`) of `R2.LxZS`: the layer of the terms below
`e_x(x) = ϑˣ(Ω₁ + Γ(x) + x) = ε_{Γ(x)+x}` (the atoms `e_c(x) = ε_{Γ(x)+1+c}`, `c < x`).

* `lx_eps_code` (**an `ε`-number code `e` with `Γ_{Ω₁+1} < e < ε_{Γ_{Ω₁+1}+Ω₁}` is `φ(1, i)` with a code `i`**: by
  induction on the code; `φ(a, b)` with `a ≥ 2` is a fixed point of `φ(1, ·)` and too large);
* `lxTh_P` (**`Θ'_y(ε_{Γ_{Ω₁+1}+1+j}) = e_j(y)`** for `j < y`), `lxTh_ZC` (**`Θ'_y(ε_{Γ_{Ω₁+1}+Ω₁}) = e_y(y)`**): `Θ'_y`
  keeps the `ε`-numbers, is onto an initial segment, and `lxZE_enum` lists the `ε`-numbers above `Γ(y)`;
* `lxZ_poly` (**`LgPoly lxZ (ε_{Γ_{Ω₁+1}+Ω₁})`**), `lxZ_top`;
* `lxZ_loc` (**`Λ⁺(lxZ) = ι(ε_{Γ_{Ω₁+1}+Ω₁}·ω)`, `ρ` of it `= P(…) < L(0)`**), `lxZT_fix`, `lxZEnum` (**ENUM-REACH at
  every restart of the range below `Λ⁺(lxZ)`**, fixed points included), `lxZ_capV`, `lxZ_blk`, `lxZRoad`,
  `lxFam_lt_Z` (**`sup_n Λ⁺(lxK n) = ι(ε_{Γ_{Ω₁+1}+ω}) < Λ⁺(lxZ)`**), `lxZ_fr_order`.

No new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Lx

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Cd
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Ly Googology.Trans.PoR.InaccPsi.R2.Cp Googology.Trans.PoR.InaccPsi.R2.Nm

/-! ## Codes -/

/-- **The code `ε_{Γ_{Ω₁+1}+Ω₁}`** (`= φ(1, Γ_{Ω₁+1} + Ω₁)`) of the top of `lxZ`. -/
noncomputable def lxZC : Ordinal.{0} := veblen 1 (ggGam + Om 1)

theorem lx_cl_ZC {Z : Ordinal.{0}} (hZ : SC Z) : LgCl Z lxZC :=
  LgCl.phi (LgCl.small (gg_one_lt_of_SC hZ)) (LgCl.add LgCl.gam LgCl.om)

theorem lx_vG : veblen 1 ggGam = ggGam := ggGam_spec.1.veblen_right (gg_one_lt_of_SC ggGam_spec.1)

theorem lx_Om1_le_ZC : Om 1 ≤ lxZC := ggGam_spec.2.le.trans (le_self_add.trans (right_le_veblen _ _))

theorem lx_G_lt_veblen {i : Ordinal.{0}} (h : ggGam < veblen 1 i) : ggGam < i := by
  rw [← lx_vG] at h; exact veblen_lt_veblen_iff_right.1 h

/-- An `ε`-number is a value of `φ(1, ·)`. -/
theorem lx_range1 {e : Ordinal.{0}} (he : ω ^ e = e) : ∃ i, veblen 1 i = e :=
  (mem_range_veblen one_ne_zero).2 fun b hb => by rw [Order.lt_one_iff.1 hb, veblen_zero_apply]; exact he

/-- **An `ε`-number code `e` with `Γ_{Ω₁+1} < e < ε_{Γ_{Ω₁+1}+Ω₁}` is `φ(1, i)` with a code `i`.** -/
theorem lx_eps_code {Z : Ordinal.{0}} (hZ1 : Z < Om 1) {e : Ordinal.{0}} (he : LgCl Z e) :
    ω ^ e = e → ggGam < e → e < lxZC → ∃ i, LgCl Z i ∧ e = veblen 1 i := by
  induction he with
  | small h => intro _ hG _; exact absurd (h.trans (hZ1.trans ggGam_spec.2)) (not_lt.2 hG.le)
  | om => intro _ hG _; exact absurd ggGam_spec.2 (not_lt.2 hG.le)
  | gam => intro _ hG _; exact absurd hG (lt_irrefl _)
  | @add x y hx hy ihx ihy =>
    intro hE hG hT
    have hp : IsPrincipal (· + ·) (x + y) := by rw [← hE]; exact isPrincipal_add_omega0_opow _
    rcases eq_or_lt_of_le (le_self_add : x ≤ x + y) with h1 | h1
    · obtain ⟨i, hi, e⟩ := ihx (by rw [h1]; exact hE) (by rw [h1]; exact hG) (by rw [h1]; exact hT)
      exact ⟨i, hi, by rw [← h1]; exact e⟩
    · rcases eq_or_lt_of_le (le_add_self : y ≤ x + y) with h2 | h2
      · obtain ⟨i, hi, e⟩ := ihy (by rw [h2]; exact hE) (by rw [h2]; exact hG) (by rw [h2]; exact hT)
        exact ⟨i, hi, by rw [← h2]; exact e⟩
      · exact absurd (hp h1 h2) (lt_irrefl _)
  | @phi a b ha hb iha ihb =>
    intro hE hG hT
    rcases eq_or_ne a 0 with rfl | ha0
    · rw [veblen_zero_apply] at hE hG hT
      have hbE : ω ^ b = b := opow_inj hE
      obtain ⟨i, hi, e⟩ := ihb hbE (by rw [← hbE]; exact hG) (by rw [← hbE]; exact hT)
      exact ⟨i, hi, by rw [veblen_zero_apply, hbE, e]⟩
    · rcases eq_or_ne a 1 with rfl | ha1
      · exact ⟨b, hb, rfl⟩
      · have h1a : 1 < a := lt_of_le_of_ne (one_le_iff_ne_zero.2 ha0) (Ne.symm ha1)
        have hfix : veblen 1 (veblen a b) = veblen a b := veblen_veblen_of_lt h1a b
        have h2 : veblen a b < ggGam + Om 1 := by
          rw [← hfix] at hT; exact veblen_lt_veblen_iff_right.1 hT
        have hp : IsPrincipal (· + ·) (veblen a b) := by rw [← hE]; exact isPrincipal_add_omega0_opow _
        exact absurd (hp hG (ggGam_spec.2.trans hG)) (not_lt.2 h2.le)

/-- A code whose reading is an `ε`-number is an `ε`-number. -/
theorem lxTh_eps_of {y e : Ordinal.{0}} (hy : SC y) (he : LgCl y e) (hE : ω ^ lgTh y e = lgTh y e) :
    ω ^ e = e := by
  by_contra hne
  have hlt : e < ω ^ e := lt_of_le_of_ne (right_le_opow _ one_lt_omega0) (Ne.symm hne)
  have h2 := lgTh_lt he hlt
  rw [lgTh_opow hy he, hE] at h2
  exact lt_irrefl _ h2

theorem lx_cl_d {Z j : Ordinal.{0}} (hZ : SC Z) (hj : j < Z) : LgCl Z (veblen 1 (ggGam + 1 + j)) :=
  LgCl.phi (LgCl.small (gg_one_lt_of_SC hZ))
    (LgCl.add (LgCl.add LgCl.gam (LgCl.small (gg_one_lt_of_SC hZ))) (LgCl.small hj))

theorem lx_d_lt_ZC {j : Ordinal.{0}} (hj : j < Om 1) : veblen 1 (ggGam + 1 + j) < lxZC := by
  refine veblen_lt_veblen_iff_right.2 ?_
  rw [add_assoc]
  refine (add_lt_add_iff_left _).2 ?_
  have hp : IsPrincipal (· + ·) (Om (1 : Ordinal.{0})) := by
    rw [← Om1_opow]; exact isPrincipal_add_omega0_opow _
  exact hp (gg_one_lt_of_SC ph_SC_Om1) hj

/-- **`Θ'_y(ε_{Γ_{Ω₁+1}+1+j}) = e_j(y)`** for `j < y`. -/
theorem lxTh_P {y : Ordinal.{0}} (hy : SC y) (hy1 : y < Om 1) :
    ∀ j, j < y → lgTh y (veblen 1 (ggGam + 1 + j)) = lxZE lgLay y j := by
  have hyE : InE y := gg_SC_eps hy
  have hy1' : y < Om1 := lx_y1 hy1
  have hyO : y < Om 1 := hy1
  intro j
  induction j using WellFoundedLT.induction with
  | ind j IH =>
  intro hjy
  have hdcl : LgCl y (veblen 1 (ggGam + 1 + j)) := lx_cl_d hy hjy
  have hdE : ω ^ veblen 1 (ggGam + 1 + j) = veblen 1 (ggGam + 1 + j) := gg_veblen_eps one_ne_zero
  have hGd : ggGam < veblen 1 (ggGam + 1 + j) := by
    calc ggGam = veblen 1 ggGam := lx_vG.symm
      _ < veblen 1 (ggGam + 1 + j) :=
        veblen_lt_veblen_iff_right.2 ((lt_add_one _).trans_le le_self_add)
  have hThE : ω ^ lgTh y (veblen 1 (ggGam + 1 + j)) = lgTh y (veblen 1 (ggGam + 1 + j)) := by
    rw [← lgTh_opow hy hdcl, hdE]
  have hGlt : lgG y < lgTh y (veblen 1 (ggGam + 1 + j)) := by
    rw [← lgTh_Gam hy hyO]; exact lgTh_lt LgCl.gam hGd
  apply le_antisymm
  · by_contra hlt
    push Not at hlt
    obtain ⟨e, he, hed, hev⟩ := lgTh_onto hlt
    have hjE := (lxZE_facts lxZK_lg hyE hy1' hjy.le).2.2.2.2.2.1
    have heE : ω ^ e = e := lxTh_eps_of hy he (by rw [hev]; exact hjE)
    have hGe : ggGam < e := by
      by_contra hle
      push Not at hle
      have h2 := lgTh_mono (y := y) hle
      rw [hev, lgTh_Gam hy hyO] at h2
      exact absurd (lxZE_E_lt lxZK_lg hyE hy1' hjy.le) (not_lt.2 h2)
    obtain ⟨i, -, rfl⟩ := lx_eps_code hyO he heE hGe (hed.trans (lx_d_lt_ZC (hjy.trans hyO)))
    have hGi := lx_G_lt_veblen hGe
    obtain ⟨t, rfl⟩ := exists_add_of_le (Order.add_one_le_of_lt hGi)
    have htj : t < j := (add_lt_add_iff_left _).1 (veblen_lt_veblen_iff_right.1 hed)
    rw [IH t htj (htj.trans hjy)] at hev
    exact absurd hev (lxZE_strict lxZK_lg hyE hy1' htj hjy.le).ne
  · by_contra hlt
    push Not at hlt
    obtain ⟨t, htj, ht⟩ := lxZE_enum lxZK_lg hyE hy1' hjy.le hThE hGlt hlt
    have hdt : veblen 1 (ggGam + 1 + t) < veblen 1 (ggGam + 1 + j) :=
      veblen_lt_veblen_iff_right.2 ((add_lt_add_iff_left _).2 htj)
    have h2 := lgTh_lt (lx_cl_d hy (htj.trans hjy)) hdt
    rw [IH t htj (htj.trans hjy), ← ht] at h2
    exact lt_irrefl _ h2

/-- **`Θ'_y(ε_{Γ_{Ω₁+1}+Ω₁}) = e_y(y)`.** -/
theorem lxTh_ZC {y : Ordinal.{0}} (hy : SC y) (hy1 : y < Om 1) : lgTh y lxZC = lxZE lgLay y y := by
  have hyE : InE y := gg_SC_eps hy
  have hy1' : y < Om1 := lx_y1 hy1
  have hTcl := lx_cl_ZC hy
  have hTE : ω ^ lxZC = lxZC := gg_veblen_eps one_ne_zero
  have hGT : ggGam < lxZC := by
    calc ggGam = veblen 1 ggGam := lx_vG.symm
      _ < lxZC := veblen_lt_veblen_iff_right.2 (lt_add_of_pos_right _ ph_SC_Om1.1)
  have hThE : ω ^ lgTh y lxZC = lgTh y lxZC := by rw [← lgTh_opow hy hTcl, hTE]
  have hGlt : lgG y < lgTh y lxZC := by rw [← lgTh_Gam hy hy1]; exact lgTh_lt LgCl.gam hGT
  apply le_antisymm
  · by_contra hlt
    push Not at hlt
    obtain ⟨e, he, heT, hev⟩ := lgTh_onto hlt
    have hjE := (lxZE_facts lxZK_lg hyE hy1' le_rfl).2.2.2.2.2.1
    have heE : ω ^ e = e := lxTh_eps_of hy he (by rw [hev]; exact hjE)
    have hGe : ggGam < e := by
      by_contra hle
      push Not at hle
      have h2 := lgTh_mono (y := y) hle
      rw [hev, lgTh_Gam hy hy1] at h2
      exact absurd (lxZE_E_lt lxZK_lg hyE hy1' le_rfl) (not_lt.2 h2)
    obtain ⟨i, hi, rfl⟩ := lx_eps_code hy1 he heE hGe heT
    have hGi := lx_G_lt_veblen hGe
    obtain ⟨t, rfl⟩ := exists_add_of_le (Order.add_one_le_of_lt hGi)
    have hG1 : LgCl y (ggGam + 1) := LgCl.add LgCl.gam (LgCl.small (gg_one_lt_of_SC hy))
    have htc : LgCl y t := by
      have := (lgDec hy _ hi).1 _ hG1 le_self_add
      rwa [Ordinal.add_sub_cancel] at this
    have ht1 : t < Om 1 := by
      have h3 := veblen_lt_veblen_iff_right.1 heT
      rw [add_assoc] at h3
      exact le_add_self.trans_lt ((add_lt_add_iff_left _).1 h3)
    have hty : t < y := htc.lt_of_lt_Om1 hy ht1
    rw [lxTh_P hy hy1 t hty] at hev
    exact absurd hev (lxZE_strict lxZK_lg hyE hy1' hty le_rfl).ne
  · by_contra hlt
    push Not at hlt
    obtain ⟨t, hty, ht⟩ := lxZE_enum lxZK_lg hyE hy1' le_rfl hThE hGlt hlt
    have h2 := lgTh_lt (lx_cl_d hy hty) (lx_d_lt_ZC (hty.trans hy1))
    rw [lxTh_P hy hy1 t hty, ← ht] at h2
    exact lt_irrefl _ h2

/-! ## The layer `lxZ` and its codes -/

/-- **The layer `lxZ`**: the terms below `ε_{Γ(x)+x}`. -/
noncomputable def lxZ : XtLay := lxZLay lgLay lxZK_lg

theorem lx_lgPoly : LgPoly lgLay.sys ggGam := by have h := lqLay_poly; rwa [lg_Gam_eps] at h

/-- **`LgPoly lxZ (ε_{Γ_{Ω₁+1}+Ω₁})`.** -/
theorem lxZ_poly : LgPoly lxZ.sys lxZC := by
  refine lgPoly_of_SC fun Z hZ hZ1 => ?_
  intro d
  induction d using WellFoundedLT.induction with
  | ind d IH =>
  intro hd hdT
  rcases lt_or_ge d (eN ggGam) with h0 | h0
  · obtain ⟨t, ht⟩ := lxExpTm (K := lgLay) hZ (fun y hy hy1 => (lgTh_Gam hy hy1).symm) lx_lgPoly d hd h0
    exact ⟨LxZTm.ex t, fun y hy hy1 hZy => ht y hy hy1 hZy⟩
  have hGd : ggGam < d := (lt_eN _).trans_le h0
  by_cases hdE : ω ^ d = d
  · obtain ⟨i, hi, rfl⟩ := lx_eps_code hZ1 hd hdE hGd hdT
    have hGi := lx_G_lt_veblen hGd
    obtain ⟨t, rfl⟩ := exists_add_of_le (Order.add_one_le_of_lt hGi)
    have hG1 : LgCl Z (ggGam + 1) := LgCl.add LgCl.gam (LgCl.small (gg_one_lt_of_SC hZ))
    have htc : LgCl Z t := by
      have := (lgDec hZ _ hi).1 _ hG1 le_self_add
      rwa [Ordinal.add_sub_cancel] at this
    have ht1 : t < Om 1 := by
      have h3 := veblen_lt_veblen_iff_right.1 hdT
      rw [add_assoc] at h3
      exact le_add_self.trans_lt ((add_lt_add_iff_left _).1 h3)
    have htZ : t < Z := htc.lt_of_lt_Om1 hZ ht1
    refine ⟨LxZTm.ep t, fun y hy hy1 hZy => ⟨lt_of_lt_of_le htZ hZy, ?_⟩⟩
    show lxZE lgLay y t = lgTh y (veblen 1 (ggGam + 1 + t))
    rw [lxTh_P hy hy1 t (lt_of_lt_of_le htZ hZy)]
  · have hd0 : d ≠ 0 := (lt_of_le_of_lt zero_le hGd).ne'
    obtain ⟨hsub, hlog⟩ := lgDec hZ d hd
    set L := log ω d with hL
    have hwd : ω ^ L ≤ d := opow_log_le_self ω hd0
    have hwL : LgCl Z (ω ^ L) := LgCl.opow hZ.1 hlog
    have hr := hsub _ hwL hwd
    have hdec : ω ^ L + (d - ω ^ L) = d := Ordinal.add_sub_cancel_of_le hwd
    rcases eq_or_ne (d - ω ^ L) 0 with hr0 | hr0
    · have hdw : ω ^ L = d := by rw [← hdec, hr0, add_zero]
      have hLd : L < d := by
        refine lt_of_le_of_ne ((right_le_opow L one_lt_omega0).trans hdw.le) (fun e => hdE ?_)
        calc ω ^ d = ω ^ L := by rw [e]
          _ = d := hdw
      obtain ⟨t, ht⟩ := IH L hLd hlog (hLd.trans hdT)
      refine ⟨LxZTm.pw t, fun y hy hy1 hZy => ⟨(ht y hy hy1 hZy).1, ?_⟩⟩
      show ω ^ lxZ.sys.val t y = lgTh y d
      rw [(ht y hy hy1 hZy).2, ← lgTh_opow hy (hlog.mono hZy), hdw]
    · have h1 : ω ^ L < d := by
        rw [← hdec]; exact lt_add_of_pos_right _ (pos_iff_ne_zero.2 hr0)
      have h2 : d - ω ^ L < d := lg_sub_log_lt hd0
      obtain ⟨t1, ht1⟩ := IH _ h1 hwL (h1.trans hdT)
      obtain ⟨t2, ht2⟩ := IH _ h2 hr (h2.trans hdT)
      refine ⟨LxZTm.sm t1 t2, fun y hy hy1 hZy => ⟨⟨(ht1 y hy hy1 hZy).1, (ht2 y hy hy1 hZy).1⟩, ?_⟩⟩
      show lxZ.sys.val t1 y + lxZ.sys.val t2 y = lgTh y d
      rw [(ht1 y hy hy1 hZy).2, (ht2 y hy hy1 hZy).2, ← lgTh_add hy (hwL.mono hZy), hdec]

/-- The top of `lxZ`: `e_y(y) = Θ'_y(ε_{Γ_{Ω₁+1}+Ω₁})`. -/
theorem lxZ_top : ∀ y, SC y → y < Om 1 → lxZ.sys.top y = lgTh y lxZC := fun y hy hy1 =>
  (lxTh_ZC hy hy1).symm

theorem lxZ_topE (x : Ordinal.{0}) (hx : InE x) (hx1 : x < Om1) : eN x < lxZ.sys.top x :=
  ((((eN_le_gT hx hx1 0).trans_lt (gT_lt_lgG hx hx1 0)).trans (lt_eN _))).trans
    (lxz_e0_lt_top lxZK_lg hx hx1)

theorem lxZC_eps : ω ^ lxZC = lxZC := gg_veblen_eps one_ne_zero

theorem lxZC_le_Gam' (S : InaccSeq.{0}) : lxZC ≤ lgGam' := (lgCl_lt_Gam' S (lx_cl_ZC ph_SC_Om1)).le

variable {S : InaccSeq.{0}}

/-- **`Λ⁺(lxZ) = ι(ε_{Γ_{Ω₁+1}+Ω₁}·ω)`, `ρ` of it `= P(…) < L(0)`.** -/
theorem lxZ_loc : xtB1 lxZ.sys = iota S (lxZC * ω) ∧
    upsilon (xtB1 lxZ.sys) = Pv S (lxZC * ω) ∧ Pv S (lxZC * ω) < Nc.ncL S 0 := by
  have h := lgB1_eq2 (S := S) (lxZC_le_Gam' S) lxZ_poly lxZ_top (fun _ hZ => lx_cl_ZC hZ) lx_Om1_le_ZC
    lxZ_topE lxZ.topPkg
  rwa [lxZC_eps] at h

/-- **The notation hypothesis at every fixed point of the range below `Λ⁺(lxZ)`.** -/
theorem lxZT_fix {l : Ordinal.{0}} (hr : CdRange S l) (hlB : l < xtB1 lxZ.sys) (hfix : upsilon l = l) :
    cdTheta S l (cdCode S l) = xtOrec lxZ.sys l := by
  have hlt : l < iota S (ω ^ lxZC * ω) := by rw [lxZC_eps, ← (lxZ_loc (S := S)).1]; exact hlB
  exact lgUniTh (lxZC_le_Gam' S) lxZ_poly hr.1 hfix (cp_name_L hr.2.2.1)
    (phExp_le hr.1 hfix (cp_name_L hr.2.2.1) hlt)

theorem lxZ_nonfix : XtNonfix (xtOrec lxZ.sys) (xtB1 lxZ.sys) :=
  fun _ hμ hww hfix hμB => xtNonfix hμ hww hfix (hμB.trans (xtB1_lt_Om1 lxZ.topPkg))

/-- **ENUM-REACH at every restart of the range below `Λ⁺(lxZ)`**, fixed points of `υ` included. -/
theorem lxZEnum {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtB1 lxZ.sys) : CdUpper S l ∧ CdLower S l := by
  rcases (upsilon_normal.strictMono.le_apply : l ≤ upsilon l).lt_or_eq with hnf | hfx
  · exact xtInit (xtSpec1 lxZ.topPkg) lxZ_nonfix hr hl hnf
  · exact (xtExact_iff (xtSpec1 lxZ.topPkg) hr.1 hl).2 (lxZT_fix hr hl hfx.symm)

/-- **The cap of the values at every non-fixed restart of the range below `Λ⁺(lxZ)`.** -/
theorem lxZ_capV {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtB1 lxZ.sys) (hfix : l < upsilon l) :
    CdCapV S l := by
  have hww := cp_ww_lt_B0.trans_le hr.2.1
  exact xtCapV_nonfix (xtSpec1 lxZ.topPkg) hr.1 hww hfix hl (cp_name_L hr.2.2.1) (lxZ_nonfix l hr.1 hww hfix hl)

/-- **Theorem BLK^O below `υ_{Λ⁺(lxZ)}`** in `R₂^C`, with the exact reaches `lh(ρ_λ) = δ_λ + O_{lxZ}(λ)`. -/
theorem lxZ_blk :
    (∀ c d, c < d → d < upsilon (xtB1 lxZ.sys) → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < xtB1 lxZ.sys ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < xtB1 lxZ.sys →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec lxZ.sys l)) ∧
    (∀ α < upsilon (xtB1 lxZ.sys), ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  xtBlk1 lxZ.topPkg

/-- **The road with UPPER and LOWER asked only at `λ ≥ Λ⁺(lxZ)`**: the rest is CapV at the outer restarts below
`L(ω)`, (CL), EQ, TCrest, (EMB₂). -/
theorem lxZRoad (hU : ∀ l, CdRange S l → xtB1 lxZ.sys ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → xtB1 lxZ.sys ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut (xtB1 lxZ.sys) l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  xtRoad3 (xtSpec1 lxZ.topPkg) lxZ_nonfix hU hL (fun _ hr hlB hfix => lxZT_fix hr hlB hfix) hV hC hEQ hrest hB2

/-- **`sup_n Λ⁺(lxK n) = ι(ε_{Γ_{Ω₁+1}+ω}) < Λ⁺(lxZ) = ι(ε_{Γ_{Ω₁+1}+Ω₁}·ω)`.** -/
theorem lxFam_lt_Z (S : InaccSeq.{0}) : lxFam.famSup < xtB1 lxZ.sys := by
  rw [(lxFam_loc (S := S)).1, (lxZ_loc (S := S)).1]
  have h1 : lxCw < lxZC := veblen_lt_veblen_iff_right.2 ((add_lt_add_iff_left _).2 (ph_omega_lt ph_SC_Om1))
  have h2 : lxCw < lxZC * ω := h1.trans_le (le_mul_of_one_le_right zero_le one_lt_omega0.le)
  exact cd_iota_lt_of_good (lg_good (fun Z hZ => lx_cl_Cw hZ)) h2

/-- **Where `Λ⁺(lxZ)` lies**: `ρ(sup_n Λ⁺(lxK n)) < ρ(Λ⁺(lxZ)) < L(0) = m* ≤ L(k+1) < L(ω) < L(ω+1)`, and
`Λ⁺(lxZ) < L(ω+1)`, unconditionally. -/
theorem lxZ_fr_order (k : ℕ) :
    upsilon lxFam.famSup < upsilon (xtB1 lxZ.sys) ∧ upsilon (xtB1 lxZ.sys) < Nc.ncL S 0 ∧
    Nc.ncL S 0 ≤ Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ∧
    Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) < Nc.ncL S ω ∧ Nc.ncL S ω < Nc.ncL S (ω + 1) ∧
    xtB1 lxZ.sys < Nc.ncL S (ω + 1) := by
  obtain ⟨h0, h1, h2⟩ := phL_chain (S := S) k
  obtain ⟨-, hups, hlt⟩ := lxZ_loc (S := S)
  have hU : upsilon (xtB1 lxZ.sys) < Nc.ncL S 0 := hups ▸ hlt
  refine ⟨upsilon_normal.strictMono (lxFam_lt_Z S), hU, h0, h1, h2, ?_⟩
  exact upsilon_normal.strictMono.le_apply.trans_lt (((hU.trans_le h0).trans h1).trans h2)

end Googology.Trans.PoR.InaccPsi.R2.Lx
