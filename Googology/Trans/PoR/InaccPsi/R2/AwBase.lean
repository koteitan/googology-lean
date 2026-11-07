import Googology.Trans.PoR.InaccPsi.R2.AwLay
import Googology.Trans.PoR.InaccPsi.R2.ZsCap

/-!
# AwBase: UPPER AND LOWER AT THE BASE `l₀ = ι(Ω₂)`

The term system `Aw.awSys` of the bound `K_ω` itself (the code `K_ω` is not an atom, but its reading `Θ_y(K_ω) = sup_j Θ_y(K_j)` lies
below `ϑˣ(Ω₁·Ω₁ + Ω₁)`, is an `ε`-number, and has Lemma IMG by `Aw.awE_core`).  Below `l₀` the offsets agree with those of the
systems of `K_{j+1}`, which read below `Θ_μ(K_ω)`: there is no frontier below `l₀`, so `l₀` lies below the first limit of frontiers.
The frontiers of the systems of `K_{j+1}` are cofinal below `l₀`, so every term is realized cofinally: `l₀` is the first frontier, with
offset `Θ_{l₀}(K_ω)`, the reading of the code of `l₀`.

* `aw_K_cl`, `aw_V_lt`, `aw_V_SC`, `aw_topV`, `aw_HV` (**THE HYPOTHESIS `AwH` AT `K_ω`**);
* `aw_below`, `aw_no_fr`, `aw_base_lt`, `aw_base_off`, `aw_base_theta`, `aw_base_UL` (**UPPER AND LOWER AT `l₀`**).

No new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Aw

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Zr
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Zo

variable {S : InaccSeq.{0}}

/-- `K_j` is a code over every base. -/
theorem aw_K_cl (Z : Ordinal.{0}) : ∀ j, GxCl Z (awAt S Z) (zrK S j)
  | 0 => by rw [zrK_zero]; exact GxCl.om
  | j + 1 => GxCl.atom (aw_K_mem Z j)

/-- **`Θ_y(K_ω)` lies below `ϑˣ(Ω₁·Ω₁ + Ω₁)`, below the next `υ`-point after `x`.** -/
theorem aw_V_lt {y : Ordinal.{0}} (hy : SC y) (hy1 : y < Om1) : gxTh y (awAt S y) (awV S) < awNx (awNx y) := by
  obtain ⟨hyx, -, hxS, hx1, -, -⟩ := awNx_facts hy hy1
  obtain ⟨hxm, -, -, hm1, hTm, -⟩ := awNx_facts hxS hx1
  have hAt : GxAt (awAt S y) := (awU S).gxAt y
  have hy1' : y < Om 1 := by rw [← Rj.rj_Om1]; exact hy1
  have hxE : InE (awNx y) := Low.opow_eq_self_of_SC hxS
  have h1x : (1 : Ordinal.{0}) < awNx y := Lu.lu_one_lt_E hxE
  have h1T : (1 : Ordinal.{0}) ∈ Tset (awNx y) := mem_T_of_le hxE hx1 h1x.le
  have h0T : (0 : Ordinal.{0}) ∈ Tset (awNx y) := mem_T_of_le hxE hx1 zero_le
  have h1Ω : (1 : Ordinal.{0}) < Om1 := h1x.trans hx1
  have h0Ω : (0 : Ordinal.{0}) < Om1 := hxE.pos.trans hx1
  obtain ⟨-, -, hBT, hxB, hB1, -, -, -, -, -⟩ := Lq.lq_facts hxE hx1 le_rfl h1T h1Ω h1T h1Ω h0T h0Ω
  set B := vt (awNx y) (Om1 * (Om1 * 1 + 1) + 0) with hB
  have hBm : B < awNx (awNx y) := (hTm B hB1).1 hBT
  have hK : ∀ j, gxTh y (awAt S y) (zrK S j) < B := by
    intro j
    induction j with
    | zero =>
      rw [zrK_zero, gxTh_Om1 hy hy1' hAt]
      exact hyx.trans hxB
    | succ j ih =>
      have hd0 : 0 < zrK S j := lt_of_lt_of_le (by rw [zrK_zero]; exact Om_pos one_ne_zero) (zrK_mono.monotone (Nat.zero_le j))
      have e := (aw_read (S := S) hy hy1 _ (aw_K_mem y j)).2 _ (zrK_succ j) hd0 (aw_K_cl y j)
      rw [e]
      unfold awG
      set w := cdOff (gxTh y (awAt S y) (zrK S j)) with hw
      have hwB : w < B := (cdOff_le _).trans_lt ih
      have hwm : w < awNx (awNx y) := hwB.trans hBm
      have hwΩ : w < Om1 := hwm.trans hm1
      have hwT : w ∈ Tset (awNx y) := (hTm w hwΩ).2 hwm
      have hlt := lqVt_lt hxE hx1 h1T h1Ω h0T h0Ω hwT hwΩ le_rfl h1T h1Ω h1T h1Ω h0T h0Ω
        (γ' := 1) (β' := 0) (η' := w) (γ := 1) (β := 1) (η := 0)
        (by
          rw [mul_one, add_zero, add_zero, mul_add_one]
          exact (add_lt_add_iff_left _).2 hwΩ)
        (h1x.trans hxB) (hxE.pos.trans hxB) hwB
      have e1 : Om1 * (Om1 * 1 + 0) + w = Om1 * Om1 + w := by rw [mul_one, add_zero]
      rwa [e1] at hlt
  refine lt_of_le_of_lt (le_of_forall_lt fun v hv => ?_) hBm
  obtain ⟨c, hc, hcV, rfl⟩ := gxTh_onto hv
  obtain ⟨j, hj⟩ := aw_lt_V_iff.1 hcV
  exact (gxTh_lt hc hj).trans (hK j)

theorem aw_V_SC {y : Ordinal.{0}} (hy : SC y) (hy1 : y < Om1) : SC (gxTh y (awAt S y) (awV S)) :=
  gxTh_SC hy (aw_gxAt S y) awV_SC (hy1.trans (by rw [Rj.rj_Om1]; exact aw_Om1_lt_V))

/-- **The IMG package at `K_ω`.** -/
theorem aw_topV {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ) (hρS : SC ρ) :
    ImgPkg ρ δ (fun x => gxTh x (awAt S x) (awV S)) := by
  have hx : awNx ρ < gxTh ρ (awAt S ρ) (awV S) := by
    have := gxTh_lt (Z := ρ) (At := awAt S ρ) (GxCl.atom (aw_th_mem _)) aw_th_lt_V
    rwa [aw_Rd_th hρS h.ρ1] at this
  obtain ⟨W, Z, w, m, -, b⟩ := awE_core h hρS (Low.opow_eq_self_of_SC (aw_V_SC hρS h.ρ1)) hx le_rfl ∅ (by simp)
    (fun y hy hy1 _ => aw_V_lt hy hy1) (fun c₀ hc₀ hlt => aw_img h hρS c₀ hc₀ hlt)
  refine ⟨?_, ?_, W, Z, w, m, b⟩
  · exact (Order.one_le_iff_pos.2 (hρS.1.trans (awNx_facts hρS h.ρ1).1)).trans hx.le
  · obtain ⟨-, -, -, hmτ⟩ := aw_x_facts h hρS
    exact (aw_V_lt hρS h.ρ1).trans (hmτ.trans h.τδ)

/-- **THE HYPOTHESIS `AwH` AT `K_ω`.** -/
theorem aw_HV : AwH S (awV S) := by
  refine ⟨le_rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact (aw_H 0).gE.trans (zrK_lt_V _)
  · intro l hl hl1
    obtain ⟨hU, h1, hSC⟩ := aw_ri_SC S hl hl1
    exact (aw_V_lt hSC h1).trans (aw_mm_lt S hl hl1)
  · intro l hl hl1 c hc1 hcT hcc R
    obtain ⟨hU, h1, hSC⟩ := aw_ri_SC S hl hl1
    refine aw_pkg R hSC hcc hcT ?_
    exact (Order.one_le_iff_pos.2 hSC.1).trans (aw_val_ge (by rw [← Rj.rj_Om1]; exact h1.le) hc1)
  · intro l hl hl1 R
    obtain ⟨hU, h1, hSC⟩ := aw_ri_SC S hl hl1
    exact aw_topV R hSC
  · intro l hl hl1 c hc1 hcT hcc
    exact aw_rs hl1 hcT hcc

/-- Below `l₀`, every restart lies below some `ι(K_{j+1}·ω)`. -/
theorem aw_below {l : Ordinal.{0}} (hl : l < iota S (Om (1 + 1))) : ∃ j, l < iota S (zrK S (j + 1) * ω) :=
  aw_below_K hl

section Base

local notation "XV" => awSys (aw_HV (S := S))

theorem aw_KT {j : ℕ} {μ : Ordinal.{0}} (hμ : IsRestartIdx μ) (hμ1 : μ < Om1) :
    (awSys (aw_H (S := S) j)).top (upsilon μ) = gxTh (upsilon μ) (awAt S (upsilon μ)) (zrK S (j + 1)) := by
  obtain ⟨-, -, hSC⟩ := aw_ri_SC S hμ hμ1
  exact awSys_top _ hSC

theorem aw_VT {μ : Ordinal.{0}} (hμ : IsRestartIdx μ) (hμ1 : μ < Om1) :
    (XV).top (upsilon μ) = gxTh (upsilon μ) (awAt S (upsilon μ)) (awV S) := by
  obtain ⟨-, -, hSC⟩ := aw_ri_SC S hμ hμ1
  exact awSys_top _ hSC

theorem aw_B1K (j : ℕ) : xtB1 (awSys (aw_H (S := S) j)) = iota S (zrK S (j + 1) * ω) := by
  have h := (awLoc (aw_H (S := S) j) (Low.opow_eq_self_of_SC (zrK_SC j)) (fun Z => aw_K_cl Z (j + 1))).1
  rwa [Low.opow_eq_self_of_SC (zrK_SC j)] at h

/-- The offsets of the system of `K_ω` are those of the systems of `K_{j+1}`. -/
theorem aw_off_agree {j : ℕ} {μ : Ordinal.{0}} (hμ : IsRestartIdx μ) (h1 : μ < xtB1 XV)
    (h2 : μ < iota S (zrK S (j + 1) * ω)) : xtOrec XV μ = xtOrec (awSys (aw_H (S := S) j)) μ := by
  rw [← aw_B1K j] at h2
  exact xt_off_eq (xtSpec1 (aw_topPkg _)) (xtSpec1 (aw_topPkg _)) hμ h1 h2

theorem aw_l0_lt_Om1 : iota S (Om (1 + 1)) < Om1 :=
  calc iota S (Om (1 + 1)) = zoBase S := zrBase_eq.symm
    _ = upsilon (zoBase S) := Zs.zsFix.symm
    _ = Pv S (Om (1 + 1)) := zrBase_rho
    _ < Om1 := by rw [Rj.rj_Om1]; exact Pv_lt_Om1 S _

/-- **No frontier below `l₀`.** -/
theorem aw_no_fr {μ : Ordinal.{0}} (hμ : IsRestartIdx μ) (h1 : μ < iota S (Om (1 + 1))) (hB : μ < xtB1 XV) :
    xtOrec XV μ < (XV).top (upsilon μ) := by
  have hμ1 : μ < Om1 := h1.trans aw_l0_lt_Om1
  obtain ⟨j, hj⟩ := aw_below h1
  rw [aw_off_agree hμ hB hj, aw_VT hμ hμ1]
  refine (xtOrec_le_top hμ hμ1).trans_lt ?_
  rw [aw_KT hμ hμ1]
  exact gxTh_lt (aw_K_cl _ _) (zrK_lt_V _)

/-- **`l₀` lies below the first limit of frontiers.** -/
theorem aw_base_lt : iota S (Om (1 + 1)) < xtB1 XV := by
  by_contra hle
  push Not at hle
  obtain ⟨h0, hc⟩ := xtB1_spec (aw_topPkg (aw_HV (S := S)))
  obtain ⟨μ, ⟨hμ, hfr⟩, -, hμB⟩ := hc 0 h0
  exact absurd hfr (aw_no_fr hμ (hμB.trans_le hle) hμB).ne

/-- **At `l₀` the offset is the top.** -/
theorem aw_base_off : xtOrec XV (iota S (Om (1 + 1))) = (XV).top (upsilon (iota S (Om (1 + 1)))) := by
  classical
  have hri : IsRestartIdx (iota S (Om (1 + 1))) := zrIota_ri.1
  have hl1 : iota S (Om (1 + 1)) < Om1 := aw_l0_lt_Om1
  have hfix : upsilon (iota S (Om (1 + 1))) = iota S (Om (1 + 1)) := by rw [← zrBase_eq]; exact Zs.zsFix
  refine le_antisymm (xtOrec_le_top hri hl1) (le_of_forall_lt fun v hv => ?_)
  obtain ⟨t, hCB, rfl⟩ := (XV).rep _ hri hl1 v hv
  refine lt_xtOrec_of_cof hri hl1 hCB fun ν hν => ?_
  -- the constants of `t`
  have hl0 : 0 < iota S (Om (1 + 1)) := pos_iff_ne_zero.2 hri.1
  have hsup : (insert ν ((XV).cs t).toFinset).sup id < iota S (Om (1 + 1)) := by
    rw [Finset.sup_lt_iff hl0]
    intro b hb
    rcases Finset.mem_insert.1 hb with rfl | hb
    · exact hν
    · have := (XV).cb_cst t _ hCB b (List.mem_toFinset.1 hb)
      rwa [hfix] at this
  set κ₀ := (insert ν ((XV).cs t).toFinset).sup id with hκ₀
  have hνκ : ν ≤ κ₀ := Finset.le_sup (f := id) (Finset.mem_insert_self _ _)
  have hcsκ : ∀ c ∈ (XV).cs t, c ≤ κ₀ := fun c hc =>
    Finset.le_sup (f := id) (Finset.mem_insert_of_mem (List.mem_toFinset.2 hc))
  -- a system `K_{j+1}` above `κ₀` and above the code of `t`
  obtain ⟨j₁, hj₁⟩ := aw_below hsup
  have hρ1' : upsilon (iota S (Om (1 + 1))) ≤ Om 1 := by
    rw [hfix, ← Rj.rj_Om1]; exact hl1.le
  have hcode : ∃ j₂, ∀ c, t = Sum.inr c → c < zrK S (j₂ + 1) := by
    cases t with
    | inl a => exact ⟨0, fun c h => by cases h⟩
    | inr c =>
      obtain ⟨-, hcT, -⟩ := awCB_code (S := S) (T := awV S) hρ1' hCB
      obtain ⟨j, hj⟩ := aw_lt_V_iff.1 hcT
      exact ⟨j, fun c' h => by cases h; exact hj.trans (zrK_lt_succ j)⟩
  obtain ⟨j₂, hj₂⟩ := hcode
  set j := max j₁ j₂ with hj
  have hκj : κ₀ < iota S (zrK S (j + 1) * ω) := hj₁.trans_le (iota_mono _ _ (mul_le_mul_left
    (zrK_mono.monotone (Nat.succ_le_succ (le_max_left _ _))) _))
  obtain ⟨h0, hc⟩ := xtB1_spec (aw_topPkg (aw_H (S := S) j))
  rw [aw_B1K j] at h0 hc
  obtain ⟨μ, ⟨hμ, hfr⟩, hκμ, hμB⟩ := hc κ₀ hκj
  have hμl : μ < iota S (Om (1 + 1)) := by
    have hE2 : InE (Om (1 + 1 : Ordinal.{0})) := Low.opow_eq_self_of_SC Gg.gg_SC_Om2
    exact hμB.trans_le (iota_mono _ _ (hE2.mul_lt (zrK_lt_Om2 _) (omega0_lt_inE hE2)).le)
  have hμ1 : μ < Om1 := hμl.trans hl1
  have hagree := aw_off_agree (S := S) hμ (hμl.trans aw_base_lt) hμB
  obtain ⟨hU, hu1, hSC⟩ := aw_ri_SC S hμ hμ1
  have hμup : μ ≤ upsilon μ := upsilon_normal.strictMono.le_apply
  have hcsμ : ∀ c ∈ (XV).cs t, c < upsilon μ := fun c hc' => ((hcsκ c hc').trans_lt hκμ).trans_le hμup
  refine ⟨μ, hμ, hνκ.trans_lt hκμ, hμl, (XV).cb_iff t _ _ hCB hcsμ, ?_⟩
  rw [hagree, hfr, aw_KT hμ hμ1]
  cases t with
  | inl c =>
    have hcμ : c < upsilon μ := hcsμ c (by simp [awSys, awCs])
    show c ≤ _
    exact hcμ.le.trans (aw_val_ge (by rw [← Rj.rj_Om1]; exact hu1.le) (zrK_gt_Om1 j).le)
  | inr c =>
    show gxTh _ _ c ≤ _
    exact gxTh_mono ((hj₂ c rfl).le.trans (zrK_mono.monotone (Nat.succ_le_succ (le_max_right _ _))))

/-- **The reading of the code of `l₀` is `Θ_{l₀}(K_ω)`.** -/
theorem aw_base_theta :
    cdTheta S (zoBase S) (cdCode S (zoBase S)) = gxTh (zoBase S) (awAt S (zoBase S)) (awV S) := by
  have hfix : upsilon (zoBase S) = zoBase S := Zs.zsFix
  have hX := Zs.zsPvLt (S := S) zoBase_range Zs.zsBase_lt_Lw
  have hA : ConjT.Aη S (cdEta S (zoBase S)) = Om ω + Om (1 + 1) := zrBase_A
  rw [zrBase_theta]
  have hle : cdTheta S (zoBase S) (Om (1 + 1)) = cdTheta S (zoBase S) (awV S) := by
    refine le_antisymm (le_of_forall_lt fun v hv => ?_) (cdTheta_mono S _ (psi_lt (InR_Om_succ 1) _).le)
    obtain ⟨c, hcH, hc2, rfl⟩ := Gg.ggOtp_onto _ _ _ hv
    refine cdOtp_lt_of_mem hcH ?_
    have hmem : c ∈ S.CSet (Om ω + Om (1 + 1)) (awV S) := by
      have hcH' : c ∈ S.CSet (Om ω + Om (1 + 1)) (upsilon (zoBase S)) := by
        unfold cdHull at hcH; rwa [hA] at hcH
      refine CSet_mono le_rfl ?_ hcH'
      rw [zrBase_rho]
      exact ((Pv_lt_Om1 S _).trans (psiS_bounds (S := S) _ 1).1).le
    exact lt_psi_of_mem (InR_Om_succ 1) hmem hc2
  rw [hle]
  refine (awU S).theta_eq zoBase_spec.1 hfix hX le_rfl ?_
  rw [zrBase_eta, zr_th_Om2]
  exact (psi_lt (InR_Om_succ 1) _).le

/-- **UPPER AND LOWER AT THE BASE `l₀ = ι(Ω₂)`.** -/
theorem aw_base_UL : CdUpper S (zoBase S) ∧ CdLower S (zoBase S) := by
  have hb : zoBase S = iota S (Om (1 + 1)) := zrBase_eq
  have hfix : upsilon (zoBase S) = zoBase S := Zs.zsFix
  have hri : IsRestartIdx (zoBase S) := zoBase_spec.1
  have hl1 : zoBase S < Om1 := by rw [hb]; exact aw_l0_lt_Om1
  have hoff := aw_base_off (S := S)
  have hlt := aw_base_lt (S := S)
  rw [← hb] at hoff hlt
  refine (xtExact_iff (xtSpec1 (aw_topPkg (aw_HV (S := S)))) hri hlt).2 ?_
  rw [hoff, aw_VT hri hl1, hfix]
  exact aw_base_theta

end Base

end Googology.Trans.PoR.InaccPsi.R2.Aw
