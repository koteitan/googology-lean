import Googology.Trans.PoR.InaccPsi.R2.GvRec

/-!
# ITERATED UNIONS OVER `Ω₁`: the bounds `ε_{G+Ω₁·k}` and the frontier `ι(Γ(ε_{G+Ω₁·ω}))`

For a start `St : GvSt` (index `i₀`, base `φ(1, i(x))`, offset `a(x)`) the recursion `gvRD St ν`, `ν < Ω₁`, is a
family over `Ω₁` (`gvFamOf St : GvFam`): its union `gvUof St` has the bound `ε_{i₀+Ω₁}` read `φ(1, i(x) + x)`
(Lemma EXACT from `ϑˣ(Ω₁ + a(x) + x) = φ(1, i(x) + x)`, `gvR_bΩ`, and `π(ρ) = σ`), base gate `0`.  Its step is again
a start (`gvNext St`: index `i₀ + Ω₁ + 1`, base `φ(1, i(x) + x + 1)`).  Starting from `gvS` (`ε_{G+Ω₁+1}`,
`R2.GvFr`) the starts `gvSt k` have the indices `G + Ω₁·(k+1) + 1` (`gvSt_i0`) and the unions the bounds
`ε_{G+Ω₁·(k+2)}` (`gvUk_B`).  Each bound `ε_{i₀+Ω₁}` has gate `0` in the step, so it is located (`gvLocU`), with
BLK^O, exact reaches, ENUM-REACH and CapV below `ι(Γ(ε_{i₀+Ω₁})·ω)`; the supremum is **`ι(Γ(ε_{G+Ω₁·ω}))`**.

* `gvR_bΩ` (**`ϑˣ(Ω₁ + a(x) + x) = φ(1, i(x) + x)`**), `gvFamOf`, `gvUof`, `gvUof_B`, `gvNext`, `gvSt0`, `gvSt`,
  `gvSt_i0`, `gvUk_B`;
* `gvLocU`, `gvLocU_enum`, `gvLocU_capV`, `gvLocU_blk` (every start), `gvWW`, `gvWW_cof`, `gvWW_enum`, `gvWW_capV`,
  `gvWW_road` (**THE ROAD**), `gvWW_le_Om2`, `gvWW_P`, `gvWW_fr_order`.

No new axiom.  New definitions: `gvFamOf`, `gvUof`, `gvNext`, `gvSt0`, `gvSt`, `gvWW`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gv

open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gj
  Googology.Trans.PoR.InaccPsi.R2.Gi Googology.Trans.PoR.InaccPsi.R2.Gn Googology.Trans.PoR.InaccPsi.R2.Go
  Googology.Trans.PoR.InaccPsi.R2.Gp
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Lp Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Gd

theorem gv_Om1_lt_G1 : (Om1 : Ordinal.{0}) < gcG 1 := by rw [Br.Om1_eq]; exact gcG_Om1_lt 1

section Fam

variable (St : GvSt)

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem gvR_T_lt : St.a x + x < gq 1 x :=
  (inE_indec (gm1_facts hx hx1).2.2.2).add_lt (St.a_lt hx hx1) (gm1_facts hx hx1).2.1

/-- **The base of the union**: `ϑˣ(Ω₁ + a(x) + x) = φ(1, i(x) + x)` (the index `Ω₁` read as `x`). -/
theorem gvR_bΩ : glA 1 (St.a x + x) x = veblen 1 (St.i x + x) := by
  have hxl : IsSuccLimit x := ev_isSuccLimit_of_inE hx
  have hx0 : x ≠ 0 := hx.pos.ne'
  have hδ := fun k => gqFs_lt hxl hx1 k
  have hval : ∀ k, glA 1 (St.a x + gpOff (gqFs x k)) x = veblen 1 (St.i x + gqFs x k + 1) := fun k => by
    have hk1 : gqFs x k < Om1 := (hδ k).trans hx1
    have h := (gvRD St (gqFs x k)).b_eN x hx hx1 ((gvR_γ hk1).trans_lt (hδ k))
    rw [gvR_b hk1 hx hx1 (hδ k), gvR_ba hk1, go_eN_veb] at h
    exact h.symm
  have hT := gvR_T_lt St hx hx1
  refine go_glA_sup hx hx1 (s := fun k => St.a x + gpOff (gqFs x k)) (f := fun k => St.i x + gqFs x k + 1) hT
    (fun k => (add_lt_add_iff_left _).2 (gpOff_lt hxl (hδ k))) (fun σ hσ => ?_) (fun k => ?_) (fun σ hσ => ?_)
    (isSuccLimit_add _ hxl) ?_ hval
  · exact go_lt_add_sup hx0 (fun t ht => (gqFs_cof hxl hx1 t ht).imp fun _ hk => hk.trans_le (le_gpOff _)) hσ
  · show St.i x + gqFs x k + 1 < St.i x + x
    rw [add_assoc]; exact (add_lt_add_iff_left _).2 (hxl.add_one_lt (hδ k))
  · obtain ⟨k, hk⟩ := go_lt_add_sup hx0 (gqFs_cof hxl hx1) hσ
    exact ⟨k, hk.trans (lt_add_one _)⟩
  · have hE : InE (veblen 1 (St.i x + x)) := omega0_opow_epsilon _
    obtain ⟨h1T, h11⟩ := gl_one_T hx hx1
    obtain ⟨haT, ha1⟩ := gm1_T hx hx1 (St.a_lt hx hx1)
    have h0 : St.D0.b x = veblen 1 (St.i x) := St.b0 x hx hx1
    have hglA : glA 1 (St.a x) x = veblen 1 (St.i x + 1) := by
      rw [← St.ba0, ← St.D0.b_eN x hx hx1 (St.γ_lt hx), h0, go_eN_veb]
    have ha : St.a x < veblen 1 (St.i x + x) := by
      have h1 := (glA_facts hx hx1 le_rfl h1T h11 haT ha1).2.2.2.2.2
      rw [hglA] at h1
      exact h1.trans_le ((isNormal_veblen 1).monotone ((add_le_add_iff_left _).2
        (Order.one_le_iff_pos.2 hx.pos)))
    have hxb : x < veblen 1 (St.i x + x) := by
      have h1 := St.D0.x_lt_b x hx hx1 (St.γ_lt hx)
      rw [h0] at h1
      exact h1.trans_le ((isNormal_veblen 1).monotone le_self_add)
    exact (inE_indec hE).add_lt ha hxb

theorem gvR_TT : St.a x + x ∈ Tset x ∧ St.a x + x < Om1 := gm1_T hx hx1 (gvR_T_lt St hx hx1)

theorem gvR_i_lt_Z : St.i x < evZ (lgG x) := by
  have h0 := St.D0.b_Z x hx hx1 (St.γ_lt hx)
  rw [St.b0 x hx hx1] at h0
  exact (right_le_veblen 1 _).trans_lt ((lt_eN _).trans h0)

end Base

theorem gvR_TB {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) :
    St.a ρ + ρ ∈ TB ρ σ ∧ pi σ ρ (St.a ρ + ρ) = St.a σ + σ := by
  obtain ⟨g1, g2⟩ := St.a_pi hB
  obtain ⟨r1, r2⟩ := pi_base hB
  obtain ⟨s1, s2⟩ := pi_add hB g1 r1
  exact ⟨s1, by rw [s2, g2, r2]⟩

/-- **The recursion from `St` as a family over `Ω₁`.** -/
noncomputable def gvFamOf : GvFam where
  F := gvRD St
  i0 := St.i0
  i := St.i
  baΩ := fun x => St.a x + x + 1
  ix := fun ν hν => (gvR_inv St ν hν).ix ν (lt_add_one ν)
  hb := fun ν hν x hx hx1 hνx => gvR_b hν hx hx1 hνx
  γ_le := fun ν hν => gvR_γ hν
  cohR := fun β γ hβγ hγ => (gvR_ext St hβγ hγ).1
  cohg := fun β γ hβγ hγ => (gvR_ext St hβγ hγ).2
  small := fun ν hν c hc σ hσ hg => gvR_small St hν hc hσ hg
  i0_mem := fun _ _ _ ha hb => St.i0_mem ha hb
  ix_lt := (inE_indec (Low.opow_eq_self_of_SC (gcG_SC 1))).add_lt St.i0_lt gv_Om1_lt_G1
  b_eN := fun x hx hx1 => by
    obtain ⟨hT, h1⟩ := gvR_TT St hx hx1
    rw [← gvR_bΩ St hx hx1]; exact glA_eN_one hx hx1 hT h1
  ba_lt := fun x hx hx1 =>
    (ev_isSuccLimit_of_inE (gm1_facts hx hx1).2.2.2).add_one_lt (gvR_T_lt St hx hx1)
  b_Z := fun x hx hx1 => by
    refine go_eN_lt_evZ ?_
    have hZ := evZ_E (lgG x)
    have hxZ : x < evZ (lgG x) := (lgG_facts hx hx1).2.1.trans (lt_evZ _)
    have := (isNormal_veblen 1).strictMono ((inE_indec hZ).add_lt (gvR_i_lt_Z St hx hx1) hxZ)
    rwa [show veblen 1 (evZ (lgG x)) = evZ (lgG x) from epsilon_evZ _] at this
  b_pi := fun σ ρ hB => by
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
    obtain ⟨s1, s2⟩ := gvR_TB St hB
    obtain ⟨o1, o2⟩ := one_TB hB
    have h := glA_pi hB o1 (gl_one_T hB.2.1 hρ1).2 s1 (gvR_TT St hB.2.1 hρ1).2
    rw [o2, s2, gvR_bΩ St hB.2.1 hρ1, gvR_bΩ St hB.1 hσ1] at h
    exact h
  ba_pi := fun σ ρ hB => by
    obtain ⟨s1, s2⟩ := gvR_TB St hB
    obtain ⟨o1, o2⟩ := one_TB hB
    obtain ⟨t1, t2⟩ := pi_add hB s1 o1
    exact ⟨t1, by rw [t2, s2, o2]⟩

/-- **The union over `Ω₁` of the recursion from `St`**: bound `ε_{i₀+Ω₁}`, base gate `0`. -/
noncomputable def gvUof : GvD := (gvFamOf St).U

theorem gvUof_B : (gvUof St).B = veblen 1 (St.i0 + Om1) := rfl

theorem gvUof_γ : (gvUof St).γ = 0 := rfl

/-- **The next start**: the step of the union (index `i₀ + Ω₁ + 1`). -/
noncomputable def gvNext : GvSt where
  D0 := (gvUof St).step
  i0 := St.i0 + Om1 + 1
  i := fun x => St.i x + x + 1
  a := fun x => St.a x + x + 1 + 1
  P0 := St.P0 + Om1
  j0 := 1
  γ0 := rfl
  ix0 := rfl
  b0 := fun x _ _ => by
    show eN (veblen 1 (St.i x + x)) = _
    rw [go_eN_veb]
  ba0 := fun _ => rfl
  i0_eq := by
    rw [St.i0_eq, add_assoc St.P0 St.j0, Br.Om1_eq, Fx.fx_Om1_prin.add_eq_right St.j0_lt]
  P0_dvd := dvd_add St.P0_dvd (by rw [Br.Om1_eq])
  P0_ge := St.P0_ge.trans le_self_add
  j0_lt := one_lt_Om1
  i_big := fun x hx hx1 => (St.i_big x hx hx1).trans
    ((isNormal_veblen 1).monotone (le_self_add.trans le_self_add))

end Fam

/-! ## The first start: `gvS` -/

theorem gv_G_dvd : Om 1 ∣ gcG 0 + Om1 := by
  refine dvd_add ?_ (by rw [Br.Om1_eq])
  have e : ω ^ gcG 0 = gcG 0 := Low.opow_eq_self_of_SC (gcG_SC 0)
  have h := gv_Om1_dvd_opow (e.symm ▸ (gcG_Om1_lt 0).le : Om 1 ≤ ω ^ gcG 0)
  rwa [e] at h

/-- **The first start**: `gvS` (bound `ε_{G+Ω₁+1}`), index `G + Ω₁ + 1`, base `φ(1, Γ_{x+1} + x + 1)`. -/
noncomputable def gvSt0 : GvSt where
  D0 := gvS
  i0 := gcG 0 + Om1 + 1
  i := fun x => gpI x + x + 1
  a := fun x => lgG x + (x + 1) + 1
  P0 := gcG 0 + Om1
  j0 := 1
  γ0 := rfl
  ix0 := rfl
  b0 := fun x _ _ => by
    show eN (veblen 1 (gpI x + x)) = _
    rw [go_eN_veb]
  ba0 := fun _ => rfl
  i0_eq := rfl
  P0_dvd := gv_G_dvd
  P0_ge := (gcG_Om1_lt 0).le.trans le_self_add
  j0_lt := one_lt_Om1
  i_big := fun x hx hx1 => by
    have e : veblen 1 (gpI x) = lgG x := epsilon_evIx (lgG_facts hx hx1).2.2.2.1
    rw [← e]
    exact (isNormal_veblen 1).monotone (le_self_add.trans le_self_add)

/-- **The iterated starts**: `gvSt 0 = gvSt0`, `gvSt (k+1) = gvNext (gvSt k)`. -/
noncomputable def gvSt : ℕ → GvSt
  | 0 => gvSt0
  | k + 1 => gvNext (gvSt k)

/-- **The index of the `k`-th start**: `G + Ω₁·(k+1) + 1`. -/
theorem gvSt_i0 : ∀ k : ℕ, (gvSt k).i0 = gcG 0 + Om1 * ((k : Ordinal.{0}) + 1) + 1
  | 0 => by
    show gcG 0 + Om1 + 1 = _
    rw [Nat.cast_zero, zero_add, mul_one]
  | k + 1 => by
    show (gvSt k).i0 + Om1 + 1 = _
    rw [gvSt_i0 k, add_assoc (gcG 0 + _) 1 Om1, Br.Om1_eq, Fx.fx_Om1_prin.add_eq_right one_lt_Om1, ← Br.Om1_eq,
      add_assoc (gcG 0), ← mul_add_one (Om1 : Ordinal.{0})]
    push_cast; rfl

/-- **The bound of the `k`-th union**: `ε_{G+Ω₁·(k+2)}`. -/
theorem gvUk_B (k : ℕ) : (gvUof (gvSt k)).B = veblen 1 (gcG 0 + Om1 * ((k : Ordinal.{0}) + 2)) := by
  rw [gvUof_B, gvSt_i0, add_assoc (gcG 0 + _) 1 Om1, Br.Om1_eq, Fx.fx_Om1_prin.add_eq_right one_lt_Om1,
    ← Br.Om1_eq, add_assoc (gcG 0), ← mul_add_one (Om1 : Ordinal.{0}), add_assoc]
  norm_num

/-! ## Location of the bound of every union -/

section Loc

variable (St : GvSt) (S : InaccSeq.{0})

theorem gvLocU_lt : (gvUof St).B < (gvUof St).step.B := (gvUof St).B_lt_NB

theorem gvLocU_E : gfE ≤ (gvUof St).B := (gvUof St).E_lt_B.le

theorem gvLocU_g : (gvUof St).step.toRS.K.gt (gvUof St).B < Td.tdK S := by
  rw [GsD.toRS_gt, GvD.step_g_B]; exact gv_K_pos S

/-- **THE BOUND `ε_{i₀+Ω₁}` OF EVERY UNION IS LOCATED**: `Λ⁺ = ι(Γ(ε_{i₀+Ω₁})·ω)`, `P(Γ(ε_{i₀+Ω₁})·ω) < L(0)`. -/
theorem gvLocU : ∃ X : XtSys, XtTopPkg X ∧ xtB1 X = iota S (gcG (gvUof St).B * ω) ∧
    upsilon (xtB1 X) = Pv S (gcG (gvUof St).B * ω) ∧ Pv S (gcG (gvUof St).B * ω) < Nc.ncL S 0 :=
  ⟨gsX (gvUof St).step.toRS _ (gvLocU_E St) (gvLocU_lt St) S (gvLocU_g St S),
    gsX_pkg (gvUof St).step.toRS _ (gvLocU_E St) (gvLocU_lt St) S (gvLocU_g St S),
    gsLoc (gvUof St).step.toRS _ (gvLocU_E St) (gvLocU_lt St) S (gvLocU_g St S)⟩

theorem gvLocU_enum {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG (gvUof St).B * ω)) :
    CdUpper S l ∧ CdLower S l :=
  gsEnum (gvUof St).step.toRS _ (gvLocU_E St) (gvLocU_lt St) S (gvLocU_g St S) hr hl

theorem gvLocU_capV {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG (gvUof St).B * ω)) :
    CdCapV S l :=
  gsCapV (gvUof St).step.toRS _ (gvLocU_E St) (gvLocU_lt St) S (gvLocU_g St S) hr hl

/-- **Theorem BLK^O below `P(Γ(ε_{i₀+Ω₁})·ω)`**, with the exact reaches. -/
theorem gvLocU_blk :
    let X := gsX (gvUof St).step.toRS _ (gvLocU_E St) (gvLocU_lt St) S (gvLocU_g St S)
    (∀ c' d, c' < d → d < upsilon (xtB1 X) → (le2 c' d ↔ ∃ μ, ∃ j : ℕ, (μ = 0 ∨ IsRestartIdx μ) ∧ μ < xtB1 X ∧
        c' = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧ d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < xtB1 X →
      (∀ c' < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c' g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec X l)) ∧
    (∀ α < upsilon (xtB1 X), ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  gsBlk (gvUof St).step.toRS _ (gvLocU_E St) (gvLocU_lt St) S (gvLocU_g St S)

end Loc

/-! ## The frontier `ι(Γ(ε_{G+Ω₁·ω}))` -/

/-- **The new bound** `ε_{G+Ω₁·ω}`. -/
noncomputable def gvWW : Ordinal.{0} := veblen 1 (gcG 0 + Om1 * ω)

theorem gvWW_lim : IsSuccLimit gvWW := ev_isSuccLimit_of_inE (omega0_opow_epsilon _)

theorem gvUk_lt_WW (k : ℕ) : (gvUof (gvSt k)).B < gvWW := by
  rw [gvUk_B]
  refine (isNormal_veblen 1).strictMono ((add_lt_add_iff_left _).2 ?_)
  refine (mul_lt_mul_iff_right₀ gv_Om1_pos).2 ?_
  have : (k : Ordinal.{0}) + 2 = ((k + 2 : ℕ) : Ordinal.{0}) := by push_cast; rfl
  rw [this]; exact natCast_lt_omega0 _

theorem gvWW_codes {c : Ordinal.{0}} (hc : c < gvWW) : ∃ k : ℕ, c < (gvUof (gvSt k)).B := by
  have hl : IsSuccLimit (Om1 * ω : Ordinal.{0}) := isSuccLimit_mul_right gv_Om1_pos isSuccLimit_omega0
  obtain ⟨t, ht, hct⟩ := ((isNormal_veblen 1).lt_iff_exists_lt (isSuccLimit_add _ hl)).1 hc
  obtain ⟨d, hd, htd⟩ := (lt_add_iff hl.bot_lt.ne').1 ht
  obtain ⟨m, hm, hdm⟩ := (lt_mul_iff_of_isSuccLimit isSuccLimit_omega0).1 hd
  obtain ⟨k, rfl⟩ := lt_omega0.1 hm
  refine ⟨k, ?_⟩
  rw [gvUk_B]
  refine hct.trans_le ((isNormal_veblen 1).monotone (htd.trans ((add_le_add_iff_left _).2 ?_)))
  refine hdm.le.trans ((mul_le_mul_iff_right₀ gv_Om1_pos).2 ?_)
  exact (le_self_add).trans (add_le_add_left (by norm_num) _)

/-- **`ι(Γ(ε_{G+Ω₁·ω})) = sup_k ι(Γ(ε_{G+Ω₁·(k+2)}))`**, below each the code `ε_{G+Ω₁·(k+2)}` is located. -/
theorem gvWW_cof (S : InaccSeq.{0}) {l : Ordinal.{0}} (hl : l < iota S (gcG gvWW)) :
    ∃ k : ℕ, l < iota S (gcG (gvUof (gvSt k)).B * ω) := by
  have hlim : IsSuccLimit (gcG gvWW) := ev_isSuccLimit_of_inE (Low.opow_eq_self_of_SC (gcG_SC _))
  rw [iota_limit hlim] at hl
  haveI : Nonempty (Iio (gcG gvWW)) := ⟨⟨0, hlim.bot_lt⟩⟩
  obtain ⟨e, he⟩ := (lt_ciSup_iff (iota_bdd _)).1 hl
  obtain ⟨β, hβ, heβ⟩ := gcG_lt_of_lt_limit gvWW_lim e.2
  obtain ⟨k, hk⟩ := gvWW_codes hβ
  refine ⟨k, he.trans_le (iota_mono _ _ ((heβ.trans (gcG_lt hk)).trans_le ?_).le)⟩
  exact le_mul_of_one_le_right' one_lt_omega0.le

/-- **ENUM-REACH at every range restart below `ι(Γ(ε_{G+Ω₁·ω}))`, fixed points included** (UNCONDITIONAL). -/
theorem gvWW_enum (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG gvWW)) :
    CdUpper S l ∧ CdLower S l := by
  obtain ⟨k, h⟩ := gvWW_cof S hl
  exact gvLocU_enum (gvSt k) S hr h

/-- **CapV at every range restart below `ι(Γ(ε_{G+Ω₁·ω}))`** (UNCONDITIONAL). -/
theorem gvWW_capV (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG gvWW)) :
    CdCapV S l := by
  obtain ⟨k, h⟩ := gvWW_cof S hl
  exact gvLocU_capV (gvSt k) S hr h

/-- **THE ROAD**: UPPER, LOWER, CapV asked only at `λ ≥ ι(Γ(ε_{G+Ω₁·ω}))` (CapV also `υ_λ < L(ω)`), (CL), EQ,
TCrest, (EMB₂) ⟹ `ν_C = L(ω+1)`, `L(ω) ≤ ν_C`, `L(ω) <₂ L(ω+1)`, (P), (Q), the reaches. -/
theorem gvWW_road (S : InaccSeq.{0}) (hU : ∀ l, CdRange S l → iota S (gcG gvWW) ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S (gcG gvWW) ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S (gcG gvWW) ≤ l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  refine goGl.go_road S (fun l hr _ => ?_) (fun l hr _ => ?_) (fun l hr hω _ => ?_) hC hEQ hrest hB2
  · by_cases h : l < iota S (gcG gvWW)
    · exact (gvWW_enum S hr h).1
    · exact hU l hr (not_lt.1 h)
  · by_cases h : l < iota S (gcG gvWW)
    · exact (gvWW_enum S hr h).2
    · exact hL l hr (not_lt.1 h)
  · by_cases h : l < iota S (gcG gvWW)
    · exact gvWW_capV S hr h
    · exact hV l hr hω (not_lt.1 h)

theorem gvWW_lt_G1 : gvWW < gcG 1 := by
  have hE : InE (gcG 1) := Low.opow_eq_self_of_SC (gcG_SC 1)
  have hOw : (Om1 : Ordinal.{0}) * ω < gcG 1 := InE.mul_lt hE gv_Om1_lt_G1 (omega0_lt_inE hE)
  have h1 : gcG 0 + Om1 * ω < gcG 1 := (inE_indec hE).add_lt (gcG_lt zero_lt_one) hOw
  exact (gcG_SC 1).2 1 (one_lt_omega0.trans (omega0_lt_inE hE)) _ h1

/-- **`Γ(ε_{G+Ω₁·ω}) < Ω₂`.** -/
theorem gvWW_le_Om2 : gcG gvWW < Om (1 + 1) := by
  have hBE : InE Tf.tfBG := Low.opow_eq_self_of_SC Tf.tfBG_SC
  have hO : (Om1 : Ordinal.{0}) < Tf.tfBG := Tf.tfBG_gt
  have h1 : (1 : Ordinal.{0}) < Tf.tfBG := one_lt_omega0.trans (omega0_lt_inE hBE)
  have hG1 : gcG 1 < Tf.tfBG := by
    rw [Tf.tf_gcG, ← Tf.tfBG_fix]
    exact gamma_lt_gamma.2 ((inE_indec hBE).add_lt ((inE_indec hBE).add_lt hO h1) h1)
  have h2 : gcG gvWW < Tf.tfBG := by
    rw [Tf.tf_gcG, ← Tf.tfBG_fix]
    exact gamma_lt_gamma.2 ((inE_indec hBE).add_lt ((inE_indec hBE).add_lt hO h1) (gvWW_lt_G1.trans hG1))
  exact h2.trans Tf.tfBG_lt_Om2

/-- **`P(Γ(ε_{G+Ω₁·ω})) < L(0)`.** -/
theorem gvWW_P (S : InaccSeq.{0}) : Pv S (gcG gvWW) < Nc.ncL S 0 := ga_Pv_lt_L0 S gvWW_le_Om2.le

/-- **The order of the frontiers**: `ι(Γ(ε_{G+Ω₁+ω})) ≤ ι(Γ(ε_{G+Ω₁·(k+2)})) < ι(Γ(ε_{G+Ω₁·(k+2)})·ω) ≤
ι(Γ(ε_{G+Ω₁·ω})) ≤ ι(Ω₂)` for every `k`, `P(Γ(ε_{G+Ω₁·ω})) ≤ P(Ω₂) < L(0)`. -/
theorem gvWW_fr_order (S : InaccSeq.{0}) (k : ℕ) :
    gvW < (gvUof (gvSt k)).B ∧ iota S (gcG gvW) ≤ iota S (gcG (gvUof (gvSt k)).B) ∧
      iota S (gcG (gvUof (gvSt k)).B) < iota S (gcG (gvUof (gvSt k)).B * ω) ∧
      iota S (gcG (gvUof (gvSt k)).B * ω) ≤ iota S (gcG gvWW) ∧
      iota S (gcG gvWW) ≤ iota S (Om (1 + 1)) ∧ Pv S (gcG gvWW) ≤ Pv S (Om (1 + 1)) ∧
      Pv S (Om (1 + 1)) < Nc.ncL S 0 := by
  set St := gvSt k
  have hWk : gvW < (gvUof St).B := by
    rw [gvUk_B]
    refine (isNormal_veblen 1).strictMono ?_
    rw [add_assoc]
    refine (add_lt_add_iff_left _).2 ?_
    calc (Om1 : Ordinal.{0}) + ω < Om1 + Om1 := (add_lt_add_iff_left _).2 omega_lt_Om1
      _ = Om1 * 2 := by rw [show (2 : Ordinal.{0}) = 1 + 1 by norm_num, mul_add_one, mul_one]
      _ ≤ Om1 * ((k : Ordinal.{0}) + 2) := mul_le_mul_left' le_add_self _
  have hg0 := gvLocU_g St S
  have hgood : Bt.Good S (gcG (gvUof St).B) :=
    gs_good (K := (gvUof St).step.toRS.K) fun Z _ hKZ =>
      GxCl.atom (gsmG_atom (K := (gvUof St).step.toRS.K) (gvLocU_lt St) (hg0.trans_le hKZ))
  have hG : InE (gcG (gvUof St).B) := Low.opow_eq_self_of_SC (gcG_SC _)
  have hV : InE (gcG gvWW) := Low.opow_eq_self_of_SC (gcG_SC _)
  refine ⟨hWk, iota_mono _ _ (gcG_lt hWk).le,
    cd_iota_lt_of_good hgood (lt_mul_of_one_lt_right hG.pos one_lt_omega0),
    iota_mono _ _ (InE.mul_lt hV (gcG_lt (gvUk_lt_WW k)) (omega0_lt_inE hV)).le,
    iota_mono _ _ gvWW_le_Om2.le, Nm.Pv_mono gvWW_le_Om2.le, ga_Pv_lt_L0 S le_rfl⟩

end Googology.Trans.PoR.InaccPsi.R2.Gv
