import Googology.Trans.PoR.InaccPsi.R2.XlKFr

/-!
# XlW: THE LEVEL `G + Ω₁`: THE UNION OF ALL LEVELS `G + κ`, `κ < Ω₁`, AND THE FRONTIER `ι(Γ(φ(G + Ω₁, 0))·ω)`

* `xlT_high` (**A CODE OF THE TOP OF A LEVEL IN `[φ(L+κ, e), N)` WITH GATE BELOW `σ` FORCES `γN < σ`**, the port of
  `Hn.hnVT_high` with the base `0`), `xlK_lim_eq` (the shape of `Xl.xlK λ` at a limit), `xlK_small` (**SMALL**: a
  code of `xlK ν` with gate below an `ε`-number `σ` lies in some `xlK μ`, `μ < σ`);
* `xlWF : Ho.HoFam` (the family `xlK μ`, `μ < Ω₁`: bound `φ(G + Ω₁, 0)`, gate `1`, base reading
  `φ(Γ_{x+1} + x, 0)` (the level `G + Ω₁` read `Γ_{x+1} + x`, `Hn.HnLv.succ`)), `xlW = Ho.hoOU xlWF` (**THE SYSTEM
  AT `φ(G + Ω₁, 0)`**, gate `1`), `xlW_ext` (it extends every `xlK μ`);
* `xlw_loc` (**`ι(Γ(φ(G + Ω₁, 0))·ω)` IS LOCATED**), `xlw_enum`, `xlw_capV`, `xlw_sysG`, `XlWPast`, `xlw_past_k`,
  `xlwRoad` / `xlwRoadZ`, `xlwRoad_hyp_iff` (**equivalent to the hypotheses of `Xl.xlkRoad`**).

No new axiom.  New definitions: `xlWF`, `xlW`, `XlWPast`.
-/

set_option autoImplicit false


open Googology.Trans.PoR.InaccPsi.R2.Wm Googology.Trans.PoR.InaccPsi.R2.Wh Googology.Trans.PoR.InaccPsi.R2.Ho
open Googology.Trans.PoR.InaccPsi.R2.Hn Googology.Trans.PoR.InaccPsi.R2.Hl
open Googology.Trans.PoR.InaccPsi.R2.Hj Googology.Trans.PoR.InaccPsi.R2.Hk
open Googology.Trans.PoR.InaccPsi.R2.Hi Googology.Trans.PoR.InaccPsi.R2.Hg
open Googology.Trans.PoR.InaccPsi.R2.Hf Googology.Trans.PoR.InaccPsi.R2.Hd Googology.Trans.PoR.InaccPsi.R2.He
open Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Hb
open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn Googology.Trans.PoR.InaccPsi.R2.Gf
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd
open Googology.Trans.PoR.InaccPsi.R2.Wo Googology.Trans.PoR.InaccPsi.R2.Wn Googology.Trans.PoR.InaccPsi.R2.Wp
  Googology.Trans.PoR.InaccPsi.R2.Ws Googology.Trans.PoR.InaccPsi.R2.Wt Googology.Trans.PoR.InaccPsi.R2.Wy
  Googology.Trans.PoR.InaccPsi.R2.Wx


open Googology.Trans.PoR.InaccPsi.R2.Xc
open Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Bt

open Googology.Trans.PoR.InaccPsi.R2.Xf

open Googology.Trans.PoR.InaccPsi.R2.Ho

namespace Googology.Trans.PoR.InaccPsi.R2.Xl

/-! ## High codes of a top -/

/-- **A code `c ∈ [S0.B, N)` of the top with gate below a base `σ` forces `γN < σ`.** -/
theorem xlT_high {Λ : HnLv} {κ : Ordinal.{0}} {St : ∀ (Q : HnVQ Λ κ) (U : HgVD), HgSStart (hnVPB Q) U → HgVD}
    {A : XlB Λ κ} {S0 : HgVD} (hSt : ∀ Q U h, HnVSpec Q U (St Q U h)) (hS : XlStart A S0) {c σ : Ordinal.{0}}
    (hc : c < hcN (Λ.L + κ) 0) (hFc : S0.B ≤ c) (hσ : InE σ) (hσ1 : σ < Om1)
    (hg : (xlTU hSt hS).g c < σ) : A.γN < σ := by
  obtain ⟨n, hn1, hn⟩ := xlT_cof hSt hS hc
  obtain ⟨-, hN1, hcNc⟩ := xlTN_spec hn1 hn
  have hgN : (xlTU hSt hS).g c = (xlU St A S0 (xlTN St A S0 c)).g c := rfl
  have I := xl_inv hSt hS _ hN1
  rcases zero_or_succ_or_isSuccLimit (xlTN St A S0 c) with h0 | ⟨m, hm⟩ | hlim
  · exfalso
    rw [h0, xlU_zero] at hcNc
    exact absurd hcNc (not_lt.2 hFc)
  · have hm' : xlTN St A S0 c = m + 1 := by rw [← hm, Order.succ_eq_add_one]
    have hmN : m < xlTN St A S0 c := by rw [hm']; exact lt_add_one m
    have hml : m < hcN (Λ.L + κ) 0 := hmN.trans hN1
    have hBc : (xlU St A S0 m).B ≤ c := not_lt.1 (xlTN_min hmN hml)
    rw [hgN, hm'] at hg
    rw [hm'] at hcNc I hN1
    have hγ := I.high m (lt_add_one _) c σ hBc hcNc hσ hσ1 hg
    exact (max_lt_iff.1 ((xlU_γ_iff hSt hS hN1 hσ hσ1).1 hγ)).1
  · exfalso
    rw [xlU_B hSt hS hN1] at hcNc
    obtain ⟨t, ht, hct⟩ := ((isNormal_veblen (Λ.L + κ)).lt_iff_exists_lt
        (isSuccLimit_add _ hlim)).1 hcNc
    obtain ⟨d, hf, htd⟩ := (lt_add_iff hlim.bot_lt.ne').1 ht
    have hfl : d < hcN (Λ.L + κ) 0 := hf.trans hN1
    refine xlTN_min hf hfl ?_
    rw [xlU_B hSt hS hfl]; exact hct.trans_le ((isNormal_veblen (Λ.L + κ)).monotone htd)

/-! ## The shape of `xlK` and SMALL -/

theorem xlK_succ_eq {μ : Ordinal.{0}} (hμ : μ + 1 < Om1) :
    xlK (μ + 1) = xlTU (xlSt_spec hμ) (xl_start_of_at le_add_self hμ (xlK_at ((lt_add_one μ).trans hμ))) := by
  rw [xlK_succ]; exact xlLT_eq le_add_self hμ (xlK_at ((lt_add_one μ).trans hμ))

/-- **The shape of `xlK λ` at a limit**: the top of the level `G + λ` over a union of the `xlK (heFs λ k)`. -/
theorem xlK_lim_eq {l : Ordinal.{0}} (hl : IsSuccLimit l) (hl1 : l < Om1) :
    ∃ (C : HgfCh) (hC : XlAt l C.U), (∀ k, C.D k = xlK (heFs l k)) ∧
      xlK l = xlTU (xlSt_spec hl1) (xl_start_of_at (xl_one_le_l hl) hl1 hC) := by
  have H : XlKInv l xlK := xlKInv_lim (fun β hβ => xlK_inv β (hβ.trans hl1))
  have Hx : XlKInv l (xlKExt l fun β _ => xlK β) := H.congr fun β h => xlKExt_eq h
  refine ⟨xlKCh hl hl1 (xlKExt l fun β _ => xlK β) Hx, xlKCh_at hl hl1 _ Hx,
    fun k => xlKExt_eq (xl_fs_lt hl hl1 k), ?_⟩
  rw [xlK_limit hl]; unfold xlKLim; rw [dif_pos ⟨hl1, Hx⟩]
  exact xlLT_eq (xl_one_le_l hl) hl1 (xlKCh_at hl hl1 _ Hx)

/-- **SMALL**: a code of `xlK ν` with gate below an `ε`-number `σ` lies in some `xlK μ`, `μ < σ`. -/
theorem xlK_small : ∀ ν, ν < Om1 → ∀ c, c < (xlK ν).B → ∀ σ, InE σ → σ < Om1 → (xlK ν).g c < σ →
    ∃ μ, μ < σ ∧ c < (xlK μ).B := by
  intro ν
  induction ν using WellFoundedLT.induction with
  | ind ν IH =>
  intro hν c hc σ hσ hσ1 hg
  by_cases hνσ : ν < σ
  · exact ⟨ν, hνσ, hc⟩
  rcases zero_or_succ_or_isSuccLimit ν with h0 | ⟨μ, hμ⟩ | hlim
  · exact absurd (by rw [h0]; exact hσ.pos) hνσ
  · have hμ' : ν = μ + 1 := by rw [← hμ, Order.succ_eq_add_one]
    subst hμ'
    have hμ1 : μ < Om1 := (lt_add_one μ).trans hν
    by_cases hcμ : c < (xlK μ).B
    · rw [(xlK_ext (le_add_right le_rfl) hν hcμ 0).2] at hg
      exact IH μ (lt_add_one μ) hμ1 c hcμ σ hσ hσ1 hg
    · exfalso
      have e := xlK_succ_eq hν
      rw [e] at hc hg
      have h := xlT_high _ _ hc (not_lt.1 hcμ) hσ hσ1 hg
      exact hνσ h
  · obtain ⟨C, hC, hD, e⟩ := xlK_lim_eq hlim hν
    by_cases hcU : c < C.U.B
    · obtain ⟨k, hk⟩ := C.B_cof c hcU
      have hk1 : heFs ν k < ν := xl_fs_lt hlim hν k
      have hg' : (xlK (heFs ν k)).g c < σ := by
        rw [e, xlTU_g0 _ _ hcU, C.U_g hk, hD] at hg; exact hg
      rw [hD] at hk
      exact IH _ hk1 (hk1.trans hν) c hk σ hσ hσ1 hg'
    · exfalso
      rw [e] at hc hg
      exact hνσ (xlT_high _ _ hc (not_lt.1 hcU) hσ hσ1 hg)

/-! ## The family and its union -/

theorem xl_GOm_lt1 : gcG 0 + Om1 < gcG 1 :=
  (inE_indec (Low.opow_eq_self_of_SC (gcG_SC 1))).add_lt (gcG_lt zero_lt_one) (gl_Om1_lt_G0.trans (gcG_lt zero_lt_one))

theorem xl_GOm_lim : IsSuccLimit (gcG 0 + Om1) := isSuccLimit_add _ gl_Om1_lim

section Rd

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem xl_lxx_lt : xfLv.l x + x < veblen (xfLv.l x + x) 0 :=
  xl_lt_veb0 hx.pos (by rw [xf_l hx hx1]; exact (lgG_facts hx hx1).2.1.trans_le le_self_add)

theorem xl_lxx_q : xfLv.l x + x < gq 1 x :=
  (inE_indec (gm1_facts hx hx1).2.2.2).add_lt (xfLv.l_lt x hx hx1) (gm1_facts hx hx1).2.1

/-- `ϑˣ(Ω₁·(Γ_{x+1} + x)) = φ(Γ_{x+1} + x, 0)`. -/
theorem xl_glA_W : glA (xfLv.succ.l x + 0) 0 x = veblen (xfLv.l x + x) 0 := by
  have h := xl_glAv (α := xfLv.l x + x) hx hx1 ((wo_one_lt_inE hx).le.trans ((xfLv.l_ge x).trans le_self_add))
    (xl_lxx_q hx hx1)
    ((xfLv.l_ge x).trans le_self_add) (xl_lxx_lt hx hx1)
    (he_N_lt1 hx hx1 ((ev_isSuccLimit_of_inE (gm1_facts hx hx1).2.2.2).add_one_lt (xl_lxx_q hx hx1))
      (gm1_facts hx hx1).2.2.2.pos) 0 (hcN_E _ _).pos
  show glA (xfLv.l x + x + 0) 0 x = _
  rw [add_zero]; exact h

end Rd

/-- **THE FAMILY OF THE LEVELS `G + κ`, `κ < Ω₁`**: bound `φ(G + Ω₁, 0)`, gate `1`, base reading
`φ(Γ_{x+1} + x, 0)`. -/
noncomputable def xlWF : HoFam where
  D := xlK
  B := veblen (gcG 0 + Om1) 0
  γ := 1
  b := fun x => veblen (xfLv.l x + x) 0
  Zo := xlZs
  γ_lt := wh_one_lt_Om1
  γ_cl := fun _ hZ _ _ => xc_one_lt_SC hZ
  G_lt := (by simpa using (add_lt_add_iff_left (gcG 0)).2 gv_Om1_pos : gcG 0 < gcG 0 + Om1).trans_le
    (left_le_veblen _ 0)
  B_E := gg_veblen_eps (xl_GOm_lim.bot_lt.ne')
  B_lt1 := by
    have h := (isNormal_veblen (gcG 0 + Om1)).strictMono (gcG_SC 1).1
    rwa [gn_veb_fix (gcG_SC 1) xl_GOm_lt1] at h
  B_fix1 := veblen_veblen_of_lt ((wh_one_lt_Om1.trans_le le_add_self)) 0
  B_mem := fun S _ _ ha _ => CSet.phi_mem (CSet.add_mem (gmS_G0_mem S ha)
    (by rw [Br.Om1_eq]; exact CSet.Om_mem (CSet.one_mem _ _))) (CSet.zero_mem _ _)
  DB_lt := fun μ hμ => by
    rw [xlK_B hμ]
    exact veblen_zero_lt_veblen_zero.2 ((add_lt_add_iff_left _).2 (gl_Om1_lim.add_one_lt hμ))
  B_cof := fun c hc => by
    obtain ⟨a, ha, hca⟩ := wx_veb_lim_cof0 xl_GOm_lim hc
    obtain ⟨d, hd, had⟩ := (lt_add_iff gl_Om1_lim.bot_lt.ne').1 ha
    refine ⟨d, hd, ?_⟩
    rw [xlK_B hd]
    exact hca.trans_le (veblen_zero_le_veblen_zero.2 (had.trans ((add_le_add_iff_left _).2 le_self_add)))
  ext := fun μ' μ h hμ c x hc => xlK_ext h hμ hc x
  small := fun μ hμ c hc σ hσ hσ1 hg => xlK_small μ hμ c hc σ hσ hσ1 hg
  γD := fun x hx _ _ μ hμ => (xlK_γ (hμ.trans ‹x < Om1›)).trans_lt ((ev_isSuccLimit_of_inE hx).add_one_lt hμ)
  bD := fun x hx hx1 _ μ hμ => by
    rw [(xlK_at (hμ.trans hx1)).b x hx hx1 ((ev_isSuccLimit_of_inE hx).add_one_lt hμ)]
    exact veblen_zero_lt_veblen_zero.2 ((add_lt_add_iff_left _).2 ((ev_isSuccLimit_of_inE hx).add_one_lt hμ))
  ZD := fun x hx hx1 _ μ hμ => by
    have hμ1 : μ + 1 < x := (ev_isSuccLimit_of_inE hx).add_one_lt hμ
    rw [(xlK_at (hμ.trans hx1)).Z x hx hx1, if_pos hμ1]
    have h2 : (2 : Ordinal.{0}) < xfLv.l x + x :=
      ((show (2 : Ordinal.{0}) < ω from (by exact_mod_cast natCast_lt_omega0 2)).trans_le
        ((omega0_lt_inE hx).le.trans (xfLv.l_ge x))).trans_le le_self_add
    exact (hb_evZ_lt_fix2 (veblen_veblen_of_lt h2 0)
      (veblen_zero_lt_veblen_zero.2 ((add_lt_add_iff_left _).2 hμ1))).le
  b_cof := fun x hx hx1 _ ν hν => by
    obtain ⟨a, ha, hνa⟩ := wx_veb_lim_cof0 (isSuccLimit_add _ (ev_isSuccLimit_of_inE hx)) hν
    obtain ⟨d, hd, had⟩ := (lt_add_iff hx.pos.ne').1 ha
    refine ⟨d, hd, ?_⟩
    rw [(xlK_at (hd.trans hx1)).b x hx hx1 ((ev_isSuccLimit_of_inE hx).add_one_lt hd)]
    exact hνa.trans_le (veblen_zero_le_veblen_zero.2 (had.trans ((add_le_add_iff_left _).2 le_self_add)))
  b_E := fun _ hx _ _ => gg_veblen_eps (hx.pos.trans_le le_add_self).ne'
  x_lt_b := fun x hx hx1 _ => ((xfLv.l_ge x).trans le_self_add).trans_lt (xl_lxx_lt hx hx1)
  b_fix1 := fun x hx _ _ => veblen_veblen_of_lt ((wo_one_lt_inE hx).trans_le le_add_self) 0
  b_lt1 := fun x hx hx1 _ => (veblen_zero_lt_veblen_zero.2 (lt_add_one _) |>.trans_eq
    (xlZs_eq hx).symm).trans (xlZs_G1 hx hx1)
  b_pi := fun σ ρ hB hγ => by
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
    have h0σ : (0 : Ordinal.{0}) < σ := hB.1.pos
    have h := hnv_glA_pi xfLv.succ (ν := 0) hB (by show xfLv.g < σ; rw [xfLv_g]; exact hγ) h0σ
      (mem_TB_of_lt hB h0σ) (gm1_facts hB.2.1 hρ1).2.2.2.pos
    rw [pi_lt hB h0σ, xl_glA_W hB.2.1 hρ1, xl_glA_W hB.1 hσ1] at h
    exact h
  Z_low := fun _ _ x hx _ h => absurd (wo_one_lt_inE hx) h
  Zo_fix := xlZs_fix
  Zo_G1 := fun _ hx hx1 => xlZs_G1 hx hx1

/-- **THE SYSTEM AT `φ(G + Ω₁, 0)`**: the union of all `xlK κ`, `κ < Ω₁`; gate `1`, base reading
`φ(Γ_{x+1} + x, 0)`. -/
noncomputable def xlW : HgVD := hoOU xlWF

theorem xlW_B : xlW.B = veblen (gcG 0 + Om1) 0 := rfl

theorem xlW_γ : xlW.γ = 1 := rfl

theorem xlW_b (x : Ordinal.{0}) : xlW.b x = veblen (xfLv.l x + x) 0 := rfl

/-- **`xlW` extends every `xlK κ`** (hence `Xl.xlTop`, `Xf.xfV1`, `Hg.hgU`). -/
theorem xlW_ext {κ c : Ordinal.{0}} (hκ : κ < Om1) (hc : c < (xlK κ).B) (x : Ordinal.{0}) :
    xlW.R c x = (xlK κ).R c x ∧ xlW.g c = (xlK κ).g c := ⟨hoOU_R xlWF hκ hc x, hoOU_g xlWF hκ hc⟩

/-- **`xlW` extends `Hg.hgU`** (the system at `φ(Ω₁, G+1)`). -/
theorem xlW_hgU {c : Ordinal.{0}} (hc : c < hgU.B) (x : Ordinal.{0}) :
    xlW.R c x = hgU.R c x ∧ xlW.g c = hgU.g c := by
  have hc1 : c < xfV1.B := (hc.trans_le (ws_S1_le (xf_cf_lev 0) (wsSh_hgU wsA2_G) (xfD_M 0).1)).trans (xfCh.B_lt 0)
  have hcT : c < (xlK 0).B := by
    rw [xlK_zero]; refine hc1.trans_le (le_of_lt ?_)
    have h := xl_V_lt_top xlN_E.pos; rwa [add_zero] at h
  obtain ⟨e1, e2⟩ := xlW_ext gv_Om1_pos hcT x
  rw [xlK_zero] at e1 e2
  obtain ⟨f1, f2⟩ := xlTop_hgU hc x
  exact ⟨e1.trans f1, e2.trans f2⟩

/-! ## The frontier `ι(Γ(φ(G + Ω₁, 0))·ω)` -/

section Fr

variable (S : InaccSeq.{0})

theorem xlW_γK : xlW.γ < Td.tdK S := xf_one_lt_gam0.trans_le (Td.tdGam_le_K (S := S))

/-- **`φ(G + Ω₁, 0)` IS LOCATED**: `Λ⁺ = ι(Γ(φ(G + Ω₁, 0))·ω)`, `P(…) < L(0)` (UNCONDITIONAL). -/
theorem xlw_loc :
    ∃ X : Xt.XtSys, Xt.XtTopPkg X ∧ Xt.xtB1 X = iota S (gcG (veblen (gcG 0 + Om1) 0) * ω) ∧
      upsilon (Xt.xtB1 X) = Nm.Pv S (gcG (veblen (gcG 0 + Om1) 0) * ω) ∧
        Nm.Pv S (gcG (veblen (gcG 0 + Om1) 0) * ω) < Nc.ncL S 0 :=
  hgV_locD xlW S (xlW_γK S)

theorem xlw_enum {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG (veblen (gcG 0 + Om1) 0) * ω)) :
    CdUpper S l ∧ CdLower S l := hgV_locD_enum xlW S (xlW_γK S) hr hl

theorem xlw_capV {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG (veblen (gcG 0 + Om1) 0) * ω)) :
    CdCapV S l := hgV_locD_capV xlW S (xlW_γK S) hr hl

/-- **EVERY `B ≤ φ(G + Ω₁, 0)` IS BELOW THE BOUND OF A SYSTEM WITH GATE `< K`** (UNCONDITIONAL). -/
theorem xlw_sysG : ∀ B, B ≤ veblen (gcG 0 + Om1) 0 → ∃ V : HgVD, B ≤ V.B ∧ V.γ < Td.tdK S :=
  fun _ hB => ⟨xlW, hB, xlW_γK S⟩

/-- **`l` lies past the new frontier `ι(Γ(φ(G + Ω₁, 0))·ω)`.** -/
def XlWPast (l : Ordinal.{0}) : Prop := iota S (gcG (veblen (gcG 0 + Om1) 0) * ω) ≤ l

theorem xlw_notPast {l : Ordinal.{0}} (hr : CdRange S l) (h : ¬ XlWPast S l) :
    CdUpper S l ∧ CdLower S l ∧ CdCapV S l := by
  unfold XlWPast at h; push Not at h
  exact ⟨(xlw_enum S hr h).1, (xlw_enum S hr h).2, xlw_capV S hr h⟩

/-- **The old frontier lies below the new one.** -/
theorem xlw_FK_le {κ : Ordinal.{0}} (hκ : κ < Td.tdK S) :
    iota S (gcG (veblen (gcG 0 + (κ + 1)) 0) * ω) ≤ iota S (gcG (veblen (gcG 0 + Om1) 0) * ω) := by
  refine iota_mono _ _ (mul_le_mul_left (gcG_le ?_) ω)
  have hκ1 : κ < Om1 := hκ.trans (xl_K_lt_Om1 S)
  exact veblen_zero_le_veblen_zero.2 ((add_le_add_iff_left _).2 (gl_Om1_lim.add_one_lt hκ1).le)

/-- **Past the new frontier ⇒ past `F_K`** (`Xl.XlKPast`). -/
theorem xlw_past_k {l : Ordinal.{0}} (h : XlWPast S l) : XlKPast S l := fun _ hκ => (xlw_FK_le S hκ).trans h

end Fr

variable {S : InaccSeq.{0}}

/-- **NON-VACUITY (relative)**: the four hypotheses of `xlwRoad` are EQUIVALENT to those of `Xl.xlkRoad`. -/
theorem xlwRoad_hyp_iff :
    ((∀ l, CdRange S l → XlKPast S l → CdUpper S l) ↔ (∀ l, CdRange S l → XlWPast S l → CdUpper S l)) ∧
    ((∀ l, CdRange S l → XlKPast S l → CdLower S l) ↔ (∀ l, CdRange S l → XlWPast S l → CdLower S l)) ∧
    ((∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XlKPast S l → CdCapV S l) ↔
      (∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XlWPast S l → CdCapV S l)) ∧
    ((∀ l, CdRange S l → Nc.ncL S ω < upsilon l → XlKPast S l → CdCapV S l) ↔
      (∀ l, CdRange S l → Nc.ncL S ω < upsilon l → XlWPast S l → CdCapV S l)) := by
  refine ⟨⟨fun h l hr hp => h l hr (xlw_past_k S hp), fun h l hr _ => ?_⟩,
    ⟨fun h l hr hp => h l hr (xlw_past_k S hp), fun h l hr _ => ?_⟩,
    ⟨fun h l hr hu hp => h l hr hu (xlw_past_k S hp), fun h l hr hu _ => ?_⟩,
    ⟨fun h l hr hu hp => h l hr hu (xlw_past_k S hp), fun h l hr hu _ => ?_⟩⟩
  · by_cases hp : XlWPast S l
    · exact h l hr hp
    · exact (xlw_notPast S hr hp).1
  · by_cases hp : XlWPast S l
    · exact h l hr hp
    · exact (xlw_notPast S hr hp).2.1
  · by_cases hp : XlWPast S l
    · exact h l hr hu hp
    · exact (xlw_notPast S hr hp).2.2
  · by_cases hp : XlWPast S l
    · exact h l hr hu hp
    · exact (xlw_notPast S hr hp).2.2

/-- **THE ROAD `Xf.xfRoad` WITH UPPER / LOWER / CapV ASKED ONLY PAST `ι(Γ(φ(G + Ω₁, 0))·ω)`.** -/
theorem xlwRoad
    (hUH : ∀ l, CdRange S l → XlWPast S l → CdUpper S l)
    (hLH : ∀ l, CdRange S l → XlWPast S l → CdLower S l)
    (hVH : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XlWPast S l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → XlWPast S l → CdCapV S l)
    (hT : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdThLow S)
    (hF : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdEQfar S)
    (hS : Xb.XbShift S)
    (h0 : ∀ l, IsRestartIdx l → Nc.ncL S 0 = upsilon l →
      Xb.XbVisGen S l (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Te.teW (Nc.ncL S 0))))
    (hn : ∀ n : ℕ, ∀ l, IsRestartIdx l → Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) = upsilon l →
      Xb.XbVisGen S l (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
        (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Te.teW (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))) :
    CdTC S ∧ CdEMB2 S ∧ CdCL S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S (k + 1)) (Nc.ncL S (ω + 1)) := by
  obtain ⟨a, b, c, d⟩ := xlwRoad_hyp_iff (S := S)
  exact xlkRoad (a.2 hUH) (b.2 hLH) (c.2 hVH) (d.2 hVt) hT hF hS h0 hn

/-- **The conclusion of `Xb.xbRoadZ` with UPPER / LOWER / CapV asked only past `ι(Γ(φ(G + Ω₁, 0))·ω)`.** -/
theorem xlwRoadZ
    (hUH : ∀ l, CdRange S l → XlWPast S l → CdUpper S l)
    (hLH : ∀ l, CdRange S l → XlWPast S l → CdLower S l)
    (hVH : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XlWPast S l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → XlWPast S l → CdCapV S l)
    (hT : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdThLow S)
    (hF : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdEQfar S)
    (hS : Xb.XbShift S)
    (h0 : ∀ l, IsRestartIdx l → Nc.ncL S 0 = upsilon l →
      Xb.XbVisGen S l (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Te.teW (Nc.ncL S 0))))
    (hn : ∀ n : ℕ, ∀ l, IsRestartIdx l → Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) = upsilon l →
      Xb.XbVisGen S l (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
        (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Te.teW (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S (k + 1)) (Nc.ncL S (ω + 1)) := by
  obtain ⟨a, b, c, d⟩ := xlwRoad_hyp_iff (S := S)
  exact xlkRoadZ (a.2 hUH) (b.2 hLH) (c.2 hVH) (d.2 hVt) hT hF hS h0 hn

end Googology.Trans.PoR.InaccPsi.R2.Xl
