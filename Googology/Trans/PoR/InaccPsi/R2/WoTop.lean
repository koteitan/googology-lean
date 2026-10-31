import Googology.Trans.PoR.InaccPsi.R2.WoEnt
import Googology.Trans.PoR.InaccPsi.R2.WfRoad
import Googology.Trans.PoR.InaccPsi.R2.HoRoad

/-!
# WoTop: THE SYSTEM AT `φ(ε_{Ω₁+1}, G+1)`; THE FRONTIER `ι(Γ(φ(ε_{Ω₁+1}, G+1))·ω)`; THE ROAD

* `woU x k` (the tower `1, x, x^x, …`), `woU_cof` (**it is cofinal in `ε_{x+1}`** for every `ε`-number `x`), `woT k`
  (`= woU Ω₁ k`: levels `Ω₁, Ω₁^{Ω₁}, …` cofinal in `ε_{Ω₁+1}`, gate `1`, reading `woU x k`);
* `woChE` (**the gated `ω`-chain over `G` of the systems `Wo.woV (woT (k+1))`**: bound `φ(ε_{Ω₁+1}, G+1)`, gate `1`,
  base reading `φ(ε_{x+1}, Γ_{x+1}+1)`), `woVE` (its union);
* `woE_loc`, `woE_enum`, `woE_capV` (**`φ(ε_{Ω₁+1}, G+1)` IS LOCATED; ENUM-REACH and CapV at every range restart
  below `ι(Γ(φ(ε_{Ω₁+1}, G+1))·ω)`**, UNCONDITIONAL), `woE_fr_order`;
* `woRoad` (**THE ROAD `Wf.wfRoad` WITH UPPER / LOWER / CapV ASKED ONLY ABOVE THE NEW FRONTIER**), `woRoad_hyp_iff`
  (**the four new hypotheses are EQUIVALENT to those of `Wf.wfRoad`**: non-vacuity relative to `Wf.wfRoad`).

No new axiom.  New definitions: `woU`, `woT`, `woChE`, `woVE`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Wo

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
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Bt

/-! ## The tower -/

/-- **The tower** `1, x, x^x, x^{x^x}, …`. -/
noncomputable def woU (x : Ordinal.{0}) : ℕ → Ordinal.{0}
  | 0 => 1
  | k + 1 => x ^ woU x k

theorem woU_succ (x : Ordinal.{0}) (k : ℕ) : woU x (k + 1) = x ^ woU x k := rfl

theorem wo_two_le {x : Ordinal.{0}} (hx : InE x) : (2 : Ordinal.{0}) ≤ x :=
  ((show (2 : Ordinal.{0}) < ω from by exact_mod_cast natCast_lt_omega0 2).trans (omega0_lt_inE hx)).le

/-- `ω`-iterates from `x + 1` lie below the tower. -/
theorem woU_iter {x : Ordinal.{0}} (hx : InE x) : ∀ n : ℕ, (fun a : Ordinal.{0} => ω ^ a)^[n] (x + 1) ≤ woU x (n + 2)
  | 0 => by
    show x + 1 ≤ x ^ (x ^ (1 : Ordinal.{0}))
    rw [opow_one]
    have e2 : x * 2 = x + x := by
      rw [show (2 : Ordinal.{0}) = 1 + 1 from one_add_one_eq_two.symm, mul_add, mul_one]
    have e3 : x ^ (2 : Ordinal.{0}) = x * x := by
      rw [show (2 : Ordinal.{0}) = 1 + 1 from one_add_one_eq_two.symm, opow_add, opow_one]
    calc x + 1 ≤ x + x := (add_le_add_iff_left x).2 (one_le_iff_pos.2 hx.pos)
    _ = x * 2 := e2.symm
    _ ≤ x * x := mul_le_mul_left' (wo_two_le hx) x
    _ = x ^ (2 : Ordinal.{0}) := e3.symm
    _ ≤ x ^ x := opow_le_opow_right hx.pos (wo_two_le hx)
  | n + 1 => by
    rw [Function.iterate_succ_apply']
    show ω ^ _ ≤ x ^ woU x (n + 2)
    exact (opow_le_opow_right omega0_pos (woU_iter hx n)).trans
      (opow_le_opow_left _ (omega0_lt_inE hx).le)

/-- **THE TOWER IS COFINAL IN `ε_{x+1}`.** -/
theorem woU_cof {x y : Ordinal.{0}} (hx : InE x) (hy : y < eN x) : ∃ k, y < woU x k := by
  obtain ⟨n, hn⟩ := lt_nfp_iff.1 hy
  exact ⟨n + 2, hn.trans_le (woU_iter hx n)⟩

/-- The levels `Ω₁, Ω₁^{Ω₁}, …`. -/
noncomputable def woT (k : ℕ) : Ordinal.{0} := woU Om1 k

theorem wo_pow_lt_E {l : Ordinal.{0}} (hl : l < gfE) : Om1 ^ l < gfE := by
  rw [Om1_pow_eq]
  have h := eW_E
  have hm : Om1 * l < gfE := h.mul_lt Om1_lt_eW hl
  have := (isNormal_opow one_lt_omega0).strictMono hm
  rwa [show ω ^ gfE = gfE from h] at this

/-- The facts of the levels `woT k`: below `ε_{Ω₁+1}`, gate `1`, reading `woU x k`. -/
theorem woT_facts : ∀ k : ℕ, woT k < gfE ∧ gtc (woT k) = 1 ∧ ∀ x, rdc (woT k) x = woU x k
  | 0 => ⟨gf_one_lt_Om1.trans Om1_lt_eW, (rdc_const gf_one_lt_Om1 0).2, fun x => (rdc_const gf_one_lt_Om1 x).1⟩
  | k + 1 => by
    obtain ⟨h1, h2, h3⟩ := woT_facts k
    refine ⟨wo_pow_lt_E h1, ?_, fun x => ?_⟩
    · show gtc (Om1 ^ woT k) = 1
      rw [(rdc_pow h1 0).2, h2, max_self]
    · show rdc (Om1 ^ woT k) x = x ^ woU x k
      rw [(rdc_pow h1 x).1, h3]

theorem woT_ge_one : ∀ k : ℕ, (1 : Ordinal.{0}) ≤ woT k
  | 0 => le_rfl
  | k + 1 => (one_le_iff_pos.2 (opow_pos _ wh_Om1_pos))

theorem woT_lev (k : ℕ) : WmLev (woT (k + 1)) :=
  ⟨wm_Om1_le_pow (woT_ge_one k), wm_Om1_dvd_pow (woT_ge_one k), (woT_facts (k + 1)).1⟩

theorem woT_lt_succ (k : ℕ) : woT k < woT (k + 1) := lt_Om1_pow (woT_facts k).1

theorem woT_mono {k k' : ℕ} (h : k ≤ k') : woT k ≤ woT k' := by
  induction k', h using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih => exact ih.trans (woT_lt_succ n).le

/-! ## The system at `φ(ε_{Ω₁+1}, G+1)` -/

theorem wo_G_fixE : veblen gfE (gcG 0) = gcG 0 := gn_veb_fix (gcG_SC 0) gfE_lt_G0

theorem woZo_eq {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : whZo x = hdNx (eN x) (lgG x) := by
  unfold whZo
  rw [max_eq_right (omega0_lt_inE hx).le, hdNx_fixP (hjG_fix hx hx1 (wh_one_le_eN x) (wh_eN_lt_lgG hx hx1))]

theorem woVk_b {k : ℕ} {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    (woV (woT (k + 1))).b x = hdNx (woU x (k + 1)) (lgG x) := by
  have hg : max woG.γ (gtc (woT (k + 1))) < x := by
    rw [(woT_facts (k + 1)).2.1]; exact max_lt hx.pos (wo_one_lt_inE hx)
  rw [(woV_sh (woT_lev k)).2.2.2.1 x hx hx1 hg, (woT_facts (k + 1)).2.2 x]; rfl

theorem woU_lt_eN {x : Ordinal.{0}} (hx : InE x) (k : ℕ) : woU x k < eN x := by
  have h := rdc_lt_eN hx (woT k) (by rw [(woT_facts k).2.1]; exact wo_one_lt_inE hx)
  rwa [(woT_facts k).2.2 x] at h

/-- **THE GATED `ω`-CHAIN OVER `G` OF THE SYSTEMS AT THE LEVELS `woT (k+1)`.** -/
noncomputable def woChE : HgfCh where
  D := fun k => woV (woT (k + 1))
  B := veblen gfE (gcG 0 + 1)
  b := whZo
  γ := 1
  Zo := whZo
  γ_lt := gf_one_lt_Om1
  γ0 := fun k => (woV_γ (woT_lev k)).trans (woT_facts (k + 1)).2.1.le
  γ_cl := fun Z hZ _ _ => by
    have := hZ.isSuccLimit.add_one_lt hZ.1; rwa [zero_add] at this
  B_mono := fun k => by
    rw [woV_B (woT_lev k), woV_B (woT_lev (k + 1))]
    exact (hd_veb_left_lt (woT_lt_succ (k + 1)) _).le
  B_lt := fun k => by rw [woV_B (woT_lev k)]; exact hd_veb_left_lt (woT_facts (k + 1)).1 _
  B_cof := fun c hc => by
    rw [← hdNx_fixP wo_G_fixE] at hc
    obtain ⟨b, hb, hcb⟩ := hjw_Nx_cof (wh_Om1_pos.trans Om1_lt_eW).ne' ⟨gcG 0, wo_G_fixE⟩ hc
    obtain ⟨k, hk⟩ := woU_cof gl_Om1_E (show b + 1 < eN Om1 from (eW_E |> fun h =>
      (ev_isSuccLimit_of_inE h).add_one_lt hb))
    refine ⟨k, ?_⟩
    rw [woV_B (woT_lev k), ← hdNx_fixP (wo_G_fix (woT_lev k))]
    exact hcb.trans (hdN_lt_Nx (hk.trans_le (woT_lt_succ k).le))
  R_ext := fun k c x hc =>
    ((woFam _ (woT_lev (k + 1))).2 _ (woT_lt_succ (k + 1)) (woT_lev k) woG hgU (woGood_G (woT_lev (k + 1)))
      woSh_hgU c x hc).1
  g_ext := fun k c hc =>
    ((woFam _ (woT_lev (k + 1))).2 _ (woT_lt_succ (k + 1)) (woT_lev k) woG hgU (woGood_G (woT_lev (k + 1)))
      woSh_hgU c 0 hc).2
  B_lt1 := by
    have hG1 := gcG_SC 1
    have hE := Low.opow_eq_self_of_SC hG1
    have hfix : veblen gfE (gcG 1) = gcG 1 := gn_veb_fix hG1 (gfE_lt_G0.trans (gcG_lt zero_lt_one))
    have h2 := (isNormal_veblen gfE).strictMono ((ev_isSuccLimit_of_inE hE).add_one_lt (gcG_lt zero_lt_one))
    rwa [hfix] at h2
  B_fix := veblen_veblen_of_lt (gf_one_lt_Om1.trans Om1_lt_eW) _
  B_mem := fun S a b ha hb => by
    have hEB : gfE < hgU.B := gfE_lt_G0.trans_le hgU.G_le
    refine CSet.phi_mem (hgU.mem S a b ha gfE hEB ?_).1 (CSet.succ_mem (gmS_G0_mem S ha))
    rw [hgU.g_E]; exact zero_lt_one.trans hb
  b_ge := fun k x hx hx1 _ => by
    rw [woVk_b hx hx1, woZo_eq hx hx1]
    exact hdNx_mono (woU_lt_eN hx (k + 1)).le _
  b_cof := fun x hx hx1 _ ν hν => by
    rw [woZo_eq hx hx1] at hν
    obtain ⟨b, hb, hνb⟩ := hjw_Nx_cof (eN_E x).pos.ne' ⟨lgG x, hjG_fix hx hx1 (wh_one_le_eN x) (wh_eN_lt_lgG hx hx1)⟩ hν
    obtain ⟨k, hk⟩ := woU_cof hx ((ev_isSuccLimit_of_inE (eN_E x)).add_one_lt hb)
    refine ⟨k, ?_⟩
    rw [woVk_b hx hx1]
    have hmono : woU x k ≤ woU x (k + 1) := by
      rw [← (woT_facts k).2.2 x, ← (woT_facts (k + 1)).2.2 x]
      exact rdc_le_mono hx (woT_facts (k + 1)).1 (woT_lt_succ k).le
        (by rw [(woT_facts (k + 1)).2.1]; exact wo_one_lt_inE hx) (by rw [(woT_facts k).2.1]; exact wo_one_lt_inE hx)
    exact hνb.trans (hdN_lt_Nx (hk.trans_le hmono))
  b_fix := fun x _ _ _ => hc_fix_down one_le_two (whZo_fix x)
  b_gt := fun x hx hx1 _ => by
    rw [woZo_eq hx hx1]
    exact (((lt_eN x).trans (wh_eN_lt_lgG hx hx1))).trans (hdNx_gt _ _)
  b_lt := fun x hx hx1 _ => whZo_G1 hx hx1
  b_pi := fun σ ρ hB _ => by
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
    rw [woZo_eq hB.2.1 hρ1, woZo_eq hB.1 hσ1]
    exact hjG_S_pi hB (Gh.gh_eN_pi hB) (wh_one_le_eN ρ) (wh_eN_lt_lgG hB.2.1 hρ1) (wh_one_le_eN σ)
      (wh_eN_lt_lgG hB.1 hσ1)
  Z_low := fun _ x hx _ h => absurd (wo_one_lt_inE hx) h
  Zo_fix := fun x => hc_fix_down one_le_two (whZo_fix x)
  Zo_G1 := fun x hx hx1 => whZo_G1 hx hx1

/-- **THE SYSTEM OVER `G` AT `φ(ε_{Ω₁+1}, G+1)`**, gate `1`. -/
noncomputable def woVE : HgVD := woChE.U

theorem woVE_B : woVE.B = veblen gfE (gcG 0 + 1) := rfl

theorem woVE_γ : woVE.γ = 1 := rfl

/-! ## The frontier -/

section Fr

variable (S : InaccSeq.{0})

theorem woVE_γK : woVE.γ < Td.tdK S := by
  rw [woVE_γ]
  exact ((one_lt_omega0.trans (omega0_lt_epsilon 0)).trans gq_eps0_lt_gam).trans_le (Td.tdGam_le_K (S := S))

/-- **`φ(ε_{Ω₁+1}, G+1)` IS LOCATED**: `Λ⁺ = ι(Γ(φ(ε_{Ω₁+1}, G+1))·ω)`, `P(…) < L(0)` (UNCONDITIONAL). -/
theorem woE_loc : ∃ X : Xt.XtSys, Xt.XtTopPkg X ∧ Xt.xtB1 X = iota S (gcG woVE.B * ω) ∧
    upsilon (Xt.xtB1 X) = Nm.Pv S (gcG woVE.B * ω) ∧ Nm.Pv S (gcG woVE.B * ω) < Nc.ncL S 0 :=
  hgV_locD woVE S (woVE_γK S)

/-- **ENUM-REACH at every range restart below `ι(Γ(φ(ε_{Ω₁+1}, G+1))·ω)`** (UNCONDITIONAL). -/
theorem woE_enum {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG woVE.B * ω)) :
    CdUpper S l ∧ CdLower S l := hgV_locD_enum woVE S (woVE_γK S) hr hl

/-- **CapV at every range restart below `ι(Γ(φ(ε_{Ω₁+1}, G+1))·ω)`** (UNCONDITIONAL). -/
theorem woE_capV {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG woVE.B * ω)) : CdCapV S l :=
  hgV_locD_capV woVE S (woVE_γK S) hr hl

theorem wo_O3_lt_E : (Om1 : Ordinal.{0}) * Om1 * Om1 < gfE :=
  eW_E.mul_lt (eW_E.mul_lt Om1_lt_eW Om1_lt_eW) Om1_lt_eW

/-- **The frontiers in order**: `ι(Γ(φ(Ω₁², G+1))·ω) ≤ ι(Γ(φ(Ω₁³, G+1))·ω) ≤ ι(Γ(φ(ε_{Ω₁+1}, G+1))·ω)`. -/
theorem woE_fr_order : iota S (gcG hlU.B * ω) ≤ iota S (gcG hoUf.B * ω) ∧
    iota S (gcG hoUf.B * ω) ≤ iota S (gcG woVE.B * ω) := by
  have h0 : (Om1 : Ordinal.{0}) * Om1 < Om1 * Om1 * Om1 := by
    have := mul_lt_mul_of_pos_left wh_one_lt_Om1 (mul_pos wh_Om1_pos wh_Om1_pos)
    rwa [mul_one] at this
  have h1 : hlU.B ≤ hoUf.B := by rw [hlU_B, hoUf_B]; exact (hd_veb_left_lt h0 _).le
  have h2 : hoUf.B ≤ woVE.B := by rw [hoUf_B, woVE_B]; exact (hd_veb_left_lt wo_O3_lt_E _).le
  exact ⟨iota_mono _ _ (mul_le_mul_right' (gcG_le h1) ω), iota_mono _ _ (mul_le_mul_right' (gcG_le h2) ω)⟩

/-- **THE ROAD `Wf.wfRoad` WITH UPPER / LOWER / CapV ASKED ONLY ABOVE `ι(Γ(φ(ε_{Ω₁+1}, G+1))·ω)`.** -/
theorem woRoad
    (hUH : ∀ l, CdRange S l → iota S (gcG woVE.B * ω) ≤ l → CdUpper S l)
    (hLH : ∀ l, CdRange S l → iota S (gcG woVE.B * ω) ≤ l → CdLower S l)
    (hVH : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S (gcG woVE.B * ω) ≤ l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → iota S (gcG woVE.B * ω) ≤ l → CdCapV S l)
    (hT : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdThLow S)
    (hF : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdEQfar S)
    (h0 : ∀ l, IsRestartIdx l → Nc.ncL S 0 = upsilon l →
      Wf.WfVisGen S l (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Te.teW (Nc.ncL S 0))))
    (hn : ∀ n : ℕ, ∀ l, IsRestartIdx l → Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) = upsilon l →
      Wf.WfVisGen S l (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
        (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Te.teW (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))) :
    CdTC S ∧ CdEMB2 S ∧ CdCL S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S (k + 1)) (Nc.ncL S (ω + 1)) := by
  refine Wf.wfRoad (fun l hr _ => ?_) (fun l hr _ => ?_) (fun l hr hu _ => ?_) (fun l hr hu _ => ?_) hT hF h0 hn
  · rcases lt_or_ge l (iota S (gcG woVE.B * ω)) with h | h
    · exact (woE_enum S hr h).1
    · exact hUH l hr h
  · rcases lt_or_ge l (iota S (gcG woVE.B * ω)) with h | h
    · exact (woE_enum S hr h).2
    · exact hLH l hr h
  · rcases lt_or_ge l (iota S (gcG woVE.B * ω)) with h | h
    · exact woE_capV S hr h
    · exact hVH l hr hu h
  · rcases lt_or_ge l (iota S (gcG woVE.B * ω)) with h | h
    · exact woE_capV S hr h
    · exact hVt l hr hu h

/-- **NON-VACUITY (relative)**: the four hypotheses UPPER, LOWER, CapV (`υ_λ < L(ω)`), CapV (`L(ω) < υ_λ`) of
`woRoad` are EQUIVALENT to those of `Wf.wfRoad` (asked from `ι(Γ(φ(Ω₁·Ω₁, G+1))·ω)` on). -/
theorem woRoad_hyp_iff :
    ((∀ l, CdRange S l → iota S (gcG hlU.B * ω) ≤ l → CdUpper S l) ↔
      (∀ l, CdRange S l → iota S (gcG woVE.B * ω) ≤ l → CdUpper S l)) ∧
    ((∀ l, CdRange S l → iota S (gcG hlU.B * ω) ≤ l → CdLower S l) ↔
      (∀ l, CdRange S l → iota S (gcG woVE.B * ω) ≤ l → CdLower S l)) ∧
    ((∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S (gcG hlU.B * ω) ≤ l → CdCapV S l) ↔
      (∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S (gcG woVE.B * ω) ≤ l → CdCapV S l)) ∧
    ((∀ l, CdRange S l → Nc.ncL S ω < upsilon l → iota S (gcG hlU.B * ω) ≤ l → CdCapV S l) ↔
      (∀ l, CdRange S l → Nc.ncL S ω < upsilon l → iota S (gcG woVE.B * ω) ≤ l → CdCapV S l)) := by
  have hle : iota S (gcG hlU.B * ω) ≤ iota S (gcG woVE.B * ω) :=
    (woE_fr_order S).1.trans (woE_fr_order S).2
  refine ⟨⟨fun h l hr hl => h l hr (hle.trans hl), fun h l hr hl => ?_⟩,
    ⟨fun h l hr hl => h l hr (hle.trans hl), fun h l hr hl => ?_⟩,
    ⟨fun h l hr hu hl => h l hr hu (hle.trans hl), fun h l hr hu hl => ?_⟩,
    ⟨fun h l hr hu hl => h l hr hu (hle.trans hl), fun h l hr hu hl => ?_⟩⟩
  · rcases lt_or_ge l (iota S (gcG woVE.B * ω)) with h' | h'
    · exact (woE_enum S hr h').1
    · exact h l hr h'
  · rcases lt_or_ge l (iota S (gcG woVE.B * ω)) with h' | h'
    · exact (woE_enum S hr h').2
    · exact h l hr h'
  · rcases lt_or_ge l (iota S (gcG woVE.B * ω)) with h' | h'
    · exact woE_capV S hr h'
    · exact h l hr hu h'
  · rcases lt_or_ge l (iota S (gcG woVE.B * ω)) with h' | h'
    · exact woE_capV S hr h'
    · exact h l hr hu h'

end Fr

end Googology.Trans.PoR.InaccPsi.R2.Wo
