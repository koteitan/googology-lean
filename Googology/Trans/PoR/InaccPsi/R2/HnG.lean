import Googology.Trans.PoR.InaccPsi.R2.HnRec

/-!
# HnG: OVER `G`, ONE RECURSION OF SYSTEMS AT `φ(Ω₁·Ω₁ + Ω₁·μ, G+1)`, `μ < Ω₁`

PORT of `Hl.HlG` to the band levels: `hnkGS 0 = Hl.hlU` (bound `φ(Ω₁·Ω₁, G+1)`), `hnkGS (μ+1)` is the union over `G`
(`hnGW`) of the levels `Ω₁·Ω₁ + Ω₁·μ + κ` with the steps of the package `hnkPk μ`, and at a limit `λ` the union of
the gated `ω`-chain of the systems at `heFs λ k`.  What differs from `Hl.HlG`: the levels `Ω₁·Ω₁ + Ω₁·μ` read
`x·x + x·μ`, the start `Hl.hlU` (with `hnU_shape`) in place of `Hg.hgU`, the base `hnGW Λ hN` asks the outer-field
bound `HnNB` (supplied by `hnkNB`), the outer low field `φ(x·x·2, Γ_{x+1}+1)`.

No new axiom.  New definitions: `HnkGCoh`, `hnkGCh`, `hnkGLimF`, `hnkGSucc`, `hnkGS`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hn

open Googology.Trans.PoR.InaccPsi.R2.Hl
open Googology.Trans.PoR.InaccPsi.R2.Hj Googology.Trans.PoR.InaccPsi.R2.Hk
open Googology.Trans.PoR.InaccPsi.R2.Hi Googology.Trans.PoR.InaccPsi.R2.Hg
open Googology.Trans.PoR.InaccPsi.R2.Hf Googology.Trans.PoR.InaccPsi.R2.Hd Googology.Trans.PoR.InaccPsi.R2.He
open Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Hb
open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Lp Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Gd

/-- **The base `G` depends only on the level datum** (transport along an equality of data). -/
theorem hnGW_shape_congr {Λ Λ' : HnLv} (e : Λ = Λ') (hN : HnNB Λ) (hN' : HnNB Λ') {κ : Ordinal.{0}} {S : HgVD}
    (h : HnWShape (hnGW Λ hN) κ S) : HnWShape (hnGW Λ' hN') κ S := by
  subst e; exact h

/-! ## The band levels below `G` and `Γ_{x+1}` -/

theorem hnkG_fixG {M : Ordinal.{0}} (hM : M < Om1) : veblen (Om1 * Om1 + Om1 * M) (gcG 0) = gcG 0 :=
  gn_veb_fix (gcG_SC 0) (hn_OOM_lt hM 0)

theorem hnkG_B_eq {M : Ordinal.{0}} (hM : M < Om1) :
    veblen (Om1 * Om1 + Om1 * M) (gcG 0 + 1) = hdNx (Om1 * Om1 + Om1 * M) (gcG 0) :=
  (hdNx_fixP (hnkG_fixG hM)).symm

theorem hnkG_one (M : Ordinal.{0}) : (1 : Ordinal.{0}) < Om1 * Om1 + Om1 * M :=
  hl_one_lt_OO.trans_le le_self_add

theorem hnkG_ne (M : Ordinal.{0}) : (Om1 : Ordinal.{0}) * Om1 + Om1 * M ≠ 0 :=
  (zero_lt_one.trans (hnkG_one M)).ne'

section Base

variable {M x : Ordinal.{0}} (hMx : M < x) (hx : InE x) (hx1 : x < Om1)
include hMx hx hx1

theorem hnkG_x1 : (1 : Ordinal.{0}) ≤ x * x + x * M :=
  ((one_lt_omega0.trans (omega0_lt_inE hx)).le.trans (hl_lt_sq hx).le).trans le_self_add

theorem hnkG_xlt : x * x + x * M < lgG x :=
  (inE_indec (lgG_facts hx hx1).2.2.2.1).add_lt (hl_sq_lt hx hx1)
    (InE.mul_lt (lgG_facts hx hx1).2.2.2.1 (lgG_facts hx hx1).2.1 (hMx.trans (lgG_facts hx hx1).2.1))

theorem hnkG_fixx : veblen (x * x + x * M) (lgG x) = lgG x :=
  hjG_fix hx hx1 (hnkG_x1 hMx hx hx1) (hnkG_xlt hMx hx hx1)

theorem hnkG_b_eq : veblen (x * x + x * M) (lgG x + 1) = hdNx (x * x + x * M) (lgG x) :=
  (hdNx_fixP (hnkG_fixx hMx hx hx1)).symm

end Base

/-! ## The limit case -/

/-- **The condition at a limit**: the earlier systems are starts over `G` at their packages with base gate the gate
of the package, and later ones extend earlier ones. -/
def HnkGCoh (l : Ordinal.{0}) (IH : ∀ μ, μ < l → HgVD) : Prop :=
  (∀ μ (h : μ < l) (hμ : μ < Om1), HnWShape (hnGW (hnkPk μ).Λ (hnkNB hμ)) 0 (IH μ h) ∧ (IH μ h).γ = (hnkPk μ).Λ.g) ∧
    ∀ μ' μ (h' : μ' < l) (h : μ < l), μ' < μ → ∀ c x, c < (IH μ' h').B →
      (IH μ h).R c x = (IH μ' h').R c x ∧ (IH μ h).g c = (IH μ' h').g c

section Lim

variable (l : Ordinal.{0}) (hl : IsSuccLimit l) (hle : l < Om1) (IH : ∀ μ, μ < l → HgVD) (H : HnkGCoh l IH)

include hl hle in
theorem hnkGCoh_g (k : ℕ) : (hnkPk (heFs l k)).Λ.g ≤ hlGt l :=
  (hnkPk_g ((heFs_lt hl (hl_om hle) k).trans hle)).trans (hlGt_mono (heFs_lt hl (hl_om hle) k).le)

include H in
theorem hnkGCoh_B (k : ℕ) :
    (IH (heFs l k) (heFs_lt hl (hl_om hle) k)).B = veblen (Om1 * Om1 + Om1 * heFs l k) (gcG 0 + 1) := by
  have h := (H.1 _ (heFs_lt hl (hl_om hle) k) ((heFs_lt hl (hl_om hle) k).trans hle)).1.1
  rw [h]
  show veblen ((hnkPk (heFs l k)).Λ.L + 0) (gcG 0 + 1) = _
  rw [hnkPk_L ((heFs_lt hl (hl_om hle) k).trans hle), add_zero]

include H in
theorem hnkGCoh_b (k : ℕ) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγ : hlGt l < x) :
    (IH (heFs l k) (heFs_lt hl (hl_om hle) k)).b x = veblen (x * x + x * heFs l k) (lgG x + 1) := by
  have hg' := (hnkGCoh_g l hl hle k).trans_lt hγ
  have h := (H.1 _ (heFs_lt hl (hl_om hle) k) ((heFs_lt hl (hl_om hle) k).trans hle)).1.2.2.1 x hx hx1
    (max_lt hg' hx.pos)
  rw [h]
  show veblen ((hnkPk (heFs l k)).Λ.l x + 0) (lgG x + 1) = _
  rw [hnkPk_l ((heFs_lt hl (hl_om hle) k).trans hle) hg', add_zero]

/-- **THE GATED `ω`-CHAIN OF THE SYSTEMS `hnkGS (heFs λ k)` OVER `G`**: union bound `φ(Ω₁·Ω₁ + Ω₁·λ, G+1)`, union
base reading `φ(x·x + x·λ, Γ_{x+1}+1)`, union base gate `hlGt λ`. -/
noncomputable def hnkGCh : HgfCh where
  D := fun k => IH (heFs l k) (heFs_lt hl (hl_om hle) k)
  B := veblen (Om1 * Om1 + Om1 * l) (gcG 0 + 1)
  b := fun x => veblen (x * x + x * l) (lgG x + 1)
  γ := hlGt l
  Zo := (hnGW (hnMLv l hle) (hnMLv_NB l hle)).hnwZo
  γ_lt := (hlGt_le _).trans_lt hle
  γ0 := fun k => by
    rw [(H.1 _ _ ((heFs_lt hl (hl_om hle) k).trans hle)).2]; exact hnkGCoh_g l hl hle k
  γ_cl := fun Z hZ hZ1 h => by
    have hG : gcG 0 < veblen (Om1 * Om1 + Om1 * l) (gcG 0 + 1) := (lt_add_one _).trans_le (right_le_veblen _ _)
    have hc := hi_cl_lvl (hnkG_one l).le hZ1 (hd_succ_lt (hnkG_ne l) _) hG h le_rfl
      ((isNormal_veblen _).strictMono (lt_add_one _))
    have h2 := (hnMLv l hle).L_add_lt (ν := 0) (by rw [← Br.Om1_eq]; exact gv_Om1_pos)
    rw [add_zero] at h2
    exact (hnMLv l hle).g_cl Z _ hZ hZ1 hc le_rfl h2
  B_mono := fun k => by
    rw [hnkGCoh_B l hl hle IH H, hnkGCoh_B l hl hle IH H]
    exact (hd_veb_left_lt ((add_lt_add_iff_left _).2
      (mul_lt_mul_of_pos_left (heFs_mono hl (hl_om hle) k) gv_Om1_pos)) _).le
  B_lt := fun k => by
    rw [hnkGCoh_B l hl hle IH H]
    exact hd_veb_left_lt ((add_lt_add_iff_left _).2
      (mul_lt_mul_of_pos_left (heFs_lt hl (hl_om hle) k) gv_Om1_pos)) _
  B_cof := fun c hc => by
    obtain ⟨b, hb, hcb⟩ := hgVeb_cof (hnkG_ne l) (hnkG_fixG hle) hc
    obtain ⟨k, hk⟩ := hn_cof1 (fun _ h => hn_sq_succ gl_Om1_E h) gv_Om1_pos (heFs_mono hl (hl_om hle))
      (heFs_cof hl (hl_om hle)) hb
    refine ⟨k, ?_⟩
    rw [hnkGCoh_B l hl hle IH H, hnkG_B_eq ((heFs_lt hl (hl_om hle) k).trans hle)]
    exact hcb.trans (hdN_lt_Nx hk)
  R_ext := fun k c x hc => (H.2 _ _ _ _ (heFs_mono hl (hl_om hle) k) c x hc).1
  g_ext := fun k c hc => (H.2 _ _ _ _ (heFs_mono hl (hl_om hle) k) c 0 hc).2
  B_lt1 := by
    have hG1 := gcG_SC 1
    have hE := Low.opow_eq_self_of_SC hG1
    have hfix : veblen (Om1 * Om1 + Om1 * l) (gcG 1) = gcG 1 := gn_veb_fix hG1 (hn_OOM_lt hle 1)
    have h2 := (isNormal_veblen (Om1 * Om1 + Om1 * l)).strictMono
      ((ev_isSuccLimit_of_inE hE).add_one_lt (gcG_lt zero_lt_one))
    rwa [hfix] at h2
  B_fix := veblen_veblen_of_lt (hnkG_one l) _
  B_mem := fun S a b ha hb =>
    CSet.phi_mem ((hnMLv l hle).L_mem S a b ha hb) (CSet.succ_mem (gmS_G0_mem S ha))
  b_ge := fun k x hx hx1 hγ => by
    rw [hnkGCoh_b l hl hle IH H k hx hx1 hγ]
    exact (hd_veb_left_lt ((add_lt_add_iff_left _).2
      (mul_lt_mul_of_pos_left (heFs_lt hl (hl_om hle) k) hx.pos)) _).le
  b_cof := fun x hx hx1 hγ ν hν => by
    have hlx : l < x := hl_gt_E hx hγ
    obtain ⟨b, hb, hνb⟩ := hgVeb_cof (zero_lt_one.trans_le (hnkG_x1 hlx hx hx1)).ne' (hnkG_fixx hlx hx hx1) hν
    obtain ⟨k, hk⟩ := hn_cof1 (fun _ h => hn_sq_succ hx h) hx.pos (heFs_mono hl (hl_om hle))
      (heFs_cof hl (hl_om hle)) hb
    refine ⟨k, ?_⟩
    rw [hnkGCoh_b l hl hle IH H k hx hx1 hγ, hnkG_b_eq ((heFs_lt hl (hl_om hle) k).trans hlx) hx hx1]
    exact hνb.trans (hdN_lt_Nx hk)
  b_fix := fun x hx hx1 _ => veblen_veblen_of_lt ((one_lt_omega0.trans (omega0_lt_inE hx)).trans_le
    ((hl_lt_sq hx).le.trans le_self_add)) _
  b_gt := fun x hx hx1 _ => (lgG_facts hx hx1).2.1.trans ((lt_add_one _).trans_le (right_le_veblen _ _))
  b_lt := fun x hx hx1 hγ => by
    rw [hnkG_b_eq (hl_gt_E hx hγ) hx hx1]
    exact hjG_lt1 hx hx1 (hnkG_x1 (hl_gt_E hx hγ) hx hx1) (hnkG_xlt (hl_gt_E hx hγ) hx hx1)
  b_pi := fun σ ρ hB hγ => by
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
    have hlσ : l < σ := hl_gt_E hB.1 hγ
    have hlρ : l < ρ := hlσ.trans hB.2.2.1
    have hp := (hnMLv l hle).l_pi σ ρ hB hγ
    rw [show (hnMLv l hle).l ρ = ρ * ρ + ρ * l from hnMLv_l _ _ (hγ.trans hB.2.2.1),
      show (hnMLv l hle).l σ = σ * σ + σ * l from hnMLv_l _ _ hγ] at hp
    rw [hnkG_b_eq hlρ hB.2.1 hρ1, hnkG_b_eq hlσ hB.1 hσ1]
    exact hjG_S_pi hB hp (hnkG_x1 hlρ hB.2.1 hρ1) (hnkG_xlt hlρ hB.2.1 hρ1) (hnkG_x1 hlσ hB.1 hσ1)
      (hnkG_xlt hlσ hB.1 hσ1)
  Z_low := fun k x hx hx1 h => by
    have hkl := heFs_lt hl (hl_om hle) k
    have hk1 : heFs l k < Om1 := hkl.trans hle
    show (IH (heFs l k) hkl).Z x ≤ (hnGW (hnMLv l hle) (hnMLv_NB l hle)).hnwZo x
    rw [(H.1 _ _ hk1).1.2.2.2.1 x hx hx1, (hnGW (hnMLv l hle) (hnMLv_NB l hle)).hnwZo_low h]
    split_ifs with h'
    · have hP : veblen 2 (veblen (max ω x * max ω x * 2) (lgG x + 1)) =
          veblen (max ω x * max ω x * 2) (lgG x + 1) := (hnGW (hnkPk (heFs l k)).Λ (hnkNB hk1)).Zo_fix x
      refine (hb_evZ_lt_fix2 hP ?_).le
      show veblen ((hnkPk (heFs l k)).Λ.l x + 0) (lgG x + 1) < _
      rw [add_zero, max_eq_right (omega0_lt_inE hx).le]
      exact hd_veb_left_lt (le_self_add.trans_lt (hnkNB hk1 x hx hx1 (max_lt_iff.1 h').1)) _
    · rw [(hnGW (hnkPk (heFs l k)).Λ (hnkNB hk1)).hnwZo_low (fun h'' => h' (max_lt h'' hx.pos))]
      rfl
  Zo_fix := fun x => hc_fix_down one_le_two ((hnGW (hnMLv l hle) (hnMLv_NB l hle)).hnwZo_fix x)
  Zo_G1 := fun x hx hx1 => (hnGW (hnMLv l hle) (hnMLv_NB l hle)).hnwZo_G1 x hx hx1

/-- **The union of the chain is a start over `G` at the package `hnkPk λ`.** -/
theorem hnkGCh_shape : HnWShape (hnGW (hnkPk l).Λ (hnkNB hle)) 0 (hnkGCh l hl hle IH H).U := by
  refine hnGW_shape_congr (hnkPk_lim_Λ hl hle).symm (hnMLv_NB l hle) _ ?_
  refine ⟨by rw [add_zero]; rfl,
    fun x _ _ => ?_, fun x _ _ hg => ?_, fun x hx _ => ?_, fun _ σ _ _ hσ _ _ => hσ.pos⟩
  · show hlGt l < x ↔ max (hlGt l) 0 < x
    rw [max_eq_left zero_le]
  · show veblen (x * x + x * l) (lgG x + 1) = veblen ((hnMLv l hle).l x + 0) (lgG x + 1)
    rw [hnMLv_l _ _ (max_lt_iff.1 hg).1, add_zero]
  · show (if hlGt l < x then evZ (veblen (x * x + x * l) (lgG x + 1))
        else (hnGW (hnMLv l hle) (hnMLv_NB l hle)).hnwZo x) =
      if max (hlGt l) 0 < x then evZ (veblen ((hnMLv l hle).l x + 0) (lgG x + 1))
        else (hnGW (hnMLv l hle) (hnMLv_NB l hle)).hnwZo x
    rw [max_eq_left zero_le, add_zero]
    split_ifs with h
    · rw [hnMLv_l _ _ h]
    · rfl

end Lim

open Classical in
/-- **The limit case**: the union of the chain (when `λ < Ω₁` and the condition holds). -/
noncomputable def hnkGLimF (l : Ordinal.{0}) (hl : IsSuccLimit l) (IH : ∀ μ, μ < l → HgVD) : HgVD :=
  if h : l < Om1 ∧ HnkGCoh l IH then (hnkGCh l hl h.1 IH h.2).U else hlU

open Classical in
/-- **The successor case**: the union of all levels `Ω₁·Ω₁ + Ω₁·μ + κ` over `G`, started at the given system. -/
noncomputable def hnkGSucc (μ : Ordinal.{0}) (S : HgVD) : HgVD :=
  if hμ : μ < Om1 then
    (if h : HnWShape (hnGW (hnkPk μ).Λ (hnkNB hμ)) 0 S then
      hnwU (hnGW (hnkPk μ).Λ (hnkNB hμ)) (hnkPk μ).St0 (hnkPk μ).h0 S h else S)
  else S

/-- **THE SYSTEMS OVER `G` AT `φ(Ω₁·Ω₁ + Ω₁·μ, G+1)`, BY ONE RECURSION ON `μ`.** -/
noncomputable def hnkGS (μ : Ordinal.{0}) : HgVD :=
  Ordinal.limitRecOn (motive := fun _ => HgVD) μ hlU hnkGSucc hnkGLimF

theorem hnkGS_zero : hnkGS 0 = hlU := by unfold hnkGS; rw [Ordinal.limitRecOn_zero]

theorem hnkGS_succ (μ : Ordinal.{0}) : hnkGS (μ + 1) = hnkGSucc μ (hnkGS μ) := by
  unfold hnkGS; rw [Ordinal.limitRecOn_add_one]

theorem hnkGS_limit {l : Ordinal.{0}} (hl : IsSuccLimit l) : hnkGS l = hnkGLimF l hl (fun μ _ => hnkGS μ) := by
  unfold hnkGS; rw [Ordinal.limitRecOn_limit _ _ _ _ hl]

theorem hnkGS_Bsh {μ : Ordinal.{0}} (hμ : μ < Om1) {S0 : HgVD} (h : HnWShape (hnGW (hnkPk μ).Λ (hnkNB hμ)) 0 S0) :
    S0.B = veblen (Om1 * Om1 + Om1 * μ) (gcG 0 + 1) := by
  rw [h.1]; show veblen ((hnkPk μ).Λ.L + 0) (gcG 0 + 1) = _; rw [hnkPk_L hμ, add_zero]

theorem hnk_veb_lt {μ' μ : Ordinal.{0}} (h : μ' < μ) :
    veblen (Om1 * Om1 + Om1 * μ') (gcG 0 + 1) < veblen (Om1 * Om1 + Om1 * μ) (gcG 0 + 1) :=
  hd_veb_left_lt ((add_lt_add_iff_left _).2 (mul_lt_mul_of_pos_left h gv_Om1_pos)) _

/-- **THE INVARIANT**: every `hnkGS μ`, `μ < Ω₁`, is a start over `G` at `hnkPk μ` with base gate the gate of
`hnkPk μ`, and extends every `hnkGS μ'`, `μ' < μ`. -/
theorem hnkGS_inv : ∀ μ (hμ : μ < Om1), (HnWShape (hnGW (hnkPk μ).Λ (hnkNB hμ)) 0 (hnkGS μ) ∧
    (hnkGS μ).γ = (hnkPk μ).Λ.g) ∧
    ∀ μ', μ' < μ → ∀ c x, c < (hnkGS μ').B → (hnkGS μ).R c x = (hnkGS μ').R c x ∧
      (hnkGS μ).g c = (hnkGS μ').g c := by
  intro μ
  induction μ using WellFoundedLT.induction with
  | ind μ IH =>
  intro hμ
  rcases zero_or_succ_or_isSuccLimit μ with h0 | ⟨ν, hν⟩ | hlim
  · subst h0
    rw [hnkGS_zero]
    refine ⟨⟨hnGW_shape_congr (by rw [hnkPk_zero]; rfl) hnSqNB _ hnU_shape, by rw [hnkPk_zero]; rfl⟩,
      fun μ' h => absurd h (not_lt.2 zero_le)⟩
  · have hν' : μ = ν + 1 := by rw [← hν, succ_eq_add_one]
    subst hν'
    have hνε : ν < Om1 := (lt_add_one ν).trans hμ
    obtain ⟨⟨hsh, hγ⟩, hext⟩ := IH ν (lt_add_one ν) hνε
    have e : hnkGS (ν + 1) =
        hnwU (hnGW (hnkPk ν).Λ (hnkNB hνε)) (hnkPk ν).St0 (hnkPk ν).h0 (hnkGS ν) hsh := by
      rw [hnkGS_succ]; unfold hnkGSucc; rw [dif_pos hνε, dif_pos hsh]
    refine ⟨⟨?_, by rw [e, hnkPk_succ]; rfl⟩, fun μ' hμ' c x hc => ?_⟩
    · rw [e]
      exact hnGW_shape_congr (by rw [hnkPk_succ]; rfl) (hnkNB' hνε) _
        (hnGU_shape (hnkPk ν).Λ (hnkNB hνε) (hnkNB' hνε) (hnkPk ν).St0 (hnkPk ν).h0 _ hsh)
    · rw [e]
      rcases (Order.lt_add_one_iff.1 hμ').lt_or_eq with hlt | heq
      · obtain ⟨⟨hsh', -⟩, -⟩ := IH μ' (hlt.trans (lt_add_one ν)) (hlt.trans hνε)
        have hc0 : c < (hnkGS ν).B := by
          rw [hnkGS_Bsh hνε hsh]; rw [hnkGS_Bsh (hlt.trans hνε) hsh'] at hc
          exact hc.trans (hnk_veb_lt hlt)
        obtain ⟨r1, g1⟩ := hext μ' hlt c x hc
        exact ⟨(hnwU_R0 (hnGW (hnkPk ν).Λ (hnkNB hνε)) (hnkPk ν).St0 (hnkPk ν).h0 _ hsh hc0 x).trans r1,
          (hnwU_g0 (hnGW (hnkPk ν).Λ (hnkNB hνε)) (hnkPk ν).St0 (hnkPk ν).h0 _ hsh hc0).trans g1⟩
      · subst heq
        exact ⟨hnwU_R0 (hnGW (hnkPk μ').Λ (hnkNB hνε)) (hnkPk μ').St0 (hnkPk μ').h0 _ hsh hc x,
          hnwU_g0 (hnGW (hnkPk μ').Λ (hnkNB hνε)) (hnkPk μ').St0 (hnkPk μ').h0 _ hsh hc⟩
  · have hcoh : HnkGCoh μ (fun μ' _ => hnkGS μ') :=
      ⟨fun μ' h hμ' => (IH μ' h hμ').1, fun μ₁ μ₂ h₁ h₂ h12 => (IH μ₂ h₂ (h₂.trans hμ)).2 μ₁ h12⟩
    have e : hnkGS μ = (hnkGCh μ hlim hμ (fun μ' _ => hnkGS μ') hcoh).U := by
      rw [hnkGS_limit hlim]; unfold hnkGLimF; rw [dif_pos ⟨hμ, hcoh⟩]
    refine ⟨⟨by rw [e]; exact hnkGCh_shape μ hlim hμ _ hcoh, by rw [e, hnkPk_lim_Λ hlim hμ]; rfl⟩,
      fun μ' hμ' c x hc => ?_⟩
    rw [e]
    obtain ⟨k, hk⟩ := heFs_cof hlim (hl_om hμ) μ' hμ'
    have hkl := heFs_lt hlim (hl_om hμ) k
    obtain ⟨⟨hsh', -⟩, -⟩ := IH μ' hμ' (hμ'.trans hμ)
    obtain ⟨-, hextk⟩ := IH _ hkl (hkl.trans hμ)
    have hc' : c < (hnkGS (heFs μ k)).B := by
      rw [hnkGCoh_B μ hlim hμ _ hcoh k]; rw [hnkGS_Bsh (hμ'.trans hμ) hsh'] at hc
      exact hc.trans (hnk_veb_lt hk)
    obtain ⟨r2, g2⟩ := hextk μ' hk c x hc
    exact ⟨((hnkGCh μ hlim hμ (fun μ' _ => hnkGS μ') hcoh).U_R (k := k) hc' x).trans r2,
      ((hnkGCh μ hlim hμ (fun μ' _ => hnkGS μ') hcoh).U_g (k := k) hc').trans g2⟩

theorem hnkGS_shape {μ : Ordinal.{0}} (hμ : μ < Om1) : HnWShape (hnGW (hnkPk μ).Λ (hnkNB hμ)) 0 (hnkGS μ) :=
  (hnkGS_inv μ hμ).1.1

theorem hnkGS_γ {μ : Ordinal.{0}} (hμ : μ < Om1) : (hnkGS μ).γ = (hnkPk μ).Λ.g := (hnkGS_inv μ hμ).1.2

/-- **The base gate of `hnkGS μ` is at most `μ`.** -/
theorem hnkGS_γ_le {μ : Ordinal.{0}} (hμ : μ < Om1) : (hnkGS μ).γ ≤ μ := by
  rw [hnkGS_γ hμ]; exact (hnkPk_g hμ).trans (hlGt_le _)

/-- **The bound of `hnkGS μ` is `φ(Ω₁·Ω₁ + Ω₁·μ, G+1)`.** -/
theorem hnkGS_B {μ : Ordinal.{0}} (hμ : μ < Om1) : (hnkGS μ).B = veblen (Om1 * Om1 + Om1 * μ) (gcG 0 + 1) :=
  hnkGS_Bsh hμ (hnkGS_shape hμ)

theorem hnkGS_ext {μ' μ : Ordinal.{0}} (hμ : μ < Om1) (h : μ' < μ) {c : Ordinal.{0}} (hc : c < (hnkGS μ').B)
    (x : Ordinal.{0}) : (hnkGS μ).R c x = (hnkGS μ').R c x ∧ (hnkGS μ).g c = (hnkGS μ').g c :=
  (hnkGS_inv μ hμ).2 μ' h c x hc

end Googology.Trans.PoR.InaccPsi.R2.Hn
