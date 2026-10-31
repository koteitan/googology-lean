import Googology.Trans.PoR.InaccPsi.R2.HnQW

/-!
# HnQG: OVER A PSEUDO-BASE `Q` OF LEVEL `Ω₁·Ω₁`, ONE RECURSION OF SYSTEMS AT `φ(Ω₁·(1+μ), F+1)`, `μ < Ω₁`

PORT of `Hl.HlG` (the systems `Hl.hlkGS μ` over `G`) to an arbitrary pseudo-base `Q : HnVQ hnSqLv 0` with a start
`U`: what differs is the base (`hnQW Q Λ` in place of `Hl.hlGW Λ`: the point `Q.F`, the reading `Q.Fr`, the outer low
field `Q.Zo`, the code gate `Q.γ`, the reading gate `max Q.γ g`), the start of the recursion (the step of the level
`Ω₁ + 0` at `Q`, `Hl.hlPk1.St0 (hnQ1 Q) U`, in place of `Hg.hgU`), and the high condition (codes past `Q.F` with a
gate below `σ` force `Q.γ < σ`; over `G` it is empty).  The packages `Hl.hlkPk μ` are imported.

* `hnq_N0_pi` (Lemma EXACT for `hdNx (ℓ(ρ)+0) (Q.Fr ρ)`), `hnQU_shape` (**the union over `hnQW Q Λ` started at a start
  over it is a start over `hnQW Q Λ.succ`**);
* `HnQCoh`, `hnQCh` (the gated `ω`-chain at a limit), `hnQCh_shape`;
* `hnQGS Q U hU μ` (**THE SYSTEMS OVER `Q` AT `φ(Ω₁·(1+μ), F+1)`**, `limitRecOn`), `hnQGS_inv`, `hnQGS_shape`,
  `hnQGS_γ` (base gate `max Q.γ (hlkPk μ).g`), `hnQGS_B`, `hnQGS_ext`, `hnQGS_spec0` (the member `0` has the
  specification of level `Ω₁ + 0`).

No new axiom.  New definitions: `HnQCoh`, `hnQCh`, `hnQLimF`, `hnQSucc`, `hnQGS`.
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

section QG

variable (Q : HnVQ hnSqLv 0)

/-- **`hdNx (ℓ(ρ)+0) (Q.Fr ρ) < hdNx (ρ·ρ + 0) ...`**: the levels below `Ω₁·Ω₁` at `Q`. -/
theorem hnq_lle0 (Λ : HlLv) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hg : Λ.g < x) :
    Λ.l x + 0 < hnSqLv.l x + 0 := by
  rw [add_zero]; exact (lt_add_of_pos_right _ hx.pos).trans_le (hnq_lle Λ hx hx1 hg)

theorem hnq_rfix0 (Λ : HlLv) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγ : Q.γ < x) (hg : Λ.g < x) :
    veblen (Λ.l x + 0) (Q.Fr x) = Q.Fr x := by
  obtain ⟨a, ha⟩ := Q.Fr_P hx hx1 hγ; rw [← ha]; exact veblen_veblen_of_lt (hnq_lle0 Λ hx hx1 hg) a

/-- **Lemma EXACT for `hdNx (ℓ(ρ)+0) (Q.Fr ρ)`** above both gates. -/
theorem hnq_N0_pi (Λ : HlLv) {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) (hγ : Q.γ < σ) (hg : Λ.g < σ) :
    hdNx (Λ.l ρ + 0) (Q.Fr ρ) ∈ TB ρ σ ∧ pi σ ρ (hdNx (Λ.l ρ + 0) (Q.Fr ρ)) = hdNx (Λ.l σ + 0) (Q.Fr σ) := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  have hγρ : Q.γ < ρ := hγ.trans hB.2.2.1
  have hgρ : Λ.g < ρ := hg.trans hB.2.2.1
  obtain ⟨f1, f2⟩ := Q.Fr_pi hB hγ
  have h := hlv_glA_pi Λ hB hg hB.1.pos f1 (Q.Fr_lt1 hB.2.1 hρ1 hγρ)
  rw [f2, hlv_glA_fixP Λ hB.2.1 hρ1 (hB.1.pos.trans hB.2.2.1) (hnq_rfix0 Q Λ hB.2.1 hρ1 hγρ hgρ)
    ((hnq_lle0 Λ hB.2.1 hρ1 hgρ).trans (Q.Fr_gt hB.2.1 hρ1 hγρ)) (Q.Fr_lt1 hB.2.1 hρ1 hγρ),
    hlv_glA_fixP Λ hB.1 hσ1 hB.1.pos (hnq_rfix0 Q Λ hB.1 hσ1 hγ hg)
    ((hnq_lle0 Λ hB.1 hσ1 hg).trans (Q.Fr_gt hB.1 hσ1 hγ)) (Q.Fr_lt1 hB.1 hσ1 hγ)] at h
  exact h

theorem hnq_fix0 (Λ : HlLv) : veblen (Λ.L + 0) Q.F = Q.F := by
  obtain ⟨a, ha⟩ := Q.F_P; rw [← ha]
  refine veblen_veblen_of_lt ?_ a
  rw [add_zero]; exact (lt_add_of_pos_right _ gv_Om1_pos).trans (hnq_lt0 Λ)

theorem hnq_B0_lt (Λ : HlLv) : hdNx (Λ.L + 0) Q.F < hdNx (hnSqLv.L + 0) Q.F :=
  (hdNx_mono (by rw [add_zero]; exact le_self_add) _).trans_lt (hnq_S_lt Q Λ)

/-- **The union over `hnQW Q Λ` started at a start over it is a start over `hnQW Q Λ.succ`.** -/
theorem hnQU_shape (Λ : HlLv) (St0 : HlVStTy Λ 0) (h0 : ∀ Q U h, HlVSpec Q U (St0 Q U h)) (S0 : HgVD)
    (hS0 : HlWShape (hnQW Q Λ) 0 S0) : HlWShape (hnQW Q Λ.succ) 0 (hlwU (hnQW Q Λ) St0 h0 S0 hS0) := by
  have hmx : ∀ x : Ordinal.{0}, max (max Q.γ Λ.succ.g) 0 < x ↔ max Q.γ Λ.g < x := fun x => by
    rw [max_eq_left zero_le]; rfl
  refine ⟨?_, fun x _ _ => ?_, fun x hx hx1 hk => ?_, fun x hx hx1 => ?_, fun c σ hFc hc hσ hσ1 hg => ?_⟩
  · show hdNx (Λ.L + Om1) Q.F = veblen (Λ.succ.L + 0) (Q.F + 1)
    rw [add_zero, hdNx_fixP (hnq_Ffix Q Λ)]; rfl
  · show max Q.γ Λ.g < x ↔ max (max Q.γ Λ.succ.g) 0 < x
    rw [hmx]
  · have hk' : max Q.γ Λ.g < x := (hmx x).1 hk
    show hdNx (Λ.l x + x) (Q.Fr x) = veblen (Λ.succ.l x + 0) (Q.Fr x + 1)
    rw [add_zero, hdNx_fixP (hnq_rfix Q Λ hx hx1 (max_lt_iff.1 hk').1 (max_lt_iff.1 hk').2)]; rfl
  · show hlwUZ (hnQW Q Λ) x = if max (max Q.γ Λ.succ.g) 0 < x then evZ (veblen (Λ.succ.l x + 0) (Q.Fr x + 1))
      else (hnQW Q Λ.succ).hlwZo x
    unfold hlwUZ
    by_cases hg : max Q.γ Λ.g < x
    · rw [if_pos (show (hnQW Q Λ).γR < x from hg), if_pos ((hmx x).2 hg), add_zero]
      show evZ (hdNx (Λ.l x + x) (Q.Fr x)) = evZ (veblen (Λ.l x + x) (Q.Fr x + 1))
      rw [hdNx_fixP (hnq_rfix Q Λ hx hx1 (max_lt_iff.1 hg).1 (max_lt_iff.1 hg).2)]
    · rw [if_neg (show ¬ (hnQW Q Λ).γR < x from hg), if_neg (fun h' => hg ((hmx x).1 h')),
        (hnQW Q Λ.succ).hlwZo_low (show ¬ (hnQW Q Λ.succ).γR < x from hg)]
      rfl
  · by_cases hSc : S0.B ≤ c
    · exact (le_max_left _ _).trans_lt (hlwU_highR (hnQW Q Λ) St0 h0 S0 hS0 hSc hc hσ hσ1 hg)
    · have hc0 : c < S0.B := not_le.1 hSc
      rw [hlwU_g0 (hnQW Q Λ) St0 h0 S0 hS0 hc0] at hg
      exact hS0.2.2.2.2 c σ hFc hc0 hσ hσ1 hg

end QG

/-! ## The limit case -/

/-- **The condition at a limit**: the earlier systems are starts over `hnQW Q (hlkPk μ).Λ` with base gate
`max Q.γ (hlkPk μ).g`, and later ones extend earlier ones. -/
def HnQCoh (Q : HnVQ hnSqLv 0) (l : Ordinal.{0}) (IH : ∀ μ, μ < l → HgVD) : Prop :=
  (∀ μ (h : μ < l), HlWShape (hnQW Q (hlkPk μ).Λ) 0 (IH μ h) ∧ (IH μ h).γ = max Q.γ (hlkPk μ).Λ.g) ∧
    ∀ μ' μ (h' : μ' < l) (h : μ < l), μ' < μ → ∀ c x, c < (IH μ' h').B →
      (IH μ h).R c x = (IH μ' h').R c x ∧ (IH μ h).g c = (IH μ' h').g c

section Lim

variable (Q : HnVQ hnSqLv 0) (l : Ordinal.{0}) (hl : IsSuccLimit l) (hle : l < Om1) (IH : ∀ μ, μ < l → HgVD)
  (H : HnQCoh Q l IH)

theorem hnq_FM {M : Ordinal.{0}} (hM : M < Om1) : veblen (Om1 * M) Q.F = Q.F := by
  obtain ⟨a, ha⟩ := Q.F_P; rw [← ha]
  refine veblen_veblen_of_lt ?_ a
  rw [add_zero]; exact mul_lt_mul_of_pos_left hM gv_Om1_pos

theorem hnq_B_eq {M : Ordinal.{0}} (hM : M < Om1) : veblen (Om1 * M) (Q.F + 1) = hdNx (Om1 * M) Q.F :=
  (hdNx_fixP (hnq_FM Q hM)).symm

theorem hnq_FrM {M x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγ : Q.γ < x) (hMx : M < x) :
    veblen (x * M) (Q.Fr x) = Q.Fr x := by
  obtain ⟨a, ha⟩ := Q.Fr_P hx hx1 hγ; rw [← ha]
  refine veblen_veblen_of_lt ?_ a
  rw [add_zero]; exact mul_lt_mul_of_pos_left hMx hx.pos

theorem hnq_b_eq {M x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγ : Q.γ < x) (hMx : M < x) :
    veblen (x * M) (Q.Fr x + 1) = hdNx (x * M) (Q.Fr x) :=
  (hdNx_fixP (hnq_FrM Q hx hx1 hγ hMx)).symm

include hl hle in
theorem hnQCoh_g (k : ℕ) : (hlkPk (heFs l k)).Λ.g ≤ hlGt (1 + l) :=
  (hlkPk_g ((heFs_lt hl (hl_om hle) k).trans hle)).trans (hlGt_mono (hlk_fs_lt hl hle k).le)

include H in
theorem hnQCoh_B (k : ℕ) :
    (IH (heFs l k) (heFs_lt hl (hl_om hle) k)).B = veblen (Om1 * (1 + heFs l k)) (Q.F + 1) := by
  have h := (H.1 _ (heFs_lt hl (hl_om hle) k)).1.1
  rw [h]
  show veblen ((hlkPk (heFs l k)).Λ.L + 0) (Q.F + 1) = _
  rw [hlkPk_L ((heFs_lt hl (hl_om hle) k).trans hle), add_zero]

include H in
theorem hnQCoh_b (k : ℕ) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγ : max Q.γ (hlGt (1 + l)) < x) :
    (IH (heFs l k) (heFs_lt hl (hl_om hle) k)).b x = veblen (x * (1 + heFs l k)) (Q.Fr x + 1) := by
  have hg' := (hnQCoh_g l hl hle k).trans_lt (max_lt_iff.1 hγ).2
  have h := (H.1 _ (heFs_lt hl (hl_om hle) k)).1.2.2.1 x hx hx1 (max_lt (max_lt (max_lt_iff.1 hγ).1 hg') hx.pos)
  rw [h]
  show veblen ((hlkPk (heFs l k)).Λ.l x + 0) (Q.Fr x + 1) = _
  rw [hlkPk_l ((heFs_lt hl (hl_om hle) k).trans hle) hg', add_zero]

/-- **THE GATED `ω`-CHAIN OF THE SYSTEMS `IH (heFs λ k)` OVER `Q`**: union bound `φ(Ω₁·(1+λ), F+1)`, union base reading
`φ(x·(1+λ), F(x)+1)`, union base gate `max Q.γ (hlGt (1+λ))`. -/
noncomputable def hnQCh : HgfCh where
  D := fun k => IH (heFs l k) (heFs_lt hl (hl_om hle) k)
  B := veblen (Om1 * (1 + l)) (Q.F + 1)
  b := fun x => veblen (x * (1 + l)) (Q.Fr x + 1)
  γ := max Q.γ (hlGt (1 + l))
  Zo := (hnQW Q (hlMLv (1 + l) le_self_add (hl_one_add hle))).hlwZo
  γ_lt := max_lt Q.γ_lt ((hlGt_le _).trans_lt (hl_one_add hle))
  γ0 := fun k => by rw [(H.1 _ _).2]; exact max_le_max le_rfl (hnQCoh_g l hl hle k)
  γ_cl := fun Z hZ hZ1 h => by
    have ha : (1 : Ordinal.{0}) ≤ Om1 * (1 + l) := (hkG_one le_self_add).le
    have hG : gcG 0 < veblen (Om1 * (1 + l)) (Q.F + 1) :=
      Q.G_lt.trans ((lt_add_one _).trans_le (right_le_veblen _ _))
    have hc := hi_cl_lvl ha hZ1 (hd_succ_lt (hkG_ne le_self_add) _) hG h le_rfl
      ((isNormal_veblen _).strictMono (lt_add_one _))
    have h2 : (Om1 : Ordinal.{0}) * (1 + l) < Om 1 * Om 1 := by
      rw [Br.Om1_eq]; exact mul_lt_mul_of_pos_left (hl_om (hl_one_add hle)) gw_Om_pos
    refine max_lt ?_ ((hlGt_le _).trans_lt (hl_mul_cl hZ hZ1 hc le_rfl h2))
    refine Q.F_cl Z hZ hZ1 _ h ((lt_add_one _).le.trans (right_le_veblen _ _)) ?_
    have e := hnq_B_eq Q (hl_one_add hle)
    rw [e]
    have := hnq_B0_lt Q (hlMLv (1 + l) le_self_add (hl_one_add hle))
    rwa [add_zero] at this
  B_mono := fun k => by
    rw [hnQCoh_B Q l hl hle IH H, hnQCoh_B Q l hl hle IH H]
    exact (hd_veb_left_lt (mul_lt_mul_of_pos_left (hlk_fs_mono hl hle k) gv_Om1_pos) _).le
  B_lt := fun k => by
    rw [hnQCoh_B Q l hl hle IH H]
    exact hd_veb_left_lt (mul_lt_mul_of_pos_left (hlk_fs_lt hl hle k) gv_Om1_pos) _
  B_cof := fun c hc => by
    obtain ⟨b, hb, hcb⟩ := hgVeb_cof (hkG_ne le_self_add) (hnq_FM Q (hl_one_add hle)) hc
    obtain ⟨k, hk⟩ := hk_mul_cof1 gv_Om1_pos (hlk_fs_mono hl hle) (hlk_fs_cof hl hle) hb
    refine ⟨k, ?_⟩
    rw [hnQCoh_B Q l hl hle IH H, hnq_B_eq Q (hl_one_add ((heFs_lt hl (hl_om hle) k).trans hle))]
    exact hcb.trans (hdN_lt_Nx hk)
  R_ext := fun k c x hc => (H.2 _ _ _ _ (heFs_mono hl (hl_om hle) k) c x hc).1
  g_ext := fun k c hc => (H.2 _ _ _ _ (heFs_mono hl (hl_om hle) k) c 0 hc).2
  B_lt1 := by
    rw [hnq_B_eq Q (hl_one_add hle)]
    have := hnq_B0_lt Q (hlMLv (1 + l) le_self_add (hl_one_add hle))
    rw [add_zero] at this
    exact this.trans Q.S_lt1
  B_fix := veblen_veblen_of_lt (hkG_one le_self_add) _
  B_mem := fun S a b ha hb =>
    CSet.phi_mem ((hlMLv (1 + l) le_self_add (hl_one_add hle)).L_mem S a b ha (max_lt_iff.1 hb).2)
      (CSet.succ_mem (Q.F_mem S ha (max_lt_iff.1 hb).1))
  b_ge := fun k x hx hx1 hγ => by
    rw [hnQCoh_b Q l hl hle IH H k hx hx1 hγ]
    exact (hd_veb_left_lt (mul_lt_mul_of_pos_left (hlk_fs_lt hl hle k) hx.pos) _).le
  b_cof := fun x hx hx1 hγ ν hν => by
    have hlx : 1 + l < x := hl_gt_E hx (max_lt_iff.1 hγ).2
    obtain ⟨b, hb, hνb⟩ := hgVeb_cof (mul_pos hx.pos (zero_lt_one.trans_le le_self_add)).ne'
      (hnq_FrM Q hx hx1 (max_lt_iff.1 hγ).1 hlx) hν
    obtain ⟨k, hk⟩ := hk_mul_cof1 hx.pos (hlk_fs_mono hl hle) (hlk_fs_cof hl hle) hb
    refine ⟨k, ?_⟩
    rw [hnQCoh_b Q l hl hle IH H k hx hx1 hγ,
      hnq_b_eq Q hx hx1 (max_lt_iff.1 hγ).1 ((hlk_fs_lt hl hle k).trans hlx)]
    exact hνb.trans (hdN_lt_Nx hk)
  b_fix := fun x hx hx1 _ => veblen_veblen_of_lt ((one_lt_omega0.trans (omega0_lt_inE hx)).trans_le
    (le_mul_of_one_le_right' le_self_add)) _
  b_gt := fun x hx hx1 hγ => (Q.Fr_gtx hx hx1 (max_lt_iff.1 hγ).1).trans
    ((lt_add_one _).trans_le (right_le_veblen _ _))
  b_lt := fun x hx hx1 hγ => by
    have hlx : 1 + l < x := hl_gt_E hx (max_lt_iff.1 hγ).2
    rw [hnq_b_eq Q hx hx1 (max_lt_iff.1 hγ).1 hlx]
    refine (hdNx_mono ?_ _).trans_lt (Q.S_lt1x hx hx1 (max_lt_iff.1 hγ).1)
    rw [add_zero]; exact (mul_lt_mul_of_pos_left hlx hx.pos).le
  b_pi := fun σ ρ hB hγ => by
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
    have hlσ : 1 + l < σ := hl_gt_E hB.1 (max_lt_iff.1 hγ).2
    have hlρ : 1 + l < ρ := hlσ.trans hB.2.2.1
    have hp := hnq_N0_pi Q (hlMLv (1 + l) le_self_add (hl_one_add hle)) hB (max_lt_iff.1 hγ).1
      (max_lt_iff.1 hγ).2
    rw [show (hlMLv (1 + l) le_self_add (hl_one_add hle)).l ρ = ρ * (1 + l) from
        hlMLv_l _ _ _ ((max_lt_iff.1 hγ).2.trans hB.2.2.1),
      show (hlMLv (1 + l) le_self_add (hl_one_add hle)).l σ = σ * (1 + l) from hlMLv_l _ _ _ (max_lt_iff.1 hγ).2,
      add_zero, add_zero] at hp
    rw [hnq_b_eq Q hB.2.1 hρ1 ((max_lt_iff.1 hγ).1.trans hB.2.2.1) hlρ,
      hnq_b_eq Q hB.1 hσ1 (max_lt_iff.1 hγ).1 hlσ]
    exact hp
  Z_low := fun k x hx hx1 h => by
    have hkl := heFs_lt hl (hl_om hle) k
    show (IH (heFs l k) hkl).Z x ≤ (hnQW Q (hlMLv (1 + l) le_self_add (hl_one_add hle))).hlwZo x
    rw [(H.1 _ _).1.2.2.2.1 x hx hx1, hnQW_Zo_low Q (hlMLv (1 + l) le_self_add (hl_one_add hle)) h]
    split_ifs with h'
    · have hg' : max Q.γ (hlkPk (heFs l k)).Λ.g < x := (max_lt_iff.1 h').1
      refine (hb_evZ_lt_fix2 (Q.Zo_fix x) ?_).le
      have e := hnq_rfix0 Q (hlkPk (heFs l k)).Λ hx hx1 (max_lt_iff.1 hg').1 (max_lt_iff.1 hg').2
      show veblen ((hlkPk (heFs l k)).Λ.l x + 0) (Q.Fr x + 1) < Q.Zo x
      rw [← hdNx_fixP e]
      refine (hdNx_mono (hnq_lle0 _ hx hx1 (max_lt_iff.1 hg').2).le _).trans_lt (Q.S_Zo hx hx1 (max_lt_iff.1 hg').1)
    · rw [hnQW_Zo_low Q _ (fun h'' => h' (max_lt h'' hx.pos))]
  Zo_fix := fun x => hc_fix_down one_le_two ((hnQW Q (hlMLv (1 + l) le_self_add (hl_one_add hle))).hlwZo_fix x)
  Zo_G1 := fun x hx hx1 => (hnQW Q (hlMLv (1 + l) le_self_add (hl_one_add hle))).hlwZo_G1 x hx hx1

/-- **The union of the chain is a start over `hnQW Q (hlkPk λ).Λ`.** -/
theorem hnQCh_shape : HlWShape (hnQW Q (hlkPk l).Λ) 0 (hnQCh Q l hl hle IH H).U := by
  rw [hlkPk_lim_Λ hl hle]
  refine ⟨by show veblen (Om1 * (1 + l)) (Q.F + 1) = veblen (Om1 * (1 + l) + 0) (Q.F + 1); rw [add_zero],
    fun x _ _ => ?_, fun x _ _ hg => ?_, fun x hx _ => ?_, fun c σ hFc hc hσ hσ1 hg => ?_⟩
  · show max Q.γ (hlGt (1 + l)) < x ↔ max (max Q.γ (hlGt (1 + l))) 0 < x
    rw [max_eq_left zero_le]
  · show veblen (x * (1 + l)) (Q.Fr x + 1) =
      veblen ((hlMLv (1 + l) le_self_add (hl_one_add hle)).l x + 0) (Q.Fr x + 1)
    rw [hlMLv_l _ _ _ (max_lt_iff.1 (max_lt_iff.1 hg).1).2, add_zero]
  · show (if max Q.γ (hlGt (1 + l)) < x then evZ (veblen (x * (1 + l)) (Q.Fr x + 1))
        else (hnQW Q (hlMLv (1 + l) le_self_add (hl_one_add hle))).hlwZo x) =
      if max (max Q.γ (hlGt (1 + l))) 0 < x then
        evZ (veblen ((hlMLv (1 + l) le_self_add (hl_one_add hle)).l x + 0) (Q.Fr x + 1))
        else (hnQW Q (hlMLv (1 + l) le_self_add (hl_one_add hle))).hlwZo x
    rw [max_eq_left zero_le, add_zero]
    split_ifs with h
    · rw [hlMLv_l _ _ _ (max_lt_iff.1 h).2]
    · rfl
  · obtain ⟨k, hk⟩ := (hnQCh Q l hl hle IH H).B_cof c hc
    rw [(hnQCh Q l hl hle IH H).U_g (k := k) hk] at hg
    exact (H.1 _ _).1.2.2.2.2 c σ hFc hk hσ hσ1 hg

end Lim

open Classical in
/-- **The limit case**: the union of the chain (when `λ < Ω₁` and the condition holds). -/
noncomputable def hnQLimF (Q : HnVQ hnSqLv 0) (S0 : HgVD) (l : Ordinal.{0}) (hl : IsSuccLimit l)
    (IH : ∀ μ, μ < l → HgVD) : HgVD :=
  if h : l < Om1 ∧ HnQCoh Q l IH then (hnQCh Q l hl h.1 IH h.2).U else S0

open Classical in
/-- **The successor case**: the union of all levels `Ω₁·(1+μ) + κ` over `Q`, started at the given system. -/
noncomputable def hnQSucc (Q : HnVQ hnSqLv 0) (μ : Ordinal.{0}) (S : HgVD) : HgVD :=
  if h : HlWShape (hnQW Q (hlkPk μ).Λ) 0 S then hlwU (hnQW Q (hlkPk μ).Λ) (hlkPk μ).St0 (hlkPk μ).h0 S h else S

section Rec

variable (Q : HnVQ hnSqLv 0) (U : HgVD) (hU : HgSStart (hnVPB Q) U)

include hU in
theorem hnQ1_start : HgSStart (hlVPB (hnQ1 Q)) U := by rw [hnQ1_PB]; exact hU

/-- **The member `0`**: the step of the level `Ω₁ + 0` at `Q` (`Hl.hlPk1`). -/
noncomputable def hnQM0 : HgVD := hlPk1.St0 (hnQ1 Q) U (hnQ1_start Q U hU)

theorem hnQM0_spec : HlVSpec (hnQ1 Q) U (hnQM0 Q U hU) := hlPk1.h0 (hnQ1 Q) U (hnQ1_start Q U hU)

/-- **THE SYSTEMS OVER `Q` AT `φ(Ω₁·(1+μ), F+1)`, BY ONE RECURSION ON `μ`.** -/
noncomputable def hnQGS (μ : Ordinal.{0}) : HgVD :=
  Ordinal.limitRecOn (motive := fun _ => HgVD) μ (hnQM0 Q U hU) (hnQSucc Q) (hnQLimF Q (hnQM0 Q U hU))

theorem hnQGS_zero : hnQGS Q U hU 0 = hnQM0 Q U hU := by unfold hnQGS; rw [Ordinal.limitRecOn_zero]

theorem hnQGS_succ (μ : Ordinal.{0}) : hnQGS Q U hU (μ + 1) = hnQSucc Q μ (hnQGS Q U hU μ) := by
  unfold hnQGS; rw [Ordinal.limitRecOn_add_one]

theorem hnQGS_limit {l : Ordinal.{0}} (hl : IsSuccLimit l) :
    hnQGS Q U hU l = hnQLimF Q (hnQM0 Q U hU) l hl (fun μ _ => hnQGS Q U hU μ) := by
  unfold hnQGS; rw [Ordinal.limitRecOn_limit _ _ _ _ hl]

theorem hnQGS_Bsh {μ : Ordinal.{0}} (hμ : μ < Om1) {S0 : HgVD} (h : HlWShape (hnQW Q (hlkPk μ).Λ) 0 S0) :
    S0.B = veblen (Om1 * (1 + μ)) (Q.F + 1) := by
  rw [h.1]; show veblen ((hlkPk μ).Λ.L + 0) (Q.F + 1) = _; rw [hlkPk_L hμ, add_zero]

/-- **THE INVARIANT**: every `hnQGS μ`, `μ < Ω₁`, is a start over `hnQW Q (hlkPk μ).Λ` with base gate
`max Q.γ (hlkPk μ).g`, and extends every `hnQGS μ'`, `μ' < μ`. -/
theorem hnQGS_inv : ∀ μ, μ < Om1 → (HlWShape (hnQW Q (hlkPk μ).Λ) 0 (hnQGS Q U hU μ) ∧
    (hnQGS Q U hU μ).γ = max Q.γ (hlkPk μ).Λ.g) ∧
    ∀ μ', μ' < μ → ∀ c x, c < (hnQGS Q U hU μ').B → (hnQGS Q U hU μ).R c x = (hnQGS Q U hU μ').R c x ∧
      (hnQGS Q U hU μ).g c = (hnQGS Q U hU μ').g c := by
  intro μ
  induction μ using WellFoundedLT.induction with
  | ind μ IH =>
  intro hμ
  rcases zero_or_succ_or_isSuccLimit μ with h0 | ⟨ν, hν⟩ | hlim
  · subst h0
    rw [hnQGS_zero, hlkPk_zero]
    refine ⟨⟨hnQ1_shape Q (hnQM0_spec Q U hU), ?_⟩, fun μ' h => absurd h (not_lt.2 zero_le)⟩
    show (hnQM0 Q U hU).γ = max Q.γ 0
    rw [(hnQM0_spec Q U hU).γ, max_eq_left zero_le]; rfl
  · have hν' : μ = ν + 1 := by rw [← hν, succ_eq_add_one]
    subst hν'
    have hνε : ν < Om1 := (lt_add_one ν).trans hμ
    obtain ⟨⟨hsh, hγ⟩, hext⟩ := IH ν (lt_add_one ν) hνε
    have e : hnQGS Q U hU (ν + 1) = hlwU (hnQW Q (hlkPk ν).Λ) (hlkPk ν).St0 (hlkPk ν).h0 (hnQGS Q U hU ν) hsh := by
      rw [hnQGS_succ]; unfold hnQSucc; rw [dif_pos hsh]
    refine ⟨⟨?_, by rw [e, hlkPk_succ]; rfl⟩, fun μ' hμ' c x hc => ?_⟩
    · rw [e, hlkPk_succ]
      exact hnQU_shape Q (hlkPk ν).Λ (hlkPk ν).St0 (hlkPk ν).h0 _ hsh
    · rw [e]
      rcases (Order.lt_add_one_iff.1 hμ').lt_or_eq with hlt | heq
      · obtain ⟨⟨hsh', -⟩, -⟩ := IH μ' (hlt.trans (lt_add_one ν)) (hlt.trans hνε)
        have hc0 : c < (hnQGS Q U hU ν).B := by
          rw [hnQGS_Bsh Q hνε hsh]; rw [hnQGS_Bsh Q (hlt.trans hνε) hsh'] at hc
          exact hc.trans (hd_veb_left_lt (mul_lt_mul_of_pos_left ((add_lt_add_iff_left 1).2 hlt) gv_Om1_pos) _)
        obtain ⟨r1, g1⟩ := hext μ' hlt c x hc
        exact ⟨(hlwU_R0 (hnQW Q (hlkPk ν).Λ) (hlkPk ν).St0 (hlkPk ν).h0 _ hsh hc0 x).trans r1,
          (hlwU_g0 (hnQW Q (hlkPk ν).Λ) (hlkPk ν).St0 (hlkPk ν).h0 _ hsh hc0).trans g1⟩
      · subst heq
        exact ⟨hlwU_R0 (hnQW Q (hlkPk μ').Λ) (hlkPk μ').St0 (hlkPk μ').h0 _ hsh hc x,
          hlwU_g0 (hnQW Q (hlkPk μ').Λ) (hlkPk μ').St0 (hlkPk μ').h0 _ hsh hc⟩
  · have hcoh : HnQCoh Q μ (fun μ' _ => hnQGS Q U hU μ') :=
      ⟨fun μ' h => (IH μ' h (h.trans hμ)).1, fun μ₁ μ₂ h₁ h₂ h12 => (IH μ₂ h₂ (h₂.trans hμ)).2 μ₁ h12⟩
    have e : hnQGS Q U hU μ = (hnQCh Q μ hlim hμ (fun μ' _ => hnQGS Q U hU μ') hcoh).U := by
      rw [hnQGS_limit Q U hU hlim]; unfold hnQLimF; rw [dif_pos ⟨hμ, hcoh⟩]
    refine ⟨⟨by rw [e]; exact hnQCh_shape Q μ hlim hμ _ hcoh, by rw [e, hlkPk_lim_Λ hlim hμ]; rfl⟩,
      fun μ' hμ' c x hc => ?_⟩
    rw [e]
    obtain ⟨k, hk⟩ := heFs_cof hlim (hl_om hμ) μ' hμ'
    have hkl := heFs_lt hlim (hl_om hμ) k
    obtain ⟨⟨hsh', -⟩, -⟩ := IH μ' hμ' (hμ'.trans hμ)
    obtain ⟨-, hextk⟩ := IH _ hkl (hkl.trans hμ)
    have hc' : c < (hnQGS Q U hU (heFs μ k)).B := by
      rw [hnQCoh_B Q μ hlim hμ _ hcoh k]; rw [hnQGS_Bsh Q (hμ'.trans hμ) hsh'] at hc
      exact hc.trans (hd_veb_left_lt (mul_lt_mul_of_pos_left ((add_lt_add_iff_left 1).2 hk) gv_Om1_pos) _)
    obtain ⟨r2, g2⟩ := hextk μ' hk c x hc
    exact ⟨((hnQCh Q μ hlim hμ (fun μ' _ => hnQGS Q U hU μ') hcoh).U_R (k := k) hc' x).trans r2,
      ((hnQCh Q μ hlim hμ (fun μ' _ => hnQGS Q U hU μ') hcoh).U_g (k := k) hc').trans g2⟩

theorem hnQGS_shape {μ : Ordinal.{0}} (hμ : μ < Om1) : HlWShape (hnQW Q (hlkPk μ).Λ) 0 (hnQGS Q U hU μ) :=
  (hnQGS_inv Q U hU μ hμ).1.1

theorem hnQGS_γ {μ : Ordinal.{0}} (hμ : μ < Om1) : (hnQGS Q U hU μ).γ = max Q.γ (hlkPk μ).Λ.g :=
  (hnQGS_inv Q U hU μ hμ).1.2

/-- **The bound of `hnQGS μ` is `φ(Ω₁·(1+μ), F+1)`.** -/
theorem hnQGS_B {μ : Ordinal.{0}} (hμ : μ < Om1) : (hnQGS Q U hU μ).B = veblen (Om1 * (1 + μ)) (Q.F + 1) :=
  hnQGS_Bsh Q hμ (hnQGS_shape Q U hU hμ)

theorem hnQGS_ext {μ' μ : Ordinal.{0}} (hμ : μ < Om1) (h : μ' < μ) {c : Ordinal.{0}} (hc : c < (hnQGS Q U hU μ').B)
    (x : Ordinal.{0}) : (hnQGS Q U hU μ).R c x = (hnQGS Q U hU μ').R c x ∧
      (hnQGS Q U hU μ).g c = (hnQGS Q U hU μ').g c :=
  (hnQGS_inv Q U hU μ hμ).2 μ' h c x hc

theorem hnQGS_ext' {μ' μ : Ordinal.{0}} (hμ : μ < Om1) (h : μ' ≤ μ) {c : Ordinal.{0}}
    (hc : c < (hnQGS Q U hU μ').B) (x : Ordinal.{0}) :
    (hnQGS Q U hU μ).R c x = (hnQGS Q U hU μ').R c x ∧ (hnQGS Q U hU μ).g c = (hnQGS Q U hU μ').g c := by
  rcases h.lt_or_eq with h | rfl
  · exact hnQGS_ext Q U hU hμ h hc x
  · exact ⟨rfl, rfl⟩

end Rec

end Googology.Trans.PoR.InaccPsi.R2.Hn
