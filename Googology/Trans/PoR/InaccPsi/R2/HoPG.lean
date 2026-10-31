import Googology.Trans.PoR.InaccPsi.R2.HoPk

/-!
# HoPG: OVER `G`, ONE RECURSION OF SYSTEMS AT `φ(Ω₁²·(1+ν), G+1)`, `ν < Ω₁`

`hoSg 0 = Hl.hlU` (bound `φ(Ω₁·Ω₁, G+1)`); `hoSg (ν+1)` is the union `Ho.hoGU` over `G` of the band systems of the
prefix package `hoKp ν` started at `hoSg ν` (bound `φ(Ω₁²·(1+ν+1), G+1)`); at a limit `λ` the union of the gated
`ω`-chain of the systems at `heFs λ k` (bound `φ(Ω₁²·(1+λ), G+1)`, base reading `φ(x·x·(1+λ), Γ_{x+1}+1)`, gate
`hlGt (1+λ)`).  Each is a start over `G` at the first band package of the prefix, and extends the earlier ones.

* `hoKfp ν` (the band family of `hoKp ν`), `hoK0g`, `HoGSh` (the start condition), `hoGSh_B`, `hoGSh_γ`, `hoGSh_b`;
* `HoGCoh`, `hoGCh` (**THE PREFIX CHAIN OVER `G`**), `hoGCh_shape`, `hoGSucc`, `hoGLimF`;
* `hoSg ν` (**THE SYSTEMS**), `hoSg_inv` (**THE INVARIANT**), `hoSg_B`, `hoSg_γ`, `hoSg_ext`, `hoSg_small` (**SMALL**).

No new axiom.  New definitions: `hoKfp`, `HoGSh`, `HoGCoh`, `hoGCh`, `hoGSucc`, `hoGLimF`, `hoSg`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ho

open Googology.Trans.PoR.InaccPsi.R2.Hn Googology.Trans.PoR.InaccPsi.R2.Hl
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

/-- **The band family of the prefix package `hoKp ν`.** -/
noncomputable def hoKfp (ν : Ordinal.{0}) (hν : ν < Om1) : HoBF (1 + ν) le_self_add (hl_one_add hν) :=
  hoKf le_self_add (hl_one_add hν) (hoKp ν) (hoKp_inv ν hν).1.1 (hoKp_inv ν hν).1.2.1 (hoKp_inv ν hν).1.2.2

theorem hoK0eq (ν : Ordinal.{0}) (hν : ν < Om1) : (hoKfp ν hν).K 0 = hoKp ν :=
  hoBF_K0 le_self_add (hl_one_add hν) (hoKp ν) (hoKp_inv ν hν).1.1 (hoKp_inv ν hν).1.2.1 (hoKp_inv ν hν).1.2.2

theorem hoK0g (ν : Ordinal.{0}) (hν : ν < Om1) : ((hoKfp ν hν).K 0).Λ.g = hlGt (1 + ν) := by
  refine le_antisymm (((hoKfp ν hν).ghi 0 gv_Om1_pos).trans ?_) ((hoKfp ν hν).glo 0 gv_Om1_pos)
  rw [ho_hlGt0, max_eq_left zero_le]

theorem hoK0L (ν : Ordinal.{0}) (hν : ν < Om1) : ((hoKfp ν hν).K 0).Λ.L = Om1 * Om1 * (1 + ν) := by
  rw [(hoKfp ν hν).L 0 gv_Om1_pos, mul_zero, add_zero]

theorem hoK0l (ν : Ordinal.{0}) (hν : ν < Om1) (x : Ordinal.{0}) (hx : ((hoKfp ν hν).K 0).Λ.g < x) :
    ((hoKfp ν hν).K 0).Λ.l x = x * x * (1 + ν) := by
  rw [(hoKfp ν hν).l 0 gv_Om1_pos x hx, mul_zero, add_zero]

/-- **The start condition at the prefix `Ω₁²·(1+ν)`**: a start over `G` at the first band package, base gate
`max 0 g`. -/
def HoGSh (ν : Ordinal.{0}) (hν : ν < Om1) (S : HgVD) : Prop :=
  HnWShape (hoW (hoGD (1 + ν) (hl_one_add hν)) ((hoKfp ν hν).K 0).Λ ((hoKfp ν hν).good gv_Om1_pos)) 0 S ∧
    S.γ = max (hoGD (1 + ν) (hl_one_add hν)).γ ((hoKfp ν hν).K 0).Λ.g

theorem ho_sqv_lt_G' {v : Ordinal.{0}} (hv : v < Om1) : (Om1 : Ordinal.{0}) * Om1 * v < gcG 0 := ho_sqv_lt_G hv 0

theorem hoG_fixv {v : Ordinal.{0}} (hv : v < Om1) : veblen (Om1 * Om1 * v) (gcG 0) = gcG 0 :=
  gn_veb_fix (gcG_SC 0) (ho_sqv_lt_G' hv)

section Sh

variable {ν : Ordinal.{0}} (hν : ν < Om1) {S : HgVD} (h : HoGSh ν hν S)
include h

theorem hoGSh_B : S.B = veblen (Om1 * Om1 * (1 + ν)) (gcG 0 + 1) := by
  rw [h.1.1]; show veblen (((hoKfp ν hν).K 0).Λ.L + 0) (gcG 0 + 1) = _; rw [add_zero, hoK0L]

theorem hoGSh_γ : S.γ = max 0 (hlGt (1 + ν)) := by rw [h.2, hoK0g]; rfl

theorem hoGSh_b {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hg : hlGt (1 + ν) < x) :
    S.b x = veblen (x * x * (1 + ν)) (lgG x + 1) := by
  have hg' : ((hoKfp ν hν).K 0).Λ.g < x := by rw [hoK0g]; exact hg
  rw [h.1.2.2.1 x hx hx1 (max_lt (max_lt hx.pos hg') hx.pos)]
  show veblen (((hoKfp ν hν).K 0).Λ.l x + 0) (lgG x + 1) = _
  rw [add_zero, hoK0l ν hν x hg']

theorem hoGSh_Z {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    S.Z x = if hlGt (1 + ν) < x then evZ (veblen (x * x * (1 + ν)) (lgG x + 1)) else hoZo x := by
  rw [h.1.2.2.2.1 x hx hx1]
  have hiff : max (hoW (hoGD (1 + ν) (hl_one_add hν)) ((hoKfp ν hν).K 0).Λ ((hoKfp ν hν).good gv_Om1_pos)).γR 0 < x ↔
      hlGt (1 + ν) < x := by
    show max (max 0 ((hoKfp ν hν).K 0).Λ.g) 0 < x ↔ _
    rw [hoK0g, max_eq_left zero_le]; exact ⟨fun h' => (max_lt_iff.1 h').2, fun h' => max_lt hx.pos h'⟩
  by_cases hg : hlGt (1 + ν) < x
  · rw [if_pos ((hiff).2 hg), if_pos hg, add_zero, hoK0l ν hν x (by rw [hoK0g]; exact hg)]; rfl
  · rw [if_neg (fun h' => hg ((hiff).1 h')), if_neg hg, hoW_Zo_low]
    · rfl
    · exact fun h' => hg (by rw [← hoK0g ν hν]; exact (max_lt_iff.1 h').2)

end Sh

/-! ## Level arithmetic at the prefixes -/

theorem ho_sqv_one {a v : Ordinal.{0}} (ha : InE a) (hv1 : 1 ≤ v) : (1 : Ordinal.{0}) < a * a * v :=
  (one_lt_omega0.trans ((omega0_lt_inE ha).trans (hl_lt_sq ha))).trans_le (ho_xsq_le hv1)

theorem ho_sqv_ne {a v : Ordinal.{0}} (ha : InE a) (hv1 : 1 ≤ v) : a * a * v ≠ 0 :=
  (zero_lt_one.trans (ho_sqv_one ha hv1)).ne'

theorem ho_sqv_lgG {x v : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hv : v < x) : x * x * v < lgG x :=
  InE.mul_lt (lgG_facts hx hx1).2.2.2.1 (hl_sq_lt hx hx1) (hv.trans (lgG_facts hx hx1).2.1)

theorem ho_xsqv_lt3 {x v : Ordinal.{0}} (hx : InE x) (hv : v < x) : x * x * v < x * x * x :=
  mul_lt_mul_of_pos_left hv (mul_pos hx.pos hx.pos)

theorem ho_G1v {v : Ordinal.{0}} (hv : v < Om1) : veblen (Om1 * Om1 * v) (gcG 0 + 1) < gcG 1 := by
  have hG1 := gcG_SC 1
  have hE := Low.opow_eq_self_of_SC hG1
  have hfix : veblen (Om1 * Om1 * v) (gcG 1) = gcG 1 := gn_veb_fix hG1 (ho_sqv_lt_G hv 1)
  have h2 := (isNormal_veblen (Om1 * Om1 * v)).strictMono ((ev_isSuccLimit_of_inE hE).add_one_lt (gcG_lt zero_lt_one))
  rwa [hfix] at h2

theorem ho_x1v {x v : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hv1 : 1 ≤ v) (hv : v < x) :
    veblen (x * x * v) (lgG x + 1) = hdNx (x * x * v) (lgG x) :=
  (hdNx_fixP (hjG_fix hx hx1 (ho_sqv_one hx hv1).le (ho_sqv_lgG hx hx1 hv))).symm

/-! ## The prefix chain over `G` -/

/-- **The condition at a limit**: the earlier systems satisfy the start condition and extend each other. -/
def HoGCoh (l : Ordinal.{0}) (IH : ∀ ν, ν < l → HgVD) : Prop :=
  (∀ ν (h : ν < l) (hν : ν < Om1), HoGSh ν hν (IH ν h)) ∧
    ∀ ν' ν (h' : ν' < l) (h : ν < l), ν' < ν → ∀ c x, c < (IH ν' h').B →
      (IH ν h).R c x = (IH ν' h').R c x ∧ (IH ν h).g c = (IH ν' h').g c

section Lim

variable (l : Ordinal.{0}) (hl : IsSuccLimit l) (hle : l < Om1) (IH : ∀ ν, ν < l → HgVD) (H : HoGCoh l IH)
include hl hle

theorem hoGCh_hk (k : ℕ) : heFs l k < Om1 := (heFs_lt hl (hl_om hle) k).trans hle

theorem hoGCh_mono (k : ℕ) : 1 + heFs l k < 1 + heFs l (k + 1) :=
  (add_lt_add_iff_left 1).2 (heFs_mono hl (hl_om hle) k)

theorem hoGCh_lt (k : ℕ) : 1 + heFs l k < 1 + l := (add_lt_add_iff_left 1).2 (heFs_lt hl (hl_om hle) k)

theorem hoGCh_cof : ∀ t, t < 1 + l → ∃ k, t < 1 + heFs l k := fun t ht => by
  rw [ho_1l_eq hl] at ht
  obtain ⟨k, hk⟩ := heFs_cof hl (hl_om hle) t ht
  exact ⟨k, hk.trans_le le_add_self⟩

include H in
theorem hoGCh_B (k : ℕ) :
    (IH (heFs l k) (heFs_lt hl (hl_om hle) k)).B = veblen (Om1 * Om1 * (1 + heFs l k)) (gcG 0 + 1) :=
  hoGSh_B (hoGCh_hk l hl hle k) (H.1 _ _ (hoGCh_hk l hl hle k))

include H in
theorem hoGCh_b (k : ℕ) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγ : hlGt (1 + l) < x) :
    (IH (heFs l k) (heFs_lt hl (hl_om hle) k)).b x = veblen (x * x * (1 + heFs l k)) (lgG x + 1) :=
  hoGSh_b (hoGCh_hk l hl hle k) (H.1 _ _ (hoGCh_hk l hl hle k)) hx hx1
    ((hlGt_mono (hoGCh_lt l hl hle k).le).trans_lt hγ)

/-- **THE GATED `ω`-CHAIN OF THE SYSTEMS `IH (heFs λ k)` OVER `G`**: union bound `φ(Ω₁²·(1+λ), G+1)`, union base
reading `φ(x·x·(1+λ), Γ_{x+1}+1)`, union base gate `hlGt (1+λ)`, low field `hoZo`. -/
noncomputable def hoGCh : HgfCh where
  D := fun k => IH (heFs l k) (heFs_lt hl (hl_om hle) k)
  B := veblen (Om1 * Om1 * (1 + l)) (gcG 0 + 1)
  b := fun x => veblen (x * x * (1 + l)) (lgG x + 1)
  γ := hlGt (1 + l)
  Zo := hoZo
  γ_lt := (hlGt_le _).trans_lt (hl_one_add hle)
  γ0 := fun k => by
    rw [hoGSh_γ (hoGCh_hk l hl hle k) (H.1 _ _ (hoGCh_hk l hl hle k))]
    exact max_le zero_le (hlGt_mono (hoGCh_lt l hl hle k).le)
  γ_cl := fun Z hZ hZ1 h => by
    have ha : (1 : Ordinal.{0}) ≤ Om1 * Om1 * (1 + l) := (ho_sqv_one gl_Om1_E le_self_add).le
    have hG : gcG 0 < veblen (Om1 * Om1 * (1 + l)) (gcG 0 + 1) := (lt_add_one _).trans_le (right_le_veblen _ _)
    have hc := hi_cl_lvl ha hZ1 (hd_succ_lt (ho_sqv_ne gl_Om1_E le_self_add) _) hG h le_rfl
      ((isNormal_veblen _).strictMono (lt_add_one _))
    have hhi : Om1 * Om1 * (1 + l) < Om1 * Om1 * Om1 := mul_lt_mul_of_pos_left (hl_one_add hle) ho_OO_pos
    exact (hlGt_le _).trans_lt (ho_cl_sq hZ hZ1 hc le_rfl hhi)
  B_mono := fun k => by
    rw [hoGCh_B l hl hle IH H, hoGCh_B l hl hle IH H]
    exact (hd_veb_left_lt (mul_lt_mul_of_pos_left (hoGCh_mono l hl hle k) ho_OO_pos) _).le
  B_lt := fun k => by
    rw [hoGCh_B l hl hle IH H]
    exact hd_veb_left_lt (mul_lt_mul_of_pos_left (hoGCh_lt l hl hle k) ho_OO_pos) _
  B_cof := fun c hc => by
    obtain ⟨b, hb, hcb⟩ := hgVeb_cof (ho_sqv_ne gl_Om1_E le_self_add) (hoG_fixv (hl_one_add hle)) hc
    obtain ⟨k, hk⟩ := hk_mul_cof1 (Ms := fun k => 1 + heFs l k) ho_OO_pos (hoGCh_mono l hl hle)
      (hoGCh_cof l hl hle) hb
    refine ⟨k, ?_⟩
    rw [hoGCh_B l hl hle IH H, ← hdNx_fixP (hoG_fixv (hl_one_add (hoGCh_hk l hl hle k)))]
    exact hcb.trans (hdN_lt_Nx hk)
  R_ext := fun k c x hc => (H.2 _ _ _ _ (heFs_mono hl (hl_om hle) k) c x hc).1
  g_ext := fun k c hc => (H.2 _ _ _ _ (heFs_mono hl (hl_om hle) k) c 0 hc).2
  B_lt1 := ho_G1v (hl_one_add hle)
  B_fix := veblen_veblen_of_lt (ho_sqv_one gl_Om1_E le_self_add) _
  B_mem := fun S a b ha hb =>
    CSet.phi_mem (ho_sqmul_mem S a b _ (ho_gt_or hb)) (CSet.succ_mem (gmS_G0_mem S ha))
  b_ge := fun k x hx hx1 hγ => by
    rw [hoGCh_b l hl hle IH H k hx hx1 hγ]
    exact (hd_veb_left_lt (mul_lt_mul_of_pos_left (hoGCh_lt l hl hle k) (mul_pos hx.pos hx.pos)) _).le
  b_cof := fun x hx hx1 hγ ν hν => by
    have hlx : 1 + l < x := hl_gt_E hx hγ
    obtain ⟨b, hb, hνb⟩ := hgVeb_cof (ho_sqv_ne hx le_self_add)
      (hjG_fix hx hx1 (ho_sqv_one hx le_self_add).le (ho_sqv_lgG hx hx1 hlx)) hν
    obtain ⟨k, hk⟩ := hk_mul_cof1 (Ms := fun k => 1 + heFs l k) (mul_pos hx.pos hx.pos) (hoGCh_mono l hl hle)
      (hoGCh_cof l hl hle) hb
    refine ⟨k, ?_⟩
    rw [hoGCh_b l hl hle IH H k hx hx1 hγ, ho_x1v hx hx1 le_self_add ((hoGCh_lt l hl hle k).trans hlx)]
    exact hνb.trans (hdN_lt_Nx hk)
  b_fix := fun x hx _ _ => veblen_veblen_of_lt (ho_sqv_one hx le_self_add) _
  b_gt := fun x hx hx1 _ => (lgG_facts hx hx1).2.1.trans ((lt_add_one _).trans_le (right_le_veblen _ _))
  b_lt := fun x hx hx1 hγ => by
    have hlx : 1 + l < x := hl_gt_E hx hγ
    rw [ho_x1v hx hx1 le_self_add hlx]
    exact hjG_lt1 hx hx1 (ho_sqv_one hx le_self_add).le (ho_sqv_lgG hx hx1 hlx)
  b_pi := fun σ ρ hB hγ => by
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
    have hlσ : 1 + l < σ := hl_gt_E hB.1 hγ
    have hlρ : 1 + l < ρ := hlσ.trans hB.2.2.1
    rw [ho_x1v hB.2.1 hρ1 le_self_add hlρ, ho_x1v hB.1 hσ1 le_self_add hlσ]
    exact hjG_S_pi hB (ho_pi_sqmul hB (1 + l) hlσ) (ho_sqv_one hB.2.1 le_self_add).le (ho_sqv_lgG hB.2.1 hρ1 hlρ)
      (ho_sqv_one hB.1 le_self_add).le (ho_sqv_lgG hB.1 hσ1 hlσ)
  Z_low := fun k x hx hx1 h => by
    have hk1 := hoGCh_hk l hl hle k
    show (IH (heFs l k) (heFs_lt hl (hl_om hle) k)).Z x ≤ hoZo x
    rw [hoGSh_Z hk1 (H.1 _ _ hk1) hx hx1]
    split_ifs with h'
    · refine (hb_evZ_lt_fix2 (hoZo_fix x) ?_).le
      rw [hoZo_eq hx]
      exact hd_veb_left_lt (ho_xsqv_lt3 hx (hl_gt_E hx h')) _
    · exact le_rfl
  Zo_fix := fun x => hc_fix_down one_le_two (hoZo_fix x)
  Zo_G1 := hoZo_G1

/-- **The union of the chain satisfies the start condition at the prefix `Ω₁²·(1+λ)`.** -/
theorem hoGCh_shape : HoGSh l hle (hoGCh l hl hle IH H).U := by
  have eΛ : hoLv (1 + l) 0 le_self_add (hl_one_add hle) gv_Om1_pos = ((hoKfp l hle).K 0).Λ :=
    ((congrArg HnPk.Λ (hoK0eq l hle)).trans (hoKp_lim_Λ hl hle)).symm
  have hg : (hoLv (1 + l) 0 le_self_add (hl_one_add hle) gv_Om1_pos).g = hlGt (1 + l) := by
    show max (hlGt (1 + l)) (hlGt 0) = _; rw [ho_hlGt0, max_eq_left zero_le]
  have hgd : HoGood (1 + l) (hoLv (1 + l) 0 le_self_add (hl_one_add hle) gv_Om1_pos) := hoLv_good _ _ _
  refine ⟨hoW_congr (hoGD (1 + l) (hl_one_add hle)) _ hgd eΛ _ ?_, ?_⟩
  · have hB : veblen (Om1 * Om1 * (1 + l)) (gcG 0 + 1) = veblen (Om1 * Om1 * (1 + l) + Om1 * 0 + 0) (gcG 0 + 1) := by
      rw [mul_zero, add_zero, add_zero]
    refine ⟨hB, fun x _ _ => ?_, fun x _ _ hgx => ?_, fun x hx _ => ?_,
      fun _ σ _ _ hσ _ _ => hσ.pos⟩
    · show hlGt (1 + l) < x ↔ max (max 0 (hoLv (1 + l) 0 le_self_add (hl_one_add hle) gv_Om1_pos).g) 0 < x
      rw [hg, max_eq_left zero_le, max_eq_right zero_le]
    · have hgx' : (hoLv (1 + l) 0 le_self_add (hl_one_add hle) gv_Om1_pos).g < x :=
        (max_lt_iff.1 (max_lt_iff.1 hgx).1).2
      show veblen (x * x * (1 + l)) (lgG x + 1) = veblen ((hoLv (1 + l) 0 _ _ _).l x + 0) (lgG x + 1)
      rw [hoLv_l0 _ _ hgx', add_zero]
    · show (if hlGt (1 + l) < x then evZ (veblen (x * x * (1 + l)) (lgG x + 1)) else hoZo x) =
        if max (max 0 (hoLv (1 + l) 0 le_self_add (hl_one_add hle) gv_Om1_pos).g) 0 < x then
          evZ (veblen ((hoLv (1 + l) 0 le_self_add (hl_one_add hle) gv_Om1_pos).l x + 0) (lgG x + 1))
          else (hoW (hoGD (1 + l) (hl_one_add hle)) _ hgd).hnwZo x
      rw [hg, max_eq_left zero_le, max_eq_right zero_le]
      split_ifs with h
      · rw [hoLv_l0 _ _ (by rw [hg]; exact h), add_zero]
      · rw [hoW_Zo_low _ _ _ (fun h' => h (by rw [← hg]; exact (max_lt_iff.1 h').2))]; rfl
  · show hlGt (1 + l) = max 0 ((hoKfp l hle).K 0).Λ.g
    rw [hoK0g, max_eq_right zero_le]

end Lim

open Classical in
/-- **The limit case**: the union of the chain (when `λ < Ω₁` and the condition holds). -/
noncomputable def hoGLimF (l : Ordinal.{0}) (hl : IsSuccLimit l) (IH : ∀ ν, ν < l → HgVD) : HgVD :=
  if h : l < Om1 ∧ HoGCoh l IH then (hoGCh l hl h.1 IH h.2).U else hlU

open Classical in
/-- **The successor case**: the union `Ho.hoGU` over `G` of the band systems of `hoKp ν`, started at `S`. -/
noncomputable def hoGSucc (ν : Ordinal.{0}) (S : HgVD) : HgVD :=
  if hν : ν < Om1 then
    (if h : HoGSh ν hν S then
      hoGU le_self_add (hl_one_add hν) (hoKp ν) (hoKp_inv ν hν).1.1 (hoKp_inv ν hν).1.2.1 (hoKp_inv ν hν).1.2.2 S
        h.1 h.2
      else S)
  else S

/-- **THE SYSTEMS OVER `G` AT `φ(Ω₁²·(1+ν), G+1)`, BY ONE RECURSION ON `ν`.** -/
noncomputable def hoSg (ν : Ordinal.{0}) : HgVD :=
  Ordinal.limitRecOn (motive := fun _ => HgVD) ν hlU hoGSucc hoGLimF

theorem hoSg_zero : hoSg 0 = hlU := by unfold hoSg; rw [Ordinal.limitRecOn_zero]

theorem hoSg_succ (ν : Ordinal.{0}) : hoSg (ν + 1) = hoGSucc ν (hoSg ν) := by
  unfold hoSg; rw [Ordinal.limitRecOn_add_one]

theorem hoSg_limit {l : Ordinal.{0}} (hl : IsSuccLimit l) : hoSg l = hoGLimF l hl (fun ν _ => hoSg ν) := by
  unfold hoSg; rw [Ordinal.limitRecOn_limit _ _ _ _ hl]

/-- **`Hl.hlU` satisfies the start condition at the prefix `Ω₁²·1`.** -/
theorem hoSh_hlU : HoGSh 0 gv_Om1_pos hlU := by
  have eΛ : hnPkSq.Λ = ((hoKfp 0 gv_Om1_pos).K 0).Λ := (congrArg HnPk.Λ ((hoK0eq 0 gv_Om1_pos).trans hoKp_zero)).symm
  have hgd : HoGood (1 + 0) hnPkSq.Λ :=
    hoGood_of gv_Om1_pos (by show Om1 * Om1 = _; rw [add_zero, mul_one, mul_zero, add_zero])
      (fun x _ => by show x * x = _; rw [add_zero, mul_one, mul_zero, add_zero])
      (by show hlGt (1 + 0) ≤ 0; rw [ho_hlGt1]) (fun _ hx _ _ => hx.pos)
  refine ⟨hoW_congr (hoGD (1 + 0) (hl_one_add gv_Om1_pos)) _ hgd eΛ _ ?_, ?_⟩
  · refine ⟨by show veblen (Om1 * Om1) (gcG 0 + 1) = veblen (Om1 * Om1 + 0) (gcG 0 + 1); rw [add_zero],
      fun x _ _ => ?_, fun x _ _ _ => ?_, fun x hx _ => ?_, fun _ σ _ _ hσ _ _ => hσ.pos⟩
    · show (0 : Ordinal.{0}) < x ↔ max (max (0 : Ordinal.{0}) 0) 0 < x
      rw [max_self, max_self]
    · show veblen (x * x) (lgG x + 1) = veblen (x * x + 0) (lgG x + 1)
      rw [add_zero]
    · show evZ (hlBR x) = if max (max (0 : Ordinal.{0}) 0) 0 < x then evZ (veblen (x * x + 0) (lgG x + 1))
        else (hoW (hoGD (1 + 0) (hl_one_add gv_Om1_pos)) hnPkSq.Λ hgd).hnwZo x
      rw [max_self, max_self, if_pos hx.pos, add_zero]; rfl
  · show (0 : Ordinal.{0}) = max 0 ((hoKfp 0 gv_Om1_pos).K 0).Λ.g
    rw [hoK0g, ho_hlGt1, max_self]

/-- **THE INVARIANT**: every `hoSg ν`, `ν < Ω₁`, satisfies the start condition at the prefix `Ω₁²·(1+ν)` and extends
every `hoSg ν'`, `ν' < ν`. -/
theorem hoSg_inv : ∀ ν (hν : ν < Om1), HoGSh ν hν (hoSg ν) ∧
    ∀ ν', ν' < ν → ∀ c x, c < (hoSg ν').B → (hoSg ν).R c x = (hoSg ν').R c x ∧ (hoSg ν).g c = (hoSg ν').g c := by
  intro ν
  induction ν using WellFoundedLT.induction with
  | ind ν IH =>
  intro hν
  rcases zero_or_succ_or_isSuccLimit ν with h0 | ⟨μ, hμ⟩ | hlim
  · subst h0
    rw [hoSg_zero]
    exact ⟨hoSh_hlU, fun ν' h => absurd h (not_lt.2 zero_le)⟩
  · have hμ' : ν = μ + 1 := by rw [← hμ, succ_eq_add_one]
    subst hμ'
    have hμ1 : μ < Om1 := (lt_add_one μ).trans hν
    obtain ⟨hsh, hext⟩ := IH μ (lt_add_one μ) hμ1
    have e : hoSg (μ + 1) = hoGU le_self_add (hl_one_add hμ1) (hoKp μ) (hoKp_inv μ hμ1).1.1
        (hoKp_inv μ hμ1).1.2.1 (hoKp_inv μ hμ1).1.2.2 (hoSg μ) hsh.1 hsh.2 := by
      rw [hoSg_succ]; unfold hoGSucc; rw [dif_pos hμ1, dif_pos hsh]
    have hw : 1 + (μ + 1) = 1 + μ + 1 := (add_assoc 1 μ 1).symm
    have hshape := hoGU_shape le_self_add (hl_one_add hμ1) (hoKp μ) (hoKp_inv μ hμ1).1.1 (hoKp_inv μ hμ1).1.2.1
      (hoKp_inv μ hμ1).1.2.2 (hoSg μ) hsh.1 hsh.2 (1 + (μ + 1)) hw (hl_one_add hν) ((hoKfp (μ + 1) hν).K 0)
      (hoK0L (μ + 1) hν) (hoK0l (μ + 1) hν) (hoK0g (μ + 1) hν) ((hoKfp (μ + 1) hν).good gv_Om1_pos)
    refine ⟨by rw [e]; exact hshape, fun ν' hν' c x hc => ?_⟩
    rw [e]
    have hc0 : c < (hoSg μ).B := by
      rcases (Order.lt_add_one_iff.1 hν').lt_or_eq with hlt | heq
      · rw [hoGSh_B hμ1 hsh]; rw [hoGSh_B (hlt.trans hμ1) (IH ν' (hlt.trans (lt_add_one μ)) (hlt.trans hμ1)).1] at hc
        exact hc.trans (hd_veb_left_lt (mul_lt_mul_of_pos_left ((add_lt_add_iff_left 1).2 hlt) ho_OO_pos) _)
      · subst heq; exact hc
    obtain ⟨r1, g1⟩ := hoGU_ext0 le_self_add (hl_one_add hμ1) (hoKp μ) (hoKp_inv μ hμ1).1.1 (hoKp_inv μ hμ1).1.2.1
      (hoKp_inv μ hμ1).1.2.2 (hoSg μ) hsh.1 hsh.2 hc0 x
    rcases (Order.lt_add_one_iff.1 hν').lt_or_eq with hlt | heq
    · obtain ⟨r2, g2⟩ := hext ν' hlt c x hc
      exact ⟨r1.trans r2, g1.trans g2⟩
    · subst heq; exact ⟨r1, g1⟩
  · have hcoh : HoGCoh ν (fun ν' _ => hoSg ν') :=
      ⟨fun ν' h hν' => (IH ν' h hν').1, fun ν₁ ν₂ h₁ h₂ h12 => (IH ν₂ h₂ (h₂.trans hν)).2 ν₁ h12⟩
    have e : hoSg ν = (hoGCh ν hlim hν (fun ν' _ => hoSg ν') hcoh).U := by
      rw [hoSg_limit hlim]; unfold hoGLimF; rw [dif_pos ⟨hν, hcoh⟩]
    refine ⟨by rw [e]; exact hoGCh_shape ν hlim hν _ hcoh, fun ν' hν' c x hc => ?_⟩
    rw [e]
    obtain ⟨k, hk⟩ := heFs_cof hlim (hl_om hν) ν' hν'
    have hkl := heFs_lt hlim (hl_om hν) k
    obtain ⟨-, hextk⟩ := IH _ hkl (hkl.trans hν)
    have hc' : c < (hoSg (heFs ν k)).B := by
      rw [hoGSh_B (hkl.trans hν) (IH _ hkl (hkl.trans hν)).1]
      rw [hoGSh_B (hν'.trans hν) (IH ν' hν' (hν'.trans hν)).1] at hc
      exact hc.trans (hd_veb_left_lt (mul_lt_mul_of_pos_left ((add_lt_add_iff_left 1).2 hk) ho_OO_pos) _)
    obtain ⟨r2, g2⟩ := hextk ν' hk c x hc
    exact ⟨((hoGCh ν hlim hν (fun ν' _ => hoSg ν') hcoh).U_R (k := k) hc' x).trans r2,
      ((hoGCh ν hlim hν (fun ν' _ => hoSg ν') hcoh).U_g (k := k) hc').trans g2⟩

theorem hoSg_sh {ν : Ordinal.{0}} (hν : ν < Om1) : HoGSh ν hν (hoSg ν) := (hoSg_inv ν hν).1

/-- **The bound of `hoSg ν` is `φ(Ω₁²·(1+ν), G+1)`.** -/
theorem hoSg_B {ν : Ordinal.{0}} (hν : ν < Om1) : (hoSg ν).B = veblen (Om1 * Om1 * (1 + ν)) (gcG 0 + 1) :=
  hoGSh_B hν (hoSg_sh hν)

/-- **The base gate of `hoSg ν` is `hlGt (1+ν)`** (`0` for `ν < ε₀`). -/
theorem hoSg_γ {ν : Ordinal.{0}} (hν : ν < Om1) : (hoSg ν).γ = max 0 (hlGt (1 + ν)) := hoGSh_γ hν (hoSg_sh hν)

theorem hoSg_ext {ν' ν : Ordinal.{0}} (hν : ν < Om1) (h : ν' ≤ ν) {c : Ordinal.{0}} (hc : c < (hoSg ν').B)
    (x : Ordinal.{0}) : (hoSg ν).R c x = (hoSg ν').R c x ∧ (hoSg ν).g c = (hoSg ν').g c := by
  rcases h.lt_or_eq with h | rfl
  · exact (hoSg_inv ν hν).2 ν' h c x hc
  · exact ⟨rfl, rfl⟩

/-- **SMALL**: a code of `hoSg ν` with gate below an `ε`-number `σ` lies in some `hoSg ν'`, `ν' < σ`. -/
theorem hoSg_small : ∀ ν, ν < Om1 → ∀ c, c < (hoSg ν).B → ∀ σ, InE σ → σ < Om1 → (hoSg ν).g c < σ →
    ∃ ν', ν' < σ ∧ c < (hoSg ν').B := by
  intro ν
  induction ν using WellFoundedLT.induction with
  | ind ν IH =>
  intro hν c hc σ hσ hσ1 hg
  by_cases hνσ : ν < σ
  · exact ⟨ν, hνσ, hc⟩
  rcases zero_or_succ_or_isSuccLimit ν with h0 | ⟨μ, hμ⟩ | hlim
  · exact absurd (by rw [h0]; exact hσ.pos) hνσ
  · have hμ' : ν = μ + 1 := by rw [← hμ, succ_eq_add_one]
    subst hμ'
    have hμ1 : μ < Om1 := (lt_add_one μ).trans hν
    by_cases hcμ : c < (hoSg μ).B
    · rw [(hoSg_ext hν (lt_add_one μ).le hcμ 0).2] at hg
      exact IH μ (lt_add_one μ) hμ1 c hcμ σ hσ hσ1 hg
    · exfalso
      have hsh := hoSg_sh hμ1
      have e : hoSg (μ + 1) = hoGU le_self_add (hl_one_add hμ1) (hoKp μ) (hoKp_inv μ hμ1).1.1
          (hoKp_inv μ hμ1).1.2.1 (hoKp_inv μ hμ1).1.2.2 (hoSg μ) hsh.1 hsh.2 := by
        rw [hoSg_succ]; unfold hoGSucc; rw [dif_pos hμ1, dif_pos hsh]
      rw [e] at hc hg
      have h := hoGU_high le_self_add (hl_one_add hμ1) (hoKp μ) (hoKp_inv μ hμ1).1.1 (hoKp_inv μ hμ1).1.2.1
        (hoKp_inv μ hμ1).1.2.2 (hoSg μ) hsh.1 hsh.2 (not_lt.1 hcμ) hc hσ hσ1 hg
      have h1 : 1 + μ < σ := hl_gt_E hσ h
      exact hνσ ((ev_isSuccLimit_of_inE hσ).add_one_lt (le_add_self.trans_lt h1))
  · have hcS : c < veblen (Om1 * Om1 * (1 + ν)) (gcG 0 + 1) := by rw [← hoSg_B hν]; exact hc
    rw [hoSg_limit hlim] at hc hg
    have hcoh : HoGCoh ν (fun ν' _ => hoSg ν') :=
      ⟨fun ν' _ hν' => hoSg_sh hν', fun _ _ _ h₂ h12 => (hoSg_inv _ (h₂.trans hν)).2 _ h12⟩
    unfold hoGLimF at hc hg
    rw [dif_pos ⟨hν, hcoh⟩] at hc hg
    obtain ⟨k, hk⟩ := (hoGCh ν hlim hν (fun ν' _ => hoSg ν') hcoh).B_cof c hc
    rw [(hoGCh ν hlim hν (fun ν' _ => hoSg ν') hcoh).U_g (k := k) hk] at hg
    have hkl := heFs_lt hlim (hl_om hν) k
    exact IH _ hkl (hkl.trans hν) c hk σ hσ hσ1 hg

end Googology.Trans.PoR.InaccPsi.R2.Ho
