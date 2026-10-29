import Googology.Trans.PoR.InaccPsi.R2.HlRec

/-!
# HlG: OVER `G`, ONE RECURSION OF SYSTEMS AT `φ(Ω₁·(1+μ), G+1)`, `μ < Ω₁`

PORT of `Hk.HkG` with the range `μ < Ω₁` and gated levels: `hlkGS μ` has base gate `(hlkPk μ).g ≤ 1+μ` (was `0`);
the chain `hlkGCh` at a limit `λ` has the growing gates of `Hg.HgfCh` with union gate `hlGt (1+λ)`.

What differs from the source: the level datum is a GATED one (`Hl.HlLv`: Lemma EXACT for the reading `ℓ` only at
base pairs `(σ, ρ)` above the level gate `g`, the hull membership of `L` only at `0 < a`, `g < b`, the code gate
`g < Z` only when a code over `Z` exists at the level); every pseudo-base and base carries `g ≤` its reading gate
(fields `lg`), and the code-gate fields take the extra hypothesis `g < Z`.  Proofs are otherwise those of the source;
names: prefix `hl`/`Hl` in place of `hj`/`Hj`.

No new axiom.  New definitions: `HlkGCoh`, `hlkGCh`, `hlkGLimF`, `hlkGS`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hl

open Googology.Trans.PoR.InaccPsi.R2.Hk

open Googology.Trans.PoR.InaccPsi.R2.Hj Googology.Trans.PoR.InaccPsi.R2.Hi Googology.Trans.PoR.InaccPsi.R2.Hg
open Googology.Trans.PoR.InaccPsi.R2.Hf Googology.Trans.PoR.InaccPsi.R2.Hd Googology.Trans.PoR.InaccPsi.R2.He
open Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Hb
open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

/-! ## The levels `Ω₁·M` and `x·M` below `G` and `Γ_{x+1}` -/

theorem hlkG_LG {M : Ordinal.{0}} (hM : M < Om1) (α : Ordinal.{0}) : (Om1 : Ordinal.{0}) * M < gcG α :=
  InE.mul_lt (Low.opow_eq_self_of_SC (gcG_SC α)) (hg_Om1_lt_G α) (hM.trans (hg_Om1_lt_G α))

theorem hlkG_fixG {M : Ordinal.{0}} (hM : M < Om1) : veblen (Om1 * M) (gcG 0) = gcG 0 :=
  gn_veb_fix (gcG_SC 0) (hlkG_LG hM 0)

theorem hlkG_B_eq {M : Ordinal.{0}} (hM : M < Om1) :
    veblen (Om1 * M) (gcG 0 + 1) = hdNx (Om1 * M) (gcG 0) :=
  (hdNx_fixP (hlkG_fixG hM)).symm

section Base

variable {M x : Ordinal.{0}} (h1 : 1 ≤ M) (hMx : M < x) (hx : InE x) (hx1 : x < Om1)
include h1 hMx hx hx1

theorem hlkG_x1 : (1 : Ordinal.{0}) ≤ x * M :=
  (one_lt_omega0.trans (omega0_lt_inE hx)).le.trans (le_mul_of_one_le_right' h1)

theorem hlkG_xlt : x * M < lgG x :=
  InE.mul_lt (lgG_facts hx hx1).2.2.2.1 (lgG_facts hx hx1).2.1 (hMx.trans (lgG_facts hx hx1).2.1)

theorem hlkG_fixx : veblen (x * M) (lgG x) = lgG x :=
  hjG_fix hx hx1 (hlkG_x1 h1 hMx hx hx1) (hlkG_xlt h1 hMx hx hx1)

theorem hlkG_b_eq : veblen (x * M) (lgG x + 1) = hdNx (x * M) (lgG x) :=
  (hdNx_fixP (hlkG_fixx h1 hMx hx hx1)).symm

end Base

theorem hlk_fs_mono {l : Ordinal.{0}} (hl : IsSuccLimit l) (hle : l < Om1) (k : ℕ) :
    1 + heFs l k < 1 + heFs l (k + 1) := (add_lt_add_iff_left 1).2 (heFs_mono hl (hl_om hle) k)

theorem hlk_fs_lt {l : Ordinal.{0}} (hl : IsSuccLimit l) (hle : l < Om1) (k : ℕ) : 1 + heFs l k < 1 + l :=
  (add_lt_add_iff_left 1).2 (heFs_lt hl (hl_om hle) k)

theorem hlk_fs_cof {l : Ordinal.{0}} (hl : IsSuccLimit l) (hle : l < Om1) (t : Ordinal.{0}) (ht : t < 1 + l) :
    ∃ k, t < 1 + heFs l k := by
  rw [one_add_of_omega0_le (omega0_le_of_isSuccLimit hl)] at ht
  obtain ⟨k, hk⟩ := heFs_cof hl (hl_om hle) t ht
  exact ⟨k, hk.trans_le le_add_self⟩

/-- **The outer low field of `G` below the reading gate does not depend on the level datum.** -/
theorem hlGW_Zo_low (Λ : HlLv) {x : Ordinal.{0}} (h : ¬ Λ.g < x) :
    (hlGW Λ).hlwZo x = veblen (max ω x * max ω x) (lgG x + 1) := (hlGW Λ).hlwZo_low h

/-! ## The limit case -/

/-- **The condition at a limit**: the earlier systems are starts over `G` at their packages with base gate the gate
of the package, and later ones extend earlier ones. -/
def HlkGCoh (l : Ordinal.{0}) (IH : ∀ μ, μ < l → HgVD) : Prop :=
  (∀ μ (h : μ < l), HlWShape (hlGW (hlkPk μ).Λ) 0 (IH μ h) ∧ (IH μ h).γ = (hlkPk μ).Λ.g) ∧
    ∀ μ' μ (h' : μ' < l) (h : μ < l), μ' < μ → ∀ c x, c < (IH μ' h').B →
      (IH μ h).R c x = (IH μ' h').R c x ∧ (IH μ h).g c = (IH μ' h').g c

section Lim

variable (l : Ordinal.{0}) (hl : IsSuccLimit l) (hle : l < Om1) (IH : ∀ μ, μ < l → HgVD) (H : HlkGCoh l IH)

include hl hle in
theorem hlkGCoh_g (k : ℕ) : (hlkPk (heFs l k)).Λ.g ≤ hlGt (1 + l) :=
  (hlkPk_g ((heFs_lt hl (hl_om hle) k).trans hle)).trans (hlGt_mono (hlk_fs_lt hl hle k).le)

include H in
theorem hlkGCoh_B (k : ℕ) :
    (IH (heFs l k) (heFs_lt hl (hl_om hle) k)).B = veblen (Om1 * (1 + heFs l k)) (gcG 0 + 1) := by
  have h := (H.1 _ (heFs_lt hl (hl_om hle) k)).1.1
  rw [h]
  show veblen ((hlkPk (heFs l k)).Λ.L + 0) (gcG 0 + 1) = _
  rw [hlkPk_L ((heFs_lt hl (hl_om hle) k).trans hle), add_zero]

include H in
theorem hlkGCoh_b (k : ℕ) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγ : hlGt (1 + l) < x) :
    (IH (heFs l k) (heFs_lt hl (hl_om hle) k)).b x = veblen (x * (1 + heFs l k)) (lgG x + 1) := by
  have hg' := (hlkGCoh_g l hl hle k).trans_lt hγ
  have h := (H.1 _ (heFs_lt hl (hl_om hle) k)).1.2.2.1 x hx hx1 (max_lt hg' hx.pos)
  rw [h]
  show veblen ((hlkPk (heFs l k)).Λ.l x + 0) (lgG x + 1) = _
  rw [hlkPk_l ((heFs_lt hl (hl_om hle) k).trans hle) hg', add_zero]

/-- **THE GATED `ω`-CHAIN OF THE SYSTEMS `hlkGS (heFs λ k)` OVER `G`, WITH GROWING GATES**: union bound
`φ(Ω₁·(1+λ), G+1)`, union base reading `φ(x·(1+λ), Γ_{x+1}+1)`, union base gate `hlGt (1+λ)`. -/
noncomputable def hlkGCh : HgfCh where
  D := fun k => IH (heFs l k) (heFs_lt hl (hl_om hle) k)
  B := veblen (Om1 * (1 + l)) (gcG 0 + 1)
  b := fun x => veblen (x * (1 + l)) (lgG x + 1)
  γ := hlGt (1 + l)
  Zo := (hlGW (hlMLv (1 + l) le_self_add (hl_one_add hle))).hlwZo
  γ_lt := (hlGt_le _).trans_lt (hl_one_add hle)
  γ0 := fun k => by rw [(H.1 _ _).2]; exact hlkGCoh_g l hl hle k
  γ_cl := fun Z hZ hZ1 h => by
    have ha : (1 : Ordinal.{0}) ≤ Om1 * (1 + l) := (hkG_one le_self_add).le
    have hG : gcG 0 < veblen (Om1 * (1 + l)) (gcG 0 + 1) := (lt_add_one _).trans_le (right_le_veblen _ _)
    have hc := hi_cl_lvl ha hZ1 (hd_succ_lt (hkG_ne le_self_add) _) hG h le_rfl
      ((isNormal_veblen _).strictMono (lt_add_one _))
    have h2 : (Om1 : Ordinal.{0}) * (1 + l) < Om 1 * Om 1 := by
      rw [Br.Om1_eq]; exact mul_lt_mul_of_pos_left (hl_om (hl_one_add hle)) gw_Om_pos
    exact (hlGt_le _).trans_lt (hl_mul_cl hZ hZ1 hc le_rfl h2)
  B_mono := fun k => by
    rw [hlkGCoh_B l hl hle IH H, hlkGCoh_B l hl hle IH H]
    exact (hd_veb_left_lt (mul_lt_mul_of_pos_left (hlk_fs_mono hl hle k) gv_Om1_pos) _).le
  B_lt := fun k => by
    rw [hlkGCoh_B l hl hle IH H]
    exact hd_veb_left_lt (mul_lt_mul_of_pos_left (hlk_fs_lt hl hle k) gv_Om1_pos) _
  B_cof := fun c hc => by
    obtain ⟨b, hb, hcb⟩ := hgVeb_cof (hkG_ne le_self_add) (hlkG_fixG (hl_one_add hle)) hc
    obtain ⟨k, hk⟩ := hk_mul_cof1 gv_Om1_pos (hlk_fs_mono hl hle) (hlk_fs_cof hl hle) hb
    refine ⟨k, ?_⟩
    rw [hlkGCoh_B l hl hle IH H, hlkG_B_eq (hl_one_add ((heFs_lt hl (hl_om hle) k).trans hle))]
    exact hcb.trans (hdN_lt_Nx hk)
  R_ext := fun k c x hc => (H.2 _ _ _ _ (heFs_mono hl (hl_om hle) k) c x hc).1
  g_ext := fun k c hc => (H.2 _ _ _ _ (heFs_mono hl (hl_om hle) k) c 0 hc).2
  B_lt1 := by
    have hG1 := gcG_SC 1
    have hE := Low.opow_eq_self_of_SC hG1
    have hfix : veblen (Om1 * (1 + l)) (gcG 1) = gcG 1 := gn_veb_fix hG1 (hlkG_LG (hl_one_add hle) 1)
    have h2 := (isNormal_veblen (Om1 * (1 + l))).strictMono
      ((ev_isSuccLimit_of_inE hE).add_one_lt (gcG_lt zero_lt_one))
    rwa [hfix] at h2
  B_fix := veblen_veblen_of_lt (hkG_one le_self_add) _
  B_mem := fun S a b ha hb =>
    CSet.phi_mem ((hlMLv (1 + l) le_self_add (hl_one_add hle)).L_mem S a b ha hb) (CSet.succ_mem (gmS_G0_mem S ha))
  b_ge := fun k x hx hx1 hγ => by
    rw [hlkGCoh_b l hl hle IH H k hx hx1 hγ]
    exact (hd_veb_left_lt (mul_lt_mul_of_pos_left (hlk_fs_lt hl hle k) hx.pos) _).le
  b_cof := fun x hx hx1 hγ ν hν => by
    obtain ⟨b, hb, hνb⟩ := hgVeb_cof (mul_pos hx.pos (zero_lt_one.trans_le le_self_add)).ne'
      (hlkG_fixx le_self_add (hl_gt_E hx hγ) hx hx1) hν
    obtain ⟨k, hk⟩ := hk_mul_cof1 hx.pos (hlk_fs_mono hl hle) (hlk_fs_cof hl hle) hb
    refine ⟨k, ?_⟩
    rw [hlkGCoh_b l hl hle IH H k hx hx1 hγ,
      hlkG_b_eq le_self_add ((hlk_fs_lt hl hle k).trans (hl_gt_E hx hγ)) hx hx1]
    exact hνb.trans (hdN_lt_Nx hk)
  b_fix := fun x hx hx1 _ => veblen_veblen_of_lt ((one_lt_omega0.trans (omega0_lt_inE hx)).trans_le
    (le_mul_of_one_le_right' le_self_add)) _
  b_gt := fun x hx hx1 _ => (lgG_facts hx hx1).2.1.trans ((lt_add_one _).trans_le (right_le_veblen _ _))
  b_lt := fun x hx hx1 hγ => by
    rw [hlkG_b_eq le_self_add (hl_gt_E hx hγ) hx hx1]
    exact hjG_lt1 hx hx1 (hlkG_x1 le_self_add (hl_gt_E hx hγ) hx hx1)
      (hlkG_xlt le_self_add (hl_gt_E hx hγ) hx hx1)
  b_pi := fun σ ρ hB hγ => by
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
    have hlσ : 1 + l < σ := hl_gt_E hB.1 hγ
    have hlρ : 1 + l < ρ := hlσ.trans hB.2.2.1
    have hp := (hlMLv (1 + l) le_self_add (hl_one_add hle)).l_pi σ ρ hB hγ
    rw [show (hlMLv (1 + l) le_self_add (hl_one_add hle)).l ρ = ρ * (1 + l) from
        hlMLv_l _ _ _ (hγ.trans hB.2.2.1),
      show (hlMLv (1 + l) le_self_add (hl_one_add hle)).l σ = σ * (1 + l) from hlMLv_l _ _ _ hγ] at hp
    rw [hlkG_b_eq le_self_add hlρ hB.2.1 hρ1, hlkG_b_eq le_self_add hlσ hB.1 hσ1]
    exact hjG_S_pi hB hp
      (hlkG_x1 le_self_add hlρ hB.2.1 hρ1) (hlkG_xlt le_self_add hlρ hB.2.1 hρ1)
      (hlkG_x1 le_self_add hlσ hB.1 hσ1) (hlkG_xlt le_self_add hlσ hB.1 hσ1)
  Z_low := fun k x hx hx1 h => by
    have hkl := heFs_lt hl (hl_om hle) k
    have hP : veblen 2 (veblen (max ω x * max ω x) (lgG x + 1)) = veblen (max ω x * max ω x) (lgG x + 1) :=
      (hlGW (hlkPk (heFs l k)).Λ).Zo_fix x
    show (IH (heFs l k) hkl).Z x ≤ (hlGW (hlMLv (1 + l) le_self_add (hl_one_add hle))).hlwZo x
    rw [(H.1 _ _).1.2.2.2.1 x hx hx1, hlGW_Zo_low (hlMLv (1 + l) le_self_add (hl_one_add hle)) h]
    split_ifs with h'
    · refine (hb_evZ_lt_fix2 hP ?_).le
      show veblen ((hlkPk (heFs l k)).Λ.l x + 0) (lgG x + 1) < _
      rw [add_zero, max_eq_right (omega0_lt_inE hx).le]
      exact hd_veb_left_lt (le_self_add.trans_lt
        ((hlkPk (heFs l k)).Λ.l_lt2 x hx hx1 (max_lt_iff.1 h').1)) _
    · rw [hlGW_Zo_low _ (fun h'' => h' (max_lt h'' hx.pos))]
  Zo_fix := fun x => hc_fix_down one_le_two ((hlGW (hlMLv (1 + l) le_self_add (hl_one_add hle))).hlwZo_fix x)
  Zo_G1 := fun x hx hx1 => (hlGW (hlMLv (1 + l) le_self_add (hl_one_add hle))).hlwZo_G1 x hx hx1

/-- **The union of the chain is a start over `G` at the package `hlkPk λ`.** -/
theorem hlkGCh_shape : HlWShape (hlGW (hlkPk l).Λ) 0 (hlkGCh l hl hle IH H).U := by
  rw [hlkPk_lim_Λ hl hle]
  refine ⟨by show veblen (Om1 * (1 + l)) (gcG 0 + 1) = veblen (Om1 * (1 + l) + 0) (gcG 0 + 1); rw [add_zero],
    fun x _ _ => ?_, fun x _ _ hg => ?_, fun x hx _ => ?_, fun _ σ _ _ hσ _ _ => hσ.pos⟩
  · show hlGt (1 + l) < x ↔ max (hlGt (1 + l)) 0 < x
    rw [max_eq_left zero_le]
  · show veblen (x * (1 + l)) (lgG x + 1) = veblen ((hlMLv (1 + l) le_self_add (hl_one_add hle)).l x + 0) (lgG x + 1)
    rw [hlMLv_l _ _ _ (max_lt_iff.1 hg).1, add_zero]
  · show (if hlGt (1 + l) < x then evZ (veblen (x * (1 + l)) (lgG x + 1))
        else (hlGW (hlMLv (1 + l) le_self_add (hl_one_add hle))).hlwZo x) =
      if max (hlGt (1 + l)) 0 < x then
        evZ (veblen ((hlMLv (1 + l) le_self_add (hl_one_add hle)).l x + 0) (lgG x + 1))
        else (hlGW (hlMLv (1 + l) le_self_add (hl_one_add hle))).hlwZo x
    rw [max_eq_left zero_le, add_zero]
    split_ifs with h
    · rw [hlMLv_l _ _ _ h]
    · rfl

end Lim

open Classical in
/-- **The limit case**: the union of the chain (when `λ < Γ₀` and the condition holds). -/
noncomputable def hlkGLimF (l : Ordinal.{0}) (hl : IsSuccLimit l) (IH : ∀ μ, μ < l → HgVD) : HgVD :=
  if h : l < Om1 ∧ HlkGCoh l IH then (hlkGCh l hl h.1 IH h.2).U else hgU

open Classical in
/-- **The successor case**: the union of all levels `Ω₁·(1+μ) + κ` over `G`, started at the given system. -/
noncomputable def hlkGSucc (μ : Ordinal.{0}) (S : HgVD) : HgVD :=
  if h : HlWShape (hlGW (hlkPk μ).Λ) 0 S then hlwU (hlGW (hlkPk μ).Λ) (hlkPk μ).St0 (hlkPk μ).h0 S h else S

/-- **THE SYSTEMS OVER `G` AT `φ(Ω₁·(1+μ), G+1)`, BY ONE RECURSION ON `μ`** (gated level data). -/
noncomputable def hlkGS (μ : Ordinal.{0}) : HgVD :=
  Ordinal.limitRecOn (motive := fun _ => HgVD) μ hgU hlkGSucc hlkGLimF

theorem hlkGS_zero : hlkGS 0 = hgU := by unfold hlkGS; rw [Ordinal.limitRecOn_zero]

theorem hlkGS_succ (μ : Ordinal.{0}) : hlkGS (μ + 1) = hlkGSucc μ (hlkGS μ) := by
  unfold hlkGS; rw [Ordinal.limitRecOn_add_one]

theorem hlkGS_limit {l : Ordinal.{0}} (hl : IsSuccLimit l) : hlkGS l = hlkGLimF l hl (fun μ _ => hlkGS μ) := by
  unfold hlkGS; rw [Ordinal.limitRecOn_limit _ _ _ _ hl]

theorem hlkGS_Bsh {μ : Ordinal.{0}} (hμ : μ < Om1) {S0 : HgVD} (h : HlWShape (hlGW (hlkPk μ).Λ) 0 S0) :
    S0.B = veblen (Om1 * (1 + μ)) (gcG 0 + 1) := by
  rw [h.1]; show veblen ((hlkPk μ).Λ.L + 0) (gcG 0 + 1) = _; rw [hlkPk_L hμ, add_zero]

/-- **THE INVARIANT**: every `hlkGS μ`, `μ < Γ₀`, is a start over `G` at `hlkPk μ` with base gate the gate of
`hlkPk μ`, and extends every `hlkGS μ'`, `μ' < μ`. -/
theorem hlkGS_inv : ∀ μ, μ < Om1 → (HlWShape (hlGW (hlkPk μ).Λ) 0 (hlkGS μ) ∧
    (hlkGS μ).γ = (hlkPk μ).Λ.g) ∧
    ∀ μ', μ' < μ → ∀ c x, c < (hlkGS μ').B → (hlkGS μ).R c x = (hlkGS μ').R c x ∧
      (hlkGS μ).g c = (hlkGS μ').g c := by
  intro μ
  induction μ using WellFoundedLT.induction with
  | ind μ IH =>
  intro hμ
  rcases zero_or_succ_or_isSuccLimit μ with h0 | ⟨ν, hν⟩ | hlim
  · subst h0
    rw [hlkGS_zero, hlkPk_zero]
    exact ⟨⟨hlgU_shape, rfl⟩, fun μ' h => absurd h (not_lt.2 zero_le)⟩
  · have hν' : μ = ν + 1 := by rw [← hν, succ_eq_add_one]
    subst hν'
    have hνε : ν < Om1 := (lt_add_one ν).trans hμ
    obtain ⟨⟨hsh, hγ⟩, hext⟩ := IH ν (lt_add_one ν) hνε
    have e : hlkGS (ν + 1) = hlwU (hlGW (hlkPk ν).Λ) (hlkPk ν).St0 (hlkPk ν).h0 (hlkGS ν) hsh := by
      rw [hlkGS_succ]; unfold hlkGSucc; rw [dif_pos hsh]
    refine ⟨⟨?_, by rw [e, hlkPk_succ]; rfl⟩, fun μ' hμ' c x hc => ?_⟩
    · rw [e, hlkPk_succ]
      exact hlGU_shape (hlkPk ν).Λ (hlkPk ν).St0 (hlkPk ν).h0 _ hsh
    · rw [e]
      rcases (Order.lt_add_one_iff.1 hμ').lt_or_eq with hlt | heq
      · obtain ⟨⟨hsh', -⟩, -⟩ := IH μ' (hlt.trans (lt_add_one ν)) (hlt.trans hνε)
        have hc0 : c < (hlkGS ν).B := by
          rw [hlkGS_Bsh hνε hsh]; rw [hlkGS_Bsh (hlt.trans hνε) hsh'] at hc
          exact hc.trans (hd_veb_left_lt (mul_lt_mul_of_pos_left ((add_lt_add_iff_left 1).2 hlt) gv_Om1_pos) _)
        obtain ⟨r1, g1⟩ := hext μ' hlt c x hc
        exact ⟨(hlwU_R0 (hlGW (hlkPk ν).Λ) (hlkPk ν).St0 (hlkPk ν).h0 _ hsh hc0 x).trans r1,
          (hlwU_g0 (hlGW (hlkPk ν).Λ) (hlkPk ν).St0 (hlkPk ν).h0 _ hsh hc0).trans g1⟩
      · subst heq
        exact ⟨hlwU_R0 (hlGW (hlkPk μ').Λ) (hlkPk μ').St0 (hlkPk μ').h0 _ hsh hc x,
          hlwU_g0 (hlGW (hlkPk μ').Λ) (hlkPk μ').St0 (hlkPk μ').h0 _ hsh hc⟩
  · have hcoh : HlkGCoh μ (fun μ' _ => hlkGS μ') :=
      ⟨fun μ' h => (IH μ' h (h.trans hμ)).1, fun μ₁ μ₂ h₁ h₂ h12 => (IH μ₂ h₂ (h₂.trans hμ)).2 μ₁ h12⟩
    have e : hlkGS μ = (hlkGCh μ hlim hμ (fun μ' _ => hlkGS μ') hcoh).U := by
      rw [hlkGS_limit hlim]; unfold hlkGLimF; rw [dif_pos ⟨hμ, hcoh⟩]
    refine ⟨⟨by rw [e]; exact hlkGCh_shape μ hlim hμ _ hcoh, by rw [e, hlkPk_lim_Λ hlim hμ]; rfl⟩,
      fun μ' hμ' c x hc => ?_⟩
    rw [e]
    obtain ⟨k, hk⟩ := heFs_cof hlim (hl_om hμ) μ' hμ'
    have hkl := heFs_lt hlim (hl_om hμ) k
    obtain ⟨⟨hsh', -⟩, -⟩ := IH μ' hμ' (hμ'.trans hμ)
    obtain ⟨-, hextk⟩ := IH _ hkl (hkl.trans hμ)
    have hc' : c < (hlkGS (heFs μ k)).B := by
      rw [hlkGCoh_B μ hlim hμ _ hcoh k]; rw [hlkGS_Bsh (hμ'.trans hμ) hsh'] at hc
      exact hc.trans (hd_veb_left_lt (mul_lt_mul_of_pos_left ((add_lt_add_iff_left 1).2 hk) gv_Om1_pos) _)
    obtain ⟨r2, g2⟩ := hextk μ' hk c x hc
    exact ⟨((hlkGCh μ hlim hμ (fun μ' _ => hlkGS μ') hcoh).U_R (k := k) hc' x).trans r2,
      ((hlkGCh μ hlim hμ (fun μ' _ => hlkGS μ') hcoh).U_g (k := k) hc').trans g2⟩

theorem hlkGS_shape {μ : Ordinal.{0}} (hμ : μ < Om1) : HlWShape (hlGW (hlkPk μ).Λ) 0 (hlkGS μ) :=
  (hlkGS_inv μ hμ).1.1

theorem hlkGS_γ {μ : Ordinal.{0}} (hμ : μ < Om1) : (hlkGS μ).γ = (hlkPk μ).Λ.g := (hlkGS_inv μ hμ).1.2

/-- **The base gate of `hlkGS μ` is at most `1 + μ`.** -/
theorem hlkGS_γ_le {μ : Ordinal.{0}} (hμ : μ < Om1) : (hlkGS μ).γ ≤ 1 + μ := by
  rw [hlkGS_γ hμ]; exact (hlkPk_g hμ).trans (hlGt_le _)

/-- **The bound of `hlkGS μ` is `φ(Ω₁·(1+μ), G+1)`.** -/
theorem hlkGS_B {μ : Ordinal.{0}} (hμ : μ < Om1) : (hlkGS μ).B = veblen (Om1 * (1 + μ)) (gcG 0 + 1) :=
  hlkGS_Bsh hμ (hlkGS_shape hμ)

theorem hlkGS_ext {μ' μ : Ordinal.{0}} (hμ : μ < Om1) (h : μ' < μ) {c : Ordinal.{0}} (hc : c < (hlkGS μ').B)
    (x : Ordinal.{0}) : (hlkGS μ).R c x = (hlkGS μ').R c x ∧ (hlkGS μ).g c = (hlkGS μ').g c :=
  (hlkGS_inv μ hμ).2 μ' h c x hc

end Googology.Trans.PoR.InaccPsi.R2.Hl
