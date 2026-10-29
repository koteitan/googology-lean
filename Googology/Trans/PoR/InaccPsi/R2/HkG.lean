import Googology.Trans.PoR.InaccPsi.R2.HkRec

/-!
# HkG: OVER `G`, ONE RECURSION OF SYSTEMS AT `φ(Ω₁·(1+μ), G+1)`, `μ < ε₀`

`hkGS μ` is a start over `G` at the package `Hk.hkPk μ` (the shape `Hj.HjWShape (hjGW (hkPk μ).Λ) 0`): at `0` the
system `Hg.hgU` (bound `φ(Ω₁, G+1)`), at `μ + 1` the union `Hj.hjwU` of all levels `Ω₁·(1+μ) + κ` over `G`
started at `hkGS μ` (bound `φ(Ω₁·(1+μ+1), G+1)`), at a limit `λ < ε₀` the union of the gated `ω`-chain of the systems
`hkGS (heFs λ k)` (`hkGCh`; the port of `Hj.hjGWCh` with `x·ω` replaced by `x·(1+λ)`).  `hkGS_inv`: every
`hkGS μ`, `μ < ε₀`, has the shape, base gate `0`, and extends every `hkGS μ'`, `μ' < μ`.

* `hkG_LG`, `hkG_fixG`, `hkG_fixx`, `HkGCoh`, `hkGCh`, `hkGCh_shape`, `hkGLimF`, `hkGS` (**THE SYSTEMS OVER `G`**),
  `hkGS_inv` (**THE INVARIANT**), `hkGS_B`, `hkGS_γ`, `hkGS_ext`.

No new axiom.  New definitions: `HkGCoh`, `hkGCh`, `hkGLimF`, `hkGS`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hk

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

theorem hkG_LG {M : Ordinal.{0}} (hM : M < ε₀) (α : Ordinal.{0}) : (Om1 : Ordinal.{0}) * M < gcG α :=
  InE.mul_lt (Low.opow_eq_self_of_SC (gcG_SC α)) (hg_Om1_lt_G α) (hk_lt_E hM (Low.opow_eq_self_of_SC (gcG_SC α)))

theorem hkG_fixG {M : Ordinal.{0}} (hM : M < ε₀) : veblen (Om1 * M) (gcG 0) = gcG 0 :=
  gn_veb_fix (gcG_SC 0) (hkG_LG hM 0)

theorem hkG_one {M : Ordinal.{0}} (h1 : 1 ≤ M) : (1 : Ordinal.{0}) < Om1 * M :=
  hg_one_lt_Om1.trans_le (le_mul_of_one_le_right' h1)

theorem hkG_ne {M : Ordinal.{0}} (h1 : 1 ≤ M) : (Om1 : Ordinal.{0}) * M ≠ 0 := (zero_lt_one.trans (hkG_one h1)).ne'

theorem hkG_B_eq {M : Ordinal.{0}} (hM : M < ε₀) : veblen (Om1 * M) (gcG 0 + 1) = hdNx (Om1 * M) (gcG 0) :=
  (hdNx_fixP (hkG_fixG hM)).symm

section Base

variable {M x : Ordinal.{0}} (h1 : 1 ≤ M) (hM : M < ε₀) (hx : InE x) (hx1 : x < Om1)
include h1 hM hx hx1

theorem hkG_x1 : (1 : Ordinal.{0}) ≤ x * M :=
  (one_lt_omega0.trans (omega0_lt_inE hx)).le.trans (le_mul_of_one_le_right' h1)

theorem hkG_xlt : x * M < lgG x := (hkLv M h1 hM).l_lt x hx hx1

theorem hkG_fixx : veblen (x * M) (lgG x) = lgG x := hjG_fix hx hx1 (hkG_x1 h1 hM hx hx1) (hkG_xlt h1 hM hx hx1)

theorem hkG_b_eq : veblen (x * M) (lgG x + 1) = hdNx (x * M) (lgG x) := (hdNx_fixP (hkG_fixx h1 hM hx hx1)).symm

end Base

theorem hk_fs_mono {l : Ordinal.{0}} (hl : IsSuccLimit l) (hle : l < ε₀) (k : ℕ) :
    1 + heFs l k < 1 + heFs l (k + 1) := (add_lt_add_iff_left 1).2 (heFs_mono hl (hk_om hle) k)

theorem hk_fs_lt {l : Ordinal.{0}} (hl : IsSuccLimit l) (hle : l < ε₀) (k : ℕ) : 1 + heFs l k < 1 + l :=
  (add_lt_add_iff_left 1).2 (heFs_lt hl (hk_om hle) k)

theorem hk_fs_cof {l : Ordinal.{0}} (hl : IsSuccLimit l) (hle : l < ε₀) (t : Ordinal.{0}) (ht : t < 1 + l) :
    ∃ k, t < 1 + heFs l k := by
  rw [one_add_of_omega0_le (omega0_le_of_isSuccLimit hl)] at ht
  obtain ⟨k, hk⟩ := heFs_cof hl (hk_om hle) t ht
  exact ⟨k, hk.trans_le le_add_self⟩

/-! ## The limit case -/

/-- **The condition at a limit**: the earlier systems are starts over `G` at their packages with base gate `0`, and
later ones extend earlier ones. -/
def HkGCoh (l : Ordinal.{0}) (IH : ∀ μ, μ < l → HgVD) : Prop :=
  (∀ μ (h : μ < l), HjWShape (hjGW (hkPk μ).Λ) 0 (IH μ h) ∧ (IH μ h).γ = 0) ∧
    ∀ μ' μ (h' : μ' < l) (h : μ < l), μ' < μ → ∀ c x, c < (IH μ' h').B →
      (IH μ h).R c x = (IH μ' h').R c x ∧ (IH μ h).g c = (IH μ' h').g c

section Lim

variable (l : Ordinal.{0}) (hl : IsSuccLimit l) (hle : l < ε₀) (IH : ∀ μ, μ < l → HgVD) (H : HkGCoh l IH)

include H in
theorem hkGCoh_B (k : ℕ) :
    (IH (heFs l k) (heFs_lt hl (hk_om hle) k)).B = veblen (Om1 * (1 + heFs l k)) (gcG 0 + 1) := by
  have h := (H.1 _ (heFs_lt hl (hk_om hle) k)).1.1
  rw [h]
  show veblen ((hkPk (heFs l k)).Λ.L + 0) (gcG 0 + 1) = _
  rw [hkPk_L ((heFs_lt hl (hk_om hle) k).trans hle), add_zero]

include H in
theorem hkGCoh_b (k : ℕ) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    (IH (heFs l k) (heFs_lt hl (hk_om hle) k)).b x = veblen (x * (1 + heFs l k)) (lgG x + 1) := by
  have h := (H.1 _ (heFs_lt hl (hk_om hle) k)).1.2.2.1 x hx hx1 ((max_le le_rfl le_rfl).trans_lt hx.pos)
  rw [h]
  show veblen ((hkPk (heFs l k)).Λ.l x + 0) (lgG x + 1) = _
  rw [hkPk_l ((heFs_lt hl (hk_om hle) k).trans hle), add_zero]

/-- **THE GATED `ω`-CHAIN OF THE SYSTEMS `hkGS (heFs λ k)` OVER `G`**: union bound `φ(Ω₁·(1+λ), G+1)`, union base
reading `φ(x·(1+λ), Γ_{x+1}+1)`. -/
noncomputable def hkGCh : HgfCh where
  D := fun k => IH (heFs l k) (heFs_lt hl (hk_om hle) k)
  B := veblen (Om1 * (1 + l)) (gcG 0 + 1)
  b := fun x => veblen (x * (1 + l)) (lgG x + 1)
  γ := 0
  Zo := (hjGW (hkLv (1 + l) le_self_add (hk_one_add hle))).hjwZo
  γ_lt := gv_Om1_pos
  γ0 := fun k => (H.1 _ _).2.le
  γ_cl := fun _ hZ _ _ => hZ.1
  B_mono := fun k => by
    rw [hkGCoh_B l hl hle IH H, hkGCoh_B l hl hle IH H]
    exact (hd_veb_left_lt (mul_lt_mul_of_pos_left (hk_fs_mono hl hle k) gv_Om1_pos) _).le
  B_lt := fun k => by
    rw [hkGCoh_B l hl hle IH H]
    exact hd_veb_left_lt (mul_lt_mul_of_pos_left (hk_fs_lt hl hle k) gv_Om1_pos) _
  B_cof := fun c hc => by
    obtain ⟨b, hb, hcb⟩ := hgVeb_cof (hkG_ne le_self_add) (hkG_fixG (hk_one_add hle)) hc
    obtain ⟨k, hk⟩ := hk_mul_cof1 gv_Om1_pos (hk_fs_mono hl hle) (hk_fs_cof hl hle) hb
    refine ⟨k, ?_⟩
    rw [hkGCoh_B l hl hle IH H, hkG_B_eq (hk_one_add ((heFs_lt hl (hk_om hle) k).trans hle))]
    exact hcb.trans (hdN_lt_Nx hk)
  R_ext := fun k c x hc => (H.2 _ _ _ _ (heFs_mono hl (hk_om hle) k) c x hc).1
  g_ext := fun k c hc => (H.2 _ _ _ _ (heFs_mono hl (hk_om hle) k) c 0 hc).2
  B_lt1 := by
    have hG1 := gcG_SC 1
    have hE := Low.opow_eq_self_of_SC hG1
    have hfix : veblen (Om1 * (1 + l)) (gcG 1) = gcG 1 := gn_veb_fix hG1 (hkG_LG (hk_one_add hle) 1)
    have h2 := (isNormal_veblen (Om1 * (1 + l))).strictMono
      ((ev_isSuccLimit_of_inE hE).add_one_lt (gcG_lt zero_lt_one))
    rwa [hfix] at h2
  B_fix := veblen_veblen_of_lt (hkG_one le_self_add) _
  B_mem := fun S a b ha _ =>
    CSet.phi_mem ((hkLv (1 + l) le_self_add (hk_one_add hle)).L_mem S a b) (CSet.succ_mem (gmS_G0_mem S ha))
  b_ge := fun k x hx hx1 _ => by
    rw [hkGCoh_b l hl hle IH H k hx hx1]
    exact (hd_veb_left_lt (mul_lt_mul_of_pos_left (hk_fs_lt hl hle k) hx.pos) _).le
  b_cof := fun x hx hx1 _ ν hν => by
    obtain ⟨b, hb, hνb⟩ := hgVeb_cof (mul_pos hx.pos (zero_lt_one.trans_le le_self_add)).ne'
      (hkG_fixx le_self_add (hk_one_add hle) hx hx1) hν
    obtain ⟨k, hk⟩ := hk_mul_cof1 hx.pos (hk_fs_mono hl hle) (hk_fs_cof hl hle) hb
    refine ⟨k, ?_⟩
    rw [hkGCoh_b l hl hle IH H k hx hx1,
      hkG_b_eq le_self_add (hk_one_add ((heFs_lt hl (hk_om hle) k).trans hle)) hx hx1]
    exact hνb.trans (hdN_lt_Nx hk)
  b_fix := fun x hx hx1 _ => veblen_veblen_of_lt ((one_lt_omega0.trans (omega0_lt_inE hx)).trans_le
    (le_mul_of_one_le_right' le_self_add)) _
  b_gt := fun x hx hx1 _ => (lgG_facts hx hx1).2.1.trans ((lt_add_one _).trans_le (right_le_veblen _ _))
  b_lt := fun x hx hx1 _ => by
    rw [hkG_b_eq le_self_add (hk_one_add hle) hx hx1]
    exact hjG_lt1 hx hx1 (hkG_x1 le_self_add (hk_one_add hle) hx hx1) (hkG_xlt le_self_add (hk_one_add hle) hx hx1)
  b_pi := fun σ ρ hB _ => by
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
    rw [hkG_b_eq le_self_add (hk_one_add hle) hB.2.1 hρ1, hkG_b_eq le_self_add (hk_one_add hle) hB.1 hσ1]
    exact hjG_S_pi hB ((hkLv (1 + l) le_self_add (hk_one_add hle)).l_pi σ ρ hB)
      (hkG_x1 le_self_add (hk_one_add hle) hB.2.1 hρ1) (hkG_xlt le_self_add (hk_one_add hle) hB.2.1 hρ1)
      (hkG_x1 le_self_add (hk_one_add hle) hB.1 hσ1) (hkG_xlt le_self_add (hk_one_add hle) hB.1 hσ1)
  Z_low := fun _ x hx _ h => absurd hx.pos h
  Zo_fix := fun x => hc_fix_down one_le_two ((hjGW (hkLv (1 + l) le_self_add (hk_one_add hle))).hjwZo_fix x)
  Zo_G1 := fun x hx hx1 => (hjGW (hkLv (1 + l) le_self_add (hk_one_add hle))).hjwZo_G1 x hx hx1

/-- **The union of the chain is a start over `G` at the package `hkPk λ`.** -/
theorem hkGCh_shape : HjWShape (hjGW (hkPk l).Λ) 0 (hkGCh l hl hle IH H).U := by
  rw [hkPk_lim_Λ hl hle]
  refine ⟨by show veblen (Om1 * (1 + l)) (gcG 0 + 1) = veblen (Om1 * (1 + l) + 0) (gcG 0 + 1); rw [add_zero],
    fun x _ _ => ?_, fun x _ _ _ => ?_, fun x hx _ => ?_, fun _ σ _ _ hσ _ _ => hσ.pos⟩
  · show (0 : Ordinal.{0}) < x ↔ max 0 0 < x
    rw [max_self]
  · show veblen (x * (1 + l)) (lgG x + 1) = veblen (x * (1 + l) + 0) (lgG x + 1)
    rw [add_zero]
  · show (if (0 : Ordinal.{0}) < x then evZ (veblen (x * (1 + l)) (lgG x + 1))
        else (hjGW (hkLv (1 + l) le_self_add (hk_one_add hle))).hjwZo x) =
      if max 0 0 < x then evZ (veblen (x * (1 + l) + 0) (lgG x + 1))
        else (hjGW (hkLv (1 + l) le_self_add (hk_one_add hle))).hjwZo x
    rw [max_self, add_zero]

end Lim

open Classical in
/-- **The limit case**: the union of the chain (when `λ < ε₀` and the condition holds). -/
noncomputable def hkGLimF (l : Ordinal.{0}) (hl : IsSuccLimit l) (IH : ∀ μ, μ < l → HgVD) : HgVD :=
  if h : l < ε₀ ∧ HkGCoh l IH then (hkGCh l hl h.1 IH h.2).U else hgU

open Classical in
/-- **The successor case**: the union of all levels `Ω₁·(1+μ) + κ` over `G`, started at the given system. -/
noncomputable def hkGSucc (μ : Ordinal.{0}) (S : HgVD) : HgVD :=
  if h : HjWShape (hjGW (hkPk μ).Λ) 0 S then hjwU (hjGW (hkPk μ).Λ) (hkPk μ).St0 (hkPk μ).h0 S h else S

/-- **THE SYSTEMS OVER `G` AT `φ(Ω₁·(1+μ), G+1)`, BY ONE RECURSION ON `μ`.** -/
noncomputable def hkGS (μ : Ordinal.{0}) : HgVD :=
  Ordinal.limitRecOn (motive := fun _ => HgVD) μ hgU hkGSucc hkGLimF

theorem hkGS_zero : hkGS 0 = hgU := by unfold hkGS; rw [Ordinal.limitRecOn_zero]

theorem hkGS_succ (μ : Ordinal.{0}) : hkGS (μ + 1) = hkGSucc μ (hkGS μ) := by
  unfold hkGS; rw [Ordinal.limitRecOn_add_one]

theorem hkGS_limit {l : Ordinal.{0}} (hl : IsSuccLimit l) : hkGS l = hkGLimF l hl (fun μ _ => hkGS μ) := by
  unfold hkGS; rw [Ordinal.limitRecOn_limit _ _ _ _ hl]

theorem hkGS_Bsh {μ : Ordinal.{0}} (hμ : μ < ε₀) {S0 : HgVD} (h : HjWShape (hjGW (hkPk μ).Λ) 0 S0) :
    S0.B = veblen (Om1 * (1 + μ)) (gcG 0 + 1) := by
  rw [h.1]; show veblen ((hkPk μ).Λ.L + 0) (gcG 0 + 1) = _; rw [hkPk_L hμ, add_zero]

/-- **THE INVARIANT**: every `hkGS μ`, `μ < ε₀`, is a start over `G` at `hkPk μ` with base gate `0`, and extends every
`hkGS μ'`, `μ' < μ`. -/
theorem hkGS_inv : ∀ μ, μ < ε₀ → (HjWShape (hjGW (hkPk μ).Λ) 0 (hkGS μ) ∧ (hkGS μ).γ = 0) ∧
    ∀ μ', μ' < μ → ∀ c x, c < (hkGS μ').B → (hkGS μ).R c x = (hkGS μ').R c x ∧ (hkGS μ).g c = (hkGS μ').g c := by
  intro μ
  induction μ using WellFoundedLT.induction with
  | ind μ IH =>
  intro hμ
  rcases zero_or_succ_or_isSuccLimit μ with h0 | ⟨ν, hν⟩ | hlim
  · subst h0
    rw [hkGS_zero, hkPk_zero]
    exact ⟨⟨hgU_shapeJ, rfl⟩, fun μ' h => absurd h (not_lt.2 zero_le)⟩
  · have hν' : μ = ν + 1 := by rw [← hν, succ_eq_add_one]
    subst hν'
    have hνε : ν < ε₀ := (lt_add_one ν).trans hμ
    obtain ⟨⟨hsh, hγ⟩, hext⟩ := IH ν (lt_add_one ν) hνε
    have e : hkGS (ν + 1) = hjwU (hjGW (hkPk ν).Λ) (hkPk ν).St0 (hkPk ν).h0 (hkGS ν) hsh := by
      rw [hkGS_succ]; unfold hkGSucc; rw [dif_pos hsh]
    refine ⟨⟨?_, by rw [e]; rfl⟩, fun μ' hμ' c x hc => ?_⟩
    · rw [e, hkPk_succ]
      exact hjGU_shape (hkPk ν).Λ (hkPk ν).St0 (hkPk ν).h0 _ hsh
    · rw [e]
      rcases (Order.lt_add_one_iff.1 hμ').lt_or_eq with hlt | heq
      · obtain ⟨⟨hsh', -⟩, -⟩ := IH μ' (hlt.trans (lt_add_one ν)) (hlt.trans hνε)
        have hc0 : c < (hkGS ν).B := by
          rw [hkGS_Bsh hνε hsh]; rw [hkGS_Bsh (hlt.trans hνε) hsh'] at hc
          exact hc.trans (hd_veb_left_lt (mul_lt_mul_of_pos_left ((add_lt_add_iff_left 1).2 hlt) gv_Om1_pos) _)
        obtain ⟨r1, g1⟩ := hext μ' hlt c x hc
        exact ⟨(hjwU_R0 (hjGW (hkPk ν).Λ) (hkPk ν).St0 (hkPk ν).h0 _ hsh hc0 x).trans r1,
          (hjwU_g0 (hjGW (hkPk ν).Λ) (hkPk ν).St0 (hkPk ν).h0 _ hsh hc0).trans g1⟩
      · subst heq
        exact ⟨hjwU_R0 (hjGW (hkPk μ').Λ) (hkPk μ').St0 (hkPk μ').h0 _ hsh hc x,
          hjwU_g0 (hjGW (hkPk μ').Λ) (hkPk μ').St0 (hkPk μ').h0 _ hsh hc⟩
  · have hcoh : HkGCoh μ (fun μ' _ => hkGS μ') :=
      ⟨fun μ' h => (IH μ' h (h.trans hμ)).1, fun μ₁ μ₂ h₁ h₂ h12 => (IH μ₂ h₂ (h₂.trans hμ)).2 μ₁ h12⟩
    have e : hkGS μ = (hkGCh μ hlim hμ (fun μ' _ => hkGS μ') hcoh).U := by
      rw [hkGS_limit hlim]; unfold hkGLimF; rw [dif_pos ⟨hμ, hcoh⟩]
    refine ⟨⟨by rw [e]; exact hkGCh_shape μ hlim hμ _ hcoh, by rw [e]; rfl⟩, fun μ' hμ' c x hc => ?_⟩
    rw [e]
    obtain ⟨k, hk⟩ := heFs_cof hlim (hk_om hμ) μ' hμ'
    have hkl := heFs_lt hlim (hk_om hμ) k
    obtain ⟨⟨hsh', -⟩, -⟩ := IH μ' hμ' (hμ'.trans hμ)
    obtain ⟨-, hextk⟩ := IH _ hkl (hkl.trans hμ)
    have hc' : c < (hkGS (heFs μ k)).B := by
      rw [hkGCoh_B μ hlim hμ _ hcoh k]; rw [hkGS_Bsh (hμ'.trans hμ) hsh'] at hc
      exact hc.trans (hd_veb_left_lt (mul_lt_mul_of_pos_left ((add_lt_add_iff_left 1).2 hk) gv_Om1_pos) _)
    obtain ⟨r2, g2⟩ := hextk μ' hk c x hc
    exact ⟨((hkGCh μ hlim hμ (fun μ' _ => hkGS μ') hcoh).U_R (k := k) hc' x).trans r2,
      ((hkGCh μ hlim hμ (fun μ' _ => hkGS μ') hcoh).U_g (k := k) hc').trans g2⟩

theorem hkGS_shape {μ : Ordinal.{0}} (hμ : μ < ε₀) : HjWShape (hjGW (hkPk μ).Λ) 0 (hkGS μ) := (hkGS_inv μ hμ).1.1

theorem hkGS_γ {μ : Ordinal.{0}} (hμ : μ < ε₀) : (hkGS μ).γ = 0 := (hkGS_inv μ hμ).1.2

/-- **The bound of `hkGS μ` is `φ(Ω₁·(1+μ), G+1)`.** -/
theorem hkGS_B {μ : Ordinal.{0}} (hμ : μ < ε₀) : (hkGS μ).B = veblen (Om1 * (1 + μ)) (gcG 0 + 1) :=
  hkGS_Bsh hμ (hkGS_shape hμ)

theorem hkGS_ext {μ' μ : Ordinal.{0}} (hμ : μ < ε₀) (h : μ' < μ) {c : Ordinal.{0}} (hc : c < (hkGS μ').B)
    (x : Ordinal.{0}) : (hkGS μ).R c x = (hkGS μ').R c x ∧ (hkGS μ).g c = (hkGS μ').g c :=
  (hkGS_inv μ hμ).2 μ' h c x hc

end Googology.Trans.PoR.InaccPsi.R2.Hk
