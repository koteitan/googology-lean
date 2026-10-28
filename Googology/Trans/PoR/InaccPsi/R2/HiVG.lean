import Googology.Trans.PoR.InaccPsi.R2.HiVL

/-!
# HiVG: `G` AS A BASE OF EVERY LEVEL `Ω₁ + κ`, AND THE RECURSION ON THE LEVEL OVER `G`

`G = Γ_{Ω₁+1}` is a base of every level `Ω₁ + κ` (`κ < Ω₁`; `hiGB κ`: code gate `0`, reading gate `κ`, reading
`Γ_{x+1}`, outer low field `hdNx (x+x) (Γ_{x+1})`).  The systems `hiGL κ` (bound `N_{Ω₁+κ}(G) = φ(Ω₁+κ+1, G+1)`, base
gate `κ`, base reading `N_{x+κ}(Γ_{x+1}) = φ(x+κ+1, Γ_{x+1}+1)`) are defined by one recursion on `κ < Ω₁`:
`hiGL κ` is the union of all gated offsets over `G` at level `Ω₁ + κ` (`Hi.hiVTU` with the step `Hi.hiVLS κ`), started
at `Hg.hgU` (`κ = 0`), at `hiGL μ` (`κ = μ + 1`), and at the union of the gated `ω`-chain `hiGL κ_k`
(`κ_k = He.heFs κ k`, `Hg.HgfCh`) at a limit `κ`.  `hiGL_inv`: the shape and the extension of every earlier system.

* `hiGZo`, `hiGB` (**`G` AS A BASE OF LEVEL `Ω₁ + κ`**), `HiGShape`, `hiG_start`, `HiGOK`, `hiG_ok_shape`, `hiGSt`,
  `HiGCoh`, `hiGCh`, `hiGChU`, `hiGL` (**THE RECURSION ON THE LEVEL OVER `G`**), `hiGL_inv` (**THE INVARIANT**),
  `hiGL_B`, `hiGL_γ`, `hiGL_ext`.

No new axiom.  New definitions: `hiGZo`, `hiGB`, `HiGShape`, `HiGOK`, `hiGSt`, `HiGCoh`, `hiGCh`, `hiGChU`, `hiGL`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hi

open Googology.Trans.PoR.InaccPsi.R2.Hg
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

/-! ## `G` as a base of every level `Ω₁ + κ` -/

/-- **The outer low field over `G`**: `hdNx (x+x) (Γ_{x+1})` (read with `max(ω, x)`). -/
noncomputable def hiGZo (x : Ordinal.{0}) : Ordinal.{0} := hdNx (max ω x + max ω x) (lgG x)

theorem hiGZo_fix (x : Ordinal.{0}) : veblen 2 (hiGZo x) = hiGZo x :=
  hdNx_fix (((show (2 : Ordinal.{0}) < ω from by exact_mod_cast natCast_lt_omega0 2).trans_le
    (le_max_left ω x)).trans_le
    le_self_add) _

section GBase

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem hiGZo_eq : hiGZo x = hdNx (x + x) (lgG x) := by
  unfold hiGZo; rw [max_eq_right (omega0_lt_inE hx).le]

theorem hi_xx_lt_G : x + x < lgG x :=
  (inE_indec (lgG_facts hx hx1).2.2.2.1).add_lt (lgG_facts hx hx1).2.1 (lgG_facts hx hx1).2.1

theorem hiGZo_lt1 : hiGZo x < gq 1 x := by
  have hq := (gm1_facts hx hx1).2.2.2
  have hxx : x + x < gq 1 x := (inE_indec hq).add_lt (gm1_facts hx hx1).2.1 (gm1_facts hx hx1).2.1
  have hfix : veblen (x + x) (lgG x) = lgG x := hc_G_fix hx hx1 ((hi_one_le hx hx1).trans le_self_add)
    (hi_xx_lt_G hx hx1)
  rw [hiGZo_eq hx hx1, hdNx_fixP hfix, ← hc_glA_fixG hx hx1 ((hi_one_le hx hx1).trans le_self_add) hxx hfix
    (hi_xx_lt_G hx hx1) (lgG_facts hx hx1).2.1 (mg_lgG_lt_G1 hx hx1)]
  exact hi_glA_lt1 hx hx1 hxx (mg_lgG_lt_G1 hx hx1)

variable {κ : Ordinal.{0}} (hκx : κ < x)
include hκx

theorem hi_xk_lt_G : x + κ < lgG x :=
  (inE_indec (lgG_facts hx hx1).2.2.2.1).add_lt (lgG_facts hx hx1).2.1 (hκx.trans (lgG_facts hx hx1).2.1)

theorem hi_xk1_lt_G : x + κ + 1 < lgG x :=
  (ev_isSuccLimit_of_inE (lgG_facts hx hx1).2.2.2.1).add_one_lt (hi_xk_lt_G hx hx1 hκx)

theorem hiG_fix_xk : veblen (x + κ) (lgG x) = lgG x :=
  hc_G_fix hx hx1 ((hi_one_le hx hx1).trans le_self_add) (hi_xk_lt_G hx hx1 hκx)

theorem hiG_fix_xk1 : veblen (x + κ + 1) (lgG x) = lgG x :=
  hc_G_fix hx hx1 (((hi_one_le hx hx1).trans le_self_add).trans le_self_add) (hi_xk1_lt_G hx hx1 hκx)

/-- **`N_{x+κ}(Γ_{x+1}) = φ(x+κ+1, Γ_{x+1}+1)`.** -/
theorem hiG_N_eq : hcN (x + κ) (lgG x) = veblen (x + κ + 1) (lgG x + 1) := by
  have := hcN_veb (x + κ) (lgG x); rwa [hiG_fix_xk1 hx hx1 hκx] at this

theorem hiG_N_lt_Zo : hcN (x + κ) (lgG x) < hiGZo x := by
  rw [hiGZo_eq hx hx1]
  refine hdN_lt_Nx ?_
  rw [add_assoc]
  exact (add_lt_add_iff_left x).2 ((ev_isSuccLimit_of_inE hx).add_one_lt hκx)

end GBase

theorem hiG_L_lt_G {κ : Ordinal.{0}} (hκ : κ < Om1) : Om1 + κ < gcG 0 :=
  (inE_indec gr_G_inE).add_lt (hg_Om1_lt_G 0) (hκ.trans (hg_Om1_lt_G 0))

theorem hiG_L1_lt_G {κ : Ordinal.{0}} (hκ : κ < Om1) : Om1 + κ + 1 < gcG 0 :=
  (ev_isSuccLimit_of_inE gr_G_inE).add_one_lt (hiG_L_lt_G hκ)

theorem hiG_fixL {κ : Ordinal.{0}} (hκ : κ < Om1) : veblen (Om1 + κ) (gcG 0) = gcG 0 :=
  gn_veb_fix (gcG_SC 0) (hiG_L_lt_G hκ)

theorem hiG_fixL1 {κ : Ordinal.{0}} (hκ : κ < Om1) : veblen (Om1 + κ + 1) (gcG 0) = gcG 0 :=
  gn_veb_fix (gcG_SC 0) (hiG_L1_lt_G hκ)

/-- **`N_{Ω₁+κ}(G) = φ(Ω₁+κ+1, G+1)`.** -/
theorem hiG_NL_eq {κ : Ordinal.{0}} (hκ : κ < Om1) : hcN (Om1 + κ) (gcG 0) = veblen (Om1 + κ + 1) (gcG 0 + 1) := by
  have := hcN_veb (Om1 + κ) (gcG 0); rwa [hiG_fixL1 hκ] at this

theorem hiG_NL_lt1 {κ : Ordinal.{0}} (hκ : κ < Om1) : hcN (Om1 + κ) (gcG 0) < gcG 1 := by
  have hG1 := gcG_SC 1
  have hE := Low.opow_eq_self_of_SC hG1
  have hfix : veblen (Om1 + κ + 1) (gcG 1) = gcG 1 :=
    gn_veb_fix hG1 ((hiG_L1_lt_G hκ).trans (gcG_lt zero_lt_one))
  rw [hiG_NL_eq hκ]
  have h2 := (isNormal_veblen (Om1 + κ + 1)).strictMono ((ev_isSuccLimit_of_inE hE).add_one_lt (gcG_lt zero_lt_one))
  rwa [hfix] at h2

/-- **Lemma EXACT for `N_{ρ+κ}(Γ_{ρ+1}) = ϑᵖ(Ω₁·(ρ+κ+1) + Γ_{ρ+1})`**, `κ < σ`. -/
theorem hiG_N_pi {κ σ ρ : Ordinal.{0}} (hB : Bases σ ρ) (hκσ : κ < σ) :
    hcN (ρ + κ) (lgG ρ) ∈ TB ρ σ ∧ pi σ ρ (hcN (ρ + κ) (lgG ρ)) = hcN (σ + κ) (lgG σ) := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  have hκρ : κ < ρ := hκσ.trans hB.2.2.1
  obtain ⟨u1, u2⟩ := hiv_lev1_pi hB hκσ
  obtain ⟨g1, g2⟩ : lgG ρ ∈ TB ρ σ ∧ pi σ ρ (lgG ρ) = lgG σ := Go.goGl.ba_pi σ ρ hB
  have hq1 : ρ + κ + 1 < Om1 := ((hi_xk1_lt_G hB.2.1 hρ1 hκρ).trans (lgG_facts hB.2.1 hρ1).2.2.1)
  have h := glA_pi hB u1 hq1 g1 (lgG_facts hB.2.1 hρ1).2.2.1
  rw [u2, g2] at h
  rw [hiv_N_glA hB.2.1 hρ1 hκρ (hiG_fix_xk1 hB.2.1 hρ1 hκρ) (hi_xk1_lt_G hB.2.1 hρ1 hκρ) (mg_lgG_lt_G1 hB.2.1 hρ1),
    hiv_N_glA hB.1 hσ1 hκσ (hiG_fix_xk1 hB.1 hσ1 hκσ) (hi_xk1_lt_G hB.1 hσ1 hκσ) (mg_lgG_lt_G1 hB.1 hσ1)]
  exact h

/-- **`G` AS A BASE OF LEVEL `Ω₁ + κ`** (code gate `0`, reading gate `κ`, reading `Γ_{x+1}`). -/
noncomputable def hiGB (κ : Ordinal.{0}) (hκ : κ < Om1) : HiVB κ where
  F := gcG 0
  Fr := lgG
  γ := 0
  γN := κ
  Zo := hiGZo
  lv := hκ
  γ_le := zero_le
  lvN := le_rfl
  γN_lt := hκ
  F_fix := hiG_fixL hκ
  G_le := le_rfl
  N_lt1 := hiG_NL_lt1 hκ
  F_mem := fun S _ _ ha _ => gmS_G0_mem S ha
  N_mem := fun S _ _ ha hb => by
    rw [hiG_NL_eq hκ]
    exact CSet.phi_mem (CSet.succ_mem (hiv_L_mem S hb)) (CSet.succ_mem (gmS_G0_mem S ha))
  F_code := fun _ _ _ _ _ _ _ => GxCl.atom (Set.mem_singleton _)
  F_cl := fun _ hZ _ _ _ _ _ => hZ.1
  N_cl := fun Z hZ hZ1 h => by
    rw [hiG_NL_eq hκ, add_assoc] at h
    have hκ1 : κ + 1 < Om1 := gl_Om1_lim.add_one_lt hκ
    have hG : gcG 0 < veblen (Om1 + (κ + 1)) (gcG 0 + 1) :=
      (lt_add_one _).trans_le (right_le_veblen _ _)
    exact (lt_add_one κ).trans (hiv_cl_gate hκ1 hZ hZ1 (hd_succ_lt (hiv_L0 _) _) hG h le_rfl
      ((isNormal_veblen _).strictMono (lt_add_one _)))
  γN_cl := fun _ _ _ _ h => h
  Fr_gt := fun hx hx1 hγ => hi_xk_lt_G hx hx1 hγ
  Fr_fix := fun hx hx1 hγ => hiG_fix_xk hx hx1 hγ
  N_Zo := fun hx hx1 hγ => hiG_N_lt_Zo hx hx1 hγ
  Zo_fix := hiGZo_fix
  Zo_G1 := fun x hx hx1 => hiGZo_lt1 hx hx1
  Fr_pi := fun hB _ => Go.goGl.ba_pi _ _ hB
  N_pi := fun hB hγ => hiG_N_pi hB hγ

/-! ## The start of the offset recursion over `G` at level `Ω₁ + κ` -/

/-- **The shape of a start at `φ(Ω₁+κ, G+1)`.** -/
def HiGShape (κ : Ordinal.{0}) (S0 : HgVD) : Prop :=
  S0.B = veblen (Om1 + κ) (gcG 0 + 1) ∧ (∀ x, InE x → x < Om1 → (S0.γ < x ↔ κ < x)) ∧
    (∀ x, InE x → x < Om1 → κ < x → S0.b x = veblen (x + κ) (lgG x + 1)) ∧
    ∀ x, InE x → x < Om1 → S0.Z x = if κ < x then evZ (veblen (x + κ) (lgG x + 1)) else hiGZo x

theorem hiG_glA {κ x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hκx : κ < x) :
    glA (x + κ) (lgG x) x = veblen (x + κ) (lgG x + 1) := by
  rw [hiv_glA_fixP hx hx1 hκx (hiG_fix_xk hx hx1 hκx) (hi_xk_lt_G hx hx1 hκx) (mg_lgG_lt_G1 hx hx1),
    hdNx_fixP (hiG_fix_xk hx hx1 hκx)]

/-- **A system of the shape starts the offset recursion over `G` at level `Ω₁ + κ`.** -/
theorem hiG_start (κ : Ordinal.{0}) (hκ : κ < Om1) (S0 : HgVD) (h : HiGShape κ S0) :
    HiVStart (hiGB κ hκ) S0 where
  B := by rw [add_zero]; exact h.1
  Zb := fun x hx hx1 => by
    rw [h.2.2.2 x hx hx1]
    by_cases hk : κ < x
    · rw [if_pos hk, (hiGB κ hκ).Zl_eq hx hk]
      exact (hb_evZ_lt_fix2 (hc_fix_down ((show (2 : Ordinal.{0}) ≤ ω from
        (by exact_mod_cast (natCast_lt_omega0 2).le)).trans ((omega0_lt_inE hx).le.trans le_self_add))
        (hcN_fix _ _)) hc_next_lt_N).le
    · rw [if_neg hk, (hiGB κ hκ).Zl_low hk]; rfl
  st := fun h2 hZ => {
    ix := by
      show S0.ix = veblen (Om1 + κ) (gcG 0 + 1 + 0)
      rw [add_zero]; exact hg_ix_of_B (veblen_veblen_of_lt (hg_one_lt_Om1.trans_le le_self_add) _) h.1
    γ := fun x hx hx1 => by
      show S0.γ < x ↔ max κ (S0.g 0) < x
      rw [S0.g_zero, max_eq_left zero_le]; exact h.2.1 x hx hx1
    b := fun x hx hx1 hg => by
      have hk : κ < x := by
        have : max κ (S0.g 0) < x := hg
        rwa [S0.g_zero, max_eq_left zero_le] at this
      show S0.b x = glA (x + κ) (lgG x + S0.R 0 x) x
      rw [S0.R_zero, add_zero, h.2.2.1 x hx hx1 hk, hiG_glA hx hx1 hk]
    Z := fun x hx hx1 => by
      unfold HgPB.Zst
      show S0.Z x = if max κ (S0.g 0) < x then evZ (glA (x + κ) (lgG x + S0.R 0 x) x)
        else (hiGB κ hκ).Zl x
      rw [S0.g_zero, max_eq_left zero_le, S0.R_zero, add_zero, h.2.2.2 x hx hx1]
      by_cases hk : κ < x
      · rw [if_pos hk, if_pos hk, hiG_glA hx hx1 hk]
      · rw [if_neg hk, if_neg hk, (hiGB κ hκ).Zl_low hk]; rfl }
  high0 := fun _ _ _ _ hσ _ _ => hσ.pos

/-- **`Hg.hgU` has the shape at level `Ω₁ + 0`.** -/
theorem hgU_shape : HiGShape 0 hgU := by
  refine ⟨by rw [add_zero]; rfl, fun x hx hx1 => hgU_startF.γ x hx hx1, fun x hx hx1 _ => ?_, fun x hx hx1 => ?_⟩
  · rw [add_zero, hgU_hib hx hx1]; rfl
  · rw [add_zero, if_pos hx.pos, hgU_hiZ hx hx1]; rfl

/-! ## The recursion on the level over `G` -/

/-- **The shape of the system at level `Ω₁ + κ` over `G`.** -/
def HiGOK (κ : Ordinal.{0}) (T : HgVD) : Prop :=
  T.B = hcN (Om1 + κ) (gcG 0) ∧ T.γ = κ ∧ (∀ x, InE x → x < Om1 → κ < x → T.b x = hcN (x + κ) (lgG x)) ∧
    ∀ x, InE x → x < Om1 → T.Z x = if κ < x then evZ (hcN (x + κ) (lgG x)) else hiGZo x

theorem hi_lt_succ_iff {κ x : Ordinal.{0}} (hx : InE x) : κ < x ↔ κ + 1 < x :=
  ⟨fun h => (ev_isSuccLimit_of_inE hx).add_one_lt h, fun h => (lt_add_one κ).trans h⟩

/-- **The system at level `Ω₁ + μ` has the shape of a start at level `Ω₁ + μ + 1`.** -/
theorem hiG_ok_shape {μ : Ordinal.{0}} (hμ : μ + 1 < Om1) {T : HgVD} (h : HiGOK μ T) : HiGShape (μ + 1) T := by
  have hμ1 : μ < Om1 := (lt_add_one μ).trans hμ
  refine ⟨by rw [h.1, hiG_NL_eq hμ1, add_assoc], fun x hx hx1 => ?_, fun x hx hx1 hk => ?_, fun x hx hx1 => ?_⟩
  · rw [h.2.1]; exact hi_lt_succ_iff hx
  · have hk' : μ < x := (lt_add_one μ).trans hk
    rw [h.2.2.1 x hx hx1 hk', hiG_N_eq hx hx1 hk', add_assoc]
  · rw [h.2.2.2 x hx hx1]
    by_cases hk : μ < x
    · rw [if_pos hk, if_pos ((hi_lt_succ_iff hx).1 hk), hiG_N_eq hx hx1 hk, add_assoc]
    · rw [if_neg hk, if_neg (fun h' => hk ((hi_lt_succ_iff hx).2 h'))]

open Classical in
/-- **The step of the level recursion over `G`**: the union of all offsets over `G` at level `Ω₁ + κ`, started at
`S0` (when `S0` has the shape). -/
noncomputable def hiGSt (κ : Ordinal.{0}) (S0 : HgVD) : HgVD :=
  if H : ∃ hκ : κ < Om1, HiGShape κ S0 then
    hiVTU (St := hiVLS κ) (fun Q U h => hiVLS_spec H.choose Q U h) (hiG_start κ H.choose S0 H.choose_spec)
  else S0

theorem hiGSt_eq {κ : Ordinal.{0}} (hκ : κ < Om1) {S0 : HgVD} (h : HiGShape κ S0) :
    hiGSt κ S0 = hiVTU (St := hiVLS κ) (fun Q U h => hiVLS_spec hκ Q U h) (hiG_start κ hκ S0 h) := by
  unfold hiGSt; rw [dif_pos ⟨hκ, h⟩]

theorem hiGSt_OK {κ : Ordinal.{0}} (hκ : κ < Om1) {S0 : HgVD} (h : HiGShape κ S0) : HiGOK κ (hiGSt κ S0) := by
  rw [hiGSt_eq hκ h]
  exact ⟨rfl, rfl, fun _ _ _ _ => rfl, fun x _ _ => rfl⟩

theorem hiGSt_ext {κ : Ordinal.{0}} (hκ : κ < Om1) {S0 : HgVD} (h : HiGShape κ S0) {c : Ordinal.{0}}
    (hc : c < S0.B) : (∀ x, (hiGSt κ S0).R c x = S0.R c x) ∧ (hiGSt κ S0).g c = S0.g c := by
  rw [hiGSt_eq hκ h]
  exact ⟨fun x => hiVTU_R0 _ _ hc x, hiVTU_g0 _ _ hc⟩

/-- **The condition at a limit level.** -/
def HiGCoh (l : Ordinal.{0}) (IH : ∀ κ, κ < l → HgVD) : Prop :=
  (∀ κ (h : κ < l), HiGOK κ (IH κ h)) ∧ ∀ κ κ' (h : κ < l) (h' : κ' < l), κ ≤ κ' → ∀ c x, c < (IH κ h).B →
    (IH κ' h').R c x = (IH κ h).R c x ∧ (IH κ' h').g c = (IH κ h).g c

section LimCh

variable (l : Ordinal.{0}) (hl : IsSuccLimit l) (hle : l < Om1) (IH : ∀ κ, κ < l → HgVD) (H : HiGCoh l IH)

include hl hle in
theorem hiG_kk_lt (a : Ordinal.{0}) (k : ℕ) : a + heFs l k + 1 < a + l := by
  rw [add_assoc]; exact (add_lt_add_iff_left _).2 (hl.add_one_lt (heFs_lt hl (hgf_om hle) k))

include hle in
theorem hiG_NxQ : hdNx (Om1 + l) (gcG 0) = veblen (Om1 + l) (gcG 0 + 1) := hdNx_fixP (hiG_fixL hle)

theorem hiG_Nxx {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (h : l < x) :
    hdNx (x + l) (lgG x) = veblen (x + l) (lgG x + 1) := hdNx_fixP (hiG_fix_xk hx hx1 h)

include H in
/-- **THE CHAIN AT A LIMIT LEVEL** over `G`. -/
noncomputable def hiGCh : HgfCh where
  D := fun k => IH (heFs l k) (heFs_lt hl (hgf_om hle) k)
  B := hdNx (Om1 + l) (gcG 0)
  b := fun x => hdNx (x + l) (lgG x)
  γ := l
  Zo := hiGZo
  γ_lt := hle
  γ0 := fun k => by rw [(H.1 _ _).2.1]; exact (heFs_lt hl (hgf_om hle) k).le
  γ_cl := fun Z hZ hZ1 h => by
    rw [hiG_NxQ l hle] at h
    have hG : gcG 0 < veblen (Om1 + l) (gcG 0 + 1) := (lt_add_one _).trans_le (right_le_veblen _ _)
    exact hiv_cl_gate hle hZ hZ1 (hd_succ_lt (hiv_L0 _) _) hG h le_rfl ((isNormal_veblen _).strictMono (lt_add_one _))
  B_mono := fun k => by
    rw [(H.1 _ _).1, (H.1 _ _).1]
    exact hcN_mono (add_le_add le_rfl (heFs_mono hl (hgf_om hle) k).le) _
  B_lt := fun k => by
    rw [(H.1 _ _).1]
    exact hdN_lt_Nx (hiG_kk_lt l hl hle Om1 k)
  B_cof := fun c hc => by
    obtain ⟨k, hk⟩ := (hiVLmOf l hl hle).cofNx Om1 hc
    refine ⟨k, ?_⟩
    rw [(H.1 _ _).1]
    exact hk.trans_le (hdNx_le (hc_LuP_of_fix (hcN_fix _ _) |> hd_LuP_mono le_self_add) (hcN_gt _ _))
  R_ext := fun k c x hc => (H.2 _ _ _ _ (heFs_mono hl (hgf_om hle) k).le c x hc).1
  g_ext := fun k c hc => (H.2 _ _ _ _ (heFs_mono hl (hgf_om hle) k).le c 0 hc).2
  B_lt1 := (hdNx_le (hc_LuP_of_fix (hcN_fix _ _) |> hd_LuP_mono le_self_add) (hcN_gt _ _)).trans_lt
    (hiG_NL_lt1 hle)
  B_fix := hdNx_fix (hg_one_lt_Om1.trans_le le_self_add) _
  B_mem := fun S _ _ ha hb => by
    rw [hiG_NxQ l hle]
    exact CSet.phi_mem (hiv_L_mem S hb) (CSet.succ_mem (gmS_G0_mem S ha))
  b_ge := fun k x hx hx1 hγ => by
    rw [(H.1 _ _).2.2.1 x hx hx1 ((heFs_lt hl (hgf_om hle) k).trans hγ)]
    exact (hdN_lt_Nx (hiG_kk_lt l hl hle x k)).le
  b_cof := fun x hx hx1 hγ μ hμ => by
    obtain ⟨k, hk⟩ := (hiVLmOf l hl hle).cofNx x hμ
    refine ⟨k, ?_⟩
    rw [(H.1 _ _).2.2.1 x hx hx1 ((heFs_lt hl (hgf_om hle) k).trans hγ)]
    exact hk.trans_le (hdNx_le (hc_LuP_of_fix (hcN_fix _ _) |> hd_LuP_mono le_self_add) (hcN_gt _ _))
  b_fix := fun x hx _ _ => hdNx_fix ((one_lt_omega0.trans (omega0_lt_inE hx)).trans_le le_self_add) _
  b_gt := fun x hx hx1 _ => (lgG_facts hx hx1).2.1.trans (hdNx_gt _ _)
  b_lt := fun x hx hx1 hγ => by
    rw [hiG_Nxx l hx hx1 hγ]
    refine (hiv_glA_facts hx hx1 hγ (mg_lgG_lt_G1 hx hx1)).2.1 |> fun _ => ?_
    rw [← hiG_glA hx hx1 hγ]
    exact hi_glA_lt1 hx hx1 (hiv_q hx hx1 hγ) (mg_lgG_lt_G1 hx hx1)
  b_pi := fun σ ρ hB hγ => by
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
    have hγρ : l < ρ := hγ.trans hB.2.2.1
    obtain ⟨g1, g2⟩ : lgG ρ ∈ TB ρ σ ∧ pi σ ρ (lgG ρ) = lgG σ := Go.goGl.ba_pi σ ρ hB
    have h := hiv_glA_pi hB hγ g1 (mg_lgG_lt_G1 hB.2.1 hρ1)
    rw [g2, hiG_glA hB.2.1 hρ1 hγρ, hiG_glA hB.1 hσ1 hγ] at h
    rw [hiG_Nxx l hB.2.1 hρ1 hγρ, hiG_Nxx l hB.1 hσ1 hγ]
    exact h
  Z_low := fun k x hx hx1 hγ => by
    rw [(H.1 _ _).2.2.2 x hx hx1]
    split_ifs with h
    · exact (hb_evZ_lt_fix2 (hiGZo_fix x) (hiG_N_lt_Zo hx hx1 h)).le
    · exact le_rfl
  Zo_fix := fun x => hc_fix_down one_le_two (hiGZo_fix x)
  Zo_G1 := fun x hx hx1 => hiGZo_lt1 hx hx1

theorem hiGCh_shape : HiGShape l (hiGCh l hl hle IH H).U := by
  refine ⟨hiG_NxQ l hle, fun x _ _ => Iff.rfl, fun x hx hx1 h => hiG_Nxx l hx hx1 h, fun x hx hx1 => ?_⟩
  show (if l < x then evZ (hdNx (x + l) (lgG x)) else hiGZo x) = _
  by_cases h : l < x
  · rw [if_pos h, if_pos h, hiG_Nxx l hx hx1 h]
  · rw [if_neg h, if_neg h]

end LimCh

open Classical in
/-- The start at a limit level: the union of the chain (when the condition holds). -/
noncomputable def hiGChU (l : Ordinal.{0}) (hl : IsSuccLimit l) (IH : ∀ κ, κ < l → HgVD) : HgVD :=
  if H : ∃ hle : l < Om1, HiGCoh l IH then (hiGCh l hl H.choose IH H.choose_spec).U else hgU

/-- **THE SYSTEM AT `φ(Ω₁+κ+1, G+1)`, BY ONE RECURSION ON THE LEVEL `κ < Ω₁`.** -/
noncomputable def hiGL (κ : Ordinal.{0}) : HgVD :=
  Ordinal.limitRecOn (motive := fun _ => HgVD) κ (hiGSt 0 hgU) (fun μ T => hiGSt (μ + 1) T)
    (fun l hl IH => hiGSt l (hiGChU l hl IH))

theorem hiGL_zero : hiGL 0 = hiGSt 0 hgU := by unfold hiGL; rw [Ordinal.limitRecOn_zero]

theorem hiGL_succ (μ : Ordinal.{0}) : hiGL (μ + 1) = hiGSt (μ + 1) (hiGL μ) := by
  unfold hiGL; rw [Ordinal.limitRecOn_add_one]

theorem hiGL_limit {l : Ordinal.{0}} (hl : IsSuccLimit l) : hiGL l = hiGSt l (hiGChU l hl (fun κ _ => hiGL κ)) := by
  unfold hiGL; rw [Ordinal.limitRecOn_limit _ _ _ _ hl]

/-- **THE INVARIANT**: every `hiGL κ`, `κ < Ω₁`, has the shape at level `Ω₁ + κ` and extends every `hiGL κ'`,
`κ' ≤ κ`. -/
theorem hiGL_inv : ∀ κ, κ < Om1 → HiGOK κ (hiGL κ) ∧ ∀ κ', κ' ≤ κ → ∀ c x, c < (hiGL κ').B →
    (hiGL κ).R c x = (hiGL κ').R c x ∧ (hiGL κ).g c = (hiGL κ').g c := by
  intro κ
  induction κ using WellFoundedLT.induction with
  | ind κ IH =>
  intro hκ
  rcases zero_or_succ_or_isSuccLimit κ with h0 | ⟨μ, hμ⟩ | hlim
  · subst h0
    rw [hiGL_zero]
    refine ⟨hiGSt_OK hκ hgU_shape, fun κ' hκ' c x _ => ?_⟩
    rw [nonpos_iff_eq_zero.1 hκ', hiGL_zero]; exact ⟨rfl, rfl⟩
  · have hμ' : κ = μ + 1 := by rw [← hμ, succ_eq_add_one]
    subst hμ'
    have hμ1 : μ < Om1 := (lt_add_one μ).trans hκ
    obtain ⟨hok, hext⟩ := IH μ (lt_add_one μ) hμ1
    have hsh := hiG_ok_shape hκ hok
    rw [hiGL_succ]
    refine ⟨hiGSt_OK hκ hsh, fun κ' hκ' c x hc => ?_⟩
    rcases hκ'.lt_or_eq with hlt | heq
    · have hle : κ' ≤ μ := Order.lt_add_one_iff.1 hlt
      have hcμ : c < (hiGL μ).B := by
        rw [hok.1]; rw [(IH κ' (lt_of_le_of_lt hle (lt_add_one μ)) (hle.trans_lt hμ1)).1.1] at hc
        exact hc.trans_le (hcN_mono (add_le_add le_rfl hle) _)
      obtain ⟨r2, g2⟩ := hext κ' hle c x hc
      exact ⟨((hiGSt_ext hκ hsh hcμ).1 x).trans r2, (hiGSt_ext hκ hsh hcμ).2.trans g2⟩
    · subst heq; rw [hiGL_succ]; exact ⟨rfl, rfl⟩
  · have hcoh : HiGCoh κ (fun κ' _ => hiGL κ') :=
      ⟨fun κ' h => (IH κ' h (h.trans hκ)).1, fun κ₁ κ₂ h₁ h₂ h12 c x hc =>
        (IH κ₂ h₂ (h₂.trans hκ)).2 κ₁ h12 c x hc⟩
    have eU : hiGChU κ hlim (fun κ' _ => hiGL κ') = (hiGCh κ hlim hκ (fun κ' _ => hiGL κ') hcoh).U := by
      unfold hiGChU; rw [dif_pos ⟨hκ, hcoh⟩]
    have hsh := hiGCh_shape κ hlim hκ (fun κ' _ => hiGL κ') hcoh
    rw [hiGL_limit hlim, eU]
    refine ⟨hiGSt_OK hκ hsh, fun κ' hκ' c x hc => ?_⟩
    rcases hκ'.lt_or_eq with hlt | heq
    · obtain ⟨k, hk⟩ := heFs_cof hlim (hgf_om hκ) κ' hlt
      have hkl := heFs_lt hlim (hgf_om hκ) k
      obtain ⟨hokk, hextk⟩ := IH _ hkl (hkl.trans hκ)
      have hck : c < (hiGL (heFs κ k)).B := by
        rw [hokk.1]; rw [(IH κ' hlt (hlt.trans hκ)).1.1] at hc
        exact hc.trans_le (hcN_mono (add_le_add le_rfl hk.le) _)
      set C := hiGCh κ hlim hκ (fun κ' _ => hiGL κ') hcoh with hC
      have hcC : c < C.U.B := hck.trans (C.B_lt k)
      obtain ⟨r2, g2⟩ := hextk κ' hk.le c x hc
      refine ⟨((hiGSt_ext hκ hsh hcC).1 x).trans ((C.U_R (k := k) hck x).trans r2),
        (hiGSt_ext hκ hsh hcC).2.trans ((C.U_g (k := k) hck).trans g2)⟩
    · subst heq; rw [hiGL_limit hlim, eU]; exact ⟨rfl, rfl⟩

theorem hiGL_B {κ : Ordinal.{0}} (hκ : κ < Om1) : (hiGL κ).B = veblen (Om1 + κ + 1) (gcG 0 + 1) := by
  rw [(hiGL_inv κ hκ).1.1, hiG_NL_eq hκ]

theorem hiGL_γ {κ : Ordinal.{0}} (hκ : κ < Om1) : (hiGL κ).γ = κ := (hiGL_inv κ hκ).1.2.1

theorem hiGL_ext {κ κ' : Ordinal.{0}} (hκ : κ < Om1) (h : κ' ≤ κ) {c : Ordinal.{0}} (hc : c < (hiGL κ').B)
    (x : Ordinal.{0}) : (hiGL κ).R c x = (hiGL κ').R c x ∧ (hiGL κ).g c = (hiGL κ').g c :=
  (hiGL_inv κ hκ).2 κ' h c x hc

end Googology.Trans.PoR.InaccPsi.R2.Hi
