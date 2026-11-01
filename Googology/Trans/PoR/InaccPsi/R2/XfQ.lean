import Googology.Trans.PoR.InaccPsi.R2.XfG1

/-!
# XfQ: THE PSEUDO-BASES `φ(G, ν)` OF THE LEVEL `G` (`1 ≤ ν < Γ₀`), THE PACKAGE AT `G`, THE SUCCESSOR STEP

The level `G` of the (A3) code interface is the level datum `xfLv = Xc.xcA3.lv G` (gate `1`, reading `Γ_{x+1}`).

* `xfQ ν` (**THE PSEUDO-BASE `φ(G, ν)` OF THE LEVEL `G`** for every constant `1 ≤ ν < Γ₀`: reading `φ(Γ_{x+1}, ν)`
  above the gate `ν`, low field `Wn.wnZo`; Lemma EXACT from `Xf.xf_veb_pi` at the bases `σ > ν`, where `ν` is a
  constant; the code-gate fields hold since `ν < Γ₀ ≤ Z` for every strongly critical `Z`);
* `xfPk` (**THE PACKAGE AT THE LEVEL `G`**: the entry of the (A3) family `Ws.wsF Xc.xcCls` at `G`);
* `xf_start_iff` (the start of `xfQ ν`, explicitly), `xf_start1` (**`Xf.xfV1` STARTS `φ(G, 1)`**),
  `xf_start_succ` (**THE PACKAGE AT `G` MAPS A START OF `φ(G, ν)` TO A START OF `φ(G, ν+1)`**).

No new axiom.  New definitions: `xfLv`, `xfQ`, `xfPk`.
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

namespace Googology.Trans.PoR.InaccPsi.R2.Xf

/-- **The level datum of `G`** in the (A3) code interface (gate `1`). -/
noncomputable def xfLv : HnLv := xcA3.lv (gcG 0) xf_lev_G

theorem xfLv_L : xfLv.L = gcG 0 := rfl

theorem xfLv_g : xfLv.g = 1 := xf_xg_G

theorem xf_l {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : xfLv.l x = lgG x := by
  have h := xcA3.lv_l xf_lev_G hx hx1 (by rw [xcA3_g, xf_xg_G]; exact wo_one_lt_inE hx)
  rw [show xfLv.l x = (xcA3.lv (gcG 0) xf_lev_G).l x from rfl, h, xcA3_R, wtD_RG]

theorem xf_eps0_le_SC {Z : Ordinal.{0}} (hZ : SC Z) : ε₀ ≤ Z := gc_eps0_le (Low.opow_eq_self_of_SC hZ)

theorem xf_eps0_lt_G1 : (ε₀ : Ordinal.{0}) < gcG 1 :=
  (gc_eps0_le gl_G0_E).trans_lt (gcG_lt zero_lt_one)

theorem xf_vG_lt1 {a : Ordinal.{0}} (ha : a < gcG 1) : veblen (gcG 0) a < gcG 1 := by
  have h := (isNormal_veblen (gcG 0)).strictMono ha
  rwa [gn_veb_fix (gcG_SC 1) (gcG_lt zero_lt_one)] at h

theorem xf_G_lt_vG {a : Ordinal.{0}} (ha : 0 < a) : gcG 0 < veblen (gcG 0) a := by
  have h := (isNormal_veblen (gcG 0)).strictMono ha
  rwa [xf_G_veb0] at h

theorem xf_Zo_fixG {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : veblen (lgG x) (wnZo x) = wnZo x := by
  unfold wnZo; rw [wn_lgG_max hx hx1]; exact hdNx_fix (lt_add_one _) _

theorem xf_x_lt_Zo {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : x < wnZo x :=
  (lgG_facts hx hx1).2.1.trans (by unfold wnZo; rw [wn_lgG_max hx hx1]; exact hdNx_gt _ _)

theorem xf_vGx_lt_Zo {x a : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (ha : a < x) : veblen (lgG x) a < wnZo x := by
  have h := (isNormal_veblen (lgG x)).strictMono (ha.trans (xf_x_lt_Zo hx hx1))
  rwa [xf_Zo_fixG hx hx1] at h

theorem xf_Gx_lt_v {x a : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (ha : 0 < a) : lgG x < veblen (lgG x) a := by
  have h := (isNormal_veblen (lgG x)).strictMono ha
  rwa [he_G_sc hx hx1] at h

theorem xf_gam0_SC : SC (gamma 0 : Ordinal.{0}) := Lq.lq_gamma_SC 0

theorem xf_gam0_lim : IsSuccLimit (gamma 0 : Ordinal.{0}) :=
  ev_isSuccLimit_of_inE (Low.opow_eq_self_of_SC xf_gam0_SC)

theorem xf_gam0_lt_Om1 : (gamma 0 : Ordinal.{0}) < Om1 := gq_gam_lt_Om1

theorem xf_gam0_lt_G1 : (gamma 0 : Ordinal.{0}) < gcG 1 :=
  xf_gam0_lt_Om1.trans (gl_Om1_lt_G0.trans (gcG_lt zero_lt_one))

theorem xf_gam0_lt_gam1 : (gamma 0 : Ordinal.{0}) < gamma 1 := gamma_lt_gamma.2 zero_lt_one

theorem xf_lt_SC {o Z : Ordinal.{0}} (ho : o < gamma 0) (hZ : SC Z) : o < Z := ho.trans_le (Ta.taGam_le_SC hZ)

theorem xf_lim_x {o x : Ordinal.{0}} (hx : InE x) (h : o < x) : o + 1 < x := (ev_isSuccLimit_of_inE hx).add_one_lt h

/-- **THE PSEUDO-BASE `φ(G, ν)` OF THE LEVEL `G`**, `1 ≤ ν < Γ₀` (gate `ν`). -/
noncomputable def xfQ (o : Ordinal.{0}) (h1 : 1 ≤ o) (hΓ : o < gamma 0) : HnVQ xfLv 0 where
  F := veblen (gcG 0) o
  Fr := fun x => veblen (lgG x) o
  γ := o
  Zo := wnZo
  lv := gv_Om1_pos
  γ_ge := zero_le
  lg := xfLv_g.trans_le h1
  γ_lt := hΓ.trans xf_gam0_lt_Om1
  F_P := by rw [add_zero]; exact ⟨o, rfl⟩
  G_lt := xf_G_lt_vG (zero_lt_one.trans_le h1)
  S_lt1 := by
    rw [add_zero, xfLv_L, hdNx_veb]
    exact xf_vG_lt1 ((xf_gam0_lim.add_one_lt hΓ).trans xf_gam0_lt_G1)
  F_mem := fun S _ _ ha _ => CSet.phi_mem (gmS_G0_mem S ha) (gr_cst_mem ha _ o (hΓ.trans xf_gam0_lt_gam1))
  S_mem := fun S _ _ ha _ => by
    rw [add_zero, xfLv_L, hdNx_veb]
    exact CSet.phi_mem (gmS_G0_mem S ha)
      (gr_cst_mem ha _ (o + 1) ((xf_gam0_lim.add_one_lt hΓ).trans xf_gam0_lt_gam1))
  F_code := fun _ hZ _ _ _ _ _ =>
    GxCl.phi (GxCl.atom (Set.mem_singleton _)) (GxCl.small (xf_lt_SC hΓ hZ))
  F_cl := fun _ hZ _ _ _ _ _ => xf_lt_SC hΓ hZ
  S_cl := fun _ hZ _ _ => xf_lt_SC hΓ hZ
  Fr_gt := fun hx hx1 _ => by
    rw [xf_l hx hx1, add_zero]; exact xf_Gx_lt_v hx hx1 (zero_lt_one.trans_le h1)
  Fr_P := fun hx hx1 _ => by rw [xf_l hx hx1, add_zero]; exact ⟨o, rfl⟩
  S_Zo := fun {x} hx hx1 hγ => by
    rw [xf_l hx hx1, add_zero, hdNx_veb]
    exact xf_vGx_lt_Zo hx hx1 (xf_lim_x hx hγ)
  Zo_fix := wnZo_fix
  Zo_G1 := fun _ hx hx1 => wnZo_G1 hx hx1
  Fr_pi := fun hB hγ => xf_veb_pi hB h1 hγ
  S_pi := fun {σ ρ} hB hγ => by
    show hdNx (xfLv.l ρ + 0) (veblen (lgG ρ) o) ∈ TB ρ σ ∧
      pi σ ρ (hdNx (xfLv.l ρ + 0) (veblen (lgG ρ) o)) = hdNx (xfLv.l σ + 0) (veblen (lgG σ) o)
    rw [xf_l hB.2.1 hB.2.2.2, xf_l hB.1 (hB.2.2.1.trans hB.2.2.2), add_zero, add_zero, hdNx_veb, hdNx_veb]
    exact xf_veb_pi hB (h1.trans le_self_add) (xf_lim_x hB.1 hγ)

theorem xfQ_F (o : Ordinal.{0}) (h1 : 1 ≤ o) (hε : o < gamma 0) : (xfQ o h1 hε).F = veblen (gcG 0) o := rfl

theorem xfQ_γ (o : Ordinal.{0}) (h1 : 1 ≤ o) (hε : o < gamma 0) : (xfQ o h1 hε).γ = o := rfl

/-- **THE PACKAGE AT THE LEVEL `G`**: the entry of the (A3) family at `G`. -/
noncomputable def xfPk : HnPk :=
  wsPkOf (gcG 0) xf_lev_G (wsF xcCls (gcG 0)) (xcFam _ xf_lev_G xc_G_lt_t0).1

theorem xfPk_Λ : xfPk.Λ = xfLv := rfl

/-- **THE START OF `φ(G, ν)`, EXPLICITLY.** -/
theorem xf_start_iff (o : Ordinal.{0}) (h1 : 1 ≤ o) (hε : o < gamma 0) (U : HgVD) :
    HgSStart (hnVPB (xfQ o h1 hε)) U ↔
      U.ix = veblen (gcG 0) o ∧ (∀ x, InE x → x < Om1 → (U.γ < x ↔ o < x)) ∧
        (∀ x, InE x → x < Om1 → o < x → U.b x = veblen (lgG x) o) ∧
          ∀ x, InE x → x < Om1 → U.Z x = if o < x then evZ (veblen (lgG x) o) else wnZo x :=
  ⟨fun h => ⟨h.ix, h.γ, h.b, h.Z⟩, fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩⟩

theorem xf_one_lt_gam0 : (1 : Ordinal.{0}) < gamma 0 := xc_one_lt_SC xf_gam0_SC

/-- **`Xf.xfV1` STARTS `φ(G, 1)`.** -/
theorem xf_start1 : HgSStart (hnVPB (xfQ 1 le_rfl xf_one_lt_gam0)) xfV1 :=
  (xf_start_iff _ _ _ _).2 ⟨rfl, fun _ _ _ => Iff.rfl, fun _ _ _ _ => rfl, fun x _ _ => xfV1_Z x⟩

/-- A start of `φ(G, ν)` has the bound `φ(G, ν)`. -/
theorem xf_start_B {o : Ordinal.{0}} {h1 : 1 ≤ o} {hε : o < gamma 0} {U : HgVD}
    (h : HgSStart (hnVPB (xfQ o h1 hε)) U) : U.B = veblen (gcG 0) o := by
  rw [U.B_ix, ((xf_start_iff o h1 hε U).1 h).1]
  exact veblen_veblen_of_lt xf_one_lt_G _

/-- **THE SUCCESSOR STEP**: the package at `G` maps a start of `φ(G, ν)` to a start of `φ(G, ν+1)`. -/
theorem xf_start_succ (o : Ordinal.{0}) (h1 : 1 ≤ o) (hε : o < gamma 0) (hε1 : o + 1 < gamma 0) (U : HgVD)
    (h : HgSStart (hnVPB (xfQ o h1 hε)) U) :
    HgSStart (hnVPB (xfQ (o + 1) (h1.trans le_self_add) hε1)) (xfPk.St0 (xfQ o h1 hε) U h) := by
  have sp := xfPk.h0 (xfQ o h1 hε) U h
  have hB : (xfPk.St0 (xfQ o h1 hε) U h).B = veblen (gcG 0) (o + 1) := by
    rw [sp.B]; show hdNx (gcG 0 + 0) (veblen (gcG 0) o) = _
    rw [add_zero, hdNx_veb]
  refine (xf_start_iff _ _ _ _).2 ⟨?_, fun x hx _ => by
      rw [sp.γ]; exact ⟨fun h => xf_lim_x hx h, fun h => (lt_add_one o).trans h⟩, fun x hx hx1 hg => ?_,
    fun x hx hx1 => ?_⟩
  · have hfix : veblen 1 (veblen (gcG 0) (o + 1)) = veblen (gcG 0) (o + 1) := veblen_veblen_of_lt xf_one_lt_G _
    have h2 := (xfPk.St0 (xfQ o h1 hε) U h).B_ix
    rw [hB] at h2
    exact (isNormal_veblen 1).strictMono.injective (h2.symm.trans hfix.symm)
  · rw [sp.b x hx hx1 ((lt_add_one o).trans hg)]
    show hdNx (xfLv.l x + 0) (veblen (lgG x) o) = _
    rw [xf_l hx hx1, add_zero, hdNx_veb]
  · rw [sp.Z x hx hx1]
    show (if o < x then evZ (hdNx (xfLv.l x + 0) (veblen (lgG x) o)) else wnZo x) = _
    by_cases ho : o < x
    · rw [if_pos ho, if_pos (xf_lim_x hx ho), xf_l hx hx1, add_zero, hdNx_veb]
    · rw [if_neg ho, if_neg (fun h => ho ((lt_add_one o).trans h))]

/-- The successor step extends the start. -/
theorem xf_succ_ext (o : Ordinal.{0}) (h1 : 1 ≤ o) (hε : o < gamma 0) (U : HgVD) (h : HgSStart (hnVPB (xfQ o h1 hε)) U)
    {c : Ordinal.{0}} (hc : c < U.B) (x : Ordinal.{0}) :
    (xfPk.St0 (xfQ o h1 hε) U h).R c x = U.R c x ∧ (xfPk.St0 (xfQ o h1 hε) U h).g c = U.g c :=
  ⟨(xfPk.h0 _ U h).extR c x hc, (xfPk.h0 _ U h).extg c hc⟩

theorem xf_succ_γ (o : Ordinal.{0}) (h1 : 1 ≤ o) (hε : o < gamma 0) (U : HgVD) (h : HgSStart (hnVPB (xfQ o h1 hε)) U) :
    (xfPk.St0 (xfQ o h1 hε) U h).γ = o := (xfPk.h0 _ U h).γ

end Googology.Trans.PoR.InaccPsi.R2.Xf
