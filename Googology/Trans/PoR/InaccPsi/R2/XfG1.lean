import Googology.Trans.PoR.InaccPsi.R2.XcQ

/-!
# XfG1: THE LEVEL `G` OVER THE RAW DATUM `G`: THE SYSTEM AT `φ(G, 1)`

`G = Γ_{Ω₁+1}` is the first (A3) level and `φ(G, 0) = G` (`xf_sc_veb0`).  The generic family `Ws.wsF` cannot be
applied at the level `G` over the datum `G`: `Ws.WsGood` asks `R G x < F(x)`, here `R G x = F(x) = Γ_{x+1}`.  But
`φ(G, 1) = sup_k φ(ℓ_k, G+1)` for the `ω`-sequence `ℓ_k = Xc.xcCf k` of gate-`0` (A2) levels cofinal in `G`
(`Xc.xc_base_G`), so the gated `ω`-chain of the (A2) systems `Ws.wsV Wx.wxClsA2 ℓ_k` over `G` has the union

* `xfV1` (**THE SYSTEM AT `φ(G, 1)`**: bound `φ(G, 1)`, gate `1`, base reading `φ(Γ_{x+1}, 1)`, bound field
  `ζ`-next of it), extending `Hg.hgU` (`xfV1_ext`);

and the reading facts used by every pseudo-base of the level `G`:

* `xf_sc_veb0` (`φ(b, 0) = b` for strongly critical `b`), `xf_glA_veb` (**`ϑˣ(Ω₁·Γ_{x+1} + t) = φ(Γ_{x+1}, 1+t)`
  for every `t < Γ_{x+1}`**), `xf_veb_pi` (**Lemma EXACT for `φ(Γ_{ρ+1}, ν)` at every constant `1 ≤ ν < σ`**).

No new axiom.  New definitions: `xfD`, `xfCh`, `xfV1`.
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

/-! ## Readings at the level `G` -/

/-- **`φ(b, 0) = b` for every strongly critical `b`.** -/
theorem xf_sc_veb0 {b : Ordinal.{0}} (hb : SC b) : veblen b 0 = b := by
  have hE : InE b := Low.opow_eq_self_of_SC hb
  have hb0 : b ≠ 0 := hb.1.ne'
  have hmem : b ∈ Set.range (veblen b) := by
    refine (mem_range_veblen hb0).2 (fun c hc => ?_)
    rcases eq_or_ne c 0 with rfl | hc0
    · rw [veblen_zero_apply]; exact hE
    · exact gn_veb_fix hb hc
  obtain ⟨a, ha⟩ := hmem
  rcases eq_or_ne a 0 with rfl | ha0
  · exact ha
  · exfalso
    have h1 := (isNormal_veblen b).strictMono (pos_iff_ne_zero.2 ha0)
    rw [ha] at h1
    exact absurd ((left_le_veblen b 0).trans_lt h1) (lt_irrefl _)

theorem xf_G_veb0 : veblen (gcG 0) 0 = gcG 0 := xf_sc_veb0 (gcG_SC 0)

theorem xf_G_LuP : LuP (gcG 0) (gcG 0) := ⟨0, xf_G_veb0⟩

theorem xf_G_lim : IsSuccLimit (gcG 0) := ev_isSuccLimit_of_inE gl_G0_E

theorem xf_one_lt_G : (1 : Ordinal.{0}) < gcG 0 := wh_one_lt_Om1.trans gl_Om1_lt_G0

/-- `hdNx G G = φ(G, 1)`. -/
theorem xf_NG : hdNx (gcG 0) (gcG 0) = veblen (gcG 0) 1 := by
  have h := hdNx_veb (gcG 0) 0
  rwa [xf_G_veb0, zero_add] at h

section X

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem xf_Gx_LuP : LuP (lgG x) (lgG x) := ⟨0, he_G_sc hx hx1⟩

theorem xf_one_lt_Gx : (1 : Ordinal.{0}) < lgG x := (wo_one_lt_inE hx).trans (lgG_facts hx hx1).2.1

/-- `hdNx Γ_{x+1} Γ_{x+1} = φ(Γ_{x+1}, 1)`. -/
theorem xf_NGx : hdNx (lgG x) (lgG x) = veblen (lgG x) 1 := by
  have h := hdNx_veb (lgG x) 0
  rwa [he_G_sc hx hx1, zero_add] at h

/-- **`ϑˣ(Ω₁·Γ_{x+1} + t) = φ(Γ_{x+1}, 1 + t)` for every `t < Γ_{x+1}`.** -/
theorem xf_glA_veb : ∀ t, t < lgG x → glA (lgG x) t x = veblen (lgG x) (1 + t) := by
  obtain ⟨hGT, hxG, hG1, -, -⟩ := lgG_facts hx hx1
  have hG1' : (1 : Ordinal.{0}) ≤ lgG x := (xf_one_lt_Gx hx hx1).le
  have hsc := he_G_sc hx hx1
  have hpos : ∀ s, lgG x < veblen (lgG x) (1 + s) := fun s => by
    conv_lhs => rw [← hsc]
    exact (isNormal_veblen _).strictMono (zero_lt_one.trans_le le_self_add)
  intro t
  induction t using WellFoundedLT.induction with
  | ind t IH =>
  intro ht
  obtain ⟨htT, ht1⟩ := gl_T_of_lt_G hx hx1 ht
  have hF := glA_facts hx hx1 hG1' hGT hG1 htT ht1
  obtain ⟨i, hi⟩ := glA_P hx hx1 hG1' hGT hG1 htT ht1
  apply le_antisymm
  · refine glA_min hx hx1 hG1' hGT hG1 htT ht1 ⟨1 + t, rfl⟩ (hxG.trans (hpos t)) (ht.trans (hpos t)) (hpos t)
      (fun σ hσ => ?_)
    rw [IH σ hσ (hσ.trans ht)]
    exact (isNormal_veblen _).strictMono ((add_lt_add_iff_left 1).2 hσ)
  · rw [← hi]
    apply (isNormal_veblen _).monotone
    refine le_of_forall_lt (fun s hs => ?_)
    have hi0 : 0 < i := by
      rcases eq_or_ne i 0 with h0 | h0
      · exfalso
        have h5 := hF.2.2.2.2.1
        rw [← hi, h0, hsc] at h5
        exact lt_irrefl _ h5
      · exact pos_iff_ne_zero.2 h0
    rcases eq_or_ne s 0 with rfl | hs0
    · exact hi0
    · have h1s : (1 : Ordinal.{0}) ≤ s := one_le_iff_ne_zero.2 hs0
      have hss : 1 + (s - 1) = s := Ordinal.add_sub_cancel_of_le h1s
      have hs' : s - 1 < t := by
        rw [← hss] at hs; exact (add_lt_add_iff_left 1).1 hs
      obtain ⟨hsT, hs1⟩ := gl_T_of_lt_G hx hx1 (hs'.trans ht)
      have h := glA_lt_of hx hx1 hG1' hGT hG1 hsT htT ht1 hs'
      rw [IH (s - 1) hs' (hs'.trans ht), ← hi] at h
      have h' := (isNormal_veblen (lgG x)).strictMono.lt_iff_lt.1 h
      rwa [hss] at h'

end X

/-- **Lemma EXACT for `φ(Γ_{ρ+1}, ν)` at every constant `1 ≤ ν < σ`.** -/
theorem xf_veb_pi {σ ρ ν : Ordinal.{0}} (hB : Bases σ ρ) (h1 : 1 ≤ ν) (hν : ν < σ) :
    veblen (lgG ρ) ν ∈ TB ρ σ ∧ pi σ ρ (veblen (lgG ρ) ν) = veblen (lgG σ) ν := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  have hss : 1 + (ν - 1) = ν := Ordinal.add_sub_cancel_of_le h1
  have htσ : ν - 1 < σ := (Ordinal.sub_le_self _ _).trans_lt hν
  have htGσ : ν - 1 < lgG σ := htσ.trans (lgG_facts hB.1 hσ1).2.1
  have htGρ : ν - 1 < lgG ρ := (htσ.trans hB.2.2.1).trans (lgG_facts hB.2.1 hρ1).2.1
  obtain ⟨g1, g2⟩ : lgG ρ ∈ TB ρ σ ∧ pi σ ρ (lgG ρ) = lgG σ := goGl.ba_pi σ ρ hB
  have h := glA_pi hB g1 (lgG_facts hB.2.1 hρ1).2.2.1 (mem_TB_of_lt hB htσ) (htσ.trans hσ1)
  rw [g2, pi_lt hB htσ, xf_glA_veb hB.2.1 hρ1 _ htGρ, xf_glA_veb hB.1 hσ1 _ htGσ, hss] at h
  exact h

/-! ## The `ω`-sequence of (A2) levels cofinal in `G` -/

theorem xf_cf_Om (k : ℕ) : Om1 < xcCf k := Om1_lt_eW.trans_le ((glBn_spec k).2.2.2.2.1 k).1

theorem xf_cf_lt (k : ℕ) : xcCf k < gcG 0 := ((glBn_spec k).2.2.2.2.1 k).2.1.trans (glBn_spec k).1

theorem xf_cf_lev (k : ℕ) : wsA2.Lev (xcCf k) :=
  ⟨(xf_cf_Om k).le, wp_Om1_dvd_E (xc_cfn_E k k) (xf_cf_Om k), xf_cf_lt k⟩

theorem xf_cf_mono (k : ℕ) : xcCf k < xcCf (k + 1) :=
  ((glBn_spec k).2.2.2.2.1 k).2.2.2.trans_le (xc_cfn_le_succ k (k + 1))

theorem xf_cf_cof {t : Ordinal.{0}} (ht : t < gcG 0) : ∃ k, t < xcCf k := by
  obtain ⟨n, hn⟩ := glBn_cof ht
  obtain ⟨k, hk⟩ := (glBn_spec n).2.2.2.2.2 t hn
  exact ⟨max n k, hk.trans_le ((xc_cfn_mono_n (le_max_left n k) k).trans (xc_cfn_mono_k _ (le_max_right n k)))⟩

theorem xf_cf_gh (k : ℕ) : gh (xcCf k) = 1 := by
  show max 1 (glG (glCfn k k)) = 1
  rw [((glBn_spec k).2.2.2.2.1 k).2.2.1, max_eq_left zero_le]

theorem xf_cf_g (k : ℕ) : max (wsG wsA2).γ (wsA2.g (xcCf k)) = 1 := by
  show max (0 : Ordinal.{0}) (gh (xcCf k)) = 1
  rw [xf_cf_gh, max_eq_right zero_le]

/-- **`G` as a level of `xcA3`**, gate `1`. -/
theorem xf_lev_G : xcA3.Lev (gcG 0) := ⟨gl_Om1_lt_G0.le, wp_Om1_dvd_E gl_G0_E gl_Om1_lt_G0, xc_G_lt_t0⟩

theorem xf_xg_G : xg (gcG 0) = 1 := by unfold xg; rw [wtD_gG, max_eq_left zero_le]

/-! ## The chain -/

/-- The (A2) system over `G` at the level `ℓ_k`. -/
noncomputable def xfD (k : ℕ) : HgVD := wsF wxClsA2 (xcCf k) (wsG wsA2) hgU

theorem xfD_M (k : ℕ) : WsSh wsA2 (wsG wsA2) (xcCf k) (xfD k) ∧
    (∀ c x, c < hgU.B → (xfD k).R c x = hgU.R c x ∧ (xfD k).g c = hgU.g c) ∧
      WsSm wsA2 (wsG wsA2) (xcCf k) hgU (xfD k) :=
  (wsFam wxClsA2 (xcCf k) (xf_cf_lev k) (xf_cf_lt k)).1 _ _ (wsGood_G wsA2_G (xf_cf_lev k)) (wsSh_hgU wsA2_G)

theorem xfD_ext (k : ℕ) (c x : Ordinal.{0}) (hc : c < (xfD k).B) :
    (xfD (k + 1)).R c x = (xfD k).R c x ∧ (xfD (k + 1)).g c = (xfD k).g c :=
  (wsFam wxClsA2 (xcCf (k + 1)) (xf_cf_lev (k + 1)) (xf_cf_lt (k + 1))).2 (xcCf k) (xf_cf_mono k)
    (xf_cf_lev k) _ _ (wsGood_G wsA2_G (xf_cf_lev (k + 1))) (wsSh_hgU wsA2_G) c x hc

theorem xfD_B (k : ℕ) : (xfD k).B = hdNx (xcCf k) (gcG 0) := (xfD_M k).1.1

theorem xf_b1_le_Zo {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : veblen (lgG x) 1 ≤ wnZo x := by
  rw [← xf_NGx hx hx1]; unfold wnZo; rw [wn_lgG_max hx hx1]
  exact hdNx_mono le_self_add _

/-- **THE GATED `ω`-CHAIN OF THE (A2) SYSTEMS OVER `G` AT `ℓ_k`**: bound `φ(G, 1)`. -/
noncomputable def xfCh : HgfCh where
  D := xfD
  B := veblen (gcG 0) 1
  b := fun x => veblen (lgG x) 1
  γ := 1
  Zo := wnZo
  γ_lt := wh_one_lt_Om1
  γ0 := fun k => (xfD_M k).1.2.1.2.trans (xf_cf_g k).le
  γ_cl := fun _ hZ _ _ => xc_one_lt_SC hZ
  B_mono := fun k => by rw [xfD_B, xfD_B]; exact hdNx_mono (xf_cf_mono k).le _
  B_lt := fun k => by rw [xfD_B, ← xf_NG]; exact ws_N_lt (C := xcA3) xf_lev_G xf_G_LuP (xf_cf_lt k)
  B_cof := fun c hc => by
    rw [← xf_NG] at hc
    obtain ⟨b, hb, hcb⟩ := hjw_Nx_cof (gcG_SC 0).1.ne' xf_G_LuP hc
    obtain ⟨k, hk⟩ := xf_cf_cof (xf_G_lim.add_one_lt hb)
    exact ⟨k, by rw [xfD_B]; exact hcb.trans (hdN_lt_Nx hk)⟩
  R_ext := fun k c x hc => (xfD_ext k c x hc).1
  g_ext := fun k c hc => (xfD_ext k c 0 hc).2
  B_lt1 := by
    have hfix : veblen (gcG 0) (gcG 1) = gcG 1 := gn_veb_fix (gcG_SC 1) (gcG_lt zero_lt_one)
    calc veblen (gcG 0) 1 < veblen (gcG 0) (gcG 1) :=
          (isNormal_veblen _).strictMono (xc_one_lt_SC (gcG_SC 1))
      _ = gcG 1 := hfix
  B_fix := by rw [← xf_NG]; exact hdNx_fix xf_one_lt_G _
  B_mem := fun S _ _ ha _ => CSet.phi_mem (gmS_G0_mem S ha) (CSet.one_mem _ _)
  b_ge := fun k x hx hx1 hγ => by
    have hg : max (wsG wsA2).γ (wsA2.g (xcCf k)) < x := by rw [xf_cf_g]; exact hγ
    rw [(xfD_M k).1.2.2.2.1 x hx hx1 hg, ← xf_NGx hx hx1]
    exact hdNx_mono (wsA2_G.R_lt hx hx1 (xf_cf_lt k) (max_lt_iff.1 hg).2).le _
  b_cof := fun x hx hx1 hγ ν hν => by
    rw [← xf_NGx hx hx1] at hν
    obtain ⟨b, hb, hνb⟩ := hjw_Nx_cof (zero_lt_one.trans (xf_one_lt_Gx hx hx1)).ne' (xf_Gx_LuP hx hx1) hν
    have hgG : xcA3.g (gcG 0) < x := by rw [xcA3_g, xf_xg_G]; exact hγ
    obtain ⟨t, ht, hgt, hbt⟩ := xcA3.R_cof hx hx1 xc_G_lt_t0 hgG b (by rw [xcA3_R, wtD_RG]; exact hb)
    obtain ⟨k, hk⟩ := xf_cf_cof (xf_G_lim.add_one_lt ht)
    have hgk : max (wsG wsA2).γ (wsA2.g (xcCf k)) < x := by rw [xf_cf_g]; exact hγ
    have hgt' : wsA2.g t < x := by show gh t < x; rw [← xg_low ht]; exact hgt
    have hbt' : b ≤ wsA2.R t x := by
      show b ≤ glR t x; rw [← xcR_low ht x]; exact hbt
    have hlt' : wsA2.R t x + 1 < wsA2.R (xcCf k) x :=
      WsC.R_succ_lt hx hx1 (xf_cf_lt k) hk (max_lt_iff.1 hgk).2 hgt'
    refine ⟨k, ?_⟩
    rw [(xfD_M k).1.2.2.2.1 x hx hx1 hgk]
    exact hνb.trans (hdN_lt_Nx ((add_le_add hbt' le_rfl).trans_lt hlt'))
  b_fix := fun x hx hx1 _ => by rw [← xf_NGx hx hx1]; exact hdNx_fix (xf_one_lt_Gx hx hx1) _
  b_gt := fun x hx hx1 _ => (lgG_facts hx hx1).2.1.trans (by rw [← xf_NGx hx hx1]; exact hdNx_gt _ _)
  b_lt := fun x hx hx1 _ => (xf_b1_le_Zo hx hx1).trans_lt (wnZo_G1 hx hx1)
  b_pi := fun σ ρ hB _ => xf_veb_pi hB le_rfl (wo_one_lt_inE hB.1)
  Z_low := fun _ x hx _ hγ => absurd (wo_one_lt_inE hx) hγ
  Zo_fix := fun x => hc_fix_down one_le_two (wnZo_fix x)
  Zo_G1 := fun x hx hx1 => wnZo_G1 hx hx1

/-- **THE SYSTEM AT `φ(G, 1)`**: the union of the (A2) systems over `G` at the levels `ℓ_k`; gate `1`, base
reading `φ(Γ_{x+1}, 1)`. -/
noncomputable def xfV1 : HgVD := xfCh.U

theorem xfV1_B : xfV1.B = veblen (gcG 0) 1 := rfl

theorem xfV1_γ : xfV1.γ = 1 := rfl

theorem xfV1_ix : xfV1.ix = veblen (gcG 0) 1 := rfl

theorem xfV1_b (x : Ordinal.{0}) : xfV1.b x = veblen (lgG x) 1 := rfl

theorem xfV1_Z (x : Ordinal.{0}) :
    xfV1.Z x = if (1 : Ordinal.{0}) < x then evZ (veblen (lgG x) 1) else wnZo x := xfCh.U_Z x

/-- **`xfV1` extends `Hg.hgU`** (the system at `φ(Ω₁, G+1)`). -/
theorem xfV1_ext {c : Ordinal.{0}} (hc : c < hgU.B) (x : Ordinal.{0}) :
    xfV1.R c x = hgU.R c x ∧ xfV1.g c = hgU.g c := by
  have hc0 : c < (xfCh.D 0).B := hc.trans_le (ws_S1_le (xf_cf_lev 0) (wsSh_hgU wsA2_G) (xfD_M 0).1)
  show xfCh.U.R c x = _ ∧ xfCh.U.g c = _
  rw [xfCh.U_R hc0, xfCh.U_g hc0]; exact (xfD_M 0).2.1 c x hc

/-- **`xfV1` lies above every (A2) system over `G`**: `φ(ℓ, G+1) < φ(G, 1)` for every `ℓ < G`. -/
theorem xfV1_cover {ℓ : Ordinal.{0}} (hℓ : ℓ < gcG 0) : veblen ℓ (gcG 0 + 1) < xfV1.B := by
  rw [xfV1_B, ← xf_NG, ← hdNx_fixP (gn_veb_fix (gcG_SC 0) hℓ)]
  exact ws_N_lt (C := xcA3) xf_lev_G xf_G_LuP hℓ

end Googology.Trans.PoR.InaccPsi.R2.Xf
