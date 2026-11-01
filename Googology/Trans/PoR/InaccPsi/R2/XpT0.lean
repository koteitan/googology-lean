import Googology.Trans.PoR.InaccPsi.R2.XpRec

/-!
# XpT0: THE LEVEL `t₀ = ε_{G+1}` FROM THE BOTTOM UP TO THE OFFSET `G`, AND `Wn.WnEnt3 S 0`

* `xpTwCh` (**THE `ω`-CHAIN OF THE TOWER BANDS** `xpSys (G^{⋯^G})`: bound `φ(t₀, 0)`, gate `1`, base reading
  `φ(ε_{Γ_{x+1}+1}, 0)`), `xpV0` (its union), `xp_at_t0` (**A SYSTEM AT THE BOTTOM `φ(t₀, 0)` OF THE DATUM OF `t₀`
  WITH GATE `1`**, `Xc.xcLvT0`);
* `xpBT0` (the basic band datum of `t₀`: the package `Wm.wmPkL Xc.xcSeqT0`, i.e. the step of `Xc.xcPkT0`),
  `xpVT l` (**THE STAGE AT THE OFFSET `l` OF THE LEVEL `t₀`**, the bottom recursion `Xl.xlU`), `xpVT_B`;
* `xpQG` (the pseudo-base `φ(t₀, G)` of the recursion, gate `1`), `xpEnt3` (**`Wn.WnEnt3 S 0`, UNCONDITIONAL**: the
  skeleton node `skSysA3Lev0W` with no open hypothesis);
* `xpT0_sys` (the system at `φ(t₀, G + 1)` with gate `< K`), `xpT0_loc` (**THE FRONTIER
  `ι(Γ(φ(t₀, G+1))·ω)` IS LOCATED**), `xpT0_enum`, `xpT0_capV`, `xpT0_sysG`, `XpT0Past`, `xpT0Hyp_iff` (the four frontier
  hypotheses past the new frontier ⇔ past `ι(Γ(φ(G + Ω₁, 0))·ω)`), `xpT0RoadZ` / `xpT0Road_vac`.

No new axiom.  New definitions: `xpTwCh`, `xpV0`, `xpBT0`, `xpVT`, `xpQG`, `XpT0Past`.
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

open Googology.Trans.PoR.InaccPsi.R2.Xl
open Googology.Trans.PoR.InaccPsi.R2.Xp

namespace Googology.Trans.PoR.InaccPsi.R2.Xp

/-! ## The tower bands and the bottom `φ(t₀, 0)` -/

theorem xp_lv_tw (n : ℕ) : XpLv (wtTw n) := ⟨wtTw_G n, wtTw_dvd n, wtTw_lt n⟩

theorem xp_xg_tw (n : ℕ) : xg (wtTw n) = 1 := xg_tw n

theorem xp_tw_g_lt {x : Ordinal.{0}} (hx : InE x) (n : ℕ) : xg (wtTw n) < x := by
  rw [xp_xg_tw]; exact wo_one_lt_inE hx

theorem xp_tw_R {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (n : ℕ) :
    xcA3.R (wtTw n) x = (wtTwLv n).l x := (wtTwLv_l n hx hx1).symm

theorem xp_tw_R_lt {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (n : ℕ) :
    xcA3.R (wtTw n) x < wnLv3T0.l x := by
  rw [wnLv3T0_l hx hx1]
  exact goGl.hR_lt_eNb hx hx1 (wt_LB (wtTw_lt n)) ((xg_lt_iff hx).1 (xp_tw_g_lt hx n))

theorem xp_t0_E : InE (Wj.wjT 0) := xc_t0_E

theorem xp_one_lt_t0 : (1 : Ordinal.{0}) < Wj.wjT 0 := xf_one_lt_G.trans xc_G_lt_t0

theorem xp_a_lim {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : IsSuccLimit (wnLv3T0.l x) :=
  ev_isSuccLimit_of_inE (xp_aE hx hx1)

/-- **The basic band datum of `t₀`**: the package `Wm.wmPkL Xc.xcSeqT0` (datum `Wy.wyLv Xc.xcLvT0`: level `t₀`,
reading `ε_{Γ_{x+1}+1}`, gate `1`). -/
noncomputable def xpBT0 : XpBd0 where
  K := wmPkL xcSeqT0
  G_lt := xc_G_lt_t0
  l_nsc := fun x hx hx1 _ => by
    show wnLv3T0.l x < veblen (wnLv3T0.l x) 0
    rw [wnLv3T0_l hx hx1]; exact xp_eN_nsc _

theorem xpBT0_L : xpBT0.K.Λ.L = Wj.wjT 0 := rfl

theorem xpBT0_g : xpBT0.K.Λ.g = 1 := rfl

theorem xpBT0_l (x : Ordinal.{0}) : xpBT0.K.Λ.l x = wnLv3T0.l x := rfl

/-- **Lemma EXACT for `φ(ε_{Γ_{ρ+1}+1}, 0)`.** -/
theorem xp_a_pi {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) :
    veblen (wnLv3T0.l ρ) 0 ∈ TB ρ σ ∧ pi σ ρ (veblen (wnLv3T0.l ρ) 0) = veblen (wnLv3T0.l σ) 0 := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  have h0σ : (0 : Ordinal.{0}) < σ := hB.1.pos
  have h1σ : (1 : Ordinal.{0}) < σ := wo_one_lt_inE hB.1
  have h := hnv_glA_pi xpBT0.K.Λ (ν := 0) hB h1σ h0σ (mem_TB_of_lt hB h0σ) (gm1_facts hB.2.1 hρ1).2.2.2.pos
  rw [pi_lt hB h0σ, xp_glA xpBT0 hB.2.1 hρ1 (h1σ.trans hB.2.2.1) hB.2.1.pos 0 (hcN_E _ _).pos,
    xp_glA xpBT0 hB.1 hσ1 h1σ h0σ 0 (hcN_E _ _).pos, add_zero, add_zero] at h
  exact h

/-- **THE `ω`-CHAIN OF THE TOWER BANDS** `xpSys (wtTw k)`: bound `φ(t₀, 0)`, gate `1`, base reading
`φ(ε_{Γ_{x+1}+1}, 0)`. -/
noncomputable def xpTwCh : HgfCh where
  D := fun k => xpSys (wtTw k)
  B := veblen (Wj.wjT 0) 0
  b := fun x => veblen (wnLv3T0.l x) 0
  γ := 1
  Zo := xpZ
  γ_lt := wh_one_lt_Om1
  γ0 := fun k => (xpSys_γ (xp_lv_tw k)).trans (xp_xg_tw k).le
  γ_cl := fun _ hZ _ _ => xc_one_lt_SC hZ
  B_mono := fun k => by
    rw [xpSys_B (xp_lv_tw k), xpSys_B (xp_lv_tw (k + 1))]
    exact veblen_zero_le_veblen_zero.2 (wtTw_strict k).le
  B_lt := fun k => by
    rw [xpSys_B (xp_lv_tw k)]; exact veblen_zero_lt_veblen_zero.2 (wtTw_lt k)
  B_cof := fun c hc => by
    obtain ⟨a, ha, hca⟩ := wx_veb_lim_cof0 (ev_isSuccLimit_of_inE xp_t0_E) hc
    obtain ⟨k, hk⟩ := wtTowSeq.2.2.1 a ha
    refine ⟨k, ?_⟩
    rw [xpSys_B (xp_lv_tw k)]
    exact hca.trans (veblen_zero_lt_veblen_zero.2 hk)
  R_ext := fun k c x hc => (xpSys_ext (xp_lv_tw (k + 1)) (wtTw_strict k) (xp_lv_tw k) c x hc).1
  g_ext := fun k c hc => (xpSys_ext (xp_lv_tw (k + 1)) (wtTw_strict k) (xp_lv_tw k) c 0 hc).2
  B_lt1 := by
    have h := (isNormal_veblen (Wj.wjT 0)).strictMono (gcG_SC 1).1
    rwa [gn_veb_fix (gcG_SC 1) xp_t0_lt1] at h
  B_fix := veblen_veblen_of_lt xp_one_lt_t0 0
  B_mem := fun S _ _ ha hb => CSet.phi_mem (xcLvT0.L_mem S _ _ ha hb) (CSet.zero_mem _ _)
  b_ge := fun k x hx hx1 _ => by
    rw [xpSys_b (xp_lv_tw k) hx hx1 (xp_tw_g_lt hx k)]
    exact (veblen_zero_lt_veblen_zero.2 (xp_tw_R_lt hx hx1 k)).le
  b_cof := fun x hx hx1 _ ν hν => by
    obtain ⟨a, ha, hνa⟩ := wx_veb_lim_cof0 (xp_a_lim hx hx1) hν
    obtain ⟨k, hk⟩ := wtTowSeq.2.2.2.2 x hx hx1 a ha
    refine ⟨k, ?_⟩
    rw [xpSys_b (xp_lv_tw k) hx hx1 (xp_tw_g_lt hx k), xp_tw_R hx hx1 k]
    exact hνa.trans (veblen_zero_lt_veblen_zero.2 hk)
  b_fix := fun x hx hx1 _ => veblen_veblen_of_lt ((wo_one_lt_inE hx).trans (xp_x_lt_a hx hx1)) 0
  b_gt := fun x hx hx1 _ => (xp_x_lt_a hx hx1).trans_le (left_le_veblen _ 0)
  b_lt := fun x hx hx1 _ => by
    refine lt_of_lt_of_le ?_ (xpZ_G1 hx hx1).le
    rw [xpZ_eq hx, xl_N_eq]; exact veblen_zero_lt_veblen_zero.2 (lt_add_one _)
  b_pi := fun _ _ hB _ => xp_a_pi hB
  Z_low := fun _ x hx _ h => absurd (wo_one_lt_inE hx) h
  Zo_fix := xpZ_fix1
  Zo_G1 := fun _ hx hx1 => xpZ_G1 hx hx1

/-- **THE SYSTEM AT `φ(t₀, 0)`**: the union of the tower bands; gate `1`. -/
noncomputable def xpV0 : HgVD := xpTwCh.U

theorem xpV0_B : xpV0.B = veblen (Wj.wjT 0) 0 := rfl

theorem xpV0_γ : xpV0.γ = 1 := rfl

/-- **`xpV0` IS A SYSTEM AT THE BOTTOM OF THE DATUM OF `t₀`** (`Xc.xcLvT0`, gate `1`). -/
theorem xp_at_t0 : XpAt xpBT0.K.Λ 0 xpV0 where
  B := by show veblen (Wj.wjT 0) 0 = veblen (Wj.wjT 0 + 0) 0; rw [add_zero]
  ix := by show veblen (Wj.wjT 0) 0 = veblen (Wj.wjT 0 + 0) 0; rw [add_zero]
  γ := fun x _ _ => by rw [xpV0_γ, xpBT0_g, max_eq_right zero_le]
  b := fun x _ _ _ => by show veblen (wnLv3T0.l x) 0 = veblen (wnLv3T0.l x + 0) 0; rw [add_zero]
  γ_le := by rw [xpV0_γ, xpBT0_g, max_eq_right zero_le]
  Z := fun x _ _ => by
    rw [show xpV0.Z x = if (1 : Ordinal.{0}) < x then evZ (veblen (wnLv3T0.l x) 0) else xpZ x from xpTwCh.U_Z x,
      xpBT0_g, max_eq_right zero_le, xpBT0_l, add_zero]

/-- **`xpV0` extends every tower band, hence `Hg.hgU`.** -/
theorem xpV0_ext (k : ℕ) {c : Ordinal.{0}} (hc : c < (xpSys (wtTw k)).B) (x : Ordinal.{0}) :
    xpV0.R c x = (xpSys (wtTw k)).R c x ∧ xpV0.g c = (xpSys (wtTw k)).g c :=
  ⟨xpTwCh.U_R (k := k) hc x, xpTwCh.U_g (k := k) hc⟩

/-! ## The offsets of the level `t₀` up to `G` -/

theorem xp_t0_zero : (0 : Ordinal.{0}) < Om1 := gv_Om1_pos

/-- **THE STAGE AT THE OFFSET `l` OF THE LEVEL `t₀`** (the bottom recursion `Xl.xlU` over `xpV0`). -/
noncomputable def xpVT (l : Ordinal.{0}) : HgVD :=
  xlU (xpSt xpBT0 0) (xpBK xpBT0 0 xp_t0_zero) xpV0 l

theorem xpVT_start0 : XlStart (xpBK xpBT0 0 xp_t0_zero) xpV0 := xp_start_of_at xpBT0 xp_t0_zero xp_at_t0

theorem xp_G_lt_Nt0 : gcG 0 < hcN (xpBT0.K.Λ.L + 0) 0 := by
  rw [add_zero, xl_N_eq]
  exact xc_G_lt_t0.trans_le ((le_add_right le_rfl).trans (left_le_veblen _ 0))

/-- **THE STAGE AT THE OFFSET `l < N_{t₀}(0)` IS A SYSTEM AT `φ(t₀, l)`.** -/
theorem xpVT_B {l : Ordinal.{0}} (hl : l < hcN (xpBT0.K.Λ.L + 0) 0) : (xpVT l).B = veblen (Wj.wjT 0) l := by
  have h := xlU_B (xpSt_spec xpBT0 xp_t0_zero) xpVT_start0 hl
  rw [xpBK_e, zero_add, add_zero] at h; exact h

theorem xpVT_gG : (xpVT (gcG 0)).g (gcG 0) = 0 :=
  (xpVT (gcG 0)).g_G0 (by rw [xpVT_B xp_G_lt_Nt0]; exact (xf_G_veb0.symm.trans_lt
    ((veblen_zero_lt_veblen_zero.2 xc_G_lt_t0).trans_le ((isNormal_veblen _).monotone zero_le))))

/-- **THE PSEUDO-BASE `φ(t₀, G)` OF THE RECURSION** (gate `1`). -/
noncomputable def xpQG : HnVQ xpBT0.K.Λ 0 :=
  xlOff (xpBK xpBT0 0 xp_t0_zero) (xpVT (gcG 0)) (gcG 0)
    (xlU_self (xpSt_spec xpBT0 xp_t0_zero) xpVT_start0 xp_G_lt_Nt0) xp_G_lt_Nt0
    (xlU_Zb (xpSt_spec xpBT0 xp_t0_zero) xpVT_start0 xp_G_lt_Nt0)

theorem xpQG_F : xpQG.F = veblen (Wj.wjT 0) (gcG 0) := by
  show veblen (Wj.wjT 0 + 0) ((((xpBK xpBT0 0 xp_t0_zero).e : ℕ) : Ordinal.{0}) + gcG 0) = _
  rw [xpBK_e, zero_add, add_zero]

theorem xpQG_γ : xpQG.γ = 1 := by
  show max (max 0 xpBT0.K.Λ.g) ((xpVT (gcG 0)).g (gcG 0)) = 1
  rw [xpVT_gG, xpBT0_g, max_eq_right zero_le, max_eq_left zero_le]

/-- **THE STAGE `φ(t₀, G)` STARTS THE PSEUDO-BASE `φ(t₀, G)`.** -/
theorem xpQG_start : HgSStart (hnVPB xpQG) (xpVT (gcG 0)) :=
  xlU_start (xpSt_spec xpBT0 xp_t0_zero) xpVT_start0 xp_G_lt_Nt0

/-- **`Wn.WnEnt3 S 0`, UNCONDITIONAL**: the package `Xc.xcPkT0` at `t₀`, the pseudo-base `φ(t₀, G)` (gate `1`) and
the system `φ(t₀, G)` starting it. -/
theorem xpEnt3 (S : InaccSeq.{0}) : WnEnt3 S 0 :=
  ⟨xcPkT0, rfl, xc_one_lt_SC Td.tdK_SC, wyQ3 xpQG, xpVT (gcG 0), xpQG_start, xpQG_F,
    by rw [wyQ3_γ, xpQG_γ]; exact xc_one_lt_SC Td.tdK_SC⟩

end Googology.Trans.PoR.InaccPsi.R2.Xp
