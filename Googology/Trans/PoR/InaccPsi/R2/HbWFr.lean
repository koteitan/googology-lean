import Googology.Trans.PoR.InaccPsi.R2.HbRec

/-!
# HbWFr: THE FRONTIER `ι(Γ(φ(ω, G+1)))` AND THE WALL THERE

The chain `hbTG k` (bound `N_{k+2}(G) = φ(k+3, G+1)`, base gate `0`) is cofinal in `φ(ω, G+1) = sup_k N_k(G)`
(`hbTw`, `hbTw_eq`), so every `φ(k+3, G+1)` is located (`hbTG_loc`) and **the new frontier is `ι(Γ(φ(ω, G+1)))`**
(was `ι(Γ(φ(3, G+1)))`): ENUM-REACH and CapV at every range restart below it, BLK^O and exact reaches below each
located bound, unconditionally; the road asks UPPER, LOWER, CapV only above it.  The code `N_{k+2}(G)` is read in
`hbTG (k+1)` as `N_{k+2}(Γ_{x+1})` with gate `0` (`hbTG_read`), so these readings are cofinal in `B_ω(x)`, and no
`HbVD` extending the chain reads `φ(ω, G+1)` with its gate below a base (`hb_wall_Tw`): the bound field
`Z(x) ≤ B_ω(x)` stops there.

* `hbTw`, `hbTw_veb`, `hbTw_eq` (**`sup_k N_k(G) = φ(ω, G+1)`**), `hbN_lt_Tw`, `hbTw_lt_G1`, `hbTG_K`, `hbTG_loc`,
  `hbTw_codes`, `hbTw_iota_cof`, `hbTw_enum`, `hbTw_capV`, `hbTw_blk`, `hbTw_road` (**THE ROAD**), `hbTw_le_Om2`,
  `hbTw_P`, `hbTw_fr_order`, `hbTG_read`, `hb_wall_Tw` (**THE WALL**).

No new axiom.  New definition: `hbTw`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hb

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

/-! ## `φ(ω, G+1)` -/

/-- **`sup_k N_k(G)`**, the least common fixed point of every `φ(k, ·)`, `k < ω`, above `G`. -/
noncomputable def hbTw : Ordinal.{0} := ⨆ k : ℕ, hbN k (gcG 0)

theorem hbTw_bdd : BddAbove (Set.range fun k : ℕ => hbN k (gcG 0)) := Ordinal.bddAbove_range _

theorem hbN_le_Tw (k : ℕ) : hbN k (gcG 0) ≤ hbTw := le_ciSup hbTw_bdd k

theorem hbN_lt_Tw (k : ℕ) : hbN k (gcG 0) < hbTw := (hbN_lt_succ k _).trans_le (hbN_le_Tw (k + 1))

/-- **`φ(ω, G+1)` is a fixed point of every `φ(k, ·)`, `k < ω`.** -/
theorem hbTw_veb (k : ℕ) : veblen (k : Ordinal.{0}) hbTw = hbTw := by
  unfold hbTw
  rw [(isNormal_veblen (k : Ordinal.{0})).map_iSup hbTw_bdd]
  refine le_antisymm (Ordinal.iSup_le fun n => ?_) (Ordinal.iSup_le fun n => ?_)
  · have h1 : veblen (k : Ordinal.{0}) (hbN n (gcG 0)) ≤ veblen (k : Ordinal.{0}) (hbN (n + k) (gcG 0)) :=
      (isNormal_veblen _).monotone (hbN_mono (Nat.le_add_right n k) _)
    rw [hb_fix_down (Nat.le_add_left k n) (hbN_fix (n + k) (gcG 0))] at h1
    exact h1.trans (Ordinal.le_iSup (fun n => hbN n (gcG 0)) (n + k))
  · exact (right_le_veblen _ _).trans (Ordinal.le_iSup (fun n => veblen (k : Ordinal.{0}) (hbN n (gcG 0))) n)

theorem hb_G_veb_w : veblen ω (gcG 0) = gcG 0 := gn_veb_fix (gcG_SC 0) (omega0_lt_inE gr_G_inE)

/-- **`sup_k N_k(G) = φ(ω, G+1)`.** -/
theorem hbTw_eq : hbTw = veblen ω (gcG 0 + 1) := by
  refine le_antisymm (Ordinal.iSup_le fun k => hbN_le k (veblen_veblen_of_lt (natCast_lt_omega0 k) _)
    ((lt_add_one _).trans_le (right_le_veblen _ _))) ?_
  obtain ⟨b, hb⟩ := (mem_range_veblen omega0_ne_zero).2 (fun k hk => by
    obtain ⟨n, rfl⟩ := lt_omega0.1 hk; exact hbTw_veb n)
  rw [← hb]
  refine (isNormal_veblen ω).monotone (Order.add_one_le_of_lt ?_)
  have h : veblen ω (gcG 0) < veblen ω b := by
    rw [hb, hb_G_veb_w]; exact (hbN_gt 0 _).trans (hbN_lt_Tw 0)
  exact (isNormal_veblen ω).strictMono.lt_iff_lt.1 h

theorem hbTw_lt_G1 : hbTw < gcG 1 := by
  rw [hbTw_eq]
  have hG1 := gcG_SC 1
  exact hG1.2 ω (omega0_lt_inE (Low.opow_eq_self_of_SC hG1)) _ (hG1.add_one_lt (gcG_lt zero_lt_one))

theorem hbTw_E : InE hbTw := by have h := hbTw_veb 0; rw [Nat.cast_zero, veblen_zero_apply] at h; exact h

theorem hbTw_lim : IsSuccLimit hbTw := ev_isSuccLimit_of_inE hbTw_E

/-! ## Location -/

theorem hbTG_K (S : InaccSeq.{0}) (k : ℕ) : (hbTG k).1.γ < Td.tdK S := by
  rw [hbTG_γ]; exact Td.tdK_SC.1

/-- **`φ(k+3, G+1)` IS LOCATED** for every `k`: `Λ⁺ = ι(Γ(N_{k+2}(G))·ω)`, `P(Γ(N_{k+2}(G))·ω) < L(0)`. -/
theorem hbTG_loc (S : InaccSeq.{0}) (k : ℕ) :
    ∃ X : XtSys, XtTopPkg X ∧ xtB1 X = iota S (gcG (hbN (k + 2) (gcG 0)) * ω) ∧
      upsilon (xtB1 X) = Pv S (gcG (hbN (k + 2) (gcG 0)) * ω) ∧
      Pv S (gcG (hbN (k + 2) (gcG 0)) * ω) < Nc.ncL S 0 := by
  rw [← hbTG_B k]; exact hbV_locD (hbTG k).1 S (hbTG_K S k)

/-- **Every `c < φ(ω, G+1)` lies below a located bound** (gate `0`). -/
theorem hbTw_codes {c : Ordinal.{0}} (hc : c < hbTw) : ∃ k : ℕ, c < (hbTG k).1.B := by
  obtain ⟨k, hk⟩ := (Ordinal.lt_iSup_iff).1 hc
  exact ⟨k, by rw [hbTG_B]; exact hk.trans_le (hbN_mono (by omega) _)⟩

theorem hbTw_iota_cof (S : InaccSeq.{0}) {l : Ordinal.{0}} (hl : l < iota S (gcG hbTw)) :
    ∃ k : ℕ, l < iota S (gcG (hbTG k).1.B * ω) := by
  have hlim : IsSuccLimit (gcG hbTw) := ev_isSuccLimit_of_inE (Low.opow_eq_self_of_SC (gcG_SC _))
  rw [iota_limit hlim] at hl
  haveI : Nonempty (Iio (gcG hbTw)) := ⟨⟨0, hlim.bot_lt⟩⟩
  obtain ⟨e, he⟩ := (lt_ciSup_iff (iota_bdd _)).1 hl
  obtain ⟨β, hβ, heβ⟩ := gcG_lt_of_lt_limit hbTw_lim e.2
  obtain ⟨k, hk⟩ := hbTw_codes hβ
  refine ⟨k, he.trans_le (iota_mono _ _ ((heβ.trans (gcG_lt hk)).trans_le ?_).le)⟩
  exact le_mul_of_one_le_right' one_lt_omega0.le

/-- **ENUM-REACH at every range restart below `ι(Γ(φ(ω, G+1)))`, fixed points included** (UNCONDITIONAL). -/
theorem hbTw_enum (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG hbTw)) :
    CdUpper S l ∧ CdLower S l := by
  obtain ⟨k, h⟩ := hbTw_iota_cof S hl
  exact hbV_locD_enum (hbTG k).1 S (hbTG_K S k) hr h

/-- **CapV at every range restart below `ι(Γ(φ(ω, G+1)))`** (UNCONDITIONAL). -/
theorem hbTw_capV (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG hbTw)) :
    CdCapV S l := by
  obtain ⟨k, h⟩ := hbTw_iota_cof S hl
  exact hbV_locD_capV (hbTG k).1 S (hbTG_K S k) hr h

/-- **BLK^O and the exact reaches below `P(Γ(φ(k+3, G+1))·ω)` for every `k`** (UNCONDITIONAL). -/
theorem hbTw_blk (S : InaccSeq.{0}) (k : ℕ) :
    let D := (hbTG k).1
    let X := gsX D.step.toRS _ D.E_lt_B.le D.B_lt_NB S (hbV_locD_g D S (hbTG_K S k))
    xtB1 X = iota S (gcG (hbN (k + 2) (gcG 0)) * ω) ∧
    (∀ c' d, c' < d → d < upsilon (xtB1 X) → (le2 c' d ↔ ∃ μ, ∃ j : ℕ, (μ = 0 ∨ IsRestartIdx μ) ∧ μ < xtB1 X ∧
        c' = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧ d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < xtB1 X →
      (∀ c' < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c' g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec X l)) ∧
    (∀ α < upsilon (xtB1 X), ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) := by
  intro D X
  refine ⟨?_, hbV_locD_blk D S (hbTG_K S k)⟩
  have h := (gsLoc D.step.toRS _ D.E_lt_B.le D.B_lt_NB S (hbV_locD_g D S (hbTG_K S k))).1
  rw [← hbTG_B k]; exact h

/-- **THE ROAD**: UPPER, LOWER, CapV asked only at `λ ≥ ι(Γ(φ(ω, G+1)))` (CapV also `υ_λ < L(ω)`), (CL), EQ, TCrest,
(EMB₂) ⟹ `ν_C = L(ω+1)`, `L(ω) ≤ ν_C`, `L(ω) <₂ L(ω+1)`, (P), (Q), the reaches. -/
theorem hbTw_road (S : InaccSeq.{0}) (hU : ∀ l, CdRange S l → iota S (gcG hbTw) ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S (gcG hbTw) ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S (gcG hbTw) ≤ l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  gv_road_of S _ (fun _ hr h => hbTw_enum S hr h) (fun _ hr h => hbTw_capV S hr h) hU hL hV hC hEQ hrest hB2

/-- **`Γ(φ(ω, G+1)) < Ω₂`.** -/
theorem hbTw_le_Om2 : gcG hbTw < Om (1 + 1) := by
  have hBE : InE Tf.tfBG := Low.opow_eq_self_of_SC Tf.tfBG_SC
  have hO : (Om1 : Ordinal.{0}) < Tf.tfBG := Tf.tfBG_gt
  have h1 : (1 : Ordinal.{0}) < Tf.tfBG := one_lt_omega0.trans (omega0_lt_inE hBE)
  have hG1 : gcG 1 < Tf.tfBG := by
    rw [Tf.tf_gcG, ← Tf.tfBG_fix]
    exact gamma_lt_gamma.2 ((inE_indec hBE).add_lt ((inE_indec hBE).add_lt hO h1) h1)
  have h2 : gcG hbTw < Tf.tfBG := by
    rw [Tf.tf_gcG, ← Tf.tfBG_fix]
    exact gamma_lt_gamma.2 ((inE_indec hBE).add_lt ((inE_indec hBE).add_lt hO h1) (hbTw_lt_G1.trans hG1))
  exact h2.trans Tf.tfBG_lt_Om2

/-- **`P(Γ(φ(ω, G+1))) < L(0)`.** -/
theorem hbTw_P (S : InaccSeq.{0}) : Pv S (gcG hbTw) < Nc.ncL S 0 := ga_Pv_lt_L0 S hbTw_le_Om2.le

/-- **The order of the frontiers**: `φ(3, G+1) = N_2(G) < φ(4, G+1) = N_3(G) < φ(ω, G+1)`,
`ι(Γ(φ(3, G+1))) ≤ ι(Γ(φ(k+3, G+1))·ω) ≤ ι(Γ(φ(ω, G+1))) ≤ ι(Ω₂)`, `P(Γ(φ(ω, G+1))) ≤ P(Ω₂) < L(0)`. -/
theorem hbTw_fr_order (S : InaccSeq.{0}) (k : ℕ) :
    hbN 2 (gcG 0) = haT ∧ hbN 3 (gcG 0) = veblen 4 (gcG 0 + 1) ∧ hbN 3 (gcG 0) < hbTw ∧
      iota S (gcG haT) ≤ iota S (gcG (hbN (k + 2) (gcG 0)) * ω) ∧
      iota S (gcG (hbN (k + 2) (gcG 0)) * ω) ≤ iota S (gcG hbTw) ∧
      iota S (gcG hbTw) ≤ iota S (Om (1 + 1)) ∧ Pv S (gcG hbTw) ≤ Pv S (Om (1 + 1)) ∧
      Pv S (Om (1 + 1)) < Nc.ncL S 0 := by
  have hV : InE (gcG hbTw) := Low.opow_eq_self_of_SC (gcG_SC _)
  have e2 : hbN 2 (gcG 0) = haT := by
    have := hbAG_N 1; rw [this]; norm_num; rfl
  have e3 : hbN 3 (gcG 0) = veblen 4 (gcG 0 + 1) := by
    have := hbAG_N 2; rw [this]; norm_num
  refine ⟨e2, e3, hbN_lt_Tw 3, ?_, iota_mono _ _ (InE.mul_lt hV (gcG_lt (hbN_lt_Tw (k + 2)))
    (omega0_lt_inE hV)).le, iota_mono _ _ hbTw_le_Om2.le, Nm.Pv_mono hbTw_le_Om2.le, ga_Pv_lt_L0 S le_rfl⟩
  rw [← e2]
  exact iota_mono _ _ ((gcG_le (hbN_mono (by omega) _)).trans (le_mul_of_one_le_right' one_lt_omega0.le))

/-! ## The wall `φ(ω, G+1)` -/

/-- **The code `N_{k+2}(G)` is read in `hbTG (k+1)` as `N_{k+2}(Γ_{x+1})`, with gate `0`.** -/
theorem hbTG_read (k : ℕ) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    (hbTG (k + 1)).1.R (hbTG k).1.B x = hbN (k + 2) (lgG x) ∧ (hbTG (k + 1)).1.g (hbTG k).1.B < x := by
  set St : ∀ (X : HbX (k + 1)) (U : HbVD), HbSStart (hbXPB X) U → HbVD := fun X U h => (hbRecS (k + 1) X U h).1
  have hSt : ∀ X U h, HbSpec X U (St X U h) := fun X U h => (hbRecS (k + 1) X U h).2
  have hS := hbG_next_start k (hbTG k).2
  have e : (hbTG (k + 1)).1 = hbLvTU hSt hS := rfl
  have hsp := hbLvU_succ_spec hSt hS (hbLv_zero_lt_N (hbAG (k + 1 + 1)))
  have hB0 : (hbLvU St (hbAG (k + 1 + 1)) (hbTG k).1 0).B = (hbTG k).1.B := by rw [hbLvU_zero]
  have hXF : (hbXoff (k + 1) (hbAG (k + 1 + 1)) (hbLvU St (hbAG (k + 1 + 1)) (hbTG k).1 0) 0
      (hbLvU_self hSt hS (hbLv_zero_lt_N _)) (hbLv_zero_lt_N _) (hbLvU_Zb hSt hS (hbLv_zero_lt_N _))).F =
      (hbTG k).1.B := by
    rw [hbXoff_F, add_zero, hbTG_B, hbAG_N (k + 1)]; rfl
  have h1 : (0 : Ordinal.{0}) + 1 < hbN (k + 1 + 1 + 1) (hbAG (k + 1 + 1)).F :=
    (hbAG (k + 1 + 1)).N_lim.add_one_lt (hbLv_zero_lt_N _)
  have hc1 : (hbTG k).1.B < (hbLvU St (hbAG (k + 1 + 1)) (hbTG k).1 (0 + 1)).B := by
    rw [← hXF, hsp.B]; exact hbN_gt _ _
  have hγ0 : (hbXoff (k + 1) (hbAG (k + 1 + 1)) (hbLvU St (hbAG (k + 1 + 1)) (hbTG k).1 0) 0
      (hbLvU_self hSt hS (hbLv_zero_lt_N _)) (hbLv_zero_lt_N _) (hbLvU_Zb hSt hS (hbLv_zero_lt_N _))).γ < x := by
    rw [hbXoff_γ, (hbLvU _ _ _ 0).g_zero, max_eq_left zero_le]; exact hx.pos
  refine ⟨?_, ?_⟩
  · rw [e, hbLvTU_R hSt hS h1 hc1, ← hXF, hsp.RF x hx hx1 hγ0, hbXoff_Fr, hbLvU_zero, (hbTG k).1.R_zero, add_zero]
    exact hb_glA_G hx hx1 (k + 1 + 1)
  · rw [e, hbLvTU_g hSt hS h1 hc1, ← hXF]; exact (hsp.gF x hx hx1).2 hγ0

/-- **THE WALL `φ(ω, G+1)`**: no system `D : HbVD` that extends every `hbTG k` (readings and gates) contains the code
`φ(ω, G+1)` with its gate below some base `x`: its reading would lie above every `N_{k+2}(Γ_{x+1})`, hence
`≥ B_ω(x)`, but `D` reads below `Z(x) ≤ B_ω(x)`. -/
theorem hb_wall_Tw (D : HbVD) (hB : hbTw < D.B)
    (hR : ∀ (k : ℕ) c x, c < (hbTG k).1.B → D.R c x = (hbTG k).1.R c x)
    (hg : ∀ (k : ℕ) c, c < (hbTG k).1.B → D.g c = (hbTG k).1.g c)
    {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hgx : D.g hbTw < x) : False := by
  have hk : ∀ k : ℕ, hbN (k + 2) (lgG x) < D.R hbTw x := fun k => by
    obtain ⟨r1, g1⟩ := hbTG_read k hx hx1
    have hkB : (hbTG k).1.B < (hbTG (k + 1)).1.B := by rw [hbTG_B, hbTG_B]; exact hbN_lt_succ _ _
    have hkT : (hbTG k).1.B < hbTw := by rw [hbTG_B]; exact hbN_lt_Tw _
    have hgk : D.g (hbTG k).1.B < x := by rw [hg (k + 1) _ hkB]; exact g1
    have := D.mono x hx hx1 hbTw hB (hbTG k).1.B hkT hgx hgk
    rwa [hR (k + 1) _ x hkB, r1] at this
  have hge : hbBw x ≤ D.R hbTw x := Ordinal.iSup_le fun k =>
    (hbN_mono (Nat.le_add_right k 2) _).trans (hk k).le
  exact absurd ((D.R_lt_Z x hx hx1 hbTw hB hgx).trans_le (D.Z_Bw x hx hx1)) (not_lt.2 hge)

end Googology.Trans.PoR.InaccPsi.R2.Hb
