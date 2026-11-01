import Googology.Trans.PoR.InaccPsi.R2.XlTop
import Googology.Trans.PoR.InaccPsi.R2.XfFr

/-!
# XlFr: THE LEVEL `G` IS COMPLETE: THE SYSTEM AT `φ(G+1, 0)`, THE FRONTIER `ι(Γ(φ(G+1, 0))·ω)`, THE ROAD

The bottom recursion of `Xl.XlRec` / `Xl.XlTop` started at `Xf.xfV1` (the system at `φ(G, 1)`) with the step of the
package at the level `G` (`Xf.xfPk`):

* `xl_start0` (**`Xf.xfV1` STARTS THE OFFSET `0` OF THE BOTTOM**), `xlV λ` (**THE SYSTEM AT `φ(G, 1 + λ)` FOR EVERY
  `λ < φ(G+1, 0)`**: `xlV_B`, `xlV_start`, `xlV_γ_iff`: its gate is `max(1, g(λ))`, `g(λ)` the code gate of the
  offset `λ` in the system reading it), `xlTop` (**THE SYSTEM AT `φ(G+1, 0)`**, gate `1`, base reading
  `φ(Γ_{x+1}+1, 0)`, extending `Xf.xfV1` and `Hg.hgU`);
* `xl_loc` (**`ι(Γ(φ(G+1, 0))·ω)` IS LOCATED**, `P(…) < L(0)`), `xl_enum`, `xl_capV` (**ENUM-REACH and CapV at every
  range restart below it**, UNCONDITIONAL), `xl_sysG` (every `B ≤ φ(G+1, 0)` lies below a system of gate `< K`);
* `XlPast S l` (`ι(Γ(φ(G+1, 0))·ω) ≤ l`), `xl_past_xf` (past the new frontier ⇒ past `F_G` of `Xf.XfPast`),
  `xlRoad` / `xlRoadZ` (**THE ROAD `Xf.xfRoad` WITH UPPER / LOWER / CapV ONLY PAST `ι(Γ(φ(G+1, 0))·ω)`**),
  `xlRoad_hyp_iff` (**the four new hypotheses are EQUIVALENT to those of `Xf.xfRoad`**).

No new axiom.  New definitions: `xlV`, `xlTop`, `XlPast`.
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

namespace Googology.Trans.PoR.InaccPsi.R2.Xl

/-! ## The bottom base of the level `G` -/

theorem xl_L : xfLv.L + 0 = gcG 0 := add_zero _

/-- **`N = N_G(0)`, the first fixed point of `φ(G, ·)`.** -/
noncomputable def xlN : Ordinal.{0} := hcN (xfLv.L + 0) 0

theorem xlN_E : InE xlN := hcN_E _ _

theorem xlN_lim : IsSuccLimit xlN := hcN_lim _ _

theorem xlN_eq : xlN = veblen (gcG 0 + 1) 0 := by unfold xlN; rw [xl_L, xl_N_eq]

theorem xlN_lt1 : xlN < gcG 1 := by
  rw [xlN_eq]
  have hG : gcG 0 + 1 < gcG 1 :=
    (ev_isSuccLimit_of_inE (Low.opow_eq_self_of_SC (gcG_SC 1))).add_one_lt (gcG_lt zero_lt_one)
  have h := (isNormal_veblen (gcG 0 + 1)).strictMono (gcG_SC 1).1
  rwa [gn_veb_fix (gcG_SC 1) hG] at h

theorem xl_N_mem (S : InaccSeq.{0}) {a b : Ordinal.{0}} (ha : 0 < a) : xlN ∈ S.CSet a b := by
  rw [xlN_eq]; exact CSet.phi_mem (CSet.succ_mem (gmS_G0_mem S ha)) (CSet.zero_mem _ _)

/-- **THE BOTTOM BASE OF THE LEVEL `G`**: shift `e = 1` (`φ(G, 0) = G`), reading gate `1`, low field `Z_o`. -/
noncomputable def xlBG : XlB xfLv 0 where
  e := 1
  γN := 1
  Zo := wnZo
  lv := gv_Om1_pos
  lvN := zero_le
  lg := xfLv_g.le
  γN_lt := wh_one_lt_Om1
  G_lt := by rw [xl_L, Nat.cast_one]; exact xf_G_lt_vG zero_lt_one
  N_lt1 := xlN_lt1
  N_mem := fun S _ _ ha _ => xl_N_mem S ha
  N_cl := fun _ hZ _ _ => xc_one_lt_SC hZ
  γN_cl := fun _ hZ _ _ _ => xc_one_lt_SC hZ
  Zo_fix := wnZo_fix
  Zo_G1 := fun _ hx hx1 => wnZo_G1 hx hx1
  read := fun hx hx1 _ _ ht => by rw [Nat.cast_one]; exact xl_glA_eq hx hx1 ht
  N_pi := fun hB _ => xl_N_pi hB

theorem xlBG_e : ((xlBG.e : ℕ) : Ordinal.{0}) = 1 := Nat.cast_one

theorem xlBG_Zl {x : Ordinal.{0}} (hx : InE x) : xlBG.Zl x = hcN (xfLv.l x + 0) 0 :=
  xlBG.Zl_eq hx (wo_one_lt_inE hx)

theorem xl_two_le {x : Ordinal.{0}} (h : 1 < x) : (2 : Ordinal.{0}) ≤ xfLv.l x + 0 := by
  have : (1 : Ordinal.{0}) + 1 ≤ x := Order.add_one_le_of_lt h
  rw [one_add_one_eq_two] at this
  exact this.trans ((xfLv.l_ge x).trans le_self_add)

theorem xl_G_lt_N : gcG 0 < xlN := xlBG.G_lt_N

theorem xl_Q_lt_N {l : Ordinal.{0}} (hl : l < xlN) : veblen (xfLv.L + 0) (1 + l) < xlN := by
  have h := xlBG.Q_lt_N hl; rwa [xlBG_e] at h

/-! ## The instance at the level `G` -/

theorem xl_one_lt_Nx {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : veblen (lgG x) 1 < hcN (xfLv.l x + 0) 0 := by
  rw [xl_lx hx hx1]
  have h := xl_Qg_lt_N (α := lgG x) (t := 0) (hcN_E _ _).pos
  rwa [add_zero] at h

theorem xl_glA0 {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : glA (xfLv.l x + 0) 0 x = veblen (lgG x) 1 := by
  rw [xl_glA_eq hx hx1 (hcN_E _ _).pos, xl_lx hx hx1, add_zero]

/-- **`Xf.xfV1` STARTS THE OFFSET `0` OF THE BOTTOM OF THE LEVEL `G`.** -/
theorem xl_start0 : XlStart xlBG xfV1 where
  B := by rw [xfV1_B, xlBG_e, xl_L, add_zero]
  Zb := fun x hx hx1 => by
    rw [xfV1_Z, if_pos (wo_one_lt_inE hx), xlBG_Zl hx]
    exact (hb_evZ_lt_fix2 (hc_fix_down (xl_two_le (wo_one_lt_inE hx)) (hcN_fix _ _)) (xl_one_lt_Nx hx hx1)).le
  st := fun h2 hZ => by
    have hg : max xlBG.γN (xfV1.g 0) = 1 := by rw [xfV1.g_zero, max_eq_left zero_le]; rfl
    refine ⟨?_, fun x _ _ => ?_, fun x hx hx1 _ => ?_, fun x hx hx1 => ?_⟩
    · show xfV1.ix = veblen (xfLv.L + 0) (xlBG.e + 0)
      rw [xfV1_ix, xlBG_e, xl_L, add_zero]
    · show xfV1.γ < x ↔ max xlBG.γN (xfV1.g 0) < x
      rw [xfV1_γ, hg]
    · show xfV1.b x = glA (xfLv.l x + 0) (xfV1.R 0 x) x
      rw [xfV1.R_zero, xl_glA0 hx hx1]; rfl
    · have h1 : (1 : Ordinal.{0}) < x := wo_one_lt_inE hx
      rw [xfV1_Z, if_pos h1, HgPB.Zst_eq _ (show max xlBG.γN (xfV1.g 0) < x by rw [hg]; exact h1)]
      show evZ (veblen (lgG x) 1) = evZ (glA (xfLv.l x + 0) (xfV1.R 0 x) x)
      rw [xfV1.R_zero, xl_glA0 hx hx1]

/-- **THE SYSTEM AT `φ(G, 1 + λ)`** for every offset `λ < φ(G+1, 0)`. -/
noncomputable def xlV (l : Ordinal.{0}) : HgVD := xlU xfPk.St0 xlBG xfV1 l

/-- **THE SYSTEM AT `φ(G+1, 0)`**: the top of the level `G`. -/
noncomputable def xlTop : HgVD := xlTU xfPk.h0 xl_start0

section Main

variable {l : Ordinal.{0}} (hl : l < xlN)
include hl

theorem xlV_B : (xlV l).B = veblen (gcG 0) (1 + l) := by
  unfold xlV; rw [xlU_B xfPk.h0 xl_start0 hl, xlBG_e]; exact congrArg (fun a => veblen a (1 + l)) xl_L

theorem xlV_start :
    HgSStart (xlMPB xlBG (xlV l) l (xlU_self xfPk.h0 xl_start0 hl) hl (xlU_Zb xfPk.h0 xl_start0 hl)) (xlV l) :=
  xlU_start xfPk.h0 xl_start0 hl

/-- **THE GATE OF THE STAGE `λ`**: `max(1, g(λ))`, `g(λ)` the code gate of `λ` in the system reading it. -/
theorem xlV_γ_iff {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : (xlV l).γ < x ↔ max 1 ((xlV l).g l) < x :=
  xlU_γ_iff xfPk.h0 xl_start0 hl hx hx1

/-- **The base reading of the stage `λ`**: `φ(Γ_{x+1}, 1 + λ(x))` above its gate. -/
theorem xlV_b {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hg : max 1 ((xlV l).g l) < x) :
    (xlV l).b x = veblen (lgG x) (1 + (xlV l).R l x) := by
  rw [(xlV_start hl).b x hx hx1 hg]
  show glA (xfLv.l x + 0) ((xlV l).R l x) x = _
  have hR : (xlV l).R l x < hcN (xfLv.l x + 0) 0 :=
    xlOff_R_lt xlBG _ _ (xlU_self xfPk.h0 xl_start0 hl) (xlU_Zb xfPk.h0 xl_start0 hl) hx hx1 hg
  rw [xl_glA_eq hx hx1 hR, xl_lx hx hx1]

end Main

/-- **Later stages keep the readings and gates of earlier ones.** -/
theorem xlV_ext {β γ : Ordinal.{0}} (hβγ : β ≤ γ) (hγ : γ < xlN) {c : Ordinal.{0}} (hc : c < (xlV β).B)
    (x : Ordinal.{0}) : (xlV γ).R c x = (xlV β).R c x ∧ (xlV γ).g c = (xlV β).g c :=
  ⟨(xl_ext xfPk.h0 xl_start0 hβγ hγ).1 c x hc, (xl_ext xfPk.h0 xl_start0 hβγ hγ).2 c hc⟩

theorem xlTop_B : xlTop.B = veblen (gcG 0 + 1) 0 := xlN_eq

theorem xlTop_γ : xlTop.γ = 1 := rfl

theorem xlTop_b (x : Ordinal.{0}) : xlTop.b x = hcN (xfLv.l x + 0) 0 := rfl

/-- **`xlTop` extends every stage.** -/
theorem xlTop_ext {l c : Ordinal.{0}} (hl : l < xlN) (hc : c < (xlV l).B) (x : Ordinal.{0}) :
    xlTop.R c x = (xlV l).R c x ∧ xlTop.g c = (xlV l).g c :=
  ⟨xlTU_R xfPk.h0 xl_start0 hl hc x, xlTU_g xfPk.h0 xl_start0 hl hc⟩

/-- **`xlTop` extends `Xf.xfV1` and `Hg.hgU`.** -/
theorem xlTop_hgU {c : Ordinal.{0}} (hc : c < hgU.B) (x : Ordinal.{0}) :
    xlTop.R c x = hgU.R c x ∧ xlTop.g c = hgU.g c := by
  have hc1 : c < xfV1.B := (hc.trans_le (ws_S1_le (xf_cf_lev 0) (wsSh_hgU wsA2_G) (xfD_M 0).1)).trans (xfCh.B_lt 0)
  have h0 : xlTop.R c x = xfV1.R c x ∧ xlTop.g c = xfV1.g c :=
    ⟨xlTU_R0 xfPk.h0 xl_start0 hc1 x, xlTU_g0 xfPk.h0 xl_start0 hc1⟩
  have h1 := xfV1_ext hc x
  exact ⟨h0.1.trans h1.1, h0.2.trans h1.2⟩

/-- `φ(G, 1 + ν) < φ(G+1, 0)` for every `ν < φ(G+1, 0)`. -/
theorem xl_V_lt_top {ν : Ordinal.{0}} (hν : ν < xlN) : veblen (gcG 0) (1 + ν) < xlTop.B := by
  have h := xl_Q_lt_N hν; rw [xl_L] at h; rw [xlTop_B, ← xlN_eq]; exact h

/-- **`φ(G, G+1) < φ(G+1, 0)`**: the old cut between (A2) and (A3) lies below the top of the level `G`. -/
theorem xl_GG1_lt : veblen (gcG 0) (gcG 0 + 1) < veblen (gcG 0 + 1) 0 := by
  have h := xl_V_lt_top (xlN_lim.add_one_lt xl_G_lt_N)
  rw [xlTop_B] at h
  rwa [one_add_of_omega0_le ((omega0_lt_inE gl_G0_E).le.trans le_self_add)] at h

theorem xl_gam0_lt_N : (gamma 0 : Ordinal.{0}) < xlN :=
  xf_gam0_lt_Om1.trans (gl_Om1_lt_G0.trans xl_G_lt_N)

/-! ## The frontier -/

section Fr

variable (S : InaccSeq.{0})

theorem xlTop_γK : xlTop.γ < Td.tdK S := xf_one_lt_gam0.trans_le (Td.tdGam_le_K (S := S))

/-- **`φ(G+1, 0)` IS LOCATED**: `Λ⁺ = ι(Γ(φ(G+1, 0))·ω)`, `P(…) < L(0)` (UNCONDITIONAL). -/
theorem xl_loc :
    ∃ X : Xt.XtSys, Xt.XtTopPkg X ∧ Xt.xtB1 X = iota S (gcG (veblen (gcG 0 + 1) 0) * ω) ∧
      upsilon (Xt.xtB1 X) = Nm.Pv S (gcG (veblen (gcG 0 + 1) 0) * ω) ∧
        Nm.Pv S (gcG (veblen (gcG 0 + 1) 0) * ω) < Nc.ncL S 0 := by
  rw [← xlTop_B]; exact hgV_locD xlTop S (xlTop_γK S)

/-- **ENUM-REACH at every range restart below `ι(Γ(φ(G+1, 0))·ω)`** (UNCONDITIONAL). -/
theorem xl_enum {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG (veblen (gcG 0 + 1) 0) * ω)) :
    CdUpper S l ∧ CdLower S l := by
  rw [← xlTop_B] at hl; exact hgV_locD_enum xlTop S (xlTop_γK S) hr hl

/-- **CapV at every range restart below `ι(Γ(φ(G+1, 0))·ω)`** (UNCONDITIONAL). -/
theorem xl_capV {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG (veblen (gcG 0 + 1) 0) * ω)) :
    CdCapV S l := by
  rw [← xlTop_B] at hl; exact hgV_locD_capV xlTop S (xlTop_γK S) hr hl

/-- **EVERY `B ≤ φ(G+1, 0)` IS BELOW THE BOUND OF A SYSTEM WITH GATE `< K`** (UNCONDITIONAL). -/
theorem xl_sysG : ∀ B, B ≤ veblen (gcG 0 + 1) 0 → ∃ V : HgVD, B ≤ V.B ∧ V.γ < Td.tdK S :=
  fun _ hB => ⟨xlTop, by rw [xlTop_B]; exact hB, xlTop_γK S⟩

/-- **`l` lies past the new frontier `ι(Γ(φ(G+1, 0))·ω)`.** -/
def XlPast (l : Ordinal.{0}) : Prop := iota S (gcG (veblen (gcG 0 + 1) 0) * ω) ≤ l

theorem xl_notPast {l : Ordinal.{0}} (hr : CdRange S l) (h : ¬ XlPast S l) :
    CdUpper S l ∧ CdLower S l ∧ CdCapV S l := by
  unfold XlPast at h; push Not at h
  exact ⟨(xl_enum S hr h).1, (xl_enum S hr h).2, xl_capV S hr h⟩

/-- **The old frontier lies below the new one**: `ι(Γ(φ(G, 1+ν))·ω) ≤ ι(Γ(φ(G+1, 0))·ω)` for every `ν < Γ₀`. -/
theorem xl_FG_le {ν : Ordinal.{0}} (hν : ν < gamma 0) :
    iota S (gcG (veblen (gcG 0) (1 + ν)) * ω) ≤ iota S (gcG (veblen (gcG 0 + 1) 0) * ω) := by
  refine iota_mono _ _ (mul_le_mul_left (gcG_le ?_) ω)
  rw [← xlTop_B]; exact (xl_V_lt_top (hν.trans xl_gam0_lt_N)).le

/-- **Past the new frontier ⇒ past `F_G`** (`Xf.XfPast`). -/
theorem xl_past_xf {l : Ordinal.{0}} (h : XlPast S l) : XfPast S l := fun _ hν => (xl_FG_le S hν).trans h

end Fr

variable {S : InaccSeq.{0}}

/-- **NON-VACUITY (relative)**: the four hypotheses of `xlRoad` are EQUIVALENT to those of `Xf.xfRoad`. -/
theorem xlRoad_hyp_iff :
    ((∀ l, CdRange S l → XfPast S l → CdUpper S l) ↔ (∀ l, CdRange S l → XlPast S l → CdUpper S l)) ∧
    ((∀ l, CdRange S l → XfPast S l → CdLower S l) ↔ (∀ l, CdRange S l → XlPast S l → CdLower S l)) ∧
    ((∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XfPast S l → CdCapV S l) ↔
      (∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XlPast S l → CdCapV S l)) ∧
    ((∀ l, CdRange S l → Nc.ncL S ω < upsilon l → XfPast S l → CdCapV S l) ↔
      (∀ l, CdRange S l → Nc.ncL S ω < upsilon l → XlPast S l → CdCapV S l)) := by
  refine ⟨⟨fun h l hr hp => h l hr (xl_past_xf S hp), fun h l hr _ => ?_⟩,
    ⟨fun h l hr hp => h l hr (xl_past_xf S hp), fun h l hr _ => ?_⟩,
    ⟨fun h l hr hu hp => h l hr hu (xl_past_xf S hp), fun h l hr hu _ => ?_⟩,
    ⟨fun h l hr hu hp => h l hr hu (xl_past_xf S hp), fun h l hr hu _ => ?_⟩⟩
  · by_cases hp : XlPast S l
    · exact h l hr hp
    · exact (xl_notPast S hr hp).1
  · by_cases hp : XlPast S l
    · exact h l hr hp
    · exact (xl_notPast S hr hp).2.1
  · by_cases hp : XlPast S l
    · exact h l hr hu hp
    · exact (xl_notPast S hr hp).2.2
  · by_cases hp : XlPast S l
    · exact h l hr hu hp
    · exact (xl_notPast S hr hp).2.2

/-- **THE ROAD `Xf.xfRoad` WITH UPPER / LOWER / CapV ASKED ONLY PAST `ι(Γ(φ(G+1, 0))·ω)`.** -/
theorem xlRoad
    (hUH : ∀ l, CdRange S l → XlPast S l → CdUpper S l)
    (hLH : ∀ l, CdRange S l → XlPast S l → CdLower S l)
    (hVH : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XlPast S l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → XlPast S l → CdCapV S l)
    (hT : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdThLow S)
    (hF : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdEQfar S)
    (hS : Xb.XbShift S)
    (h0 : ∀ l, IsRestartIdx l → Nc.ncL S 0 = upsilon l →
      Xb.XbVisGen S l (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Te.teW (Nc.ncL S 0))))
    (hn : ∀ n : ℕ, ∀ l, IsRestartIdx l → Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) = upsilon l →
      Xb.XbVisGen S l (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
        (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Te.teW (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))) :
    CdTC S ∧ CdEMB2 S ∧ CdCL S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S (k + 1)) (Nc.ncL S (ω + 1)) := by
  obtain ⟨a, b, c, d⟩ := xlRoad_hyp_iff (S := S)
  exact xfRoad (a.2 hUH) (b.2 hLH) (c.2 hVH) (d.2 hVt) hT hF hS h0 hn

/-- **The conclusion of `Xb.xbRoadZ` with UPPER / LOWER / CapV asked only past `ι(Γ(φ(G+1, 0))·ω)`.** -/
theorem xlRoadZ
    (hUH : ∀ l, CdRange S l → XlPast S l → CdUpper S l)
    (hLH : ∀ l, CdRange S l → XlPast S l → CdLower S l)
    (hVH : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XlPast S l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → XlPast S l → CdCapV S l)
    (hT : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdThLow S)
    (hF : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdEQfar S)
    (hS : Xb.XbShift S)
    (h0 : ∀ l, IsRestartIdx l → Nc.ncL S 0 = upsilon l →
      Xb.XbVisGen S l (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Te.teW (Nc.ncL S 0))))
    (hn : ∀ n : ℕ, ∀ l, IsRestartIdx l → Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) = upsilon l →
      Xb.XbVisGen S l (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
        (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Te.teW (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S (k + 1)) (Nc.ncL S (ω + 1)) := by
  obtain ⟨a, b, c, d⟩ := xlRoad_hyp_iff (S := S)
  exact xfRoadZ (a.2 hUH) (b.2 hLH) (c.2 hVH) (d.2 hVt) hT hF hS h0 hn

end Googology.Trans.PoR.InaccPsi.R2.Xl
