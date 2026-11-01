import Googology.Trans.PoR.InaccPsi.R2.XfRec
import Googology.Trans.PoR.InaccPsi.R2.XbRoad

/-!
# XfFr: THE FRONTIER PASSES `φ(G, 1)`: EVERY `φ(G, ν)`, `ν < Γ₀`, IS LOCATED; THE ROAD

The systems `Xf.xfV ν` (bound `φ(G, 1+ν)`, gate `≤ 1+ν < Γ₀ ≤ K`) are located by `Hg.hgV_locD`:

* `xfV_γK`, `xf_loc` (**`ι(Γ(φ(G, 1+ν))·ω)` IS LOCATED FOR EVERY `ν < Γ₀`**, `P(…) < L(0)`), `xf_enum`, `xf_capV`
  (**ENUM-REACH and CapV at every range restart below it**, UNCONDITIONAL);
* `xf_sysG` (**every `B < φ(G, Γ₀)` lies below the bound of a system with gate `< K`**);
* `XfPast S l` (`l` lies at or above `ι(Γ(φ(G, 1+ν))·ω)` for every `ν < Γ₀`: the new frontier
  `F_G = sup_{ν<Γ₀} ι(Γ(φ(G, ν))·ω) = ι(Γ(φ(G, Γ₀)))`), `xf_FZ_le` (`F_Z ≤ ι(Γ(φ(G, 1))·ω)`), `xf_A2_le`
  (every (A2) frontier `ι(Γ(φ(ℓ, G+1))·ω)`, `ℓ < G`, lies below `ι(Γ(φ(G, 1))·ω)`);
* `xfRoad` (**THE ROAD `Xb.xbRoad` WITH UPPER / LOWER / CapV ASKED ONLY PAST `F_G`**), `xfRoadZ` (the conclusion of
  `Xb.xbRoadZ`), `xfRoad_hyp_iff` (**the four new hypotheses are EQUIVALENT to those of `Xb.xbRoadZ`**:
  non-vacuity relative to `Xb.xbRoadZ`).

No new axiom.  New definition: `XfPast`.
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

namespace Googology.Trans.PoR.InaccPsi.R2.Xf

section Fr

variable (S : InaccSeq.{0})

theorem xfV_γK {ν : Ordinal.{0}} (hν : ν < gamma 0) : (xfV ν).γ < Td.tdK S :=
  (xfV_γ hν).trans_lt ((xf_one_add_lt hν).trans_le (Td.tdGam_le_K (S := S)))

/-- **`φ(G, 1+ν)` IS LOCATED FOR EVERY `ν < Γ₀`**: `Λ⁺ = ι(Γ(φ(G, 1+ν))·ω)`, `P(…) < L(0)` (UNCONDITIONAL). -/
theorem xf_loc {ν : Ordinal.{0}} (hν : ν < gamma 0) :
    ∃ X : Xt.XtSys, Xt.XtTopPkg X ∧ Xt.xtB1 X = iota S (gcG (veblen (gcG 0) (1 + ν)) * ω) ∧
      upsilon (Xt.xtB1 X) = Nm.Pv S (gcG (veblen (gcG 0) (1 + ν)) * ω) ∧
        Nm.Pv S (gcG (veblen (gcG 0) (1 + ν)) * ω) < Nc.ncL S 0 := by
  rw [← xfV_B hν]; exact hgV_locD (xfV ν) S (xfV_γK S hν)

/-- **ENUM-REACH at every range restart below `ι(Γ(φ(G, 1+ν))·ω)`** (UNCONDITIONAL). -/
theorem xf_enum {ν : Ordinal.{0}} (hν : ν < gamma 0) {l : Ordinal.{0}} (hr : CdRange S l)
    (hl : l < iota S (gcG (veblen (gcG 0) (1 + ν)) * ω)) : CdUpper S l ∧ CdLower S l := by
  rw [← xfV_B hν] at hl; exact hgV_locD_enum (xfV ν) S (xfV_γK S hν) hr hl

/-- **CapV at every range restart below `ι(Γ(φ(G, 1+ν))·ω)`** (UNCONDITIONAL). -/
theorem xf_capV {ν : Ordinal.{0}} (hν : ν < gamma 0) {l : Ordinal.{0}} (hr : CdRange S l)
    (hl : l < iota S (gcG (veblen (gcG 0) (1 + ν)) * ω)) : CdCapV S l := by
  rw [← xfV_B hν] at hl; exact hgV_locD_capV (xfV ν) S (xfV_γK S hν) hr hl

/-- **EVERY `B < φ(G, Γ₀)` IS BELOW THE BOUND OF A SYSTEM WITH GATE `< K`** (UNCONDITIONAL). -/
theorem xf_sysG : ∀ B, B < veblen (gcG 0) (gamma 0) → ∃ V : HgVD, B ≤ V.B ∧ V.γ < Td.tdK S := by
  intro B hB
  obtain ⟨β, hβ, hBβ⟩ := ((isNormal_veblen (gcG 0)).lt_iff_exists_lt xf_gam0_lim).1 hB
  refine ⟨xfV β, ?_, xfV_γK S hβ⟩
  rw [xfV_B hβ]
  exact hBβ.le.trans ((isNormal_veblen _).monotone le_add_self)

/-- **`l` lies past the new frontier**: `ι(Γ(φ(G, 1+ν))·ω) ≤ l` for every `ν < Γ₀`. -/
def XfPast (l : Ordinal.{0}) : Prop := ∀ ν, ν < gamma 0 → iota S (gcG (veblen (gcG 0) (1 + ν)) * ω) ≤ l

/-- Below the new frontier ENUM-REACH and CapV hold. -/
theorem xf_notPast {l : Ordinal.{0}} (hr : CdRange S l) (h : ¬ XfPast S l) :
    CdUpper S l ∧ CdLower S l ∧ CdCapV S l := by
  unfold XfPast at h; push Not at h
  obtain ⟨ν, hν, hl⟩ := h
  exact ⟨(xf_enum S hν hr hl).1, (xf_enum S hν hr hl).2, xf_capV S hν hr hl⟩

/-- `F_Z = ι(Γ(φ(ζ_{Ω₁+1}, G+1))·ω) ≤ ι(Γ(φ(G, 1))·ω)`. -/
theorem xf_FZ_le : iota S (gcG Ws.wsVz.B * ω) ≤ iota S (gcG (veblen (gcG 0) (1 + 0)) * ω) := by
  refine iota_mono _ _ (mul_le_mul_left (gcG_le ?_) ω)
  rw [Ws.wsVz_B, add_zero, ← xfV1_B]; exact (xfV1_cover Ws.wsZ_lt_G).le

/-- Every (A2) frontier lies below `ι(Γ(φ(G, 1))·ω)`. -/
theorem xf_A2_le {ℓ : Ordinal.{0}} (hℓ : ℓ < gcG 0) :
    iota S (gcG (veblen ℓ (gcG 0 + 1)) * ω) ≤ iota S (gcG (veblen (gcG 0) (1 + 0)) * ω) := by
  refine iota_mono _ _ (mul_le_mul_left (gcG_le ?_) ω)
  rw [add_zero, ← xfV1_B]; exact (xfV1_cover hℓ).le

theorem xf_past_FZ {l : Ordinal.{0}} (h : XfPast S l) : iota S (gcG Ws.wsVz.B * ω) ≤ l :=
  (xf_FZ_le S).trans (h 0 xf_gam0_SC.1)

/-- **Past the new frontier ⇒ past the end of (A2)** (`Wx.WxPast`). -/
theorem xf_past_A2 {l : Ordinal.{0}} (h : XfPast S l) : Wx.WxPast S l :=
  (Wx.wxFA2_cof S).2 fun n => (xf_A2_le S (glBn_spec n).1).trans (h 0 xf_gam0_SC.1)

/-- **WHERE THE NEW FRONTIER IS**: every `ι(Γ(φ(G, 1+ν))·ω)`, `ν < Γ₀`, is `≤ ι(Γ(φ(G, Γ₀)))`. -/
theorem xf_FG_le {ν : Ordinal.{0}} (hν : ν < gamma 0) :
    iota S (gcG (veblen (gcG 0) (1 + ν)) * ω) ≤ iota S (gcG (veblen (gcG 0) (gamma 0))) := by
  refine iota_mono (S := S) _ _ ?_
  have hE : InE (gcG (veblen (gcG 0) (1 + ν))) := Low.opow_eq_self_of_SC (gcG_SC _)
  have hE' : InE (gcG (veblen (gcG 0) (gamma 0))) := Low.opow_eq_self_of_SC (gcG_SC _)
  have hlt : gcG (veblen (gcG 0) (1 + ν)) < gcG (veblen (gcG 0) (gamma 0)) :=
    gcG_lt ((isNormal_veblen _).strictMono (xf_one_add_lt hν))
  calc gcG (veblen (gcG 0) (1 + ν)) * ω = ω ^ (gcG (veblen (gcG 0) (1 + ν)) + 1) := by
        conv_lhs => rw [← hE]
        rw [opow_add, opow_one]
    _ ≤ ω ^ gcG (veblen (gcG 0) (gamma 0)) := opow_le_opow_right omega0_pos (Order.add_one_le_of_lt hlt)
    _ = gcG (veblen (gcG 0) (gamma 0)) := hE'

end Fr

variable {S : InaccSeq.{0}}

/-- **THE ROAD `Xb.xbRoad` WITH UPPER / LOWER / CapV ASKED ONLY PAST `F_G = ι(Γ(φ(G, Γ₀)))`.** -/
theorem xfRoad
    (hUH : ∀ l, CdRange S l → XfPast S l → CdUpper S l)
    (hLH : ∀ l, CdRange S l → XfPast S l → CdLower S l)
    (hVH : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XfPast S l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → XfPast S l → CdCapV S l)
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
  refine Xb.xbRoad (fun l hr _ => ?_) (fun l hr _ => ?_) (fun l hr hu _ => ?_) (fun l hr hu _ => ?_) hT hF hS h0 hn
  · by_cases h : XfPast S l
    · exact hUH l hr h
    · exact (xf_notPast S hr h).1
  · by_cases h : XfPast S l
    · exact hLH l hr h
    · exact (xf_notPast S hr h).2.1
  · by_cases h : XfPast S l
    · exact hVH l hr hu h
    · exact (xf_notPast S hr h).2.2
  · by_cases h : XfPast S l
    · exact hVt l hr hu h
    · exact (xf_notPast S hr h).2.2

/-- **NON-VACUITY (relative)**: the four hypotheses of `xfRoad` are EQUIVALENT to those of `Xb.xbRoadZ`. -/
theorem xfRoad_hyp_iff :
    ((∀ l, CdRange S l → iota S (gcG Ws.wsVz.B * ω) ≤ l → CdUpper S l) ↔
      (∀ l, CdRange S l → XfPast S l → CdUpper S l)) ∧
    ((∀ l, CdRange S l → iota S (gcG Ws.wsVz.B * ω) ≤ l → CdLower S l) ↔
      (∀ l, CdRange S l → XfPast S l → CdLower S l)) ∧
    ((∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S (gcG Ws.wsVz.B * ω) ≤ l → CdCapV S l) ↔
      (∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XfPast S l → CdCapV S l)) ∧
    ((∀ l, CdRange S l → Nc.ncL S ω < upsilon l → iota S (gcG Ws.wsVz.B * ω) ≤ l → CdCapV S l) ↔
      (∀ l, CdRange S l → Nc.ncL S ω < upsilon l → XfPast S l → CdCapV S l)) := by
  refine ⟨⟨fun h l hr hp => h l hr (xf_past_FZ S hp), fun h l hr _ => ?_⟩,
    ⟨fun h l hr hp => h l hr (xf_past_FZ S hp), fun h l hr _ => ?_⟩,
    ⟨fun h l hr hu hp => h l hr hu (xf_past_FZ S hp), fun h l hr hu _ => ?_⟩,
    ⟨fun h l hr hu hp => h l hr hu (xf_past_FZ S hp), fun h l hr hu _ => ?_⟩⟩
  · by_cases hp : XfPast S l
    · exact h l hr hp
    · exact (xf_notPast S hr hp).1
  · by_cases hp : XfPast S l
    · exact h l hr hp
    · exact (xf_notPast S hr hp).2.1
  · by_cases hp : XfPast S l
    · exact h l hr hu hp
    · exact (xf_notPast S hr hp).2.2
  · by_cases hp : XfPast S l
    · exact h l hr hu hp
    · exact (xf_notPast S hr hp).2.2

/-- **The conclusion of `Xb.xbRoadZ` with UPPER / LOWER / CapV asked only past `F_G`.** -/
theorem xfRoadZ
    (hUH : ∀ l, CdRange S l → XfPast S l → CdUpper S l)
    (hLH : ∀ l, CdRange S l → XfPast S l → CdLower S l)
    (hVH : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XfPast S l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → XfPast S l → CdCapV S l)
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
  obtain ⟨a, b, c, d⟩ := xfRoad_hyp_iff (S := S)
  exact Xb.xbRoadZ (a.2 hUH) (b.2 hLH) (c.2 hVH) (d.2 hVt) hT hF hS h0 hn

end Googology.Trans.PoR.InaccPsi.R2.Xf
