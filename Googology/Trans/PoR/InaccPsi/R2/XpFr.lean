import Googology.Trans.PoR.InaccPsi.R2.XpT0
import Googology.Trans.PoR.InaccPsi.R2.XjShift
import Googology.Trans.PoR.InaccPsi.R2.XjGap

/-!
# XpFr: THE FRONTIER `ι(Γ(φ(t₀, G+1))·ω)` AND THE ROAD PAST IT

* `xpV1` (the step of `Xc.xcPkT0` at the pseudo-base `φ(t₀, G)`: **THE SYSTEM AT `φ(t₀, G + 1)`**, gate `1`);
* `xpT0_loc` (**`φ(t₀, G + 1)` IS LOCATED**: `Λ⁺ = ι(Γ(φ(t₀, G+1))·ω)`, `P(…) < L(0)`), `xpT0_enum`, `xpT0_capV`,
  `xpT0_sysG` (every `B ≤ φ(t₀, G+1)` lies below the bound of a system with gate `< K`), `xpT0_blkBound`;
* `XpT0Past`, `xpT0_past_W`, `xpT0Hyp_iff` (**THE FOUR FRONTIER HYPOTHESES PAST THE NEW FRONTIER ⇔ PAST
  `ι(Γ(φ(G + Ω₁, 0))·ω)`**, i.e. ⇔ those of `Xl.xlwRoad` / `Xl.xlwRoadZ`);
* `xpT0RoadZ` (the conclusion of `Xl.xlwRoadZ` with UPPER / LOWER / CapV only past the new frontier, `XbShift`
  supplied by `Xj.xbShift_holds`), `xpT0Road_vac` (**ITS HYPOTHESES ARE JOINTLY FALSE**, from `Xj.xjRoad_false`: the
  supply hypotheses `Xb.XbVisGen` are refuted there, the frontier move does not change that).

No new axiom.  New definitions: `xpV1`, `XpT0Past`.
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

/-- **THE SYSTEM AT `φ(t₀, G + 1)`**: the step of the (A3) package `Xc.xcPkT0` at the pseudo-base `φ(t₀, G)`. -/
noncomputable def xpV1 : HgVD := xcPkT0.St0 (wyQ3 xpQG) (xpVT (gcG 0)) xpQG_start

theorem xpV1_B : xpV1.B = veblen (Wj.wjT 0) (gcG 0 + 1) := by
  rw [xpV1, (xcPkT0.h0 (wyQ3 xpQG) (xpVT (gcG 0)) xpQG_start).B, add_zero, wyQ3_F, xpQG_F]
  exact hdNx_veb _ _

theorem xpV1_γ : xpV1.γ = 1 := by
  rw [xpV1, (xcPkT0.h0 (wyQ3 xpQG) (xpVT (gcG 0)) xpQG_start).γ, wyQ3_γ, xpQG_γ]

variable (S : InaccSeq.{0})

theorem xpV1_γK : xpV1.γ < Td.tdK S := by rw [xpV1_γ]; exact xc_one_lt_SC Td.tdK_SC

/-- **`φ(t₀, G + 1)` IS LOCATED** (UNCONDITIONAL): `Λ⁺ = ι(Γ(φ(t₀, G+1))·ω)`, `P(…) < L(0)`. -/
theorem xpT0_loc :
    ∃ X : Xt.XtSys, Xt.XtTopPkg X ∧ Xt.xtB1 X = iota S (gcG (veblen (Wj.wjT 0) (gcG 0 + 1)) * ω) ∧
      upsilon (Xt.xtB1 X) = Nm.Pv S (gcG (veblen (Wj.wjT 0) (gcG 0 + 1)) * ω) ∧
        Nm.Pv S (gcG (veblen (Wj.wjT 0) (gcG 0 + 1)) * ω) < Nc.ncL S 0 := by
  have h := hgV_locD xpV1 S (xpV1_γK S)
  rwa [xpV1_B] at h

theorem xpT0_enum {l : Ordinal.{0}} (hr : CdRange S l)
    (hl : l < iota S (gcG (veblen (Wj.wjT 0) (gcG 0 + 1)) * ω)) : CdUpper S l ∧ CdLower S l := by
  rw [← xpV1_B] at hl; exact hgV_locD_enum xpV1 S (xpV1_γK S) hr hl

theorem xpT0_capV {l : Ordinal.{0}} (hr : CdRange S l)
    (hl : l < iota S (gcG (veblen (Wj.wjT 0) (gcG 0 + 1)) * ω)) : CdCapV S l := by
  rw [← xpV1_B] at hl; exact hgV_locD_capV xpV1 S (xpV1_γK S) hr hl

/-- **EVERY `B ≤ φ(t₀, G + 1)` LIES BELOW THE BOUND OF A SYSTEM WITH GATE `< K`** (UNCONDITIONAL). -/
theorem xpT0_sysG : ∀ B, B ≤ veblen (Wj.wjT 0) (gcG 0 + 1) → ∃ V : HgVD, B ≤ V.B ∧ V.γ < Td.tdK S :=
  fun _ hB => ⟨xpV1, by rw [xpV1_B]; exact hB, xpV1_γK S⟩

/-- **`l` lies past the new frontier `ι(Γ(φ(t₀, G+1))·ω)`.** -/
def XpT0Past (l : Ordinal.{0}) : Prop := iota S (gcG (veblen (Wj.wjT 0) (gcG 0 + 1)) * ω) ≤ l

theorem xpT0_notPast {l : Ordinal.{0}} (hr : CdRange S l) (h : ¬ XpT0Past S l) :
    CdUpper S l ∧ CdLower S l ∧ CdCapV S l := by
  unfold XpT0Past at h; push Not at h
  exact ⟨(xpT0_enum S hr h).1, (xpT0_enum S hr h).2, xpT0_capV S hr h⟩

/-- **The old frontier `ι(Γ(φ(G + Ω₁, 0))·ω)` lies below the new one.** -/
theorem xpT0_FW_le :
    iota S (gcG (veblen (gcG 0 + Om1) 0) * ω) ≤ iota S (gcG (veblen (Wj.wjT 0) (gcG 0 + 1)) * ω) := by
  refine iota_mono _ _ (mul_le_mul_left (gcG_le ?_) ω)
  exact (veblen_zero_le_veblen_zero.2 wt_GO_lt.le).trans ((isNormal_veblen _).monotone zero_le)

theorem xpT0_past_W {l : Ordinal.{0}} (h : XpT0Past S l) : XlWPast S l := (xpT0_FW_le S).trans h

variable {S}

/-- **NON-VACUITY (relative)**: the four frontier hypotheses past the new frontier are EQUIVALENT to those of
`Xl.xlwRoad` / `Xl.xlwRoadZ`. -/
theorem xpT0Hyp_iff :
    ((∀ l, CdRange S l → XlWPast S l → CdUpper S l) ↔ (∀ l, CdRange S l → XpT0Past S l → CdUpper S l)) ∧
    ((∀ l, CdRange S l → XlWPast S l → CdLower S l) ↔ (∀ l, CdRange S l → XpT0Past S l → CdLower S l)) ∧
    ((∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XlWPast S l → CdCapV S l) ↔
      (∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XpT0Past S l → CdCapV S l)) ∧
    ((∀ l, CdRange S l → Nc.ncL S ω < upsilon l → XlWPast S l → CdCapV S l) ↔
      (∀ l, CdRange S l → Nc.ncL S ω < upsilon l → XpT0Past S l → CdCapV S l)) := by
  refine ⟨⟨fun h l hr hp => h l hr (xpT0_past_W S hp), fun h l hr _ => ?_⟩,
    ⟨fun h l hr hp => h l hr (xpT0_past_W S hp), fun h l hr _ => ?_⟩,
    ⟨fun h l hr hu hp => h l hr hu (xpT0_past_W S hp), fun h l hr hu _ => ?_⟩,
    ⟨fun h l hr hu hp => h l hr hu (xpT0_past_W S hp), fun h l hr hu _ => ?_⟩⟩
  · by_cases hp : XpT0Past S l
    · exact h l hr hp
    · exact (xpT0_notPast S hr hp).1
  · by_cases hp : XpT0Past S l
    · exact h l hr hp
    · exact (xpT0_notPast S hr hp).2.1
  · by_cases hp : XpT0Past S l
    · exact h l hr hu hp
    · exact (xpT0_notPast S hr hp).2.2
  · by_cases hp : XpT0Past S l
    · exact h l hr hu hp
    · exact (xpT0_notPast S hr hp).2.2

/-- **The conclusion of `Xl.xlwRoadZ` with UPPER / LOWER / CapV asked only past `ι(Γ(φ(t₀, G+1))·ω)`** (and
`Xb.XbShift` supplied by `Xj.xbShift_holds`).  VACUOUS: see `xpT0Road_vac`. -/
theorem xpT0RoadZ
    (hUH : ∀ l, CdRange S l → XpT0Past S l → CdUpper S l)
    (hLH : ∀ l, CdRange S l → XpT0Past S l → CdLower S l)
    (hVH : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XpT0Past S l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → XpT0Past S l → CdCapV S l)
    (hT : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdThLow S)
    (hF : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdEQfar S)
    (h0 : ∀ l, IsRestartIdx l → Nc.ncL S 0 = upsilon l →
      Xb.XbVisGen S l (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Te.teW (Nc.ncL S 0))))
    (hn : ∀ n : ℕ, ∀ l, IsRestartIdx l → Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) = upsilon l →
      Xb.XbVisGen S l (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
        (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Te.teW (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S (k + 1)) (Nc.ncL S (ω + 1)) := by
  obtain ⟨a, b, c, d⟩ := xpT0Hyp_iff (S := S)
  exact xlwRoadZ (a.2 hUH) (b.2 hLH) (c.2 hVH) (d.2 hVt) hT hF Xj.xbShift_holds h0 hn

/-- **THE HYPOTHESES OF `xpT0RoadZ` ARE JOINTLY FALSE** (`Xj.xjRoad_false`; the frontier hypotheses past the new
frontier are equivalent to those past `Xf.XfPast`). -/
theorem xpT0Road_vac
    (hUH : ∀ l, CdRange S l → XpT0Past S l → CdUpper S l)
    (hLH : ∀ l, CdRange S l → XpT0Past S l → CdLower S l)
    (hVH : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XpT0Past S l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → XpT0Past S l → CdCapV S l)
    (hT : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdThLow S)
    (hF : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdEQfar S)
    (h0 : ∀ l, IsRestartIdx l → Nc.ncL S 0 = upsilon l →
      Xb.XbVisGen S l (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Te.teW (Nc.ncL S 0))))
    (hn : ∀ n : ℕ, ∀ l, IsRestartIdx l → Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) = upsilon l →
      Xb.XbVisGen S l (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
        (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Te.teW (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))) :
    False := by
  obtain ⟨a, b, c, d⟩ := xpT0Hyp_iff (S := S)
  obtain ⟨a1, b1, c1, d1⟩ := xlwRoad_hyp_iff (S := S)
  obtain ⟨a2, b2, c2, d2⟩ := xlkRoad_hyp_iff (S := S)
  obtain ⟨a3, b3, c3, d3⟩ := xlRoad_hyp_iff (S := S)
  exact Xj.xjRoad_false (a3.2 (a2.2 (a1.2 (a.2 hUH)))) (b3.2 (b2.2 (b1.2 (b.2 hLH))))
    (c3.2 (c2.2 (c1.2 (c.2 hVH)))) (d3.2 (d2.2 (d1.2 (d.2 hVt)))) hT hF h0 hn

end Googology.Trans.PoR.InaccPsi.R2.Xp
