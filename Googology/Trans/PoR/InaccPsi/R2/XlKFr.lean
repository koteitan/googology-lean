import Googology.Trans.PoR.InaccPsi.R2.XlKRec

/-!
# XlKFr: THE FRONTIER PASSES EVERY LEVEL `G + κ`, `κ < K`: LOCATION AND THE ROAD

The systems `Xl.xlK κ` (bound `φ(G + κ + 1, 0)`, gate `≤ κ + 1`) are located by `Hg.hgV_locD` when `κ < K`
(`K = Td.tdK S`, the gate bound of the frontier lemma; constant levels `κ ≥ K` have gate `≥ K` and are not located):

* `xlK_γK`, `xlk_loc` (**`ι(Γ(φ(G + κ + 1, 0))·ω)` IS LOCATED FOR EVERY `κ < K`**, `P(…) < L(0)`), `xlk_enum`,
  `xlk_capV` (**ENUM-REACH and CapV at every range restart below it**, UNCONDITIONAL);
* `xlk_sysG` (**every `B < φ(G + K, 0)` lies below the bound of a system with gate `< K`**);
* `XlKPast S l` (`l` lies at or above `ι(Γ(φ(G + κ + 1, 0))·ω)` for every `κ < K`: the new frontier
  `F_K = sup_{κ<K} ι(Γ(φ(G + κ + 1, 0))·ω) ≤ ι(Γ(φ(G + K, 0)))`, `xlk_FK_le`), `xlk_past_xl` (past `F_K` ⇒ past the
  frontier of `Xl.XlPast`);
* `xlkRoad` / `xlkRoadZ` (**THE ROAD `Xf.xfRoad` WITH UPPER / LOWER / CapV ONLY PAST `F_K`**), `xlkRoad_hyp_iff`
  (**the four new hypotheses are EQUIVALENT to those of `Xl.xlRoad`**, hence to those of `Xf.xfRoad`).

No new axiom.  New definition: `XlKPast`.
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

section Fr

variable (S : InaccSeq.{0})

theorem xl_K_lt_Om1 : Td.tdK S < Om1 := by rw [Br.Om1_eq]; exact Td.tdK_lt_Om1

theorem xl_K_lim : IsSuccLimit (Td.tdK S) := ev_isSuccLimit_of_inE (Low.opow_eq_self_of_SC Td.tdK_SC)

theorem xlK_γK {κ : Ordinal.{0}} (hκ : κ < Td.tdK S) : (xlK κ).γ < Td.tdK S :=
  (xlK_γ (hκ.trans (xl_K_lt_Om1 S))).trans_lt ((xl_K_lim S).add_one_lt hκ)

/-- **`φ(G + κ + 1, 0)` IS LOCATED FOR EVERY `κ < K`**: `Λ⁺ = ι(Γ(φ(G + κ + 1, 0))·ω)`, `P(…) < L(0)`
(UNCONDITIONAL). -/
theorem xlk_loc {κ : Ordinal.{0}} (hκ : κ < Td.tdK S) :
    ∃ X : Xt.XtSys, Xt.XtTopPkg X ∧ Xt.xtB1 X = iota S (gcG (veblen (gcG 0 + (κ + 1)) 0) * ω) ∧
      upsilon (Xt.xtB1 X) = Nm.Pv S (gcG (veblen (gcG 0 + (κ + 1)) 0) * ω) ∧
        Nm.Pv S (gcG (veblen (gcG 0 + (κ + 1)) 0) * ω) < Nc.ncL S 0 := by
  rw [← xlK_B (hκ.trans (xl_K_lt_Om1 S))]; exact hgV_locD (xlK κ) S (xlK_γK S hκ)

/-- **ENUM-REACH at every range restart below `ι(Γ(φ(G + κ + 1, 0))·ω)`, `κ < K`** (UNCONDITIONAL). -/
theorem xlk_enum {κ : Ordinal.{0}} (hκ : κ < Td.tdK S) {l : Ordinal.{0}} (hr : CdRange S l)
    (hl : l < iota S (gcG (veblen (gcG 0 + (κ + 1)) 0) * ω)) : CdUpper S l ∧ CdLower S l := by
  rw [← xlK_B (hκ.trans (xl_K_lt_Om1 S))] at hl; exact hgV_locD_enum (xlK κ) S (xlK_γK S hκ) hr hl

/-- **CapV at every range restart below `ι(Γ(φ(G + κ + 1, 0))·ω)`, `κ < K`** (UNCONDITIONAL). -/
theorem xlk_capV {κ : Ordinal.{0}} (hκ : κ < Td.tdK S) {l : Ordinal.{0}} (hr : CdRange S l)
    (hl : l < iota S (gcG (veblen (gcG 0 + (κ + 1)) 0) * ω)) : CdCapV S l := by
  rw [← xlK_B (hκ.trans (xl_K_lt_Om1 S))] at hl; exact hgV_locD_capV (xlK κ) S (xlK_γK S hκ) hr hl

/-- **EVERY `B < φ(G + K, 0)` IS BELOW THE BOUND OF A SYSTEM WITH GATE `< K`** (UNCONDITIONAL). -/
theorem xlk_sysG : ∀ B, B < veblen (gcG 0 + Td.tdK S) 0 → ∃ V : HgVD, B ≤ V.B ∧ V.γ < Td.tdK S := by
  intro B hB
  obtain ⟨a, ha, hBa⟩ := wx_veb_lim_cof0 (isSuccLimit_add _ (xl_K_lim S)) hB
  obtain ⟨d, hd, had⟩ := (lt_add_iff (xl_K_lim S).bot_lt.ne').1 ha
  refine ⟨xlK d, ?_, xlK_γK S hd⟩
  rw [xlK_B (hd.trans (xl_K_lt_Om1 S))]
  exact hBa.le.trans (veblen_zero_le_veblen_zero.2 (had.trans ((add_le_add_iff_left _).2 le_self_add)))

/-- **`l` lies past the new frontier**: `ι(Γ(φ(G + κ + 1, 0))·ω) ≤ l` for every `κ < K`. -/
def XlKPast (l : Ordinal.{0}) : Prop :=
  ∀ κ, κ < Td.tdK S → iota S (gcG (veblen (gcG 0 + (κ + 1)) 0) * ω) ≤ l

theorem xlk_notPast {l : Ordinal.{0}} (hr : CdRange S l) (h : ¬ XlKPast S l) :
    CdUpper S l ∧ CdLower S l ∧ CdCapV S l := by
  unfold XlKPast at h; push Not at h
  obtain ⟨κ, hκ, hl⟩ := h
  exact ⟨(xlk_enum S hκ hr hl).1, (xlk_enum S hκ hr hl).2, xlk_capV S hκ hr hl⟩

/-- **Past the new frontier ⇒ past the frontier of the level `G`** (`Xl.XlPast`). -/
theorem xlk_past_xl {l : Ordinal.{0}} (h : XlKPast S l) : XlPast S l := by
  have h0 := h 0 Td.tdK_SC.1
  rwa [zero_add] at h0

/-- **WHERE THE NEW FRONTIER IS**: every `ι(Γ(φ(G + κ + 1, 0))·ω)`, `κ < K`, is `≤ ι(Γ(φ(G + K, 0)))`. -/
theorem xlk_FK_le {κ : Ordinal.{0}} (hκ : κ < Td.tdK S) :
    iota S (gcG (veblen (gcG 0 + (κ + 1)) 0) * ω) ≤ iota S (gcG (veblen (gcG 0 + Td.tdK S) 0)) := by
  refine iota_mono (S := S) _ _ ?_
  have hE : InE (gcG (veblen (gcG 0 + (κ + 1)) 0)) := Low.opow_eq_self_of_SC (gcG_SC _)
  have hE' : InE (gcG (veblen (gcG 0 + Td.tdK S) 0)) := Low.opow_eq_self_of_SC (gcG_SC _)
  have hlt : gcG (veblen (gcG 0 + (κ + 1)) 0) < gcG (veblen (gcG 0 + Td.tdK S) 0) :=
    gcG_lt (veblen_zero_lt_veblen_zero.2 ((add_lt_add_iff_left _).2 ((xl_K_lim S).add_one_lt hκ)))
  calc gcG (veblen (gcG 0 + (κ + 1)) 0) * ω = ω ^ (gcG (veblen (gcG 0 + (κ + 1)) 0) + 1) := by
        conv_lhs => rw [← hE]
        rw [opow_add, opow_one]
    _ ≤ ω ^ gcG (veblen (gcG 0 + Td.tdK S) 0) := opow_le_opow_right omega0_pos (Order.add_one_le_of_lt hlt)
    _ = gcG (veblen (gcG 0 + Td.tdK S) 0) := hE'

end Fr

variable {S : InaccSeq.{0}}

/-- **NON-VACUITY (relative)**: the four hypotheses of `xlkRoad` are EQUIVALENT to those of `Xl.xlRoad`. -/
theorem xlkRoad_hyp_iff :
    ((∀ l, CdRange S l → XlPast S l → CdUpper S l) ↔ (∀ l, CdRange S l → XlKPast S l → CdUpper S l)) ∧
    ((∀ l, CdRange S l → XlPast S l → CdLower S l) ↔ (∀ l, CdRange S l → XlKPast S l → CdLower S l)) ∧
    ((∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XlPast S l → CdCapV S l) ↔
      (∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XlKPast S l → CdCapV S l)) ∧
    ((∀ l, CdRange S l → Nc.ncL S ω < upsilon l → XlPast S l → CdCapV S l) ↔
      (∀ l, CdRange S l → Nc.ncL S ω < upsilon l → XlKPast S l → CdCapV S l)) := by
  refine ⟨⟨fun h l hr hp => h l hr (xlk_past_xl S hp), fun h l hr _ => ?_⟩,
    ⟨fun h l hr hp => h l hr (xlk_past_xl S hp), fun h l hr _ => ?_⟩,
    ⟨fun h l hr hu hp => h l hr hu (xlk_past_xl S hp), fun h l hr hu _ => ?_⟩,
    ⟨fun h l hr hu hp => h l hr hu (xlk_past_xl S hp), fun h l hr hu _ => ?_⟩⟩
  · by_cases hp : XlKPast S l
    · exact h l hr hp
    · exact (xlk_notPast S hr hp).1
  · by_cases hp : XlKPast S l
    · exact h l hr hp
    · exact (xlk_notPast S hr hp).2.1
  · by_cases hp : XlKPast S l
    · exact h l hr hu hp
    · exact (xlk_notPast S hr hp).2.2
  · by_cases hp : XlKPast S l
    · exact h l hr hu hp
    · exact (xlk_notPast S hr hp).2.2

/-- **THE ROAD `Xf.xfRoad` WITH UPPER / LOWER / CapV ASKED ONLY PAST `F_K`.** -/
theorem xlkRoad
    (hUH : ∀ l, CdRange S l → XlKPast S l → CdUpper S l)
    (hLH : ∀ l, CdRange S l → XlKPast S l → CdLower S l)
    (hVH : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XlKPast S l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → XlKPast S l → CdCapV S l)
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
  obtain ⟨a, b, c, d⟩ := xlkRoad_hyp_iff (S := S)
  exact xlRoad (a.2 hUH) (b.2 hLH) (c.2 hVH) (d.2 hVt) hT hF hS h0 hn

/-- **The conclusion of `Xb.xbRoadZ` with UPPER / LOWER / CapV asked only past `F_K`.** -/
theorem xlkRoadZ
    (hUH : ∀ l, CdRange S l → XlKPast S l → CdUpper S l)
    (hLH : ∀ l, CdRange S l → XlKPast S l → CdLower S l)
    (hVH : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XlKPast S l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → XlKPast S l → CdCapV S l)
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
  obtain ⟨a, b, c, d⟩ := xlkRoad_hyp_iff (S := S)
  exact xlRoadZ (a.2 hUH) (b.2 hLH) (c.2 hVH) (d.2 hVt) hT hF hS h0 hn

end Googology.Trans.PoR.InaccPsi.R2.Xl
