import Googology.Trans.PoR.InaccPsi.R2.WxBase

/-!
# WxTop: REGION (A2) CLOSED WITH NO HYPOTHESIS; THE FRONTIER AT THE END OF (A2)

From `Wx.wx_baseI` (`WsBaseI G`, unconditional):

* `wxClsA2` (**THE (A2) CLASSIFICATION `WsCls wsA2 G`**), `wxSysAllG2` (systems over `G` at every (A2) level, gate
  `≤ gh ℓ`), `wxSysA2Lev` (at the cofinal levels `glBn n`, gate `< K`), `wxSysA2` (**REGION (A2)**: every
  `B < φ(G, 1)` is `≤` the bound of a system over `G` with gate `< K`);
* `wxA2_enum` / `wxA2_capV` (**UPPER, LOWER, CapV at every range restart `λ < ι(Γ(B)·ω)` for some `B < φ(G, 1)`**);
  the frontier is `F_{A2} = sup_{B < φ(G,1)} ι(Γ(B)·ω) = sup_n ι(Γ(φ(glBn n, G+1))·ω)` (`wxFA2_cof`), and
  `ι(Γ(B)·ω) ≤ ι(Γ(φ(G, 1)))` for every such `B` (`wxFA2_le`);
* `wxRoadA2` (**THE ROAD WITH UPPER / LOWER / CapV ASKED ONLY AT `λ ≥ F_{A2}`**, i.e. at `λ` with
  `ι(Γ(B)·ω) ≤ λ` for every `B < φ(G, 1)`; the other hypotheses are those of `Ws.wsRoadZ` / `Wo.woRoad`),
  `wxRoadA2_hyp_iff` (its four hypotheses are EQUIVALENT to those of `Ws.wsRoadZ`).

No new axiom.  New definition: `WxPast` (the frontier condition `∀ B < φ(G, 1), ι(Γ(B)·ω) ≤ λ`).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Wx

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
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Bt
open Googology.Trans.PoR.InaccPsi.R2.Wo Googology.Trans.PoR.InaccPsi.R2.Wn Googology.Trans.PoR.InaccPsi.R2.Wp
open Googology.Trans.PoR.InaccPsi.R2.Gk
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Bt
open Googology.Trans.PoR.InaccPsi.R2.Ws Googology.Trans.PoR.InaccPsi.R2.Ws.WsC

/-- **THE (A2) CLASSIFICATION**, UNCONDITIONAL. -/
theorem wxClsA2 : WsCls wsA2 (gcG 0) := wsCls_of_baseI le_rfl wx_baseI

/-- **THE SYSTEMS OVER `G` AT EVERY (A2) LEVEL**, UNCONDITIONAL: `B = φ(ℓ, G+1)`, gate `≤ gh ℓ`. -/
theorem wxSysAllG2 : ∀ ℓ, WpLev ℓ → ∃ V : HgVD, V.B = veblen ℓ (gcG 0 + 1) ∧ V.γ ≤ gh ℓ :=
  wsA2_sysAll wxClsA2

theorem wxSysA2Lev (S : InaccSeq.{0}) (n : ℕ) :
    ∃ V : HgVD, V.B = veblen (glBn n) (gcG 0 + 1) ∧ V.γ < Td.tdK S :=
  wsSysA2Lev_baseI S wx_baseI n

/-- **REGION (A2), UNCONDITIONAL**: every `B < φ(G, 1)` is `≤` the bound of a system over `G` with gate `< K`. -/
theorem wxSysA2 (S : InaccSeq.{0}) : ∀ B, B < veblen (gcG 0) 1 → ∃ V : HgVD, B ≤ V.B ∧ V.γ < Td.tdK S :=
  wsSysA2_baseI S wx_baseI

section Fr

variable (S : InaccSeq.{0})

/-- **The frontier condition at the end of (A2)**: `ι(Γ(B)·ω) ≤ λ` for every `B < φ(G, 1)`. -/
def WxPast (l : Ordinal.{0}) : Prop := ∀ B, B < veblen (gcG 0) 1 → iota S (gcG B * ω) ≤ l

theorem wx_past_iff {l : Ordinal.{0}} : WxPast S l ↔ ¬ ∃ B, B < veblen (gcG 0) 1 ∧ l < iota S (gcG B * ω) := by
  constructor
  · rintro h ⟨B, hB, hl⟩; exact absurd (h B hB) (not_le.2 hl)
  · intro h B hB; by_contra hc; exact h ⟨B, hB, not_le.1 hc⟩

theorem wx_sysOf {l : Ordinal.{0}} (hl : ∃ B, B < veblen (gcG 0) 1 ∧ l < iota S (gcG B * ω)) :
    ∃ V : HgVD, V.γ < Td.tdK S ∧ l < iota S (gcG V.B * ω) := by
  obtain ⟨B, hB, hlB⟩ := hl
  obtain ⟨V, hBV, hγ⟩ := wxSysA2 S B hB
  exact ⟨V, hγ, hlB.trans_le (iota_mono (S := S) _ _ (mul_le_mul_left (gcG_le hBV) ω))⟩

/-- **ENUM-REACH below the end of (A2)** (UNCONDITIONAL). -/
theorem wxA2_enum {l : Ordinal.{0}} (hr : CdRange S l)
    (hl : ∃ B, B < veblen (gcG 0) 1 ∧ l < iota S (gcG B * ω)) : CdUpper S l ∧ CdLower S l := by
  obtain ⟨V, hγ, hlV⟩ := wx_sysOf S hl
  exact hgV_locD_enum V S hγ hr hlV

/-- **CapV below the end of (A2)** (UNCONDITIONAL). -/
theorem wxA2_capV {l : Ordinal.{0}} (hr : CdRange S l)
    (hl : ∃ B, B < veblen (gcG 0) 1 ∧ l < iota S (gcG B * ω)) : CdCapV S l := by
  obtain ⟨V, hγ, hlV⟩ := wx_sysOf S hl
  exact hgV_locD_capV V S hγ hr hlV

theorem wx_G_lt_G1 : gcG 0 + 1 < veblen (gcG 0) 1 := by
  have hl : IsSuccLimit (veblen (gcG 0) 1) := Ta.taVeb_lim gl_G0_E.pos.ne'
  exact hl.add_one_lt ((left_le_veblen _ 0).trans_lt ((veblen_lt_veblen_iff_right).2 zero_lt_one))

theorem wx_lev_lt_G1 {ℓ : Ordinal.{0}} (hℓ : ℓ < gcG 0) : veblen ℓ (gcG 0 + 1) < veblen (gcG 0) 1 :=
  calc veblen ℓ (gcG 0 + 1) < veblen ℓ (veblen (gcG 0) 1) := (veblen_lt_veblen_iff_right).2 wx_G_lt_G1
    _ = veblen (gcG 0) 1 := veblen_veblen_of_lt hℓ _

/-- **The frontier is the supremum over the cofinal levels**: past every `ι(Γ(φ(glBn n, G+1))·ω)` iff `WxPast`. -/
theorem wxFA2_cof {l : Ordinal.{0}} :
    WxPast S l ↔ ∀ n : ℕ, iota S (gcG (veblen (glBn n) (gcG 0 + 1)) * ω) ≤ l := by
  constructor
  · intro h n; exact h _ (wx_lev_lt_G1 (glBn_spec n).1)
  · intro h B hB
    obtain ⟨n, hn⟩ := Wj.wjA2Cof hB
    exact (iota_mono (S := S) _ _ (mul_le_mul_left (gcG_le hn.le) ω)).trans (h n)

/-- `ι(Γ(B)·ω) ≤ ι(Γ(φ(G, 1)))` for every `B < φ(G, 1)`. -/
theorem wxFA2_le {B : Ordinal.{0}} (hB : B < veblen (gcG 0) 1) :
    iota S (gcG B * ω) ≤ iota S (gcG (veblen (gcG 0) 1)) := by
  refine iota_mono (S := S) _ _ ?_
  have hE : InE (gcG B) := Low.opow_eq_self_of_SC (gcG_SC B)
  have hE' : InE (gcG (veblen (gcG 0) 1)) := Low.opow_eq_self_of_SC (gcG_SC _)
  have hlt : gcG B < gcG (veblen (gcG 0) 1) := gcG_lt hB
  calc gcG B * ω = ω ^ (gcG B + 1) := by
        conv_lhs => rw [← hE]
        rw [opow_add, opow_one]
    _ ≤ ω ^ gcG (veblen (gcG 0) 1) :=
        opow_le_opow_right omega0_pos (Order.add_one_le_of_lt hlt)
    _ = gcG (veblen (gcG 0) 1) := hE'

theorem wx_FZ_past {l : Ordinal.{0}} (h : WxPast S l) : iota S (gcG wsVz.B * ω) ≤ l := by
  refine h _ ?_
  rw [wsVz_B]; exact wx_lev_lt_G1 wsZ_lt_G

/-- **THE ROAD WITH UPPER / LOWER / CapV ASKED ONLY PAST THE END OF (A2).** -/
theorem wxRoadA2
    (hUH : ∀ l, CdRange S l → WxPast S l → CdUpper S l)
    (hLH : ∀ l, CdRange S l → WxPast S l → CdLower S l)
    (hVH : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → WxPast S l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → WxPast S l → CdCapV S l)
    (hT : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdThLow S)
    (hF : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdEQfar S)
    (h0 : ∀ l, IsRestartIdx l → Nc.ncL S 0 = upsilon l →
      Wf.WfVisGen S l (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Te.teW (Nc.ncL S 0))))
    (hn : ∀ n : ℕ, ∀ l, IsRestartIdx l → Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) = upsilon l →
      Wf.WfVisGen S l (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
        (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Te.teW (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))) :
    CdTC S ∧ CdEMB2 S ∧ CdCL S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S (k + 1)) (Nc.ncL S (ω + 1)) := by
  refine wsRoadZ S (fun l hr _ => ?_) (fun l hr _ => ?_) (fun l hr hu _ => ?_) (fun l hr hu _ => ?_) hT hF h0 hn
  · by_cases h : ∃ B, B < veblen (gcG 0) 1 ∧ l < iota S (gcG B * ω)
    · exact (wxA2_enum S hr h).1
    · exact hUH l hr ((wx_past_iff S).2 h)
  · by_cases h : ∃ B, B < veblen (gcG 0) 1 ∧ l < iota S (gcG B * ω)
    · exact (wxA2_enum S hr h).2
    · exact hLH l hr ((wx_past_iff S).2 h)
  · by_cases h : ∃ B, B < veblen (gcG 0) 1 ∧ l < iota S (gcG B * ω)
    · exact wxA2_capV S hr h
    · exact hVH l hr hu ((wx_past_iff S).2 h)
  · by_cases h : ∃ B, B < veblen (gcG 0) 1 ∧ l < iota S (gcG B * ω)
    · exact wxA2_capV S hr h
    · exact hVt l hr hu ((wx_past_iff S).2 h)

/-- **NON-VACUITY (relative)**: the four hypotheses of `wxRoadA2` are EQUIVALENT to those of `Ws.wsRoadZ`. -/
theorem wxRoadA2_hyp_iff :
    ((∀ l, CdRange S l → iota S (gcG wsVz.B * ω) ≤ l → CdUpper S l) ↔
      (∀ l, CdRange S l → WxPast S l → CdUpper S l)) ∧
    ((∀ l, CdRange S l → iota S (gcG wsVz.B * ω) ≤ l → CdLower S l) ↔
      (∀ l, CdRange S l → WxPast S l → CdLower S l)) ∧
    ((∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S (gcG wsVz.B * ω) ≤ l → CdCapV S l) ↔
      (∀ l, CdRange S l → upsilon l < Nc.ncL S ω → WxPast S l → CdCapV S l)) ∧
    ((∀ l, CdRange S l → Nc.ncL S ω < upsilon l → iota S (gcG wsVz.B * ω) ≤ l → CdCapV S l) ↔
      (∀ l, CdRange S l → Nc.ncL S ω < upsilon l → WxPast S l → CdCapV S l)) := by
  refine ⟨⟨fun h l hr hp => h l hr (wx_FZ_past S hp), fun h l hr _ => ?_⟩,
    ⟨fun h l hr hp => h l hr (wx_FZ_past S hp), fun h l hr _ => ?_⟩,
    ⟨fun h l hr hu hp => h l hr hu (wx_FZ_past S hp), fun h l hr hu _ => ?_⟩,
    ⟨fun h l hr hu hp => h l hr hu (wx_FZ_past S hp), fun h l hr hu _ => ?_⟩⟩
  · by_cases h' : ∃ B, B < veblen (gcG 0) 1 ∧ l < iota S (gcG B * ω)
    · exact (wxA2_enum S hr h').1
    · exact h l hr ((wx_past_iff S).2 h')
  · by_cases h' : ∃ B, B < veblen (gcG 0) 1 ∧ l < iota S (gcG B * ω)
    · exact (wxA2_enum S hr h').2
    · exact h l hr ((wx_past_iff S).2 h')
  · by_cases h' : ∃ B, B < veblen (gcG 0) 1 ∧ l < iota S (gcG B * ω)
    · exact wxA2_capV S hr h'
    · exact h l hr hu ((wx_past_iff S).2 h')
  · by_cases h' : ∃ B, B < veblen (gcG 0) 1 ∧ l < iota S (gcG B * ω)
    · exact wxA2_capV S hr h'
    · exact h l hr hu ((wx_past_iff S).2 h')

end Fr

end Googology.Trans.PoR.InaccPsi.R2.Wx
