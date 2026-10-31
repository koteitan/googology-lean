import Googology.Trans.PoR.InaccPsi.R2.WsEps

/-!
# WsTop: THE (A2) SYSTEM AT `φ(ε_{Ω₁+ω}, G+1)`; THE NEW FRONTIER; THE ROAD; REGION (A2) FROM THE BASES

* `wsVw` (**the system over `G` at the level `ε_{Ω₁+ω}`**: `B = φ(ε_{Ω₁+ω}, G+1)`, gate `≤ gh ε_{Ω₁+ω} < Γ₀ ≤ K`,
  from the generic family `Ws.wsF` of `wsA2` and the unconditional classification `Ws.wsCls_w`);
* `wsW_loc`, `wsW_enum`, `wsW_capV` (**`φ(ε_{Ω₁+ω}, G+1)` IS LOCATED; ENUM-REACH and CapV at every range restart
  below `F_W = ι(Γ(φ(ε_{Ω₁+ω}, G+1))·ω)`**, UNCONDITIONAL), `wsW_fr_order` (`F_E ≤ F_W`);
* `wsRoad` (**THE ROAD `Wo.woRoad` WITH UPPER / LOWER / CapV ASKED ONLY ABOVE `F_W`**), `wsRoad_hyp_iff` (the four
  new hypotheses are EQUIVALENT to those of `Wo.woRoad`);
* `wsSysA2_base` (**REGION (A2) — every `B < φ(G, 1)` below the bound of a system with gate `< K` — FROM `WsBase G`**:
  the `ε`-number codes `e ∈ [ε_{Ω₁+1}, G)` have sequences of levels), `wsSysA2Lev_base`.

No new axiom.  New definition: `wsVw`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ws

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
open Googology.Trans.PoR.InaccPsi.R2.Wo Googology.Trans.PoR.InaccPsi.R2.Wn Googology.Trans.PoR.InaccPsi.R2.Wp WsC

theorem wsLw_Om1 : Om1 < wsLw := (wsEp_Om1 0).trans (wsEp_lt_Lw 0)

theorem wsLw_lev : wsA2.Lev wsLw := ⟨wsLw_Om1.le, wp_Om1_dvd_E wsLw_E wsLw_Om1, wsLw_lt_G⟩

/-- **THE SYSTEM OVER `G` AT THE LEVEL `ε_{Ω₁+ω}`.** -/
noncomputable def wsVw : HgVD := wsV wsCls_w wsLw

theorem wsVw_B : wsVw.B = veblen wsLw (gcG 0 + 1) := wsV_B wsCls_w wsLw_lev (lt_add_one _)

theorem wsVw_γ : wsVw.γ ≤ gh wsLw := wsV_γ wsCls_w wsLw_lev (lt_add_one _)

/-- `ε_{Ω₁+ω} = φ(1, Ω₁ + ω)` is a code over `Γ₀` with the atom `G`. -/
theorem wsLw_code : GxCl (gamma 0) {gcG 0} wsLw := by
  have hω : ω < gamma 0 := wn_omega_lt_SC (Lq.lq_gamma_SC 0)
  refine GxCl.phi (GxCl.small (one_lt_omega0.trans hω)) (GxCl.add ?_ (GxCl.small hω))
  rw [Br.Om1_eq]; exact GxCl.om

theorem ws_gh_Lw : gh wsLw < gamma 0 :=
  gh_lt_SC (Lq.lq_gamma_SC 0) (Wj.wjDigitGateG (gamma 0) (Lq.lq_gamma_SC 0)
    (by rw [← Br.Om1_eq]; exact gq_gam_lt_Om1.le) _ wsLw_code wsLw_lt_G)

section Fr

variable (S : InaccSeq.{0})

theorem wsVw_γK : wsVw.γ < Td.tdK S :=
  (wsVw_γ.trans_lt ws_gh_Lw).trans_le (Td.tdGam_le_K (S := S))

/-- **`φ(ε_{Ω₁+ω}, G+1)` IS LOCATED**: `Λ⁺ = ι(Γ(φ(ε_{Ω₁+ω}, G+1))·ω)`, `P(…) < L(0)` (UNCONDITIONAL). -/
theorem wsW_loc : ∃ X : Xt.XtSys, Xt.XtTopPkg X ∧ Xt.xtB1 X = iota S (gcG wsVw.B * ω) ∧
    upsilon (Xt.xtB1 X) = Nm.Pv S (gcG wsVw.B * ω) ∧ Nm.Pv S (gcG wsVw.B * ω) < Nc.ncL S 0 :=
  hgV_locD wsVw S (wsVw_γK S)

/-- **ENUM-REACH at every range restart below `ι(Γ(φ(ε_{Ω₁+ω}, G+1))·ω)`** (UNCONDITIONAL). -/
theorem wsW_enum {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG wsVw.B * ω)) :
    CdUpper S l ∧ CdLower S l := hgV_locD_enum wsVw S (wsVw_γK S) hr hl

/-- **CapV at every range restart below `ι(Γ(φ(ε_{Ω₁+ω}, G+1))·ω)`** (UNCONDITIONAL). -/
theorem wsW_capV {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG wsVw.B * ω)) : CdCapV S l :=
  hgV_locD_capV wsVw S (wsVw_γK S) hr hl

/-- **The frontiers in order**: `F_E = ι(Γ(φ(ε_{Ω₁+1}, G+1))·ω) ≤ F_W = ι(Γ(φ(ε_{Ω₁+ω}, G+1))·ω)`. -/
theorem wsW_fr_order : iota S (gcG woVE.B * ω) ≤ iota S (gcG wsVw.B * ω) := by
  have hlt : gfE < wsLw := by rw [← wsEp_zero]; exact wsEp_lt_Lw 0
  have h : woVE.B ≤ wsVw.B := by rw [woVE_B, wsVw_B]; exact (hd_veb_left_lt hlt _).le
  exact iota_mono _ _ (mul_le_mul_right' (gcG_le h) ω)

/-- **THE ROAD `Wo.woRoad` WITH UPPER / LOWER / CapV ASKED ONLY ABOVE `ι(Γ(φ(ε_{Ω₁+ω}, G+1))·ω)`.** -/
theorem wsRoad
    (hUH : ∀ l, CdRange S l → iota S (gcG wsVw.B * ω) ≤ l → CdUpper S l)
    (hLH : ∀ l, CdRange S l → iota S (gcG wsVw.B * ω) ≤ l → CdLower S l)
    (hVH : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S (gcG wsVw.B * ω) ≤ l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → iota S (gcG wsVw.B * ω) ≤ l → CdCapV S l)
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
  refine woRoad S (fun l hr _ => ?_) (fun l hr _ => ?_) (fun l hr hu _ => ?_) (fun l hr hu _ => ?_) hT hF h0 hn
  · rcases lt_or_ge l (iota S (gcG wsVw.B * ω)) with h | h
    · exact (wsW_enum S hr h).1
    · exact hUH l hr h
  · rcases lt_or_ge l (iota S (gcG wsVw.B * ω)) with h | h
    · exact (wsW_enum S hr h).2
    · exact hLH l hr h
  · rcases lt_or_ge l (iota S (gcG wsVw.B * ω)) with h | h
    · exact wsW_capV S hr h
    · exact hVH l hr hu h
  · rcases lt_or_ge l (iota S (gcG wsVw.B * ω)) with h | h
    · exact wsW_capV S hr h
    · exact hVt l hr hu h

/-- **NON-VACUITY (relative)**: the four hypotheses of `wsRoad` are EQUIVALENT to those of `Wo.woRoad`. -/
theorem wsRoad_hyp_iff :
    ((∀ l, CdRange S l → iota S (gcG woVE.B * ω) ≤ l → CdUpper S l) ↔
      (∀ l, CdRange S l → iota S (gcG wsVw.B * ω) ≤ l → CdUpper S l)) ∧
    ((∀ l, CdRange S l → iota S (gcG woVE.B * ω) ≤ l → CdLower S l) ↔
      (∀ l, CdRange S l → iota S (gcG wsVw.B * ω) ≤ l → CdLower S l)) ∧
    ((∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S (gcG woVE.B * ω) ≤ l → CdCapV S l) ↔
      (∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S (gcG wsVw.B * ω) ≤ l → CdCapV S l)) ∧
    ((∀ l, CdRange S l → Nc.ncL S ω < upsilon l → iota S (gcG woVE.B * ω) ≤ l → CdCapV S l) ↔
      (∀ l, CdRange S l → Nc.ncL S ω < upsilon l → iota S (gcG wsVw.B * ω) ≤ l → CdCapV S l)) := by
  have hle := wsW_fr_order S
  refine ⟨⟨fun h l hr hl => h l hr (hle.trans hl), fun h l hr hl => ?_⟩,
    ⟨fun h l hr hl => h l hr (hle.trans hl), fun h l hr hl => ?_⟩,
    ⟨fun h l hr hu hl => h l hr hu (hle.trans hl), fun h l hr hu hl => ?_⟩,
    ⟨fun h l hr hu hl => h l hr hu (hle.trans hl), fun h l hr hu hl => ?_⟩⟩
  · rcases lt_or_ge l (iota S (gcG wsVw.B * ω)) with h' | h'
    · exact (wsW_enum S hr h').1
    · exact h l hr h'
  · rcases lt_or_ge l (iota S (gcG wsVw.B * ω)) with h' | h'
    · exact (wsW_enum S hr h').2
    · exact h l hr h'
  · rcases lt_or_ge l (iota S (gcG wsVw.B * ω)) with h' | h'
    · exact wsW_capV S hr h'
    · exact h l hr hu h'
  · rcases lt_or_ge l (iota S (gcG wsVw.B * ω)) with h' | h'
    · exact wsW_capV S hr h'
    · exact h l hr hu h'

/-- **REGION (A2) FROM THE `ε`-NUMBER BASES**: given `WsBase G`, every `B < φ(G, 1)` is `≤` the bound of a system
over `G` whose gate is below `K`. -/
theorem wsSysA2_base (hb : WsBase (gcG 0)) : ∀ B, B < veblen (gcG 0) 1 → ∃ V : HgVD, B ≤ V.B ∧ V.γ < Td.tdK S :=
  wsA2_sysA2 (wsCls_of_base le_rfl hb) S

/-- **The systems at the cofinal levels `glBn n`** given `WsBase G` (`B = φ(glBn n, G+1)`, gate `< K`). -/
theorem wsSysA2Lev_base (hb : WsBase (gcG 0)) (n : ℕ) :
    ∃ V : HgVD, V.B = veblen (glBn n) (gcG 0 + 1) ∧ V.γ < Td.tdK S := by
  obtain ⟨V, hVB, hγ⟩ := wsA2_sysAll (wsCls_of_base le_rfl hb) _ (wpLev_Bn n)
  exact ⟨V, hVB, (hγ.trans_lt (gh_lt_SC (Lq.lq_gamma_SC 0) (wnGateBn n))).trans_le (Td.tdGam_le_K (S := S))⟩

end Fr

/-- **REGION (A2) BELOW `φ(ε_{Ω₁+ω}, G+1)`, UNCONDITIONAL**: every (A2) level `ℓ ≤ ε_{Ω₁+ω}` has a system over `G`
with `B = φ(ℓ, G+1)` and gate `≤ gh ℓ`. -/
theorem wsSysW : ∀ ℓ, WpLev ℓ → ℓ ≤ wsLw → ∃ V : HgVD, V.B = veblen ℓ (gcG 0 + 1) ∧ V.γ ≤ gh ℓ :=
  fun ℓ hℓ hle => wsSysAll wsCls_w ℓ hℓ (Order.lt_add_one_iff.2 hle)

end Googology.Trans.PoR.InaccPsi.R2.Ws
