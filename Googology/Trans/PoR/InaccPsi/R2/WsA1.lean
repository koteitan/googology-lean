import Googology.Trans.PoR.InaccPsi.R2.WsAll

/-!
# WsA1: THE INSTANCE OF REGION (A1) — `rdc`, `gtc`, `ε_{Ω₁+1}` — AND THE CHECK AGAINST `R2.Wo`

* `wsA1 : WsC` (bound `ε_{Ω₁+1}`, reading `rdc`, gate `gtc`, outer low field `Wh.whZo`);
* the dictionary: `wsA1_good` (`Wo.WoGood ↔ WsGood wsA1`), `wsA1_spec`, `wsA1_ext`, `wsA1_coh`, `wsA1_stepAt`
  (`Wo.WoStepAt ↔ WsStepAt wsA1`); `WoSh`, `WoSm`, `WoFs1`, `WmFs`, `WmLev` are the `wsA1` notions by definition;
* THE CHECK — the `Wo` theorems reproved from the generic modules: `wsA1_step_om1` (= `Wo.woStep_om1`),
  `wsA1_cls` (the classification below `ε_{Ω₁+1}`, from `Wo.wo_fs1`), `wsA1_step_all` (= `Wo.woStep_all`),
  `wsA1_fam` (the statement of `Wo.woFam` for the generic family), `wsA1_sysAll` (= `Wo.woSysAll`), `wsA1_sysA1`
  (= `Wo.woSysA1`, REGION A1).

No new axiom.  New definition: `wsA1`.
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
open Googology.Trans.PoR.InaccPsi.R2.Wo WsC

/-- **THE CODE INTERFACE OF REGION (A1)**: `rdc`, `gtc`, `ε_{Ω₁+1}`, low field `Wh.whZo`. -/
noncomputable def wsA1 : WsC where
  Bd := gfE
  R := rdc
  g := gtc
  Zo := whZo
  Om1_lt := Om1_lt_eW
  Bd_lt1 := gfE_lt_G0.trans (gcG_lt zero_lt_one)
  add_lt := fun _ _ ha hb => eW_indec.add_lt ha hb
  g_lt := gtc_lt_Om1
  R_Om1 := fun x => (rdc_Om1 x).1
  g_Om1 := (rdc_Om1 0).2
  succ_R := fun a ha hd x => (wh_rdc_add_Om1 a ha hd x).1
  succ_g := fun a ha hd => (wh_rdc_add_Om1 a ha hd 0).2
  succ_g_lt := fun hx ha _ hg => wh_gtc_add_Om1_ltE hx ha hg
  g_succ1 := fun hx ht hg => ((rdc_succ _ ht 0).2.2).trans_lt (wo_add_one_lt_inE hx hg)
  le_R := fun hx _ h1 hB _ => wh_le_rdc hx h1 hB
  R_lt := fun hx hx1 _ hg => ((rdc_lt_eN hx _ hg).trans (wh_eN_lt_lgG hx hx1)).trans (mg_lgG_lt_G1 hx hx1)
  R_mono := fun hx _ hc hbc hgc hgb => rdc_mono hx hc hbc hgc hgb
  R_cof := fun hx hx1 hc hg ν hν => by
    obtain ⟨b, hb, hgb, e⟩ := rdc_surj hx hx1.le hc hg hν
    exact ⟨b, hb, hgb, e.ge⟩
  R_pi := fun hB ha hg => rdc_pi hB ha hg
  g_cl := fun ℓ h1 h2 h3 => (whLv ℓ h1 h2 h3).g_cl
  L_mem := fun ℓ h S a b ha hb => by
    have hlt : ℓ < hgU.B := (h.trans gfE_lt_G0).trans_le hgU.G_le
    refine (hgU.mem S a b ha ℓ hlt ?_).1
    rw [hgU.g_lowE ℓ h]; exact hb
  Zo_fix := whZo_fix
  Zo_G1 := fun _ hx hx1 => whZo_G1 hx hx1

/-- **`G` is a base for `wsA1`.** -/
theorem wsA1_G : WsCG wsA1 where
  Bd_le := gfE_lt_G0.le
  R_lt := fun hx hx1 _ hg => (rdc_lt_eN hx _ hg).trans (wh_eN_lt_lgG hx hx1)
  Zo_gt := fun {x ℓ} hx hx1 h1 hB hg => by
    have hlt : rdc ℓ x < lgG x := (rdc_lt_eN hx ℓ hg).trans (wh_eN_lt_lgG hx hx1)
    have hfix := hjG_fix hx hx1 ((wo_one_lt_inE hx).le.trans (wh_le_rdc hx h1 hB)) hlt
    show hdNx (rdc ℓ x) (lgG x) < veblen (eN (max ω x)) (lgG x + 1)
    rw [max_eq_right (omega0_lt_inE hx).le, hdNx_fixP hfix]
    exact hd_veb_left_lt (rdc_lt_eN hx ℓ hg) _

/-! ## The dictionary -/

theorem wsA1_lev {ℓ : Ordinal.{0}} : WmLev ℓ ↔ wsA1.Lev ℓ := Iff.rfl

theorem wsA1_good {r : WoR} {ℓ : Ordinal.{0}} : WoGood r ℓ ↔ WsGood wsA1 r ℓ :=
  ⟨fun h => ⟨h.lev, h.γ_lt, h.F_P, h.G_le, h.S_lt1, h.F_mem, h.S_mem, h.S_memW, h.F_code, h.F_cl, h.S_cl, h.rd,
      h.S_pi, h.Zo_fix, h.Zo_G1, h.Fr_pi⟩,
    fun h => ⟨h.lev, h.γ_lt, h.F_P, h.G_le, h.S_lt1, h.F_mem, h.S_mem, h.S_memW, h.F_code, h.F_cl, h.S_cl, h.rd,
      h.S_pi, h.Zo_fix, h.Zo_G1, h.Fr_pi⟩⟩

theorem wsA1_sh {r : WoR} {ℓ : Ordinal.{0}} {S : HgVD} : WoSh r ℓ S ↔ WsSh wsA1 r ℓ S := Iff.rfl

theorem wsA1_fs {ℓ : Ordinal.{0}} : WmFs ℓ ↔ wsA1.Fs ℓ := Iff.rfl

theorem wsA1_fs1 {ℓ : Ordinal.{0}} {s : Ordinal.{0} → Ordinal.{0}} : WoFs1 ℓ s ↔ wsA1.Fs1 ℓ s := Iff.rfl

theorem wsA1_spec {ℓ : Ordinal.{0}} {E : WoE} : WoSpec ℓ E ↔ WsSpec wsA1 ℓ E :=
  ⟨fun h r S1 hr h1 => h r S1 (wsA1_good.2 hr) h1, fun h r S1 hr h1 => h r S1 (wsA1_good.1 hr) h1⟩

theorem wsA1_ext {ℓ : Ordinal.{0}} {E' E : WoE} : WoExt ℓ E' E ↔ WsExt wsA1 ℓ E' E :=
  ⟨fun h r S1 hr h1 => h r S1 (wsA1_good.2 hr) h1, fun h r S1 hr h1 => h r S1 (wsA1_good.1 hr) h1⟩

theorem wsA1_coh {ℓ : Ordinal.{0}} {f : ∀ μ : Ordinal.{0}, μ < ℓ → WoE} : WoCoh ℓ f ↔ WsCoh wsA1 ℓ f :=
  ⟨fun h => ⟨fun μ hμ hl => wsA1_spec.1 (h.1 μ hμ hl),
      fun μ' μ h' h'' hlt hl' hl => wsA1_ext.1 (h.2 μ' μ h' h'' hlt hl' hl)⟩,
    fun h => ⟨fun μ hμ hl => wsA1_spec.2 (h.1 μ hμ hl),
      fun μ' μ h' h'' hlt hl' hl => wsA1_ext.2 (h.2 μ' μ h' h'' hlt hl' hl)⟩⟩

theorem wsA1_stepAt {ℓ : Ordinal.{0}} : WoStepAt ℓ ↔ WsStepAt wsA1 ℓ := by
  constructor
  · intro h f hc
    obtain ⟨E, hE, hx⟩ := h f (wsA1_coh.2 hc)
    exact ⟨E, wsA1_spec.1 hE, fun μ hμ hl => wsA1_ext.1 (hx μ hμ hl)⟩
  · intro h f hc
    obtain ⟨E, hE, hx⟩ := h f (wsA1_coh.1 hc)
    exact ⟨E, wsA1_spec.2 hE, fun μ hμ hl => wsA1_ext.2 (hx μ hμ hl)⟩

/-! ## The check: the `Wo` theorems from the generic modules -/

/-- **`Wo.woStep_om1` REPROVED** from the generic `Ws.wsStep_om1`. -/
theorem wsA1_step_om1 {ℓ : Ordinal.{0}} {s : Ordinal.{0} → Ordinal.{0}} (hs : WoFs1 ℓ s) : WoStepAt ℓ :=
  wsA1_stepAt.2 (wsStep_om1 (C := wsA1) hs)

/-- **THE CLASSIFICATION BELOW `ε_{Ω₁+1}`** (`Wo.wo_fs1`). -/
theorem wsA1_cls : WsCls wsA1 gfE := fun ℓ hℓ _ h1 h2 h3 => wo_fs1 hℓ h1 h2 h3

/-- **`Wo.woStep_all` REPROVED** from the generic `Ws.wsStep_all`. -/
theorem wsA1_step_all : ∀ ℓ, WmLev ℓ → WoStepAt ℓ := fun ℓ hℓ =>
  wsA1_stepAt.2 (wsStep_all wsA1_cls ℓ hℓ hℓ.2.2)

/-- **The statement of `Wo.woFam` for the generic family `Ws.wsF`.** -/
theorem wsA1_fam : ∀ ℓ, WmLev ℓ → WoSpec ℓ (wsF wsA1_cls ℓ) ∧
    ∀ ℓ', ℓ' < ℓ → WmLev ℓ' → WoExt ℓ (wsF wsA1_cls ℓ') (wsF wsA1_cls ℓ) := fun ℓ hℓ =>
  ⟨wsA1_spec.2 (wsFam wsA1_cls ℓ hℓ hℓ.2.2).1,
    fun ℓ' h h' => wsA1_ext.2 ((wsFam wsA1_cls ℓ hℓ hℓ.2.2).2 ℓ' h h')⟩

/-- **`Wo.woSysAll` REPROVED.** -/
theorem wsA1_sysAll : ∀ ℓ, WmLev ℓ → ∃ V : HgVD, V.B = veblen ℓ (gcG 0 + 1) ∧ V.γ ≤ gtc ℓ := fun ℓ hℓ =>
  wsSysAll wsA1_G wsA1_cls ℓ hℓ hℓ.2.2

/-- **`Wo.woSysA1` REPROVED (REGION A1)**: every `B < φ(ε_{Ω₁+1}, G+1)` is `≤` the bound of a system over `G`
whose gate is below `K`. -/
theorem wsA1_sysA1 (S : InaccSeq.{0}) : ∀ B, B < veblen gfE (gcG 0 + 1) →
    ∃ V : HgVD, B ≤ V.B ∧ V.γ < Td.tdK S := by
  intro B hB
  obtain ⟨ℓ, hℓ, hg, hBl⟩ := whCofLev S B hB
  obtain ⟨V, hVB, hVγ⟩ := wsA1_sysAll ℓ hℓ
  exact ⟨V, hVB ▸ hBl, hVγ.trans_lt hg⟩

end Googology.Trans.PoR.InaccPsi.R2.Ws
