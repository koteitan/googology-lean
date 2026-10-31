import Googology.Trans.PoR.InaccPsi.R2.WsA1
import Googology.Trans.PoR.InaccPsi.R2.WpStep

/-!
# WsA2: THE INSTANCE OF REGION (A2) — `glR`, `glG`, `G` — AND REGION (A2) FROM ITS CLASSIFICATION

* `wsA2 : WsC` (bound `G = Γ_{Ω₁+1}`, reading `Gl.glR`, gate `gh = max 1 glG`, outer low field `Wn.wnZo`): every field from
  `Gl` / `Wn` (`Wn.wn_glR_add_Om1`, `Gl.glR_mono`, `Gl.glR_cof`, `Gl.gl_pi`, `Wn.wnLv`'s digit gate, `Gl.gl_mem`,
  `Wn.wn_S_Zo`);
* `gh = max 1 glG` (the gate; same cut as `glG` at every `ε`-number), `wsA2_fs_of` (`Wp.WpFs ⇒ wsA2.Fs`),
  `wsA2_lev` (`Wp.WpLev ↔ wsA2.Lev`);
* `wsA2_clsE` (**THE (A2) CLASSIFICATION BELOW `ε_{Ω₁+1}`**, from `Wo.wo_fs1`: below `ε_{Ω₁+1}` the gates agree);
* `wsA2_fam`, `wsA2_sysAll`, `wsA2_sysA2` (**REGION (A2)**: every `B < φ(G, 1)` is `≤` the bound of a system over
  `G` with gate below `K`) given the classification `WsCls wsA2 G` — the one remaining hypothesis, code arithmetic
  only;
* `wsA2_sysE`: the same with no hypothesis below `ε_{Ω₁+1}`.

No new axiom.  New definitions: `gh`, `wsA2`.
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
open Googology.Trans.PoR.InaccPsi.R2.Wo Googology.Trans.PoR.InaccPsi.R2.Wn Googology.Trans.PoR.InaccPsi.R2.Wp WsC

/-- **THE GATE OF REGION (A2)**: `max 1 (glG c)`.  `Gl.glG` ignores finite parts (`Gl.glQ`) above `ε_{Ω₁+1}` but
counts them below (`gtc`), so `glG ε_{Ω₁+1} = 0` while every level below has gate `≥ 1` (`ws_glG_E_noFs`); the two
gates have the same cut at every `ε`-number. -/
noncomputable def gh (c : Ordinal.{0}) : Ordinal.{0} := max 1 (glG c)

theorem gh_lt_iff {c x : Ordinal.{0}} (hx : InE x) : gh c < x ↔ glG c < x :=
  ⟨fun h => (le_max_right _ _).trans_lt h, fun h => max_lt (wo_one_lt_inE hx) h⟩

theorem gh_lt_SC {c Z : Ordinal.{0}} (hZ : SC Z) (h : glG c < Z) : gh c < Z :=
  max_lt (one_lt_omega0.trans (wn_omega_lt_SC hZ)) h

theorem glG_le_gh (c : Ordinal.{0}) : glG c ≤ gh c := le_max_right _ _

/-- **THE CODE INTERFACE OF REGION (A2)**: `glR`, gate `gh = max 1 glG`, `G`, low field `Wn.wnZo`. -/
noncomputable def wsA2 : WsC where
  Bd := gcG 0
  R := glR
  g := gh
  Zo := wnZo
  Om1_lt := gl_Om1_lt_G0
  Bd_le := le_rfl
  add_lt := fun _ _ ha hb => (inE_indec gl_G0_E).add_lt ha hb
  g_lt := fun a ha => max_lt wh_one_lt_Om1 (glG_lt_Om1 a ha)
  R_Om1 := fun x => by rw [glR_low Om1_lt_eW, (rdc_Om1 x).1]
  g_Om1 := by unfold gh; rw [glG_low Om1_lt_eW, (rdc_Om1 0).2, max_self]
  succ_R := fun a ha hd x => (wn_glR_add_Om1 a ha hd x).1
  succ_g := fun a ha hd => max_le_max le_rfl (wn_glR_add_Om1 a ha hd 0).2
  succ_g_lt := fun hx ha _ hg => (gh_lt_iff hx).2 (wn_glG_add_Om1_lt hx ha ((gh_lt_iff hx).1 hg))
  g_succ1 := fun {x t} hx ht hg => (gh_lt_iff hx).2
    (glG_succ (ev_isSuccLimit_of_inE hx) t ((inE_indec gl_G0_E).add_lt ht gl_one_lt_G0) ((gh_lt_iff hx).1 hg))
  le_R := fun hx hx1 h1 hB hg => wn_le_glR hx hx1 h1 hB ((gh_lt_iff hx).1 hg)
  R_lt := fun hx hx1 hB hg => glR_lt_G hx hx1 hB ((gh_lt_iff hx).1 hg)
  R_mono := fun hx hx1 hc hbc hgc hgb => glR_mono hx hx1 hc hbc ((gh_lt_iff hx).1 hgc) ((gh_lt_iff hx).1 hgb)
  R_cof := fun hx hx1 hc hg ν hν => by
    obtain ⟨b, hb, hgb, hνb⟩ := glR_cof hx hx1 _ hc ((gh_lt_iff hx).1 hg) ν hν
    exact ⟨b, hb, (gh_lt_iff hx).2 hgb, hνb⟩
  R_pi := fun hB ha hg => gl_pi hB _ ha ((gh_lt_iff hB.1).1 hg)
  g_cl := fun ℓ h1 h2 h3 Z y hZ hZ1 hy hLy hy2 => gh_lt_SC hZ ((wnLv ℓ h1 h2 h3).g_cl Z y hZ hZ1 hy hLy hy2)
  L_mem := fun ℓ h _ _ _ _ hb => (gl_mem ℓ h ((glG_le_gh ℓ).trans_lt hb)).1
  Zo_fix := wnZo_fix
  Zo_G1 := fun _ hx hx1 => wnZo_G1 hx hx1
  Zo_gt := fun hx hx1 h1 hB hg =>
    wn_S_Zo hx hx1 ((wo_one_lt_inE hx).le.trans (wn_le_glR hx hx1 h1 hB ((gh_lt_iff hx).1 hg)))
      (glR_lt_G hx hx1 hB ((gh_lt_iff hx).1 hg))

theorem wsA2_lev {ℓ : Ordinal.{0}} : WpLev ℓ ↔ wsA2.Lev ℓ := Iff.rfl

/-- **Every `Wp.WpFs` sequence is a `wsA2.Fs` sequence.** -/
theorem wsA2_fs_of {ℓ : Ordinal.{0}} (h : WpFs ℓ) : wsA2.Fs ℓ := by
  obtain ⟨ls, h1, h2, h3, h4, h5⟩ := h
  exact ⟨ls, h1, h2, h3, h4, fun k => max_le_max le_rfl (h5 k)⟩

/-! ## The classification below `ε_{Ω₁+1}` -/

/-- Below `ε_{Ω₁+1}` an `Ω₁`-sequence for the gate `gtc` is one for the gate `glG`. -/
theorem wsA2_seq_of_A1 {a : Ordinal.{0}} {s : Ordinal.{0} → Ordinal.{0}} (ha : a < gfE) (h : WoSeq1 a s) :
    wsA2.Seq1 a s := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hlow : ∀ b, b < a → glG b = gtc b := fun b hb => glG_low (hb.trans ha)
  refine ⟨h1, h2, fun x hx hx1 hg μ hμ => ?_, fun σ hσ hσ1 b hb hg => ?_⟩
  · show gh (s μ) < x
    rw [gh_lt_iff hx, hlow _ (h1 μ (hμ.trans hx1)).2]
    exact h3 x hx hx1 (by rw [← glG_low ha]; exact (gh_lt_iff hx).1 hg) μ hμ
  · exact h4 σ hσ hσ1 b hb (by rw [← hlow b hb]; exact (gh_lt_iff hσ).1 hg)

/-- **THE (A2) CLASSIFICATION BELOW `ε_{Ω₁+1}`** (from `Wo.wo_fs1`). -/
theorem wsA2_clsE : WsCls wsA2 gfE := by
  intro ℓ hℓ hE h1 h2 h3
  have hℓ' : WmLev ℓ := ⟨hℓ.1, hℓ.2.1, hE⟩
  have h2' : ¬ ∃ ℓ', WmLev ℓ' ∧ ℓ = ℓ' + Om1 := fun ⟨ℓ', hl, he⟩ =>
    h2 ⟨ℓ', ⟨hl.1, hl.2.1, hl.2.2.trans gfE_lt_G0⟩, he⟩
  have h3' : ¬ WmFs ℓ := fun h => h3 (wsA2_fs_of (wpFs_of_wm hE h))
  obtain ⟨s, hs1, hs2⟩ := wo_fs1 hℓ' h1 h2' h3'
  exact ⟨s, wsA2_seq_of_A1 hE hs1, hs2⟩

/-! ## Region (A2) from the classification -/

section Fam

variable (hc : WsCls wsA2 (gcG 0))
include hc

/-- **THE (A2) FAMILY** given the classification. -/
theorem wsA2_fam : ∀ ℓ, WpLev ℓ → WsSpec wsA2 ℓ (wsF hc ℓ) ∧
    ∀ ℓ', ℓ' < ℓ → WpLev ℓ' → WsExt wsA2 ℓ (wsF hc ℓ') (wsF hc ℓ) := fun ℓ hℓ =>
  wsFam hc ℓ hℓ hℓ.2.2

/-- **THE SYSTEMS OVER `G` AT EVERY (A2) LEVEL** given the classification (the statement of `Wp.wpSysAll` at `G`). -/
theorem wsA2_sysAll : ∀ ℓ, WpLev ℓ → ∃ V : HgVD, V.B = veblen ℓ (gcG 0 + 1) ∧ V.γ ≤ gh ℓ := fun ℓ hℓ =>
  wsSysAll hc ℓ hℓ hℓ.2.2

/-- **REGION (A2)** given the classification: every `B < φ(G, 1)` is `≤` the bound of a system over `G` whose gate
is below `K`. -/
theorem wsA2_sysA2 (S : InaccSeq.{0}) : ∀ B, B < veblen (gcG 0) 1 → ∃ V : HgVD, B ≤ V.B ∧ V.γ < Td.tdK S := by
  intro B hB
  obtain ⟨n, hn⟩ := Wj.wjA2Cof hB
  obtain ⟨V, hVB, hγ⟩ := wsA2_sysAll hc _ (wpLev_Bn n)
  have hG0 : gh (glBn n) < gamma 0 := gh_lt_SC (Lq.lq_gamma_SC 0) (wnGateBn n)
  exact ⟨V, hVB ▸ hn.le, (hγ.trans_lt hG0).trans_le (Td.tdGam_le_K (S := S))⟩

end Fam

/-- **THE SYSTEMS OVER `G` AT EVERY (A2) LEVEL BELOW `ε_{Ω₁+1}`**, with no hypothesis (non-vacuity of the (A2)
family). -/
theorem wsA2_sysE : ∀ ℓ, WpLev ℓ → ℓ < gfE → ∃ V : HgVD, V.B = veblen ℓ (gcG 0 + 1) ∧ V.γ ≤ gh ℓ :=
  fun ℓ hℓ hE => wsSysAll wsA2_clsE ℓ hℓ hE

end Googology.Trans.PoR.InaccPsi.R2.Ws
