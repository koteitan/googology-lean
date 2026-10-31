import Googology.Trans.PoR.InaccPsi.R2.WpSys
import Googology.Trans.PoR.InaccPsi.R2.WpGate
import Googology.Trans.PoR.InaccPsi.R2.WmA1

/-!
# WpStep: REGION (A2) ON THE CORRECTED COHERENCE, REDUCED TO ONE `Ω₁`-COFINAL STEP

The (A2) induction of round 117 (`Wn.WnAt` entries) related packages by the old `Hn.HnkExt`, which is vacuous across
a gate drop (`Wm.wm_old_vacuous`); a gate drop happens between (A2) levels too (`wp_gate_drop`).  Here the (A2)
coherence uses the corrected entry relation `Wm.WmExtE` (packages by `Wm.WmExt`, lowering by the pseudo-base gate);
it implies the old one (`wpCoh_old`).

* `WpLev`, `WpCoh`, `WpStepAt` (**the corrected (A2) step**: entries `Wn.WnAt`, relation `Wm.WmExtE`);
* `wpStep_base`, `wpStep_succ`, `wpStep_fs` (**EVERY (A2) LEVEL WITH AN `ω`-SEQUENCE `WpFs`**), `wpStep_coef`
  (**every coefficient limit `P + Ω₁^e·c`, unconditional**), `wpStep_Bn` (**every cofinal level `glBn n`**);
* `WpOm1Step L` (the step at the remaining levels `< L`: not `Ω₁`, not a successor, no `ω`-sequence),
  `wpStep_all`, `wpFam`, `wpSysAll` (**the (A2) family and its systems from `WpOm1Step G`**), `wpSysA2Lev`,
  `wpSysA2` (**REGION (A2) GIVEN THE ONE REMAINING CASE**: every `B < φ(G, 1)` is below a system with gate `< K`);
* `wpOm1Step_sq`, `wpFam_sq` (**non-vacuity: the remaining case is empty below `Ω₁²`; the family on `[Ω₁, Ω₁²)`**).

No new axiom.  New definitions: `WpLev`, `WpCoh`, `WpStepAt`, `WpOm1Step`, `wpG`, `wpF`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Wp

open Googology.Trans.PoR.InaccPsi.R2.Wh Googology.Trans.PoR.InaccPsi.R2.Ho
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
open Googology.Trans.PoR.InaccPsi.R2.Wm Googology.Trans.PoR.InaccPsi.R2.Wn Googology.Trans.PoR.InaccPsi.R2.Gk

/-- The (A2) level codes: `Ω₁ ≤ ℓ`, `Ω₁ ∣ ℓ`, `ℓ < G`. -/
def WpLev (ℓ : Ordinal.{0}) : Prop := Om1 ≤ ℓ ∧ Om1 ∣ ℓ ∧ ℓ < gcG 0

/-- **THE CORRECTED (A2) COHERENCE** of a family below `ℓ`: (A2) entries `Wn.WnAt` at every level, `Wm.WmExtE` between
levels. -/
def WpCoh (ℓ : Ordinal.{0}) (f : ∀ ℓ' : Ordinal.{0}, ℓ' < ℓ → WmEnt) : Prop :=
  (∀ ℓ' (h : ℓ' < ℓ), WpLev ℓ' → WnAt ℓ' (f ℓ' h).1 (f ℓ' h).2.down) ∧
    ∀ ℓ'' ℓ' (h'' : ℓ'' < ℓ) (h' : ℓ' < ℓ), ℓ'' < ℓ' → WpLev ℓ'' → WpLev ℓ' → WmExtE (f ℓ'' h'') (f ℓ' h')

/-- **The corrected (A2) step at `ℓ`**: every coherent family below `ℓ` has an (A2) entry at `ℓ` extending all of it. -/
def WpStepAt (ℓ : Ordinal.{0}) : Prop :=
  ∀ f, WpCoh ℓ f → ∃ E : WmEnt, WnAt ℓ E.1 E.2.down ∧ ∀ ℓ' (h : ℓ' < ℓ), WpLev ℓ' → WmExtE (f ℓ' h) E

/-- **The corrected (A2) coherence implies the old one** (`Hn.HnkExt` between packages; = the skeleton's `SkCohWG`). -/
theorem wpCoh_old {ℓ : Ordinal.{0}} {f : ∀ ℓ' : Ordinal.{0}, ℓ' < ℓ → WmEnt} (h : WpCoh ℓ f) :
    (∀ ℓ' (h' : ℓ' < ℓ), WpLev ℓ' → WnAt ℓ' (f ℓ' h').1 (f ℓ' h').2.down) ∧
    ∀ ℓ'' ℓ' (h'' : ℓ'' < ℓ) (h' : ℓ' < ℓ), ℓ'' < ℓ' → WpLev ℓ'' → WpLev ℓ' →
      WhExt (f ℓ'' h'').1 (f ℓ'' h'').2.down (f ℓ' h').1 (f ℓ' h').2.down :=
  ⟨h.1, fun a b ha hb hab h1 h2 => wmExtE_old (h.2 a b ha hb hab h1 h2)⟩

/-- **A GATE DROP BETWEEN TWO (A2) LEVELS**: `Ω₁·ω < Ω₁·Ω₁`, `glG (Ω₁·Ω₁) = 2 < ω = glG (Ω₁·ω)`. -/
theorem wp_gate_drop : WpLev (Om1 * ω) ∧ WpLev (Om1 * Om1) ∧ Om1 * ω < Om1 * Om1 ∧
    glG (Om1 * Om1) = 2 ∧ glG (Om1 * ω) = ω := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := wm_gate_drop
  exact ⟨⟨h1.1, h1.2.1, h1.2.2.trans gfE_lt_G0⟩, ⟨h2.1, h2.2.1, h2.2.2.trans gfE_lt_G0⟩, h3,
    by rw [glG_low h2.2.2, h4], by rw [glG_low h1.2.2, h5]⟩

/-! ## The steps -/

/-- **The step at `Ω₁`**: `Hn.hnPk1` and `Hg.hgU` (`Wn.wnAt_base`). -/
theorem wpStep_base : WpStepAt Om1 := fun _ _ =>
  ⟨(hnPk1, ULift.up hgU), wnAt_base, fun _ h hl => absurd hl.1 (not_le.2 h)⟩

/-- **THE SUCCESSOR STEP** `ℓ = ℓ' + Ω₁` on the corrected (A2) coherence (`Wn.wnSucc_at`, `wpSucc_ext_lt`). -/
theorem wpStep_succ {ℓ' : Ordinal.{0}} (hℓ' : WpLev ℓ') (hℓ : ℓ' + Om1 < gcG 0) : WpStepAt (ℓ' + Om1) := by
  intro f ⟨hat, hext⟩
  have hlt : ℓ' < ℓ' + Om1 := lt_add_of_pos_right _ wh_Om1_pos
  have hat' := hat ℓ' hlt hℓ'
  refine ⟨((f ℓ' hlt).1.succ, ULift.up (wnSuccV hat')), wnSucc_at hℓ'.2.1 hℓ'.2.2 hat', fun ℓ'' h'' hℓ'' => ?_⟩
  have hle : ℓ'' ≤ ℓ' := not_lt.1 fun h => absurd h'' (not_lt.2 (wh_lev_succ_le hℓ'.2.1 hℓ''.2.1 h))
  rcases hle.lt_or_eq with hl | rfl
  · have he := hext ℓ'' ℓ' h'' hlt hl hℓ'' hℓ'
    have hold := wnSucc_ext_lt hℓ'.2.1 hℓ'.2.2 hat' hl hℓ''.2.1 (hat ℓ'' h'' hℓ'') (wmExtE_old he)
    exact ⟨wpSucc_ext_lt (hat ℓ'' h'' hℓ'') hat' hℓ''.2.1 hℓ'.2.1 hl hℓ'.2.2 he.1, hold.2.1, hold.2.2⟩
  · have hold := wnSucc_ext hat'
    exact ⟨wmSucc_ext _, hold.2.1, hold.2.2⟩

/-- **THE `ω`-LIMIT STEP**: every (A2) level with an `ω`-sequence `WpFs` (`WpLim`). -/
theorem wpStep_fs {ℓ : Ordinal.{0}} (hℓ : WpLev ℓ) (hfs : WpFs ℓ) : WpStepAt ℓ := by
  intro f ⟨hat, hext⟩
  obtain ⟨ls, hlev, hmono, hlt, hcof, hg⟩ := hfs
  have hL : ∀ k, WpLev (ls k) := fun k => ⟨(hlev k).1, (hlev k).2, (hlt k).trans hℓ.2.2⟩
  let W : WpLim ℓ :=
    { h1 := hℓ.1, h2 := hℓ.2.1, h3 := hℓ.2.2, ls := ls, lev := hlev, mono := hmono, lt := hlt, cof := hcof,
      gate := hg, K := fun k => (f (ls k) (hlt k)).1, V := fun k => (f (ls k) (hlt k)).2.down,
      at' := fun k => hat (ls k) (hlt k) (hL k),
      ext := fun k => (hext (ls k) (ls (k + 1)) (hlt k) (hlt (k + 1)) (hmono k) (hL k) (hL (k + 1))).1,
      vext := fun k c x hc => (hext (ls k) (ls (k + 1)) (hlt k) (hlt (k + 1)) (hmono k) (hL k) (hL (k + 1))).2.2 c x hc }
  refine ⟨(W.K', ULift.up W.V'), W.at_lim, fun ℓ' h' hℓ' => ?_⟩
  obtain ⟨k, hk⟩ := hcof ℓ' h'
  have hlk : ℓ' < ls k := (lt_add_one ℓ').trans hk
  have he := hext ℓ' (ls k) h' (hlt k) hlk hℓ' (hL k)
  exact W.ext_below (hat ℓ' h' hℓ') hℓ'.2.1 k hlk he.1 he.2.1 he.2.2

/-- **THE COEFFICIENT-LIMIT STEP** `ℓ = P + Ω₁^e·c < G` (`1 ≤ e`, `c < Ω₁` a limit, `Ω₁^{e+1} ∣ P`), UNCONDITIONAL. -/
theorem wpStep_coef {P e c : Ordinal.{0}} (he : 1 ≤ e) (hc : IsSuccLimit c) (hcO : c < Om1)
    (hP : Om1 ^ (e + 1) ∣ P) (hℓ : WpLev (P + Om1 ^ e * c)) : WpStepAt (P + Om1 ^ e * c) :=
  wpStep_fs hℓ (wpFs_coef he hc hcO hP hℓ.2.2)

/-- **THE STEP AT EVERY COFINAL LEVEL `glBn n`**, UNCONDITIONAL. -/
theorem wpLev_Bn (n : ℕ) : WpLev (glBn n) :=
  ⟨Om1_lt_eW.le.trans (glBn_spec n).2.1.le, wp_Om1_dvd_E (glBn_spec n).2.2.1
    (Om1_lt_eW.trans (glBn_spec n).2.1), (glBn_spec n).1⟩

theorem wpStep_Bn (n : ℕ) : WpStepAt (glBn n) := wpStep_fs (wpLev_Bn n) (wpFs_Bn n)

/-! ## The induction -/

/-- **THE REMAINING (A2) CASE BELOW `L`**: the step at every level `ℓ < L` that is not `Ω₁`, not a successor
`ℓ' + Ω₁`, and has no `ω`-sequence `WpFs` (the levels of cofinality `Ω₁`: `P + Ω₁^{e+1}` and `P + Ω₁^e` with `e` of
cofinality `Ω₁`, and the exponent limits for which no gated `ω`-sequence is proved). -/
def WpOm1Step (L : Ordinal.{0}) : Prop :=
  ∀ ℓ, WpLev ℓ → ℓ < L → ℓ ≠ Om1 → (¬ ∃ ℓ', WpLev ℓ' ∧ ℓ = ℓ' + Om1) → ¬ WpFs ℓ → WpStepAt ℓ

/-- **THE STEP AT EVERY (A2) LEVEL BELOW `L`** given the remaining case below `L`. -/
theorem wpStep_all {L : Ordinal.{0}} (hOm : WpOm1Step L) : ∀ ℓ, WpLev ℓ → ℓ < L → WpStepAt ℓ := by
  intro ℓ hℓ hL
  by_cases h1 : ℓ = Om1
  · subst h1; exact wpStep_base
  by_cases h2 : ∃ ℓ', WpLev ℓ' ∧ ℓ = ℓ' + Om1
  · obtain ⟨ℓ', hℓ', rfl⟩ := h2; exact wpStep_succ hℓ' hℓ.2.2
  by_cases h3 : WpFs ℓ
  · exact wpStep_fs hℓ h3
  exact hOm ℓ hℓ hL h1 h2 h3

/-- The recursion step of the (A2) family below `L`. -/
noncomputable def wpG (L : Ordinal.{0}) (hOm : WpOm1Step L) (ℓ : Ordinal.{0})
    (f : ∀ ℓ' : Ordinal.{0}, ℓ' < ℓ → WmEnt) : WmEnt := by
  classical
  exact if h : WpLev ℓ ∧ ℓ < L ∧ WpCoh ℓ f then Classical.choose (wpStep_all hOm ℓ h.1 h.2.1 f h.2.2)
    else (hnPk1, ULift.up hgU)

/-- The (A2) family below `L`, by well-founded recursion. -/
noncomputable def wpF (L : Ordinal.{0}) (hOm : WpOm1Step L) : Ordinal.{0} → WmEnt := Ordinal.lt_wf.fix (wpG L hOm)

/-- **THE (A2) FAMILY BELOW `L`** given the remaining case below `L`: an entry `Wn.WnAt` at every level `ℓ < L`, each
extending (`Wm.WmExtE`) every earlier one. -/
theorem wpFam {L : Ordinal.{0}} (hOm : WpOm1Step L) :
    ∀ ℓ, WpLev ℓ → ℓ < L → WnAt ℓ (wpF L hOm ℓ).1 (wpF L hOm ℓ).2.down ∧
      ∀ ℓ', ℓ' < ℓ → WpLev ℓ' → WmExtE (wpF L hOm ℓ') (wpF L hOm ℓ) := by
  intro ℓ
  induction ℓ using WellFoundedLT.induction with
  | _ ℓ ih =>
    intro hℓ hL
    have hcoh : WpCoh ℓ (fun ℓ' _ => wpF L hOm ℓ') :=
      ⟨fun ℓ' h h' => (ih ℓ' h h' (h.trans hL)).1,
        fun ℓ'' ℓ' _ h' hlt h1 h2 => (ih ℓ' h' h2 (h'.trans hL)).2 ℓ'' hlt h1⟩
    have heq : wpF L hOm ℓ = wpG L hOm ℓ (fun ℓ' _ => wpF L hOm ℓ') := Ordinal.lt_wf.fix_eq (wpG L hOm) ℓ
    have hsp := Classical.choose_spec (wpStep_all hOm ℓ hℓ hL (fun ℓ' _ => wpF L hOm ℓ') hcoh)
    have hG : wpG L hOm ℓ (fun ℓ' _ => wpF L hOm ℓ') =
        Classical.choose (wpStep_all hOm ℓ hℓ hL (fun ℓ' _ => wpF L hOm ℓ') hcoh) := by
      unfold wpG; rw [dif_pos ⟨hℓ, hL, hcoh⟩]
    rw [heq, hG]
    exact ⟨hsp.1, fun ℓ' h h' => hsp.2 ℓ' h h'⟩

/-- **THE SYSTEMS OVER `G` AT EVERY (A2) LEVEL BELOW `L`** given the remaining case below `L`: `B = φ(ℓ, G+1)`,
gate `≤ glG ℓ`. -/
theorem wpSysAll {L : Ordinal.{0}} (hOm : WpOm1Step L) :
    ∀ ℓ, WpLev ℓ → ℓ < L → ∃ V : HgVD, V.B = veblen ℓ (gcG 0 + 1) ∧ V.γ ≤ glG ℓ := fun ℓ hℓ hL =>
  ⟨(wpF L hOm ℓ).2.down, (wpFam hOm ℓ hℓ hL).1.2.2.1, (wpFam hOm ℓ hℓ hL).1.2.2.2.1⟩

/-- **THE SYSTEMS AT THE COFINAL LEVELS `glBn n`** given the remaining (A2) case: `B = φ(glBn n, G+1)`, gate `< K`. -/
theorem wpSysA2Lev (S : InaccSeq.{0}) (hOm : WpOm1Step (gcG 0)) (n : ℕ) :
    ∃ V : HgVD, V.B = veblen (glBn n) (gcG 0 + 1) ∧ V.γ < Td.tdK S := by
  obtain ⟨V, hB, hγ⟩ := wpSysAll hOm _ (wpLev_Bn n) (glBn_spec n).1
  exact ⟨V, hB, hγ.trans_lt (wnGateBnK S n)⟩

/-- **REGION (A2) GIVEN THE ONE REMAINING CASE** `WpOm1Step G`: every `B < φ(G, 1)` is `≤` the bound of a system over
`G` whose gate is below `K`. -/
theorem wpSysA2 (S : InaccSeq.{0}) (hOm : WpOm1Step (gcG 0)) : ∀ B, B < veblen (gcG 0) 1 →
    ∃ V : HgVD, B ≤ V.B ∧ V.γ < Td.tdK S := by
  intro B hB
  obtain ⟨n, hn⟩ := Wj.wjA2Cof hB
  obtain ⟨V, hVB, hγ⟩ := wpSysA2Lev S hOm n
  exact ⟨V, hVB ▸ hn.le, hγ⟩

/-! ## Non-vacuity: below `Ω₁²` the remaining case is empty -/

/-- **Below `Ω₁²` every (A2) level is `Ω₁`, a successor, or has an `ω`-sequence.** -/
theorem wpOm1Step_sq : WpOm1Step (Om1 * Om1) := by
  intro ℓ hℓ hL h1 h2 h3
  exfalso
  rcases wnShape ℓ hℓ.1 hℓ.2.1 hℓ.2.2 with h | h | ⟨P, e, he, hP, rfl⟩ | ⟨P, e, he, hP, rfl⟩ |
      ⟨P, e, c, he, hc, hcO, hP, rfl⟩
  · exact h1 h
  · exact h2 h
  · have h2' : Om1 * Om1 ≤ Om1 ^ (e + 1) := by
      rw [wm_sq_eq]; exact opow_le_opow_right wh_Om1_pos (by
        calc (2 : Ordinal.{0}) = 1 + 1 := one_add_one_eq_two.symm
        _ ≤ e + 1 := add_le_add_left he 1)
    exact absurd hL (not_lt.2 (h2'.trans le_add_self))
  · have hω : ω ≤ e := omega0_le_of_isSuccLimit he
    have h2' : Om1 * Om1 ≤ Om1 ^ e := by
      rw [wm_sq_eq]; exact opow_le_opow_right wh_Om1_pos ((natCast_lt_omega0 2).le.trans hω)
    exact absurd hL (not_lt.2 (h2'.trans le_add_self))
  · exact h3 (wpFs_coef he hc hcO hP hℓ.2.2)

/-- **THE CORRECTED (A2) FAMILY ON ALL LEVELS BELOW `Ω₁²`, UNCONDITIONAL** (non-vacuity of `WpCoh`). -/
theorem wpFam_sq : ∀ ℓ, WpLev ℓ → ℓ < Om1 * Om1 →
    WnAt ℓ (wpF _ wpOm1Step_sq ℓ).1 (wpF _ wpOm1Step_sq ℓ).2.down ∧
      ∀ ℓ', ℓ' < ℓ → WpLev ℓ' → WmExtE (wpF _ wpOm1Step_sq ℓ') (wpF _ wpOm1Step_sq ℓ) :=
  wpFam wpOm1Step_sq

end Googology.Trans.PoR.InaccPsi.R2.Wp
