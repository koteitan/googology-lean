import Googology.Trans.PoR.InaccPsi.R2.WmSys

/-!
# WmStep: THE LEVEL-CODE INDUCTION ON THE CORRECTED COHERENCE

The skeleton's coherence (`SkCohW`) relates the packages of two entries by `Hn.HnkExt`, which says nothing when the
gate drops; then a limit entry cannot be shown to extend every member.  Here the coherence uses `Wm.WmExt` (lowering
by the pseudo-base gate):

* `WmLev`, `WmEnt`, `WmExtE` (**the corrected extension of entries**), `WmCoh` (**the corrected coherence**),
  `WmStepAt`; `wmExtE_old` (**`WmExtE` implies the old extension**), `wmCoh_old` (**the corrected coherence implies
  the old one**);
* `wmStep_base` (`ℓ = Ω₁`), `wmStep_succ` (**`ℓ = ℓ' + Ω₁`**), `wmStep_fs` (**EVERY LEVEL WITH AN `ω`-SEQUENCE**,
  `Wm.WmFs`), `wmStep_coef` (**every coefficient-limit level `P + Ω₁^e·c`**), `wmStep_exp` (**every exponent-limit
  level `P + Ω₁^e` whose exponent has an `ω`-sequence**);
* `WmOm1Step L` (the remaining case: levels `< L` that are not `Ω₁`, not a successor and have no `ω`-sequence),
  `wmStep_all`, `wmFam` (**THE FAMILY BELOW `L` GIVEN THE REMAINING CASE BELOW `L`**), `wmOm1Step_sq` (**below `Ω₁²`
  the remaining case is empty**), `wmFam_sq` (**the family on all levels below `Ω₁²`, unconditional**).

No new axiom.  New definitions: `WmLev`, `WmEnt`, `WmExtE`, `WmCoh`, `WmStepAt`, `WmOm1Step`, `wmG`, `wmF`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Wm

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

/-- The level codes: `Ω₁ ≤ ℓ`, `Ω₁ ∣ ℓ`, `ℓ < ε_{Ω₁+1}`. -/
def WmLev (ℓ : Ordinal.{0}) : Prop := Om1 ≤ ℓ ∧ Om1 ∣ ℓ ∧ ℓ < gfE

/-- An entry: a package and a system. -/
abbrev WmEnt : Type 1 := HnPk × ULift.{1} HgVD

/-- **THE CORRECTED EXTENSION OF ENTRIES**: the packages extend in the new sense (`WmExt`), the system bound grows,
readings and gates of the systems agree below. -/
def WmExtE (E' E : WmEnt) : Prop :=
  WmExt E'.1 E.1 ∧ E'.2.down.B < E.2.down.B ∧
    ∀ c x, c < E'.2.down.B → E.2.down.R c x = E'.2.down.R c x ∧ E.2.down.g c = E'.2.down.g c

/-- **THE CORRECTED COHERENCE** of a family below `ℓ`: entries at every level (`Wh.WhAt`), `WmExtE` between levels. -/
def WmCoh (ℓ : Ordinal.{0}) (f : ∀ ℓ' : Ordinal.{0}, ℓ' < ℓ → WmEnt) : Prop :=
  (∀ ℓ' (h : ℓ' < ℓ), WmLev ℓ' → WhAt ℓ' (f ℓ' h).1 (f ℓ' h).2.down) ∧
    ∀ ℓ'' ℓ' (h'' : ℓ'' < ℓ) (h' : ℓ' < ℓ), ℓ'' < ℓ' → WmLev ℓ'' → WmLev ℓ' → WmExtE (f ℓ'' h'') (f ℓ' h')

/-- **The step at `ℓ`** (corrected): every coherent family below `ℓ` has an entry at `ℓ` extending all of it. -/
def WmStepAt (ℓ : Ordinal.{0}) : Prop :=
  ∀ f, WmCoh ℓ f → ∃ E : WmEnt, WhAt ℓ E.1 E.2.down ∧ ∀ ℓ' (h : ℓ' < ℓ), WmLev ℓ' → WmExtE (f ℓ' h) E

/-- **The corrected extension implies the old one** (`Hn.HnkExt` of the packages; = the skeleton's `SkExt`). -/
theorem wmExtE_old {E' E : WmEnt} (h : WmExtE E' E) :
    HnkExt E'.1 E.1 ∧ E'.2.down.B < E.2.down.B ∧
      ∀ c x, c < E'.2.down.B → E.2.down.R c x = E'.2.down.R c x ∧ E.2.down.g c = E'.2.down.g c :=
  ⟨wmExt_old h.1, h.2.1, h.2.2⟩

/-- **The corrected coherence implies the old one** (the skeleton's `SkCohW`, written out). -/
theorem wmCoh_old {ℓ : Ordinal.{0}} {f : ∀ ℓ' : Ordinal.{0}, ℓ' < ℓ → WmEnt} (h : WmCoh ℓ f) :
    (∀ ℓ' (h' : ℓ' < ℓ), WmLev ℓ' → WhAt ℓ' (f ℓ' h').1 (f ℓ' h').2.down) ∧
    ∀ ℓ'' ℓ' (h'' : ℓ'' < ℓ) (h' : ℓ' < ℓ), ℓ'' < ℓ' → WmLev ℓ'' → WmLev ℓ' →
      HnkExt (f ℓ'' h'').1 (f ℓ' h').1 ∧ (f ℓ'' h'').2.down.B < (f ℓ' h').2.down.B ∧
      ∀ c x, c < (f ℓ'' h'').2.down.B → (f ℓ' h').2.down.R c x = (f ℓ'' h'').2.down.R c x ∧
        (f ℓ' h').2.down.g c = (f ℓ'' h'').2.down.g c :=
  ⟨h.1, fun a b ha hb hab h1 h2 => wmExtE_old (h.2 a b ha hb hab h1 h2)⟩

/-! ## The steps -/

/-- **The step at `Ω₁`**: `Hn.hnPk1` and `Hg.hgU`. -/
theorem wmStep_base : WmStepAt Om1 := fun _ _ =>
  ⟨(hnPk1, ULift.up hgU), whAt_base, fun _ h hl => absurd hl.1 (not_le.2 h)⟩

/-- **THE SUCCESSOR STEP** `ℓ = ℓ' + Ω₁` on the corrected coherence. -/
theorem wmStep_succ {ℓ' : Ordinal.{0}} (hℓ' : WmLev ℓ') (hℓ : ℓ' + Om1 < gfE) : WmStepAt (ℓ' + Om1) := by
  intro f ⟨hat, hext⟩
  have hlt : ℓ' < ℓ' + Om1 := lt_add_of_pos_right _ wh_Om1_pos
  have hat' := hat ℓ' hlt hℓ'
  refine ⟨((f ℓ' hlt).1.succ, ULift.up (whSuccV hat')), whSucc_at hℓ'.2.1 hℓ hat', fun ℓ'' h'' hℓ'' => ?_⟩
  have hle : ℓ'' ≤ ℓ' := not_lt.1 fun h => absurd h'' (not_lt.2 (wh_lev_succ_le hℓ'.2.1 hℓ''.2.1 h))
  rcases hle.lt_or_eq with hl | rfl
  · have he := hext ℓ'' ℓ' h'' hlt hl hℓ'' hℓ'
    have hold := whSucc_ext_lt hℓ'.2.1 hℓ hat' hl hℓ''.2.1 (hat ℓ'' h'' hℓ'') ⟨wmExt_old he.1, he.2.1, he.2.2⟩
    exact ⟨wmSucc_ext_lt (hat ℓ'' h'' hℓ'') hat' hℓ''.2.1 hℓ'.2.1 hl hℓ'.2.2 he.1, hold.2.1, hold.2.2⟩
  · have hold := whSucc_ext hat'
    exact ⟨wmSucc_ext _, hold.2.1, hold.2.2⟩

/-- **THE `ω`-LIMIT STEP**: every level with an `ω`-sequence of levels (`Wm.WmFs`). -/
theorem wmStep_fs {ℓ : Ordinal.{0}} (hℓ : WmLev ℓ) (hfs : WmFs ℓ) : WmStepAt ℓ := by
  intro f ⟨hat, hext⟩
  obtain ⟨ls, hlev, hmono, hlt, hcof, hg⟩ := hfs
  have hL : ∀ k, WmLev (ls k) := fun k => ⟨(hlev k).1, (hlev k).2, (hlt k).trans hℓ.2.2⟩
  let W : WmLim ℓ :=
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

/-- **THE COEFFICIENT-LIMIT STEP** `ℓ = P + Ω₁^e·c` (`1 ≤ e`, `c < Ω₁` a limit, `Ω₁^{e+1} ∣ P`). -/
theorem wmStep_coef {P e c : Ordinal.{0}} (he : 1 ≤ e) (hc : IsSuccLimit c) (hcO : c < Om1)
    (hP : Om1 ^ (e + 1) ∣ P) (hℓ : WmLev (P + Om1 ^ e * c)) : WmStepAt (P + Om1 ^ e * c) :=
  wmStep_fs hℓ (wmFs_coef he hc hcO hP hℓ.2.2)

/-- **THE EXPONENT-LIMIT STEP** `ℓ = P + Ω₁^e` (`e` a limit with an `ω`-sequence, `Ω₁^e ∣ P`). -/
theorem wmStep_exp {P e : Ordinal.{0}} (he : IsSuccLimit e) (hP : Om1 ^ e ∣ P) (hE : WmExpFs e)
    (hℓ : WmLev (P + Om1 ^ e)) : WmStepAt (P + Om1 ^ e) :=
  wmStep_fs hℓ (wmFs_exp he hP hℓ.2.2 hE)

/-! ## The induction -/

/-- **THE REMAINING CASE BELOW `L`**: the step at every level `ℓ < L` that is not `Ω₁`, not a successor `ℓ' + Ω₁`,
and has no `ω`-sequence (the levels of cofinality `Ω₁`: `P + Ω₁^{e+1}` and `P + Ω₁^e` with `e` of cofinality
`Ω₁`). -/
def WmOm1Step (L : Ordinal.{0}) : Prop :=
  ∀ ℓ, WmLev ℓ → ℓ < L → ℓ ≠ Om1 → (¬ ∃ ℓ', WmLev ℓ' ∧ ℓ = ℓ' + Om1) → ¬ WmFs ℓ → WmStepAt ℓ

/-- **THE STEP AT EVERY LEVEL BELOW `L`** given the remaining case below `L`. -/
theorem wmStep_all {L : Ordinal.{0}} (hOm : WmOm1Step L) : ∀ ℓ, WmLev ℓ → ℓ < L → WmStepAt ℓ := by
  intro ℓ hℓ hL
  by_cases h1 : ℓ = Om1
  · subst h1; exact wmStep_base
  by_cases h2 : ∃ ℓ', WmLev ℓ' ∧ ℓ = ℓ' + Om1
  · obtain ⟨ℓ', hℓ', rfl⟩ := h2; exact wmStep_succ hℓ' hℓ.2.2
  by_cases h3 : WmFs ℓ
  · exact wmStep_fs hℓ h3
  exact hOm ℓ hℓ hL h1 h2 h3

/-- The recursion step of the family below `L`. -/
noncomputable def wmG (L : Ordinal.{0}) (hOm : WmOm1Step L) (ℓ : Ordinal.{0})
    (f : ∀ ℓ' : Ordinal.{0}, ℓ' < ℓ → WmEnt) : WmEnt := by
  classical
  exact if h : WmLev ℓ ∧ ℓ < L ∧ WmCoh ℓ f then Classical.choose (wmStep_all hOm ℓ h.1 h.2.1 f h.2.2)
    else (hnPk1, ULift.up hgU)

/-- The family below `L`, by well-founded recursion. -/
noncomputable def wmF (L : Ordinal.{0}) (hOm : WmOm1Step L) : Ordinal.{0} → WmEnt := Ordinal.lt_wf.fix (wmG L hOm)

/-- **THE FAMILY BELOW `L`** given the remaining case below `L`: an entry at every level `ℓ < L`, each extending
(in the corrected sense) every earlier one. -/
theorem wmFam {L : Ordinal.{0}} (hOm : WmOm1Step L) :
    ∀ ℓ, WmLev ℓ → ℓ < L → WhAt ℓ (wmF L hOm ℓ).1 (wmF L hOm ℓ).2.down ∧
      ∀ ℓ', ℓ' < ℓ → WmLev ℓ' → WmExtE (wmF L hOm ℓ') (wmF L hOm ℓ) := by
  intro ℓ
  induction ℓ using WellFoundedLT.induction with
  | _ ℓ ih =>
    intro hℓ hL
    have hcoh : WmCoh ℓ (fun ℓ' _ => wmF L hOm ℓ') :=
      ⟨fun ℓ' h h' => (ih ℓ' h h' (h.trans hL)).1,
        fun ℓ'' ℓ' _ h' hlt h1 h2 => (ih ℓ' h' h2 (h'.trans hL)).2 ℓ'' hlt h1⟩
    have heq : wmF L hOm ℓ = wmG L hOm ℓ (fun ℓ' _ => wmF L hOm ℓ') := Ordinal.lt_wf.fix_eq (wmG L hOm) ℓ
    have hsp := Classical.choose_spec (wmStep_all hOm ℓ hℓ hL (fun ℓ' _ => wmF L hOm ℓ') hcoh)
    have hG : wmG L hOm ℓ (fun ℓ' _ => wmF L hOm ℓ') =
        Classical.choose (wmStep_all hOm ℓ hℓ hL (fun ℓ' _ => wmF L hOm ℓ') hcoh) := by
      unfold wmG; rw [dif_pos ⟨hℓ, hL, hcoh⟩]
    rw [heq, hG]
    exact ⟨hsp.1, fun ℓ' h h' => hsp.2 ℓ' h h'⟩

/-- **THE SYSTEMS OVER `G` AT EVERY LEVEL BELOW `L`** given the remaining case below `L`: `B = φ(ℓ, G+1)`,
gate `≤ gtc ℓ`. -/
theorem wmSysAll {L : Ordinal.{0}} (hOm : WmOm1Step L) :
    ∀ ℓ, WmLev ℓ → ℓ < L → ∃ V : HgVD, V.B = veblen ℓ (gcG 0 + 1) ∧ V.γ ≤ gtc ℓ := fun ℓ hℓ hL =>
  ⟨(wmF L hOm ℓ).2.down, (wmFam hOm ℓ hℓ hL).1.2.2.1, (wmFam hOm ℓ hℓ hL).1.2.2.2.1⟩

/-! ## Below `Ω₁²` the remaining case is empty -/

theorem wm_sq_eq : (Om1 : Ordinal.{0}) * Om1 = Om1 ^ (2 : Ordinal.{0}) := by
  rw [show (2 : Ordinal.{0}) = 1 + 1 from one_add_one_eq_two.symm, opow_add, opow_one]

/-- **Below `Ω₁²` every level is `Ω₁`, a successor, or has an `ω`-sequence.** -/
theorem wmOm1Step_sq : WmOm1Step (Om1 * Om1) := by
  intro ℓ hℓ hL h1 h2 h3
  exfalso
  rcases whShape ℓ hℓ.1 hℓ.2.1 hℓ.2.2 with h | h | ⟨P, e, he, hP, rfl⟩ | ⟨P, e, he, hP, rfl⟩ |
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
  · exact h3 (wmFs_coef he hc hcO hP hℓ.2.2)

/-- **THE FAMILY ON ALL LEVELS BELOW `Ω₁²`, UNCONDITIONAL** (non-vacuity witness of the corrected coherence). -/
theorem wmFam_sq : ∀ ℓ, WmLev ℓ → ℓ < Om1 * Om1 →
    WhAt ℓ (wmF _ wmOm1Step_sq ℓ).1 (wmF _ wmOm1Step_sq ℓ).2.down ∧
      ∀ ℓ', ℓ' < ℓ → WmLev ℓ' → WmExtE (wmF _ wmOm1Step_sq ℓ') (wmF _ wmOm1Step_sq ℓ) :=
  wmFam wmOm1Step_sq

end Googology.Trans.PoR.InaccPsi.R2.Wm
