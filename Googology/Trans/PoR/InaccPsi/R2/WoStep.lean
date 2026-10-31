import Googology.Trans.PoR.InaccPsi.R2.WoPk

/-!
# WoStep: FAMILIES OF SYSTEMS OVER ALL RAW DATA; THE STEP AT `Ω₁` AND AT A SUCCESSOR LEVEL

An entry at the level `ℓ` is now a FAMILY `E : WoR → HgVD → HgVD`: for every raw datum `r` good up to `ℓ` and every
system `S₁` with the shape at `Ω₁` over `r`, a system `E r S₁` with the shape at `ℓ` over `r` (`Wo.WoSh`) that
extends `S₁` and has the REGION GATES (`WoSm`: a code past `S₁` with gate below an `ε`-number `σ` lies below
`hdNx (μ+Ω₁) F` for a level `μ < ℓ` with `gtc μ < σ`).  Entries extend each other over EVERY datum good up to the
higher level (`WoExt`): there is no gate condition, so the gate drop (`Wm.wm_gate_drop`) is no obstacle.

* `WoSpec ℓ E`, `WoExt ℓ E' E`, `WoCoh ℓ f`, `WoStepAt ℓ` (as `Wm.WmStepAt`, on families over raw data);
* `woPkOf` (**the package of an entry**: `Wo.woPk` with the specification from `Wo.woSpecOf`);
* `woStep_base` (**`ℓ = Ω₁`**: `E r S₁ = S₁`), `woStep_succ` (**`ℓ = μ + Ω₁`**: the union `Hn.hnwU` over
  `Wo.woWB r μ` with the steps of the package of the entry at `μ`).

No new axiom.  New definitions: `WoE`, `WoSm`, `WoSpec`, `WoExt`, `WoCoh`, `WoStepAt`, `woPkOf`, `woSuccE`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Wo

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

/-- A family of systems over raw data. -/
abbrev WoE : Type 1 := WoR → HgVD → HgVD

/-- **THE REGION GATES**: a code of `T` past `S₁` with gate below an `ε`-number `σ` lies below `hdNx (μ+Ω₁) F` for
a level `μ < ℓ` with `gtc μ < σ`. -/
def WoSm (r : WoR) (ℓ : Ordinal.{0}) (S1 T : HgVD) : Prop :=
  ∀ c σ, S1.B ≤ c → c < T.B → InE σ → σ < Om1 → T.g c < σ →
    ∃ μ, WmLev μ ∧ μ < ℓ ∧ gtc μ < σ ∧ c < hdNx (μ + Om1) r.F

/-- **THE SPECIFICATION OF AN ENTRY AT `ℓ`.** -/
def WoSpec (ℓ : Ordinal.{0}) (E : WoE) : Prop :=
  ∀ r S1, WoGood r ℓ → WoSh r Om1 S1 →
    WoSh r ℓ (E r S1) ∧ (∀ c x, c < S1.B → (E r S1).R c x = S1.R c x ∧ (E r S1).g c = S1.g c) ∧
      WoSm r ℓ S1 (E r S1)

/-- **`E` EXTENDS `E'` OVER EVERY DATUM GOOD UP TO `ℓ`.** -/
def WoExt (ℓ : Ordinal.{0}) (E' E : WoE) : Prop :=
  ∀ r S1, WoGood r ℓ → WoSh r Om1 S1 → ∀ c x, c < (E' r S1).B →
    (E r S1).R c x = (E' r S1).R c x ∧ (E r S1).g c = (E' r S1).g c

/-- **A COHERENT FAMILY OF ENTRIES BELOW `ℓ`.** -/
def WoCoh (ℓ : Ordinal.{0}) (f : ∀ μ : Ordinal.{0}, μ < ℓ → WoE) : Prop :=
  (∀ μ (h : μ < ℓ), WmLev μ → WoSpec μ (f μ h)) ∧
    ∀ μ' μ (h' : μ' < ℓ) (h : μ < ℓ), μ' < μ → WmLev μ' → WmLev μ → WoExt μ (f μ' h') (f μ h)

/-- **THE STEP AT `ℓ`**: every coherent family below `ℓ` has an entry at `ℓ` extending all of it. -/
def WoStepAt (ℓ : Ordinal.{0}) : Prop :=
  ∀ f, WoCoh ℓ f → ∃ E : WoE, WoSpec ℓ E ∧ ∀ μ (h : μ < ℓ), WmLev μ → WoExt ℓ (f μ h) E

theorem woSh_B {r : WoR} {ℓ : Ordinal.{0}} {S : HgVD} (h : WoSh r ℓ S) : S.B = hdNx ℓ r.F := h.1

theorem wo_S1_le {r : WoR} {ℓ : Ordinal.{0}} {S1 T : HgVD} (hℓ : WmLev ℓ) (h1 : WoSh r Om1 S1) (hT : WoSh r ℓ T) :
    S1.B ≤ T.B := by rw [h1.1, hT.1]; exact hdNx_mono hℓ.1 _

/-- **The package of an entry.** -/
noncomputable def woPkOf (μ : Ordinal.{0}) (hμ : WmLev μ) (E : WoE) (hs : WoSpec μ E) : HnPk :=
  woPk μ hμ E (fun Q U h => woSpecOf hμ Q U h
    (hs _ _ (woGood_Q hμ Q) (woSt1_sh hμ Q U h)).1 (hs _ _ (woGood_Q hμ Q) (woSt1_sh hμ Q U h)).2.1)

/-! ## The step at `Ω₁` -/

/-- **THE STEP AT `Ω₁`**: `E r S₁ = S₁`. -/
theorem woStep_base : WoStepAt Om1 := fun _ _ =>
  ⟨fun _ S1 => S1, fun _ _ _ h1 => ⟨h1, fun _ _ _ => ⟨rfl, rfl⟩, fun _ _ h1' h2 => absurd h2 (not_lt.2 h1')⟩,
    fun _ h hμ => absurd hμ.1 (not_le.2 h)⟩

/-! ## The successor step -/

section Succ

variable {μ : Ordinal.{0}} (hμ : WmLev μ) (hS : μ + Om1 < gfE) (f : ∀ μ' : Ordinal.{0}, μ' < μ + Om1 → WoE)
  (hcoh : WoCoh (μ + Om1) f)

theorem wo_lt_succ : μ < μ + Om1 := lt_add_of_pos_right _ wh_Om1_pos

open Classical in
/-- **The entry at `μ + Ω₁`**: the union over `woWB r μ` started at the entry at `μ`. -/
noncomputable def woSuccE : WoE := fun r S1 =>
  if h : WoGood r (μ + Om1) ∧ WoSh r μ (f μ wo_lt_succ r S1) then
    hnwU (woWB r μ hμ h.1) (woPkOf μ hμ (f μ wo_lt_succ) (hcoh.1 μ wo_lt_succ hμ)).St0
      (woPkOf μ hμ (f μ wo_lt_succ) (hcoh.1 μ wo_lt_succ hμ)).h0 (f μ wo_lt_succ r S1) (woSh_W hμ h.1 h.2)
  else S1

include hμ hS in
theorem woSucc_lev : WmLev (μ + Om1) := ⟨hμ.1.trans le_self_add, dvd_add hμ.2.1 (dvd_refl _), hS⟩

variable {r : WoR} {S1 : HgVD} (hr : WoGood r (μ + Om1)) (h1 : WoSh r Om1 S1)
include hμ hcoh hr h1

theorem woSucc_mem : WoSh r μ (f μ wo_lt_succ r S1) ∧
    (∀ c x, c < S1.B → (f μ wo_lt_succ r S1).R c x = S1.R c x ∧ (f μ wo_lt_succ r S1).g c = S1.g c) ∧
      WoSm r μ S1 (f μ wo_lt_succ r S1) :=
  hcoh.1 μ wo_lt_succ hμ r S1 (hr.mono hμ (le_of_lt wo_lt_succ)) h1

theorem woSucc_eq : woSuccE hμ f hcoh r S1 =
    hnwU (woWB r μ hμ hr) (woPkOf μ hμ (f μ wo_lt_succ) (hcoh.1 μ wo_lt_succ hμ)).St0
      (woPkOf μ hμ (f μ wo_lt_succ) (hcoh.1 μ wo_lt_succ hμ)).h0 (f μ wo_lt_succ r S1)
      (woSh_W hμ hr (woSucc_mem hμ f hcoh hr h1).1) := by
  unfold woSuccE; rw [dif_pos ⟨hr, (woSucc_mem hμ f hcoh hr h1).1⟩]

end Succ

/-- **THE SUCCESSOR STEP** `ℓ = μ + Ω₁`. -/
theorem woStep_succ {μ : Ordinal.{0}} (hμ : WmLev μ) (hS : μ + Om1 < gfE) : WoStepAt (μ + Om1) := by
  intro f hcoh
  have hlv := woSucc_lev hμ hS
  refine ⟨woSuccE hμ f hcoh, fun r S1 hr h1 => ?_, fun μ'' h'' hμ'' r S1 hr h1 c x hc => ?_⟩
  · obtain ⟨m1, m2, m3⟩ := woSucc_mem hμ f hcoh hr h1
    set P := woWB r μ hμ hr
    set K := woPkOf μ hμ (f μ wo_lt_succ) (hcoh.1 μ wo_lt_succ hμ)
    have hsh := woSh_W hμ hr m1
    have hS1 : S1.B ≤ (f μ wo_lt_succ r S1).B := wo_S1_le hμ h1 m1
    rw [woSucc_eq hμ f hcoh hr h1]
    refine ⟨woSh_succ hμ hr K.St0 K.h0 m1, fun c x hc => ?_, fun c σ hSc hc hσ hσ1 hg => ?_⟩
    · have hc' : c < (f μ wo_lt_succ r S1).B := hc.trans_le hS1
      rw [hnwU_R0 P K.St0 K.h0 _ hsh hc' x, hnwU_g0 P K.St0 K.h0 _ hsh hc']
      exact m2 c x hc
    · by_cases hcμ : c < (f μ wo_lt_succ r S1).B
      · rw [hnwU_g0 P K.St0 K.h0 _ hsh hcμ] at hg
        obtain ⟨μ', hμ', hlt, hg', hc'⟩ := m3 c σ hSc hcμ hσ hσ1 hg
        exact ⟨μ', hμ', hlt.trans wo_lt_succ, hg', hc'⟩
      · have h := hnwU_highR P K.St0 K.h0 _ hsh (not_lt.1 hcμ) hc hσ hσ1 hg
        exact ⟨μ, hμ, wo_lt_succ, (max_lt_iff.1 h).2, hc⟩
  · obtain ⟨m1, -, -⟩ := woSucc_mem hμ f hcoh hr h1
    set P := woWB r μ hμ hr
    set K := woPkOf μ hμ (f μ wo_lt_succ) (hcoh.1 μ wo_lt_succ hμ)
    have hsh := woSh_W hμ hr m1
    rw [woSucc_eq hμ f hcoh hr h1]
    have hle : μ'' ≤ μ := not_lt.1 fun h => absurd h'' (not_lt.2 (wh_lev_succ_le hμ.2.1 hμ''.2.1 h))
    rcases hle.lt_or_eq with hlt | rfl
    · have e := hcoh.2 μ'' μ h'' wo_lt_succ hlt hμ'' hμ r S1 (hr.mono hμ (le_of_lt wo_lt_succ)) h1
      have hsp := hcoh.1 μ'' h'' hμ'' r S1 (hr.mono hμ'' (hlt.le.trans (le_of_lt wo_lt_succ))) h1
      have hc' : c < (f μ wo_lt_succ r S1).B := by
        rw [m1.1]; rw [hsp.1.1] at hc
        exact hc.trans_le (hdNx_mono hlt.le _)
      rw [hnwU_R0 P K.St0 K.h0 _ hsh hc' x, hnwU_g0 P K.St0 K.h0 _ hsh hc']
      exact e c x hc
    · rw [hnwU_R0 P K.St0 K.h0 _ hsh hc x, hnwU_g0 P K.St0 K.h0 _ hsh hc]
      exact ⟨rfl, rfl⟩

end Googology.Trans.PoR.InaccPsi.R2.Wo
