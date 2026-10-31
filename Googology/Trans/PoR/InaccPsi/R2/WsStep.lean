import Googology.Trans.PoR.InaccPsi.R2.WsDat

/-!
# WsStep: THE PACKAGE OF A FAMILY OVER RAW DATA; ENTRIES, EXTENSION, THE STEP AT `Ω₁` AND AT A SUCCESSOR

`R2.WoPk` and `R2.WoStep` for an arbitrary code interface `C`:

* `wsQ1` (a pseudo-base of the level `ℓ` of `C` as one of the level `Ω₁ + 0`), `wsSt1` (the step at `Ω₁`),
  `wsSt1_sh`, `wsSpecOf` (**a system with the shape at `ℓ` over `Q` that extends the step at `Ω₁` has the
  specification `Hn.HnVSpec`**), `wsPk` (**the package of a family**);
* `WsSm`, `WsSpec`, `WsExt`, `WsCoh`, `WsStepAt` (`Wo.WoSm` … `Wo.WoStepAt` for `C`; families are `Wo.WoE`);
* `wsStep_base` (**`ℓ = Ω₁`**), `wsStep_succ` (**`ℓ = μ + Ω₁`**: the union `Hn.hnwU` over `wsWB r μ`).

No new axiom.  New definitions: `wsQ1`, `wsSt1`, `wsPk`, `WsSm`, `WsSpec`, `WsExt`, `WsCoh`, `WsStepAt`, `wsPkOf`,
`wsSuccE`.
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

variable {C : WsC}

section Q1

variable {ℓ : Ordinal.{0}} (hℓ : C.Lev ℓ) (Q : HnVQ (C.lv ℓ hℓ) 0)

/-- **A PSEUDO-BASE OF THE LEVEL `ℓ` AS ONE OF THE LEVEL `Ω₁ + 0`.** -/
noncomputable def wsQ1 : HnVQ hnL1 0 where
  F := Q.F
  Fr := Q.Fr
  γ := Q.γ
  Zo := Q.Zo
  lv := gv_Om1_pos
  γ_ge := zero_le
  lg := zero_le
  γ_lt := Q.γ_lt
  F_P := by show LuP (Om1 + 0) Q.F; rw [add_zero]; exact ((wsGood_Q hℓ Q).mono lev_Om1 hℓ.1).F_P
  G_lt := Q.G_lt
  S_lt1 := by show hdNx (Om1 + 0) Q.F < _; rw [add_zero]; exact ((wsGood_Q hℓ Q).mono lev_Om1 hℓ.1).S_lt1
  F_mem := Q.F_mem
  S_mem := fun S _ _ ha hb => by
    show hdNx (Om1 + 0) Q.F ∈ _
    rw [add_zero]
    rcases hℓ.1.lt_or_eq with hlt | heq
    · rw [hdNx_fixP (wo_fix_of_LuP (ws_Q_FP hℓ Q) hlt)]
      exact CSet.phi_mem (hnL1.L_mem S _ _ ha (zero_le.trans_lt hb)) (CSet.succ_mem (Q.F_mem S ha hb))
    · have := Q.S_mem S ha hb
      rw [ws_Q_N hℓ Q] at this
      have e : hdNx Om1 Q.F = hdNx ℓ Q.F := by rw [heq]
      rw [e]; exact this
  F_code := fun Z hZ hZ1 y hy hQy hyZ => ((wsGood_Q hℓ Q).mono lev_Om1 hℓ.1).F_code Z hZ hZ1 y hy hQy
    (by rw [add_zero] at hyZ; exact hyZ)
  F_cl := fun Z hZ hZ1 y hy hQy hyZ => ((wsGood_Q hℓ Q).mono lev_Om1 hℓ.1).F_cl Z hZ hZ1 y hy hQy
    (by rw [add_zero] at hyZ; exact hyZ)
  S_cl := fun Z hZ hZ1 hc => ((wsGood_Q hℓ Q).mono lev_Om1 hℓ.1).S_cl Z hZ hZ1
    (by rw [add_zero] at hc; exact hc)
  Fr_gt := fun {x} hx hx1 hγ => by
    show x + 0 < Q.Fr x
    have := (((wsGood_Q hℓ Q).rd Om1 lev_Om1 hℓ.1 x hx hx1 ((cut1 hx).2 hγ))).2.1
    rw [C.R_Om1 x] at this; rw [add_zero]; exact this
  Fr_P := fun {x} hx hx1 hγ => by
    show LuP (x + 0) (Q.Fr x)
    have := (((wsGood_Q hℓ Q).rd Om1 lev_Om1 hℓ.1 x hx hx1 ((cut1 hx).2 hγ))).1
    rw [C.R_Om1 x] at this; rw [add_zero]; exact this
  S_Zo := fun {x} hx hx1 hγ => by
    show hdNx (x + 0) (Q.Fr x) < Q.Zo x
    have := (((wsGood_Q hℓ Q).rd Om1 lev_Om1 hℓ.1 x hx hx1 ((cut1 hx).2 hγ))).2.2
    rw [C.R_Om1 x] at this; rw [add_zero]; exact this
  Zo_fix := Q.Zo_fix
  Zo_G1 := Q.Zo_G1
  Fr_pi := Q.Fr_pi
  S_pi := fun {σ ρ} hB hγ => by
    show hdNx (ρ + 0) (Q.Fr ρ) ∈ _ ∧ pi σ ρ (hdNx (ρ + 0) (Q.Fr ρ)) = hdNx (σ + 0) (Q.Fr σ)
    have := (wsGood_Q hℓ Q).S_pi Om1 lev_Om1 hℓ.1 σ ρ hB ((cut1 hB.1).2 hγ)
    rw [C.R_Om1 ρ, C.R_Om1 σ] at this; rw [add_zero, add_zero]; exact this

/-- **The step of the level `Ω₁ + 0` at `Q`** (`Hn.hnSt1` at `wsQ1 Q`). -/
noncomputable def wsSt1 (U : HgVD) (h : HgSStart (hnVPB Q) U) : HgVD := hnSt1 (wsQ1 hℓ Q) U h

theorem wsSt1_spec (U : HgVD) (h : HgSStart (hnVPB Q) U) : HnVSpec (wsQ1 hℓ Q) U (wsSt1 hℓ Q U h) :=
  hnSt1_spec (wsQ1 hℓ Q) U h

/-- **The step of the level `Ω₁ + 0` has the shape at `Ω₁`.** -/
theorem wsSt1_sh (U : HgVD) (h : HgSStart (hnVPB Q) U) : WsSh C (woQR Q) Om1 (wsSt1 hℓ Q U h) := by
  have s := wsSt1_spec hℓ Q U h
  refine ⟨?_, ⟨?_, ?_⟩, fun x hx _ => ?_, fun x hx hx1 hk => ?_, fun x hx hx1 => ?_,
    fun c σ h1 h2 => s.high c σ h1 (by rw [← s.B]; exact h2)⟩
  · rw [s.B]; show hdNx (Om1 + 0) Q.F = _; rw [add_zero]; rfl
  · rw [s.γ]; exact le_rfl
  · rw [s.γ]; exact le_max_left _ _
  · rw [s.γ]; exact (cut1 hx).symm
  · rw [s.b x hx hx1 ((cut1 hx).1 hk), C.R_Om1 x]
    show hdNx (x + 0) (Q.Fr x) = hdNx x (Q.Fr x); rw [add_zero]
  · rw [s.Z x hx hx1, C.R_Om1 x]
    show (if Q.γ < x then evZ (hdNx (x + 0) (Q.Fr x)) else Q.Zo x) =
      if max Q.γ (C.g Om1) < x then evZ (hdNx x (Q.Fr x)) else Q.Zo x
    by_cases hk : Q.γ < x
    · rw [if_pos hk, if_pos ((cut1 hx).2 hk), add_zero]
    · rw [if_neg hk, if_neg (fun h' => hk ((cut1 hx).1 h'))]

/-- The bound of the start `U` is `F`. -/
theorem ws_U_B {U : HgVD} (h : HgSStart (hnVPB Q) U) : U.B = Q.F := by
  rw [U.B_ix, h.ix]
  show veblen 1 Q.F = Q.F
  exact wo_fix_of_LuP (ws_Q_FP hℓ Q) ((wh_one_lt_Om1).trans_le hℓ.1)

/-- **A SYSTEM WITH THE SHAPE AT `ℓ` OVER `Q` EXTENDING THE STEP AT `Ω₁` HAS THE SPECIFICATION OF `ℓ + 0` AT `Q`.** -/
theorem wsSpecOf (U : HgVD) (h : HgSStart (hnVPB Q) U) {T : HgVD} (hT : WsSh C (woQR Q) ℓ T)
    (hext : ∀ c x, c < (wsSt1 hℓ Q U h).B → T.R c x = (wsSt1 hℓ Q U h).R c x ∧ T.g c = (wsSt1 hℓ Q U h).g c) :
    HnVSpec Q U T := by
  dsimp only [WsSh, woQR] at hT
  have s := wsSt1_spec hℓ Q U h
  have hg : max Q.γ (C.g ℓ) = Q.γ := max_eq_left (ws_Q_g hℓ Q)
  have hS1B : (wsSt1 hℓ Q U h).B = hdNx Om1 Q.F := by rw [s.B]; show hdNx (Om1 + 0) Q.F = _; rw [add_zero]
  have hFS1 : Q.F < (wsSt1 hℓ Q U h).B := by rw [hS1B]; exact hdNx_gt _ _
  have hUS1 : ∀ c, c < U.B → c < (wsSt1 hℓ Q U h).B := fun c hc =>
    hc.trans (by rw [ws_U_B hℓ Q h]; exact hFS1)
  obtain ⟨hB, ⟨hγ1, hγ2⟩, -, hb, hZ, hhi⟩ := hT
  refine ⟨?_, ?_, fun x hx hx1 hk => ?_, fun x hx hx1 => ?_, fun c x hc => ?_, fun c hc => ?_,
    fun c σ h1 h2 => hhi c σ h1 (by rw [hB]; rw [ws_Q_N hℓ Q] at h2; exact h2), fun x hx hx1 hk => ?_,
    fun x hx hx1 => ?_⟩
  · rw [hB]; exact (ws_Q_N hℓ Q).symm
  · exact le_antisymm (by rw [hg] at hγ2; exact hγ2) hγ1
  · rw [hb x hx hx1 (by rw [hg]; exact hk), ← ws_Q_l hℓ Q hx hx1 hk]
  · rw [hZ x hx hx1, hg]
    by_cases hk : Q.γ < x
    · rw [if_pos hk, if_pos hk, ← ws_Q_l hℓ Q hx hx1 hk]
    · rw [if_neg hk, if_neg hk]
  · rw [(hext c x (hUS1 c hc)).1]; exact s.extR c x hc
  · rw [(hext c 0 (hUS1 c hc)).2]; exact s.extg c hc
  · rw [(hext Q.F x hFS1).1]; exact s.RF x hx hx1 hk
  · rw [(hext Q.F 0 hFS1).2]; exact s.gF x hx hx1

end Q1

/-- **THE PACKAGE OF A FAMILY `E` OF SYSTEMS OVER RAW DATA** at the level `ℓ` of `C`. -/
noncomputable def wsPk (ℓ : Ordinal.{0}) (hℓ : C.Lev ℓ) (E : WoE)
    (hE : ∀ (Q : HnVQ (C.lv ℓ hℓ) 0) U (h : HgSStart (hnVPB Q) U), HnVSpec Q U (E (woQR Q) (wsSt1 hℓ Q U h))) :
    HnPk := ⟨C.lv ℓ hℓ, fun Q U h => E (woQR Q) (wsSt1 hℓ Q U h), hE⟩

variable (C)

/-- **THE REGION GATES** for `C`. -/
def WsSm (r : WoR) (ℓ : Ordinal.{0}) (S1 T : HgVD) : Prop :=
  ∀ c σ, S1.B ≤ c → c < T.B → InE σ → σ < Om1 → T.g c < σ →
    ∃ μ, C.Lev μ ∧ μ < ℓ ∧ C.g μ < σ ∧ c < hdNx (μ + Om1) r.F

/-- **THE SPECIFICATION OF AN ENTRY AT `ℓ`** for `C`. -/
def WsSpec (ℓ : Ordinal.{0}) (E : WoE) : Prop :=
  ∀ r S1, WsGood C r ℓ → WsSh C r Om1 S1 →
    WsSh C r ℓ (E r S1) ∧ (∀ c x, c < S1.B → (E r S1).R c x = S1.R c x ∧ (E r S1).g c = S1.g c) ∧
      WsSm C r ℓ S1 (E r S1)

/-- **`E` EXTENDS `E'` OVER EVERY DATUM GOOD UP TO `ℓ`** for `C`. -/
def WsExt (ℓ : Ordinal.{0}) (E' E : WoE) : Prop :=
  ∀ r S1, WsGood C r ℓ → WsSh C r Om1 S1 → ∀ c x, c < (E' r S1).B →
    (E r S1).R c x = (E' r S1).R c x ∧ (E r S1).g c = (E' r S1).g c

/-- **A COHERENT FAMILY OF ENTRIES BELOW `ℓ`** for `C`. -/
def WsCoh (ℓ : Ordinal.{0}) (f : ∀ μ : Ordinal.{0}, μ < ℓ → WoE) : Prop :=
  (∀ μ (h : μ < ℓ), C.Lev μ → WsSpec C μ (f μ h)) ∧
    ∀ μ' μ (h' : μ' < ℓ) (h : μ < ℓ), μ' < μ → C.Lev μ' → C.Lev μ → WsExt C μ (f μ' h') (f μ h)

/-- **THE STEP AT `ℓ`** for `C`: every coherent family below `ℓ` has an entry at `ℓ` extending all of it. -/
def WsStepAt (ℓ : Ordinal.{0}) : Prop :=
  ∀ f, WsCoh C ℓ f → ∃ E : WoE, WsSpec C ℓ E ∧ ∀ μ (h : μ < ℓ), C.Lev μ → WsExt C ℓ (f μ h) E

variable {C}

theorem ws_S1_le {r : WoR} {ℓ : Ordinal.{0}} {S1 T : HgVD} (hℓ : C.Lev ℓ) (h1 : WsSh C r Om1 S1)
    (hT : WsSh C r ℓ T) : S1.B ≤ T.B := by rw [h1.1, hT.1]; exact hdNx_mono hℓ.1 _

/-- **The package of an entry.** -/
noncomputable def wsPkOf (μ : Ordinal.{0}) (hμ : C.Lev μ) (E : WoE) (hs : WsSpec C μ E) : HnPk :=
  wsPk μ hμ E (fun Q U h => wsSpecOf hμ Q U h
    (hs _ _ (wsGood_Q hμ Q) (wsSt1_sh hμ Q U h)).1 (hs _ _ (wsGood_Q hμ Q) (wsSt1_sh hμ Q U h)).2.1)

/-! ## The step at `Ω₁` -/

/-- **THE STEP AT `Ω₁`**: `E r S₁ = S₁`. -/
theorem wsStep_base : WsStepAt C Om1 := fun _ _ =>
  ⟨fun _ S1 => S1, fun _ _ _ h1 => ⟨h1, fun _ _ _ => ⟨rfl, rfl⟩, fun _ _ h1' h2 => absurd h2 (not_lt.2 h1')⟩,
    fun _ h hμ => absurd hμ.1 (not_le.2 h)⟩

/-! ## The successor step -/

section Succ

variable {μ : Ordinal.{0}} (hμ : C.Lev μ) (hS : μ + Om1 < C.Bd) (f : ∀ μ' : Ordinal.{0}, μ' < μ + Om1 → WoE)
  (hcoh : WsCoh C (μ + Om1) f)

theorem ws_lt_succ : μ < μ + Om1 := lt_add_of_pos_right _ wh_Om1_pos

/-- **The entry at `μ + Ω₁`**: the union over `wsWB r μ` started at the entry at `μ`. -/
noncomputable def wsSuccE : WoE := by
  classical
  exact fun r S1 => if h : WsGood C r (μ + Om1) ∧ WsSh C r μ (f μ ws_lt_succ r S1) then
    hnwU (wsWB C r μ hμ h.1) (wsPkOf μ hμ (f μ ws_lt_succ) (hcoh.1 μ ws_lt_succ hμ)).St0
      (wsPkOf μ hμ (f μ ws_lt_succ) (hcoh.1 μ ws_lt_succ hμ)).h0 (f μ ws_lt_succ r S1) (wsSh_W hμ h.1 h.2)
  else S1

include hμ hS in
theorem wsSucc_lev : C.Lev (μ + Om1) := ⟨hμ.1.trans le_self_add, dvd_add hμ.2.1 (dvd_refl _), hS⟩

variable {r : WoR} {S1 : HgVD} (hr : WsGood C r (μ + Om1)) (h1 : WsSh C r Om1 S1)
include hμ hcoh hr h1

theorem wsSucc_mem : WsSh C r μ (f μ ws_lt_succ r S1) ∧
    (∀ c x, c < S1.B → (f μ ws_lt_succ r S1).R c x = S1.R c x ∧ (f μ ws_lt_succ r S1).g c = S1.g c) ∧
      WsSm C r μ S1 (f μ ws_lt_succ r S1) :=
  hcoh.1 μ ws_lt_succ hμ r S1 (hr.mono hμ (le_of_lt ws_lt_succ)) h1

theorem wsSucc_eq : wsSuccE hμ f hcoh r S1 =
    hnwU (wsWB C r μ hμ hr) (wsPkOf μ hμ (f μ ws_lt_succ) (hcoh.1 μ ws_lt_succ hμ)).St0
      (wsPkOf μ hμ (f μ ws_lt_succ) (hcoh.1 μ ws_lt_succ hμ)).h0 (f μ ws_lt_succ r S1)
      (wsSh_W hμ hr (wsSucc_mem hμ f hcoh hr h1).1) := by
  unfold wsSuccE; rw [dif_pos ⟨hr, (wsSucc_mem hμ f hcoh hr h1).1⟩]

end Succ

/-- **THE SUCCESSOR STEP** `ℓ = μ + Ω₁`. -/
theorem wsStep_succ {μ : Ordinal.{0}} (hμ : C.Lev μ) (hS : μ + Om1 < C.Bd) : WsStepAt C (μ + Om1) := by
  intro f hcoh
  refine ⟨wsSuccE hμ f hcoh, fun r S1 hr h1 => ?_, fun μ'' h'' hμ'' r S1 hr h1 c x hc => ?_⟩
  · obtain ⟨m1, m2, m3⟩ := wsSucc_mem hμ f hcoh hr h1
    set P := wsWB C r μ hμ hr
    set K := wsPkOf μ hμ (f μ ws_lt_succ) (hcoh.1 μ ws_lt_succ hμ)
    have hsh := wsSh_W hμ hr m1
    have hS1 : S1.B ≤ (f μ ws_lt_succ r S1).B := ws_S1_le hμ h1 m1
    rw [wsSucc_eq hμ f hcoh hr h1]
    refine ⟨wsSh_succ hμ hr K.St0 K.h0 m1, fun c x hc => ?_, fun c σ hSc hc hσ hσ1 hg => ?_⟩
    · have hc' : c < (f μ ws_lt_succ r S1).B := hc.trans_le hS1
      rw [hnwU_R0 P K.St0 K.h0 _ hsh hc' x, hnwU_g0 P K.St0 K.h0 _ hsh hc']
      exact m2 c x hc
    · by_cases hcμ : c < (f μ ws_lt_succ r S1).B
      · rw [hnwU_g0 P K.St0 K.h0 _ hsh hcμ] at hg
        obtain ⟨μ', hμ', hlt, hg', hc'⟩ := m3 c σ hSc hcμ hσ hσ1 hg
        exact ⟨μ', hμ', hlt.trans ws_lt_succ, hg', hc'⟩
      · have h := hnwU_highR P K.St0 K.h0 _ hsh (not_lt.1 hcμ) hc hσ hσ1 hg
        exact ⟨μ, hμ, ws_lt_succ, (max_lt_iff.1 h).2, hc⟩
  · obtain ⟨m1, -, -⟩ := wsSucc_mem hμ f hcoh hr h1
    set P := wsWB C r μ hμ hr
    set K := wsPkOf μ hμ (f μ ws_lt_succ) (hcoh.1 μ ws_lt_succ hμ)
    have hsh := wsSh_W hμ hr m1
    rw [wsSucc_eq hμ f hcoh hr h1]
    have hle : μ'' ≤ μ := not_lt.1 fun h => absurd h'' (not_lt.2 (wh_lev_succ_le hμ.2.1 hμ''.2.1 h))
    rcases hle.lt_or_eq with hlt | rfl
    · have e := hcoh.2 μ'' μ h'' ws_lt_succ hlt hμ'' hμ r S1 (hr.mono hμ (le_of_lt ws_lt_succ)) h1
      have hsp := hcoh.1 μ'' h'' hμ'' r S1 (hr.mono hμ'' (hlt.le.trans (le_of_lt ws_lt_succ))) h1
      have hc' : c < (f μ ws_lt_succ r S1).B := by
        rw [m1.1]; rw [hsp.1.1] at hc
        exact hc.trans_le (hdNx_mono hlt.le _)
      rw [hnwU_R0 P K.St0 K.h0 _ hsh hc' x, hnwU_g0 P K.St0 K.h0 _ hsh hc']
      exact e c x hc
    · rw [hnwU_R0 P K.St0 K.h0 _ hsh hc x, hnwU_g0 P K.St0 K.h0 _ hsh hc]
      exact ⟨rfl, rfl⟩

end Googology.Trans.PoR.InaccPsi.R2.Ws
