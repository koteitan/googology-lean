import Googology.Trans.PoR.InaccPsi.R2.GwU

/-!
# ONE RECURSION OVER ALL INDICES BELOW `ζ_{G+1}`, THE INDICES READ BY THE SYSTEMS THEMSELVES

`gwD c` (`c < ζ_{G+1}`, `G = Γ_{Ω₁+1}`) is a gated digit system with bound `ε_{G+c} = φ(1, G + c)`: `gwD 0 = goGl`
(bound `G`), `gwD (c+1)` is the step of `gwD c`, and at a limit `λ` it is the union `GwFam.U` of all `gwD μ`,
`μ < λ`, with the index `λ` read by the first system that contains `λ` as a code (it exists: `λ < φ(1, G + d)` for
some `d < λ`, `gw_cover`).  No level-by-level iteration: the walls `ε₀`, `K`, `Ω₁·K`, `Ω₁²`, `G`, `ε_{G+1}`, … of
the earlier rounds are ordinary limit indices.

The invariant (`GwInv`, proved at every `ν < ζ_{G+1}`, `gw_inv`): index `G + μ`, coherence of readings and gates,
the base reading `φ(1, Γ_{x+1} + μ(x))` with `μ(x)` the reading of the code `μ` in `gwD μ` (above the base gate),
and `γ(gwD μ) < x ⇔ g(μ) < x` at every `ε`-number base `x`.

* `gw0`, `GwInv`, `gwIdx`, `gwFamOf`, `gwExt`, `gwLimD`, `gwD` (**THE RECURSION**), `gwD_zero`, `gwD_succ`,
  `gwD_limit`, `GwTop`, `gw_inv` (**THE INVARIANT AT EVERY INDEX BELOW `ζ_{G+1}`**);
* `gw_B`, `gw_ix`, `gw_b`, `gw_γ_iff`, `gw_ext`, `gw_succ_eq`, `gw_lim_eq`.

No new axiom.  New definitions: `gw0`, `GwInv`, `GwTop`, `gwIdx`, `gwFamOf`, `gwExt`, `gwLimD`, `gwD`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gw

open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gj
  Googology.Trans.PoR.InaccPsi.R2.Gi Googology.Trans.PoR.InaccPsi.R2.Gn Googology.Trans.PoR.InaccPsi.R2.Go
  Googology.Trans.PoR.InaccPsi.R2.Gp
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

/-- **The start**: `goGl` (bound `G = Γ_{Ω₁+1}`, base reading `Γ_{x+1}`, gate `0`). -/
noncomputable def gw0 : GvD := GvD.ofGs gsGl

theorem gw0_γ : gw0.γ = 0 := rfl

theorem gw0_ix : gw0.ix = gcG 0 := rfl

theorem gw0_b (x : Ordinal.{0}) : gw0.b x = lgG x := rfl

/-! ## The invariant -/

/-- **The invariant of a family below `λ`.** -/
structure GwInv (l : Ordinal.{0}) (F : Ordinal.{0} → GvD) : Prop where
  ix : ∀ μ, μ < l → (F μ).ix = gcG 0 + μ
  zero : 0 < l → F 0 = gw0
  succ : ∀ μ, μ + 1 < l → F (μ + 1) = GvD.ofGs (F μ).step
  cohR : ∀ β γ, β ≤ γ → γ < l → ∀ c x, c < (F β).B → (F γ).R c x = (F β).R c x
  cohg : ∀ β γ, β ≤ γ → γ < l → ∀ c, c < (F β).B → (F γ).g c = (F β).g c
  hb : ∀ μ, μ < l → ∀ x, InE x → x < Om1 → (F μ).γ < x → (F μ).b x = veblen 1 (gpI x + (F μ).R μ x)
  hγ : ∀ μ, μ < l → ∀ x, InE x → x < Om1 → ((F μ).γ < x ↔ (F μ).g μ < x)

namespace GwInv

variable {l : Ordinal.{0}} {F : Ordinal.{0} → GvD} (H : GwInv l F)
include H

theorem B_eq {β : Ordinal.{0}} (h : β < l) : (F β).B = veblen 1 (gcG 0 + β) := by
  rw [(F β).B_ix, H.ix β h]

theorem B_le {β γ : Ordinal.{0}} (hβγ : β ≤ γ) (h : γ < l) : (F β).B ≤ (F γ).B := by
  rw [H.B_eq (lt_of_le_of_lt hβγ h), H.B_eq h]
  exact (isNormal_veblen 1).monotone ((add_le_add_iff_left _).2 hβγ)

theorem self_lt {μ : Ordinal.{0}} (h : μ < l) (hZ : μ < evZ (gcG 0)) : μ < (F μ).B := by
  rw [H.B_eq h]; exact gw_self_lt hZ

/-- The reading of a code `μ` is the same in every member containing it. -/
theorem R_tr {μ d : Ordinal.{0}} (hμ : μ < l) (hd : d < l) (hμd : μ < (F d).B) (hμB : μ < (F μ).B)
    (x : Ordinal.{0}) : (F d).R μ x = (F μ).R μ x := by
  rcases le_total μ d with h | h
  · exact H.cohR μ d h hd μ x hμB
  · exact (H.cohR d μ h hμ μ x hμd).symm

theorem g_tr {μ d : Ordinal.{0}} (hμ : μ < l) (hd : d < l) (hμd : μ < (F d).B) (hμB : μ < (F μ).B) :
    (F d).g μ = (F μ).g μ := by
  rcases le_total μ d with h | h
  · exact H.cohg μ d h hd μ hμB
  · exact (H.cohg d μ h hμ μ hμd).symm

theorem congr {G : Ordinal.{0} → GvD} (hFG : ∀ β, β < l → G β = F β) : GwInv l G where
  ix := fun β h => by rw [hFG β h]; exact H.ix β h
  zero := fun h => by rw [hFG 0 h]; exact H.zero h
  succ := fun μ h => by rw [hFG (μ + 1) h, hFG μ ((lt_add_one μ).trans h)]; exact H.succ μ h
  cohR := fun β γ hβγ h c x hc => by
    rw [hFG β (lt_of_le_of_lt hβγ h)] at hc ⊢
    rw [hFG γ h]; exact H.cohR β γ hβγ h c x hc
  cohg := fun β γ hβγ h c hc => by
    rw [hFG β (lt_of_le_of_lt hβγ h)] at hc ⊢
    rw [hFG γ h]; exact H.cohg β γ hβγ h c hc
  hb := fun μ h x hx hx1 => by rw [hFG μ h]; exact H.hb μ h x hx hx1
  hγ := fun μ h x hx hx1 => by rw [hFG μ h]; exact H.hγ μ h x hx hx1

end GwInv

theorem gwInv_zero (F : Ordinal.{0} → GvD) : GwInv 0 F where
  ix := fun _ h => absurd h (not_lt.2 zero_le)
  zero := fun h => absurd h (lt_irrefl 0)
  succ := fun μ h => absurd h (not_lt.2 zero_le)
  cohR := fun _ _ _ h => absurd h (not_lt.2 zero_le)
  cohg := fun _ _ _ h => absurd h (not_lt.2 zero_le)
  hb := fun _ h => absurd h (not_lt.2 zero_le)
  hγ := fun _ h => absurd h (not_lt.2 zero_le)

/-! ## The family at a limit -/

/-- The first member that contains the index `λ` as a code (the index system of the union). -/
noncomputable def gwIdx (l : Ordinal.{0}) (F : Ordinal.{0} → GvD) : Ordinal.{0} :=
  sInf {d | d < l ∧ l < (F d).B}

theorem gwIdx_spec {l : Ordinal.{0}} {F : Ordinal.{0} → GvD} (hl : IsSuccLimit l) (hlZ : l < evZ (gcG 0))
    (H : GwInv l F) : gwIdx l F < l ∧ l < (F (gwIdx l F)).B := by
  obtain ⟨d, hd, hld⟩ := gw_cover hl.bot_lt hlZ
  have h : l < (F d).B := by rw [H.B_eq hd]; exact hld
  exact csInf_mem (s := {d | d < l ∧ l < (F d).B}) ⟨d, hd, h⟩

/-- **The family over all `μ < λ`**, its indices read by the first member containing `λ`. -/
noncomputable def gwFamOf (l : Ordinal.{0}) (hl : IsSuccLimit l) (hlZ : l < evZ (gcG 0)) (F : Ordinal.{0} → GvD)
    (H : GwInv l F) : GwFam where
  E := F (gwIdx l F)
  l := l
  F := F
  l_lim := hl
  l_lt := (gwIdx_spec hl hlZ H).2
  l_Z := hlZ
  ix := H.ix
  γ0 := by rw [H.zero hl.bot_lt]; rfl
  succ := H.succ
  cohR := H.cohR
  cohg := H.cohg
  hb := fun μ hμ x hx hx1 hγ => by
    obtain ⟨hd, hld⟩ := gwIdx_spec hl hlZ H
    rw [H.hb μ hμ x hx hx1 hγ, H.R_tr hμ hd (hμ.trans hld) (H.self_lt hμ (hμ.trans hlZ)) x]
  hγ := fun μ hμ x hx hx1 => by
    obtain ⟨hd, hld⟩ := gwIdx_spec hl hlZ H
    rw [H.hγ μ hμ x hx hx1, H.g_tr hμ hd (hμ.trans hld) (H.self_lt hμ (hμ.trans hlZ))]

/-- The family of the earlier values, extended by the start. -/
noncomputable def gwExt (l : Ordinal.{0}) (IH : ∀ β, β < l → GvD) (β : Ordinal.{0}) : GvD :=
  if h : β < l then IH β h else gw0

open Classical in
/-- The limit step: the union over all smaller indices when the invariant holds (it does below `ζ_{G+1}`). -/
noncomputable def gwLimD (l : Ordinal.{0}) (hl : IsSuccLimit l) (IH : ∀ β, β < l → GvD) : GvD :=
  if H : l < evZ (gcG 0) ∧ GwInv l (gwExt l IH) then (gwFamOf l hl H.1 (gwExt l IH) H.2).U else gw0

/-- **THE RECURSION**: `goGl` at `0`, the step at `c+1`, the union over all `μ < λ` at a limit `λ`. -/
noncomputable def gwD (ν : Ordinal.{0}) : GvD :=
  Ordinal.limitRecOn (motive := fun _ => GvD) ν gw0 (fun _ D => GvD.ofGs D.step) gwLimD

theorem gwD_zero : gwD 0 = gw0 := by
  unfold gwD; rw [Ordinal.limitRecOn_zero]

theorem gwD_succ (ν : Ordinal.{0}) : gwD (ν + 1) = GvD.ofGs (gwD ν).step := by
  unfold gwD; rw [Ordinal.limitRecOn_add_one]

theorem gwD_limit {l : Ordinal.{0}} (hl : IsSuccLimit l) : gwD l = gwLimD l hl (fun β _ => gwD β) := by
  unfold gwD; rw [Ordinal.limitRecOn_limit _ _ _ _ hl]

theorem gwExt_eq {l β : Ordinal.{0}} (h : β < l) : gwExt l (fun β _ => gwD β) β = gwD β := by
  unfold gwExt; rw [dif_pos h]

/-! ## The invariant at every index -/

/-- The new facts at the top `ν`. -/
structure GwTop (ν : Ordinal.{0}) : Prop where
  ix : (gwD ν).ix = gcG 0 + ν
  cohR : ∀ β, β < ν → ∀ c x, c < (gwD β).B → (gwD ν).R c x = (gwD β).R c x
  cohg : ∀ β, β < ν → ∀ c, c < (gwD β).B → (gwD ν).g c = (gwD β).g c
  hb : ∀ x, InE x → x < Om1 → (gwD ν).γ < x → (gwD ν).b x = veblen 1 (gpI x + (gwD ν).R ν x)
  hγ : ∀ x, InE x → x < Om1 → ((gwD ν).γ < x ↔ (gwD ν).g ν < x)

theorem gwInv_succ {ν : Ordinal.{0}} (H : GwInv ν gwD) (T : GwTop ν) : GwInv (ν + 1) gwD where
  ix := fun β h => by
    rcases (Order.lt_add_one_iff.1 h).lt_or_eq with h' | rfl
    · exact H.ix β h'
    · exact T.ix
  zero := fun _ => gwD_zero
  succ := fun μ _ => gwD_succ μ
  cohR := fun β γ hβγ h c x hc => by
    rcases (Order.lt_add_one_iff.1 h).lt_or_eq with h' | rfl
    · exact H.cohR β γ hβγ h' c x hc
    · rcases hβγ.lt_or_eq with h'' | rfl
      · exact T.cohR β h'' c x hc
      · rfl
  cohg := fun β γ hβγ h c hc => by
    rcases (Order.lt_add_one_iff.1 h).lt_or_eq with h' | rfl
    · exact H.cohg β γ hβγ h' c hc
    · rcases hβγ.lt_or_eq with h'' | rfl
      · exact T.cohg β h'' c hc
      · rfl
  hb := fun β h => by
    rcases (Order.lt_add_one_iff.1 h).lt_or_eq with h' | rfl
    · exact H.hb β h'
    · exact T.hb
  hγ := fun β h => by
    rcases (Order.lt_add_one_iff.1 h).lt_or_eq with h' | rfl
    · exact H.hγ β h'
    · exact T.hγ

theorem gwInv_lim {l : Ordinal.{0}} (IH : ∀ β, β < l → GwInv (β + 1) gwD) : GwInv l gwD where
  ix := fun β h => (IH β h).ix β (lt_add_one β)
  zero := fun _ => gwD_zero
  succ := fun μ _ => gwD_succ μ
  cohR := fun β γ hβγ h => (IH γ h).cohR β γ hβγ (lt_add_one γ)
  cohg := fun β γ hβγ h => (IH γ h).cohg β γ hβγ (lt_add_one γ)
  hb := fun β h => (IH β h).hb β (lt_add_one β)
  hγ := fun β h => (IH β h).hγ β (lt_add_one β)

theorem gwTop_zero : GwTop 0 where
  ix := by rw [gwD_zero, add_zero]; rfl
  cohR := fun _ h => absurd h (not_lt.2 zero_le)
  cohg := fun _ h => absurd h (not_lt.2 zero_le)
  hb := fun x hx hx1 _ => by
    rw [gwD_zero, gw0.R_zero, add_zero, gw0_b]
    exact (epsilon_evIx (goGl.b_E x hx hx1)).symm
  hγ := fun x _ _ => by rw [gwD_zero, gw0.g_zero, gw0_γ]

theorem gwTop_succ {ν : Ordinal.{0}} (hνZ : ν < evZ (gcG 0)) (H : GwInv (ν + 1) gwD) : GwTop (ν + 1) where
  ix := by
    rw [gwD_succ]
    show (gwD ν).step.ix = _
    rw [GvD.step_ix, H.ix ν (lt_add_one ν), add_assoc]
  cohR := fun β hβ c x hc => by
    have hβν : β ≤ ν := Order.lt_add_one_iff.1 hβ
    rw [gwD_succ]
    show (gwD ν).step.R c x = _
    rw [GvD.step_R_low _ (hc.trans_le (H.B_le hβν (lt_add_one ν))) x]
    exact H.cohR β ν hβν (lt_add_one ν) c x hc
  cohg := fun β hβ c hc => by
    have hβν : β ≤ ν := Order.lt_add_one_iff.1 hβ
    rw [gwD_succ]
    show (gwD ν).step.g c = _
    rw [GvD.step_g_low _ (hc.trans_le (H.B_le hβν (lt_add_one ν)))]
    exact H.cohg β ν hβν (lt_add_one ν) c hc
  hb := fun x hx hx1 hγx => by
    have hνB : ν < (gwD ν).B := H.self_lt (lt_add_one ν) hνZ
    have hν1B : ν + 1 < (gwD ν).B := (gwD ν).B_lim.add_one_lt hνB
    have hγ : (gwD ν).γ < x := by rw [gwD_succ] at hγx; exact hγx
    rw [gwD_succ]
    show (gwD ν).step.b x = veblen 1 (gpI x + (gwD ν).step.R (ν + 1) x)
    rw [GvD.step_b, GvD.step_R_low _ hν1B x, (gwD ν).R_succ, H.hb ν (lt_add_one ν) x hx hx1 hγ, go_eN_veb,
      add_assoc]
  hγ := fun x hx hx1 => by
    have hνB : ν < (gwD ν).B := H.self_lt (lt_add_one ν) hνZ
    have hν1B : ν + 1 < (gwD ν).B := (gwD ν).B_lim.add_one_lt hνB
    rw [gwD_succ]
    show (gwD ν).γ < x ↔ (gwD ν).step.g (ν + 1) < x
    rw [GvD.step_g_low _ hν1B, H.hγ ν (lt_add_one ν) x hx hx1]
    exact ⟨fun h => (gwD ν).g_succ x (ev_isSuccLimit_of_inE hx) ν hν1B h,
      fun h => ((gwD ν).g_le_succ ν).trans_lt h⟩

theorem gwD_lim_eq {l : Ordinal.{0}} (hl : IsSuccLimit l) (hlZ : l < evZ (gcG 0)) (H : GwInv l gwD) :
    gwD l = (gwFamOf l hl hlZ (gwExt l fun β _ => gwD β) (H.congr fun β h => gwExt_eq h)).U := by
  rw [gwD_limit hl]; unfold gwLimD; rw [dif_pos ⟨hlZ, H.congr fun β h => gwExt_eq h⟩]

theorem gwTop_lim {l : Ordinal.{0}} (hl : IsSuccLimit l) (hlZ : l < evZ (gcG 0)) (H : GwInv l gwD) :
    GwTop l := by
  set Q := gwFamOf l hl hlZ (gwExt l fun β _ => gwD β) (H.congr fun β h => gwExt_eq h) with hQ
  have e : gwD l = Q.U := gwD_lim_eq hl hlZ H
  have hF : ∀ β, β < l → Q.F β = gwD β := fun β h => gwExt_eq h
  have hl' : Q.l = l := rfl
  obtain ⟨hd, hld⟩ := gwIdx_spec hl hlZ (H.congr fun β h => gwExt_eq h)
  have hE : Q.E = Q.F (gwIdx l (gwExt l fun β _ => gwD β)) := rfl
  refine ⟨?_, fun β hβ c x hc => ?_, fun β hβ c hc => ?_, fun x hx hx1 hγx => ?_, fun x hx hx1 => ?_⟩
  · rw [e]; rfl
  · rw [e, Q.U_R (hl'.symm ▸ hβ) (by rw [hF β hβ]; exact hc) x, hF β hβ]
  · rw [e, Q.U_g (hl'.symm ▸ hβ) (by rw [hF β hβ]; exact hc), hF β hβ]
  · rw [e] at hγx ⊢
    rw [Q.U_b, Q.U_R hd hld x, hE]
    rfl
  · rw [e, Q.U_γ, Q.U_g hd hld, hE]
    rfl

/-- **THE INVARIANT AT EVERY INDEX `ν < ζ_{G+1}`.** -/
theorem gw_inv : ∀ ν : Ordinal.{0}, ν < evZ (gcG 0) → GwInv (ν + 1) gwD := by
  intro ν
  induction ν using Ordinal.limitRecOn with
  | zero => intro _; exact gwInv_succ (gwInv_zero _) gwTop_zero
  | add_one μ ih =>
    intro hν
    have hμ : μ < evZ (gcG 0) := (lt_add_one μ).trans hν
    have H := ih hμ
    exact gwInv_succ H (gwTop_succ hμ H)
  | limit l hl ih =>
    intro hν
    have H := gwInv_lim (fun β hβ => ih β hβ (hβ.trans hν))
    exact gwInv_succ H (gwTop_lim hl hν H)

/-! ## The main facts -/

section Main

variable {ν : Ordinal.{0}} (hν : ν < evZ (gcG 0))
include hν

theorem gw_ix : (gwD ν).ix = gcG 0 + ν := (gw_inv ν hν).ix ν (lt_add_one ν)

/-- **The bound of `gwD ν` is `ε_{G+ν}`.** -/
theorem gw_B : (gwD ν).B = veblen 1 (gcG 0 + ν) := (gw_inv ν hν).B_eq (lt_add_one ν)

/-- **The base reading of `gwD ν` is `φ(1, Γ_{x+1} + ν(x))`** above its gate. -/
theorem gw_b {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγx : (gwD ν).γ < x) :
    (gwD ν).b x = veblen 1 (gpI x + (gwD ν).R ν x) := (gw_inv ν hν).hb ν (lt_add_one ν) x hx hx1 hγx

/-- **The base gate of `gwD ν` lies below an `ε`-number `x` iff the gate of the code `ν` does.** -/
theorem gw_γ_iff {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : (gwD ν).γ < x ↔ (gwD ν).g ν < x :=
  (gw_inv ν hν).hγ ν (lt_add_one ν) x hx hx1

theorem gw_self : ν < (gwD ν).B := by rw [gw_B hν]; exact gw_self_lt hν

end Main

/-- **Later systems extend earlier ones** (readings and gates). -/
theorem gw_ext {β γ : Ordinal.{0}} (hβγ : β ≤ γ) (hγ : γ < evZ (gcG 0)) :
    (∀ c x, c < (gwD β).B → (gwD γ).R c x = (gwD β).R c x) ∧
    (∀ c, c < (gwD β).B → (gwD γ).g c = (gwD β).g c) :=
  ⟨(gw_inv γ hγ).cohR β γ hβγ (lt_add_one γ), (gw_inv γ hγ).cohg β γ hβγ (lt_add_one γ)⟩

theorem gw_succ_eq (ν : Ordinal.{0}) : gwD (ν + 1) = GvD.ofGs (gwD ν).step := gwD_succ ν

end Googology.Trans.PoR.InaccPsi.R2.Gw
