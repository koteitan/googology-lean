import Googology.Trans.PoR.InaccPsi.R2.GwY

/-!
# THE RECURSION OVER ALL INDICES IN `[ζ_{G+1}, ζ_{G+2})`, STARTING FROM THE SELF-READ UNION AT `ζ_{G+1}`

Port of `Gw.gwYD` (`R2.GwRec`) to the systems `GwZD` (`N = 1`): `gwYD d` (`d < ζ_{G+2}`) has the bound
`ε_{ζ_{G+1}+d} = φ(1, ζ_{G+1} + d)`: `gwYD 0 = gwZU` (the union at `ζ_{G+1}`, `R2.GwZU`), `gwYD (d+1)` is the step of
`gwYD d`, and at a limit `λ` it is the union `GwYFam.U` of all `gwYD μ`, `μ < λ`, with the index `λ` read by the first
system that contains `λ` as a code (`gwY_cover`).  The invariant (`GwYInv`, at every `ν < ζ_{G+2}`, `gwY_inv`): index
`ζ_{G+1} + μ`, `N = 1`, coherence, the base reading `φ(1, ζ_{Γ_{x+1}+1} + μ(x))` above the base gate, and
`γ(gwYD μ) < x ⇔ g(μ) < x`.

* `GwYInv`, `gwYIdx`, `gwYFamOf`, `gwYExt`, `gwYLimD`, `gwYD` (**THE RECURSION**), `gwYD_zero`, `gwYD_succ`,
  `gwYD_limit`, `GwYTop`, `gwY_inv` (**THE INVARIANT AT EVERY INDEX BELOW `ζ_{G+2}`**);
* `gwY_B`, `gwY_ix`, `gwY_N`, `gwY_b`, `gwY_γ_iff`, `gwY_ext`, `gwY_self`.

No new axiom.  New definitions: `GwYInv`, `GwYTop`, `gwYIdx`, `gwYFamOf`, `gwYExt`, `gwYLimD`, `gwYD`.
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

/-! ## The invariant -/

/-- **The invariant of a family below `λ`.** -/
structure GwYInv (l : Ordinal.{0}) (F : Ordinal.{0} → GwZD) : Prop where
  ix : ∀ μ, μ < l → (F μ).ix = gwZ + μ
  zero : 0 < l → F 0 = gwZU
  succ : ∀ μ, μ + 1 < l → F (μ + 1) = (F μ).step
  N : ∀ μ, μ < l → (F μ).N = 1
  cohR : ∀ β γ, β ≤ γ → γ < l → ∀ c x, c < (F β).B → (F γ).R c x = (F β).R c x
  cohg : ∀ β γ, β ≤ γ → γ < l → ∀ c, c < (F β).B → (F γ).g c = (F β).g c
  hb : ∀ μ, μ < l → ∀ x, InE x → x < Om1 → (F μ).γ < x → (F μ).b x = veblen 1 (evZ (lgG x) + (F μ).R μ x)
  hγ : ∀ μ, μ < l → ∀ x, InE x → x < Om1 → ((F μ).γ < x ↔ (F μ).g μ < x)

namespace GwYInv

variable {l : Ordinal.{0}} {F : Ordinal.{0} → GwZD} (H : GwYInv l F)
include H

theorem B_eq {β : Ordinal.{0}} (h : β < l) : (F β).B = veblen 1 (gwZ + β) := by
  rw [(F β).B_ix, H.ix β h]

theorem B_le {β γ : Ordinal.{0}} (hβγ : β ≤ γ) (h : γ < l) : (F β).B ≤ (F γ).B := by
  rw [H.B_eq (lt_of_le_of_lt hβγ h), H.B_eq h]
  exact (isNormal_veblen 1).monotone ((add_le_add_iff_left _).2 hβγ)

theorem self_lt {μ : Ordinal.{0}} (h : μ < l) (hZ : μ < evZ gwZ) : μ < (F μ).B := by
  rw [H.B_eq h]; exact gwY_self_lt hZ

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

theorem congr {G : Ordinal.{0} → GwZD} (hFG : ∀ β, β < l → G β = F β) : GwYInv l G where
  ix := fun β h => by rw [hFG β h]; exact H.ix β h
  zero := fun h => by rw [hFG 0 h]; exact H.zero h
  succ := fun μ h => by rw [hFG (μ + 1) h, hFG μ ((lt_add_one μ).trans h)]; exact H.succ μ h
  N := fun μ h => by rw [hFG μ h]; exact H.N μ h
  cohR := fun β γ hβγ h c x hc => by
    rw [hFG β (lt_of_le_of_lt hβγ h)] at hc ⊢
    rw [hFG γ h]; exact H.cohR β γ hβγ h c x hc
  cohg := fun β γ hβγ h c hc => by
    rw [hFG β (lt_of_le_of_lt hβγ h)] at hc ⊢
    rw [hFG γ h]; exact H.cohg β γ hβγ h c hc
  hb := fun μ h x hx hx1 => by rw [hFG μ h]; exact H.hb μ h x hx hx1
  hγ := fun μ h x hx hx1 => by rw [hFG μ h]; exact H.hγ μ h x hx hx1

end GwYInv

theorem gwYInv_zero (F : Ordinal.{0} → GwZD) : GwYInv 0 F where
  ix := fun _ h => absurd h (not_lt.2 zero_le)
  zero := fun h => absurd h (lt_irrefl 0)
  succ := fun μ h => absurd h (not_lt.2 zero_le)
  N := fun _ h => absurd h (not_lt.2 zero_le)
  cohR := fun _ _ _ h => absurd h (not_lt.2 zero_le)
  cohg := fun _ _ _ h => absurd h (not_lt.2 zero_le)
  hb := fun _ h => absurd h (not_lt.2 zero_le)
  hγ := fun _ h => absurd h (not_lt.2 zero_le)

/-! ## The family at a limit -/

/-- The first member that contains the index `λ` as a code (the index system of the union). -/
noncomputable def gwYIdx (l : Ordinal.{0}) (F : Ordinal.{0} → GwZD) : Ordinal.{0} :=
  sInf {d | d < l ∧ l < (F d).B}

theorem gwYIdx_spec {l : Ordinal.{0}} {F : Ordinal.{0} → GwZD} (hl : IsSuccLimit l) (hlZ : l < evZ gwZ)
    (H : GwYInv l F) : gwYIdx l F < l ∧ l < (F (gwYIdx l F)).B := by
  obtain ⟨d, hd, hld⟩ := gwY_cover hl.bot_lt hlZ
  have h : l < (F d).B := by rw [H.B_eq hd]; exact hld
  exact csInf_mem (s := {d | d < l ∧ l < (F d).B}) ⟨d, hd, h⟩

/-- **The family over all `μ < λ`**, its indices read by the first member containing `λ`. -/
noncomputable def gwYFamOf (l : Ordinal.{0}) (hl : IsSuccLimit l) (hlZ : l < evZ gwZ) (F : Ordinal.{0} → GwZD)
    (H : GwYInv l F) : GwYFam where
  E := F (gwYIdx l F)
  l := l
  F := F
  l_lim := hl
  l_lt := (gwYIdx_spec hl hlZ H).2
  l_Z := hlZ
  EN := H.N _ (gwYIdx_spec hl hlZ H).1
  hN := H.N
  ix := H.ix
  γ0 := by rw [H.zero hl.bot_lt]; rfl
  succ := H.succ
  cohR := H.cohR
  cohg := H.cohg
  hb := fun μ hμ x hx hx1 hγ => by
    obtain ⟨hd, hld⟩ := gwYIdx_spec hl hlZ H
    rw [H.hb μ hμ x hx hx1 hγ, H.R_tr hμ hd (hμ.trans hld) (H.self_lt hμ (hμ.trans hlZ)) x]
  hγ := fun μ hμ x hx hx1 => by
    obtain ⟨hd, hld⟩ := gwYIdx_spec hl hlZ H
    rw [H.hγ μ hμ x hx hx1, H.g_tr hμ hd (hμ.trans hld) (H.self_lt hμ (hμ.trans hlZ))]

/-- The family of the earlier values, extended by the start. -/
noncomputable def gwYExt (l : Ordinal.{0}) (IH : ∀ β, β < l → GwZD) (β : Ordinal.{0}) : GwZD :=
  if h : β < l then IH β h else gwZU

open Classical in
/-- The limit step: the union over all smaller indices when the invariant holds (it does below `ζ_{G+1}`). -/
noncomputable def gwYLimD (l : Ordinal.{0}) (hl : IsSuccLimit l) (IH : ∀ β, β < l → GwZD) : GwZD :=
  if H : l < evZ gwZ ∧ GwYInv l (gwYExt l IH) then (gwYFamOf l hl H.1 (gwYExt l IH) H.2).U else gwZU

/-- **THE RECURSION**: `goGl` at `0`, the step at `c+1`, the union over all `μ < λ` at a limit `λ`. -/
noncomputable def gwYD (ν : Ordinal.{0}) : GwZD :=
  Ordinal.limitRecOn (motive := fun _ => GwZD) ν gwZU (fun _ D => D.step) gwYLimD

theorem gwYD_zero : gwYD 0 = gwZU := by
  unfold gwYD; rw [Ordinal.limitRecOn_zero]

theorem gwYD_succ (ν : Ordinal.{0}) : gwYD (ν + 1) = (gwYD ν).step := by
  unfold gwYD; rw [Ordinal.limitRecOn_add_one]

theorem gwYD_limit {l : Ordinal.{0}} (hl : IsSuccLimit l) : gwYD l = gwYLimD l hl (fun β _ => gwYD β) := by
  unfold gwYD; rw [Ordinal.limitRecOn_limit _ _ _ _ hl]

theorem gwYExt_eq {l β : Ordinal.{0}} (h : β < l) : gwYExt l (fun β _ => gwYD β) β = gwYD β := by
  unfold gwYExt; rw [dif_pos h]

/-! ## The invariant at every index -/

/-- The new facts at the top `ν`. -/
structure GwYTop (ν : Ordinal.{0}) : Prop where
  ix : (gwYD ν).ix = gwZ + ν
  N : (gwYD ν).N = 1
  cohR : ∀ β, β < ν → ∀ c x, c < (gwYD β).B → (gwYD ν).R c x = (gwYD β).R c x
  cohg : ∀ β, β < ν → ∀ c, c < (gwYD β).B → (gwYD ν).g c = (gwYD β).g c
  hb : ∀ x, InE x → x < Om1 → (gwYD ν).γ < x → (gwYD ν).b x = veblen 1 (evZ (lgG x) + (gwYD ν).R ν x)
  hγ : ∀ x, InE x → x < Om1 → ((gwYD ν).γ < x ↔ (gwYD ν).g ν < x)

theorem gwYInv_succ {ν : Ordinal.{0}} (H : GwYInv ν gwYD) (T : GwYTop ν) : GwYInv (ν + 1) gwYD where
  ix := fun β h => by
    rcases (Order.lt_add_one_iff.1 h).lt_or_eq with h' | rfl
    · exact H.ix β h'
    · exact T.ix
  N := fun β h => by
    rcases (Order.lt_add_one_iff.1 h).lt_or_eq with h' | rfl
    · exact H.N β h'
    · exact T.N
  zero := fun _ => gwYD_zero
  succ := fun μ _ => gwYD_succ μ
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

theorem gwYInv_lim {l : Ordinal.{0}} (IH : ∀ β, β < l → GwYInv (β + 1) gwYD) : GwYInv l gwYD where
  ix := fun β h => (IH β h).ix β (lt_add_one β)
  N := fun β h => (IH β h).N β (lt_add_one β)
  zero := fun _ => gwYD_zero
  succ := fun μ _ => gwYD_succ μ
  cohR := fun β γ hβγ h => (IH γ h).cohR β γ hβγ (lt_add_one γ)
  cohg := fun β γ hβγ h => (IH γ h).cohg β γ hβγ (lt_add_one γ)
  hb := fun β h => (IH β h).hb β (lt_add_one β)
  hγ := fun β h => (IH β h).hγ β (lt_add_one β)

theorem gwYTop_zero : GwYTop 0 where
  ix := by rw [gwYD_zero, add_zero]; rfl
  N := by rw [gwYD_zero]; rfl
  cohR := fun _ h => absurd h (not_lt.2 zero_le)
  cohg := fun _ h => absurd h (not_lt.2 zero_le)
  hb := fun x _ _ _ => by
    rw [gwYD_zero, gwZU.R_zero, add_zero, gwZU_b]
    exact (epsilon_evZ _).symm
  hγ := fun x _ _ => by rw [gwYD_zero, gwZU.g_zero, gwZU_γ]

theorem gwYTop_succ {ν : Ordinal.{0}} (hνZ : ν < evZ gwZ) (H : GwYInv (ν + 1) gwYD) : GwYTop (ν + 1) where
  ix := by
    rw [gwYD_succ]
    show (gwYD ν).step.ix = _
    rw [GwZD.step_ix, H.ix ν (lt_add_one ν), add_assoc]
  N := by
    rw [gwYD_succ]
    show (gwYD ν).step.N = 1
    rw [GwZD.step_N]; exact H.N ν (lt_add_one ν)
  cohR := fun β hβ c x hc => by
    have hβν : β ≤ ν := Order.lt_add_one_iff.1 hβ
    rw [gwYD_succ]
    show (gwYD ν).step.R c x = _
    rw [GwZD.step_R_low _ (hc.trans_le (H.B_le hβν (lt_add_one ν))) x]
    exact H.cohR β ν hβν (lt_add_one ν) c x hc
  cohg := fun β hβ c hc => by
    have hβν : β ≤ ν := Order.lt_add_one_iff.1 hβ
    rw [gwYD_succ]
    show (gwYD ν).step.g c = _
    rw [GwZD.step_g_low _ (hc.trans_le (H.B_le hβν (lt_add_one ν)))]
    exact H.cohg β ν hβν (lt_add_one ν) c hc
  hb := fun x hx hx1 hγx => by
    have hνB : ν < (gwYD ν).B := H.self_lt (lt_add_one ν) hνZ
    have hν1B : ν + 1 < (gwYD ν).B := (gwYD ν).B_lim.add_one_lt hνB
    have hγ : (gwYD ν).γ < x := by rw [gwYD_succ] at hγx; exact hγx
    rw [gwYD_succ]
    show (gwYD ν).step.b x = veblen 1 (evZ (lgG x) + (gwYD ν).step.R (ν + 1) x)
    rw [GwZD.step_b, GwZD.step_R_low _ hν1B x, (gwYD ν).R_succ, H.hb ν (lt_add_one ν) x hx hx1 hγ, go_eN_veb,
      add_assoc]
  hγ := fun x hx hx1 => by
    have hνB : ν < (gwYD ν).B := H.self_lt (lt_add_one ν) hνZ
    have hν1B : ν + 1 < (gwYD ν).B := (gwYD ν).B_lim.add_one_lt hνB
    rw [gwYD_succ]
    show (gwYD ν).γ < x ↔ (gwYD ν).step.g (ν + 1) < x
    rw [GwZD.step_g_low _ hν1B, H.hγ ν (lt_add_one ν) x hx hx1]
    exact ⟨fun h => (gwYD ν).g_succ x (ev_isSuccLimit_of_inE hx) ν hν1B h,
      fun h => ((gwYD ν).g_le_succ ν).trans_lt h⟩

theorem gwYD_lim_eq {l : Ordinal.{0}} (hl : IsSuccLimit l) (hlZ : l < evZ gwZ) (H : GwYInv l gwYD) :
    gwYD l = (gwYFamOf l hl hlZ (gwYExt l fun β _ => gwYD β) (H.congr fun β h => gwYExt_eq h)).U := by
  rw [gwYD_limit hl]; unfold gwYLimD; rw [dif_pos ⟨hlZ, H.congr fun β h => gwYExt_eq h⟩]

theorem gwYTop_lim {l : Ordinal.{0}} (hl : IsSuccLimit l) (hlZ : l < evZ gwZ) (H : GwYInv l gwYD) :
    GwYTop l := by
  set Q := gwYFamOf l hl hlZ (gwYExt l fun β _ => gwYD β) (H.congr fun β h => gwYExt_eq h) with hQ
  have e : gwYD l = Q.U := gwYD_lim_eq hl hlZ H
  have hF : ∀ β, β < l → Q.F β = gwYD β := fun β h => gwYExt_eq h
  have hl' : Q.l = l := rfl
  obtain ⟨hd, hld⟩ := gwYIdx_spec hl hlZ (H.congr fun β h => gwYExt_eq h)
  have hE : Q.E = Q.F (gwYIdx l (gwYExt l fun β _ => gwYD β)) := rfl
  refine ⟨?_, ?_, fun β hβ c x hc => ?_, fun β hβ c hc => ?_, fun x hx hx1 hγx => ?_, fun x hx hx1 => ?_⟩
  · rw [e]; rfl
  · rw [e]; rfl
  · rw [e, Q.U_R (hl'.symm ▸ hβ) (by rw [hF β hβ]; exact hc) x, hF β hβ]
  · rw [e, Q.U_g (hl'.symm ▸ hβ) (by rw [hF β hβ]; exact hc), hF β hβ]
  · rw [e] at hγx ⊢
    rw [Q.U_b, Q.U_R hd hld x, hE]
    rfl
  · rw [e, Q.U_γ, Q.U_g hd hld, hE]
    rfl

/-- **THE INVARIANT AT EVERY INDEX `ν < ζ_{G+1}`.** -/
theorem gwY_inv : ∀ ν : Ordinal.{0}, ν < evZ gwZ → GwYInv (ν + 1) gwYD := by
  intro ν
  induction ν using Ordinal.limitRecOn with
  | zero => intro _; exact gwYInv_succ (gwYInv_zero _) gwYTop_zero
  | add_one μ ih =>
    intro hν
    have hμ : μ < evZ gwZ := (lt_add_one μ).trans hν
    have H := ih hμ
    exact gwYInv_succ H (gwYTop_succ hμ H)
  | limit l hl ih =>
    intro hν
    have H := gwYInv_lim (fun β hβ => ih β hβ (hβ.trans hν))
    exact gwYInv_succ H (gwYTop_lim hl hν H)

/-! ## The main facts -/

section Main

variable {ν : Ordinal.{0}} (hν : ν < evZ gwZ)
include hν

theorem gwY_ix : (gwYD ν).ix = gwZ + ν := (gwY_inv ν hν).ix ν (lt_add_one ν)

/-- **The bound of `gwYD ν` is `ε_{G+ν}`.** -/
theorem gwY_B : (gwYD ν).B = veblen 1 (gwZ + ν) := (gwY_inv ν hν).B_eq (lt_add_one ν)

/-- **The base reading of `gwYD ν` is `φ(1, Γ_{x+1} + ν(x))`** above its gate. -/
theorem gwY_b {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγx : (gwYD ν).γ < x) :
    (gwYD ν).b x = veblen 1 (evZ (lgG x) + (gwYD ν).R ν x) := (gwY_inv ν hν).hb ν (lt_add_one ν) x hx hx1 hγx

/-- **The base gate of `gwYD ν` lies below an `ε`-number `x` iff the gate of the code `ν` does.** -/
theorem gwY_γ_iff {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : (gwYD ν).γ < x ↔ (gwYD ν).g ν < x :=
  (gwY_inv ν hν).hγ ν (lt_add_one ν) x hx hx1

theorem gwY_self : ν < (gwYD ν).B := by rw [gwY_B hν]; exact gwY_self_lt hν

end Main

/-- **Later systems extend earlier ones** (readings and gates). -/
theorem gwY_ext {β γ : Ordinal.{0}} (hβγ : β ≤ γ) (hγ : γ < evZ gwZ) :
    (∀ c x, c < (gwYD β).B → (gwYD γ).R c x = (gwYD β).R c x) ∧
    (∀ c, c < (gwYD β).B → (gwYD γ).g c = (gwYD β).g c) :=
  ⟨(gwY_inv γ hγ).cohR β γ hβγ (lt_add_one γ), (gwY_inv γ hγ).cohg β γ hβγ (lt_add_one γ)⟩

theorem gwY_succ_eq (ν : Ordinal.{0}) : gwYD (ν + 1) = (gwYD ν).step := gwYD_succ ν

end Googology.Trans.PoR.InaccPsi.R2.Gw
