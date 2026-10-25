import Googology.Trans.PoR.InaccPsi.R2.GzS

/-!
# THE RECURSION OF A STAGE FOR SYSTEMS `GzVD`: ALL INDICES IN `[Q, evZ(Q))`, FROM ANY START

Port of `R2.GzRec` (`Gz.gzYD`) to the systems `Gz.GzVD` and any stage `Bp : GzPB`: from a start `U0` with
`GzSStart Bp U0` (index `Q`, base gate `0`, base reading `P(x)`, bound field `evZ(P(x))`), `gzSD Bp U0 d`
(`d < evZ(Q)`) has the bound `ε_{Q+d} = φ(1, Q + d)`: `gzSD Bp U0 0 = U0`, the step at `d+1`, and at a limit `λ` the
union `Gz.GzSFam.U` of all `gzSD Bp U0 μ`, `μ < λ`, with the index `λ` read by the first system containing it as a
code (`Gz.gzq_cover`).  The invariant (`GzSInv`, `gzS_inv`): index `Q + μ`, bound field `evZ(P(x))`, coherence, base
reading `φ(1, P(x) + μ(x))` above the base gate, `γ(gzSD μ) < x ⇔ g(μ) < x`.

* `GzSStart`, `GzSInv`, `gzSIdx`, `gzSFamOf`, `gzSExt`, `gzSLimD`, `gzSD` (**THE RECURSION OF A STAGE**),
  `gzSD_zero`, `gzSD_succ`, `gzSD_limit`, `GzSTop`, `gzS_inv` (**THE INVARIANT AT EVERY INDEX BELOW `evZ(Q)`**);
* `gzS_ix`, `gzS_Z`, `gzS_B`, `gzS_b`, `gzS_γ_iff`, `gzS_self`, `gzS_ext`.

No new axiom.  New definitions: `GzSStart`, `GzSInv`, `GzSTop`, `gzSIdx`, `gzSFamOf`, `gzSExt`, `gzSLimD`, `gzSD`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gz

open Googology.Trans.PoR.InaccPsi.R2.Gw

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

/-! ## The start and the invariant -/

/-- **The start of a stage `Bp`**: a system with index `Q` (bound `Q`), base gate `0`, base reading `P(x)`, bound
field `evZ(P(x))`. -/
structure GzSStart (Bp : GzPB) (U0 : GzVD) : Prop where
  ix : U0.ix = Bp.Q
  γ : U0.γ = 0
  b : ∀ x, InE x → x < Om1 → U0.b x = Bp.P x
  Z : ∀ x, InE x → x < Om1 → U0.Z x = evZ (Bp.P x)

/-- **The invariant of a family below `λ`.** -/
structure GzSInv (Bp : GzPB) (U0 : GzVD) (l : Ordinal.{0}) (F : Ordinal.{0} → GzVD) : Prop where
  ix : ∀ μ, μ < l → (F μ).ix = Bp.Q + μ
  zero : 0 < l → F 0 = U0
  γ0 : 0 < l → (F 0).γ = 0
  succ : ∀ μ, μ + 1 < l → F (μ + 1) = (F μ).step
  N : ∀ μ, μ < l → ∀ x, InE x → x < Om1 → (F μ).Z x = evZ (Bp.P x)
  cohR : ∀ β γ, β ≤ γ → γ < l → ∀ c x, c < (F β).B → (F γ).R c x = (F β).R c x
  cohg : ∀ β γ, β ≤ γ → γ < l → ∀ c, c < (F β).B → (F γ).g c = (F β).g c
  hb : ∀ μ, μ < l → ∀ x, InE x → x < Om1 → (F μ).γ < x → (F μ).b x = veblen 1 (Bp.P x + (F μ).R μ x)
  hγ : ∀ μ, μ < l → ∀ x, InE x → x < Om1 → ((F μ).γ < x ↔ (F μ).g μ < x)

namespace GzSInv

variable {Bp : GzPB} {U0 : GzVD} {l : Ordinal.{0}} {F : Ordinal.{0} → GzVD} (H : GzSInv Bp U0 l F)
include H

theorem B_eq {β : Ordinal.{0}} (h : β < l) : (F β).B = veblen 1 (Bp.Q + β) := by
  rw [(F β).B_ix, H.ix β h]

theorem B_le {β γ : Ordinal.{0}} (hβγ : β ≤ γ) (h : γ < l) : (F β).B ≤ (F γ).B := by
  rw [H.B_eq (lt_of_le_of_lt hβγ h), H.B_eq h]
  exact (isNormal_veblen 1).monotone ((add_le_add_iff_left _).2 hβγ)

theorem self_lt {μ : Ordinal.{0}} (h : μ < l) (hZ : μ < evZ Bp.Q) : μ < (F μ).B := by
  rw [H.B_eq h]; exact gzq_self_lt Bp.Q_fix hZ

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

theorem congr {G : Ordinal.{0} → GzVD} (hFG : ∀ β, β < l → G β = F β) : GzSInv Bp U0 l G where
  ix := fun β h => by rw [hFG β h]; exact H.ix β h
  zero := fun h => by rw [hFG 0 h]; exact H.zero h
  γ0 := fun h => by rw [hFG 0 h]; exact H.γ0 h
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

end GzSInv

theorem gzSInv_zero (Bp : GzPB) (U0 : GzVD) (F : Ordinal.{0} → GzVD) : GzSInv Bp U0 0 F where
  ix := fun _ h => absurd h (not_lt.2 zero_le)
  zero := fun h => absurd h (lt_irrefl 0)
  γ0 := fun h => absurd h (lt_irrefl 0)
  succ := fun μ h => absurd h (not_lt.2 zero_le)
  N := fun _ h => absurd h (not_lt.2 zero_le)
  cohR := fun _ _ _ h => absurd h (not_lt.2 zero_le)
  cohg := fun _ _ _ h => absurd h (not_lt.2 zero_le)
  hb := fun _ h => absurd h (not_lt.2 zero_le)
  hγ := fun _ h => absurd h (not_lt.2 zero_le)

/-! ## The family at a limit -/

section Fam

variable (Bp : GzPB) (U0 : GzVD)

/-- The first member that contains the index `λ` as a code (the index system of the union). -/
noncomputable def gzSIdx (l : Ordinal.{0}) (F : Ordinal.{0} → GzVD) : Ordinal.{0} :=
  sInf {d | d < l ∧ l < (F d).B}

variable {Bp U0}

theorem gzSIdx_spec {l : Ordinal.{0}} {F : Ordinal.{0} → GzVD} (hl : IsSuccLimit l) (hlZ : l < evZ Bp.Q)
    (H : GzSInv Bp U0 l F) : gzSIdx l F < l ∧ l < (F (gzSIdx l F)).B := by
  obtain ⟨d, hd, hld⟩ := gzq_cover Bp.Q_fix hl.bot_lt hlZ
  have h : l < (F d).B := by rw [H.B_eq hd]; exact hld
  exact csInf_mem (s := {d | d < l ∧ l < (F d).B}) ⟨d, hd, h⟩

variable (Bp U0)

/-- **The family over all `μ < λ`**, its indices read by the first member containing `λ`. -/
noncomputable def gzSFamOf (l : Ordinal.{0}) (hl : IsSuccLimit l) (hlZ : l < evZ Bp.Q) (F : Ordinal.{0} → GzVD)
    (H : GzSInv Bp U0 l F) : GzSFam Bp where
  E := F (gzSIdx l F)
  l := l
  F := F
  l_lim := hl
  l_lt := (gzSIdx_spec hl hlZ H).2
  l_Z := hlZ
  EZ := H.N _ (gzSIdx_spec hl hlZ H).1
  hN := H.N
  ix := H.ix
  γ0 := H.γ0 hl.bot_lt
  succ := H.succ
  cohR := H.cohR
  cohg := H.cohg
  hb := fun μ hμ x hx hx1 hγ => by
    obtain ⟨hd, hld⟩ := gzSIdx_spec hl hlZ H
    rw [H.hb μ hμ x hx hx1 hγ, H.R_tr hμ hd (hμ.trans hld) (H.self_lt hμ (hμ.trans hlZ)) x]
  hγ := fun μ hμ x hx hx1 => by
    obtain ⟨hd, hld⟩ := gzSIdx_spec hl hlZ H
    rw [H.hγ μ hμ x hx hx1, H.g_tr hμ hd (hμ.trans hld) (H.self_lt hμ (hμ.trans hlZ))]

/-- The family of the earlier values, extended by the start. -/
noncomputable def gzSExt (l : Ordinal.{0}) (IH : ∀ β, β < l → GzVD) (β : Ordinal.{0}) : GzVD :=
  if h : β < l then IH β h else U0

open Classical in
/-- The limit step: the union over all smaller indices when the invariant holds. -/
noncomputable def gzSLimD (l : Ordinal.{0}) (hl : IsSuccLimit l) (IH : ∀ β, β < l → GzVD) : GzVD :=
  if H : l < evZ Bp.Q ∧ GzSInv Bp U0 l (gzSExt U0 l IH) then (gzSFamOf Bp U0 l hl H.1 (gzSExt U0 l IH) H.2).U
  else U0

/-- **THE RECURSION OF A STAGE**: the start `U0` at `0`, the step at `c+1`, the union over all `μ < λ` at a
limit `λ`; `gzSD Bp U0 d` has the bound `ε_{Q+d}`. -/
noncomputable def gzSD (ν : Ordinal.{0}) : GzVD :=
  Ordinal.limitRecOn (motive := fun _ => GzVD) ν U0 (fun _ D => D.step) (gzSLimD Bp U0)

theorem gzSD_zero : gzSD Bp U0 0 = U0 := by
  unfold gzSD; rw [Ordinal.limitRecOn_zero]

theorem gzSD_succ (ν : Ordinal.{0}) : gzSD Bp U0 (ν + 1) = (gzSD Bp U0 ν).step := by
  unfold gzSD; rw [Ordinal.limitRecOn_add_one]

theorem gzSD_limit {l : Ordinal.{0}} (hl : IsSuccLimit l) :
    gzSD Bp U0 l = gzSLimD Bp U0 l hl (fun β _ => gzSD Bp U0 β) := by
  unfold gzSD; rw [Ordinal.limitRecOn_limit _ _ _ _ hl]

theorem gzSExt_eq {l β : Ordinal.{0}} (h : β < l) : gzSExt U0 l (fun β _ => gzSD Bp U0 β) β = gzSD Bp U0 β := by
  unfold gzSExt; rw [dif_pos h]

end Fam

/-! ## The invariant at every index -/

/-- The new facts at the top `ν`. -/
structure GzSTop (Bp : GzPB) (U0 : GzVD) (ν : Ordinal.{0}) : Prop where
  ix : (gzSD Bp U0 ν).ix = Bp.Q + ν
  N : ∀ x, InE x → x < Om1 → (gzSD Bp U0 ν).Z x = evZ (Bp.P x)
  cohR : ∀ β, β < ν → ∀ c x, c < (gzSD Bp U0 β).B → (gzSD Bp U0 ν).R c x = (gzSD Bp U0 β).R c x
  cohg : ∀ β, β < ν → ∀ c, c < (gzSD Bp U0 β).B → (gzSD Bp U0 ν).g c = (gzSD Bp U0 β).g c
  hb : ∀ x, InE x → x < Om1 → (gzSD Bp U0 ν).γ < x →
    (gzSD Bp U0 ν).b x = veblen 1 (Bp.P x + (gzSD Bp U0 ν).R ν x)
  hγ : ∀ x, InE x → x < Om1 → ((gzSD Bp U0 ν).γ < x ↔ (gzSD Bp U0 ν).g ν < x)

section Inv

variable {Bp : GzPB} {U0 : GzVD} (hU : GzSStart Bp U0)
include hU

theorem gzSInv_succ {ν : Ordinal.{0}} (H : GzSInv Bp U0 ν (gzSD Bp U0)) (T : GzSTop Bp U0 ν) :
    GzSInv Bp U0 (ν + 1) (gzSD Bp U0) where
  ix := fun β h => by
    rcases (Order.lt_add_one_iff.1 h).lt_or_eq with h' | rfl
    · exact H.ix β h'
    · exact T.ix
  N := fun β h => by
    rcases (Order.lt_add_one_iff.1 h).lt_or_eq with h' | rfl
    · exact H.N β h'
    · exact T.N
  zero := fun _ => gzSD_zero Bp U0
  γ0 := fun _ => by rw [gzSD_zero]; exact hU.γ
  succ := fun μ _ => gzSD_succ Bp U0 μ
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

theorem gzSInv_lim {l : Ordinal.{0}} (IH : ∀ β, β < l → GzSInv Bp U0 (β + 1) (gzSD Bp U0)) :
    GzSInv Bp U0 l (gzSD Bp U0) where
  ix := fun β h => (IH β h).ix β (lt_add_one β)
  N := fun β h => (IH β h).N β (lt_add_one β)
  zero := fun _ => gzSD_zero Bp U0
  γ0 := fun _ => by rw [gzSD_zero]; exact hU.γ
  succ := fun μ _ => gzSD_succ Bp U0 μ
  cohR := fun β γ hβγ h => (IH γ h).cohR β γ hβγ (lt_add_one γ)
  cohg := fun β γ hβγ h => (IH γ h).cohg β γ hβγ (lt_add_one γ)
  hb := fun β h => (IH β h).hb β (lt_add_one β)
  hγ := fun β h => (IH β h).hγ β (lt_add_one β)

theorem gzSTop_zero : GzSTop Bp U0 0 where
  ix := by rw [gzSD_zero, add_zero]; exact hU.ix
  N := fun x hx hx1 => by rw [gzSD_zero]; exact hU.Z x hx hx1
  cohR := fun _ h => absurd h (not_lt.2 zero_le)
  cohg := fun _ h => absurd h (not_lt.2 zero_le)
  hb := fun x hx hx1 _ => by
    rw [gzSD_zero, U0.R_zero, add_zero, hU.b x hx hx1]
    exact (Bp.P_fix hx hx1).symm
  hγ := fun x _ _ => by rw [gzSD_zero, U0.g_zero, hU.γ]

omit hU in
theorem gzSTop_succ {ν : Ordinal.{0}} (hνZ : ν < evZ Bp.Q) (H : GzSInv Bp U0 (ν + 1) (gzSD Bp U0)) :
    GzSTop Bp U0 (ν + 1) where
  ix := by
    rw [gzSD_succ]
    show (gzSD Bp U0 ν).step.ix = _
    rw [GzVD.step_ix, H.ix ν (lt_add_one ν), add_assoc]
  N := fun x hx hx1 => by
    rw [gzSD_succ]
    show (gzSD Bp U0 ν).step.Z x = _
    rw [GzVD.step_Z]; exact H.N ν (lt_add_one ν) x hx hx1
  cohR := fun β hβ c x hc => by
    have hβν : β ≤ ν := Order.lt_add_one_iff.1 hβ
    rw [gzSD_succ]
    show (gzSD Bp U0 ν).step.R c x = _
    rw [GzVD.step_R_low _ (hc.trans_le (H.B_le hβν (lt_add_one ν))) x]
    exact H.cohR β ν hβν (lt_add_one ν) c x hc
  cohg := fun β hβ c hc => by
    have hβν : β ≤ ν := Order.lt_add_one_iff.1 hβ
    rw [gzSD_succ]
    show (gzSD Bp U0 ν).step.g c = _
    rw [GzVD.step_g_low _ (hc.trans_le (H.B_le hβν (lt_add_one ν)))]
    exact H.cohg β ν hβν (lt_add_one ν) c hc
  hb := fun x hx hx1 hγx => by
    have hνB : ν < (gzSD Bp U0 ν).B := H.self_lt (lt_add_one ν) hνZ
    have hν1B : ν + 1 < (gzSD Bp U0 ν).B := (gzSD Bp U0 ν).B_lim.add_one_lt hνB
    have hγ : (gzSD Bp U0 ν).γ < x := by rw [gzSD_succ] at hγx; exact hγx
    rw [gzSD_succ]
    show (gzSD Bp U0 ν).step.b x = veblen 1 (Bp.P x + (gzSD Bp U0 ν).step.R (ν + 1) x)
    rw [GzVD.step_b, GzVD.step_R_low _ hν1B x, (gzSD Bp U0 ν).R_succ, H.hb ν (lt_add_one ν) x hx hx1 hγ, go_eN_veb,
      add_assoc]
  hγ := fun x hx hx1 => by
    have hνB : ν < (gzSD Bp U0 ν).B := H.self_lt (lt_add_one ν) hνZ
    have hν1B : ν + 1 < (gzSD Bp U0 ν).B := (gzSD Bp U0 ν).B_lim.add_one_lt hνB
    rw [gzSD_succ]
    show (gzSD Bp U0 ν).γ < x ↔ (gzSD Bp U0 ν).step.g (ν + 1) < x
    rw [GzVD.step_g_low _ hν1B, H.hγ ν (lt_add_one ν) x hx hx1]
    exact ⟨fun h => (gzSD Bp U0 ν).g_succ x (ev_isSuccLimit_of_inE hx) ν hν1B h,
      fun h => ((gzSD Bp U0 ν).g_le_succ ν).trans_lt h⟩

omit hU in
theorem gzSD_lim_eq {l : Ordinal.{0}} (hl : IsSuccLimit l) (hlZ : l < evZ Bp.Q) (H : GzSInv Bp U0 l (gzSD Bp U0)) :
    gzSD Bp U0 l = (gzSFamOf Bp U0 l hl hlZ (gzSExt U0 l fun β _ => gzSD Bp U0 β)
      (H.congr fun β h => gzSExt_eq Bp U0 h)).U := by
  rw [gzSD_limit Bp U0 hl]; unfold gzSLimD; rw [dif_pos ⟨hlZ, H.congr fun β h => gzSExt_eq Bp U0 h⟩]

omit hU in
theorem gzSTop_lim {l : Ordinal.{0}} (hl : IsSuccLimit l) (hlZ : l < evZ Bp.Q) (H : GzSInv Bp U0 l (gzSD Bp U0)) :
    GzSTop Bp U0 l := by
  set Q := gzSFamOf Bp U0 l hl hlZ (gzSExt U0 l fun β _ => gzSD Bp U0 β) (H.congr fun β h => gzSExt_eq Bp U0 h)
    with hQ
  have e : gzSD Bp U0 l = Q.U := gzSD_lim_eq hl hlZ H
  have hF : ∀ β, β < l → Q.F β = gzSD Bp U0 β := fun β h => gzSExt_eq Bp U0 h
  have hl' : Q.l = l := rfl
  obtain ⟨hd, hld⟩ := gzSIdx_spec hl hlZ (H.congr fun β h => gzSExt_eq Bp U0 h)
  have hE : Q.E = Q.F (gzSIdx l (gzSExt U0 l fun β _ => gzSD Bp U0 β)) := rfl
  refine ⟨?_, ?_, fun β hβ c x hc => ?_, fun β hβ c hc => ?_, fun x hx hx1 hγx => ?_, fun x hx hx1 => ?_⟩
  · rw [e]; rfl
  · intro x _ _; rw [e]; rfl
  · rw [e, Q.U_R (hl'.symm ▸ hβ) (by rw [hF β hβ]; exact hc) x, hF β hβ]
  · rw [e, Q.U_g (hl'.symm ▸ hβ) (by rw [hF β hβ]; exact hc), hF β hβ]
  · rw [e] at hγx ⊢
    rw [Q.U_b, Q.U_R hd hld x, hE]
    rfl
  · rw [e, Q.U_γ, Q.U_g hd hld, hE]
    rfl

/-- **THE INVARIANT AT EVERY INDEX `ν < evZ(Q)`.** -/
theorem gzS_inv : ∀ ν : Ordinal.{0}, ν < evZ Bp.Q → GzSInv Bp U0 (ν + 1) (gzSD Bp U0) := by
  intro ν
  induction ν using Ordinal.limitRecOn with
  | zero => intro _; exact gzSInv_succ hU (gzSInv_zero Bp U0 _) (gzSTop_zero hU)
  | add_one μ ih =>
    intro hν
    have hμ : μ < evZ Bp.Q := (lt_add_one μ).trans hν
    have H := ih hμ
    exact gzSInv_succ hU H (gzSTop_succ hμ H)
  | limit l hl ih =>
    intro hν
    have H := gzSInv_lim hU (fun β hβ => ih β hβ (hβ.trans hν))
    exact gzSInv_succ hU H (gzSTop_lim hl hν H)

end Inv

/-! ## The main facts -/

section Main

variable {Bp : GzPB} {U0 : GzVD} (hU : GzSStart Bp U0) {ν : Ordinal.{0}} (hν : ν < evZ Bp.Q)
include hU hν

theorem gzS_ix : (gzSD Bp U0 ν).ix = Bp.Q + ν := (gzS_inv hU ν hν).ix ν (lt_add_one ν)

theorem gzS_Z {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : (gzSD Bp U0 ν).Z x = evZ (Bp.P x) :=
  (gzS_inv hU ν hν).N ν (lt_add_one ν) x hx hx1

/-- **The bound of `gzSD Bp U0 ν` is `ε_{Q+ν}`.** -/
theorem gzS_B : (gzSD Bp U0 ν).B = veblen 1 (Bp.Q + ν) := (gzS_inv hU ν hν).B_eq (lt_add_one ν)

/-- **The base reading of `gzSD Bp U0 ν` is `φ(1, P(x) + ν(x))`** above its gate. -/
theorem gzS_b {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγx : (gzSD Bp U0 ν).γ < x) :
    (gzSD Bp U0 ν).b x = veblen 1 (Bp.P x + (gzSD Bp U0 ν).R ν x) :=
  (gzS_inv hU ν hν).hb ν (lt_add_one ν) x hx hx1 hγx

/-- **The base gate of `gzSD Bp U0 ν` lies below an `ε`-number `x` iff the gate of the code `ν` does.** -/
theorem gzS_γ_iff {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : (gzSD Bp U0 ν).γ < x ↔ (gzSD Bp U0 ν).g ν < x :=
  (gzS_inv hU ν hν).hγ ν (lt_add_one ν) x hx hx1

theorem gzS_self : ν < (gzSD Bp U0 ν).B := by rw [gzS_B hU hν]; exact gzq_self_lt Bp.Q_fix hν

end Main

/-- **Later systems extend earlier ones** (readings and gates). -/
theorem gzS_ext {Bp : GzPB} {U0 : GzVD} (hU : GzSStart Bp U0) {β γ : Ordinal.{0}} (hβγ : β ≤ γ) (hγ : γ < evZ Bp.Q) :
    (∀ c x, c < (gzSD Bp U0 β).B → (gzSD Bp U0 γ).R c x = (gzSD Bp U0 β).R c x) ∧
    (∀ c, c < (gzSD Bp U0 β).B → (gzSD Bp U0 γ).g c = (gzSD Bp U0 β).g c) :=
  ⟨(gzS_inv hU γ hγ).cohR β γ hβγ (lt_add_one γ), (gzS_inv hU γ hγ).cohg β γ hβγ (lt_add_one γ)⟩

end Googology.Trans.PoR.InaccPsi.R2.Gz
