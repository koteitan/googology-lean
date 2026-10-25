import Googology.Trans.PoR.InaccPsi.R2.HaS

/-!
# HaSRec: THE RECURSION OF A GATED STAGE: ALL OFFSETS IN `[Q, evZ(Q))`, FROM ANY START

`Gz.gzSD` for a gated stage `Bp : Ha.HaPB`: from a start `U0` with `HaSStart Bp U0` (index `Q`, base gate `γ < x ⇔
γ_P < x` at every base, base reading `P(x)` above it, bound field `Zst`), `haSD Bp U0 d` (`d < evZ(Q)`) has the bound
`ε_{Q+d} = φ(1, Q + d)`: `U0` at `0`, the step at `d+1`, the union `Ha.HaSFam.U` at a limit (index read by the first
member containing it).  The invariant (`HaSInv`, `haS_inv`): index `Q + μ`, bound field `Zst`, coherence, base reading
`φ(1, P(x) + μ(x))` above the base gate, `γ(haSD μ) < x ⇔ max(γ_P, g(μ)) < x`.

* `HaSStart`, `HaSInv`, `haSIdx`, `haSFamOf`, `haSExt`, `haSLimD`, `haSD` (**THE RECURSION OF A GATED STAGE**),
  `haSD_zero`, `haSD_succ`, `haSD_limit`, `HaSTop`, `haS_inv` (**THE INVARIANT AT EVERY OFFSET BELOW `evZ(Q)`**);
* `haS_ix`, `haS_Z`, `haS_B`, `haS_b`, `haS_γ_iff`, `haS_self`, `haS_ext`.

No new axiom.  New definitions: `HaSStart`, `HaSInv`, `HaSTop`, `haSIdx`, `haSFamOf`, `haSExt`, `haSLimD`, `haSD`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ha

open Googology.Trans.PoR.InaccPsi.R2.Gz

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

/-- **The start of a gated stage `Bp`**: a system with index `Q` (bound `Q`), base gate below a base `x` iff `γ_P`
is, base reading `P(x)` above it, bound field `Zst`. -/
structure HaSStart (Bp : HaPB) (U0 : GzVD) : Prop where
  ix : U0.ix = Bp.Q
  γ : ∀ x, InE x → x < Om1 → (U0.γ < x ↔ Bp.γP < x)
  b : ∀ x, InE x → x < Om1 → Bp.γP < x → U0.b x = Bp.P x
  Z : ∀ x, InE x → x < Om1 → U0.Z x = Bp.Zst x

/-- **The invariant of a family below `λ`.** -/
structure HaSInv (Bp : HaPB) (U0 : GzVD) (l : Ordinal.{0}) (F : Ordinal.{0} → GzVD) : Prop where
  ix : ∀ μ, μ < l → (F μ).ix = Bp.Q + μ
  zero : 0 < l → F 0 = U0
  γ0 : 0 < l → ∀ x, InE x → x < Om1 → ((F 0).γ < x ↔ Bp.γP < x)
  succ : ∀ μ, μ + 1 < l → F (μ + 1) = (F μ).step
  N : ∀ μ, μ < l → ∀ x, InE x → x < Om1 → (F μ).Z x = Bp.Zst x
  cohR : ∀ β γ, β ≤ γ → γ < l → ∀ c x, c < (F β).B → (F γ).R c x = (F β).R c x
  cohg : ∀ β γ, β ≤ γ → γ < l → ∀ c, c < (F β).B → (F γ).g c = (F β).g c
  hb : ∀ μ, μ < l → ∀ x, InE x → x < Om1 → (F μ).γ < x → (F μ).b x = veblen 1 (Bp.P x + (F μ).R μ x)
  hγ : ∀ μ, μ < l → ∀ x, InE x → x < Om1 → ((F μ).γ < x ↔ max Bp.γP ((F μ).g μ) < x)

namespace HaSInv

variable {Bp : HaPB} {U0 : GzVD} {l : Ordinal.{0}} {F : Ordinal.{0} → GzVD} (H : HaSInv Bp U0 l F)
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

theorem congr {G : Ordinal.{0} → GzVD} (hFG : ∀ β, β < l → G β = F β) : HaSInv Bp U0 l G where
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

end HaSInv

theorem haSInv_zero (Bp : HaPB) (U0 : GzVD) (F : Ordinal.{0} → GzVD) : HaSInv Bp U0 0 F where
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

variable (Bp : HaPB) (U0 : GzVD)

/-- The first member that contains the index `λ` as a code (the index system of the union). -/
noncomputable def haSIdx (l : Ordinal.{0}) (F : Ordinal.{0} → GzVD) : Ordinal.{0} :=
  sInf {d | d < l ∧ l < (F d).B}

variable {Bp U0}

theorem haSIdx_spec {l : Ordinal.{0}} {F : Ordinal.{0} → GzVD} (hl : IsSuccLimit l) (hlZ : l < evZ Bp.Q)
    (H : HaSInv Bp U0 l F) : haSIdx l F < l ∧ l < (F (haSIdx l F)).B := by
  obtain ⟨d, hd, hld⟩ := gzq_cover Bp.Q_fix hl.bot_lt hlZ
  have h : l < (F d).B := by rw [H.B_eq hd]; exact hld
  exact csInf_mem (s := {d | d < l ∧ l < (F d).B}) ⟨d, hd, h⟩

variable (Bp U0)

/-- **The family over all `μ < λ`**, its indices read by the first member containing `λ`. -/
noncomputable def haSFamOf (l : Ordinal.{0}) (hl : IsSuccLimit l) (hlZ : l < evZ Bp.Q) (F : Ordinal.{0} → GzVD)
    (H : HaSInv Bp U0 l F) : HaSFam Bp where
  E := F (haSIdx l F)
  l := l
  F := F
  l_lim := hl
  l_lt := (haSIdx_spec hl hlZ H).2
  l_Z := hlZ
  EZ := H.N _ (haSIdx_spec hl hlZ H).1
  hN := H.N
  ix := H.ix
  γ0 := H.γ0 hl.bot_lt
  succ := H.succ
  cohR := H.cohR
  cohg := H.cohg
  hb := fun μ hμ x hx hx1 hγ => by
    obtain ⟨hd, hld⟩ := haSIdx_spec hl hlZ H
    rw [H.hb μ hμ x hx hx1 hγ, H.R_tr hμ hd (hμ.trans hld) (H.self_lt hμ (hμ.trans hlZ)) x]
  hγ := fun μ hμ x hx hx1 => by
    obtain ⟨hd, hld⟩ := haSIdx_spec hl hlZ H
    rw [H.hγ μ hμ x hx hx1, H.g_tr hμ hd (hμ.trans hld) (H.self_lt hμ (hμ.trans hlZ))]

/-- The family of the earlier values, extended by the start. -/
noncomputable def haSExt (l : Ordinal.{0}) (IH : ∀ β, β < l → GzVD) (β : Ordinal.{0}) : GzVD :=
  if h : β < l then IH β h else U0

open Classical in
/-- The limit step: the union over all smaller indices when the invariant holds. -/
noncomputable def haSLimD (l : Ordinal.{0}) (hl : IsSuccLimit l) (IH : ∀ β, β < l → GzVD) : GzVD :=
  if H : l < evZ Bp.Q ∧ HaSInv Bp U0 l (haSExt U0 l IH) then (haSFamOf Bp U0 l hl H.1 (haSExt U0 l IH) H.2).U
  else U0

/-- **THE RECURSION OF A STAGE**: the start `U0` at `0`, the step at `c+1`, the union over all `μ < λ` at a
limit `λ`; `haSD Bp U0 d` has the bound `ε_{Q+d}`. -/
noncomputable def haSD (ν : Ordinal.{0}) : GzVD :=
  Ordinal.limitRecOn (motive := fun _ => GzVD) ν U0 (fun _ D => D.step) (haSLimD Bp U0)

theorem haSD_zero : haSD Bp U0 0 = U0 := by
  unfold haSD; rw [Ordinal.limitRecOn_zero]

theorem haSD_succ (ν : Ordinal.{0}) : haSD Bp U0 (ν + 1) = (haSD Bp U0 ν).step := by
  unfold haSD; rw [Ordinal.limitRecOn_add_one]

theorem haSD_limit {l : Ordinal.{0}} (hl : IsSuccLimit l) :
    haSD Bp U0 l = haSLimD Bp U0 l hl (fun β _ => haSD Bp U0 β) := by
  unfold haSD; rw [Ordinal.limitRecOn_limit _ _ _ _ hl]

theorem haSExt_eq {l β : Ordinal.{0}} (h : β < l) : haSExt U0 l (fun β _ => haSD Bp U0 β) β = haSD Bp U0 β := by
  unfold haSExt; rw [dif_pos h]

end Fam

/-! ## The invariant at every index -/

/-- The new facts at the top `ν`. -/
structure HaSTop (Bp : HaPB) (U0 : GzVD) (ν : Ordinal.{0}) : Prop where
  ix : (haSD Bp U0 ν).ix = Bp.Q + ν
  N : ∀ x, InE x → x < Om1 → (haSD Bp U0 ν).Z x = Bp.Zst x
  cohR : ∀ β, β < ν → ∀ c x, c < (haSD Bp U0 β).B → (haSD Bp U0 ν).R c x = (haSD Bp U0 β).R c x
  cohg : ∀ β, β < ν → ∀ c, c < (haSD Bp U0 β).B → (haSD Bp U0 ν).g c = (haSD Bp U0 β).g c
  hb : ∀ x, InE x → x < Om1 → (haSD Bp U0 ν).γ < x →
    (haSD Bp U0 ν).b x = veblen 1 (Bp.P x + (haSD Bp U0 ν).R ν x)
  hγ : ∀ x, InE x → x < Om1 → ((haSD Bp U0 ν).γ < x ↔ max Bp.γP ((haSD Bp U0 ν).g ν) < x)

section Inv

variable {Bp : HaPB} {U0 : GzVD} (hU : HaSStart Bp U0)
include hU

theorem haSInv_succ {ν : Ordinal.{0}} (H : HaSInv Bp U0 ν (haSD Bp U0)) (T : HaSTop Bp U0 ν) :
    HaSInv Bp U0 (ν + 1) (haSD Bp U0) where
  ix := fun β h => by
    rcases (Order.lt_add_one_iff.1 h).lt_or_eq with h' | rfl
    · exact H.ix β h'
    · exact T.ix
  N := fun β h => by
    rcases (Order.lt_add_one_iff.1 h).lt_or_eq with h' | rfl
    · exact H.N β h'
    · exact T.N
  zero := fun _ => haSD_zero Bp U0
  γ0 := fun _ => by rw [haSD_zero]; exact hU.γ
  succ := fun μ _ => haSD_succ Bp U0 μ
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

theorem haSInv_lim {l : Ordinal.{0}} (IH : ∀ β, β < l → HaSInv Bp U0 (β + 1) (haSD Bp U0)) :
    HaSInv Bp U0 l (haSD Bp U0) where
  ix := fun β h => (IH β h).ix β (lt_add_one β)
  N := fun β h => (IH β h).N β (lt_add_one β)
  zero := fun _ => haSD_zero Bp U0
  γ0 := fun _ => by rw [haSD_zero]; exact hU.γ
  succ := fun μ _ => haSD_succ Bp U0 μ
  cohR := fun β γ hβγ h => (IH γ h).cohR β γ hβγ (lt_add_one γ)
  cohg := fun β γ hβγ h => (IH γ h).cohg β γ hβγ (lt_add_one γ)
  hb := fun β h => (IH β h).hb β (lt_add_one β)
  hγ := fun β h => (IH β h).hγ β (lt_add_one β)

theorem haSTop_zero : HaSTop Bp U0 0 where
  ix := by rw [haSD_zero, add_zero]; exact hU.ix
  N := fun x hx hx1 => by rw [haSD_zero]; exact hU.Z x hx hx1
  cohR := fun _ h => absurd h (not_lt.2 zero_le)
  cohg := fun _ h => absurd h (not_lt.2 zero_le)
  hb := fun x hx hx1 hγx => by
    rw [haSD_zero] at hγx
    have hP : Bp.γP < x := (hU.γ x hx hx1).1 hγx
    rw [haSD_zero, U0.R_zero, add_zero, hU.b x hx hx1 hP]
    exact (Bp.P_fix hx hx1 hP).symm
  hγ := fun x hx hx1 => by
    rw [haSD_zero, U0.g_zero, max_eq_left zero_le]; exact hU.γ x hx hx1

omit hU in
theorem haSTop_succ {ν : Ordinal.{0}} (hνZ : ν < evZ Bp.Q) (H : HaSInv Bp U0 (ν + 1) (haSD Bp U0)) :
    HaSTop Bp U0 (ν + 1) where
  ix := by
    rw [haSD_succ]
    show (haSD Bp U0 ν).step.ix = _
    rw [GzVD.step_ix, H.ix ν (lt_add_one ν), add_assoc]
  N := fun x hx hx1 => by
    rw [haSD_succ]
    show (haSD Bp U0 ν).step.Z x = _
    rw [GzVD.step_Z]; exact H.N ν (lt_add_one ν) x hx hx1
  cohR := fun β hβ c x hc => by
    have hβν : β ≤ ν := Order.lt_add_one_iff.1 hβ
    rw [haSD_succ]
    show (haSD Bp U0 ν).step.R c x = _
    rw [GzVD.step_R_low _ (hc.trans_le (H.B_le hβν (lt_add_one ν))) x]
    exact H.cohR β ν hβν (lt_add_one ν) c x hc
  cohg := fun β hβ c hc => by
    have hβν : β ≤ ν := Order.lt_add_one_iff.1 hβ
    rw [haSD_succ]
    show (haSD Bp U0 ν).step.g c = _
    rw [GzVD.step_g_low _ (hc.trans_le (H.B_le hβν (lt_add_one ν)))]
    exact H.cohg β ν hβν (lt_add_one ν) c hc
  hb := fun x hx hx1 hγx => by
    have hνB : ν < (haSD Bp U0 ν).B := H.self_lt (lt_add_one ν) hνZ
    have hν1B : ν + 1 < (haSD Bp U0 ν).B := (haSD Bp U0 ν).B_lim.add_one_lt hνB
    have hγ : (haSD Bp U0 ν).γ < x := by rw [haSD_succ] at hγx; exact hγx
    rw [haSD_succ]
    show (haSD Bp U0 ν).step.b x = veblen 1 (Bp.P x + (haSD Bp U0 ν).step.R (ν + 1) x)
    rw [GzVD.step_b, GzVD.step_R_low _ hν1B x, (haSD Bp U0 ν).R_succ, H.hb ν (lt_add_one ν) x hx hx1 hγ, go_eN_veb,
      add_assoc]
  hγ := fun x hx hx1 => by
    have hνB : ν < (haSD Bp U0 ν).B := H.self_lt (lt_add_one ν) hνZ
    have hν1B : ν + 1 < (haSD Bp U0 ν).B := (haSD Bp U0 ν).B_lim.add_one_lt hνB
    rw [haSD_succ]
    show (haSD Bp U0 ν).γ < x ↔ max Bp.γP ((haSD Bp U0 ν).step.g (ν + 1)) < x
    rw [GzVD.step_g_low _ hν1B, H.hγ ν (lt_add_one ν) x hx hx1, max_lt_iff, max_lt_iff]
    exact and_congr_right fun _ => ⟨fun h => (haSD Bp U0 ν).g_succ x (ev_isSuccLimit_of_inE hx) ν hν1B h,
      fun h => ((haSD Bp U0 ν).g_le_succ ν).trans_lt h⟩

omit hU in
theorem haSD_lim_eq {l : Ordinal.{0}} (hl : IsSuccLimit l) (hlZ : l < evZ Bp.Q) (H : HaSInv Bp U0 l (haSD Bp U0)) :
    haSD Bp U0 l = (haSFamOf Bp U0 l hl hlZ (haSExt U0 l fun β _ => haSD Bp U0 β)
      (H.congr fun β h => haSExt_eq Bp U0 h)).U := by
  rw [haSD_limit Bp U0 hl]; unfold haSLimD; rw [dif_pos ⟨hlZ, H.congr fun β h => haSExt_eq Bp U0 h⟩]

omit hU in
theorem haSTop_lim {l : Ordinal.{0}} (hl : IsSuccLimit l) (hlZ : l < evZ Bp.Q) (H : HaSInv Bp U0 l (haSD Bp U0)) :
    HaSTop Bp U0 l := by
  set Q := haSFamOf Bp U0 l hl hlZ (haSExt U0 l fun β _ => haSD Bp U0 β) (H.congr fun β h => haSExt_eq Bp U0 h)
    with hQ
  have e : haSD Bp U0 l = Q.U := haSD_lim_eq hl hlZ H
  have hF : ∀ β, β < l → Q.F β = haSD Bp U0 β := fun β h => haSExt_eq Bp U0 h
  have hl' : Q.l = l := rfl
  obtain ⟨hd, hld⟩ := haSIdx_spec hl hlZ (H.congr fun β h => haSExt_eq Bp U0 h)
  have hE : Q.E = Q.F (haSIdx l (haSExt U0 l fun β _ => haSD Bp U0 β)) := rfl
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
theorem haS_inv : ∀ ν : Ordinal.{0}, ν < evZ Bp.Q → HaSInv Bp U0 (ν + 1) (haSD Bp U0) := by
  intro ν
  induction ν using Ordinal.limitRecOn with
  | zero => intro _; exact haSInv_succ hU (haSInv_zero Bp U0 _) (haSTop_zero hU)
  | add_one μ ih =>
    intro hν
    have hμ : μ < evZ Bp.Q := (lt_add_one μ).trans hν
    have H := ih hμ
    exact haSInv_succ hU H (haSTop_succ hμ H)
  | limit l hl ih =>
    intro hν
    have H := haSInv_lim hU (fun β hβ => ih β hβ (hβ.trans hν))
    exact haSInv_succ hU H (haSTop_lim hl hν H)

end Inv

/-! ## The main facts -/

section Main

variable {Bp : HaPB} {U0 : GzVD} (hU : HaSStart Bp U0) {ν : Ordinal.{0}} (hν : ν < evZ Bp.Q)
include hU hν

theorem haS_ix : (haSD Bp U0 ν).ix = Bp.Q + ν := (haS_inv hU ν hν).ix ν (lt_add_one ν)

theorem haS_Z {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : (haSD Bp U0 ν).Z x = Bp.Zst x :=
  (haS_inv hU ν hν).N ν (lt_add_one ν) x hx hx1

/-- **The bound of `haSD Bp U0 ν` is `ε_{Q+ν}`.** -/
theorem haS_B : (haSD Bp U0 ν).B = veblen 1 (Bp.Q + ν) := (haS_inv hU ν hν).B_eq (lt_add_one ν)

/-- **The base reading of `haSD Bp U0 ν` is `φ(1, P(x) + ν(x))`** above its gate. -/
theorem haS_b {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγx : (haSD Bp U0 ν).γ < x) :
    (haSD Bp U0 ν).b x = veblen 1 (Bp.P x + (haSD Bp U0 ν).R ν x) :=
  (haS_inv hU ν hν).hb ν (lt_add_one ν) x hx hx1 hγx

/-- **The base gate of `haSD Bp U0 ν` lies below an `ε`-number `x` iff `γ_P` and the gate of the code `ν` do.** -/
theorem haS_γ_iff {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    (haSD Bp U0 ν).γ < x ↔ max Bp.γP ((haSD Bp U0 ν).g ν) < x :=
  (haS_inv hU ν hν).hγ ν (lt_add_one ν) x hx hx1

theorem haS_self : ν < (haSD Bp U0 ν).B := by rw [haS_B hU hν]; exact gzq_self_lt Bp.Q_fix hν

end Main

/-- **Later systems extend earlier ones** (readings and gates). -/
theorem haS_ext {Bp : HaPB} {U0 : GzVD} (hU : HaSStart Bp U0) {β γ : Ordinal.{0}} (hβγ : β ≤ γ) (hγ : γ < evZ Bp.Q) :
    (∀ c x, c < (haSD Bp U0 β).B → (haSD Bp U0 γ).R c x = (haSD Bp U0 β).R c x) ∧
    (∀ c, c < (haSD Bp U0 β).B → (haSD Bp U0 γ).g c = (haSD Bp U0 β).g c) :=
  ⟨(haS_inv hU γ hγ).cohR β γ hβγ (lt_add_one γ), (haS_inv hU γ hγ).cohg β γ hβγ (lt_add_one γ)⟩

end Googology.Trans.PoR.InaccPsi.R2.Ha
