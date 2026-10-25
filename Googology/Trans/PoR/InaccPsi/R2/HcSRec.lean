import Googology.Trans.PoR.InaccPsi.R2.HcS

/-!
# HcSRec: THE RECURSION OF A GATED STAGE: ALL OFFSETS IN `[Q, evZ(Q))`, FROM ANY START

(Textual copy of `Hb.HbSRec` for `Hc.HcVD`: bound fields `≤ B_x(x)` (`Hc.hcBR`) in place of `≤ B_ω(x)`;
the proofs are unchanged.)

`Ha.haSD` (a textual copy) for `Hc.HcVD` and a stage `Bp : Hb.HcPB`: from a start `U0` with `HcSStart Bp U0`
(index `Q`, base gate `γ < x ⇔
γ_P < x` at every base, base reading `P(x)` above it, bound field `Zst`), `hcSD Bp U0 d` (`d < evZ(Q)`) has the bound
`ε_{Q+d} = φ(1, Q + d)`: `U0` at `0`, the step at `d+1`, the union `Hc.HcSFam.U` at a limit (index read by the first
member containing it).  The invariant (`HcSInv`, `hcS_inv`): index `Q + μ`, bound field `Zst`, coherence, base reading
`φ(1, P(x) + μ(x))` above the base gate, `γ(hcSD μ) < x ⇔ max(γ_P, g(μ)) < x`.

* `HcSStart`, `HcSInv`, `hcSIdx`, `hcSFamOf`, `hcSExt`, `hcSLimD`, `hcSD` (**THE RECURSION OF A GATED STAGE**),
  `hcSD_zero`, `hcSD_succ`, `hcSD_limit`, `HcSTop`, `hcS_inv` (**THE INVARIANT AT EVERY OFFSET BELOW `evZ(Q)`**);
* `hcS_ix`, `hcS_Z`, `hcS_B`, `hcS_b`, `hcS_γ_iff`, `hcS_self`, `hcS_ext`.

No new axiom.  New definitions: `HcSStart`, `HcSInv`, `HcSTop`, `hcSIdx`, `hcSFamOf`, `hcSExt`, `hcSLimD`, `hcSD`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hc

open Googology.Trans.PoR.InaccPsi.R2.Hb

open Googology.Trans.PoR.InaccPsi.R2.Ha

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
structure HcSStart (Bp : HcPB) (U0 : HcVD) : Prop where
  ix : U0.ix = Bp.Q
  γ : ∀ x, InE x → x < Om1 → (U0.γ < x ↔ Bp.γP < x)
  b : ∀ x, InE x → x < Om1 → Bp.γP < x → U0.b x = Bp.P x
  Z : ∀ x, InE x → x < Om1 → U0.Z x = Bp.Zst x

/-- **The invariant of a family below `λ`.** -/
structure HcSInv (Bp : HcPB) (U0 : HcVD) (l : Ordinal.{0}) (F : Ordinal.{0} → HcVD) : Prop where
  ix : ∀ μ, μ < l → (F μ).ix = Bp.Q + μ
  zero : 0 < l → F 0 = U0
  γ0 : 0 < l → ∀ x, InE x → x < Om1 → ((F 0).γ < x ↔ Bp.γP < x)
  succ : ∀ μ, μ + 1 < l → F (μ + 1) = (F μ).step
  N : ∀ μ, μ < l → ∀ x, InE x → x < Om1 → (F μ).Z x = Bp.Zst x
  cohR : ∀ β γ, β ≤ γ → γ < l → ∀ c x, c < (F β).B → (F γ).R c x = (F β).R c x
  cohg : ∀ β γ, β ≤ γ → γ < l → ∀ c, c < (F β).B → (F γ).g c = (F β).g c
  hb : ∀ μ, μ < l → ∀ x, InE x → x < Om1 → (F μ).γ < x → (F μ).b x = veblen 1 (Bp.P x + (F μ).R μ x)
  hγ : ∀ μ, μ < l → ∀ x, InE x → x < Om1 → ((F μ).γ < x ↔ max Bp.γP ((F μ).g μ) < x)

namespace HcSInv

variable {Bp : HcPB} {U0 : HcVD} {l : Ordinal.{0}} {F : Ordinal.{0} → HcVD} (H : HcSInv Bp U0 l F)
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

theorem congr {G : Ordinal.{0} → HcVD} (hFG : ∀ β, β < l → G β = F β) : HcSInv Bp U0 l G where
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

end HcSInv

theorem hcSInv_zero (Bp : HcPB) (U0 : HcVD) (F : Ordinal.{0} → HcVD) : HcSInv Bp U0 0 F where
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

variable (Bp : HcPB) (U0 : HcVD)

/-- The first member that contains the index `λ` as a code (the index system of the union). -/
noncomputable def hcSIdx (l : Ordinal.{0}) (F : Ordinal.{0} → HcVD) : Ordinal.{0} :=
  sInf {d | d < l ∧ l < (F d).B}

variable {Bp U0}

theorem hcSIdx_spec {l : Ordinal.{0}} {F : Ordinal.{0} → HcVD} (hl : IsSuccLimit l) (hlZ : l < evZ Bp.Q)
    (H : HcSInv Bp U0 l F) : hcSIdx l F < l ∧ l < (F (hcSIdx l F)).B := by
  obtain ⟨d, hd, hld⟩ := gzq_cover Bp.Q_fix hl.bot_lt hlZ
  have h : l < (F d).B := by rw [H.B_eq hd]; exact hld
  exact csInf_mem (s := {d | d < l ∧ l < (F d).B}) ⟨d, hd, h⟩

variable (Bp U0)

/-- **The family over all `μ < λ`**, its indices read by the first member containing `λ`. -/
noncomputable def hcSFamOf (l : Ordinal.{0}) (hl : IsSuccLimit l) (hlZ : l < evZ Bp.Q) (F : Ordinal.{0} → HcVD)
    (H : HcSInv Bp U0 l F) : HcSFam Bp where
  E := F (hcSIdx l F)
  l := l
  F := F
  l_lim := hl
  l_lt := (hcSIdx_spec hl hlZ H).2
  l_Z := hlZ
  EZ := H.N _ (hcSIdx_spec hl hlZ H).1
  hN := H.N
  ix := H.ix
  γ0 := H.γ0 hl.bot_lt
  succ := H.succ
  cohR := H.cohR
  cohg := H.cohg
  hb := fun μ hμ x hx hx1 hγ => by
    obtain ⟨hd, hld⟩ := hcSIdx_spec hl hlZ H
    rw [H.hb μ hμ x hx hx1 hγ, H.R_tr hμ hd (hμ.trans hld) (H.self_lt hμ (hμ.trans hlZ)) x]
  hγ := fun μ hμ x hx hx1 => by
    obtain ⟨hd, hld⟩ := hcSIdx_spec hl hlZ H
    rw [H.hγ μ hμ x hx hx1, H.g_tr hμ hd (hμ.trans hld) (H.self_lt hμ (hμ.trans hlZ))]

/-- The family of the earlier values, extended by the start. -/
noncomputable def hcSExt (l : Ordinal.{0}) (IH : ∀ β, β < l → HcVD) (β : Ordinal.{0}) : HcVD :=
  if h : β < l then IH β h else U0

open Classical in
/-- The limit step: the union over all smaller indices when the invariant holds. -/
noncomputable def hcSLimD (l : Ordinal.{0}) (hl : IsSuccLimit l) (IH : ∀ β, β < l → HcVD) : HcVD :=
  if H : l < evZ Bp.Q ∧ HcSInv Bp U0 l (hcSExt U0 l IH) then (hcSFamOf Bp U0 l hl H.1 (hcSExt U0 l IH) H.2).U
  else U0

/-- **THE RECURSION OF A STAGE**: the start `U0` at `0`, the step at `c+1`, the union over all `μ < λ` at a
limit `λ`; `hcSD Bp U0 d` has the bound `ε_{Q+d}`. -/
noncomputable def hcSD (ν : Ordinal.{0}) : HcVD :=
  Ordinal.limitRecOn (motive := fun _ => HcVD) ν U0 (fun _ D => D.step) (hcSLimD Bp U0)

theorem hcSD_zero : hcSD Bp U0 0 = U0 := by
  unfold hcSD; rw [Ordinal.limitRecOn_zero]

theorem hcSD_succ (ν : Ordinal.{0}) : hcSD Bp U0 (ν + 1) = (hcSD Bp U0 ν).step := by
  unfold hcSD; rw [Ordinal.limitRecOn_add_one]

theorem hcSD_limit {l : Ordinal.{0}} (hl : IsSuccLimit l) :
    hcSD Bp U0 l = hcSLimD Bp U0 l hl (fun β _ => hcSD Bp U0 β) := by
  unfold hcSD; rw [Ordinal.limitRecOn_limit _ _ _ _ hl]

theorem hcSExt_eq {l β : Ordinal.{0}} (h : β < l) : hcSExt U0 l (fun β _ => hcSD Bp U0 β) β = hcSD Bp U0 β := by
  unfold hcSExt; rw [dif_pos h]

end Fam

/-! ## The invariant at every index -/

/-- The new facts at the top `ν`. -/
structure HcSTop (Bp : HcPB) (U0 : HcVD) (ν : Ordinal.{0}) : Prop where
  ix : (hcSD Bp U0 ν).ix = Bp.Q + ν
  N : ∀ x, InE x → x < Om1 → (hcSD Bp U0 ν).Z x = Bp.Zst x
  cohR : ∀ β, β < ν → ∀ c x, c < (hcSD Bp U0 β).B → (hcSD Bp U0 ν).R c x = (hcSD Bp U0 β).R c x
  cohg : ∀ β, β < ν → ∀ c, c < (hcSD Bp U0 β).B → (hcSD Bp U0 ν).g c = (hcSD Bp U0 β).g c
  hb : ∀ x, InE x → x < Om1 → (hcSD Bp U0 ν).γ < x →
    (hcSD Bp U0 ν).b x = veblen 1 (Bp.P x + (hcSD Bp U0 ν).R ν x)
  hγ : ∀ x, InE x → x < Om1 → ((hcSD Bp U0 ν).γ < x ↔ max Bp.γP ((hcSD Bp U0 ν).g ν) < x)

section Inv

variable {Bp : HcPB} {U0 : HcVD} (hU : HcSStart Bp U0)
include hU

theorem hcSInv_succ {ν : Ordinal.{0}} (H : HcSInv Bp U0 ν (hcSD Bp U0)) (T : HcSTop Bp U0 ν) :
    HcSInv Bp U0 (ν + 1) (hcSD Bp U0) where
  ix := fun β h => by
    rcases (Order.lt_add_one_iff.1 h).lt_or_eq with h' | rfl
    · exact H.ix β h'
    · exact T.ix
  N := fun β h => by
    rcases (Order.lt_add_one_iff.1 h).lt_or_eq with h' | rfl
    · exact H.N β h'
    · exact T.N
  zero := fun _ => hcSD_zero Bp U0
  γ0 := fun _ => by rw [hcSD_zero]; exact hU.γ
  succ := fun μ _ => hcSD_succ Bp U0 μ
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

theorem hcSInv_lim {l : Ordinal.{0}} (IH : ∀ β, β < l → HcSInv Bp U0 (β + 1) (hcSD Bp U0)) :
    HcSInv Bp U0 l (hcSD Bp U0) where
  ix := fun β h => (IH β h).ix β (lt_add_one β)
  N := fun β h => (IH β h).N β (lt_add_one β)
  zero := fun _ => hcSD_zero Bp U0
  γ0 := fun _ => by rw [hcSD_zero]; exact hU.γ
  succ := fun μ _ => hcSD_succ Bp U0 μ
  cohR := fun β γ hβγ h => (IH γ h).cohR β γ hβγ (lt_add_one γ)
  cohg := fun β γ hβγ h => (IH γ h).cohg β γ hβγ (lt_add_one γ)
  hb := fun β h => (IH β h).hb β (lt_add_one β)
  hγ := fun β h => (IH β h).hγ β (lt_add_one β)

theorem hcSTop_zero : HcSTop Bp U0 0 where
  ix := by rw [hcSD_zero, add_zero]; exact hU.ix
  N := fun x hx hx1 => by rw [hcSD_zero]; exact hU.Z x hx hx1
  cohR := fun _ h => absurd h (not_lt.2 zero_le)
  cohg := fun _ h => absurd h (not_lt.2 zero_le)
  hb := fun x hx hx1 hγx => by
    rw [hcSD_zero] at hγx
    have hP : Bp.γP < x := (hU.γ x hx hx1).1 hγx
    rw [hcSD_zero, U0.R_zero, add_zero, hU.b x hx hx1 hP]
    exact (Bp.P_fix hx hx1 hP).symm
  hγ := fun x hx hx1 => by
    rw [hcSD_zero, U0.g_zero, max_eq_left zero_le]; exact hU.γ x hx hx1

omit hU in
theorem hcSTop_succ {ν : Ordinal.{0}} (hνZ : ν < evZ Bp.Q) (H : HcSInv Bp U0 (ν + 1) (hcSD Bp U0)) :
    HcSTop Bp U0 (ν + 1) where
  ix := by
    rw [hcSD_succ]
    show (hcSD Bp U0 ν).step.ix = _
    rw [HcVD.step_ix, H.ix ν (lt_add_one ν), add_assoc]
  N := fun x hx hx1 => by
    rw [hcSD_succ]
    show (hcSD Bp U0 ν).step.Z x = _
    rw [HcVD.step_Z]; exact H.N ν (lt_add_one ν) x hx hx1
  cohR := fun β hβ c x hc => by
    have hβν : β ≤ ν := Order.lt_add_one_iff.1 hβ
    rw [hcSD_succ]
    show (hcSD Bp U0 ν).step.R c x = _
    rw [HcVD.step_R_low _ (hc.trans_le (H.B_le hβν (lt_add_one ν))) x]
    exact H.cohR β ν hβν (lt_add_one ν) c x hc
  cohg := fun β hβ c hc => by
    have hβν : β ≤ ν := Order.lt_add_one_iff.1 hβ
    rw [hcSD_succ]
    show (hcSD Bp U0 ν).step.g c = _
    rw [HcVD.step_g_low _ (hc.trans_le (H.B_le hβν (lt_add_one ν)))]
    exact H.cohg β ν hβν (lt_add_one ν) c hc
  hb := fun x hx hx1 hγx => by
    have hνB : ν < (hcSD Bp U0 ν).B := H.self_lt (lt_add_one ν) hνZ
    have hν1B : ν + 1 < (hcSD Bp U0 ν).B := (hcSD Bp U0 ν).B_lim.add_one_lt hνB
    have hγ : (hcSD Bp U0 ν).γ < x := by rw [hcSD_succ] at hγx; exact hγx
    rw [hcSD_succ]
    show (hcSD Bp U0 ν).step.b x = veblen 1 (Bp.P x + (hcSD Bp U0 ν).step.R (ν + 1) x)
    rw [HcVD.step_b, HcVD.step_R_low _ hν1B x, (hcSD Bp U0 ν).R_succ, H.hb ν (lt_add_one ν) x hx hx1 hγ, go_eN_veb,
      add_assoc]
  hγ := fun x hx hx1 => by
    have hνB : ν < (hcSD Bp U0 ν).B := H.self_lt (lt_add_one ν) hνZ
    have hν1B : ν + 1 < (hcSD Bp U0 ν).B := (hcSD Bp U0 ν).B_lim.add_one_lt hνB
    rw [hcSD_succ]
    show (hcSD Bp U0 ν).γ < x ↔ max Bp.γP ((hcSD Bp U0 ν).step.g (ν + 1)) < x
    rw [HcVD.step_g_low _ hν1B, H.hγ ν (lt_add_one ν) x hx hx1, max_lt_iff, max_lt_iff]
    exact and_congr_right fun _ => ⟨fun h => (hcSD Bp U0 ν).g_succ x (ev_isSuccLimit_of_inE hx) ν hν1B h,
      fun h => ((hcSD Bp U0 ν).g_le_succ ν).trans_lt h⟩

omit hU in
theorem hcSD_lim_eq {l : Ordinal.{0}} (hl : IsSuccLimit l) (hlZ : l < evZ Bp.Q) (H : HcSInv Bp U0 l (hcSD Bp U0)) :
    hcSD Bp U0 l = (hcSFamOf Bp U0 l hl hlZ (hcSExt U0 l fun β _ => hcSD Bp U0 β)
      (H.congr fun β h => hcSExt_eq Bp U0 h)).U := by
  rw [hcSD_limit Bp U0 hl]; unfold hcSLimD; rw [dif_pos ⟨hlZ, H.congr fun β h => hcSExt_eq Bp U0 h⟩]

omit hU in
theorem hcSTop_lim {l : Ordinal.{0}} (hl : IsSuccLimit l) (hlZ : l < evZ Bp.Q) (H : HcSInv Bp U0 l (hcSD Bp U0)) :
    HcSTop Bp U0 l := by
  set Q := hcSFamOf Bp U0 l hl hlZ (hcSExt U0 l fun β _ => hcSD Bp U0 β) (H.congr fun β h => hcSExt_eq Bp U0 h)
    with hQ
  have e : hcSD Bp U0 l = Q.U := hcSD_lim_eq hl hlZ H
  have hF : ∀ β, β < l → Q.F β = hcSD Bp U0 β := fun β h => hcSExt_eq Bp U0 h
  have hl' : Q.l = l := rfl
  obtain ⟨hd, hld⟩ := hcSIdx_spec hl hlZ (H.congr fun β h => hcSExt_eq Bp U0 h)
  have hE : Q.E = Q.F (hcSIdx l (hcSExt U0 l fun β _ => hcSD Bp U0 β)) := rfl
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
theorem hcS_inv : ∀ ν : Ordinal.{0}, ν < evZ Bp.Q → HcSInv Bp U0 (ν + 1) (hcSD Bp U0) := by
  intro ν
  induction ν using Ordinal.limitRecOn with
  | zero => intro _; exact hcSInv_succ hU (hcSInv_zero Bp U0 _) (hcSTop_zero hU)
  | add_one μ ih =>
    intro hν
    have hμ : μ < evZ Bp.Q := (lt_add_one μ).trans hν
    have H := ih hμ
    exact hcSInv_succ hU H (hcSTop_succ hμ H)
  | limit l hl ih =>
    intro hν
    have H := hcSInv_lim hU (fun β hβ => ih β hβ (hβ.trans hν))
    exact hcSInv_succ hU H (hcSTop_lim hl hν H)

end Inv

/-! ## The main facts -/

section Main

variable {Bp : HcPB} {U0 : HcVD} (hU : HcSStart Bp U0) {ν : Ordinal.{0}} (hν : ν < evZ Bp.Q)
include hU hν

theorem hcS_ix : (hcSD Bp U0 ν).ix = Bp.Q + ν := (hcS_inv hU ν hν).ix ν (lt_add_one ν)

theorem hcS_Z {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : (hcSD Bp U0 ν).Z x = Bp.Zst x :=
  (hcS_inv hU ν hν).N ν (lt_add_one ν) x hx hx1

/-- **The bound of `hcSD Bp U0 ν` is `ε_{Q+ν}`.** -/
theorem hcS_B : (hcSD Bp U0 ν).B = veblen 1 (Bp.Q + ν) := (hcS_inv hU ν hν).B_eq (lt_add_one ν)

/-- **The base reading of `hcSD Bp U0 ν` is `φ(1, P(x) + ν(x))`** above its gate. -/
theorem hcS_b {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγx : (hcSD Bp U0 ν).γ < x) :
    (hcSD Bp U0 ν).b x = veblen 1 (Bp.P x + (hcSD Bp U0 ν).R ν x) :=
  (hcS_inv hU ν hν).hb ν (lt_add_one ν) x hx hx1 hγx

/-- **The base gate of `hcSD Bp U0 ν` lies below an `ε`-number `x` iff `γ_P` and the gate of the code `ν` do.** -/
theorem hcS_γ_iff {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    (hcSD Bp U0 ν).γ < x ↔ max Bp.γP ((hcSD Bp U0 ν).g ν) < x :=
  (hcS_inv hU ν hν).hγ ν (lt_add_one ν) x hx hx1

theorem hcS_self : ν < (hcSD Bp U0 ν).B := by rw [hcS_B hU hν]; exact gzq_self_lt Bp.Q_fix hν

end Main

/-- **Later systems extend earlier ones** (readings and gates). -/
theorem hcS_ext {Bp : HcPB} {U0 : HcVD} (hU : HcSStart Bp U0) {β γ : Ordinal.{0}} (hβγ : β ≤ γ) (hγ : γ < evZ Bp.Q) :
    (∀ c x, c < (hcSD Bp U0 β).B → (hcSD Bp U0 γ).R c x = (hcSD Bp U0 β).R c x) ∧
    (∀ c, c < (hcSD Bp U0 β).B → (hcSD Bp U0 γ).g c = (hcSD Bp U0 β).g c) :=
  ⟨(hcS_inv hU γ hγ).cohR β γ hβγ (lt_add_one γ), (hcS_inv hU γ hγ).cohg β γ hβγ (lt_add_one γ)⟩

end Googology.Trans.PoR.InaccPsi.R2.Hc
