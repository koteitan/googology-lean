import Googology.Trans.PoR.InaccPsi.R2.GvSeq

/-!
# THE RECURSION OVER EVERY COUNTABLE CONSTANT FROM ANY START `D₀` (index `i₀ = P + j`, `Ω₁ ∣ P`)

Port of `Gs.gsD` (`R2.GsRec`) to any start: a gated digit system `D₀` with base gate `0`, index `i₀ = P + j`
(`Ω₁ ∣ P`, `Ω₁ ≤ P`, `j < Ω₁`), base reading `φ(1, i(x))` and offset `a(x)` at every base (`GvSt`).  The recursion
`gvRD St ν` (`ν < Ω₁`) is `D₀` at `0`, the step at `ν+1`, and at a limit `λ` the gated union of `GvSeq` (gate `λ`).
The invariant (`GvInv`: index `i₀ + β`, base `φ(1, i(x) + β)` above `β`, offset `a(x) + gpOff β`, gate `≤ β`,
coherence) holds at every `ν < Ω₁` (`gvR_inv`); the gate of a limit system is its index and `ν = γ_ν + n`
(`gvR_γ_lim`, `gvR_γ_fin`); a code with gate below an `ε`-number `σ` lies in a system `gvRD St μ`, `μ < σ`
(`gvR_small`).  The proofs are those of `R2.GsRec`, `R2.GsWall` and `Gv.gv_small`.

* `GvSt`, `GvSt.a_lt`, `GvSt.a_pi`, `GvSt.i0_lt`; `GvInv`, `gvChain`, `gvExt`, `gvLimD`, `gvRD` (**THE RECURSION**);
* `gvR_inv`, `gvR_B`, `gvR_b`, `gvR_ba`, `gvR_γ`, `gvR_ext`, `gvR_B_lt`, `gvR_lim_cof`, `gvR_γ_lim`, `gvR_γ_fin`,
  `gvR_lt_of_γ`, `gvR_small`.

No new axiom.  New definitions: `GvSt`, `GvInv`, `GvTop`, `gvChain`, `gvExt`, `gvLimD`, `gvRD`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gv

open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gj
  Googology.Trans.PoR.InaccPsi.R2.Gi Googology.Trans.PoR.InaccPsi.R2.Gn Googology.Trans.PoR.InaccPsi.R2.Go
  Googology.Trans.PoR.InaccPsi.R2.Gp
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

/-- **A start of the recursion**: a gated digit system with base gate `0`, index `i₀ = P + j` (`Ω₁ ∣ P`), base
`φ(1, i(x))` and offset `a(x)` at every base. -/
structure GvSt where
  D0 : GsD
  i0 : Ordinal.{0}
  i : Ordinal.{0} → Ordinal.{0}
  a : Ordinal.{0} → Ordinal.{0}
  P0 : Ordinal.{0}
  j0 : Ordinal.{0}
  γ0 : D0.γ = 0
  ix0 : D0.ix = i0
  b0 : ∀ x, InE x → x < Om1 → D0.b x = veblen 1 (i x)
  ba0 : ∀ x, D0.ba x = a x
  i0_eq : i0 = P0 + j0
  P0_dvd : Om 1 ∣ P0
  P0_ge : Om 1 ≤ P0
  j0_lt : j0 < Om 1
  i_big : ∀ x, InE x → x < Om1 → lgG x ≤ veblen 1 (i x)

namespace GvSt

variable (St : GvSt)

theorem γ_lt {x : Ordinal.{0}} (hx : InE x) : St.D0.γ < x := by rw [St.γ0]; exact hx.pos

theorem a_lt {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : St.a x < gq 1 x := by
  rw [← St.ba0]; exact St.D0.ba_lt x hx hx1 (St.γ_lt hx)

theorem a_pi {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) : St.a ρ ∈ TB ρ σ ∧ pi σ ρ (St.a ρ) = St.a σ := by
  rw [← St.ba0, ← St.ba0]; exact St.D0.ba_pi σ ρ hB (St.γ_lt hB.1)

theorem i0_lt : St.i0 < gcG 1 := by
  have h := St.D0.B_lt1
  rw [St.D0.B_ix, St.ix0] at h
  exact (right_le_veblen 1 _).trans_lt h

theorem i0_mem {S : InaccSeq.{0}} {a b : Ordinal.{0}} (ha : 0 < a) (hb : 0 < b) : St.i0 ∈ S.CSet a b := by
  rw [← St.ix0]; exact St.D0.ix_mem S a b ha (by rw [St.γ0]; exact hb)

end GvSt

/-! ## The invariant -/

/-- **The invariant of a family below `λ`** over the start `St`. -/
structure GvInv (St : GvSt) (l : Ordinal.{0}) (F : Ordinal.{0} → GsD) : Prop where
  ix : ∀ β, β < l → (F β).ix = St.i0 + β
  b : ∀ β, β < l → ∀ x, InE x → x < Om1 → β < x → (F β).b x = veblen 1 (St.i x + β)
  ba : ∀ β, β < l → ∀ x, (F β).ba x = St.a x + gpOff β
  γ : ∀ β, β < l → (F β).γ ≤ β
  cohR : ∀ β γ, β ≤ γ → γ < l → ∀ c x, c < (F β).B → (F γ).R c x = (F β).R c x
  cohg : ∀ β γ, β ≤ γ → γ < l → ∀ c, c < (F β).B → (F γ).g c = (F β).g c
  cf : ∀ β γ, β < γ → γ < l → (F γ).g (F β).B ≤ max β ε₀

namespace GvInv

variable {St : GvSt} {l : Ordinal.{0}} {F : Ordinal.{0} → GsD} (H : GvInv St l F)
include H

theorem B_eq {β : Ordinal.{0}} (h : β < l) : (F β).B = veblen 1 (St.i0 + β) := by
  rw [(F β).B_ix, H.ix β h]

theorem B_lt {β γ : Ordinal.{0}} (hβγ : β < γ) (h : γ < l) : (F β).B < (F γ).B := by
  rw [H.B_eq (hβγ.trans h), H.B_eq h]
  exact (isNormal_veblen 1).strictMono ((add_lt_add_iff_left _).2 hβγ)

theorem B_le {β γ : Ordinal.{0}} (hβγ : β ≤ γ) (h : γ < l) : (F β).B ≤ (F γ).B := by
  rcases hβγ.lt_or_eq with h' | rfl
  · exact (H.B_lt h' h).le
  · exact le_rfl

theorem congr {G : Ordinal.{0} → GsD} (hFG : ∀ β, β < l → G β = F β) : GvInv St l G where
  ix := fun β h => by rw [hFG β h]; exact H.ix β h
  b := fun β h x hx hx1 => by rw [hFG β h]; exact H.b β h x hx hx1
  ba := fun β h x => by rw [hFG β h]; exact H.ba β h x
  γ := fun β h => by rw [hFG β h]; exact H.γ β h
  cohR := fun β γ hβγ h c x hc => by
    rw [hFG β (lt_of_le_of_lt hβγ h)] at hc ⊢
    rw [hFG γ h]; exact H.cohR β γ hβγ h c x hc
  cohg := fun β γ hβγ h c hc => by
    rw [hFG β (lt_of_le_of_lt hβγ h)] at hc ⊢
    rw [hFG γ h]; exact H.cohg β γ hβγ h c hc
  cf := fun β γ hβγ h => by rw [hFG β (hβγ.trans h), hFG γ h]; exact H.cf β γ hβγ h

end GvInv

theorem gvInv_zero (St : GvSt) (F : Ordinal.{0} → GsD) : GvInv St 0 F where
  ix := fun _ h => absurd h (not_lt.2 zero_le)
  b := fun _ h => absurd h (not_lt.2 zero_le)
  ba := fun _ h => absurd h (not_lt.2 zero_le)
  γ := fun _ h => absurd h (not_lt.2 zero_le)
  cohR := fun _ _ _ h => absurd h (not_lt.2 zero_le)
  cohg := fun _ _ _ h => absurd h (not_lt.2 zero_le)
  cf := fun _ _ _ h => absurd h (not_lt.2 zero_le)

/-! ## The union at a limit -/

/-- **The sequence at a limit `λ < Ω₁`**: the systems `F (gqFs λ k)`, base gate `λ`. -/
noncomputable def gvChain (St : GvSt) (l : Ordinal.{0}) (hl : IsSuccLimit l) (hlK : l < Om1)
    (F : Ordinal.{0} → GsD) (H : GvInv St l F) : GvSeq where
  D := fun k => F (gqFs l k)
  ix0 := St.i0
  i := St.i
  a := St.a
  δ := gqFs l
  s := fun k => gpOff (gqFs l k)
  Δ := l
  T := l
  γω := l
  hix := fun k => H.ix _ (gqFs_lt hl hlK k)
  hb := fun k x hx hx1 hlx => H.b _ (gqFs_lt hl hlK k) x hx hx1 ((gqFs_lt hl hlK k).trans hlx)
  hba := fun k x => H.ba _ (gqFs_lt hl hlK k) x
  coh_R := fun k c x hc => H.cohR _ _ (gqFs_mono hl hlK k).le
    (gqFs_lt hl hlK (k + 1)) c x hc
  coh_g := fun k c hc => H.cohg _ _ (gqFs_mono hl hlK k).le
    (gqFs_lt hl hlK (k + 1)) c hc
  cf_g := fun k => (H.cf _ _ (gqFs_mono hl hlK k) (gqFs_lt hl hlK (k + 1))).trans
    (max_le_max (gqFs_lt hl hlK k).le le_rfl)
  γ_le := fun k => (H.γ _ (gqFs_lt hl hlK k)).trans (gqFs_lt hl hlK k).le
  γω_lt := hlK
  γω_le := le_rfl
  Δ_le := le_rfl
  T_le := le_rfl
  δ_mono := gqFs_mono hl hlK
  δ_lt := gqFs_lt hl hlK
  δ_cof := gqFs_cof hl hlK
  Δ_lim := hl
  Δ_lt := hlK
  s_lt := fun k => gpOff_lt hl (gqFs_lt hl hlK k)
  s_cof := fun t ht => (gqFs_cof hl hlK t ht).imp fun _ hk => hk.trans_le (le_gpOff _)
  ix_mem := fun _ _ _ ha hlb => CSet.add_mem (St.i0_mem ha (lt_of_le_of_lt zero_le hlb)) (CSet.of_lt hlb)
  ix0_lt := St.i0_lt
  P0 := St.P0
  j0 := St.j0
  ix0_eq := St.i0_eq
  P0_dvd := St.P0_dvd
  P0_ge := St.P0_ge
  j0_lt := St.j0_lt
  a_lt := fun _ hx hx1 => St.a_lt hx hx1
  a_pi := fun _ _ hB _ => St.a_pi hB
  i_big := St.i_big

/-- The family of the earlier values, extended by the start. -/
noncomputable def gvExt (St : GvSt) (l : Ordinal.{0}) (IH : ∀ β, β < l → GsD) (β : Ordinal.{0}) : GsD :=
  if h : β < l then IH β h else St.D0

open Classical in
/-- The limit step: the gated union when the invariant holds (it does below `Ω₁`, `gvR_inv`). -/
noncomputable def gvLimD (St : GvSt) (l : Ordinal.{0}) (hl : IsSuccLimit l) (IH : ∀ β, β < l → GsD) : GsD :=
  if H : l < Om1 ∧ GvInv St l (gvExt St l IH) then (gvChain St l hl H.1 (gvExt St l IH) H.2).toCh.lim else St.D0

/-- **THE RECURSION FROM `St`**: `D₀` at `0`, the step at `ν+1`, the gated union at limits. -/
noncomputable def gvRD (St : GvSt) (ν : Ordinal.{0}) : GsD :=
  Ordinal.limitRecOn (motive := fun _ => GsD) ν St.D0 (fun _ D => D.step) (gvLimD St)

section Rec

variable (St : GvSt)

theorem gvRD_zero : gvRD St 0 = St.D0 := by
  unfold gvRD; rw [Ordinal.limitRecOn_zero]

theorem gvRD_succ (ν : Ordinal.{0}) : gvRD St (ν + 1) = (gvRD St ν).step := by
  unfold gvRD; rw [Ordinal.limitRecOn_add_one]

theorem gvRD_limit {l : Ordinal.{0}} (hl : IsSuccLimit l) :
    gvRD St l = gvLimD St l hl (fun β _ => gvRD St β) := by
  unfold gvRD; rw [Ordinal.limitRecOn_limit _ _ _ _ hl]

theorem gvExt_eq {l β : Ordinal.{0}} (h : β < l) : gvExt St l (fun β _ => gvRD St β) β = gvRD St β := by
  unfold gvExt; rw [dif_pos h]

/-- The new facts at the top `ν`. -/
structure GvTop (ν : Ordinal.{0}) : Prop where
  ix : (gvRD St ν).ix = St.i0 + ν
  b : ∀ x, InE x → x < Om1 → ν < x → (gvRD St ν).b x = veblen 1 (St.i x + ν)
  ba : ∀ x, (gvRD St ν).ba x = St.a x + gpOff ν
  γ : (gvRD St ν).γ ≤ ν
  cohR : ∀ β, β < ν → ∀ c x, c < (gvRD St β).B → (gvRD St ν).R c x = (gvRD St β).R c x
  cohg : ∀ β, β < ν → ∀ c, c < (gvRD St β).B → (gvRD St ν).g c = (gvRD St β).g c
  cf : ∀ β, β < ν → (gvRD St ν).g (gvRD St β).B ≤ max β ε₀

theorem gvInv_succ {ν : Ordinal.{0}} (H : GvInv St ν (gvRD St)) (T : GvTop St ν) : GvInv St (ν + 1) (gvRD St) where
  ix := fun β h => by
    rcases (Order.lt_add_one_iff.1 h).lt_or_eq with h' | rfl
    · exact H.ix β h'
    · exact T.ix
  b := fun β h => by
    rcases (Order.lt_add_one_iff.1 h).lt_or_eq with h' | rfl
    · exact H.b β h'
    · exact T.b
  ba := fun β h => by
    rcases (Order.lt_add_one_iff.1 h).lt_or_eq with h' | rfl
    · exact H.ba β h'
    · exact T.ba
  γ := fun β h => by
    rcases (Order.lt_add_one_iff.1 h).lt_or_eq with h' | rfl
    · exact H.γ β h'
    · exact T.γ
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
  cf := fun β γ hβγ h => by
    rcases (Order.lt_add_one_iff.1 h).lt_or_eq with h' | rfl
    · exact H.cf β γ hβγ h'
    · exact T.cf β hβγ

theorem gvInv_lim {l : Ordinal.{0}} (IH : ∀ β, β < l → GvInv St (β + 1) (gvRD St)) : GvInv St l (gvRD St) where
  ix := fun β h => (IH β h).ix β (lt_add_one β)
  b := fun β h => (IH β h).b β (lt_add_one β)
  ba := fun β h => (IH β h).ba β (lt_add_one β)
  γ := fun β h => (IH β h).γ β (lt_add_one β)
  cohR := fun β γ hβγ h => (IH γ h).cohR β γ hβγ (lt_add_one γ)
  cohg := fun β γ hβγ h => (IH γ h).cohg β γ hβγ (lt_add_one γ)
  cf := fun β γ hβγ h => (IH γ h).cf β γ hβγ (lt_add_one γ)

theorem gvTop_zero : GvTop St 0 where
  ix := by rw [gvRD_zero, add_zero]; exact St.ix0
  b := fun x hx hx1 _ => by rw [gvRD_zero, add_zero]; exact St.b0 x hx hx1
  ba := fun x => by rw [gvRD_zero, gpOff_zero, add_zero]; exact St.ba0 x
  γ := by rw [gvRD_zero, St.γ0]
  cohR := fun _ h => absurd h (not_lt.2 zero_le)
  cohg := fun _ h => absurd h (not_lt.2 zero_le)
  cf := fun _ h => absurd h (not_lt.2 zero_le)

theorem gvTop_succ {ν : Ordinal.{0}} (H : GvInv St (ν + 1) (gvRD St)) : GvTop St (ν + 1) where
  ix := by
    rw [gvRD_succ, GsD.step_ix, H.ix ν (lt_add_one ν), add_assoc]
  b := fun x hx hx1 hνx => by
    rw [gvRD_succ, GsD.step_b, H.b ν (lt_add_one ν) x hx hx1 ((lt_add_one ν).trans hνx), go_eN_veb, add_assoc]
  ba := fun x => by
    rw [gvRD_succ, GsD.step_ba, H.ba ν (lt_add_one ν) x, gpOff_succ, add_assoc]
  γ := by rw [gvRD_succ, GsD.step_γ]; exact (H.γ ν (lt_add_one ν)).trans le_self_add
  cohR := fun β hβ c x hc => by
    have hβν : β ≤ ν := Order.lt_add_one_iff.1 hβ
    rw [gvRD_succ, GsD.step_R_low _ (hc.trans_le (H.B_le hβν (lt_add_one ν))) x]
    exact H.cohR β ν hβν (lt_add_one ν) c x hc
  cohg := fun β hβ c hc => by
    have hβν : β ≤ ν := Order.lt_add_one_iff.1 hβ
    rw [gvRD_succ, GsD.step_g_low _ (hc.trans_le (H.B_le hβν (lt_add_one ν)))]
    exact H.cohg β ν hβν (lt_add_one ν) c hc
  cf := fun β hβ => by
    rcases (Order.lt_add_one_iff.1 hβ).lt_or_eq with h | rfl
    · rw [gvRD_succ, GsD.step_g_low _ (H.B_lt h (lt_add_one ν))]
      exact H.cf β ν h (lt_add_one ν)
    · rw [gvRD_succ, GsD.step_g_B]
      exact (H.γ β (lt_add_one β)).trans (le_max_left _ _)

theorem gvRD_lim_eq {l : Ordinal.{0}} (hl : IsSuccLimit l) (hlK : l < Om1) (H : GvInv St l (gvRD St)) :
    ∃ Q : GvSeq, Q = gvChain St l hl hlK (gvExt St l fun β _ => gvRD St β) (H.congr fun β h => gvExt_eq St h) ∧
      gvRD St l = Q.toCh.lim := by
  refine ⟨_, rfl, ?_⟩
  rw [gvRD_limit St hl]; unfold gvLimD; rw [dif_pos ⟨hlK, H.congr fun β h => gvExt_eq St h⟩]

theorem gvTop_lim {l : Ordinal.{0}} (hl : IsSuccLimit l) (hlK : l < Om1) (H : GvInv St l (gvRD St)) :
    GvTop St l := by
  have hl1 : l < Om1 := hlK
  obtain ⟨Q, hQ, e⟩ := gvRD_lim_eq St hl hlK H
  have hD : ∀ k, Q.toCh.D k = gvRD St (gqFs l k) := fun k => by
    rw [hQ]; exact gvExt_eq St (gqFs_lt hl hl1 k)
  refine ⟨?_, fun x hx hx1 hlx => ?_, fun x => ?_, ?_, fun β hβ c x hc => ?_, fun β hβ c hc => ?_, fun β hβ => ?_⟩
  · rw [e, Q.toCh_lim_ix, hQ]; rfl
  · rw [e, Q.toCh_lim_b hx hx1 (by rw [hQ]; exact hlx), hQ]; rfl
  · rw [e, Q.toCh_lim_ba, gpOff_lim hl, hQ]; exact add_assoc _ _ _
  · rw [e, Q.toCh_lim_γ, hQ]; exact le_rfl
  · obtain ⟨k, hk⟩ := gqFs_cof hl hl1 β hβ
    have hc' : c < (Q.toCh.D k).B := by rw [hD]; exact hc.trans (H.B_lt hk (gqFs_lt hl hl1 k))
    rw [e, Q.toCh.lim_R hc' x, hD]
    exact H.cohR β _ hk.le (gqFs_lt hl hl1 k) c x hc
  · obtain ⟨k, hk⟩ := gqFs_cof hl hl1 β hβ
    have hc' : c < (Q.toCh.D k).B := by rw [hD]; exact hc.trans (H.B_lt hk (gqFs_lt hl hl1 k))
    rw [e, Q.toCh.lim_g hc', hD]
    exact H.cohg β _ hk.le (gqFs_lt hl hl1 k) c hc
  · obtain ⟨k, hk⟩ := gqFs_cof hl hl1 β hβ
    have hc' : (gvRD St β).B < (Q.toCh.D k).B := by rw [hD]; exact H.B_lt hk (gqFs_lt hl hl1 k)
    rw [e, Q.toCh.lim_g hc', hD]
    exact H.cf β _ hk (gqFs_lt hl hl1 k)

/-- **THE INVARIANT AT EVERY `ν < Ω₁`.** -/
theorem gvR_inv : ∀ ν : Ordinal.{0}, ν < Om1 → GvInv St (ν + 1) (gvRD St) := by
  intro ν
  induction ν using Ordinal.limitRecOn with
  | zero => intro _; exact gvInv_succ St (gvInv_zero St _) (gvTop_zero St)
  | add_one μ ih =>
    intro hν
    have H := ih ((lt_add_one μ).trans hν)
    exact gvInv_succ St H (gvTop_succ St H)
  | limit l hl ih =>
    intro hν
    have H := gvInv_lim St (fun β hβ => ih β hβ (hβ.trans hν))
    exact gvInv_succ St H (gvTop_lim St hl hν H)

section Main

variable {St} {ν : Ordinal.{0}} (hν : ν < Om1)
include hν

theorem gvR_B : (gvRD St ν).B = veblen 1 (St.i0 + ν) := (gvR_inv St ν hν).B_eq (lt_add_one ν)

theorem gvR_b {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hνx : ν < x) :
    (gvRD St ν).b x = veblen 1 (St.i x + ν) :=
  (gvR_inv St ν hν).b ν (lt_add_one ν) x hx hx1 hνx

theorem gvR_ba (x : Ordinal.{0}) : (gvRD St ν).ba x = St.a x + gpOff ν := (gvR_inv St ν hν).ba ν (lt_add_one ν) x

theorem gvR_γ : (gvRD St ν).γ ≤ ν := (gvR_inv St ν hν).γ ν (lt_add_one ν)

end Main

theorem gvR_ext {β γ : Ordinal.{0}} (hβγ : β ≤ γ) (hγ : γ < Om1) :
    (∀ c x, c < (gvRD St β).B → (gvRD St γ).R c x = (gvRD St β).R c x) ∧
    (∀ c, c < (gvRD St β).B → (gvRD St γ).g c = (gvRD St β).g c) :=
  ⟨(gvR_inv St γ hγ).cohR β γ hβγ (lt_add_one γ), (gvR_inv St γ hγ).cohg β γ hβγ (lt_add_one γ)⟩

theorem gvR_B_lt {β γ : Ordinal.{0}} (hβγ : β < γ) (hγ : γ < Om1) : (gvRD St β).B < (gvRD St γ).B :=
  (gvR_inv St γ hγ).B_lt hβγ (lt_add_one γ)

theorem gvR_lim_cof {l : Ordinal.{0}} (hl : IsSuccLimit l) (hlK : l < Om1) {c : Ordinal.{0}}
    (hc : c < (gvRD St l).B) : ∃ β, β < l ∧ c < (gvRD St β).B := by
  rw [gvR_B hlK] at hc
  obtain ⟨t, ht, hct⟩ := ((isNormal_veblen 1).lt_iff_exists_lt (isSuccLimit_add _ hl)).1 hc
  obtain ⟨d, hd, htd⟩ := (lt_add_iff hl.bot_lt.ne').1 ht
  refine ⟨d, hd, ?_⟩
  rw [gvR_B (hd.trans hlK)]
  exact hct.trans_le ((isNormal_veblen 1).monotone htd)

/-- **The base gate of a limit system is its index.** -/
theorem gvR_γ_lim {l : Ordinal.{0}} (hl : IsSuccLimit l) (hl1 : l < Om1) : (gvRD St l).γ = l := by
  have H : GvInv St l (gvRD St) := gvInv_lim St (fun β hβ => gvR_inv St β (hβ.trans hl1))
  obtain ⟨Q, hQ, e⟩ := gvRD_lim_eq St hl hl1 H
  rw [e, Q.toCh_lim_γ, hQ]; rfl

/-- **`ν = γ_ν + n`, `n < ω`.** -/
theorem gvR_γ_fin : ∀ ν : Ordinal.{0}, ν < Om1 → ∃ n : ℕ, ν = (gvRD St ν).γ + n := by
  intro ν
  induction ν using Ordinal.limitRecOn with
  | zero =>
    intro _
    refine ⟨0, ?_⟩
    rw [gvRD_zero, St.γ0]
    simp
  | add_one μ ih =>
    intro hμ
    obtain ⟨n, hn⟩ := ih ((lt_add_one μ).trans hμ)
    refine ⟨n + 1, ?_⟩
    rw [gvRD_succ, GsD.step_γ]
    conv_lhs => rw [hn]
    push_cast
    rw [add_assoc]
  | limit l hl _ =>
    intro hl1
    exact ⟨0, by rw [gvR_γ_lim St hl hl1]; simp⟩

theorem gvR_lt_of_γ {ν x : Ordinal.{0}} (hν : ν < Om1) (hx : InE x) (h : (gvRD St ν).γ < x) : ν < x := by
  obtain ⟨n, hn⟩ := gvR_γ_fin St ν hν
  rw [hn]
  exact (inE_indec hx).add_lt h ((natCast_lt_omega0 n).trans (omega0_lt_inE hx))

/-- **`small`**: a code `c < (gvRD St ν).B` with gate below an `ε`-number `σ` lies in `gvRD St μ`, `μ < σ`. -/
theorem gvR_small {ν : Ordinal.{0}} (hν : ν < Om1) {c : Ordinal.{0}} (hc : c < (gvRD St ν).B) {σ : Ordinal.{0}}
    (hσ : InE σ) (hg : (gvRD St ν).g c < σ) : ∃ μ, μ < σ ∧ μ < Om1 ∧ c < (gvRD St μ).B := by
  have hne : ({μ | μ < Om1 ∧ c < (gvRD St μ).B} : Set Ordinal.{0}).Nonempty := ⟨ν, hν, hc⟩
  set N := sInf {μ | μ < Om1 ∧ c < (gvRD St μ).B} with hN
  obtain ⟨hN1, hcN⟩ : N < Om1 ∧ c < (gvRD St N).B := csInf_mem hne
  have hNν : N ≤ ν := csInf_le' ⟨hν, hc⟩
  have hmin : ∀ μ, μ < N → μ < Om1 → ¬ c < (gvRD St μ).B := fun μ hμ hμ1 hcμ =>
    absurd (csInf_le' ⟨hμ1, hcμ⟩ : N ≤ μ) (not_le.2 hμ)
  have hgN : (gvRD St N).g c = (gvRD St ν).g c := ((gvR_ext St hNν hν).2 c hcN).symm
  rw [← hgN] at hg
  rcases zero_or_succ_or_isSuccLimit N with h0 | ⟨m, hm⟩ | hlim
  · exact ⟨N, by rw [h0]; exact hσ.pos, hN1, hcN⟩
  · have hm' : N = m + 1 := by rw [← hm, Order.succ_eq_add_one]
    have hmN : m < N := by rw [hm']; exact lt_add_one m
    have hm1 : m < Om1 := hmN.trans hN1
    have hBc : (gvRD St m).B ≤ c := not_lt.1 (hmin m hmN hm1)
    have hγ : (gvRD St m).γ < σ := by
      have h1 := (gvRD St m).γ_le_sG hBc
      rw [hm', gvRD_succ, GsD.step_g] at hg
      exact h1.trans_lt hg
    have hmσ : m < σ := gvR_lt_of_γ St hm1 hσ hγ
    exact ⟨N, by rw [hm']; exact (ev_isSuccLimit_of_inE hσ).add_one_lt hmσ, hN1, hcN⟩
  · obtain ⟨β, hβ, hcβ⟩ := gvR_lim_cof St hlim hN1 hcN
    exact absurd hcβ (hmin β hβ (hβ.trans hN1))

end Rec

end Googology.Trans.PoR.InaccPsi.R2.Gv
