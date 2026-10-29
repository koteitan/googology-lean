import Googology.Trans.PoR.InaccPsi.R2.HlVSc

/-!
# HlVL: THE STEP OF EVERY GATED LEVEL `L + ν` (`ν < Ω₁`), BY ONE RECURSION ON THE LEVEL

PORT of `Hj.HjVL` (`Hj.hjVLmOf` is imported).

What differs from the source: the level datum is a GATED one (`Hl.HlLv`: Lemma EXACT for the reading `ℓ` only at
base pairs `(σ, ρ)` above the level gate `g`, the hull membership of `L` only at `0 < a`, `g < b`, the code gate
`g < Z` only when a code over `Z` exists at the level); every pseudo-base and base carries `g ≤` its reading gate
(fields `lg`), and the code-gate fields take the extra hypothesis `g < Z`.  Proofs are otherwise those of the source;
names: prefix `hl`/`Hl` in place of `hj`/`Hj`.

No new axiom.  New definitions: `HlVStTy`, `hlVLSucc`, `HlVLCoh`, `hlVLmSt`,
`hlVLLim`, `hlVLS`, `HlVLExt`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hl

open Googology.Trans.PoR.InaccPsi.R2.Hj Googology.Trans.PoR.InaccPsi.R2.Hk

open Googology.Trans.PoR.InaccPsi.R2.Hi

open Googology.Trans.PoR.InaccPsi.R2.Hg
open Googology.Trans.PoR.InaccPsi.R2.Hf Googology.Trans.PoR.InaccPsi.R2.Hd Googology.Trans.PoR.InaccPsi.R2.He
open Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Hb
open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

variable {Λ : HlLv}

/-- **The type of a step of level `L + ν`.** -/
abbrev HlVStTy (Λ : HlLv) (ν : Ordinal.{0}) : Type 1 := ∀ (Q : HlVQ Λ ν) (U : HgVD), HgSStart (hlVPB Q) U → HgVD

/-! ## The successor and limit cases -/

section Rec

variable (St0 : HlVStTy Λ 0) (h0 : ∀ Q U h, HlVSpec Q U (St0 Q U h))


open Classical in
/-- **The successor case**: one more offset recursion (when the step of level `L + ν` has the specification). -/
noncomputable def hlVLSucc (ν : Ordinal.{0}) (St : HlVStTy Λ ν) : HlVStTy Λ (ν + 1) := fun P U h =>
  if H : ∀ Q U h, HlVSpec Q U (St Q U h) then hlVScT rfl P H U h else U

/-- **The condition at a limit**: every earlier step has the specification, and later steps extend earlier ones at
the same pseudo-base. -/
def HlVLCoh (l : Ordinal.{0}) (IH : ∀ ν, ν < l → HlVStTy Λ ν) : Prop :=
  (∀ ν (h : ν < l), ∀ Q U h', HlVSpec Q U (IH ν h Q U h')) ∧
    ∀ ν ν' (h : ν < l) (h' : ν' < l) (hνν' : ν < ν') (Q : HlVQ Λ ν') (U : HgVD)
      (hU : HgSStart (hlVPB Q) U) (c x : Ordinal.{0}),
      c < (IH ν h (Q.down hνν') U hU).B →
      (IH ν' h' Q U hU).R c x = (IH ν h (Q.down hνν') U hU).R c x ∧
      (IH ν' h' Q U hU).g c = (IH ν h (Q.down hνν') U hU).g c

section LimDef

variable (l : Ordinal.{0}) (hl : IsSuccLimit l) (hle : l < Om1) (IH : ∀ ν, ν < l → HlVStTy Λ ν)
  (H : HlVLCoh l IH)

/-- The steps of the levels `L + λ_k`. -/
noncomputable abbrev hlVLmSt (k : ℕ) : HlVStTy Λ ((hjVLmOf l hl hle).β k) :=
  IH (heFs l k) (heFs_lt hl (hgf_om hle) k)

include H in
theorem hlVLmSt_spec (k : ℕ) : ∀ Q U h, HlVSpec Q U (hlVLmSt l hl hle IH k Q U h) :=
  H.1 (heFs l k) (heFs_lt hl (hgf_om hle) k)

include H in
theorem hlVLmSt_coh (P : HlVQ Λ l) (U : HgVD) (hU : HgSStart (hlVPB P) U) (k : ℕ) (c x : Ordinal.{0})
    (hc : c < (hlVLmSt l hl hle IH k (P.down ((hjVLmOf l hl hle).lt k)) U hU).B) :
    (hlVLmSt l hl hle IH (k + 1) (P.down ((hjVLmOf l hl hle).lt (k + 1))) U hU).R c x =
      (hlVLmSt l hl hle IH k (P.down ((hjVLmOf l hl hle).lt k)) U hU).R c x ∧
    (hlVLmSt l hl hle IH (k + 1) (P.down ((hjVLmOf l hl hle).lt (k + 1))) U hU).g c =
      (hlVLmSt l hl hle IH k (P.down ((hjVLmOf l hl hle).lt k)) U hU).g c :=
  H.2 (heFs l k) (heFs l (k + 1)) (heFs_lt hl (hgf_om hle) k) (heFs_lt hl (hgf_om hle) (k + 1))
    (heFs_mono hl (hgf_om hle) k) _ U hU c x hc

end LimDef

open Classical in
/-- **The limit case**: the union of the chain of the steps of the levels `L + λ_k` (when the condition holds). -/
noncomputable def hlVLLim (l : Ordinal.{0}) (hl : IsSuccLimit l) (IH : ∀ ν, ν < l → HlVStTy Λ ν) : HlVStTy Λ l :=
  fun P U h =>
  if hle : l < Om1 then
    if H : HlVLCoh l IH then
      hlVLmT (hjVLmOf l hl hle) (hlVLmSt l hl hle IH) (hlVLmSt_spec l hl hle IH H) P U h
        (hlVLmSt_coh l hl hle IH H P U h)
    else U
  else U

/-- **THE STEP OF EVERY LEVEL `L + ν`, BY ONE RECURSION ON THE LEVEL.** -/
noncomputable def hlVLS (ν : Ordinal.{0}) : HlVStTy Λ ν :=
  Ordinal.limitRecOn (motive := fun ν => HlVStTy Λ ν) ν St0 hlVLSucc hlVLLim

theorem hlVLS_zero : hlVLS St0 0 = St0 := by unfold hlVLS; rw [Ordinal.limitRecOn_zero]

theorem hlVLS_succ (ν : Ordinal.{0}) : hlVLS St0 (ν + 1) = hlVLSucc ν (hlVLS St0 ν) := by
  unfold hlVLS; rw [Ordinal.limitRecOn_add_one]

theorem hlVLS_limit {l : Ordinal.{0}} (hl : IsSuccLimit l) : hlVLS St0 l = hlVLLim l hl (fun ν _ => hlVLS St0 ν) := by
  unfold hlVLS; rw [Ordinal.limitRecOn_limit _ _ _ _ hl]

/-- The extension statement between two levels at one pseudo-base. -/
def HlVLExt (ν' ν : Ordinal.{0}) (hν' : ν' < ν) : Prop :=
  ∀ (Q : HlVQ Λ ν) (U : HgVD) (hU : HgSStart (hlVPB Q) U) (c x : Ordinal.{0}),
    c < (hlVLS St0 ν' (Q.down hν') U hU).B →
    (hlVLS St0 ν Q U hU).R c x = (hlVLS St0 ν' (Q.down hν') U hU).R c x ∧
    (hlVLS St0 ν Q U hU).g c = (hlVLS St0 ν' (Q.down hν') U hU).g c

include h0 in
/-- **THE INVARIANT**: every `hlVLS St0 ν`, `ν < Ω₁`, has the specification of level `L + ν` and extends every
`hlVLS St0 ν'`, `ν' < ν`, at the same pseudo-base. -/
theorem hlVLS_inv : ∀ ν (hν : ν < Om1), (∀ Q U h, HlVSpec Q U (hlVLS St0 ν Q U h)) ∧
    ∀ ν' (hν' : ν' < ν), HlVLExt St0 ν' ν hν' := by
  intro ν
  induction ν using WellFoundedLT.induction with
  | ind ν IH =>
  intro hν
  rcases zero_or_succ_or_isSuccLimit ν with h0 | ⟨μ, hμ⟩ | hlim
  · subst h0
    refine ⟨fun Q U h => ?_, fun ν' hν' => absurd hν' (not_lt.2 zero_le)⟩
    rw [hlVLS_zero]
    exact h0 Q U h
  · have hμ' : ν = μ + 1 := by rw [← hμ, succ_eq_add_one]
    subst hμ'
    have hμε : μ < Om1 := (lt_add_one μ).trans hν
    obtain ⟨hsp, hext⟩ := IH μ (lt_add_one μ) hμε
    have e : ∀ P U h, hlVLS St0 (μ + 1) P U h = hlVScT rfl P hsp U h := fun P U h => by
      rw [hlVLS_succ St0]; unfold hlVLSucc; rw [dif_pos hsp]
    refine ⟨fun P U h => by rw [e]; exact hlVScT_spec rfl P hsp U h, fun ν' hν' => ?_⟩
    intro P U hU c x hc
    rw [e]
    rcases (Order.lt_add_one_iff.1 hν').lt_or_eq with hlt | heq
    · have hB' : (hlVLS St0 ν' (P.down hν') U hU).B = hdNx (Λ.L + ν') P.F :=
        ((IH ν' hν' (hν'.trans hν)).1 _ U hU).B
      have hBμ : (hlVLS St0 μ (P.down (hjv_lt_of_eq rfl)) U hU).B = hdNx (Λ.L + μ) P.F :=
        (hsp (P.down (hjv_lt_of_eq rfl)) U hU).B
      have hc' : c < (hlVLS St0 μ (P.down (hjv_lt_of_eq rfl)) U hU).B := by
        rw [hBμ]; rw [hB'] at hc; exact hc.trans_le (hdNx_mono (add_le_add le_rfl hlt.le) _)
      obtain ⟨r1, g1⟩ := hlVScT_ext rfl P hsp U hU hc' x
      obtain ⟨r2, g2⟩ := hext ν' hlt (P.down (hjv_lt_of_eq rfl)) U hU c x hc
      exact ⟨r1.trans r2, g1.trans g2⟩
    · subst heq
      exact hlVScT_ext rfl P hsp U hU hc x
  · have hcoh : HlVLCoh ν (fun ν' _ => hlVLS St0 ν') :=
      ⟨fun ν' h => (IH ν' h (h.trans hν)).1, fun ν₁ ν₂ h₁ h₂ h12 Q U hU c x hc =>
        (IH ν₂ h₂ (h₂.trans hν)).2 ν₁ h12 Q U hU c x hc⟩
    have e : ∀ P U h, hlVLS St0 ν P U h = hlVLmT (hjVLmOf ν hlim hν) (hlVLmSt ν hlim hν (fun ν' _ => hlVLS St0 ν'))
        (hlVLmSt_spec ν hlim hν _ hcoh) P U h (hlVLmSt_coh ν hlim hν _ hcoh P U h) := fun P U h => by
      rw [hlVLS_limit St0 hlim]; unfold hlVLLim; rw [dif_pos hν, dif_pos hcoh]
    refine ⟨fun P U h => by rw [e]; exact hlVLmT_spec _ _ _ _ _ _ _, fun ν' hν' => ?_⟩
    intro P U hU c x hc
    rw [e]
    obtain ⟨k, hk⟩ := heFs_cof hlim (hgf_om hν) ν' hν'
    have hkl := heFs_lt hlim (hgf_om hν) k
    obtain ⟨hspk, hextk⟩ := IH _ hkl (hkl.trans hν)
    have hc' : c < (hlVLS St0 (heFs ν k) (P.down hkl) U hU).B := by
      rw [(hspk (P.down hkl) U hU).B]
      rw [((IH ν' hν' (hν'.trans hν)).1 (P.down hν') U hU).B] at hc
      exact hc.trans_le (hdNx_mono (add_le_add le_rfl hk.le) _)
    obtain ⟨r1, g1⟩ := hlVLmT_ext (hjVLmOf ν hlim hν) (hlVLmSt ν hlim hν (fun ν' _ => hlVLS St0 ν'))
      (hlVLmSt_spec ν hlim hν _ hcoh) P U hU (hlVLmSt_coh ν hlim hν _ hcoh P U hU) k hc' x
    obtain ⟨r2, g2⟩ := hextk ν' hk (P.down hkl) U hU c x hc
    exact ⟨r1.trans r2, g1.trans g2⟩

include h0 in
/-- **THE STEP OF EVERY LEVEL `L + ν` HAS THE SPECIFICATION.** -/
theorem hlVLS_spec {ν : Ordinal.{0}} (hν : ν < Om1) (Q : HlVQ Λ ν) (U : HgVD) (h : HgSStart (hlVPB Q) U) :
    HlVSpec Q U (hlVLS St0 ν Q U h) := (hlVLS_inv St0 h0 ν hν).1 Q U h

end Rec

end Googology.Trans.PoR.InaccPsi.R2.Hl
