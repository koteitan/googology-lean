import Googology.Trans.PoR.InaccPsi.R2.HjVSc

/-!
# HjVL: THE STEP OF EVERY LEVEL `L + ν` (`ν < Ω₁`), BY ONE RECURSION ON THE LEVEL

PORT of `Hi.HiVL` to a level datum `Λ : Hj.HjLv`: the prefix `Ω₁` of the level `Ω₁ + ν` (read `x + ν`) is replaced by
`Λ.L` (read `Λ.l x`), so every level below is `Λ.L + ν`, read `Λ.l x + ν`.  What differs: the statements carry the
parameter `Λ`; the facts `Ω₁ ≤ L`, `x ≤ ℓ(x) < Γ_{x+1}`, the level gate (`Hj.hjv_cl_gate`) and Lemma EXACT for `ℓ`
come from `Λ`; the step of the level `L + 0` is a parameter `St0` (in place of `Hi.hiVLS0`).  With `Λ = Hj.hjL1` it is
`Hi.HiVL` again.

The port of `Hg.HgfMRecL` to the levels `L + ν` read as `Λ.l x + ν`.  The level `L + 0`: the step `St0` (a
parameter).  The successor `L + ν + 1`: one more offset recursion (`Hj.hjVScT`); the limit `L + λ`:
the chain of the steps of the levels `L + λ_k`, `λ_k = He.heFs λ k` (`Hj.hjVLmT`).  `hjVLS St0 ν` is defined by
`Ordinal.limitRecOn`; `hjVLS_inv`: every `hjVLS St0 ν`, `ν < Ω₁`, has the specification `Hj.HjVSpec` and extends every
`hjVLS St0 ν'`, `ν' < ν`, at the same pseudo-base.

* `HjVStTy`, `hjVLSucc`, `hjVLmOf`, `HjVLCoh`, `hjVLmSt`, `hjVLLim`, `hjVLS` (**THE
  STEP OF EVERY LEVEL `L + ν`**), `HjVLExt`, `hjVLS_inv` (**THE INVARIANT**), `hjVLS_spec`.

No new axiom.  New definitions: `HjVStTy`, `hjVLSucc`, `hjVLmOf`, `HjVLCoh`, `hjVLmSt`,
`hjVLLim`, `hjVLS`, `HjVLExt`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hj

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

variable {Λ : HjLv}

/-- **The type of a step of level `L + ν`.** -/
abbrev HjVStTy (Λ : HjLv) (ν : Ordinal.{0}) : Type 1 := ∀ (Q : HjVQ Λ ν) (U : HgVD), HgSStart (hjVPB Q) U → HgVD

/-! ## The successor and limit cases -/

section Rec

variable (St0 : HjVStTy Λ 0) (h0 : ∀ Q U h, HjVSpec Q U (St0 Q U h))


open Classical in
/-- **The successor case**: one more offset recursion (when the step of level `L + ν` has the specification). -/
noncomputable def hjVLSucc (ν : Ordinal.{0}) (St : HjVStTy Λ ν) : HjVStTy Λ (ν + 1) := fun P U h =>
  if H : ∀ Q U h, HjVSpec Q U (St Q U h) then hjVScT rfl P H U h else U

/-- **The fundamental sequence of the limit level `L + λ`**: `Ω₁ + heFs λ k`. -/
noncomputable def hjVLmOf (l : Ordinal.{0}) (hl : IsSuccLimit l) (hle : l < Om1) : HjVLm l where
  β := fun k => heFs l k
  lt := fun k => heFs_lt hl (hgf_om hle) k
  mono := fun k => (heFs_mono hl (hgf_om hle) k).le
  cof := fun t ht => heFs_cof hl (hgf_om hle) t ht
  lim := hl
  lv := hle

/-- **The condition at a limit**: every earlier step has the specification, and later steps extend earlier ones at
the same pseudo-base. -/
def HjVLCoh (l : Ordinal.{0}) (IH : ∀ ν, ν < l → HjVStTy Λ ν) : Prop :=
  (∀ ν (h : ν < l), ∀ Q U h', HjVSpec Q U (IH ν h Q U h')) ∧
    ∀ ν ν' (h : ν < l) (h' : ν' < l) (hνν' : ν < ν') (Q : HjVQ Λ ν') (U : HgVD)
      (hU : HgSStart (hjVPB Q) U) (c x : Ordinal.{0}),
      c < (IH ν h (Q.down hνν') U hU).B →
      (IH ν' h' Q U hU).R c x = (IH ν h (Q.down hνν') U hU).R c x ∧
      (IH ν' h' Q U hU).g c = (IH ν h (Q.down hνν') U hU).g c

section LimDef

variable (l : Ordinal.{0}) (hl : IsSuccLimit l) (hle : l < Om1) (IH : ∀ ν, ν < l → HjVStTy Λ ν)
  (H : HjVLCoh l IH)

/-- The steps of the levels `L + λ_k`. -/
noncomputable abbrev hjVLmSt (k : ℕ) : HjVStTy Λ ((hjVLmOf l hl hle).β k) :=
  IH (heFs l k) (heFs_lt hl (hgf_om hle) k)

include H in
theorem hjVLmSt_spec (k : ℕ) : ∀ Q U h, HjVSpec Q U (hjVLmSt l hl hle IH k Q U h) :=
  H.1 (heFs l k) (heFs_lt hl (hgf_om hle) k)

include H in
theorem hjVLmSt_coh (P : HjVQ Λ l) (U : HgVD) (hU : HgSStart (hjVPB P) U) (k : ℕ) (c x : Ordinal.{0})
    (hc : c < (hjVLmSt l hl hle IH k (P.down ((hjVLmOf l hl hle).lt k)) U hU).B) :
    (hjVLmSt l hl hle IH (k + 1) (P.down ((hjVLmOf l hl hle).lt (k + 1))) U hU).R c x =
      (hjVLmSt l hl hle IH k (P.down ((hjVLmOf l hl hle).lt k)) U hU).R c x ∧
    (hjVLmSt l hl hle IH (k + 1) (P.down ((hjVLmOf l hl hle).lt (k + 1))) U hU).g c =
      (hjVLmSt l hl hle IH k (P.down ((hjVLmOf l hl hle).lt k)) U hU).g c :=
  H.2 (heFs l k) (heFs l (k + 1)) (heFs_lt hl (hgf_om hle) k) (heFs_lt hl (hgf_om hle) (k + 1))
    (heFs_mono hl (hgf_om hle) k) _ U hU c x hc

end LimDef

open Classical in
/-- **The limit case**: the union of the chain of the steps of the levels `L + λ_k` (when the condition holds). -/
noncomputable def hjVLLim (l : Ordinal.{0}) (hl : IsSuccLimit l) (IH : ∀ ν, ν < l → HjVStTy Λ ν) : HjVStTy Λ l :=
  fun P U h =>
  if hle : l < Om1 then
    if H : HjVLCoh l IH then
      hjVLmT (hjVLmOf l hl hle) (hjVLmSt l hl hle IH) (hjVLmSt_spec l hl hle IH H) P U h
        (hjVLmSt_coh l hl hle IH H P U h)
    else U
  else U

/-- **THE STEP OF EVERY LEVEL `L + ν`, BY ONE RECURSION ON THE LEVEL.** -/
noncomputable def hjVLS (ν : Ordinal.{0}) : HjVStTy Λ ν :=
  Ordinal.limitRecOn (motive := fun ν => HjVStTy Λ ν) ν St0 hjVLSucc hjVLLim

theorem hjVLS_zero : hjVLS St0 0 = St0 := by unfold hjVLS; rw [Ordinal.limitRecOn_zero]

theorem hjVLS_succ (ν : Ordinal.{0}) : hjVLS St0 (ν + 1) = hjVLSucc ν (hjVLS St0 ν) := by
  unfold hjVLS; rw [Ordinal.limitRecOn_add_one]

theorem hjVLS_limit {l : Ordinal.{0}} (hl : IsSuccLimit l) : hjVLS St0 l = hjVLLim l hl (fun ν _ => hjVLS St0 ν) := by
  unfold hjVLS; rw [Ordinal.limitRecOn_limit _ _ _ _ hl]

/-- The extension statement between two levels at one pseudo-base. -/
def HjVLExt (ν' ν : Ordinal.{0}) (hν' : ν' < ν) : Prop :=
  ∀ (Q : HjVQ Λ ν) (U : HgVD) (hU : HgSStart (hjVPB Q) U) (c x : Ordinal.{0}),
    c < (hjVLS St0 ν' (Q.down hν') U hU).B →
    (hjVLS St0 ν Q U hU).R c x = (hjVLS St0 ν' (Q.down hν') U hU).R c x ∧
    (hjVLS St0 ν Q U hU).g c = (hjVLS St0 ν' (Q.down hν') U hU).g c

include h0 in
/-- **THE INVARIANT**: every `hjVLS St0 ν`, `ν < Ω₁`, has the specification of level `L + ν` and extends every
`hjVLS St0 ν'`, `ν' < ν`, at the same pseudo-base. -/
theorem hjVLS_inv : ∀ ν (hν : ν < Om1), (∀ Q U h, HjVSpec Q U (hjVLS St0 ν Q U h)) ∧
    ∀ ν' (hν' : ν' < ν), HjVLExt St0 ν' ν hν' := by
  intro ν
  induction ν using WellFoundedLT.induction with
  | ind ν IH =>
  intro hν
  rcases zero_or_succ_or_isSuccLimit ν with h0 | ⟨μ, hμ⟩ | hlim
  · subst h0
    refine ⟨fun Q U h => ?_, fun ν' hν' => absurd hν' (not_lt.2 zero_le)⟩
    rw [hjVLS_zero]
    exact h0 Q U h
  · have hμ' : ν = μ + 1 := by rw [← hμ, succ_eq_add_one]
    subst hμ'
    have hμε : μ < Om1 := (lt_add_one μ).trans hν
    obtain ⟨hsp, hext⟩ := IH μ (lt_add_one μ) hμε
    have e : ∀ P U h, hjVLS St0 (μ + 1) P U h = hjVScT rfl P hsp U h := fun P U h => by
      rw [hjVLS_succ St0]; unfold hjVLSucc; rw [dif_pos hsp]
    refine ⟨fun P U h => by rw [e]; exact hjVScT_spec rfl P hsp U h, fun ν' hν' => ?_⟩
    intro P U hU c x hc
    rw [e]
    rcases (Order.lt_add_one_iff.1 hν').lt_or_eq with hlt | heq
    · have hB' : (hjVLS St0 ν' (P.down hν') U hU).B = hdNx (Λ.L + ν') P.F :=
        ((IH ν' hν' (hν'.trans hν)).1 _ U hU).B
      have hBμ : (hjVLS St0 μ (P.down (hjv_lt_of_eq rfl)) U hU).B = hdNx (Λ.L + μ) P.F :=
        (hsp (P.down (hjv_lt_of_eq rfl)) U hU).B
      have hc' : c < (hjVLS St0 μ (P.down (hjv_lt_of_eq rfl)) U hU).B := by
        rw [hBμ]; rw [hB'] at hc; exact hc.trans_le (hdNx_mono (add_le_add le_rfl hlt.le) _)
      obtain ⟨r1, g1⟩ := hjVScT_ext rfl P hsp U hU hc' x
      obtain ⟨r2, g2⟩ := hext ν' hlt (P.down (hjv_lt_of_eq rfl)) U hU c x hc
      exact ⟨r1.trans r2, g1.trans g2⟩
    · subst heq
      exact hjVScT_ext rfl P hsp U hU hc x
  · have hcoh : HjVLCoh ν (fun ν' _ => hjVLS St0 ν') :=
      ⟨fun ν' h => (IH ν' h (h.trans hν)).1, fun ν₁ ν₂ h₁ h₂ h12 Q U hU c x hc =>
        (IH ν₂ h₂ (h₂.trans hν)).2 ν₁ h12 Q U hU c x hc⟩
    have e : ∀ P U h, hjVLS St0 ν P U h = hjVLmT (hjVLmOf ν hlim hν) (hjVLmSt ν hlim hν (fun ν' _ => hjVLS St0 ν'))
        (hjVLmSt_spec ν hlim hν _ hcoh) P U h (hjVLmSt_coh ν hlim hν _ hcoh P U h) := fun P U h => by
      rw [hjVLS_limit St0 hlim]; unfold hjVLLim; rw [dif_pos hν, dif_pos hcoh]
    refine ⟨fun P U h => by rw [e]; exact hjVLmT_spec _ _ _ _ _ _ _, fun ν' hν' => ?_⟩
    intro P U hU c x hc
    rw [e]
    obtain ⟨k, hk⟩ := heFs_cof hlim (hgf_om hν) ν' hν'
    have hkl := heFs_lt hlim (hgf_om hν) k
    obtain ⟨hspk, hextk⟩ := IH _ hkl (hkl.trans hν)
    have hc' : c < (hjVLS St0 (heFs ν k) (P.down hkl) U hU).B := by
      rw [(hspk (P.down hkl) U hU).B]
      rw [((IH ν' hν' (hν'.trans hν)).1 (P.down hν') U hU).B] at hc
      exact hc.trans_le (hdNx_mono (add_le_add le_rfl hk.le) _)
    obtain ⟨r1, g1⟩ := hjVLmT_ext (hjVLmOf ν hlim hν) (hjVLmSt ν hlim hν (fun ν' _ => hjVLS St0 ν'))
      (hjVLmSt_spec ν hlim hν _ hcoh) P U hU (hjVLmSt_coh ν hlim hν _ hcoh P U hU) k hc' x
    obtain ⟨r2, g2⟩ := hextk ν' hk (P.down hkl) U hU c x hc
    exact ⟨r1.trans r2, g1.trans g2⟩

include h0 in
/-- **THE STEP OF EVERY LEVEL `L + ν` HAS THE SPECIFICATION.** -/
theorem hjVLS_spec {ν : Ordinal.{0}} (hν : ν < Om1) (Q : HjVQ Λ ν) (U : HgVD) (h : HgSStart (hjVPB Q) U) :
    HjVSpec Q U (hjVLS St0 ν Q U h) := (hjVLS_inv St0 h0 ν hν).1 Q U h

end Rec

end Googology.Trans.PoR.InaccPsi.R2.Hj
