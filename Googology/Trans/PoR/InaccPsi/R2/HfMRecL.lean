import Googology.Trans.PoR.InaccPsi.R2.HfMSc

/-!
# HfMRecL: THE STEP OF EVERY COUNTABLE LEVEL `ω ≤ α < Ω₁`, BY ONE RECURSION ON THE LEVEL

`hfLS ν` is a step of level `ω + ν` (a function from pseudo-bases `P` of level `ω + ν` and starts `U` of the stage
at `P` to digit systems), defined by `Ordinal.limitRecOn` on `ν`:

* `ν = 0`: the gated `ω`-step `Hd.hdStep`;
* `ν + 1`: **one more offset recursion** (`Hf.hfScT`): the union of all gated offsets over `P` as a base of level
  `ω + ν`, started at the step of level `ω + ν` at `P`;
* a limit `λ < Ω₁`: **the union over the lower levels** (`Hf.hfLmT`): the gated `ω`-chain of the steps of the levels
  `ω + λ_k` (`λ_k = He.heFs λ k`, any fundamental sequence) at `P`.

The invariant (`hfLS_inv`): every `hfLS ν`, `ν < Ω₁`, has the specification `Hf.HfQSpec` of level `ω + ν` (bound
`hdNx (ω + ν) F`), and extends every `hfLS ν'`, `ν' < ν`, at the same pseudo-base.

* `HfStTy`, `hf_lev`, `hf_lev_lt`, `hf_lev_e`, `hfQ_spec_om'`, `hfLS0`, `hfLSucc`, `hfLmOf`, `HfLCoh`, `hfLLim`,
  `hfLS` (**THE STEP OF EVERY COUNTABLE LEVEL**), `hfLS_zero`, `hfLS_succ`, `hfLS_limit`, `hfLS_inv` (**THE
  INVARIANT**), `hfLS_spec`.

No new axiom.  New definitions: `HfStTy`, `hfLS0`, `hfLSucc`, `hfLmOf`, `HfLCoh`, `hfLLim`, `hfLS`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hf

open Googology.Trans.PoR.InaccPsi.R2.Hd Googology.Trans.PoR.InaccPsi.R2.He

open Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Hb Googology.Trans.PoR.InaccPsi.R2.Gp
open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

/-- **The type of a step of level `μ`.** -/
abbrev HfStTy (μ : Ordinal.{0}) : Type 1 := ∀ (Q : HfQ μ) (U : HcVD), HcSStart (hfQPB Q) U → HcVD

theorem hf_om {l : Ordinal.{0}} (h : l < Om1) : l < Om (1 : Ordinal.{0}) := by rw [← Br.Om1_eq]; exact h

theorem hf_lev {ν : Ordinal.{0}} (hν : ν < Om1) : HfLvl (ω + ν) :=
  ⟨le_self_add, (inE_indec gl_Om1_E).add_lt (omega0_lt_inE gl_Om1_E) hν⟩

theorem hf_lev_lt {ν ν' : Ordinal.{0}} (h : ν < ν') : ω + ν < ω + ν' := (add_lt_add_iff_left ω).2 h

theorem hf_lev_e (ν : Ordinal.{0}) : ω + (ν + 1) = ω + ν + 1 := (add_assoc _ _ _).symm

/-- **The `ω`-step at a pseudo-base of level `μ = ω` has the specification.** -/
theorem hfQ_spec_om' {μ : Ordinal.{0}} (hμ : μ = ω) (Q : HfQ μ) (U : HcVD) (h : HcSStart (hfQPB Q) U) :
    HfQSpec Q U (hdStep Q.toP U h) := by
  subst hμ; exact hfQ_spec_om Q U h

/-! ## The three cases -/

/-- The step of level `ω + 0`: the `ω`-step. -/
noncomputable def hfLS0 : HfStTy (ω + 0) := fun Q U h => hdStep Q.toP U h

open Classical in
/-- **The successor case**: one more offset recursion (when the step of level `ω + ν` has the specification). -/
noncomputable def hfLSucc (ν : Ordinal.{0}) (St : HfStTy (ω + ν)) : HfStTy (ω + (ν + 1)) := fun P U h =>
  if H : HfLvl (ω + ν) ∧ ∀ Q U h, HfQSpec Q U (St Q U h) then hfScT H.1 (hf_lev_e ν) P H.2 U h else U

/-- **The fundamental sequence of the limit level `ω + λ`**: `ω + heFs λ k`. -/
noncomputable def hfLmOf (l : Ordinal.{0}) (hl : IsSuccLimit l) (hle : l < Om1) : HfLm (ω + l) where
  β := fun k => ω + heFs l k
  lv := fun k => hf_lev ((heFs_lt hl (hf_om hle) k).trans hle)
  lt := fun k => hf_lev_lt (heFs_lt hl (hf_om hle) k)
  mono := fun k => (add_le_add_iff_left ω).2 (heFs_mono hl (hf_om hle) k).le
  cof := fun t ht => by
    obtain ⟨t', ht', htt'⟩ := (lt_add_iff hl.bot_lt.ne').1 ht
    obtain ⟨k, hk⟩ := heFs_cof hl (hf_om hle) t' ht'
    exact ⟨k, htt'.trans_lt (hf_lev_lt hk)⟩
  lim := isSuccLimit_add ω hl

/-- **The condition at a limit**: every earlier step has the specification, and later steps extend earlier ones at
the same pseudo-base. -/
def HfLCoh (l : Ordinal.{0}) (hle : l < Om1) (IH : ∀ ν, ν < l → HfStTy (ω + ν)) : Prop :=
  (∀ ν (h : ν < l), ∀ Q U h', HfQSpec Q U (IH ν h Q U h')) ∧
    ∀ ν ν' (h : ν < l) (h' : ν' < l) (hνν' : ν < ν') (Q : HfQ (ω + ν')) (U : HcVD)
      (hU : HcSStart (hfQPB Q) U) (c x : Ordinal.{0}),
      c < (IH ν h (Q.down (hf_lev (h.trans hle)) (hf_lev_lt hνν')) U hU).B →
      (IH ν' h' Q U hU).R c x = (IH ν h (Q.down (hf_lev (h.trans hle)) (hf_lev_lt hνν')) U hU).R c x ∧
      (IH ν' h' Q U hU).g c = (IH ν h (Q.down (hf_lev (h.trans hle)) (hf_lev_lt hνν')) U hU).g c

section LimDef

variable (l : Ordinal.{0}) (hl : IsSuccLimit l) (hle : l < Om1) (IH : ∀ ν, ν < l → HfStTy (ω + ν))
  (H : HfLCoh l hle IH)

/-- The steps of the levels `ω + λ_k`. -/
noncomputable abbrev hfLmSt (k : ℕ) : HfStTy ((hfLmOf l hl hle).β k) :=
  IH (heFs l k) (heFs_lt hl (hf_om hle) k)

include H in
theorem hfLmSt_spec (k : ℕ) : ∀ Q U h, HfQSpec Q U (hfLmSt l hl hle IH k Q U h) :=
  H.1 (heFs l k) (heFs_lt hl (hf_om hle) k)

include H in
theorem hfLmSt_coh (P : HfQ (ω + l)) (U : HcVD) (hU : HcSStart (hfQPB P) U) (k : ℕ) (c x : Ordinal.{0})
    (hc : c < (hfLmSt l hl hle IH k (P.down ((hfLmOf l hl hle).lv k) ((hfLmOf l hl hle).lt k)) U hU).B) :
    (hfLmSt l hl hle IH (k + 1) (P.down ((hfLmOf l hl hle).lv (k + 1)) ((hfLmOf l hl hle).lt (k + 1))) U hU).R c x =
      (hfLmSt l hl hle IH k (P.down ((hfLmOf l hl hle).lv k) ((hfLmOf l hl hle).lt k)) U hU).R c x ∧
    (hfLmSt l hl hle IH (k + 1) (P.down ((hfLmOf l hl hle).lv (k + 1)) ((hfLmOf l hl hle).lt (k + 1))) U hU).g c =
      (hfLmSt l hl hle IH k (P.down ((hfLmOf l hl hle).lv k) ((hfLmOf l hl hle).lt k)) U hU).g c :=
  H.2 (heFs l k) (heFs l (k + 1)) (heFs_lt hl (hf_om hle) k) (heFs_lt hl (hf_om hle) (k + 1))
    (heFs_mono hl (hf_om hle) k) _ U hU c x hc

end LimDef

open Classical in
/-- **The limit case**: the union of the chain of the steps of the levels `ω + λ_k` (when the condition holds). -/
noncomputable def hfLLim (l : Ordinal.{0}) (hl : IsSuccLimit l) (IH : ∀ ν, ν < l → HfStTy (ω + ν)) :
    HfStTy (ω + l) := fun P U h =>
  if hle : l < Om1 then
    if H : HfLCoh l hle IH then
      hfLmT (hfLmOf l hl hle) (hfLmSt l hl hle IH) (hfLmSt_spec l hl hle IH H) P U h
        (hfLmSt_coh l hl hle IH H P U h)
    else U
  else U

/-- **THE STEP OF EVERY COUNTABLE LEVEL `ω + ν`, BY ONE RECURSION ON THE LEVEL.** -/
noncomputable def hfLS (ν : Ordinal.{0}) : HfStTy (ω + ν) :=
  Ordinal.limitRecOn (motive := fun ν => HfStTy (ω + ν)) ν hfLS0 hfLSucc hfLLim

theorem hfLS_zero : hfLS 0 = hfLS0 := by unfold hfLS; rw [Ordinal.limitRecOn_zero]

theorem hfLS_succ (ν : Ordinal.{0}) : hfLS (ν + 1) = hfLSucc ν (hfLS ν) := by
  unfold hfLS; rw [Ordinal.limitRecOn_add_one]

theorem hfLS_limit {l : Ordinal.{0}} (hl : IsSuccLimit l) : hfLS l = hfLLim l hl (fun ν _ => hfLS ν) := by
  unfold hfLS; rw [Ordinal.limitRecOn_limit _ _ _ _ hl]

/-- The extension statement between two levels at one pseudo-base. -/
def HfLExt (ν' ν : Ordinal.{0}) (hν : ν < Om1) (hν' : ν' < ν) : Prop :=
  ∀ (Q : HfQ (ω + ν)) (U : HcVD) (hU : HcSStart (hfQPB Q) U) (c x : Ordinal.{0}),
    c < (hfLS ν' (Q.down (hf_lev (hν'.trans hν)) (hf_lev_lt hν')) U hU).B →
    (hfLS ν Q U hU).R c x = (hfLS ν' (Q.down (hf_lev (hν'.trans hν)) (hf_lev_lt hν')) U hU).R c x ∧
    (hfLS ν Q U hU).g c = (hfLS ν' (Q.down (hf_lev (hν'.trans hν)) (hf_lev_lt hν')) U hU).g c

/-- **THE INVARIANT**: every `hfLS ν`, `ν < Ω₁`, has the specification of level `ω + ν` and extends every `hfLS ν'`,
`ν' < ν`, at the same pseudo-base. -/
theorem hfLS_inv : ∀ ν (hν : ν < Om1), (∀ Q U h, HfQSpec Q U (hfLS ν Q U h)) ∧
    ∀ ν' (hν' : ν' < ν), HfLExt ν' ν hν hν' := by
  intro ν
  induction ν using WellFoundedLT.induction with
  | ind ν IH =>
  intro hν
  rcases zero_or_succ_or_isSuccLimit ν with h0 | ⟨μ, hμ⟩ | hlim
  · subst h0
    refine ⟨fun Q U h => ?_, fun ν' hν' => absurd hν' (not_lt.2 zero_le)⟩
    rw [hfLS_zero]
    exact hfQ_spec_om' (add_zero ω) Q U h
  · have hμ' : ν = μ + 1 := by rw [← hμ, succ_eq_add_one]
    subst hμ'
    have hμε : μ < Om1 := (lt_add_one μ).trans hν
    obtain ⟨hsp, hext⟩ := IH μ (lt_add_one μ) hμε
    have hH : HfLvl (ω + μ) ∧ ∀ Q U h, HfQSpec Q U (hfLS μ Q U h) := ⟨hf_lev hμε, hsp⟩
    have e : ∀ P U h, hfLS (μ + 1) P U h = hfScT hH.1 (hf_lev_e μ) P hH.2 U h := fun P U h => by
      rw [hfLS_succ]; unfold hfLSucc; rw [dif_pos hH]
    refine ⟨fun P U h => by rw [e]; exact hfScT_spec hH.1 (hf_lev_e μ) P hH.2 U h, fun ν' hν' => ?_⟩
    intro P U hU c x hc
    rw [e]
    rcases (Order.lt_add_one_iff.1 hν').lt_or_eq with hlt | heq
    · -- `ν' < μ`: through the step of level `ω + μ`
      have hB' : (hfLS ν' (P.down (hf_lev (hν'.trans hν)) (hf_lev_lt hν')) U hU).B = hdNx (ω + ν') P.F :=
        ((IH ν' hν' (hν'.trans hν)).1 _ U hU).B
      have hBμ : (hfLS μ (P.down hH.1 (hd_lt_of_eq (hf_lev_e μ))) U hU).B = hdNx (ω + μ) P.F :=
        (hsp (P.down hH.1 (hd_lt_of_eq (hf_lev_e μ))) U hU).B
      have hc' : c < (hfLS μ (P.down hH.1 (hd_lt_of_eq (hf_lev_e μ))) U hU).B := by
        rw [hBμ]; rw [hB'] at hc; exact hc.trans_le (hdNx_mono (hf_lev_lt hlt).le _)
      obtain ⟨r1, g1⟩ := hfScT_ext hH.1 (hf_lev_e μ) P hH.2 U hU hc' x
      obtain ⟨r2, g2⟩ := hext ν' hlt (P.down hH.1 (hd_lt_of_eq (hf_lev_e μ))) U hU c x hc
      exact ⟨r1.trans r2, g1.trans g2⟩
    · subst heq
      exact hfScT_ext hH.1 (hf_lev_e _) P hH.2 U hU hc x
  · -- the limit: the union of the chain
    have hcoh : HfLCoh ν hν (fun ν' _ => hfLS ν') :=
      ⟨fun ν' h => (IH ν' h (h.trans hν)).1, fun ν₁ ν₂ h₁ h₂ h12 Q U hU c x hc =>
        (IH ν₂ h₂ (h₂.trans hν)).2 ν₁ h12 Q U hU c x hc⟩
    have e : ∀ P U h, hfLS ν P U h = hfLmT (hfLmOf ν hlim hν) (hfLmSt ν hlim hν (fun ν' _ => hfLS ν'))
        (hfLmSt_spec ν hlim hν _ hcoh) P U h (hfLmSt_coh ν hlim hν _ hcoh P U h) := fun P U h => by
      rw [hfLS_limit hlim]; unfold hfLLim; rw [dif_pos hν, dif_pos hcoh]
    refine ⟨fun P U h => by rw [e]; exact hfLmT_spec _ _ _ _ _ _ _, fun ν' hν' => ?_⟩
    intro P U hU c x hc
    rw [e]
    obtain ⟨k, hk⟩ := heFs_cof hlim (hf_om hν) ν' hν'
    have hkl := heFs_lt hlim (hf_om hν) k
    obtain ⟨hspk, hextk⟩ := IH _ hkl (hkl.trans hν)
    have hc' : c < (hfLS (heFs ν k) (P.down (hf_lev (hkl.trans hν)) (hf_lev_lt hkl)) U hU).B := by
      rw [(hspk (P.down (hf_lev (hkl.trans hν)) (hf_lev_lt hkl)) U hU).B]
      rw [((IH ν' hν' (hν'.trans hν)).1 (P.down (hf_lev (hν'.trans hν)) (hf_lev_lt hν')) U hU).B] at hc
      exact hc.trans_le (hdNx_mono (hf_lev_lt hk).le _)
    obtain ⟨r1, g1⟩ := hfLmT_ext (hfLmOf ν hlim hν) (hfLmSt ν hlim hν (fun ν' _ => hfLS ν'))
      (hfLmSt_spec ν hlim hν _ hcoh) P U hU (hfLmSt_coh ν hlim hν _ hcoh P U hU) k hc' x
    obtain ⟨r2, g2⟩ := hextk ν' hk (P.down (hf_lev (hkl.trans hν)) (hf_lev_lt hkl)) U hU c x hc
    exact ⟨r1.trans r2, g1.trans g2⟩

/-- **THE STEP OF EVERY COUNTABLE LEVEL HAS THE SPECIFICATION.** -/
theorem hfLS_spec {ν : Ordinal.{0}} (hν : ν < Om1) (Q : HfQ (ω + ν)) (U : HcVD) (h : HcSStart (hfQPB Q) U) :
    HfQSpec Q U (hfLS ν Q U h) := (hfLS_inv ν hν).1 Q U h

end Googology.Trans.PoR.InaccPsi.R2.Hf
