import Googology.Trans.PoR.InaccPsi.R2.HgPB
import Googology.Trans.PoR.InaccPsi.R2.HgS
import Googology.Trans.PoR.InaccPsi.R2.HgSRec
import Googology.Trans.PoR.InaccPsi.R2.HgSU
import Googology.Trans.PoR.InaccPsi.R2.HgX
import Googology.Trans.PoR.InaccPsi.R2.HgLv
import Googology.Trans.PoR.InaccPsi.R2.HgLvRec
import Googology.Trans.PoR.InaccPsi.R2.HgLvTop
import Googology.Trans.PoR.InaccPsi.R2.HgRec
import Googology.Trans.PoR.InaccPsi.R2.HgCh
import Googology.Trans.PoR.InaccPsi.R2.HgdX
import Googology.Trans.PoR.InaccPsi.R2.HgdCh
import Googology.Trans.PoR.InaccPsi.R2.HgdStep
import Googology.Trans.PoR.InaccPsi.R2.HgdLv
import Googology.Trans.PoR.InaccPsi.R2.HgdLvRec
import Googology.Trans.PoR.InaccPsi.R2.HgdLvTop
import Googology.Trans.PoR.InaccPsi.R2.HgdM
import Googology.Trans.PoR.InaccPsi.R2.HgdMLv
import Googology.Trans.PoR.InaccPsi.R2.HgdMRec
import Googology.Trans.PoR.InaccPsi.R2.HgdMTop
import Googology.Trans.PoR.InaccPsi.R2.HgdMSc
import Googology.Trans.PoR.InaccPsi.R2.HgdMRecL
import Googology.Trans.PoR.InaccPsi.R2.HgfM
import Googology.Trans.PoR.InaccPsi.R2.HgfMLv
import Googology.Trans.PoR.InaccPsi.R2.HgfMRec
import Googology.Trans.PoR.InaccPsi.R2.HgfMTop
import Googology.Trans.PoR.InaccPsi.R2.HgfMSc

/-!
# HgfMRecL: THE STEP OF EVERY COUNTABLE LEVEL `ω ≤ α < Ω₁`, BY ONE RECURSION ON THE LEVEL

(Textual copy of `Hf.HfMRecL` for `Hg.HgVD`: bound fields `< Γ_{x+2}` in place of `≤ B_x(x)` (`Hc.hcBR`); the proofs
are unchanged except where the bound enters.  Names: prefix `hg`/`Hg` (from `hc`/`Hc`), `hgd`/`Hgd` (from `hd`/`Hd`),
`hgf`/`Hgf` (from `hf`/`Hf`), `hge`/`Hge` (from `he`/`He`).)

`hgfLS ν` is a step of level `ω + ν` (a function from pseudo-bases `P` of level `ω + ν` and starts `U` of the stage
at `P` to digit systems), defined by `Ordinal.limitRecOn` on `ν`:

* `ν = 0`: the gated `ω`-step `Hg.hgdStep`;
* `ν + 1`: **one more offset recursion** (`Hg.hgfScT`): the union of all gated offsets over `P` as a base of level
  `ω + ν`, started at the step of level `ω + ν` at `P`;
* a limit `λ < Ω₁`: **the union over the lower levels** (`Hg.hgfLmT`): the gated `ω`-chain of the steps of the levels
  `ω + λ_k` (`λ_k = He.heFs λ k`, any fundamental sequence) at `P`.

The invariant (`hgfLS_inv`): every `hgfLS ν`, `ν < Ω₁`, has the specification `Hg.HgfQSpec` of level `ω + ν` (bound
`hdNx (ω + ν) F`), and extends every `hgfLS ν'`, `ν' < ν`, at the same pseudo-base.

* `HgfStTy`, `hgf_lev`, `hgf_lev_lt`, `hgf_lev_e`, `hgfQ_spec_om'`, `hgfLS0`, `hgfLSucc`, `hgfLmOf`, `HgfLCoh`,
  `hgfLLim`,
  `hgfLS` (**THE STEP OF EVERY COUNTABLE LEVEL**), `hgfLS_zero`, `hgfLS_succ`, `hgfLS_limit`, `hgfLS_inv` (**THE
  INVARIANT**), `hgfLS_spec`.

No new axiom.  New definitions: `HgfStTy`, `hgfLS0`, `hgfLSucc`, `hgfLmOf`, `HgfLCoh`, `hgfLLim`, `hgfLS`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hg

open Googology.Trans.PoR.InaccPsi.R2.Hc
open Googology.Trans.PoR.InaccPsi.R2.Hd
open Googology.Trans.PoR.InaccPsi.R2.He
open Googology.Trans.PoR.InaccPsi.R2.Hf

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
abbrev HgfStTy (μ : Ordinal.{0}) : Type 1 := ∀ (Q : HgfQ μ) (U : HgVD), HgSStart (hgfQPB Q) U → HgVD

theorem hgf_om {l : Ordinal.{0}} (h : l < Om1) : l < Om (1 : Ordinal.{0}) := by rw [← Br.Om1_eq]; exact h

theorem hgf_lev {ν : Ordinal.{0}} (hν : ν < Om1) : HfLvl (ω + ν) :=
  ⟨le_self_add, (inE_indec gl_Om1_E).add_lt (omega0_lt_inE gl_Om1_E) hν⟩

theorem hgf_lev_lt {ν ν' : Ordinal.{0}} (h : ν < ν') : ω + ν < ω + ν' := (add_lt_add_iff_left ω).2 h

theorem hgf_lev_e (ν : Ordinal.{0}) : ω + (ν + 1) = ω + ν + 1 := (add_assoc _ _ _).symm

/-- **The `ω`-step at a pseudo-base of level `μ = ω` has the specification.** -/
theorem hgfQ_spec_om' {μ : Ordinal.{0}} (hμ : μ = ω) (Q : HgfQ μ) (U : HgVD) (h : HgSStart (hgfQPB Q) U) :
    HgfQSpec Q U (hgdStep Q.toP U h) := by
  subst hμ; exact hgfQ_spec_om Q U h

/-! ## The three cases -/

/-- The step of level `ω + 0`: the `ω`-step. -/
noncomputable def hgfLS0 : HgfStTy (ω + 0) := fun Q U h => hgdStep Q.toP U h

open Classical in
/-- **The successor case**: one more offset recursion (when the step of level `ω + ν` has the specification). -/
noncomputable def hgfLSucc (ν : Ordinal.{0}) (St : HgfStTy (ω + ν)) : HgfStTy (ω + (ν + 1)) := fun P U h =>
  if H : HfLvl (ω + ν) ∧ ∀ Q U h, HgfQSpec Q U (St Q U h) then hgfScT H.1 (hgf_lev_e ν) P H.2 U h else U

/-- **The fundamental sequence of the limit level `ω + λ`**: `ω + heFs λ k`. -/
noncomputable def hgfLmOf (l : Ordinal.{0}) (hl : IsSuccLimit l) (hle : l < Om1) : HgfLm (ω + l) where
  β := fun k => ω + heFs l k
  lv := fun k => hgf_lev ((heFs_lt hl (hgf_om hle) k).trans hle)
  lt := fun k => hgf_lev_lt (heFs_lt hl (hgf_om hle) k)
  mono := fun k => (add_le_add_iff_left ω).2 (heFs_mono hl (hgf_om hle) k).le
  cof := fun t ht => by
    obtain ⟨t', ht', htt'⟩ := (lt_add_iff hl.bot_lt.ne').1 ht
    obtain ⟨k, hk⟩ := heFs_cof hl (hgf_om hle) t' ht'
    exact ⟨k, htt'.trans_lt (hgf_lev_lt hk)⟩
  lim := isSuccLimit_add ω hl

/-- **The condition at a limit**: every earlier step has the specification, and later steps extend earlier ones at
the same pseudo-base. -/
def HgfLCoh (l : Ordinal.{0}) (hle : l < Om1) (IH : ∀ ν, ν < l → HgfStTy (ω + ν)) : Prop :=
  (∀ ν (h : ν < l), ∀ Q U h', HgfQSpec Q U (IH ν h Q U h')) ∧
    ∀ ν ν' (h : ν < l) (h' : ν' < l) (hνν' : ν < ν') (Q : HgfQ (ω + ν')) (U : HgVD)
      (hU : HgSStart (hgfQPB Q) U) (c x : Ordinal.{0}),
      c < (IH ν h (Q.down (hgf_lev (h.trans hle)) (hgf_lev_lt hνν')) U hU).B →
      (IH ν' h' Q U hU).R c x = (IH ν h (Q.down (hgf_lev (h.trans hle)) (hgf_lev_lt hνν')) U hU).R c x ∧
      (IH ν' h' Q U hU).g c = (IH ν h (Q.down (hgf_lev (h.trans hle)) (hgf_lev_lt hνν')) U hU).g c

section LimDef

variable (l : Ordinal.{0}) (hl : IsSuccLimit l) (hle : l < Om1) (IH : ∀ ν, ν < l → HgfStTy (ω + ν))
  (H : HgfLCoh l hle IH)

/-- The steps of the levels `ω + λ_k`. -/
noncomputable abbrev hgfLmSt (k : ℕ) : HgfStTy ((hgfLmOf l hl hle).β k) :=
  IH (heFs l k) (heFs_lt hl (hgf_om hle) k)

include H in
theorem hgfLmSt_spec (k : ℕ) : ∀ Q U h, HgfQSpec Q U (hgfLmSt l hl hle IH k Q U h) :=
  H.1 (heFs l k) (heFs_lt hl (hgf_om hle) k)

include H in
theorem hgfLmSt_coh (P : HgfQ (ω + l)) (U : HgVD) (hU : HgSStart (hgfQPB P) U) (k : ℕ) (c x : Ordinal.{0})
    (hc : c < (hgfLmSt l hl hle IH k (P.down ((hgfLmOf l hl hle).lv k) ((hgfLmOf l hl hle).lt k)) U hU).B) :
    (hgfLmSt l hl hle IH (k + 1) (P.down ((hgfLmOf l hl hle).lv (k + 1)) ((hgfLmOf l hl hle).lt (k + 1))) U hU).R c x =
      (hgfLmSt l hl hle IH k (P.down ((hgfLmOf l hl hle).lv k) ((hgfLmOf l hl hle).lt k)) U hU).R c x ∧
    (hgfLmSt l hl hle IH (k + 1) (P.down ((hgfLmOf l hl hle).lv (k + 1)) ((hgfLmOf l hl hle).lt (k + 1))) U hU).g c =
      (hgfLmSt l hl hle IH k (P.down ((hgfLmOf l hl hle).lv k) ((hgfLmOf l hl hle).lt k)) U hU).g c :=
  H.2 (heFs l k) (heFs l (k + 1)) (heFs_lt hl (hgf_om hle) k) (heFs_lt hl (hgf_om hle) (k + 1))
    (heFs_mono hl (hgf_om hle) k) _ U hU c x hc

end LimDef

open Classical in
/-- **The limit case**: the union of the chain of the steps of the levels `ω + λ_k` (when the condition holds). -/
noncomputable def hgfLLim (l : Ordinal.{0}) (hl : IsSuccLimit l) (IH : ∀ ν, ν < l → HgfStTy (ω + ν)) :
    HgfStTy (ω + l) := fun P U h =>
  if hle : l < Om1 then
    if H : HgfLCoh l hle IH then
      hgfLmT (hgfLmOf l hl hle) (hgfLmSt l hl hle IH) (hgfLmSt_spec l hl hle IH H) P U h
        (hgfLmSt_coh l hl hle IH H P U h)
    else U
  else U

/-- **THE STEP OF EVERY COUNTABLE LEVEL `ω + ν`, BY ONE RECURSION ON THE LEVEL.** -/
noncomputable def hgfLS (ν : Ordinal.{0}) : HgfStTy (ω + ν) :=
  Ordinal.limitRecOn (motive := fun ν => HgfStTy (ω + ν)) ν hgfLS0 hgfLSucc hgfLLim

theorem hgfLS_zero : hgfLS 0 = hgfLS0 := by unfold hgfLS; rw [Ordinal.limitRecOn_zero]

theorem hgfLS_succ (ν : Ordinal.{0}) : hgfLS (ν + 1) = hgfLSucc ν (hgfLS ν) := by
  unfold hgfLS; rw [Ordinal.limitRecOn_add_one]

theorem hgfLS_limit {l : Ordinal.{0}} (hl : IsSuccLimit l) : hgfLS l = hgfLLim l hl (fun ν _ => hgfLS ν) := by
  unfold hgfLS; rw [Ordinal.limitRecOn_limit _ _ _ _ hl]

/-- The extension statement between two levels at one pseudo-base. -/
def HgfLExt (ν' ν : Ordinal.{0}) (hν : ν < Om1) (hν' : ν' < ν) : Prop :=
  ∀ (Q : HgfQ (ω + ν)) (U : HgVD) (hU : HgSStart (hgfQPB Q) U) (c x : Ordinal.{0}),
    c < (hgfLS ν' (Q.down (hgf_lev (hν'.trans hν)) (hgf_lev_lt hν')) U hU).B →
    (hgfLS ν Q U hU).R c x = (hgfLS ν' (Q.down (hgf_lev (hν'.trans hν)) (hgf_lev_lt hν')) U hU).R c x ∧
    (hgfLS ν Q U hU).g c = (hgfLS ν' (Q.down (hgf_lev (hν'.trans hν)) (hgf_lev_lt hν')) U hU).g c

/-- **THE INVARIANT**: every `hgfLS ν`, `ν < Ω₁`, has the specification of level `ω + ν` and extends every `hgfLS ν'`,
`ν' < ν`, at the same pseudo-base. -/
theorem hgfLS_inv : ∀ ν (hν : ν < Om1), (∀ Q U h, HgfQSpec Q U (hgfLS ν Q U h)) ∧
    ∀ ν' (hν' : ν' < ν), HgfLExt ν' ν hν hν' := by
  intro ν
  induction ν using WellFoundedLT.induction with
  | ind ν IH =>
  intro hν
  rcases zero_or_succ_or_isSuccLimit ν with h0 | ⟨μ, hμ⟩ | hlim
  · subst h0
    refine ⟨fun Q U h => ?_, fun ν' hν' => absurd hν' (not_lt.2 zero_le)⟩
    rw [hgfLS_zero]
    exact hgfQ_spec_om' (add_zero ω) Q U h
  · have hμ' : ν = μ + 1 := by rw [← hμ, succ_eq_add_one]
    subst hμ'
    have hμε : μ < Om1 := (lt_add_one μ).trans hν
    obtain ⟨hsp, hext⟩ := IH μ (lt_add_one μ) hμε
    have hH : HfLvl (ω + μ) ∧ ∀ Q U h, HgfQSpec Q U (hgfLS μ Q U h) := ⟨hgf_lev hμε, hsp⟩
    have e : ∀ P U h, hgfLS (μ + 1) P U h = hgfScT hH.1 (hgf_lev_e μ) P hH.2 U h := fun P U h => by
      rw [hgfLS_succ]; unfold hgfLSucc; rw [dif_pos hH]
    refine ⟨fun P U h => by rw [e]; exact hgfScT_spec hH.1 (hgf_lev_e μ) P hH.2 U h, fun ν' hν' => ?_⟩
    intro P U hU c x hc
    rw [e]
    rcases (Order.lt_add_one_iff.1 hν').lt_or_eq with hlt | heq
    · -- `ν' < μ`: through the step of level `ω + μ`
      have hB' : (hgfLS ν' (P.down (hgf_lev (hν'.trans hν)) (hgf_lev_lt hν')) U hU).B = hdNx (ω + ν') P.F :=
        ((IH ν' hν' (hν'.trans hν)).1 _ U hU).B
      have hBμ : (hgfLS μ (P.down hH.1 (hgd_lt_of_eq (hgf_lev_e μ))) U hU).B = hdNx (ω + μ) P.F :=
        (hsp (P.down hH.1 (hgd_lt_of_eq (hgf_lev_e μ))) U hU).B
      have hc' : c < (hgfLS μ (P.down hH.1 (hgd_lt_of_eq (hgf_lev_e μ))) U hU).B := by
        rw [hBμ]; rw [hB'] at hc; exact hc.trans_le (hgdNx_mono (hgf_lev_lt hlt).le _)
      obtain ⟨r1, g1⟩ := hgfScT_ext hH.1 (hgf_lev_e μ) P hH.2 U hU hc' x
      obtain ⟨r2, g2⟩ := hext ν' hlt (P.down hH.1 (hgd_lt_of_eq (hgf_lev_e μ))) U hU c x hc
      exact ⟨r1.trans r2, g1.trans g2⟩
    · subst heq
      exact hgfScT_ext hH.1 (hgf_lev_e _) P hH.2 U hU hc x
  · -- the limit: the union of the chain
    have hcoh : HgfLCoh ν hν (fun ν' _ => hgfLS ν') :=
      ⟨fun ν' h => (IH ν' h (h.trans hν)).1, fun ν₁ ν₂ h₁ h₂ h12 Q U hU c x hc =>
        (IH ν₂ h₂ (h₂.trans hν)).2 ν₁ h12 Q U hU c x hc⟩
    have e : ∀ P U h, hgfLS ν P U h = hgfLmT (hgfLmOf ν hlim hν) (hgfLmSt ν hlim hν (fun ν' _ => hgfLS ν'))
        (hgfLmSt_spec ν hlim hν _ hcoh) P U h (hgfLmSt_coh ν hlim hν _ hcoh P U h) := fun P U h => by
      rw [hgfLS_limit hlim]; unfold hgfLLim; rw [dif_pos hν, dif_pos hcoh]
    refine ⟨fun P U h => by rw [e]; exact hgfLmT_spec _ _ _ _ _ _ _, fun ν' hν' => ?_⟩
    intro P U hU c x hc
    rw [e]
    obtain ⟨k, hk⟩ := heFs_cof hlim (hgf_om hν) ν' hν'
    have hkl := heFs_lt hlim (hgf_om hν) k
    obtain ⟨hspk, hextk⟩ := IH _ hkl (hkl.trans hν)
    have hc' : c < (hgfLS (heFs ν k) (P.down (hgf_lev (hkl.trans hν)) (hgf_lev_lt hkl)) U hU).B := by
      rw [(hspk (P.down (hgf_lev (hkl.trans hν)) (hgf_lev_lt hkl)) U hU).B]
      rw [((IH ν' hν' (hν'.trans hν)).1 (P.down (hgf_lev (hν'.trans hν)) (hgf_lev_lt hν')) U hU).B] at hc
      exact hc.trans_le (hgdNx_mono (hgf_lev_lt hk).le _)
    obtain ⟨r1, g1⟩ := hgfLmT_ext (hgfLmOf ν hlim hν) (hgfLmSt ν hlim hν (fun ν' _ => hgfLS ν'))
      (hgfLmSt_spec ν hlim hν _ hcoh) P U hU (hgfLmSt_coh ν hlim hν _ hcoh P U hU) k hc' x
    obtain ⟨r2, g2⟩ := hextk ν' hk (P.down (hgf_lev (hkl.trans hν)) (hgf_lev_lt hkl)) U hU c x hc
    exact ⟨r1.trans r2, g1.trans g2⟩

/-- **THE STEP OF EVERY COUNTABLE LEVEL HAS THE SPECIFICATION.** -/
theorem hgfLS_spec {ν : Ordinal.{0}} (hν : ν < Om1) (Q : HgfQ (ω + ν)) (U : HgVD) (h : HgSStart (hgfQPB Q) U) :
    HgfQSpec Q U (hgfLS ν Q U h) := (hgfLS_inv ν hν).1 Q U h

end Googology.Trans.PoR.InaccPsi.R2.Hg
