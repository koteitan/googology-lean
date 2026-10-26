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

/-!
# HgdMRecL: THE STEP OF EVERY CONSTANT LEVEL `ω ≤ α < ε₀`, BY ONE RECURSION ON THE LEVEL

(Textual copy of `Hd.HdMRecL` for `Hg.HgVD`: bound fields `< Γ_{x+2}` in place of `≤ B_x(x)` (`Hc.hcBR`); the proofs
are unchanged except where the bound enters.  Names: prefix `hg`/`Hg` (from `hc`/`Hc`), `hgd`/`Hgd` (from `hd`/`Hd`),
`hgf`/`Hgf` (from `hf`/`Hf`), `hge`/`Hge` (from `he`/`He`).)

`hgdLS ν` is a step of level `ω + ν` (a function from pseudo-bases `P` of level `ω + ν` and starts `U` of the stage
at `P` to digit systems), defined by `Ordinal.limitRecOn` on `ν`:

* `ν = 0`: the gated `ω`-step `Hg.hgdStep`;
* `ν + 1`: **one more offset recursion** (`Hg.hgdScT`): the union of all gated offsets over `P` as a base of level
  `ω + ν`, started at the step of level `ω + ν` at `P`;
* a limit `λ < ε₀`: **the union over the lower levels** (`Hg.hgdLmT`): the gated `ω`-chain of the steps of the levels
  `ω + λ_k` (`λ_k = Gp.gpFs λ k`) at `P`.

The invariant (`hgdLS_inv`): every `hgdLS ν`, `ν < ε₀`, has the specification `Hg.HgdQSpec` of level `ω + ν` (bound
`hdNx (ω + ν) F`), and extends every `hgdLS ν'`, `ν' < ν`, at the same pseudo-base.

* `HgdStTy`, `hgd_lev`, `hgd_lev_lt`, `hgd_lev_e`, `hgdQ_spec_om'`, `hgdLS0`, `hgdLSucc`, `hgdLmOf`, `HgdLCoh`,
  `hgdLLim`,
  `hgdLS` (**THE STEP OF EVERY CONSTANT LEVEL**), `hgdLS_zero`, `hgdLS_succ`, `hgdLS_limit`, `hgdLS_inv` (**THE
  INVARIANT**), `hgdLS_spec`.

No new axiom.  New definitions: `HgdStTy`, `hgdLS0`, `hgdLSucc`, `hgdLmOf`, `HgdLCoh`, `hgdLLim`, `hgdLS`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hg

open Googology.Trans.PoR.InaccPsi.R2.Hc
open Googology.Trans.PoR.InaccPsi.R2.Hd

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
abbrev HgdStTy (μ : Ordinal.{0}) : Type 1 := ∀ (Q : HgdQ μ) (U : HgVD), HgSStart (hgdQPB Q) U → HgVD

theorem hgd_lev {ν : Ordinal.{0}} (hν : ν < ε₀) : HdLvl (ω + ν) :=
  ⟨le_self_add, (inE_indec hc_eps0_E).add_lt (omega0_lt_inE hc_eps0_E) hν⟩

theorem hgd_lev_lt {ν ν' : Ordinal.{0}} (h : ν < ν') : ω + ν < ω + ν' := (add_lt_add_iff_left ω).2 h

theorem hgd_lev_e (ν : Ordinal.{0}) : ω + (ν + 1) = ω + ν + 1 := (add_assoc _ _ _).symm

/-- **The `ω`-step at a pseudo-base of level `μ = ω` has the specification.** -/
theorem hgdQ_spec_om' {μ : Ordinal.{0}} (hμ : μ = ω) (Q : HgdQ μ) (U : HgVD) (h : HgSStart (hgdQPB Q) U) :
    HgdQSpec Q U (hgdStep Q.toP U h) := by
  subst hμ; exact hgdQ_spec_om Q U h

/-! ## The three cases -/

/-- The step of level `ω + 0`: the `ω`-step. -/
noncomputable def hgdLS0 : HgdStTy (ω + 0) := fun Q U h => hgdStep Q.toP U h

open Classical in
/-- **The successor case**: one more offset recursion (when the step of level `ω + ν` has the specification). -/
noncomputable def hgdLSucc (ν : Ordinal.{0}) (St : HgdStTy (ω + ν)) : HgdStTy (ω + (ν + 1)) := fun P U h =>
  if H : HdLvl (ω + ν) ∧ ∀ Q U h, HgdQSpec Q U (St Q U h) then hgdScT H.1 (hgd_lev_e ν) P H.2 U h else U

/-- **The fundamental sequence of the limit level `ω + λ`**: `ω + gpFs λ k`. -/
noncomputable def hgdLmOf (l : Ordinal.{0}) (hl : IsSuccLimit l) (hle : l < ε₀) : HgdLm (ω + l) where
  β := fun k => ω + gpFs l k
  lv := fun k => hgd_lev ((gpFs_lt hl hle k).trans hle)
  lt := fun k => hgd_lev_lt (gpFs_lt hl hle k)
  mono := fun k => (add_le_add_iff_left ω).2 (gpFs_mono hl hle k).le
  cof := fun t ht => by
    obtain ⟨t', ht', htt'⟩ := (lt_add_iff hl.bot_lt.ne').1 ht
    obtain ⟨k, hk⟩ := gpFs_cof hl hle t' ht'
    exact ⟨k, htt'.trans_lt (hgd_lev_lt hk)⟩
  lim := isSuccLimit_add ω hl

/-- **The condition at a limit**: every earlier step has the specification, and later steps extend earlier ones at
the same pseudo-base. -/
def HgdLCoh (l : Ordinal.{0}) (hle : l < ε₀) (IH : ∀ ν, ν < l → HgdStTy (ω + ν)) : Prop :=
  (∀ ν (h : ν < l), ∀ Q U h', HgdQSpec Q U (IH ν h Q U h')) ∧
    ∀ ν ν' (h : ν < l) (h' : ν' < l) (hνν' : ν < ν') (Q : HgdQ (ω + ν')) (U : HgVD)
      (hU : HgSStart (hgdQPB Q) U) (c x : Ordinal.{0}),
      c < (IH ν h (Q.down (hgd_lev (h.trans hle)) (hgd_lev_lt hνν')) U hU).B →
      (IH ν' h' Q U hU).R c x = (IH ν h (Q.down (hgd_lev (h.trans hle)) (hgd_lev_lt hνν')) U hU).R c x ∧
      (IH ν' h' Q U hU).g c = (IH ν h (Q.down (hgd_lev (h.trans hle)) (hgd_lev_lt hνν')) U hU).g c

section LimDef

variable (l : Ordinal.{0}) (hl : IsSuccLimit l) (hle : l < ε₀) (IH : ∀ ν, ν < l → HgdStTy (ω + ν))
  (H : HgdLCoh l hle IH)

/-- The steps of the levels `ω + λ_k`. -/
noncomputable abbrev hgdLmSt (k : ℕ) : HgdStTy ((hgdLmOf l hl hle).β k) := IH (gpFs l k) (gpFs_lt hl hle k)

include H in
theorem hgdLmSt_spec (k : ℕ) : ∀ Q U h, HgdQSpec Q U (hgdLmSt l hl hle IH k Q U h) :=
  H.1 (gpFs l k) (gpFs_lt hl hle k)

include H in
theorem hgdLmSt_coh (P : HgdQ (ω + l)) (U : HgVD) (hU : HgSStart (hgdQPB P) U) (k : ℕ) (c x : Ordinal.{0})
    (hc : c < (hgdLmSt l hl hle IH k (P.down ((hgdLmOf l hl hle).lv k) ((hgdLmOf l hl hle).lt k)) U hU).B) :
    (hgdLmSt l hl hle IH (k + 1) (P.down ((hgdLmOf l hl hle).lv (k + 1)) ((hgdLmOf l hl hle).lt (k + 1))) U hU).R c x =
      (hgdLmSt l hl hle IH k (P.down ((hgdLmOf l hl hle).lv k) ((hgdLmOf l hl hle).lt k)) U hU).R c x ∧
    (hgdLmSt l hl hle IH (k + 1) (P.down ((hgdLmOf l hl hle).lv (k + 1)) ((hgdLmOf l hl hle).lt (k + 1))) U hU).g c =
      (hgdLmSt l hl hle IH k (P.down ((hgdLmOf l hl hle).lv k) ((hgdLmOf l hl hle).lt k)) U hU).g c :=
  H.2 (gpFs l k) (gpFs l (k + 1)) (gpFs_lt hl hle k) (gpFs_lt hl hle (k + 1)) (gpFs_mono hl hle k) _ U hU c x hc

end LimDef

open Classical in
/-- **The limit case**: the union of the chain of the steps of the levels `ω + λ_k` (when the condition holds). -/
noncomputable def hgdLLim (l : Ordinal.{0}) (hl : IsSuccLimit l) (IH : ∀ ν, ν < l → HgdStTy (ω + ν)) :
    HgdStTy (ω + l) := fun P U h =>
  if hle : l < ε₀ then
    if H : HgdLCoh l hle IH then
      hgdLmT (hgdLmOf l hl hle) (hgdLmSt l hl hle IH) (hgdLmSt_spec l hl hle IH H) P U h
        (hgdLmSt_coh l hl hle IH H P U h)
    else U
  else U

/-- **THE STEP OF EVERY CONSTANT LEVEL `ω + ν`, BY ONE RECURSION ON THE LEVEL.** -/
noncomputable def hgdLS (ν : Ordinal.{0}) : HgdStTy (ω + ν) :=
  Ordinal.limitRecOn (motive := fun ν => HgdStTy (ω + ν)) ν hgdLS0 hgdLSucc hgdLLim

theorem hgdLS_zero : hgdLS 0 = hgdLS0 := by unfold hgdLS; rw [Ordinal.limitRecOn_zero]

theorem hgdLS_succ (ν : Ordinal.{0}) : hgdLS (ν + 1) = hgdLSucc ν (hgdLS ν) := by
  unfold hgdLS; rw [Ordinal.limitRecOn_add_one]

theorem hgdLS_limit {l : Ordinal.{0}} (hl : IsSuccLimit l) : hgdLS l = hgdLLim l hl (fun ν _ => hgdLS ν) := by
  unfold hgdLS; rw [Ordinal.limitRecOn_limit _ _ _ _ hl]

/-- The extension statement between two levels at one pseudo-base. -/
def HgdLExt (ν' ν : Ordinal.{0}) (hν : ν < ε₀) (hν' : ν' < ν) : Prop :=
  ∀ (Q : HgdQ (ω + ν)) (U : HgVD) (hU : HgSStart (hgdQPB Q) U) (c x : Ordinal.{0}),
    c < (hgdLS ν' (Q.down (hgd_lev (hν'.trans hν)) (hgd_lev_lt hν')) U hU).B →
    (hgdLS ν Q U hU).R c x = (hgdLS ν' (Q.down (hgd_lev (hν'.trans hν)) (hgd_lev_lt hν')) U hU).R c x ∧
    (hgdLS ν Q U hU).g c = (hgdLS ν' (Q.down (hgd_lev (hν'.trans hν)) (hgd_lev_lt hν')) U hU).g c

/-- **THE INVARIANT**: every `hgdLS ν`, `ν < ε₀`, has the specification of level `ω + ν` and extends every `hgdLS ν'`,
`ν' < ν`, at the same pseudo-base. -/
theorem hgdLS_inv : ∀ ν (hν : ν < ε₀), (∀ Q U h, HgdQSpec Q U (hgdLS ν Q U h)) ∧
    ∀ ν' (hν' : ν' < ν), HgdLExt ν' ν hν hν' := by
  intro ν
  induction ν using WellFoundedLT.induction with
  | ind ν IH =>
  intro hν
  rcases zero_or_succ_or_isSuccLimit ν with h0 | ⟨μ, hμ⟩ | hlim
  · subst h0
    refine ⟨fun Q U h => ?_, fun ν' hν' => absurd hν' (not_lt.2 zero_le)⟩
    rw [hgdLS_zero]
    exact hgdQ_spec_om' (add_zero ω) Q U h
  · have hμ' : ν = μ + 1 := by rw [← hμ, succ_eq_add_one]
    subst hμ'
    have hμε : μ < ε₀ := (lt_add_one μ).trans hν
    obtain ⟨hsp, hext⟩ := IH μ (lt_add_one μ) hμε
    have hH : HdLvl (ω + μ) ∧ ∀ Q U h, HgdQSpec Q U (hgdLS μ Q U h) := ⟨hgd_lev hμε, hsp⟩
    have e : ∀ P U h, hgdLS (μ + 1) P U h = hgdScT hH.1 (hgd_lev_e μ) P hH.2 U h := fun P U h => by
      rw [hgdLS_succ]; unfold hgdLSucc; rw [dif_pos hH]
    refine ⟨fun P U h => by rw [e]; exact hgdScT_spec hH.1 (hgd_lev_e μ) P hH.2 U h, fun ν' hν' => ?_⟩
    intro P U hU c x hc
    rw [e]
    rcases (Order.lt_add_one_iff.1 hν').lt_or_eq with hlt | heq
    · -- `ν' < μ`: through the step of level `ω + μ`
      have hB' : (hgdLS ν' (P.down (hgd_lev (hν'.trans hν)) (hgd_lev_lt hν')) U hU).B = hdNx (ω + ν') P.F :=
        ((IH ν' hν' (hν'.trans hν)).1 _ U hU).B
      have hBμ : (hgdLS μ (P.down hH.1 (hgd_lt_of_eq (hgd_lev_e μ))) U hU).B = hdNx (ω + μ) P.F :=
        (hsp (P.down hH.1 (hgd_lt_of_eq (hgd_lev_e μ))) U hU).B
      have hc' : c < (hgdLS μ (P.down hH.1 (hgd_lt_of_eq (hgd_lev_e μ))) U hU).B := by
        rw [hBμ]; rw [hB'] at hc; exact hc.trans_le (hgdNx_mono (hgd_lev_lt hlt).le _)
      obtain ⟨r1, g1⟩ := hgdScT_ext hH.1 (hgd_lev_e μ) P hH.2 U hU hc' x
      obtain ⟨r2, g2⟩ := hext ν' hlt (P.down hH.1 (hgd_lt_of_eq (hgd_lev_e μ))) U hU c x hc
      exact ⟨r1.trans r2, g1.trans g2⟩
    · subst heq
      exact hgdScT_ext hH.1 (hgd_lev_e _) P hH.2 U hU hc x
  · -- the limit: the union of the chain
    have hcoh : HgdLCoh ν hν (fun ν' _ => hgdLS ν') :=
      ⟨fun ν' h => (IH ν' h (h.trans hν)).1, fun ν₁ ν₂ h₁ h₂ h12 Q U hU c x hc =>
        (IH ν₂ h₂ (h₂.trans hν)).2 ν₁ h12 Q U hU c x hc⟩
    have e : ∀ P U h, hgdLS ν P U h = hgdLmT (hgdLmOf ν hlim hν) (hgdLmSt ν hlim hν (fun ν' _ => hgdLS ν'))
        (hgdLmSt_spec ν hlim hν _ hcoh) P U h (hgdLmSt_coh ν hlim hν _ hcoh P U h) := fun P U h => by
      rw [hgdLS_limit hlim]; unfold hgdLLim; rw [dif_pos hν, dif_pos hcoh]
    refine ⟨fun P U h => by rw [e]; exact hgdLmT_spec _ _ _ _ _ _ _, fun ν' hν' => ?_⟩
    intro P U hU c x hc
    rw [e]
    obtain ⟨k, hk⟩ := gpFs_cof hlim hν ν' hν'
    have hkl := gpFs_lt hlim hν k
    obtain ⟨hspk, hextk⟩ := IH _ hkl (hkl.trans hν)
    have hc' : c < (hgdLS (gpFs ν k) (P.down (hgd_lev (hkl.trans hν)) (hgd_lev_lt hkl)) U hU).B := by
      rw [(hspk (P.down (hgd_lev (hkl.trans hν)) (hgd_lev_lt hkl)) U hU).B]
      rw [((IH ν' hν' (hν'.trans hν)).1 (P.down (hgd_lev (hν'.trans hν)) (hgd_lev_lt hν')) U hU).B] at hc
      exact hc.trans_le (hgdNx_mono (hgd_lev_lt hk).le _)
    obtain ⟨r1, g1⟩ := hgdLmT_ext (hgdLmOf ν hlim hν) (hgdLmSt ν hlim hν (fun ν' _ => hgdLS ν'))
      (hgdLmSt_spec ν hlim hν _ hcoh) P U hU (hgdLmSt_coh ν hlim hν _ hcoh P U hU) k hc' x
    obtain ⟨r2, g2⟩ := hextk ν' hk (P.down (hgd_lev (hkl.trans hν)) (hgd_lev_lt hkl)) U hU c x hc
    exact ⟨r1.trans r2, g1.trans g2⟩

/-- **THE STEP OF EVERY CONSTANT LEVEL HAS THE SPECIFICATION.** -/
theorem hgdLS_spec {ν : Ordinal.{0}} (hν : ν < ε₀) (Q : HgdQ (ω + ν)) (U : HgVD) (h : HgSStart (hgdQPB Q) U) :
    HgdQSpec Q U (hgdLS ν Q U h) := (hgdLS_inv ν hν).1 Q U h

end Googology.Trans.PoR.InaccPsi.R2.Hg
