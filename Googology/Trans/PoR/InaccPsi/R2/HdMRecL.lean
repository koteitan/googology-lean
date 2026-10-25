import Googology.Trans.PoR.InaccPsi.R2.HdMSc

/-!
# HdMRecL: THE STEP OF EVERY CONSTANT LEVEL `ω ≤ α < ε₀`, BY ONE RECURSION ON THE LEVEL

`hdLS ν` is a step of level `ω + ν` (a function from pseudo-bases `P` of level `ω + ν` and starts `U` of the stage
at `P` to digit systems), defined by `Ordinal.limitRecOn` on `ν`:

* `ν = 0`: the gated `ω`-step `Hd.hdStep`;
* `ν + 1`: **one more offset recursion** (`Hd.hdScT`): the union of all gated offsets over `P` as a base of level
  `ω + ν`, started at the step of level `ω + ν` at `P`;
* a limit `λ < ε₀`: **the union over the lower levels** (`Hd.hdLmT`): the gated `ω`-chain of the steps of the levels
  `ω + λ_k` (`λ_k = Gp.gpFs λ k`) at `P`.

The invariant (`hdLS_inv`): every `hdLS ν`, `ν < ε₀`, has the specification `Hd.HdQSpec` of level `ω + ν` (bound
`hdNx (ω + ν) F`), and extends every `hdLS ν'`, `ν' < ν`, at the same pseudo-base.

* `HdStTy`, `hd_lev`, `hd_lev_lt`, `hd_lev_e`, `hdQ_spec_om'`, `hdLS0`, `hdLSucc`, `hdLmOf`, `HdLCoh`, `hdLLim`,
  `hdLS` (**THE STEP OF EVERY CONSTANT LEVEL**), `hdLS_zero`, `hdLS_succ`, `hdLS_limit`, `hdLS_inv` (**THE
  INVARIANT**), `hdLS_spec`.

No new axiom.  New definitions: `HdStTy`, `hdLS0`, `hdLSucc`, `hdLmOf`, `HdLCoh`, `hdLLim`, `hdLS`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hd

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
abbrev HdStTy (μ : Ordinal.{0}) : Type 1 := ∀ (Q : HdQ μ) (U : HcVD), HcSStart (hdQPB Q) U → HcVD

theorem hd_lev {ν : Ordinal.{0}} (hν : ν < ε₀) : HdLvl (ω + ν) :=
  ⟨le_self_add, (inE_indec hc_eps0_E).add_lt (omega0_lt_inE hc_eps0_E) hν⟩

theorem hd_lev_lt {ν ν' : Ordinal.{0}} (h : ν < ν') : ω + ν < ω + ν' := (add_lt_add_iff_left ω).2 h

theorem hd_lev_e (ν : Ordinal.{0}) : ω + (ν + 1) = ω + ν + 1 := (add_assoc _ _ _).symm

/-- **The `ω`-step at a pseudo-base of level `μ = ω` has the specification.** -/
theorem hdQ_spec_om' {μ : Ordinal.{0}} (hμ : μ = ω) (Q : HdQ μ) (U : HcVD) (h : HcSStart (hdQPB Q) U) :
    HdQSpec Q U (hdStep Q.toP U h) := by
  subst hμ; exact hdQ_spec_om Q U h

/-! ## The three cases -/

/-- The step of level `ω + 0`: the `ω`-step. -/
noncomputable def hdLS0 : HdStTy (ω + 0) := fun Q U h => hdStep Q.toP U h

open Classical in
/-- **The successor case**: one more offset recursion (when the step of level `ω + ν` has the specification). -/
noncomputable def hdLSucc (ν : Ordinal.{0}) (St : HdStTy (ω + ν)) : HdStTy (ω + (ν + 1)) := fun P U h =>
  if H : HdLvl (ω + ν) ∧ ∀ Q U h, HdQSpec Q U (St Q U h) then hdScT H.1 (hd_lev_e ν) P H.2 U h else U

/-- **The fundamental sequence of the limit level `ω + λ`**: `ω + gpFs λ k`. -/
noncomputable def hdLmOf (l : Ordinal.{0}) (hl : IsSuccLimit l) (hle : l < ε₀) : HdLm (ω + l) where
  β := fun k => ω + gpFs l k
  lv := fun k => hd_lev ((gpFs_lt hl hle k).trans hle)
  lt := fun k => hd_lev_lt (gpFs_lt hl hle k)
  mono := fun k => (add_le_add_iff_left ω).2 (gpFs_mono hl hle k).le
  cof := fun t ht => by
    obtain ⟨t', ht', htt'⟩ := (lt_add_iff hl.bot_lt.ne').1 ht
    obtain ⟨k, hk⟩ := gpFs_cof hl hle t' ht'
    exact ⟨k, htt'.trans_lt (hd_lev_lt hk)⟩
  lim := isSuccLimit_add ω hl

/-- **The condition at a limit**: every earlier step has the specification, and later steps extend earlier ones at
the same pseudo-base. -/
def HdLCoh (l : Ordinal.{0}) (hle : l < ε₀) (IH : ∀ ν, ν < l → HdStTy (ω + ν)) : Prop :=
  (∀ ν (h : ν < l), ∀ Q U h', HdQSpec Q U (IH ν h Q U h')) ∧
    ∀ ν ν' (h : ν < l) (h' : ν' < l) (hνν' : ν < ν') (Q : HdQ (ω + ν')) (U : HcVD)
      (hU : HcSStart (hdQPB Q) U) (c x : Ordinal.{0}),
      c < (IH ν h (Q.down (hd_lev (h.trans hle)) (hd_lev_lt hνν')) U hU).B →
      (IH ν' h' Q U hU).R c x = (IH ν h (Q.down (hd_lev (h.trans hle)) (hd_lev_lt hνν')) U hU).R c x ∧
      (IH ν' h' Q U hU).g c = (IH ν h (Q.down (hd_lev (h.trans hle)) (hd_lev_lt hνν')) U hU).g c

section LimDef

variable (l : Ordinal.{0}) (hl : IsSuccLimit l) (hle : l < ε₀) (IH : ∀ ν, ν < l → HdStTy (ω + ν))
  (H : HdLCoh l hle IH)

/-- The steps of the levels `ω + λ_k`. -/
noncomputable abbrev hdLmSt (k : ℕ) : HdStTy ((hdLmOf l hl hle).β k) := IH (gpFs l k) (gpFs_lt hl hle k)

include H in
theorem hdLmSt_spec (k : ℕ) : ∀ Q U h, HdQSpec Q U (hdLmSt l hl hle IH k Q U h) :=
  H.1 (gpFs l k) (gpFs_lt hl hle k)

include H in
theorem hdLmSt_coh (P : HdQ (ω + l)) (U : HcVD) (hU : HcSStart (hdQPB P) U) (k : ℕ) (c x : Ordinal.{0})
    (hc : c < (hdLmSt l hl hle IH k (P.down ((hdLmOf l hl hle).lv k) ((hdLmOf l hl hle).lt k)) U hU).B) :
    (hdLmSt l hl hle IH (k + 1) (P.down ((hdLmOf l hl hle).lv (k + 1)) ((hdLmOf l hl hle).lt (k + 1))) U hU).R c x =
      (hdLmSt l hl hle IH k (P.down ((hdLmOf l hl hle).lv k) ((hdLmOf l hl hle).lt k)) U hU).R c x ∧
    (hdLmSt l hl hle IH (k + 1) (P.down ((hdLmOf l hl hle).lv (k + 1)) ((hdLmOf l hl hle).lt (k + 1))) U hU).g c =
      (hdLmSt l hl hle IH k (P.down ((hdLmOf l hl hle).lv k) ((hdLmOf l hl hle).lt k)) U hU).g c :=
  H.2 (gpFs l k) (gpFs l (k + 1)) (gpFs_lt hl hle k) (gpFs_lt hl hle (k + 1)) (gpFs_mono hl hle k) _ U hU c x hc

end LimDef

open Classical in
/-- **The limit case**: the union of the chain of the steps of the levels `ω + λ_k` (when the condition holds). -/
noncomputable def hdLLim (l : Ordinal.{0}) (hl : IsSuccLimit l) (IH : ∀ ν, ν < l → HdStTy (ω + ν)) :
    HdStTy (ω + l) := fun P U h =>
  if hle : l < ε₀ then
    if H : HdLCoh l hle IH then
      hdLmT (hdLmOf l hl hle) (hdLmSt l hl hle IH) (hdLmSt_spec l hl hle IH H) P U h
        (hdLmSt_coh l hl hle IH H P U h)
    else U
  else U

/-- **THE STEP OF EVERY CONSTANT LEVEL `ω + ν`, BY ONE RECURSION ON THE LEVEL.** -/
noncomputable def hdLS (ν : Ordinal.{0}) : HdStTy (ω + ν) :=
  Ordinal.limitRecOn (motive := fun ν => HdStTy (ω + ν)) ν hdLS0 hdLSucc hdLLim

theorem hdLS_zero : hdLS 0 = hdLS0 := by unfold hdLS; rw [Ordinal.limitRecOn_zero]

theorem hdLS_succ (ν : Ordinal.{0}) : hdLS (ν + 1) = hdLSucc ν (hdLS ν) := by
  unfold hdLS; rw [Ordinal.limitRecOn_add_one]

theorem hdLS_limit {l : Ordinal.{0}} (hl : IsSuccLimit l) : hdLS l = hdLLim l hl (fun ν _ => hdLS ν) := by
  unfold hdLS; rw [Ordinal.limitRecOn_limit _ _ _ _ hl]

/-- The extension statement between two levels at one pseudo-base. -/
def HdLExt (ν' ν : Ordinal.{0}) (hν : ν < ε₀) (hν' : ν' < ν) : Prop :=
  ∀ (Q : HdQ (ω + ν)) (U : HcVD) (hU : HcSStart (hdQPB Q) U) (c x : Ordinal.{0}),
    c < (hdLS ν' (Q.down (hd_lev (hν'.trans hν)) (hd_lev_lt hν')) U hU).B →
    (hdLS ν Q U hU).R c x = (hdLS ν' (Q.down (hd_lev (hν'.trans hν)) (hd_lev_lt hν')) U hU).R c x ∧
    (hdLS ν Q U hU).g c = (hdLS ν' (Q.down (hd_lev (hν'.trans hν)) (hd_lev_lt hν')) U hU).g c

/-- **THE INVARIANT**: every `hdLS ν`, `ν < ε₀`, has the specification of level `ω + ν` and extends every `hdLS ν'`,
`ν' < ν`, at the same pseudo-base. -/
theorem hdLS_inv : ∀ ν (hν : ν < ε₀), (∀ Q U h, HdQSpec Q U (hdLS ν Q U h)) ∧
    ∀ ν' (hν' : ν' < ν), HdLExt ν' ν hν hν' := by
  intro ν
  induction ν using WellFoundedLT.induction with
  | ind ν IH =>
  intro hν
  rcases zero_or_succ_or_isSuccLimit ν with h0 | ⟨μ, hμ⟩ | hlim
  · subst h0
    refine ⟨fun Q U h => ?_, fun ν' hν' => absurd hν' (not_lt.2 zero_le)⟩
    rw [hdLS_zero]
    exact hdQ_spec_om' (add_zero ω) Q U h
  · have hμ' : ν = μ + 1 := by rw [← hμ, succ_eq_add_one]
    subst hμ'
    have hμε : μ < ε₀ := (lt_add_one μ).trans hν
    obtain ⟨hsp, hext⟩ := IH μ (lt_add_one μ) hμε
    have hH : HdLvl (ω + μ) ∧ ∀ Q U h, HdQSpec Q U (hdLS μ Q U h) := ⟨hd_lev hμε, hsp⟩
    have e : ∀ P U h, hdLS (μ + 1) P U h = hdScT hH.1 (hd_lev_e μ) P hH.2 U h := fun P U h => by
      rw [hdLS_succ]; unfold hdLSucc; rw [dif_pos hH]
    refine ⟨fun P U h => by rw [e]; exact hdScT_spec hH.1 (hd_lev_e μ) P hH.2 U h, fun ν' hν' => ?_⟩
    intro P U hU c x hc
    rw [e]
    rcases (Order.lt_add_one_iff.1 hν').lt_or_eq with hlt | heq
    · -- `ν' < μ`: through the step of level `ω + μ`
      have hB' : (hdLS ν' (P.down (hd_lev (hν'.trans hν)) (hd_lev_lt hν')) U hU).B = hdNx (ω + ν') P.F :=
        ((IH ν' hν' (hν'.trans hν)).1 _ U hU).B
      have hBμ : (hdLS μ (P.down hH.1 (hd_lt_of_eq (hd_lev_e μ))) U hU).B = hdNx (ω + μ) P.F :=
        (hsp (P.down hH.1 (hd_lt_of_eq (hd_lev_e μ))) U hU).B
      have hc' : c < (hdLS μ (P.down hH.1 (hd_lt_of_eq (hd_lev_e μ))) U hU).B := by
        rw [hBμ]; rw [hB'] at hc; exact hc.trans_le (hdNx_mono (hd_lev_lt hlt).le _)
      obtain ⟨r1, g1⟩ := hdScT_ext hH.1 (hd_lev_e μ) P hH.2 U hU hc' x
      obtain ⟨r2, g2⟩ := hext ν' hlt (P.down hH.1 (hd_lt_of_eq (hd_lev_e μ))) U hU c x hc
      exact ⟨r1.trans r2, g1.trans g2⟩
    · subst heq
      exact hdScT_ext hH.1 (hd_lev_e _) P hH.2 U hU hc x
  · -- the limit: the union of the chain
    have hcoh : HdLCoh ν hν (fun ν' _ => hdLS ν') :=
      ⟨fun ν' h => (IH ν' h (h.trans hν)).1, fun ν₁ ν₂ h₁ h₂ h12 Q U hU c x hc =>
        (IH ν₂ h₂ (h₂.trans hν)).2 ν₁ h12 Q U hU c x hc⟩
    have e : ∀ P U h, hdLS ν P U h = hdLmT (hdLmOf ν hlim hν) (hdLmSt ν hlim hν (fun ν' _ => hdLS ν'))
        (hdLmSt_spec ν hlim hν _ hcoh) P U h (hdLmSt_coh ν hlim hν _ hcoh P U h) := fun P U h => by
      rw [hdLS_limit hlim]; unfold hdLLim; rw [dif_pos hν, dif_pos hcoh]
    refine ⟨fun P U h => by rw [e]; exact hdLmT_spec _ _ _ _ _ _ _, fun ν' hν' => ?_⟩
    intro P U hU c x hc
    rw [e]
    obtain ⟨k, hk⟩ := gpFs_cof hlim hν ν' hν'
    have hkl := gpFs_lt hlim hν k
    obtain ⟨hspk, hextk⟩ := IH _ hkl (hkl.trans hν)
    have hc' : c < (hdLS (gpFs ν k) (P.down (hd_lev (hkl.trans hν)) (hd_lev_lt hkl)) U hU).B := by
      rw [(hspk (P.down (hd_lev (hkl.trans hν)) (hd_lev_lt hkl)) U hU).B]
      rw [((IH ν' hν' (hν'.trans hν)).1 (P.down (hd_lev (hν'.trans hν)) (hd_lev_lt hν')) U hU).B] at hc
      exact hc.trans_le (hdNx_mono (hd_lev_lt hk).le _)
    obtain ⟨r1, g1⟩ := hdLmT_ext (hdLmOf ν hlim hν) (hdLmSt ν hlim hν (fun ν' _ => hdLS ν'))
      (hdLmSt_spec ν hlim hν _ hcoh) P U hU (hdLmSt_coh ν hlim hν _ hcoh P U hU) k hc' x
    obtain ⟨r2, g2⟩ := hextk ν' hk (P.down (hd_lev (hkl.trans hν)) (hd_lev_lt hkl)) U hU c x hc
    exact ⟨r1.trans r2, g1.trans g2⟩

/-- **THE STEP OF EVERY CONSTANT LEVEL HAS THE SPECIFICATION.** -/
theorem hdLS_spec {ν : Ordinal.{0}} (hν : ν < ε₀) (Q : HdQ (ω + ν)) (U : HcVD) (h : HcSStart (hdQPB Q) U) :
    HdQSpec Q U (hdLS ν Q U h) := (hdLS_inv ν hν).1 Q U h

end Googology.Trans.PoR.InaccPsi.R2.Hd
