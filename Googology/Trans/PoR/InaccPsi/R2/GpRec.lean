import Googology.Trans.PoR.InaccPsi.R2.GpFs

/-!
# ONE RECURSION OVER ALL `ε`-INDICES BELOW `ε₀`: the digit system `gpD ν` at the bound `ε_{G+ν}` for every `ν < ε₀`

`G = Γ_{Ω₁+1}`.  By transfinite recursion on `ν` (`Ordinal.limitRecOn`):

* `gpD 0 = goGl` (the codes below `G`, `R2.GoGl`), `gpD (ν+1) = (gpD ν).step` (the generic hereditary step,
  `R2.GoStep`), `gpD λ =` the union (`R2.GoLim`, `GoSeq.toCh`, `GoCh.lim`) of the chain `gpD (gpFs λ k)` along any
  fundamental sequence of `λ` (`R2.GpFs`).

The coherence of the systems (a later system keeps the readings and gates of an earlier one) is PART OF THE INDUCTION
(`GpInv`): so the union at `λ` reads every code `c < ε_{G+β}`, `β < λ`, exactly as `gpD β` does, whatever sequence was
used (`gpD_ext`), and no comparison of operations built from different fundamental sequences is needed.

* `gpOff` (`ν ↦ ν` for finite `ν`, `ν + 1` otherwise: the offset with `ϑˣ(Ω₁ + Γ_{x+1} + gpOff ν) = ε_{b(x)+1}`), `gpI`;
* `GpInv`, `GpTop`, `gpChain`, `gpExt`, `gpLim`, `gpD` (**THE RECURSION**), `gpD_zero`, `gpD_succ`, `gpD_limit`;
* `gp_inv` (**THE INVARIANT AT EVERY `ν < ε₀`**), `gpD_B` (**`(gpD ν).B = φ(1, G + ν) = ε_{G+ν}`**), `gpD_b`, `gpD_ba`,
  `gpD_ext` (**`gpD γ` extends `gpD β` for `β ≤ γ < ε₀`**), `gpD_nat` (**`gpD n = goIt n`**), `gpD_ext_It`,
  `gpD_lim_cof` (**the bound of `gpD λ` is the union of the earlier bounds**).

No new axiom.  New definitions: `gpOff`, `gpI`, `GpInv`, `GpTop`, `gpChain`, `gpExt`, `gpLim`, `gpD`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gp

open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gj
  Googology.Trans.PoR.InaccPsi.R2.Gi Googology.Trans.PoR.InaccPsi.R2.Gn Googology.Trans.PoR.InaccPsi.R2.Go
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

/-! ## Offsets -/

/-- The offset of the `ν`-th base: `ν` for finite `ν`, `ν + 1` otherwise. -/
noncomputable def gpOff (ν : Ordinal.{0}) : Ordinal.{0} := if ν < ω then ν else ν + 1

theorem gpOff_zero : gpOff 0 = 0 := by unfold gpOff; rw [if_pos omega0_pos]

theorem gpOff_succ (ν : Ordinal.{0}) : gpOff (ν + 1) = gpOff ν + 1 := by
  unfold gpOff
  by_cases h : ν < ω
  · rw [if_pos (isSuccLimit_omega0.add_one_lt h), if_pos h]
  · rw [if_neg h, if_neg (fun h' => h ((lt_add_one ν).trans h'))]

theorem gpOff_lim {l : Ordinal.{0}} (hl : IsSuccLimit l) : gpOff l = l + 1 := by
  unfold gpOff; rw [if_neg (not_lt.2 (omega0_le_of_isSuccLimit hl))]

theorem le_gpOff (ν : Ordinal.{0}) : ν ≤ gpOff ν := by
  unfold gpOff; split_ifs
  · exact le_rfl
  · exact le_self_add

theorem gpOff_lt {l ν : Ordinal.{0}} (hl : IsSuccLimit l) (h : ν < l) : gpOff ν < l := by
  unfold gpOff; split_ifs
  · exact h
  · exact hl.add_one_lt h

/-- The index of the first base: `Γ_{x+1} = φ(1, gpI x)`. -/
noncomputable def gpI (x : Ordinal.{0}) : Ordinal.{0} := evIx (lgG x)

/-! ## The invariant -/

/-- **The invariant of a family of digit systems below `λ`**: base index `G + β`, base `φ(1, gpI x + β)`, offset
`Γ_{x+1} + gpOff β`, coherence of readings and gates, and the gate of an earlier bound below `ε₀`. -/
structure GpInv (l : Ordinal.{0}) (F : Ordinal.{0} → GoD) : Prop where
  ix : ∀ β, β < l → (F β).ix = gcG 0 + β
  b : ∀ β, β < l → ∀ x, InE x → x < Om1 → (F β).b x = veblen 1 (gpI x + β)
  ba : ∀ β, β < l → ∀ x, (F β).ba x = lgG x + gpOff β
  cohR : ∀ β γ, β ≤ γ → γ < l → ∀ c x, c < (F β).B → (F γ).R c x = (F β).R c x
  cohg : ∀ β γ, β ≤ γ → γ < l → ∀ c, c < (F β).B → (F γ).g c = (F β).g c
  cf : ∀ β γ, β < γ → γ < l → (F γ).g (F β).B < ε₀

namespace GpInv

variable {l : Ordinal.{0}} {F : Ordinal.{0} → GoD} (H : GpInv l F)
include H

theorem B_eq {β : Ordinal.{0}} (h : β < l) : (F β).B = veblen 1 (gcG 0 + β) := by
  rw [(F β).B_ix, H.ix β h]

theorem B_lt {β γ : Ordinal.{0}} (hβγ : β < γ) (h : γ < l) : (F β).B < (F γ).B := by
  rw [H.B_eq (hβγ.trans h), H.B_eq h]
  exact (isNormal_veblen 1).strictMono ((add_lt_add_iff_left _).2 hβγ)

theorem B_le {β γ : Ordinal.{0}} (hβγ : β ≤ γ) (h : γ < l) : (F β).B ≤ (F γ).B := by
  rcases hβγ.lt_or_eq with h' | rfl
  · exact (H.B_lt h' h).le
  · exact le_rfl

theorem congr {G : Ordinal.{0} → GoD} (hFG : ∀ β, β < l → G β = F β) : GpInv l G where
  ix := fun β h => by rw [hFG β h]; exact H.ix β h
  b := fun β h x hx hx1 => by rw [hFG β h]; exact H.b β h x hx hx1
  ba := fun β h x => by rw [hFG β h]; exact H.ba β h x
  cohR := fun β γ hβγ h c x hc => by
    rw [hFG β (lt_of_le_of_lt hβγ h)] at hc ⊢
    rw [hFG γ h]; exact H.cohR β γ hβγ h c x hc
  cohg := fun β γ hβγ h c hc => by
    rw [hFG β (lt_of_le_of_lt hβγ h)] at hc ⊢
    rw [hFG γ h]; exact H.cohg β γ hβγ h c hc
  cf := fun β γ hβγ h => by rw [hFG β (hβγ.trans h), hFG γ h]; exact H.cf β γ hβγ h

end GpInv

theorem gpInv_zero (F : Ordinal.{0} → GoD) : GpInv 0 F where
  ix := fun _ h => absurd h (not_lt.2 zero_le)
  b := fun _ h => absurd h (not_lt.2 zero_le)
  ba := fun _ h => absurd h (not_lt.2 zero_le)
  cohR := fun _ _ _ h => absurd h (not_lt.2 zero_le)
  cohg := fun _ _ _ h => absurd h (not_lt.2 zero_le)
  cf := fun _ _ _ h => absurd h (not_lt.2 zero_le)

/-! ## The union at a limit -/

/-- **The chain at a limit `λ < ε₀`**: the systems `F (gpFs λ k)`. -/
noncomputable def gpChain (l : Ordinal.{0}) (hl : IsSuccLimit l) (hl0 : l < ε₀) (F : Ordinal.{0} → GoD)
    (H : GpInv l F) : GoSeq where
  D := fun k => F (gpFs l k)
  ix0 := gcG 0
  i := gpI
  a := lgG
  δ := gpFs l
  s := fun k => gpOff (gpFs l k)
  Δ := l
  T := l
  hix := fun k => H.ix _ (gpFs_lt hl hl0 k)
  hb := fun k x hx hx1 => H.b _ (gpFs_lt hl hl0 k) x hx hx1
  hba := fun k x => H.ba _ (gpFs_lt hl hl0 k) x
  coh_R := fun k c x hc => H.cohR _ _ (gpFs_mono hl hl0 k).le (gpFs_lt hl hl0 (k + 1)) c x hc
  coh_g := fun k c hc => H.cohg _ _ (gpFs_mono hl hl0 k).le (gpFs_lt hl hl0 (k + 1)) c hc
  cf_g := fun k => H.cf _ _ (gpFs_mono hl hl0 k) (gpFs_lt hl hl0 (k + 1))
  δ_mono := gpFs_mono hl hl0
  δ_lt := gpFs_lt hl hl0
  δ_cof := gpFs_cof hl hl0
  Δ_lim := hl
  Δ_lt := hl0
  s_lt := fun k => gpOff_lt hl (gpFs_lt hl hl0 k)
  s_cof := fun t ht => (gpFs_cof hl hl0 t ht).imp fun _ hk => hk.trans_le (le_gpOff _)
  T_lt := hl0
  ix_mem := fun S a b ha => CSet.add_mem (goGl.ix_mem S a b ha) (gc_cst_mem (S := S) a b l hl0)
  ix0_lt := gcG_lt zero_lt_one
  a_lt := goGl.ba_lt
  a_pi := goGl.ba_pi

/-- The family of the earlier values, extended by `goGl`. -/
noncomputable def gpExt (l : Ordinal.{0}) (IH : ∀ β, β < l → GoD) (β : Ordinal.{0}) : GoD :=
  if h : β < l then IH β h else goGl

open Classical in
/-- The limit step: the union when the invariant holds (it always does, `gp_inv`). -/
noncomputable def gpLim (l : Ordinal.{0}) (hl : IsSuccLimit l) (IH : ∀ β, β < l → GoD) : GoD :=
  if H : l < ε₀ ∧ GpInv l (gpExt l IH) then (gpChain l hl H.1 (gpExt l IH) H.2).toCh.lim else goGl

/-- **THE RECURSION**: `gpD 0 = goGl`, `gpD (ν+1) = (gpD ν).step`, `gpD λ = ⋃_{β<λ} gpD β`. -/
noncomputable def gpD (ν : Ordinal.{0}) : GoD :=
  Ordinal.limitRecOn (motive := fun _ => GoD) ν goGl (fun _ D => D.step) gpLim

theorem gpD_zero : gpD 0 = goGl := by
  unfold gpD; rw [Ordinal.limitRecOn_zero]

theorem gpD_succ (ν : Ordinal.{0}) : gpD (ν + 1) = (gpD ν).step := by
  unfold gpD; rw [Ordinal.limitRecOn_add_one]

theorem gpD_limit {l : Ordinal.{0}} (hl : IsSuccLimit l) : gpD l = gpLim l hl (fun β _ => gpD β) := by
  unfold gpD; rw [Ordinal.limitRecOn_limit _ _ _ _ hl]

theorem gpExt_eq {l β : Ordinal.{0}} (h : β < l) : gpExt l (fun β _ => gpD β) β = gpD β := by
  unfold gpExt; rw [dif_pos h]

/-! ## The invariant at every `ν < ε₀` -/

/-- The new facts at the top `ν`. -/
structure GpTop (ν : Ordinal.{0}) : Prop where
  ix : (gpD ν).ix = gcG 0 + ν
  b : ∀ x, InE x → x < Om1 → (gpD ν).b x = veblen 1 (gpI x + ν)
  ba : ∀ x, (gpD ν).ba x = lgG x + gpOff ν
  cohR : ∀ β, β < ν → ∀ c x, c < (gpD β).B → (gpD ν).R c x = (gpD β).R c x
  cohg : ∀ β, β < ν → ∀ c, c < (gpD β).B → (gpD ν).g c = (gpD β).g c
  cf : ∀ β, β < ν → (gpD ν).g (gpD β).B < ε₀

theorem gpInv_succ {ν : Ordinal.{0}} (H : GpInv ν gpD) (T : GpTop ν) : GpInv (ν + 1) gpD where
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

theorem gpInv_lim {l : Ordinal.{0}} (IH : ∀ β, β < l → GpInv (β + 1) gpD) : GpInv l gpD where
  ix := fun β h => (IH β h).ix β (lt_add_one β)
  b := fun β h => (IH β h).b β (lt_add_one β)
  ba := fun β h => (IH β h).ba β (lt_add_one β)
  cohR := fun β γ hβγ h => (IH γ h).cohR β γ hβγ (lt_add_one γ)
  cohg := fun β γ hβγ h => (IH γ h).cohg β γ hβγ (lt_add_one γ)
  cf := fun β γ hβγ h => (IH γ h).cf β γ hβγ (lt_add_one γ)

theorem gpTop_zero : GpTop 0 where
  ix := by rw [gpD_zero, add_zero]; rfl
  b := fun x hx hx1 => by
    rw [gpD_zero, add_zero]
    exact (epsilon_evIx (goGl.b_E x hx hx1)).symm
  ba := fun x => by rw [gpD_zero, gpOff_zero, add_zero]; rfl
  cohR := fun _ h => absurd h (not_lt.2 zero_le)
  cohg := fun _ h => absurd h (not_lt.2 zero_le)
  cf := fun _ h => absurd h (not_lt.2 zero_le)

theorem gpTop_succ {ν : Ordinal.{0}} (H : GpInv (ν + 1) gpD) : GpTop (ν + 1) where
  ix := by
    rw [gpD_succ]
    show (gpD ν).ix + 1 = _
    rw [H.ix ν (lt_add_one ν), add_assoc]
  b := fun x hx hx1 => by
    rw [gpD_succ, GoD.step_b, H.b ν (lt_add_one ν) x hx hx1, go_eN_veb, add_assoc]
  ba := fun x => by
    rw [gpD_succ]
    show (gpD ν).ba x + 1 = _
    rw [H.ba ν (lt_add_one ν) x, gpOff_succ, add_assoc]
  cohR := fun β hβ c x hc => by
    have hβν : β ≤ ν := Order.lt_add_one_iff.1 hβ
    rw [gpD_succ, GoD.step_R_low _ (hc.trans_le (H.B_le hβν (lt_add_one ν))) x]
    exact H.cohR β ν hβν (lt_add_one ν) c x hc
  cohg := fun β hβ c hc => by
    have hβν : β ≤ ν := Order.lt_add_one_iff.1 hβ
    rw [gpD_succ, GoD.step_g_low _ (hc.trans_le (H.B_le hβν (lt_add_one ν)))]
    exact H.cohg β ν hβν (lt_add_one ν) c hc
  cf := fun β hβ => by
    rcases (Order.lt_add_one_iff.1 hβ).lt_or_eq with h | rfl
    · rw [gpD_succ, GoD.step_g_low _ (H.B_lt h (lt_add_one ν))]
      exact H.cf β ν h (lt_add_one ν)
    · rw [gpD_succ, GoD.step_g, GoD.hG_G]; exact epsilon_pos 0

theorem gpTop_lim {l : Ordinal.{0}} (hl : IsSuccLimit l) (hl0 : l < ε₀) (H : GpInv l gpD) : GpTop l := by
  have Hx : GpInv l (gpExt l fun β _ => gpD β) := H.congr fun β h => gpExt_eq h
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = gpChain l hl hl0 (gpExt l fun β _ => gpD β) Hx := ⟨_, rfl⟩
  have e : gpD l = Q.toCh.lim := by
    rw [gpD_limit hl, hQ]; unfold gpLim; rw [dif_pos ⟨hl0, Hx⟩]
  have hD : ∀ k, Q.toCh.D k = gpD (gpFs l k) := fun k => by
    rw [hQ]; exact gpExt_eq (gpFs_lt hl hl0 k)
  refine ⟨?_, fun x hx hx1 => ?_, fun x => ?_, fun β hβ c x hc => ?_, fun β hβ c hc => ?_, fun β hβ => ?_⟩
  · rw [e, Q.toCh_lim_ix, hQ]; rfl
  · rw [e, Q.toCh_lim_b hx hx1, hQ]; rfl
  · rw [e, Q.toCh_lim_ba, gpOff_lim hl, hQ]; exact add_assoc _ _ _
  · obtain ⟨k, hk⟩ := gpFs_cof hl hl0 β hβ
    have hc' : c < (Q.toCh.D k).B := by rw [hD]; exact hc.trans (H.B_lt hk (gpFs_lt hl hl0 k))
    rw [e, Q.toCh.lim_R hc' x, hD]
    exact H.cohR β _ hk.le (gpFs_lt hl hl0 k) c x hc
  · obtain ⟨k, hk⟩ := gpFs_cof hl hl0 β hβ
    have hc' : c < (Q.toCh.D k).B := by rw [hD]; exact hc.trans (H.B_lt hk (gpFs_lt hl hl0 k))
    rw [e, Q.toCh.lim_g hc', hD]
    exact H.cohg β _ hk.le (gpFs_lt hl hl0 k) c hc
  · obtain ⟨k, hk⟩ := gpFs_cof hl hl0 β hβ
    have hc' : (gpD β).B < (Q.toCh.D k).B := by rw [hD]; exact H.B_lt hk (gpFs_lt hl hl0 k)
    rw [e, Q.toCh.lim_g hc', hD]
    exact H.cf β _ hk (gpFs_lt hl hl0 k)

/-- **THE INVARIANT AT EVERY `ν < ε₀`** (one induction; the coherence is carried along). -/
theorem gp_inv : ∀ ν : Ordinal.{0}, ν < ε₀ → GpInv (ν + 1) gpD := by
  intro ν
  induction ν using Ordinal.limitRecOn with
  | zero => intro _; exact gpInv_succ (gpInv_zero gpD) gpTop_zero
  | add_one μ ih =>
    intro hν
    have H := ih ((lt_add_one μ).trans hν)
    exact gpInv_succ H (gpTop_succ H)
  | limit l hl ih =>
    intro hν
    have H := gpInv_lim (fun β hβ => ih β hβ (hβ.trans hν))
    exact gpInv_succ H (gpTop_lim hl hν H)

/-! ## The systems `gpD ν` -/

section Main

variable {ν : Ordinal.{0}} (hν : ν < ε₀)
include hν

/-- **The bound of `gpD ν` is `φ(1, G + ν) = ε_{G+ν}`.** -/
theorem gpD_B : (gpD ν).B = veblen 1 (gcG 0 + ν) := (gp_inv ν hν).B_eq (lt_add_one ν)

theorem gpD_ix : (gpD ν).ix = gcG 0 + ν := (gp_inv ν hν).ix ν (lt_add_one ν)

/-- **The base reading of `gpD ν` is `φ(1, gpI x + ν)`** (`Γ_{x+1} = φ(1, gpI x)`). -/
theorem gpD_b {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : (gpD ν).b x = veblen 1 (gpI x + ν) :=
  (gp_inv ν hν).b ν (lt_add_one ν) x hx hx1

theorem gpD_ba (x : Ordinal.{0}) : (gpD ν).ba x = lgG x + gpOff ν := (gp_inv ν hν).ba ν (lt_add_one ν) x

end Main

/-- **`gpD γ` extends `gpD β` for `β ≤ γ < ε₀`**: same readings and gates below `ε_{G+β}`; the gate of `ε_{G+β}` in
`gpD γ` is below `ε₀` when `β < γ`. -/
theorem gpD_ext {β γ : Ordinal.{0}} (hβγ : β ≤ γ) (hγ : γ < ε₀) :
    (∀ c x, c < (gpD β).B → (gpD γ).R c x = (gpD β).R c x) ∧
    (∀ c, c < (gpD β).B → (gpD γ).g c = (gpD β).g c) ∧ (β < γ → (gpD γ).g (gpD β).B < ε₀) :=
  ⟨(gp_inv γ hγ).cohR β γ hβγ (lt_add_one γ), (gp_inv γ hγ).cohg β γ hβγ (lt_add_one γ),
    fun h => (gp_inv γ hγ).cf β γ h (lt_add_one γ)⟩

theorem gpD_B_lt {β γ : Ordinal.{0}} (hβγ : β < γ) (hγ : γ < ε₀) : (gpD β).B < (gpD γ).B :=
  (gp_inv γ hγ).B_lt hβγ (lt_add_one γ)

/-- **`gpD n = goIt n`** for finite `n`. -/
theorem gpD_nat : ∀ n : ℕ, gpD n = goIt n
  | 0 => by rw [Nat.cast_zero, gpD_zero]; rfl
  | n + 1 => by rw [Nat.cast_succ, gpD_succ, gpD_nat n, goIt_succ]

/-- **`gpD ν` extends every `goIt n`, `n ≤ ν`.** -/
theorem gpD_ext_It {n : ℕ} {ν : Ordinal.{0}} (h : (n : Ordinal.{0}) ≤ ν) (hν : ν < ε₀) :
    (∀ c x, c < (goIt n).B → (gpD ν).R c x = (goIt n).R c x) ∧
    (∀ c, c < (goIt n).B → (gpD ν).g c = (goIt n).g c) := by
  obtain ⟨h1, h2, -⟩ := gpD_ext h hν
  rw [gpD_nat] at h1 h2
  exact ⟨h1, h2⟩

/-- **The bound of `gpD λ` is the union of the earlier bounds** (`λ` a limit below `ε₀`). -/
theorem gpD_lim_cof {l : Ordinal.{0}} (hl : IsSuccLimit l) (hl0 : l < ε₀) {c : Ordinal.{0}} (hc : c < (gpD l).B) :
    ∃ β, β < l ∧ c < (gpD β).B := by
  rw [gpD_B hl0] at hc
  obtain ⟨t, ht, hct⟩ := ((isNormal_veblen 1).lt_iff_exists_lt (isSuccLimit_add _ hl)).1 hc
  obtain ⟨d, hd, htd⟩ := (lt_add_iff hl.bot_lt.ne').1 ht
  refine ⟨d, hd, ?_⟩
  rw [gpD_B (hd.trans hl0)]
  exact hct.trans_le ((isNormal_veblen 1).monotone htd)

end Googology.Trans.PoR.InaccPsi.R2.Gp
