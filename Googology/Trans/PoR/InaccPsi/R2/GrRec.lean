import Googology.Trans.PoR.InaccPsi.R2.GrLim

/-!
# THE RECURSION PAST `Γ₀`: one gated digit system `grD ν` for every constant index `ν < ζ_{Γ₀+1}`

Port of `R2.GqRec` to `GrD` (`R2.GrD`, `R2.GrStep`, `R2.GrLim`): `grD 0 = goGl`, `grD (ν+1) = (grD ν).step`, and at a
limit `λ` the gated union (`R2.GrLim`) of `grD (gqFs λ k)` with base gate `λ`.  The bound is `ζ_{Γ₀+1}` (`Gr.grK`) in
place of `Γ₀`: the index of the union is in every hull `C(a, b)`, `0 < a` (`gr_cst_mem`, through `ψ_{Ω₁}(0) = Γ₀`),
and the code-gate condition of each base is carried by the systems (`GrD.γ_cl`).

* `GrInv`, `GrTop` (the invariant: base index `G + β`, base `φ(1, gpI x + β)`, base gate `≤ β`, coherence);
* `grGl`, `grChain`, `grExt`, `grLimD`, `grD` (**THE RECURSION**), `grD_zero`, `grD_succ`, `grD_limit`;
* `gr_inv` (**THE INVARIANT AT EVERY `ν < ζ_{Γ₀+1}`**), `grD_B` (**`(grD ν).B = φ(1, G + ν) = ε_{G+ν}`**), `grD_b`,
  `grD_ba`, `grD_γ` (base gate `≤ ν`), `grD_ext`, `grD_B_lt`, `grD_lim_cof`, `grD_eps0`;
* `grD_gam0` (**THE INDEX `Γ₀` IS REACHED**: `(grD Γ₀).B = ε_{G+Γ₀}`), `grD_all`.

No new axiom.  New definitions: `GrInv`, `GrTop`, `grGl`, `grChain`, `grExt`, `grLimD`, `grD`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gr

open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gj
  Googology.Trans.PoR.InaccPsi.R2.Gi Googology.Trans.PoR.InaccPsi.R2.Gn Googology.Trans.PoR.InaccPsi.R2.Go
  Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gp
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

/-! ## The invariant -/

/-- **The invariant of a family of gated digit systems below `λ`**: base index `G + β`, base `φ(1, gpI x + β)`,
offset `Γ_{x+1} + gpOff β`, base gate `≤ β`, coherence of readings and gates, the gate of an earlier bound
`≤ max β ε₀`. -/
structure GrInv (l : Ordinal.{0}) (F : Ordinal.{0} → GrD) : Prop where
  ix : ∀ β, β < l → (F β).ix = gcG 0 + β
  b : ∀ β, β < l → ∀ x, InE x → x < Om1 → (F β).b x = veblen 1 (gpI x + β)
  ba : ∀ β, β < l → ∀ x, (F β).ba x = lgG x + gpOff β
  γ : ∀ β, β < l → (F β).γ ≤ β
  cohR : ∀ β γ, β ≤ γ → γ < l → ∀ c x, c < (F β).B → (F γ).R c x = (F β).R c x
  cohg : ∀ β γ, β ≤ γ → γ < l → ∀ c, c < (F β).B → (F γ).g c = (F β).g c
  cf : ∀ β γ, β < γ → γ < l → (F γ).g (F β).B ≤ max β ε₀

namespace GrInv

variable {l : Ordinal.{0}} {F : Ordinal.{0} → GrD} (H : GrInv l F)
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

theorem congr {G : Ordinal.{0} → GrD} (hFG : ∀ β, β < l → G β = F β) : GrInv l G where
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

end GrInv

theorem grInv_zero (F : Ordinal.{0} → GrD) : GrInv 0 F where
  ix := fun _ h => absurd h (not_lt.2 zero_le)
  b := fun _ h => absurd h (not_lt.2 zero_le)
  ba := fun _ h => absurd h (not_lt.2 zero_le)
  γ := fun _ h => absurd h (not_lt.2 zero_le)
  cohR := fun _ _ _ h => absurd h (not_lt.2 zero_le)
  cohg := fun _ _ _ h => absurd h (not_lt.2 zero_le)
  cf := fun _ _ _ h => absurd h (not_lt.2 zero_le)

/-! ## The union at a limit -/

/-- The start: the codes below `G` as a gated digit system with gate `0`. -/
noncomputable def grGl : GrD := GrD.ofGo goGl

/-- **The chain at a limit `λ < ζ_{Γ₀+1}`**: the systems `F (gqFs λ k)`, base gate `λ`. -/
noncomputable def grChain (l : Ordinal.{0}) (hl : IsSuccLimit l) (hlK : l < grK) (F : Ordinal.{0} → GrD)
    (H : GrInv l F) : GrSeq where
  D := fun k => F (gqFs l k)
  ix0 := gcG 0
  i := gpI
  a := lgG
  δ := gqFs l
  s := fun k => gpOff (gqFs l k)
  Δ := l
  T := l
  γω := l
  hix := fun k => H.ix _ (gqFs_lt hl (hlK.trans grK_lt_Om1) k)
  hb := fun k x hx hx1 => H.b _ (gqFs_lt hl (hlK.trans grK_lt_Om1) k) x hx hx1
  hba := fun k x => H.ba _ (gqFs_lt hl (hlK.trans grK_lt_Om1) k) x
  coh_R := fun k c x hc => H.cohR _ _ (gqFs_mono hl (hlK.trans grK_lt_Om1) k).le
    (gqFs_lt hl (hlK.trans grK_lt_Om1) (k + 1)) c x hc
  coh_g := fun k c hc => H.cohg _ _ (gqFs_mono hl (hlK.trans grK_lt_Om1) k).le
    (gqFs_lt hl (hlK.trans grK_lt_Om1) (k + 1)) c hc
  cf_g := fun k => (H.cf _ _ (gqFs_mono hl (hlK.trans grK_lt_Om1) k) (gqFs_lt hl (hlK.trans grK_lt_Om1) (k + 1))).trans
    (max_le_max (gqFs_lt hl (hlK.trans grK_lt_Om1) k).le le_rfl)
  γ_le := fun k => (H.γ _ (gqFs_lt hl (hlK.trans grK_lt_Om1) k)).trans (gqFs_lt hl (hlK.trans grK_lt_Om1) k).le
  γω_lt := hlK
  γω_le := le_rfl
  T_le := le_rfl
  δ_mono := gqFs_mono hl (hlK.trans grK_lt_Om1)
  δ_lt := gqFs_lt hl (hlK.trans grK_lt_Om1)
  δ_cof := gqFs_cof hl (hlK.trans grK_lt_Om1)
  Δ_lim := hl
  Δ_lt := hlK
  s_lt := fun k => gpOff_lt hl (gqFs_lt hl (hlK.trans grK_lt_Om1) k)
  s_cof := fun t ht => (gqFs_cof hl (hlK.trans grK_lt_Om1) t ht).imp fun _ hk => hk.trans_le (le_gpOff _)
  T_lt := hlK
  ix_mem := fun S a b ha => CSet.add_mem (goGl.ix_mem S a b ha) (gr_cst_mem_K ha b hlK)
  ix0_lt := gcG_lt zero_lt_one
  ix0_G := rfl
  a_lt := goGl.ba_lt
  a_pi := fun σ ρ hB _ => goGl.ba_pi σ ρ hB
  i_big := fun x hx hx1 => (epsilon_evIx (goGl.b_E x hx hx1)).ge

/-- The family of the earlier values, extended by `grGl`. -/
noncomputable def grExt (l : Ordinal.{0}) (IH : ∀ β, β < l → GrD) (β : Ordinal.{0}) : GrD :=
  if h : β < l then IH β h else grGl

open Classical in
/-- The limit step: the gated union when the invariant holds (it does below `ζ_{Γ₀+1}`, `gr_inv`). -/
noncomputable def grLimD (l : Ordinal.{0}) (hl : IsSuccLimit l) (IH : ∀ β, β < l → GrD) : GrD :=
  if H : l < grK ∧ GrInv l (grExt l IH) then (grChain l hl H.1 (grExt l IH) H.2).toCh.lim else grGl

/-- **THE RECURSION**: `grD 0 = goGl`, `grD (ν+1) = (grD ν).step`, `grD λ = ⋃_{β<λ} grD β` (gate `λ`). -/
noncomputable def grD (ν : Ordinal.{0}) : GrD :=
  Ordinal.limitRecOn (motive := fun _ => GrD) ν grGl (fun _ D => D.step) grLimD

theorem grD_zero : grD 0 = grGl := by
  unfold grD; rw [Ordinal.limitRecOn_zero]

theorem grD_succ (ν : Ordinal.{0}) : grD (ν + 1) = (grD ν).step := by
  unfold grD; rw [Ordinal.limitRecOn_add_one]

theorem grD_limit {l : Ordinal.{0}} (hl : IsSuccLimit l) : grD l = grLimD l hl (fun β _ => grD β) := by
  unfold grD; rw [Ordinal.limitRecOn_limit _ _ _ _ hl]

theorem grExt_eq {l β : Ordinal.{0}} (h : β < l) : grExt l (fun β _ => grD β) β = grD β := by
  unfold grExt; rw [dif_pos h]

/-! ## The invariant at every `ν < ζ_{Γ₀+1}` -/

/-- The new facts at the top `ν`. -/
structure GrTop (ν : Ordinal.{0}) : Prop where
  ix : (grD ν).ix = gcG 0 + ν
  b : ∀ x, InE x → x < Om1 → (grD ν).b x = veblen 1 (gpI x + ν)
  ba : ∀ x, (grD ν).ba x = lgG x + gpOff ν
  γ : (grD ν).γ ≤ ν
  cohR : ∀ β, β < ν → ∀ c x, c < (grD β).B → (grD ν).R c x = (grD β).R c x
  cohg : ∀ β, β < ν → ∀ c, c < (grD β).B → (grD ν).g c = (grD β).g c
  cf : ∀ β, β < ν → (grD ν).g (grD β).B ≤ max β ε₀

theorem grInv_succ {ν : Ordinal.{0}} (H : GrInv ν grD) (T : GrTop ν) : GrInv (ν + 1) grD where
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

theorem grInv_lim {l : Ordinal.{0}} (IH : ∀ β, β < l → GrInv (β + 1) grD) : GrInv l grD where
  ix := fun β h => (IH β h).ix β (lt_add_one β)
  b := fun β h => (IH β h).b β (lt_add_one β)
  ba := fun β h => (IH β h).ba β (lt_add_one β)
  γ := fun β h => (IH β h).γ β (lt_add_one β)
  cohR := fun β γ hβγ h => (IH γ h).cohR β γ hβγ (lt_add_one γ)
  cohg := fun β γ hβγ h => (IH γ h).cohg β γ hβγ (lt_add_one γ)
  cf := fun β γ hβγ h => (IH γ h).cf β γ hβγ (lt_add_one γ)

theorem grTop_zero : GrTop 0 where
  ix := by rw [grD_zero, add_zero]; rfl
  b := fun x hx hx1 => by
    rw [grD_zero, add_zero]
    exact (epsilon_evIx (goGl.b_E x hx hx1)).symm
  ba := fun x => by rw [grD_zero, gpOff_zero, add_zero]; rfl
  γ := by rw [grD_zero]; exact le_rfl
  cohR := fun _ h => absurd h (not_lt.2 zero_le)
  cohg := fun _ h => absurd h (not_lt.2 zero_le)
  cf := fun _ h => absurd h (not_lt.2 zero_le)

theorem grTop_succ {ν : Ordinal.{0}} (H : GrInv (ν + 1) grD) : GrTop (ν + 1) where
  ix := by
    rw [grD_succ, GrD.step_ix, H.ix ν (lt_add_one ν), add_assoc]
  b := fun x hx hx1 => by
    rw [grD_succ, GrD.step_b, H.b ν (lt_add_one ν) x hx hx1, go_eN_veb, add_assoc]
  ba := fun x => by
    rw [grD_succ, GrD.step_ba, H.ba ν (lt_add_one ν) x, gpOff_succ, add_assoc]
  γ := by rw [grD_succ, GrD.step_γ]; exact (H.γ ν (lt_add_one ν)).trans le_self_add
  cohR := fun β hβ c x hc => by
    have hβν : β ≤ ν := Order.lt_add_one_iff.1 hβ
    rw [grD_succ, GrD.step_R_low _ (hc.trans_le (H.B_le hβν (lt_add_one ν))) x]
    exact H.cohR β ν hβν (lt_add_one ν) c x hc
  cohg := fun β hβ c hc => by
    have hβν : β ≤ ν := Order.lt_add_one_iff.1 hβ
    rw [grD_succ, GrD.step_g_low _ (hc.trans_le (H.B_le hβν (lt_add_one ν)))]
    exact H.cohg β ν hβν (lt_add_one ν) c hc
  cf := fun β hβ => by
    rcases (Order.lt_add_one_iff.1 hβ).lt_or_eq with h | rfl
    · rw [grD_succ, GrD.step_g_low _ (H.B_lt h (lt_add_one ν))]
      exact H.cf β ν h (lt_add_one ν)
    · rw [grD_succ, GrD.step_g_B]
      exact (H.γ β (lt_add_one β)).trans (le_max_left _ _)

theorem grTop_lim {l : Ordinal.{0}} (hl : IsSuccLimit l) (hlK : l < grK) (H : GrInv l grD) : GrTop l := by
  have hl1 : l < Om1 := hlK.trans grK_lt_Om1
  have Hx : GrInv l (grExt l fun β _ => grD β) := H.congr fun β h => grExt_eq h
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = grChain l hl hlK (grExt l fun β _ => grD β) Hx := ⟨_, rfl⟩
  have e : grD l = Q.toCh.lim := by
    rw [grD_limit hl, hQ]; unfold grLimD; rw [dif_pos ⟨hlK, Hx⟩]
  have hD : ∀ k, Q.toCh.D k = grD (gqFs l k) := fun k => by
    rw [hQ]; exact grExt_eq (gqFs_lt hl hl1 k)
  refine ⟨?_, fun x hx hx1 => ?_, fun x => ?_, ?_, fun β hβ c x hc => ?_, fun β hβ c hc => ?_, fun β hβ => ?_⟩
  · rw [e, Q.toCh_lim_ix, hQ]; rfl
  · rw [e, Q.toCh_lim_b hx hx1, hQ]; rfl
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
    have hc' : (grD β).B < (Q.toCh.D k).B := by rw [hD]; exact H.B_lt hk (gqFs_lt hl hl1 k)
    rw [e, Q.toCh.lim_g hc', hD]
    exact H.cf β _ hk (gqFs_lt hl hl1 k)

/-- **THE INVARIANT AT EVERY `ν < ζ_{Γ₀+1}`** (one induction; the coherence is carried along). -/
theorem gr_inv : ∀ ν : Ordinal.{0}, ν < grK → GrInv (ν + 1) grD := by
  intro ν
  induction ν using Ordinal.limitRecOn with
  | zero => intro _; exact grInv_succ (grInv_zero grD) grTop_zero
  | add_one μ ih =>
    intro hν
    have H := ih ((lt_add_one μ).trans hν)
    exact grInv_succ H (grTop_succ H)
  | limit l hl ih =>
    intro hν
    have H := grInv_lim (fun β hβ => ih β hβ (hβ.trans hν))
    exact grInv_succ H (grTop_lim hl hν H)

/-! ## The systems `grD ν` -/

section Main

variable {ν : Ordinal.{0}} (hν : ν < grK)
include hν

/-- **The bound of `grD ν` is `φ(1, G + ν) = ε_{G+ν}`.** -/
theorem grD_B : (grD ν).B = veblen 1 (gcG 0 + ν) := (gr_inv ν hν).B_eq (lt_add_one ν)

/-- **The base reading of `grD ν` is `φ(1, gpI x + ν)`** at every base. -/
theorem grD_b {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : (grD ν).b x = veblen 1 (gpI x + ν) :=
  (gr_inv ν hν).b ν (lt_add_one ν) x hx hx1

theorem grD_ba (x : Ordinal.{0}) : (grD ν).ba x = lgG x + gpOff ν := (gr_inv ν hν).ba ν (lt_add_one ν) x

/-- **The base gate of `grD ν` is at most `ν`.** -/
theorem grD_γ : (grD ν).γ ≤ ν := (gr_inv ν hν).γ ν (lt_add_one ν)

end Main

/-- **`grD γ` extends `grD β` for `β ≤ γ < ζ_{Γ₀+1}`**; the gate of `ε_{G+β}` in `grD γ` is `≤ max β ε₀` when
`β < γ`. -/
theorem grD_ext {β γ : Ordinal.{0}} (hβγ : β ≤ γ) (hγ : γ < grK) :
    (∀ c x, c < (grD β).B → (grD γ).R c x = (grD β).R c x) ∧
    (∀ c, c < (grD β).B → (grD γ).g c = (grD β).g c) ∧ (β < γ → (grD γ).g (grD β).B ≤ max β ε₀) :=
  ⟨(gr_inv γ hγ).cohR β γ hβγ (lt_add_one γ), (gr_inv γ hγ).cohg β γ hβγ (lt_add_one γ),
    fun h => (gr_inv γ hγ).cf β γ h (lt_add_one γ)⟩

theorem grD_B_lt {β γ : Ordinal.{0}} (hβγ : β < γ) (hγ : γ < grK) : (grD β).B < (grD γ).B :=
  (gr_inv γ hγ).B_lt hβγ (lt_add_one γ)

/-- **The bound of `grD λ` is the union of the earlier bounds** (`λ` a limit below `ζ_{Γ₀+1}`). -/
theorem grD_lim_cof {l : Ordinal.{0}} (hl : IsSuccLimit l) (hlK : l < grK) {c : Ordinal.{0}} (hc : c < (grD l).B) :
    ∃ β, β < l ∧ c < (grD β).B := by
  rw [grD_B hlK] at hc
  obtain ⟨t, ht, hct⟩ := ((isNormal_veblen 1).lt_iff_exists_lt (isSuccLimit_add _ hl)).1 hc
  obtain ⟨d, hd, htd⟩ := (lt_add_iff hl.bot_lt.ne').1 ht
  refine ⟨d, hd, ?_⟩
  rw [grD_B (hd.trans hlK)]
  exact hct.trans_le ((isNormal_veblen 1).monotone htd)

/-- **The index `ε₀` is reached**: `(grD ε₀).B = ε_{G+ε₀}`, base reading `φ(1, gpI x + ε₀)`, base gate `ε₀`. -/
theorem grD_eps0 : (grD ε₀).B = veblen 1 (gcG 0 + ε₀) ∧
    (∀ x, InE x → x < Om1 → (grD ε₀).b x = veblen 1 (gpI x + ε₀)) ∧ (grD ε₀).γ ≤ ε₀ := by
  have h : (ε₀ : Ordinal.{0}) < grK := gq_eps0_lt_gam.trans gam0_lt_grK
  exact ⟨grD_B h, fun x hx hx1 => grD_b h hx hx1, grD_γ h⟩

/-- **THE INDEX `Γ₀` IS REACHED**: `(grD Γ₀).B = ε_{G+Γ₀}`, base reading `φ(1, gpI x + Γ₀)`, base gate `≤ Γ₀`
(`Gq.gq_wall`: no system with a base gate below `Γ₀` has this base). -/
theorem grD_gam0 : (grD (gamma 0)).B = veblen 1 (gcG 0 + gamma 0) ∧
    (∀ x, InE x → x < Om1 → (grD (gamma 0)).b x = veblen 1 (gpI x + gamma 0)) ∧ (grD (gamma 0)).γ ≤ gamma 0 :=
  ⟨grD_B gam0_lt_grK, fun _ hx hx1 => grD_b gam0_lt_grK hx hx1, grD_γ gam0_lt_grK⟩

/-- **Every constant index `ν < ζ_{Γ₀+1}` is reached**: `(grD ν).B = ε_{G+ν}`. -/
theorem grD_all {ν : Ordinal.{0}} (hν : ν < grK) : (grD ν).B = veblen 1 (gcG 0 + ν) ∧ (grD ν).γ ≤ ν :=
  ⟨grD_B hν, grD_γ hν⟩

end Googology.Trans.PoR.InaccPsi.R2.Gr
