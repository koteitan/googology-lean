import Googology.Trans.PoR.InaccPsi.R2.GqLim

/-!
# ONE RECURSION OVER ALL CONSTANT `ε`-INDICES BELOW `Γ₀`, the index `ε₀` and beyond included

`G = Γ_{Ω₁+1}`.  `R2.GpRec` built the digit systems `gpD ν` for `ν < ε₀` only: at `ν = ε₀` the base reading
`φ(1, Γ_{x+1}-index + ε₀)` is not exact at every pair of bases (`R2.GpNo`).  With the gated digit systems of
`R2.GqD` the same recursion runs past `ε₀`, for every `ν < Γ₀` (`R2.GqLim`):

* `gqD 0 = GqD.ofGo goGl`, `gqD (ν+1) = (gqD ν).step` (`R2.GqStep`, the base gate is kept), `gqD λ =` the gated union
  (`R2.GqLim`) of `gqD (gqFs λ k)` along any fundamental sequence of `λ`, with base gate `λ` (a constant index `λ`
  is exact at `σ > λ`).
* The coherence (later systems keep the readings and gates of earlier ones), the base gate `≤ ν` and the gate of an
  earlier bound `≤ max β ε₀` are PART OF THE INDUCTION (`GqInv`).

* `gq_cst_mem` (**every `α < Γ₀` lies in every hull `C(a, b)`**), `gq_countable`, `gqFs` (a fundamental sequence of
  every countable limit), `gqFs_lt`, `gqFs_mono`, `gqFs_cof`;
* `GqInv`, `GqTop`, `gqChain`, `gqExt`, `gqLimD`, `gqD` (**THE RECURSION**), `gqD_zero`, `gqD_succ`, `gqD_limit`;
* `gq_inv` (**THE INVARIANT AT EVERY `ν < Γ₀`**), `gqD_B` (**`(gqD ν).B = φ(1, G + ν) = ε_{G+ν}`**), `gqD_b`
  (**base reading `φ(1, Γ_{x+1}-index + ν)`**), `gqD_ba`, `gqD_γ` (**base gate `≤ ν`**), `gqD_ext`, `gqD_B_lt`,
  `gqD_lim_cof`.

No new axiom.  New definitions: `gqFs`, `GqInv`, `GqTop`, `gqChain`, `gqExt`, `gqLimD`, `gqD`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gq

open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gj
  Googology.Trans.PoR.InaccPsi.R2.Gi Googology.Trans.PoR.InaccPsi.R2.Gn Googology.Trans.PoR.InaccPsi.R2.Go
  Googology.Trans.PoR.InaccPsi.R2.Gp
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

/-! ## Constants below `Γ₀` and fundamental sequences -/

/-- **Every `α < Γ₀` lies in every hull `C(a, b)`** (built from `0` by `+` and `φ`). -/
theorem gq_cst_mem {S : InaccSeq.{0}} (a b : Ordinal.{0}) : ∀ α : Ordinal.{0}, α < gamma 0 → α ∈ S.CSet a b := by
  intro α
  induction α using WellFoundedLT.induction with
  | ind α IH =>
  intro hα
  rcases eq_or_ne α 0 with rfl | h0
  · exact CSet.zero_mem _ _
  by_cases hE : ω ^ α = α
  · have hng : α ∉ range gamma := by
      rintro ⟨o, rfl⟩
      exact absurd hα (not_lt.2 (gamma_le_gamma.2 zero_le))
    have h1 : invVeblen₁ α < α := invVeblen₁_lt_iff.2 ⟨h0, hng⟩
    have h2 : invVeblen₂ α < α := by have := invVeblen₂_lt α; rwa [hE] at this
    have e := veblen_invVeblen₁_invVeblen₂ α
    rw [hE] at e
    rw [← e]
    exact CSet.phi_mem (IH _ h1 (h1.trans hα)) (IH _ h2 (h2.trans hα))
  · have hL : log ω α < α := by
      refine lt_of_le_of_ne (log_le_self ω α) fun e => hE ?_
      have h1 : ω ^ α ≤ α := by have := opow_log_le_self ω h0; rwa [e] at this
      exact le_antisymm h1 (right_le_opow α one_lt_omega0)
    have hw : ω ^ log ω α ∈ S.CSet a b := by
      have := CSet.phi_mem (CSet.zero_mem (S := S) a b) (IH _ hL (hL.trans hα))
      rwa [veblen_zero_apply] at this
    have hwd : ω ^ log ω α ≤ α := opow_log_le_self ω h0
    have hdr : ω ^ log ω α + (α - ω ^ log ω α) = α := Ordinal.add_sub_cancel_of_le hwd
    rcases (Ordinal.sub_le_self α (ω ^ log ω α)).lt_or_eq with hrd | hrd
    · rw [← hdr]; exact CSet.add_mem hw (IH _ hrd (hrd.trans hα))
    · exfalso
      have h1 : ω ^ log ω α + α = α := by
        conv_rhs => rw [← hdr]
        rw [hrd]
      have h2 := add_eq_right_iff_mul_omega0_le.1 h1
      rw [← opow_succ] at h2
      exact absurd (lt_opow_succ_log_self one_lt_omega0 α) (not_lt.2 h2)

theorem gq_countable {l : Ordinal.{0}} (hl : l < Om1) : Countable (Iio l) := by
  rw [Ph.ph_Om1_eq] at hl; exact gc_countable hl

/-- A surjection of `ℕ` onto the ordinals below a countable `λ > 0`. -/
theorem gq_surj {l : Ordinal.{0}} (hl : l < Om1) (h0 : 0 < l) :
    ∃ f : ℕ → Ordinal.{0}, (∀ k, f k < l) ∧ ∀ t, t < l → ∃ k, f k = t := by
  haveI := gq_countable hl
  haveI : Nonempty (Iio l) := ⟨⟨0, h0⟩⟩
  obtain ⟨f, hf⟩ := exists_surjective_nat (Iio l)
  refine ⟨fun k => (f k).1, fun k => (f k).2, fun t ht => ?_⟩
  obtain ⟨k, hk⟩ := hf ⟨t, ht⟩
  exact ⟨k, by show (f k).1 = t; rw [hk]⟩

open Classical in
/-- **A fundamental sequence of a countable limit `λ`** (arbitrary: nothing below depends on the choice). -/
noncomputable def gqFs (l : Ordinal.{0}) : ℕ → Ordinal.{0} :=
  if h : l < Om1 ∧ 0 < l then gpUp (Classical.choose (gq_surj h.1 h.2)) else fun _ => 0

section Fs

variable {l : Ordinal.{0}} (hl : IsSuccLimit l) (hl0 : l < Om1)
include hl hl0

theorem gqFs_eq : gqFs l = gpUp (Classical.choose (gq_surj hl0 hl.bot_lt)) := by
  unfold gqFs; rw [dif_pos ⟨hl0, hl.bot_lt⟩]

theorem gqFs_lt (k : ℕ) : gqFs l k < l := by
  rw [gqFs_eq hl hl0]
  exact gpUp_lt hl (Classical.choose_spec (gq_surj hl0 hl.bot_lt)).1 k

theorem gqFs_mono (k : ℕ) : gqFs l k < gqFs l (k + 1) := by
  rw [gqFs_eq hl hl0]; exact gpUp_mono _ k

theorem gqFs_cof (t : Ordinal.{0}) (ht : t < l) : ∃ k, t < gqFs l k := by
  rw [gqFs_eq hl hl0]
  obtain ⟨k, hk⟩ := (Classical.choose_spec (gq_surj hl0 hl.bot_lt)).2 t ht
  refine ⟨k + 1, ?_⟩
  rw [← hk]
  exact (gpUp_ge _ k).trans_lt (gpUp_mono _ k)

end Fs

theorem gqK_lt_Om1 : gqK < Om1 := gq_gam_lt_Om1

/-! ## The invariant -/

/-- **The invariant of a family of gated digit systems below `λ`**: base index `G + β`, base `φ(1, gpI x + β)`,
offset `Γ_{x+1} + gpOff β`, base gate `≤ β`, coherence of readings and gates, the gate of an earlier bound
`≤ max β ε₀`. -/
structure GqInv (l : Ordinal.{0}) (F : Ordinal.{0} → GqD) : Prop where
  ix : ∀ β, β < l → (F β).ix = gcG 0 + β
  b : ∀ β, β < l → ∀ x, InE x → x < Om1 → (F β).b x = veblen 1 (gpI x + β)
  ba : ∀ β, β < l → ∀ x, (F β).ba x = lgG x + gpOff β
  γ : ∀ β, β < l → (F β).γ ≤ β
  cohR : ∀ β γ, β ≤ γ → γ < l → ∀ c x, c < (F β).B → (F γ).R c x = (F β).R c x
  cohg : ∀ β γ, β ≤ γ → γ < l → ∀ c, c < (F β).B → (F γ).g c = (F β).g c
  cf : ∀ β γ, β < γ → γ < l → (F γ).g (F β).B ≤ max β ε₀

namespace GqInv

variable {l : Ordinal.{0}} {F : Ordinal.{0} → GqD} (H : GqInv l F)
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

theorem congr {G : Ordinal.{0} → GqD} (hFG : ∀ β, β < l → G β = F β) : GqInv l G where
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

end GqInv

theorem gqInv_zero (F : Ordinal.{0} → GqD) : GqInv 0 F where
  ix := fun _ h => absurd h (not_lt.2 zero_le)
  b := fun _ h => absurd h (not_lt.2 zero_le)
  ba := fun _ h => absurd h (not_lt.2 zero_le)
  γ := fun _ h => absurd h (not_lt.2 zero_le)
  cohR := fun _ _ _ h => absurd h (not_lt.2 zero_le)
  cohg := fun _ _ _ h => absurd h (not_lt.2 zero_le)
  cf := fun _ _ _ h => absurd h (not_lt.2 zero_le)

/-! ## The union at a limit -/

/-- The start: the codes below `G` as a gated digit system with gate `0`. -/
noncomputable def gqGl : GqD := GqD.ofGo goGl

/-- **The chain at a limit `λ < Γ₀`**: the systems `F (gqFs λ k)`, base gate `λ`. -/
noncomputable def gqChain (l : Ordinal.{0}) (hl : IsSuccLimit l) (hlK : l < gqK) (F : Ordinal.{0} → GqD)
    (H : GqInv l F) : GqSeq where
  D := fun k => F (gqFs l k)
  ix0 := gcG 0
  i := gpI
  a := lgG
  δ := gqFs l
  s := fun k => gpOff (gqFs l k)
  Δ := l
  T := l
  γω := l
  hix := fun k => H.ix _ (gqFs_lt hl (hlK.trans gqK_lt_Om1) k)
  hb := fun k x hx hx1 => H.b _ (gqFs_lt hl (hlK.trans gqK_lt_Om1) k) x hx hx1
  hba := fun k x => H.ba _ (gqFs_lt hl (hlK.trans gqK_lt_Om1) k) x
  coh_R := fun k c x hc => H.cohR _ _ (gqFs_mono hl (hlK.trans gqK_lt_Om1) k).le
    (gqFs_lt hl (hlK.trans gqK_lt_Om1) (k + 1)) c x hc
  coh_g := fun k c hc => H.cohg _ _ (gqFs_mono hl (hlK.trans gqK_lt_Om1) k).le
    (gqFs_lt hl (hlK.trans gqK_lt_Om1) (k + 1)) c hc
  cf_g := fun k => (H.cf _ _ (gqFs_mono hl (hlK.trans gqK_lt_Om1) k) (gqFs_lt hl (hlK.trans gqK_lt_Om1) (k + 1))).trans
    (max_le_max (gqFs_lt hl (hlK.trans gqK_lt_Om1) k).le le_rfl)
  γ_le := fun k => (H.γ _ (gqFs_lt hl (hlK.trans gqK_lt_Om1) k)).trans (gqFs_lt hl (hlK.trans gqK_lt_Om1) k).le
  γω_lt := hlK
  T_le := le_rfl
  δ_mono := gqFs_mono hl (hlK.trans gqK_lt_Om1)
  δ_lt := gqFs_lt hl (hlK.trans gqK_lt_Om1)
  δ_cof := gqFs_cof hl (hlK.trans gqK_lt_Om1)
  Δ_lim := hl
  Δ_lt := hlK
  s_lt := fun k => gpOff_lt hl (gqFs_lt hl (hlK.trans gqK_lt_Om1) k)
  s_cof := fun t ht => (gqFs_cof hl (hlK.trans gqK_lt_Om1) t ht).imp fun _ hk => hk.trans_le (le_gpOff _)
  T_lt := hlK
  ix_mem := fun S a b ha => CSet.add_mem (goGl.ix_mem S a b ha) (gq_cst_mem (S := S) a b l hlK)
  ix0_lt := gcG_lt zero_lt_one
  a_lt := goGl.ba_lt
  a_pi := fun σ ρ hB _ => goGl.ba_pi σ ρ hB
  i_big := fun x hx hx1 => (epsilon_evIx (goGl.b_E x hx hx1)).ge

/-- The family of the earlier values, extended by `gqGl`. -/
noncomputable def gqExt (l : Ordinal.{0}) (IH : ∀ β, β < l → GqD) (β : Ordinal.{0}) : GqD :=
  if h : β < l then IH β h else gqGl

open Classical in
/-- The limit step: the gated union when the invariant holds (it does below `Γ₀`, `gq_inv`). -/
noncomputable def gqLimD (l : Ordinal.{0}) (hl : IsSuccLimit l) (IH : ∀ β, β < l → GqD) : GqD :=
  if H : l < gqK ∧ GqInv l (gqExt l IH) then (gqChain l hl H.1 (gqExt l IH) H.2).toCh.lim else gqGl

/-- **THE RECURSION**: `gqD 0 = goGl`, `gqD (ν+1) = (gqD ν).step`, `gqD λ = ⋃_{β<λ} gqD β` (gate `λ`). -/
noncomputable def gqD (ν : Ordinal.{0}) : GqD :=
  Ordinal.limitRecOn (motive := fun _ => GqD) ν gqGl (fun _ D => D.step) gqLimD

theorem gqD_zero : gqD 0 = gqGl := by
  unfold gqD; rw [Ordinal.limitRecOn_zero]

theorem gqD_succ (ν : Ordinal.{0}) : gqD (ν + 1) = (gqD ν).step := by
  unfold gqD; rw [Ordinal.limitRecOn_add_one]

theorem gqD_limit {l : Ordinal.{0}} (hl : IsSuccLimit l) : gqD l = gqLimD l hl (fun β _ => gqD β) := by
  unfold gqD; rw [Ordinal.limitRecOn_limit _ _ _ _ hl]

theorem gqExt_eq {l β : Ordinal.{0}} (h : β < l) : gqExt l (fun β _ => gqD β) β = gqD β := by
  unfold gqExt; rw [dif_pos h]

/-! ## The invariant at every `ν < Γ₀` -/

/-- The new facts at the top `ν`. -/
structure GqTop (ν : Ordinal.{0}) : Prop where
  ix : (gqD ν).ix = gcG 0 + ν
  b : ∀ x, InE x → x < Om1 → (gqD ν).b x = veblen 1 (gpI x + ν)
  ba : ∀ x, (gqD ν).ba x = lgG x + gpOff ν
  γ : (gqD ν).γ ≤ ν
  cohR : ∀ β, β < ν → ∀ c x, c < (gqD β).B → (gqD ν).R c x = (gqD β).R c x
  cohg : ∀ β, β < ν → ∀ c, c < (gqD β).B → (gqD ν).g c = (gqD β).g c
  cf : ∀ β, β < ν → (gqD ν).g (gqD β).B ≤ max β ε₀

theorem gqInv_succ {ν : Ordinal.{0}} (H : GqInv ν gqD) (T : GqTop ν) : GqInv (ν + 1) gqD where
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

theorem gqInv_lim {l : Ordinal.{0}} (IH : ∀ β, β < l → GqInv (β + 1) gqD) : GqInv l gqD where
  ix := fun β h => (IH β h).ix β (lt_add_one β)
  b := fun β h => (IH β h).b β (lt_add_one β)
  ba := fun β h => (IH β h).ba β (lt_add_one β)
  γ := fun β h => (IH β h).γ β (lt_add_one β)
  cohR := fun β γ hβγ h => (IH γ h).cohR β γ hβγ (lt_add_one γ)
  cohg := fun β γ hβγ h => (IH γ h).cohg β γ hβγ (lt_add_one γ)
  cf := fun β γ hβγ h => (IH γ h).cf β γ hβγ (lt_add_one γ)

theorem gqTop_zero : GqTop 0 where
  ix := by rw [gqD_zero, add_zero]; rfl
  b := fun x hx hx1 => by
    rw [gqD_zero, add_zero]
    exact (epsilon_evIx (goGl.b_E x hx hx1)).symm
  ba := fun x => by rw [gqD_zero, gpOff_zero, add_zero]; rfl
  γ := by rw [gqD_zero]; exact le_rfl
  cohR := fun _ h => absurd h (not_lt.2 zero_le)
  cohg := fun _ h => absurd h (not_lt.2 zero_le)
  cf := fun _ h => absurd h (not_lt.2 zero_le)

theorem gqTop_succ {ν : Ordinal.{0}} (H : GqInv (ν + 1) gqD) : GqTop (ν + 1) where
  ix := by
    rw [gqD_succ, GqD.step_ix, H.ix ν (lt_add_one ν), add_assoc]
  b := fun x hx hx1 => by
    rw [gqD_succ, GqD.step_b, H.b ν (lt_add_one ν) x hx hx1, go_eN_veb, add_assoc]
  ba := fun x => by
    rw [gqD_succ, GqD.step_ba, H.ba ν (lt_add_one ν) x, gpOff_succ, add_assoc]
  γ := by rw [gqD_succ, GqD.step_γ]; exact (H.γ ν (lt_add_one ν)).trans le_self_add
  cohR := fun β hβ c x hc => by
    have hβν : β ≤ ν := Order.lt_add_one_iff.1 hβ
    rw [gqD_succ, GqD.step_R_low _ (hc.trans_le (H.B_le hβν (lt_add_one ν))) x]
    exact H.cohR β ν hβν (lt_add_one ν) c x hc
  cohg := fun β hβ c hc => by
    have hβν : β ≤ ν := Order.lt_add_one_iff.1 hβ
    rw [gqD_succ, GqD.step_g_low _ (hc.trans_le (H.B_le hβν (lt_add_one ν)))]
    exact H.cohg β ν hβν (lt_add_one ν) c hc
  cf := fun β hβ => by
    rcases (Order.lt_add_one_iff.1 hβ).lt_or_eq with h | rfl
    · rw [gqD_succ, GqD.step_g_low _ (H.B_lt h (lt_add_one ν))]
      exact H.cf β ν h (lt_add_one ν)
    · rw [gqD_succ, GqD.step_g_B]
      exact (H.γ β (lt_add_one β)).trans (le_max_left _ _)

theorem gqTop_lim {l : Ordinal.{0}} (hl : IsSuccLimit l) (hlK : l < gqK) (H : GqInv l gqD) : GqTop l := by
  have hl1 : l < Om1 := hlK.trans gqK_lt_Om1
  have Hx : GqInv l (gqExt l fun β _ => gqD β) := H.congr fun β h => gqExt_eq h
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = gqChain l hl hlK (gqExt l fun β _ => gqD β) Hx := ⟨_, rfl⟩
  have e : gqD l = Q.toCh.lim := by
    rw [gqD_limit hl, hQ]; unfold gqLimD; rw [dif_pos ⟨hlK, Hx⟩]
  have hD : ∀ k, Q.toCh.D k = gqD (gqFs l k) := fun k => by
    rw [hQ]; exact gqExt_eq (gqFs_lt hl hl1 k)
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
    have hc' : (gqD β).B < (Q.toCh.D k).B := by rw [hD]; exact H.B_lt hk (gqFs_lt hl hl1 k)
    rw [e, Q.toCh.lim_g hc', hD]
    exact H.cf β _ hk (gqFs_lt hl hl1 k)

/-- **THE INVARIANT AT EVERY `ν < Γ₀`** (one induction; the coherence is carried along). -/
theorem gq_inv : ∀ ν : Ordinal.{0}, ν < gqK → GqInv (ν + 1) gqD := by
  intro ν
  induction ν using Ordinal.limitRecOn with
  | zero => intro _; exact gqInv_succ (gqInv_zero gqD) gqTop_zero
  | add_one μ ih =>
    intro hν
    have H := ih ((lt_add_one μ).trans hν)
    exact gqInv_succ H (gqTop_succ H)
  | limit l hl ih =>
    intro hν
    have H := gqInv_lim (fun β hβ => ih β hβ (hβ.trans hν))
    exact gqInv_succ H (gqTop_lim hl hν H)

/-! ## The systems `gqD ν` -/

section Main

variable {ν : Ordinal.{0}} (hν : ν < gqK)
include hν

/-- **The bound of `gqD ν` is `φ(1, G + ν) = ε_{G+ν}`.** -/
theorem gqD_B : (gqD ν).B = veblen 1 (gcG 0 + ν) := (gq_inv ν hν).B_eq (lt_add_one ν)

/-- **The base reading of `gqD ν` is `φ(1, gpI x + ν)`** at every base. -/
theorem gqD_b {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : (gqD ν).b x = veblen 1 (gpI x + ν) :=
  (gq_inv ν hν).b ν (lt_add_one ν) x hx hx1

theorem gqD_ba (x : Ordinal.{0}) : (gqD ν).ba x = lgG x + gpOff ν := (gq_inv ν hν).ba ν (lt_add_one ν) x

/-- **The base gate of `gqD ν` is at most `ν`.** -/
theorem gqD_γ : (gqD ν).γ ≤ ν := (gq_inv ν hν).γ ν (lt_add_one ν)

end Main

/-- **`gqD γ` extends `gqD β` for `β ≤ γ < Γ₀`**; the gate of `ε_{G+β}` in `gqD γ` is `≤ max β ε₀` when `β < γ`. -/
theorem gqD_ext {β γ : Ordinal.{0}} (hβγ : β ≤ γ) (hγ : γ < gqK) :
    (∀ c x, c < (gqD β).B → (gqD γ).R c x = (gqD β).R c x) ∧
    (∀ c, c < (gqD β).B → (gqD γ).g c = (gqD β).g c) ∧ (β < γ → (gqD γ).g (gqD β).B ≤ max β ε₀) :=
  ⟨(gq_inv γ hγ).cohR β γ hβγ (lt_add_one γ), (gq_inv γ hγ).cohg β γ hβγ (lt_add_one γ),
    fun h => (gq_inv γ hγ).cf β γ h (lt_add_one γ)⟩

theorem gqD_B_lt {β γ : Ordinal.{0}} (hβγ : β < γ) (hγ : γ < gqK) : (gqD β).B < (gqD γ).B :=
  (gq_inv γ hγ).B_lt hβγ (lt_add_one γ)

/-- **The bound of `gqD λ` is the union of the earlier bounds** (`λ` a limit below `Γ₀`). -/
theorem gqD_lim_cof {l : Ordinal.{0}} (hl : IsSuccLimit l) (hlK : l < gqK) {c : Ordinal.{0}} (hc : c < (gqD l).B) :
    ∃ β, β < l ∧ c < (gqD β).B := by
  rw [gqD_B hlK] at hc
  obtain ⟨t, ht, hct⟩ := ((isNormal_veblen 1).lt_iff_exists_lt (isSuccLimit_add _ hl)).1 hc
  obtain ⟨d, hd, htd⟩ := (lt_add_iff hl.bot_lt.ne').1 ht
  refine ⟨d, hd, ?_⟩
  rw [gqD_B (hd.trans hlK)]
  exact hct.trans_le ((isNormal_veblen 1).monotone htd)

/-- **The index `ε₀` is reached**: `(gqD ε₀).B = ε_{G+ε₀}`, base reading `φ(1, gpI x + ε₀)`, base gate `ε₀`. -/
theorem gqD_eps0 : (gqD ε₀).B = veblen 1 (gcG 0 + ε₀) ∧
    (∀ x, InE x → x < Om1 → (gqD ε₀).b x = veblen 1 (gpI x + ε₀)) ∧ (gqD ε₀).γ ≤ ε₀ := by
  have h : (ε₀ : Ordinal.{0}) < gqK := gq_eps0_lt_gam
  exact ⟨gqD_B h, fun x hx hx1 => gqD_b h hx hx1, gqD_γ h⟩

end Googology.Trans.PoR.InaccPsi.R2.Gq
