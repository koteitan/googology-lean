import Googology.Trans.PoR.InaccPsi.R2.HnPkL

/-!
# HnRec: ONE RECURSION OF GATED PACKAGES OVER THE BAND LEVELS `Ω₁·Ω₁ + Ω₁·μ`, `μ < Ω₁`

PORT of `Hl.HlRec` to the band level data: the package at `μ = 0` is `hnPkSq` (the level `Ω₁·Ω₁`, built in `Hn.HnQU`
from the packages `Hl.hlkPk μ` by a union over all `μ < Ω₁` at every pseudo-base), the successor is `HnPk.succ`, and
at a limit `λ` the level datum is `hnMLv λ` (gate `hlGt λ`).  What differs from `Hl.HlRec`: the levels
`Ω₁·Ω₁ + Ω₁·μ` read `x·x + x·μ` in place of `Ω₁·(1+μ)` read `x·(1+μ)`, the gate bound `hlGt μ` in place of
`hlGt (1+μ)`, and the start `hnPkSq` in place of `Hl.hlPk1`.

No new axiom.  New definitions: `HnkCoh`, `hnkSeqOf`, `hnkLimF`, `hnkPk`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hn

open Googology.Trans.PoR.InaccPsi.R2.Hl

open Googology.Trans.PoR.InaccPsi.R2.Hk

open Googology.Trans.PoR.InaccPsi.R2.Hj Googology.Trans.PoR.InaccPsi.R2.Hi Googology.Trans.PoR.InaccPsi.R2.Hg
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

/-- **The condition at a limit**: the earlier packages have the levels `Ω₁·(1+μ)` (read `x·(1+μ)`) with gates at
most `hlGt (1+μ)`, the gates grow, and later steps extend earlier ones at every pseudo-base. -/
def HnkCoh (l : Ordinal.{0}) (IH : ∀ μ, μ < l → HnPk) : Prop :=
  (∀ μ (h : μ < l), (IH μ h).Λ.L = Om1 * Om1 + Om1 * μ ∧ ∀ x, (IH μ h).Λ.g < x → (IH μ h).Λ.l x = x * x + x * μ) ∧
    (∀ μ (h : μ < l), (IH μ h).Λ.g ≤ hlGt μ) ∧
    ∀ μ' μ (h' : μ' < l) (h : μ < l), μ' < μ → (IH μ' h').Λ.g ≤ (IH μ h).Λ.g ∧ HnkExt (IH μ' h') (IH μ h)

/-- **The coherent sequence at a limit `λ < Γ₀`**: the packages at `heFs λ k`, below the gated level datum
`Ω₁·(1+λ)`. -/
noncomputable def hnkSeqOf (l : Ordinal.{0}) (hl : IsSuccLimit l) (hle : l < Om1) (IH : ∀ μ, μ < l → HnPk)
    (H : HnkCoh l IH) : HnkSeq (hnMLv l hle) where
  M := l
  K := fun k => IH (heFs l k) (heFs_lt hl (hl_om hle) k)
  Ms := fun k => heFs l k
  L_eq := rfl
  l_eq := fun _ h => hnMLv_l _ _ h
  KL := fun k => (H.1 _ _).1
  Kl := fun k x h => (H.1 _ _).2 x h
  lt := fun k => heFs_lt hl (hl_om hle) k
  mono := fun k => heFs_mono hl (hl_om hle) k
  cof := fun t ht => heFs_cof hl (hl_om hle) t ht
  Kg := fun k => (H.2.1 _ _).trans (hlGt_mono (heFs_lt hl (hl_om hle) k).le)
  Kgm := fun k => (H.2.2 _ _ _ _ (heFs_mono hl (hl_om hle) k)).1
  ext := fun k => (H.2.2 _ _ _ _ (heFs_mono hl (hl_om hle) k)).2

open Classical in
/-- **The limit case**: the limit package of the coherent sequence (when `λ < Γ₀` and the condition holds). -/
noncomputable def hnkLimF (l : Ordinal.{0}) (hl : IsSuccLimit l) (IH : ∀ μ, μ < l → HnPk) : HnPk :=
  if h : l < Om1 ∧ HnkCoh l IH then hnkPkL (hnkSeqOf l hl h.1 IH h.2) else hnPkSq

/-- **THE PACKAGES OF ALL LEVELS `Ω₁·(1+μ)`, BY ONE RECURSION ON `μ`** (gated level data). -/
noncomputable def hnkPk (μ : Ordinal.{0}) : HnPk :=
  Ordinal.limitRecOn (motive := fun _ => HnPk) μ hnPkSq (fun _ K => K.succ) hnkLimF

theorem hnkPk_zero : hnkPk 0 = hnPkSq := by unfold hnkPk; rw [Ordinal.limitRecOn_zero]

theorem hnkPk_succ (μ : Ordinal.{0}) : hnkPk (μ + 1) = (hnkPk μ).succ := by
  unfold hnkPk; rw [Ordinal.limitRecOn_add_one]

theorem hnkPk_limit {l : Ordinal.{0}} (hl : IsSuccLimit l) : hnkPk l = hnkLimF l hl (fun μ _ => hnkPk μ) := by
  unfold hnkPk; rw [Ordinal.limitRecOn_limit _ _ _ _ hl]

theorem hnk_B_mono {K' K : HnPk} {μ' μ : Ordinal.{0}} (hK' : K'.Λ.L = Om1 * Om1 + Om1 * μ')
    (hK : K.Λ.L = Om1 * Om1 + Om1 * μ) (h : μ' ≤ μ) (F : Ordinal.{0}) :
    hdNx (K'.Λ.L + 0) F ≤ hdNx (K.Λ.L + 0) F := by
  rw [hK', hK]
  exact hdNx_mono (add_le_add (add_le_add le_rfl (mul_le_mul_left' h _)) le_rfl) _

/-- **`a·a + a·b + a ≤ a·a + a·c`** for `b < c`. -/
theorem hnk_mul_le {a b c : Ordinal.{0}} (h : b < c) : a * a + a * b + a ≤ a * a + a * c := by
  rw [add_assoc]; exact add_le_add le_rfl (HkSeq.mul_le h)

/-- **THE INVARIANT**: for every `μ < Γ₀` the package `hnkPk μ` has the level `Ω₁·(1+μ)` read `x·(1+μ)` with gate
`≤ hlGt (1+μ)`, and for every `μ' < μ` its gate is `≥` that of `hnkPk μ'` and its step extends the step of
`hnkPk μ'` at every pseudo-base. -/
theorem hnkPk_inv : ∀ μ, μ < Om1 → ((hnkPk μ).Λ.L = Om1 * Om1 + Om1 * μ ∧
    ∀ x, (hnkPk μ).Λ.g < x → (hnkPk μ).Λ.l x = x * x + x * μ) ∧
    (hnkPk μ).Λ.g ≤ hlGt μ ∧
    ∀ μ', μ' < μ → (hnkPk μ').Λ.g ≤ (hnkPk μ).Λ.g ∧ HnkExt (hnkPk μ') (hnkPk μ) := by
  intro μ
  induction μ using WellFoundedLT.induction with
  | ind μ IH =>
  intro hμ
  rcases zero_or_succ_or_isSuccLimit μ with h0 | ⟨ν, hν⟩ | hlim
  · subst h0
    rw [hnkPk_zero]
    refine ⟨⟨by show Om1 * Om1 = _; rw [mul_zero, add_zero], fun x _ => by show x * x = _; rw [mul_zero, add_zero]⟩,
      zero_le, fun μ' h => absurd h (not_lt.2 zero_le)⟩
  · have hν' : μ = ν + 1 := by rw [← hν, succ_eq_add_one]
    subst hν'
    have hνε : ν < Om1 := (lt_add_one ν).trans hμ
    obtain ⟨⟨hL, hl⟩, hg, hext⟩ := IH ν (lt_add_one ν) hνε
    refine ⟨⟨?_, fun x hgx => ?_⟩, ?_, fun μ' hμ' => ⟨?_, ?_⟩⟩
    · rw [hnkPk_succ]; show (hnkPk ν).Λ.L + Om1 = _; rw [hL, mul_add_one, add_assoc]
    · rw [hnkPk_succ] at hgx ⊢; show (hnkPk ν).Λ.l x + x = _; rw [hl x hgx, mul_add_one, add_assoc]
    · rw [hnkPk_succ]; show (hnkPk ν).Λ.g ≤ _
      exact hg.trans (hlGt_mono (le_add_right le_rfl))
    · rw [hnkPk_succ]; show (hnkPk μ').Λ.g ≤ (hnkPk ν).Λ.g
      rcases (Order.lt_add_one_iff.1 hμ').lt_or_eq with hlt | heq
      · exact (hext μ' hlt).1
      · rw [heq]
    · rw [hnkPk_succ]
      intro hg' hL' hl' Q U hU c x hc
      have hsh := hnw_shape_dn Q ((hnkPk ν).h0 Q.dn U hU)
      show (hnwU Q.toW (hnkPk ν).St0 (hnkPk ν).h0 ((hnkPk ν).St0 Q.dn U hU) hsh).R c x = _ ∧
        (hnwU Q.toW (hnkPk ν).St0 (hnkPk ν).h0 ((hnkPk ν).St0 Q.dn U hU) hsh).g c = _
      rcases (Order.lt_add_one_iff.1 hμ').lt_or_eq with hlt | heq
      · obtain ⟨⟨hL1, hl1⟩, -⟩ := IH μ' (hlt.trans (lt_add_one ν)) (hlt.trans hνε)
        have hLa : (hnkPk μ').Λ.L + Om1 ≤ (hnkPk ν).Λ.L := by rw [hL1, hL]; exact hnk_mul_le hlt
        have hla : ∀ x, InE x → x < Om1 → (hnkPk ν).Λ.g < x → (hnkPk μ').Λ.l x + x ≤ (hnkPk ν).Λ.l x :=
          fun x _ _ hgx => by rw [hl1 x ((hext μ' hlt).1.trans_lt hgx), hl x hgx]; exact hnk_mul_le hlt
        have hc0 : c < ((hnkPk ν).St0 Q.dn U hU).B := by
          rw [((hnkPk ν).h0 Q.dn U hU).B]
          rw [((hnkPk μ').h0 _ U hU).B] at hc
          exact hc.trans_le (hnk_B_mono hL1 hL hlt.le _)
        obtain ⟨r1, g1⟩ := (hext μ' hlt).2 (hext μ' hlt).1 hLa hla Q.dn U hU c x hc
        exact ⟨(hnwU_R0 Q.toW (hnkPk ν).St0 (hnkPk ν).h0 _ hsh hc0 x).trans r1,
          (hnwU_g0 Q.toW (hnkPk ν).St0 (hnkPk ν).h0 _ hsh hc0).trans g1⟩
      · subst heq
        exact ⟨hnwU_R0 Q.toW (hnkPk μ').St0 (hnkPk μ').h0 _ hsh hc x,
          hnwU_g0 Q.toW (hnkPk μ').St0 (hnkPk μ').h0 _ hsh hc⟩
  · have hcoh : HnkCoh μ (fun μ' _ => hnkPk μ') :=
      ⟨fun μ' h => (IH μ' h (h.trans hμ)).1, fun μ' h => (IH μ' h (h.trans hμ)).2.1,
        fun μ₁ μ₂ h₁ h₂ h12 => (IH μ₂ h₂ (h₂.trans hμ)).2.2 μ₁ h12⟩
    have e : hnkPk μ = hnkPkL (hnkSeqOf μ hlim hμ (fun μ' _ => hnkPk μ') hcoh) := by
      rw [hnkPk_limit hlim]; unfold hnkLimF; rw [dif_pos ⟨hμ, hcoh⟩]
    have eg : (hnkPk μ).Λ.g = hlGt μ := by rw [e]; rfl
    refine ⟨⟨by rw [e]; rfl, fun x h => by rw [e] at h ⊢; exact hnMLv_l μ hμ h⟩,
      eg.le, fun μ' hμ' => ⟨?_, ?_⟩⟩
    · rw [eg]
      exact (IH μ' hμ' (hμ'.trans hμ)).2.1.trans (hlGt_mono hμ'.le)
    rw [e]
    intro hg' hL' hl' Q U hU c x hc
    let H := hnkSeqOf μ hlim hμ (fun μ' _ => hnkPk μ') hcoh
    obtain ⟨k, hk⟩ := heFs_cof hlim (hl_om hμ) μ' hμ'
    have hkl := heFs_lt hlim (hl_om hμ) k
    obtain ⟨⟨hLk, hlk⟩, -, hextk⟩ := IH _ hkl (hkl.trans hμ)
    obtain ⟨⟨hL1, hl1⟩, -⟩ := IH μ' hμ' (hμ'.trans hμ)
    have hLa : (hnkPk μ').Λ.L + Om1 ≤ (hnkPk (heFs μ k)).Λ.L := by rw [hL1, hLk]; exact hnk_mul_le hk
    have hla : ∀ x, InE x → x < Om1 → (hnkPk (heFs μ k)).Λ.g < x →
        (hnkPk μ').Λ.l x + x ≤ (hnkPk (heFs μ k)).Λ.l x :=
      fun x _ _ hgx => by rw [hl1 x ((hextk μ' hk).1.trans_lt hgx), hlk x hgx]; exact hnk_mul_le hk
    have hc' : c < (H.D Q U hU k).B := by
      rw [(H.D_spec Q U hU k).B]
      rw [((hnkPk μ').h0 _ U hU).B] at hc
      exact hc.trans_le (hnk_B_mono hL1 hLk hk.le _)
    obtain ⟨r1, g1⟩ := hnkStL_ext H Q U hU k hc' x
    obtain ⟨r2, g2⟩ := (hextk μ' hk).2 (hextk μ' hk).1 hLa hla (Q.lowr (H.K k).Λ (H.Kg k) (H.hL k) (H.hl k)) U hU
      c x hc
    exact ⟨r1.trans r2, g1.trans g2⟩

theorem hnkPk_L {μ : Ordinal.{0}} (hμ : μ < Om1) : (hnkPk μ).Λ.L = Om1 * Om1 + Om1 * μ := (hnkPk_inv μ hμ).1.1

theorem hnkPk_l {μ : Ordinal.{0}} (hμ : μ < Om1) {x : Ordinal.{0}} (hx : (hnkPk μ).Λ.g < x) :
    (hnkPk μ).Λ.l x = x * x + x * μ :=
  (hnkPk_inv μ hμ).1.2 x hx

theorem hnkPk_g {μ : Ordinal.{0}} (hμ : μ < Om1) : (hnkPk μ).Λ.g ≤ hlGt μ := (hnkPk_inv μ hμ).2.1

theorem hnkPk_gmono {μ' μ : Ordinal.{0}} (hμ : μ < Om1) (h : μ' < μ) : (hnkPk μ').Λ.g ≤ (hnkPk μ).Λ.g :=
  ((hnkPk_inv μ hμ).2.2 μ' h).1

theorem hnkPk_ext {μ' μ : Ordinal.{0}} (hμ : μ < Om1) (h : μ' < μ) : HnkExt (hnkPk μ') (hnkPk μ) :=
  ((hnkPk_inv μ hμ).2.2 μ' h).2

theorem hnkPk_coh {l : Ordinal.{0}} (hle : l < Om1) : HnkCoh l (fun μ _ => hnkPk μ) :=
  ⟨fun μ h => (hnkPk_inv μ (h.trans hle)).1, fun μ h => hnkPk_g (h.trans hle),
    fun _ _ _ h₂ h12 => ⟨hnkPk_gmono (h₂.trans hle) h12, hnkPk_ext (h₂.trans hle) h12⟩⟩

/-- **At a limit `λ < Γ₀` the package is the limit package of the coherent sequence.** -/
theorem hnkPk_lim_eq {l : Ordinal.{0}} (hl : IsSuccLimit l) (hle : l < Om1) :
    hnkPk l = hnkPkL (hnkSeqOf l hl hle (fun μ _ => hnkPk μ) (hnkPk_coh hle)) := by
  rw [hnkPk_limit hl]; unfold hnkLimF; rw [dif_pos ⟨hle, hnkPk_coh hle⟩]

theorem hnkPk_lim_Λ {l : Ordinal.{0}} (hl : IsSuccLimit l) (hle : l < Om1) :
    (hnkPk l).Λ = hnMLv l hle := by
  rw [hnkPk_lim_eq hl hle]; rfl

/-- **The gate of `hnkPk ν` below an `ε`-number `σ` forces `ν < σ`.** -/
theorem hnkPk_g_lt : ∀ ν, ν < Om1 → ∀ σ, InE σ → (hnkPk ν).Λ.g < σ → ν < σ := by
  intro ν
  induction ν using WellFoundedLT.induction with
  | ind ν IH =>
  intro hν σ hσ hg
  rcases zero_or_succ_or_isSuccLimit ν with h0 | ⟨μ, hμ⟩ | hlim
  · rw [h0]; exact hσ.pos
  · have hμ' : ν = μ + 1 := by rw [← hμ, succ_eq_add_one]
    subst hμ'
    have hg' : (hnkPk μ).Λ.g < σ := by rw [hnkPk_succ] at hg; exact hg
    exact (ev_isSuccLimit_of_inE hσ).add_one_lt (IH μ (lt_add_one μ) ((lt_add_one μ).trans hν) σ hσ hg')
  · rw [hnkPk_lim_Λ hlim hν] at hg
    exact hl_gt_E hσ hg

/-- **Every `hnkPk μ`, `μ < Ω₁`, and its successor have the outer-field bound `ℓ(x) + x < x·x·2`.** -/
theorem hnkNB {μ : Ordinal.{0}} (hμ : μ < Om1) : HnNB (hnkPk μ).Λ :=
  hn_NB_of (fun x hx hg => hnkPk_g_lt μ hμ x hx hg) (fun x hg => hnkPk_l hμ hg)

theorem hnkNB' {μ : Ordinal.{0}} (hμ : μ < Om1) : HnNB (hnkPk μ).Λ.succ := by
  have h := hnkNB (gl_Om1_lim.add_one_lt hμ)
  rwa [hnkPk_succ] at h

end Googology.Trans.PoR.InaccPsi.R2.Hn
