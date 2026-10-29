import Googology.Trans.PoR.InaccPsi.R2.HlPkL

/-!
# HlRec: ONE RECURSION OF GATED PACKAGES OVER THE LEVELS `Ω₁·(1+μ)`, `μ < Ω₁`

PORT of `Hk.HkRec` with the range `μ < Ω₁` in place of `μ < ε₀`: at a limit `λ` the level datum is `hlMLv (1+λ)`
(gate `hlGt (1+λ)`).  The invariant `hlkPk_inv` adds: the gate of `hlkPk μ` is `≤ hlGt (1+μ)` and grows with `μ`;
the reading is `x·(1+μ)` above the gate.

What differs from the source: the level datum is a GATED one (`Hl.HlLv`: Lemma EXACT for the reading `ℓ` only at
base pairs `(σ, ρ)` above the level gate `g`, the hull membership of `L` only at `0 < a`, `g < b`, the code gate
`g < Z` only when a code over `Z` exists at the level); every pseudo-base and base carries `g ≤` its reading gate
(fields `lg`), and the code-gate fields take the extra hypothesis `g < Z`.  Proofs are otherwise those of the source;
names: prefix `hl`/`Hl` in place of `hj`/`Hj`.

No new axiom.  New definitions: `HlkCoh`, `hlkSeqOf`, `hlkLimF`, `hlkPk`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hl

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

theorem hl_one_add {l : Ordinal.{0}} (hl : l < Om1) : 1 + l < Om1 :=
  (inE_indec gl_Om1_E).add_lt hg_one_lt_Om1 hl

theorem hl_om {l : Ordinal.{0}} (hl : l < Om1) : l < Om (1 : Ordinal.{0}) := by rwa [← Br.Om1_eq]

/-- **The condition at a limit**: the earlier packages have the levels `Ω₁·(1+μ)` (read `x·(1+μ)`) with gates at
most `hlGt (1+μ)`, the gates grow, and later steps extend earlier ones at every pseudo-base. -/
def HlkCoh (l : Ordinal.{0}) (IH : ∀ μ, μ < l → HlPk) : Prop :=
  (∀ μ (h : μ < l), (IH μ h).Λ.L = Om1 * (1 + μ) ∧ ∀ x, (IH μ h).Λ.g < x → (IH μ h).Λ.l x = x * (1 + μ)) ∧
    (∀ μ (h : μ < l), (IH μ h).Λ.g ≤ hlGt (1 + μ)) ∧
    ∀ μ' μ (h' : μ' < l) (h : μ < l), μ' < μ → (IH μ' h').Λ.g ≤ (IH μ h).Λ.g ∧ HlkExt (IH μ' h') (IH μ h)

/-- **The coherent sequence at a limit `λ < Γ₀`**: the packages at `heFs λ k`, below the gated level datum
`Ω₁·(1+λ)`. -/
noncomputable def hlkSeqOf (l : Ordinal.{0}) (hl : IsSuccLimit l) (hle : l < Om1) (IH : ∀ μ, μ < l → HlPk)
    (H : HlkCoh l IH) : HlkSeq (hlMLv (1 + l) le_self_add (hl_one_add hle)) where
  M := 1 + l
  K := fun k => IH (heFs l k) (heFs_lt hl (hl_om hle) k)
  Ms := fun k => 1 + heFs l k
  L_eq := rfl
  l_eq := fun _ h => hlMLv_l _ _ _ h
  KL := fun k => (H.1 _ _).1
  Kl := fun k x h => (H.1 _ _).2 x h
  lt := fun k => (add_lt_add_iff_left 1).2 (heFs_lt hl (hl_om hle) k)
  mono := fun k => (add_lt_add_iff_left 1).2 (heFs_mono hl (hl_om hle) k)
  cof := fun t ht => by
    rw [one_add_of_omega0_le (omega0_le_of_isSuccLimit hl)] at ht
    obtain ⟨k, hk⟩ := heFs_cof hl (hl_om hle) t ht
    exact ⟨k, hk.trans_le le_add_self⟩
  Kg := fun k => (H.2.1 _ _).trans (hlGt_mono (add_le_add le_rfl (heFs_lt hl (hl_om hle) k).le))
  Kgm := fun k => (H.2.2 _ _ _ _ (heFs_mono hl (hl_om hle) k)).1
  ext := fun k => (H.2.2 _ _ _ _ (heFs_mono hl (hl_om hle) k)).2

open Classical in
/-- **The limit case**: the limit package of the coherent sequence (when `λ < Γ₀` and the condition holds). -/
noncomputable def hlkLimF (l : Ordinal.{0}) (hl : IsSuccLimit l) (IH : ∀ μ, μ < l → HlPk) : HlPk :=
  if h : l < Om1 ∧ HlkCoh l IH then hlkPkL (hlkSeqOf l hl h.1 IH h.2) else hlPk1

/-- **THE PACKAGES OF ALL LEVELS `Ω₁·(1+μ)`, BY ONE RECURSION ON `μ`** (gated level data). -/
noncomputable def hlkPk (μ : Ordinal.{0}) : HlPk :=
  Ordinal.limitRecOn (motive := fun _ => HlPk) μ hlPk1 (fun _ K => K.succ) hlkLimF

theorem hlkPk_zero : hlkPk 0 = hlPk1 := by unfold hlkPk; rw [Ordinal.limitRecOn_zero]

theorem hlkPk_succ (μ : Ordinal.{0}) : hlkPk (μ + 1) = (hlkPk μ).succ := by
  unfold hlkPk; rw [Ordinal.limitRecOn_add_one]

theorem hlkPk_limit {l : Ordinal.{0}} (hl : IsSuccLimit l) : hlkPk l = hlkLimF l hl (fun μ _ => hlkPk μ) := by
  unfold hlkPk; rw [Ordinal.limitRecOn_limit _ _ _ _ hl]

theorem hlk_B_mono {K' K : HlPk} {μ' μ : Ordinal.{0}} (hK' : K'.Λ.L = Om1 * (1 + μ'))
    (hK : K.Λ.L = Om1 * (1 + μ)) (h : μ' ≤ μ) (F : Ordinal.{0}) : hdNx (K'.Λ.L + 0) F ≤ hdNx (K.Λ.L + 0) F := by
  rw [hK', hK]
  exact hdNx_mono (add_le_add (mul_le_mul_left' (add_le_add le_rfl h) _) le_rfl) _

/-- **THE INVARIANT**: for every `μ < Γ₀` the package `hlkPk μ` has the level `Ω₁·(1+μ)` read `x·(1+μ)` with gate
`≤ hlGt (1+μ)`, and for every `μ' < μ` its gate is `≥` that of `hlkPk μ'` and its step extends the step of
`hlkPk μ'` at every pseudo-base. -/
theorem hlkPk_inv : ∀ μ, μ < Om1 → ((hlkPk μ).Λ.L = Om1 * (1 + μ) ∧
    ∀ x, (hlkPk μ).Λ.g < x → (hlkPk μ).Λ.l x = x * (1 + μ)) ∧
    (hlkPk μ).Λ.g ≤ hlGt (1 + μ) ∧
    ∀ μ', μ' < μ → (hlkPk μ').Λ.g ≤ (hlkPk μ).Λ.g ∧ HlkExt (hlkPk μ') (hlkPk μ) := by
  intro μ
  induction μ using WellFoundedLT.induction with
  | ind μ IH =>
  intro hμ
  rcases zero_or_succ_or_isSuccLimit μ with h0 | ⟨ν, hν⟩ | hlim
  · subst h0
    rw [hlkPk_zero]
    refine ⟨⟨by show Om1 = _; rw [add_zero, mul_one], fun x _ => by show x = _; rw [add_zero, mul_one]⟩,
      zero_le, fun μ' h => absurd h (not_lt.2 zero_le)⟩
  · have hν' : μ = ν + 1 := by rw [← hν, succ_eq_add_one]
    subst hν'
    have hνε : ν < Om1 := (lt_add_one ν).trans hμ
    obtain ⟨⟨hL, hl⟩, hg, hext⟩ := IH ν (lt_add_one ν) hνε
    refine ⟨⟨?_, fun x hgx => ?_⟩, ?_, fun μ' hμ' => ⟨?_, ?_⟩⟩
    · rw [hlkPk_succ]; show (hlkPk ν).Λ.L + Om1 = _; rw [hL, ← add_assoc, mul_add_one]
    · rw [hlkPk_succ] at hgx ⊢; show (hlkPk ν).Λ.l x + x = _; rw [hl x hgx, ← add_assoc, mul_add_one]
    · rw [hlkPk_succ]; show (hlkPk ν).Λ.g ≤ _
      exact hg.trans (hlGt_mono (add_le_add le_rfl (le_add_right le_rfl)))
    · rw [hlkPk_succ]; show (hlkPk μ').Λ.g ≤ (hlkPk ν).Λ.g
      rcases (Order.lt_add_one_iff.1 hμ').lt_or_eq with hlt | heq
      · exact (hext μ' hlt).1
      · rw [heq]
    · rw [hlkPk_succ]
      intro hg' hL' hl' Q U hU c x hc
      have hsh := hlw_shape_dn Q ((hlkPk ν).h0 Q.dn U hU)
      show (hlwU Q.toW (hlkPk ν).St0 (hlkPk ν).h0 ((hlkPk ν).St0 Q.dn U hU) hsh).R c x = _ ∧
        (hlwU Q.toW (hlkPk ν).St0 (hlkPk ν).h0 ((hlkPk ν).St0 Q.dn U hU) hsh).g c = _
      rcases (Order.lt_add_one_iff.1 hμ').lt_or_eq with hlt | heq
      · obtain ⟨⟨hL1, hl1⟩, -⟩ := IH μ' (hlt.trans (lt_add_one ν)) (hlt.trans hνε)
        have hLa : (hlkPk μ').Λ.L + Om1 ≤ (hlkPk ν).Λ.L := by rw [hL1, hL]; exact hk_mul_le hlt
        have hla : ∀ x, InE x → x < Om1 → (hlkPk ν).Λ.g < x → (hlkPk μ').Λ.l x + x ≤ (hlkPk ν).Λ.l x :=
          fun x _ _ hgx => by rw [hl1 x ((hext μ' hlt).1.trans_lt hgx), hl x hgx]; exact hk_mul_le hlt
        have hc0 : c < ((hlkPk ν).St0 Q.dn U hU).B := by
          rw [((hlkPk ν).h0 Q.dn U hU).B]
          rw [((hlkPk μ').h0 _ U hU).B] at hc
          exact hc.trans_le (hlk_B_mono hL1 hL hlt.le _)
        obtain ⟨r1, g1⟩ := (hext μ' hlt).2 (hext μ' hlt).1 hLa hla Q.dn U hU c x hc
        exact ⟨(hlwU_R0 Q.toW (hlkPk ν).St0 (hlkPk ν).h0 _ hsh hc0 x).trans r1,
          (hlwU_g0 Q.toW (hlkPk ν).St0 (hlkPk ν).h0 _ hsh hc0).trans g1⟩
      · subst heq
        exact ⟨hlwU_R0 Q.toW (hlkPk μ').St0 (hlkPk μ').h0 _ hsh hc x,
          hlwU_g0 Q.toW (hlkPk μ').St0 (hlkPk μ').h0 _ hsh hc⟩
  · have hcoh : HlkCoh μ (fun μ' _ => hlkPk μ') :=
      ⟨fun μ' h => (IH μ' h (h.trans hμ)).1, fun μ' h => (IH μ' h (h.trans hμ)).2.1,
        fun μ₁ μ₂ h₁ h₂ h12 => (IH μ₂ h₂ (h₂.trans hμ)).2.2 μ₁ h12⟩
    have e : hlkPk μ = hlkPkL (hlkSeqOf μ hlim hμ (fun μ' _ => hlkPk μ') hcoh) := by
      rw [hlkPk_limit hlim]; unfold hlkLimF; rw [dif_pos ⟨hμ, hcoh⟩]
    have eg : (hlkPk μ).Λ.g = hlGt (1 + μ) := by rw [e]; rfl
    refine ⟨⟨by rw [e]; rfl, fun x h => by rw [e] at h ⊢; exact hlMLv_l (1 + μ) le_self_add (hl_one_add hμ) h⟩,
      eg.le, fun μ' hμ' => ⟨?_, ?_⟩⟩
    · rw [eg]
      exact (IH μ' hμ' (hμ'.trans hμ)).2.1.trans (hlGt_mono (add_le_add le_rfl hμ'.le))
    rw [e]
    intro hg' hL' hl' Q U hU c x hc
    let H := hlkSeqOf μ hlim hμ (fun μ' _ => hlkPk μ') hcoh
    obtain ⟨k, hk⟩ := heFs_cof hlim (hl_om hμ) μ' hμ'
    have hkl := heFs_lt hlim (hl_om hμ) k
    obtain ⟨⟨hLk, hlk⟩, -, hextk⟩ := IH _ hkl (hkl.trans hμ)
    obtain ⟨⟨hL1, hl1⟩, -⟩ := IH μ' hμ' (hμ'.trans hμ)
    have hLa : (hlkPk μ').Λ.L + Om1 ≤ (hlkPk (heFs μ k)).Λ.L := by rw [hL1, hLk]; exact hk_mul_le hk
    have hla : ∀ x, InE x → x < Om1 → (hlkPk (heFs μ k)).Λ.g < x →
        (hlkPk μ').Λ.l x + x ≤ (hlkPk (heFs μ k)).Λ.l x :=
      fun x _ _ hgx => by rw [hl1 x ((hextk μ' hk).1.trans_lt hgx), hlk x hgx]; exact hk_mul_le hk
    have hc' : c < (H.D Q U hU k).B := by
      rw [(H.D_spec Q U hU k).B]
      rw [((hlkPk μ').h0 _ U hU).B] at hc
      exact hc.trans_le (hlk_B_mono hL1 hLk hk.le _)
    obtain ⟨r1, g1⟩ := hlkStL_ext H Q U hU k hc' x
    obtain ⟨r2, g2⟩ := (hextk μ' hk).2 (hextk μ' hk).1 hLa hla (Q.lowr (H.K k).Λ (H.Kg k) (H.hL k) (H.hl k)) U hU
      c x hc
    exact ⟨r1.trans r2, g1.trans g2⟩

theorem hlkPk_L {μ : Ordinal.{0}} (hμ : μ < Om1) : (hlkPk μ).Λ.L = Om1 * (1 + μ) := (hlkPk_inv μ hμ).1.1

theorem hlkPk_l {μ : Ordinal.{0}} (hμ : μ < Om1) {x : Ordinal.{0}} (hx : (hlkPk μ).Λ.g < x) :
    (hlkPk μ).Λ.l x = x * (1 + μ) :=
  (hlkPk_inv μ hμ).1.2 x hx

theorem hlkPk_g {μ : Ordinal.{0}} (hμ : μ < Om1) : (hlkPk μ).Λ.g ≤ hlGt (1 + μ) := (hlkPk_inv μ hμ).2.1

theorem hlkPk_gmono {μ' μ : Ordinal.{0}} (hμ : μ < Om1) (h : μ' < μ) : (hlkPk μ').Λ.g ≤ (hlkPk μ).Λ.g :=
  ((hlkPk_inv μ hμ).2.2 μ' h).1

theorem hlkPk_ext {μ' μ : Ordinal.{0}} (hμ : μ < Om1) (h : μ' < μ) : HlkExt (hlkPk μ') (hlkPk μ) :=
  ((hlkPk_inv μ hμ).2.2 μ' h).2

theorem hlkPk_coh {l : Ordinal.{0}} (hle : l < Om1) : HlkCoh l (fun μ _ => hlkPk μ) :=
  ⟨fun μ h => (hlkPk_inv μ (h.trans hle)).1, fun μ h => hlkPk_g (h.trans hle),
    fun _ _ _ h₂ h12 => ⟨hlkPk_gmono (h₂.trans hle) h12, hlkPk_ext (h₂.trans hle) h12⟩⟩

/-- **At a limit `λ < Γ₀` the package is the limit package of the coherent sequence.** -/
theorem hlkPk_lim_eq {l : Ordinal.{0}} (hl : IsSuccLimit l) (hle : l < Om1) :
    hlkPk l = hlkPkL (hlkSeqOf l hl hle (fun μ _ => hlkPk μ) (hlkPk_coh hle)) := by
  rw [hlkPk_limit hl]; unfold hlkLimF; rw [dif_pos ⟨hle, hlkPk_coh hle⟩]

theorem hlkPk_lim_Λ {l : Ordinal.{0}} (hl : IsSuccLimit l) (hle : l < Om1) :
    (hlkPk l).Λ = hlMLv (1 + l) le_self_add (hl_one_add hle) := by
  rw [hlkPk_lim_eq hl hle]; rfl

end Googology.Trans.PoR.InaccPsi.R2.Hl
