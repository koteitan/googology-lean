import Googology.Trans.PoR.InaccPsi.R2.HkPkL

/-!
# HkRec: ONE RECURSION OF PACKAGES OVER THE LEVELS `Ω₁·(1+μ)`, `μ < ε₀`

`hkPk μ` is defined by `Ordinal.limitRecOn`: at `0` the package `Hj.hjPk1` (level `Ω₁`), at `μ + 1` the next package
`HjPk.succ` (level `L + Ω₁`), at a limit `λ < ε₀` the limit package `Hk.hkPkL` of the coherent sequence of the
packages at `heFs λ k` (level datum `Hk.hkLv (1+λ)`), when the earlier packages are coherent (`HkCoh`; as
`Hj.HjVLCoh` does for the levels `L + ν`).  `hkPk_inv`: for every `μ < ε₀` the level of `hkPk μ` is `Ω₁·(1+μ)`,
read `x·(1+μ)`, and its step extends the step of every `hkPk μ'`, `μ' < μ`, at every pseudo-base (`HkExt`).

* `HkCoh`, `hkSeqOf`, `hkLimF`, `hkPk` (**THE PACKAGES OF ALL LEVELS `Ω₁·M`, `M < ε₀`**), `hkPk_zero`, `hkPk_succ`,
  `hkPk_limit`, `hkPk_inv` (**THE INVARIANT**), `hkPk_L`, `hkPk_l`, `hkPk_ext`, `hkPk_lim_eq`.

No new axiom.  New definitions: `HkCoh`, `hkSeqOf`, `hkLimF`, `hkPk`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hk

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

theorem hk_e0_E : InE (ε₀ : Ordinal.{0}) := omega0_opow_epsilon 0

theorem hk_one_add {l : Ordinal.{0}} (hl : l < ε₀) : 1 + l < ε₀ :=
  (inE_indec hk_e0_E).add_lt (one_lt_omega0.trans (omega0_lt_epsilon 0)) hl

theorem hk_om {l : Ordinal.{0}} (hl : l < ε₀) : l < Om (1 : Ordinal.{0}) := hl.trans_le gc_eps0_le_Om1

/-- **The condition at a limit**: the earlier packages have the levels `Ω₁·(1+μ)` (read `x·(1+μ)`) and later steps
extend earlier ones at every pseudo-base. -/
def HkCoh (l : Ordinal.{0}) (IH : ∀ μ, μ < l → HjPk) : Prop :=
  (∀ μ (h : μ < l), (IH μ h).Λ.L = Om1 * (1 + μ) ∧ ∀ x, (IH μ h).Λ.l x = x * (1 + μ)) ∧
    ∀ μ' μ (h' : μ' < l) (h : μ < l), μ' < μ → HkExt (IH μ' h') (IH μ h)

/-- **The coherent sequence at a limit `λ < ε₀`**: the packages at `heFs λ k`, below the level datum `Ω₁·(1+λ)`. -/
noncomputable def hkSeqOf (l : Ordinal.{0}) (hl : IsSuccLimit l) (hle : l < ε₀) (IH : ∀ μ, μ < l → HjPk)
    (H : HkCoh l IH) : HkSeq (hkLv (1 + l) le_self_add (hk_one_add hle)) where
  M := 1 + l
  K := fun k => IH (heFs l k) (heFs_lt hl (hk_om hle) k)
  Ms := fun k => 1 + heFs l k
  L_eq := rfl
  l_eq := fun _ => rfl
  KL := fun k => (H.1 _ _).1
  Kl := fun k x => (H.1 _ _).2 x
  lt := fun k => (add_lt_add_iff_left 1).2 (heFs_lt hl (hk_om hle) k)
  mono := fun k => (add_lt_add_iff_left 1).2 (heFs_mono hl (hk_om hle) k)
  cof := fun t ht => by
    rw [one_add_of_omega0_le (omega0_le_of_isSuccLimit hl)] at ht
    obtain ⟨k, hk⟩ := heFs_cof hl (hk_om hle) t ht
    exact ⟨k, hk.trans_le le_add_self⟩
  ext := fun k => H.2 _ _ _ _ (heFs_mono hl (hk_om hle) k)

open Classical in
/-- **The limit case**: the limit package of the coherent sequence (when `λ < ε₀` and the condition holds). -/
noncomputable def hkLimF (l : Ordinal.{0}) (hl : IsSuccLimit l) (IH : ∀ μ, μ < l → HjPk) : HjPk :=
  if h : l < ε₀ ∧ HkCoh l IH then hkPkL (hkSeqOf l hl h.1 IH h.2) else hjPk1

/-- **THE PACKAGES OF ALL LEVELS `Ω₁·(1+μ)`, BY ONE RECURSION ON `μ`.** -/
noncomputable def hkPk (μ : Ordinal.{0}) : HjPk :=
  Ordinal.limitRecOn (motive := fun _ => HjPk) μ hjPk1 (fun _ K => K.succ) hkLimF

theorem hkPk_zero : hkPk 0 = hjPk1 := by unfold hkPk; rw [Ordinal.limitRecOn_zero]

theorem hkPk_succ (μ : Ordinal.{0}) : hkPk (μ + 1) = (hkPk μ).succ := by
  unfold hkPk; rw [Ordinal.limitRecOn_add_one]

theorem hkPk_limit {l : Ordinal.{0}} (hl : IsSuccLimit l) : hkPk l = hkLimF l hl (fun μ _ => hkPk μ) := by
  unfold hkPk; rw [Ordinal.limitRecOn_limit _ _ _ _ hl]

theorem hk_mul_le {a b c : Ordinal.{0}} (h : b < c) : a * (1 + b) + a ≤ a * (1 + c) :=
  HkSeq.mul_le ((add_lt_add_iff_left 1).2 h)

theorem hk_B_mono {K' K : HjPk} {μ' μ : Ordinal.{0}} (hK' : K'.Λ.L = Om1 * (1 + μ'))
    (hK : K.Λ.L = Om1 * (1 + μ)) (h : μ' ≤ μ) (F : Ordinal.{0}) : hdNx (K'.Λ.L + 0) F ≤ hdNx (K.Λ.L + 0) F := by
  rw [hK', hK]
  exact hdNx_mono (add_le_add (mul_le_mul_left' (add_le_add le_rfl h) _) le_rfl) _

/-- **THE INVARIANT**: for every `μ < ε₀` the package `hkPk μ` has the level `Ω₁·(1+μ)` read `x·(1+μ)`, and its
step extends the step of every `hkPk μ'`, `μ' < μ`, at every pseudo-base. -/
theorem hkPk_inv : ∀ μ, μ < ε₀ → ((hkPk μ).Λ.L = Om1 * (1 + μ) ∧ ∀ x, (hkPk μ).Λ.l x = x * (1 + μ)) ∧
    ∀ μ', μ' < μ → HkExt (hkPk μ') (hkPk μ) := by
  intro μ
  induction μ using WellFoundedLT.induction with
  | ind μ IH =>
  intro hμ
  rcases zero_or_succ_or_isSuccLimit μ with h0 | ⟨ν, hν⟩ | hlim
  · subst h0
    rw [hkPk_zero]
    refine ⟨⟨by show Om1 = _; rw [add_zero, mul_one], fun x => by show x = _; rw [add_zero, mul_one]⟩,
      fun μ' h => absurd h (not_lt.2 zero_le)⟩
  · have hν' : μ = ν + 1 := by rw [← hν, succ_eq_add_one]
    subst hν'
    have hνε : ν < ε₀ := (lt_add_one ν).trans hμ
    obtain ⟨⟨hL, hl⟩, hext⟩ := IH ν (lt_add_one ν) hνε
    refine ⟨⟨?_, fun x => ?_⟩, fun μ' hμ' => ?_⟩
    · rw [hkPk_succ]; show (hkPk ν).Λ.L + Om1 = _; rw [hL, ← add_assoc, mul_add_one]
    · rw [hkPk_succ]; show (hkPk ν).Λ.l x + x = _; rw [hl, ← add_assoc, mul_add_one]
    · rw [hkPk_succ]
      intro hL' hl' Q U hU c x hc
      have hsh := hjw_shape_dn Q ((hkPk ν).h0 Q.dn U hU)
      show (hjwU Q.toW (hkPk ν).St0 (hkPk ν).h0 ((hkPk ν).St0 Q.dn U hU) hsh).R c x = _ ∧
        (hjwU Q.toW (hkPk ν).St0 (hkPk ν).h0 ((hkPk ν).St0 Q.dn U hU) hsh).g c = _
      rcases (Order.lt_add_one_iff.1 hμ').lt_or_eq with hlt | heq
      · obtain ⟨⟨hL1, hl1⟩, -⟩ := IH μ' (hlt.trans (lt_add_one ν)) (hlt.trans hνε)
        have hLa : (hkPk μ').Λ.L + Om1 ≤ (hkPk ν).Λ.L := by rw [hL1, hL]; exact hk_mul_le hlt
        have hla : ∀ x, InE x → x < Om1 → (hkPk μ').Λ.l x + x ≤ (hkPk ν).Λ.l x := fun x _ _ => by
          rw [hl1, hl]; exact hk_mul_le hlt
        have hc0 : c < ((hkPk ν).St0 Q.dn U hU).B := by
          rw [((hkPk ν).h0 Q.dn U hU).B]
          rw [((hkPk μ').h0 _ U hU).B] at hc
          exact hc.trans_le (hk_B_mono hL1 hL hlt.le _)
        obtain ⟨r1, g1⟩ := hext μ' hlt hLa hla Q.dn U hU c x hc
        exact ⟨(hjwU_R0 Q.toW (hkPk ν).St0 (hkPk ν).h0 _ hsh hc0 x).trans r1,
          (hjwU_g0 Q.toW (hkPk ν).St0 (hkPk ν).h0 _ hsh hc0).trans g1⟩
      · subst heq
        exact ⟨hjwU_R0 Q.toW (hkPk μ').St0 (hkPk μ').h0 _ hsh hc x,
          hjwU_g0 Q.toW (hkPk μ').St0 (hkPk μ').h0 _ hsh hc⟩
  · have hcoh : HkCoh μ (fun μ' _ => hkPk μ') :=
      ⟨fun μ' h => (IH μ' h (h.trans hμ)).1, fun μ₁ μ₂ h₁ h₂ h12 =>
        (IH μ₂ h₂ (h₂.trans hμ)).2 μ₁ h12⟩
    have e : hkPk μ = hkPkL (hkSeqOf μ hlim hμ (fun μ' _ => hkPk μ') hcoh) := by
      rw [hkPk_limit hlim]; unfold hkLimF; rw [dif_pos ⟨hμ, hcoh⟩]
    refine ⟨⟨by rw [e]; rfl, fun x => by rw [e]; rfl⟩, fun μ' hμ' => ?_⟩
    rw [e]
    intro hL' hl' Q U hU c x hc
    let H := hkSeqOf μ hlim hμ (fun μ' _ => hkPk μ') hcoh
    obtain ⟨k, hk⟩ := heFs_cof hlim (hk_om hμ) μ' hμ'
    have hkl := heFs_lt hlim (hk_om hμ) k
    obtain ⟨⟨hLk, hlk⟩, hextk⟩ := IH _ hkl (hkl.trans hμ)
    obtain ⟨⟨hL1, hl1⟩, -⟩ := IH μ' hμ' (hμ'.trans hμ)
    have hLa : (hkPk μ').Λ.L + Om1 ≤ (hkPk (heFs μ k)).Λ.L := by rw [hL1, hLk]; exact hk_mul_le hk
    have hla : ∀ x, InE x → x < Om1 → (hkPk μ').Λ.l x + x ≤ (hkPk (heFs μ k)).Λ.l x := fun x _ _ => by
      rw [hl1, hlk]; exact hk_mul_le hk
    have hc' : c < (H.D Q U hU k).B := by
      rw [(H.D_spec Q U hU k).B]
      rw [((hkPk μ').h0 _ U hU).B] at hc
      exact hc.trans_le (hk_B_mono hL1 hLk hk.le _)
    obtain ⟨r1, g1⟩ := hkStL_ext H Q U hU k hc' x
    obtain ⟨r2, g2⟩ := hextk μ' hk hLa hla (Q.lowr (H.K k).Λ (H.hL k) (H.hl k)) U hU c x hc
    exact ⟨r1.trans r2, g1.trans g2⟩

theorem hkPk_L {μ : Ordinal.{0}} (hμ : μ < ε₀) : (hkPk μ).Λ.L = Om1 * (1 + μ) := (hkPk_inv μ hμ).1.1

theorem hkPk_l {μ : Ordinal.{0}} (hμ : μ < ε₀) (x : Ordinal.{0}) : (hkPk μ).Λ.l x = x * (1 + μ) :=
  (hkPk_inv μ hμ).1.2 x

theorem hkPk_ext {μ' μ : Ordinal.{0}} (hμ : μ < ε₀) (h : μ' < μ) : HkExt (hkPk μ') (hkPk μ) :=
  (hkPk_inv μ hμ).2 μ' h

theorem hkPk_coh {l : Ordinal.{0}} (hle : l < ε₀) : HkCoh l (fun μ _ => hkPk μ) :=
  ⟨fun μ h => (hkPk_inv μ (h.trans hle)).1, fun _ _ _ h₂ h12 => hkPk_ext (h₂.trans hle) h12⟩

/-- **At a limit `λ < ε₀` the package is the limit package of the coherent sequence.** -/
theorem hkPk_lim_eq {l : Ordinal.{0}} (hl : IsSuccLimit l) (hle : l < ε₀) :
    hkPk l = hkPkL (hkSeqOf l hl hle (fun μ _ => hkPk μ) (hkPk_coh hle)) := by
  rw [hkPk_limit hl]; unfold hkLimF; rw [dif_pos ⟨hle, hkPk_coh hle⟩]

theorem hkPk_lim_Λ {l : Ordinal.{0}} (hl : IsSuccLimit l) (hle : l < ε₀) :
    (hkPk l).Λ = hkLv (1 + l) le_self_add (hk_one_add hle) := by
  rw [hkPk_lim_eq hl hle]; rfl

end Googology.Trans.PoR.InaccPsi.R2.Hk
