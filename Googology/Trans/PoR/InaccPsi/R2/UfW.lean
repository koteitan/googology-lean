import Googology.Trans.PoR.InaccPsi.R2.UcBH
import Googology.Trans.PoR.InaccPsi.R2.LeEMove

/-!
# `B_n` on the levels `γ < ε_{Ω₂+1}`: `B_n γ = ucMap B_n γ`, `B_n(Ω₂^γ) = Ω₂^{B_n γ}`

`B_n = Bc.bcB S n`, `MvD` its domain, `Ω₂ = OmTwo`, `E₂ = Uc.ucE = ε_{Ω₂+1}`, `ucComps γ` the hereditary base-`Ω₂`
components of `γ`, `ucMap f γ` the level rebuilt from the images of its components (`R2.UcCmp`).  For a class `Q` of
ordinals below `Ω₂` in the domain of `B_n`, closed under `log_ω` and the tail:

* `ufB_E` (**`B_n E₂ = E₂`**);
* `ufB_lev` (**for `γ < E₂` with every component in `Q`: `γ`, `Ω₂·γ`, `Ω₂^γ` are in the domain,
  `B_n γ = ucMap B_n γ`, `B_n(Ω₂·γ) = Ω₂·B_n γ`, `B_n(Ω₂^γ) = Ω₂^{B_n γ}`, `B_n γ < E₂`, the components of `B_n γ`
  are the images of those of `γ`, and `ucFold g (B_n γ) = ucFold (g ∘ B_n) γ`**);
* `ufB_mulW` (**`B_n(Ω₂^γ·D) = Ω₂^{B_n γ}·B_n D`** for `D ∈ Q`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Uf

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Mv

variable {S : InaccSeq.{0}}

theorem uf_Om2 : (OmTwo : Ordinal.{0}) = Om (1 + 1) := uc_Om2_eq

theorem ufB_Om2 {n : ℕ} : MvD S OmTwo ∧ Bc.bcB S n OmTwo = OmTwo := by
  rw [uf_Om2]; exact Ld.ldOm2_D

theorem ufD_zero : MvD S (0 : Ordinal.{0}) := mvD_of_lt (lt_of_le_of_lt zero_le (Ri.ri_one_lt_L S))

/-- **`B_n E₂ = E₂`.** -/
theorem ufB_E {n : ℕ} : MvD S ucE ∧ Bc.bcB S n ucE = ucE := by
  obtain ⟨hD2, hB2⟩ := ufB_Om2 (S := S) (n := n)
  obtain ⟨hDs, hBs⟩ := mvB_add (k := n) hD2 (Rk.rk_one_D (S := S))
  rw [hB2, Mw.mwB_one] at hBs
  have h1 : (1 : Ordinal.{0}) < veblen 1 (OmTwo + 1) := by
    rw [← uc_E_eq_veblen]; exact uc_one_lt_Om2.trans ucE_gt
  have h2 : OmTwo + 1 < veblen 1 (OmTwo + 1) := by
    rw [← uc_E_eq_veblen]; exact uc_E_indec ucE_gt (uc_one_lt_Om2.trans ucE_gt)
  obtain ⟨hD, hB⟩ := Mw.mwB_phi (k := n) (Rk.rk_one_D (S := S)) hDs h1 h2
  rw [Mw.mwB_one, hBs, ← uc_E_eq_veblen] at hB
  rw [← uc_E_eq_veblen] at hD
  exact ⟨hD, hB⟩

theorem ufB_lt_iff {n : ℕ} {x y : Ordinal.{0}} (hx : MvD S x) (hy : MvD S y) :
    Bc.bcB S n x < Bc.bcB S n y ↔ x < y := mvB_lt_iff hx hy

/-- `Ω₂·Ω₂^e·d = ω^{Ω₂ + Ω₂·e}·d`. -/
theorem uf_Om2_mul_W (e d : Ordinal.{0}) : OmTwo * (OmTwo ^ e * d) = ω ^ (OmTwo + OmTwo * e) * d := by
  rw [← mul_assoc, uc_W_eq, opow_add, uc_Om2_opow_self]

/-- **`B_n` on the levels**: for `γ < E₂` with every component in `Q` (`Q ⊆ MvD`, closed under `log_ω` and the
tail, `Q ⊆ Ω₂`): `γ`, `Ω₂·γ`, `Ω₂^γ` are in the domain, `B_n γ = ucMap B_n γ`, `B_n(Ω₂·γ) = Ω₂·B_n γ`,
`B_n(Ω₂^γ) = Ω₂^{B_n γ}`, `B_n γ < E₂`, `ucComps (B_n γ) = B_n '' ucComps γ`,
`ucFold g (B_n γ) = ucFold (g ∘ B_n) γ`. -/
theorem ufB_lev {n : ℕ} (Q : Ordinal.{0} → Prop) (hQD : ∀ x, Q x → MvD S x)
    (hQdec : ∀ x, Q x → x ≠ 0 → Q (log ω x) ∧ Q (x - ω ^ log ω x)) (hQW : ∀ x, Q x → x < OmTwo) :
    ∀ γ, γ < ucE → (∀ c ∈ ucComps γ, Q c) →
      MvD S γ ∧ Bc.bcB S n γ = ucMap (Bc.bcB S n) γ ∧
      MvD S (OmTwo * γ) ∧ Bc.bcB S n (OmTwo * γ) = OmTwo * Bc.bcB S n γ ∧
      MvD S (OmTwo ^ γ) ∧ Bc.bcB S n (OmTwo ^ γ) = OmTwo ^ Bc.bcB S n γ ∧
      Bc.bcB S n γ < ucE ∧ ucComps (Bc.bcB S n γ) = Bc.bcB S n '' ucComps γ ∧
      ∀ g : Ordinal.{0} → Ordinal.{0}, ucFold g (Bc.bcB S n γ) = ucFold (fun x => g (Bc.bcB S n x)) γ := by
  obtain ⟨hD2, hB2⟩ := ufB_Om2 (S := S) (n := n)
  obtain ⟨hDE, hBE⟩ := ufB_E (S := S) (n := n)
  have hS2 : SC (Om (1 + 1) : Ordinal.{0}) := Ld.ldOm2_SC
  have hQK : ∀ x, Q x → x < Om (1 + 1) := fun x hx => by rw [← uf_Om2]; exact hQW x hx
  obtain ⟨hD2', hB2'⟩ := Ld.ldOm2_D (S := S) (k := n)
  have hmulK := Ld.ldB_mulK (n := n) hS2 hD2' hB2' Q hQD hQdec hQK
  intro γ
  induction γ using WellFoundedLT.induction with
  | ind γ IH =>
  intro hγE hQγ
  have hBlt : ∀ {x : Ordinal.{0}}, MvD S x → x < ucE → Bc.bcB S n x < ucE := fun hx h => by
    have := (mvB_lt_iff (k := n) hx hDE).2 h; rwa [hBE] at this
  by_cases h1 : γ < OmTwo
  · have hQ : Q γ := hQγ γ (by rw [ucComps_small h1]; rfl)
    have hD := hQD γ hQ
    obtain ⟨hDm, hBm⟩ := hmulK γ hQ
    rw [← uf_Om2] at hDm hBm
    obtain ⟨hDp, hBp⟩ := Ld.ldB_opow (n := n) hDm
    have hBγ2 : Bc.bcB S n γ < OmTwo := by
      have := (mvB_lt_iff (k := n) hD hD2).2 h1; rwa [hB2] at this
    refine ⟨hD, by rw [ucMap_small _ h1], hDm, hBm, by rw [uc_W_eq]; exact hDp,
      by rw [uc_W_eq, hBp, hBm, ← uc_W_eq], hBlt hD hγE, ?_, fun g => ?_⟩
    · rw [ucComps_small hBγ2, ucComps_small h1, Set.image_singleton]
    · rw [ucFold_small _ hBγ2, ucFold_small _ h1]
  have hγ2 : OmTwo ≤ γ := not_lt.1 h1
  set e := log OmTwo γ with he
  set d := γ / OmTwo ^ e with hd
  set r := γ % OmTwo ^ e with hr
  have hel : e < γ := uc_log_lt hγ2 hγE
  have hrl : r < γ := uc_mod_lt hγ2
  have hcomps := ucComps_big hγ2 hγE
  have hQe : ∀ c ∈ ucComps e, Q c := fun c hc => hQγ c (by rw [hcomps]; exact Or.inl hc)
  have hQd : Q d := hQγ d (by rw [hcomps]; exact Or.inr (Or.inl rfl))
  have hQr : ∀ c ∈ ucComps r, Q c := fun c hc => hQγ c (by rw [hcomps]; exact Or.inr (Or.inr hc))
  obtain ⟨hDe, hBe, hDme, hBme, hDpe, hBpe, hBeE, -, -⟩ := IH e hel (hel.trans hγE) hQe
  obtain ⟨hDr, hBr, hDmr, hBmr, -, -, -, hCr, hFr⟩ := IH r hrl (hrl.trans hγE) hQr
  have hDd := hQD d hQd
  have hd2 : d < OmTwo := uc_div_lt γ
  have hd0 : 0 < d := uc_div_pos hγ2
  have hrW : r < OmTwo ^ e := Ordinal.mod_lt _ (uc_W_pos e).ne'
  have he1 : 1 ≤ e := by
    by_contra h0
    rw [not_le, Order.lt_one_iff] at h0
    have : γ < OmTwo := by
      calc γ < OmTwo ^ (log OmTwo γ + 1) := lt_opow_succ_log_self uc_one_lt_Om2 γ
        _ = OmTwo := by rw [← he, h0, zero_add, opow_one]
    exact h1 this
  have hdec : OmTwo ^ e * d + r = γ := uc_cnf_eq γ
  -- `Ω₂^e·d = ω^{Ω₂·e}·d`
  have hK1 : ∀ x, Q x → x < OmTwo * e := fun x hx =>
    (hQW x hx).trans_le (le_mul_left _ (zero_lt_one.trans_le he1))
  obtain ⟨hDt, hBt⟩ := Le.leB_mulOp2 (n := n) hDme Q hQD hQdec hK1 d hQd
  rw [← uc_W_eq, hBme, ← uc_W_eq] at hBt
  rw [← uc_W_eq] at hDt
  obtain ⟨hDγ, hBγ⟩ := mvB_add (k := n) hDt hDr
  rw [hdec] at hDγ hBγ
  rw [hBt] at hBγ
  -- `Ω₂·γ = ω^{Ω₂ + Ω₂·e}·d + Ω₂·r`
  obtain ⟨hDK, hBK⟩ := mvB_add (k := n) hD2 hDme
  rw [hB2, hBme] at hBK
  have hK2 : ∀ x, Q x → x < OmTwo + OmTwo * e := fun x hx => (hQW x hx).trans_le le_self_add
  obtain ⟨hDt2, hBt2⟩ := Le.leB_mulOp2 (n := n) hDK Q hQD hQdec hK2 d hQd
  rw [hBK] at hBt2
  rw [← uf_Om2_mul_W] at hDt2 hBt2
  rw [← uf_Om2_mul_W] at hBt2
  obtain ⟨hDmγ, hBmγ⟩ := mvB_add (k := n) hDt2 hDmr
  have hmγ : OmTwo * (OmTwo ^ e * d) + OmTwo * r = OmTwo * γ := by rw [← mul_add, hdec]
  rw [hmγ] at hDmγ hBmγ
  rw [hBt2, hBmr, ← mul_add, ← hBt] at hBmγ
  -- the image is again in normal form
  have hBe1 : 1 ≤ Bc.bcB S n e := by
    rcases he1.lt_or_eq with hlt | heq
    · rw [← Mw.mwB_one (S := S) n]; exact ((mvB_lt_iff Rk.rk_one_D hDe).2 hlt).le
    · rw [← heq, Mw.mwB_one]
  have hBd0 : Bc.bcB S n d ≠ 0 := by
    have := (mvB_lt_iff (k := n) ufD_zero hDd).2 hd0
    rw [Bc.bcB_zero] at this; exact this.ne'
  have hBd2 : Bc.bcB S n d < OmTwo := by
    have := (mvB_lt_iff (k := n) hDd hD2).2 hd2; rwa [hB2] at this
  have hBrW : Bc.bcB S n r < OmTwo ^ Bc.bcB S n e := by
    have := (mvB_lt_iff (k := n) hDr hDpe).2 hrW; rwa [hBpe] at this
  have hBγE : Bc.bcB S n γ < ucE := hBlt hDγ hγE
  have hBγ' : Bc.bcB S n γ = OmTwo ^ Bc.bcB S n e * Bc.bcB S n d + Bc.bcB S n r := by rw [hBγ]
  have hBγE' : OmTwo ^ Bc.bcB S n e * Bc.bcB S n d + Bc.bcB S n r < ucE := by rw [← hBγ']; exact hBγE
  refine ⟨hDγ, ?_, hDmγ, by rw [hBmγ, hBt, ← hBγ], ?_, ?_, hBγE, ?_, fun g => ?_⟩
  · rw [hBγ', hBe, hBr, ← ucMap_big _ hγ2 hγE]
  · rw [uc_W_eq]; exact (Ld.ldB_opow (n := n) hDmγ).1
  · rw [uc_W_eq, (Ld.ldB_opow (n := n) hDmγ).2, hBmγ, hBt, ← hBγ, ← uc_W_eq]
  · rw [hBγ', ucComps_cnf hBe1 hBd0 hBd2 hBrW hBγE', hcomps, Set.image_union, Set.image_union,
      Set.image_singleton, hCr]
    have hCe := (IH e hel (hel.trans hγE) hQe).2.2.2.2.2.2.2.1
    rw [hCe]
  · rw [hBγ', ucFold_cnf g hBe1 hBd0 hBd2 hBrW hBγE', ucFold_big _ hγ2 hγE, hFr]
    have hFe := (IH e hel (hel.trans hγE) hQe).2.2.2.2.2.2.2.2 g
    rw [hFe]

/-- **`B_n(Ω₂^γ·D) = Ω₂^{B_n γ}·B_n D`** for `γ < E₂` with every component in `Q` and `D ∈ Q`. -/
theorem ufB_mulW {n : ℕ} (Q : Ordinal.{0} → Prop) (hQD : ∀ x, Q x → MvD S x)
    (hQdec : ∀ x, Q x → x ≠ 0 → Q (log ω x) ∧ Q (x - ω ^ log ω x)) (hQW : ∀ x, Q x → x < OmTwo)
    {γ D : Ordinal.{0}} (hγ : γ < ucE) (hQγ : ∀ c ∈ ucComps γ, Q c) (hD : Q D) :
    MvD S (OmTwo ^ γ * D) ∧ Bc.bcB S n (OmTwo ^ γ * D) = OmTwo ^ Bc.bcB S n γ * Bc.bcB S n D := by
  obtain ⟨hDγ, -, hDm, hBm, -, -, -, -, -⟩ := ufB_lev (n := n) Q hQD hQdec hQW γ hγ hQγ
  rcases eq_or_ne γ 0 with rfl | hγ0
  · rw [opow_zero, one_mul, Bc.bcB_zero, opow_zero, one_mul]; exact ⟨hQD D hD, rfl⟩
  have hK : ∀ x, Q x → x < OmTwo * γ := fun x hx =>
    (hQW x hx).trans_le (le_mul_left _ (pos_iff_ne_zero.2 hγ0))
  obtain ⟨h1, h2⟩ := Le.leB_mulOp2 (n := n) hDm Q hQD hQdec hK D hD
  rw [hBm, ← uc_W_eq, ← uc_W_eq] at h2
  rw [← uc_W_eq] at h1
  exact ⟨h1, h2⟩

end Googology.Trans.PoR.InaccPsi.R2.Uf
