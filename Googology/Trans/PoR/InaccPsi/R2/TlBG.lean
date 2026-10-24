import Googology.Trans.PoR.InaccPsi.R2.TlDat

/-!
# `B_Γ` as the first new atom: `B_Γ = F₁(Ω₁ + 1)` and its data

`Ω₁ = Om1`, `F_β = Rh.rhF β`, `B_Γ = Tf.tfBG`, `X = Tl.tlX`.

* `tl_rhF_Om1` (**`F_β(Ω₁) = Ω₁` for `β < Ω₁`**), `tl_BG_eq` (**`B_Γ = F₁(Ω₁ + 1)`**: the least fixed point of `Γ`
  above `Ω₁` is the first value of `F₁` above `Ω₁`), `tlLev_BG` (`tlLev B_Γ = 1`), `tlDat_BG` (**`tlDat B_Γ = 1`**: the
  leaves of the atom `F₁(Ω₁ + 1)` are those of `1` and `Ω₁ + 1`; the `InaccPsi` normal form `ψ_{Ω₂}(Ω₂)` of `B_Γ` has no
  countable leaf, `Ti.tiDat_BG`, so `tlDat` and `Ti.tiDat` differ there by a finite leaf, which neither the citation
  `R2.CitedTl` (finite ordinals are in every `Tᵗ` and below every `ϑᵗ`-value) nor `B_n` (it fixes `ℕ`) sees).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Tl

open Ordinal Order Set Cardinal Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rj Googology.Trans.PoR.InaccPsi.R2.Tf
  Googology.Trans.PoR.InaccPsi.R2.Rh

/-- **`F_β(Ω₁) = Ω₁` for `β < Ω₁`.** -/
theorem tl_rhF_Om1 {β : Ordinal.{0}} (hβ : β < Om1) : rhF β Om1 = Om1 := by
  have hlim : IsSuccLimit (Om1 : Ordinal.{0}) := by rw [rj_Om1]; exact InaccSeq.Om_isSuccLimit one_ne_zero
  refine le_antisymm (((rhF_normal β).le_iff_forall_le hlim).2 fun z hz => ?_) (rhF_le_self β _)
  have h := tl_rhF_lt tf_reg1 tf_unc1 β (by rw [← tf_Om1_ord]; exact hβ) z (by rw [← tf_Om1_ord]; exact hz)
  rw [← tf_Om1_ord] at h
  exact h.le

/-- **`B_Γ = F₁(Ω₁ + 1)`.** -/
theorem tl_BG_eq : tfBG = rhF 1 (Om1 + 1) := by
  have h1 : rhF 1 (Om1 : Ordinal.{0}) = Om1 := tl_rhF_Om1 tf_one_lt_Om1
  have hfix1 : gamma (rhF 1 (Om1 + 1)) = rhF 1 (Om1 + 1) := by
    rw [← rhF_zero]; exact rhF_fix_lower zero_lt_one _
  have hgt : Om1 < rhF 1 (Om1 + 1) := by
    conv_lhs => rw [← h1]
    exact (rhF_lt 1).2 (lt_add_one _)
  refine le_antisymm (tfBG_le hfix1 hgt) ?_
  have hfix : ∀ j < (1 : Ordinal.{0}), rhF j tfBG = tfBG := by
    intro j hj
    rw [Order.lt_one_iff] at hj
    rw [hj, rhF_zero]; exact tfBG_fix
  obtain ⟨e, he⟩ := rhF_range tfBG_SC hfix
  have he1 : Om1 < e := by
    have : rhF 1 Om1 < rhF 1 e := by rw [h1, he]; exact tfBG_gt
    exact (rhF_lt 1).1 this
  rw [← he]
  exact (rhF_le 1).2 (Order.add_one_le_of_lt he1)

/-- `Ω₁ + 1 < B_Γ`. -/
theorem tl_Om1_succ_lt_BG : (Om1 : Ordinal.{0}) + 1 < tfBG := SC.add_one_lt tfBG_SC tfBG_gt

/-- `tlLev B_Γ = 1`. -/
theorem tlLev_BG : tlLev tfBG = 1 := by
  rw [tl_BG_eq]; refine tlLev_F ?_
  rw [← tl_BG_eq]; exact tl_Om1_succ_lt_BG

/-- **`tlDat B_Γ = 1`.** -/
theorem tlDat_BG : tlDat tfBG = 1 := by
  have hlt : (Om1 : Ordinal.{0}) + 1 < rhF 1 (Om1 + 1) := by rw [← tl_BG_eq]; exact tl_Om1_succ_lt_BG
  have h1 : (Om1 : Ordinal.{0}) < rhF 1 (Om1 + 1) := (lt_add_one _).trans hlt
  have hX : rhF 1 (Om1 + 1) < tlX := by rw [← tl_BG_eq]; exact tl_BG_lt_X
  rw [tl_BG_eq, tlDat_F one_ne_zero h1 hX hlt, tlDat_small tf_one_lt_Om1,
    tlDat_eq_tf _ tl_Om1_succ_lt_BG, tfDat_Om1_succ, max_self]

end Googology.Trans.PoR.InaccPsi.R2.Tl
