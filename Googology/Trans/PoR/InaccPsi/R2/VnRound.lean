import Googology.Trans.PoR.InaccPsi.R2.VnLim

/-!
# The members of the pointwise limit rule exist at every visible exponent (base-relative)

`W^X = Ω₂^X`, `T_X(β) = ψ_{Ω₂}(β + W^X)`; `x' = Ω₂·(x / Ω₂)` (the exponent `x` rounded down to a multiple of `Ω₂`).

* `vnRound` (**UNCONDITIONAL beyond the hypotheses on `x`**: for every exponent `x < X` of the hull with
  `x ∈ Cl(β + W^{x+1}, T_{x+1}(β))` and `Ω₂ ∣ X`, the shift `X' = x' + Ω₂` has `x < X' ≤ X`, `Ω₂ ∣ X'`, `X' ≠ 0`,
  `X' ∈ H_λ` and `X' ∈ Cl(β + W^{X'}, T_{X'}(β))`: the membership part of every member that `Vn.vnTopPt` asks);
* `vnRound_lt` (`X' < X` unless `X = x' + Ω₂`).

Together with `Vn.vnNoSh`: at the exponents `x ∈ [Y_{k+3}, Ω_{k+3})` (visible at bases `β ≥ Ω_{k+3}`) no
`Vk.VkSh` member exists, while the base-relative member `x' + Ω₂` always does.

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Vn

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Ro Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Ta

variable {S : InaccSeq.{0}}

/-- **The rounded member `X' = Ω₂·(x / Ω₂) + Ω₂`** of a visible exponent `x < X`. -/
theorem vnRound {l β x X : Ordinal.{0}} (hxH : x ∈ cdHull S l)
    (hxC : x ∈ S.CSet (β + leWe (x + 1)) (S.psi (β + leWe (x + 1)) (Om (1 + 1)))) (hxX : x < X)
    (hd : Om (1 + 1) ∣ X) :
    x < Om (1 + 1) * (x / Om (1 + 1)) + Om (1 + 1) ∧ Om (1 + 1) * (x / Om (1 + 1)) + Om (1 + 1) ≤ X ∧
      Om (1 + 1) ∣ Om (1 + 1) * (x / Om (1 + 1)) + Om (1 + 1) ∧
      Om (1 + 1) * (x / Om (1 + 1)) + Om (1 + 1) ≠ 0 ∧
      Om (1 + 1) * (x / Om (1 + 1)) + Om (1 + 1) ∈ cdHull S l ∧
      Om (1 + 1) * (x / Om (1 + 1)) + Om (1 + 1) ∈
        S.CSet (β + leWe (Om (1 + 1) * (x / Om (1 + 1)) + Om (1 + 1)))
          (S.psi (β + leWe (Om (1 + 1) * (x / Om (1 + 1)) + Om (1 + 1))) (Om (1 + 1))) := by
  set W := Om (1 + 1 : Ordinal.{0}) with hW_def
  have hW0 : W ≠ 0 := ldOm2_SC.1.ne'
  have hlt : x < W * (x / W) + W := by
    calc x = W * (x / W) + x % W := (Ordinal.div_add_mod x W).symm
      _ < W * (x / W) + W := (add_lt_add_iff_left _).2 (Ordinal.mod_lt x hW0)
  have hle : W * (x / W) + W ≤ X := by
    obtain ⟨q, rfl⟩ := hd
    have hq : x / W < q := (Ordinal.lt_mul_iff_div_lt hW0).1 hxX
    rw [← mul_add_one]
    exact mul_le_mul_right (Order.add_one_le_of_lt hq) _
  have hmemC : ∀ {a b : Ordinal.{0}}, x ∈ S.CSet a b → W * (x / W) + W ∈ S.CSet a b := fun h =>
    CSet.add_mem (rqMulK_mem ldOm2_SC (mxOm2_mem _ _) (ldDivK_mem ldOm2_SC h)) (mxOm2_mem _ _)
  have hx1 : β + leWe (x + 1) ≤ β + leWe (W * (x / W) + W) :=
    (add_le_add_iff_left β).2 (leWe_mono (Order.add_one_le_of_lt hlt))
  refine ⟨hlt, hle, dvd_add (dvd_mul_right _ _) dvd_rfl, ?_, hmemC hxH,
    (psi_mono (S := S) (InR_Om_succ 1) hx1).2 (hmemC hxC)⟩
  exact (lt_of_lt_of_le (ldOm2_SC.1) le_add_self).ne'

/-- **`X' < X` unless `X = x' + Ω₂`.** -/
theorem vnRound_lt {x X : Ordinal.{0}} (hxX : x < X) (hd : Om (1 + 1) ∣ X)
    (hne : X ≠ Om (1 + 1) * (x / Om (1 + 1)) + Om (1 + 1)) :
    Om (1 + 1) * (x / Om (1 + 1)) + Om (1 + 1) < X := by
  set W := Om (1 + 1 : Ordinal.{0}) with hW_def
  have hW0 : W ≠ 0 := ldOm2_SC.1.ne'
  have hle : W * (x / W) + W ≤ X := by
    obtain ⟨q, rfl⟩ := hd
    have hq : x / W < q := (Ordinal.lt_mul_iff_div_lt hW0).1 hxX
    rw [← mul_add_one]
    exact mul_le_mul_right (Order.add_one_le_of_lt hq) _
  exact lt_of_le_of_ne hle (Ne.symm hne)

end Googology.Trans.PoR.InaccPsi.R2.Vn
