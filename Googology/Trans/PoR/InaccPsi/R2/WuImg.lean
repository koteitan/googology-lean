import Googology.Trans.PoR.InaccPsi.R2.VrForm

/-!
# REFUTE-FIRST test: is the image of a decomposition a function of its value? (the value of `Wq.wqImgF_ref`)

`a = υ_λ`, `u₁ = υ_{λ+1}`, `τ = υ_{λ+h}`.  The value `τ + u₁` of the decomposition `E₁ = ub h base + ub 1 base` of
`Wq.wqImgF_ref` (there `h = z+ω+1`, `z = ω^{u₁}`) has the other decompositions `E₂ = ub h (base + u₁)` (the leaf
`u₁ = υ_{λ+1}`) and `E₃ = ub h base + tm 1 base` (a `Un`-term).  For EVERY offset map `f` the three images agree:
`υ_{μ+f(h)} + υ_{μ+f(1)}`.  So the failure in `Wq.wqImgF_ref` comes from the map `f` (`f z = ω²` too small for the
code `u₁` moved to `υ_{μ+f(1)}`), not from a choice between decompositions.  (In general, two decompositions whose
points lie in a realizer configuration have one image: `Vr.vrImg_agree`.)

* `wuImg_test` (**the three decompositions have one value and, for every `f`, one image**).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Wu

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Ub Googology.Trans.PoR.InaccPsi.R2.Un Googology.Trans.PoR.InaccPsi.R2.Vi

/-- The leaf `u₁ = υ_{λ+1}` is moved to `υ_{μ+f(1)}`. -/
theorem wuLf_u1 (l μ : Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}) :
    Vr.vrLf l μ f (upsilon (l + 1)) = upsilon (μ + f 1) := by
  unfold Vr.vrLf
  rw [if_neg (by rw [Order.succ_eq_add_one]; exact lt_irrefl _), Lr.lrIx_up, Ordinal.add_sub_cancel]

/-- **The image test on the value of `Wq.wqImgF_ref`**: `E₁ = ub h base + ub 1 base`, `E₂ = ub h (base + u₁)`,
`E₃ = ub h base + tm 1 base` have the value `τ + u₁` and, for every `f`, the image `υ_{μ+f(h)} + υ_{μ+f(1)}`. -/
theorem wuImg_test (l μ h δ : Ordinal.{0}) (Lf : Finset Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}) :
    let E₁ : Vr.VrE := .add (.ub h .base) (.ub 1 .base)
    let E₂ : Vr.VrE := .ub h (.add .base (.par (upsilon (l + 1))))
    let E₃ : Vr.VrE := .add (.ub h .base) (.tm 1 .base Lf δ)
    (Vr.vrVal l E₁ = upsilon (l + h) + upsilon (l + 1) ∧ Vr.vrVal l E₂ = upsilon (l + h) + upsilon (l + 1) ∧
      Vr.vrVal l E₃ = upsilon (l + h) + upsilon (l + 1)) ∧
    (Vr.vrImg l μ f E₁ = upsilon (μ + f h) + upsilon (μ + f 1) ∧
      Vr.vrImg l μ f E₂ = upsilon (μ + f h) + upsilon (μ + f 1) ∧
      Vr.vrImg l μ f E₃ = upsilon (μ + f h) + upsilon (μ + f 1)) := by
  refine ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, ?_, rfl⟩⟩
  show UbT.ev (upsilon (μ + f h)) (UbT.map (Vr.vrLf l μ f) (.add .base (.par (upsilon (l + 1))))) = _
  simp only [UbT.map, UbT.ev, wuLf_u1]

end Googology.Trans.PoR.InaccPsi.R2.Wu
