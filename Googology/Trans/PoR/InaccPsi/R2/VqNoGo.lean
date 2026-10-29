import Googology.Trans.PoR.InaccPsi.R2.VqY3

/-!
# No top with a fixed image at the shift `Ω₃` over the base `0`, for any image

`Θ = gxTh ρ_λ (ldAtR λ)`, `Y₃ = ψ_{Ω₃}(Ω₃)`, `Y₂ = ψ_{Ω₂}(Ω₂)`.

* `vqLt_Om3` (`Θ(ψ₂(Ω₃ + Y₃)) < Θ(ψ₂(Ω₃ + Ω₃))`);
* `vqNoTop_Om3` (**`¬ RvTop λ 0 Ω₃ X̂ 0` for EVERY `X̂`**, although `(Ω₃, Ω₂)` is a `Vq.VqSh` and a `Vk.VkSh` at the
  base `0`): at the base `0` the top asks `Ω^{X̂} = Y₂` (`Vn.vnTop_false` excludes `Ω^{X̂} > Y₂`), at the base `Ω₃`
  it asks `Θ(ψ₂(Ω₃·2)) = ψ₁(A + 1 + Y₂ + Ω^{X̂}) ≤ ψ₁(A + 1 + Y₂ + Y₂) = Θ(ψ₂(Ω₃ + Y₃))` (`Vq.vqRead_Om3Y3`), which
  is too small.  So the image of the level `Ω₃` depends on the base: a top law `Rv.RvTop` with one image for all
  bases `β ≥ 0` cannot hold at `Ω₃`.

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Vq

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Ro Googology.Trans.PoR.InaccPsi.R2.Rv
  Googology.Trans.PoR.InaccPsi.R2.Ug Googology.Trans.PoR.InaccPsi.R2.Uj Googology.Trans.PoR.InaccPsi.R2.Vk
  Googology.Trans.PoR.InaccPsi.R2.Vn

variable {S : InaccSeq.{0}}

theorem vqOm3_lt_A (l : Ordinal.{0}) {x : Ordinal.{0}} (hx : x < Om ω) : x < ConjT.Aη S (cdEta S l) :=
  hx.trans_le (ConjT.OmW_le_A S _)

theorem vqOm3_add_lt {x : Ordinal.{0}} (hx : x < Om (1 + 1 + 1)) : Om (1 + 1 + 1) + x < Om ω :=
  vkOmW.1.isPrincipal Ry.ryOm3_lt (hx.trans Ry.ryOm3_lt)

/-- `Θ(ψ₂(Ω₃ + Y₃)) < Θ(ψ₂(Ω₃ + Ω₃))`. -/
theorem vqLt_Om3 (l : Ordinal.{0}) :
    gxTh (upsilon l) (ldAtR S l) (S.psi (Om (1 + 1 + 1) + ugY S) (Om (1 + 1))) <
      gxTh (upsilon l) (ldAtR S l) (S.psi (Om (1 + 1 + 1) + Om (1 + 1 + 1)) (Om (1 + 1))) := by
  have h3 : (1 + 1 + 1 : Ordinal.{0}) ≠ 0 := (add_pos_of_right zero_lt_one _).ne'
  have hlt : Om (1 + 1 + 1) + ugY S < Om (1 + 1 + 1) + Om (1 + 1 + 1) :=
    (add_lt_add_iff_left _).2 ugY_lt_Om3
  have hat : S.psi (Om (1 + 1 + 1) + ugY S) (Om (1 + 1)) ∈ ldAtR S l :=
    ⟨_, CSet.add_mem (Ry.ryOm3_mem _ _) (vqY3_mem (Ry.ryOm3_lt.trans_le (ConjT.OmW_le_A S _))),
      vqOm3_lt_A l (vqOm3_add_lt ugY_lt_Om3), rfl⟩
  refine gxTh_lt (GxCl.atom hat) (psi_lt_psi_of_mem (InR_Om_succ 1) hlt ?_)
  refine CSet.add_mem (Ry.ryOm3_mem _ _) (vqY3_mem ?_)
  exact lt_add_of_pos_right _ (Om_pos h3)

/-- **`Ω₃` is a base of the shift `Ω₃`** (exponent `0`). -/
theorem vqBase_Om3Om3 (l : Ordinal.{0}) : RoBaseE S l (Om (1 + 1 + 1)) 0 (Om (1 + 1 + 1)) := by
  unfold RoBaseE
  rw [add_zero, vnWe_Om3]
  refine ⟨dvd_rfl, Ry.ryOm3_mem _ _, vqOm3_lt_A l (vkOmW.1.isPrincipal Ry.ryOm3_lt Ry.ryOm3_lt),
    fun _ _ => Ry.ryOm3_mem _ _, fun e' _ he' => ?_⟩
  rw [nonpos_iff_eq_zero.1 he']
  exact (Om_pos one_ne_zero).trans (psiS_bounds (S := S) _ 1).1

/-- **No top with a fixed image at the shift `Ω₃` over the base `0`**: `¬ RvTop λ 0 Ω₃ X̂ 0` for every `X̂`. -/
theorem vqNoTop_Om3 {l ηx A : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
    (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l) (Xh : Ordinal.{0}) :
    ¬ RvTop S l 0 (Om (1 + 1 + 1)) Xh 0 := by
  intro hT
  rcases lt_or_ge (S.psi (Om (1 + 1)) (Om (1 + 1))) (leOe Xh) with hgt | hle
  · exact vnTop_false hl hX hA hρ (by rw [vnWe_Om3]; exact ugY_lt_Om3.le) vnWe_Om3.le hgt hT
  have hκ1 : S.InR (Om 1) := Low.InR_Om_one
  have hAω := vnA_ge hl hX hA hρ
  have hle1 : A ≤ A + 1 + S.psi (Om (1 + 1)) (Om (1 + 1)) := le_self_add.trans le_self_add
  have hΩ2 : Om (1 + 1) < A + 1 + S.psi (Om (1 + 1)) (Om (1 + 1)) := (vkOmW.2.trans_le hAω).trans_le hle1
  have hÂ : A + 1 + S.psi (Om (1 + 1)) (Om (1 + 1)) ∈ S.CSet (A + 1 + S.psi (Om (1 + 1)) (Om (1 + 1)))
      (S.psi (A + 1 + S.psi (Om (1 + 1)) (Om (1 + 1))) (Om 1)) :=
    CSet.add_mem (CSet.add_mem ((psi_mono (S := S) hκ1 hle1).2 hA) (CSet.one_mem _ _)) (vqY2_mem hΩ2)
  have hbase := vnRead_W hl hX hA hρ (X := Om (1 + 1 + 1)) (by rw [vnWe_Om3]; exact ugY_lt_Om3.le)
    vnWe_Om3.le
  rw [vnWe_Om3] at hbase
  have h := hT _ _ (vqBase_Om3Om3 l) zero_le hÂ hbase
  rw [add_zero, gxTh_zero, add_zero] at h
  unfold leTe at h
  rw [vnWe_Om3] at h
  have h2 := vqLt_Om3 (S := S) l
  rw [h, vqRead_Om3Y3 hl hX hA hρ] at h2
  exact absurd h2 (not_lt.2 (psi_mono (S := S) hκ1 ((add_le_add_iff_left _).2 hle)).1)

end Googology.Trans.PoR.InaccPsi.R2.Vq
