import Googology.Trans.PoR.InaccPsi.R2.VxPlat
import Googology.Trans.PoR.InaccPsi.R2.VtDynTop
import Googology.Trans.PoR.InaccPsi.R2.VbReach

/-!
# The image of the shift `Ω_{k+3}` read from the base: exact at the base `0`, and never constant

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `Y_{k+2} = ψ_{Ω_{k+2}}(Ω_{k+2}) = Uj.ujY S k`,
`T = Vb.vbT S λ`; a restart `λ` (`IsRestartIdx λ`, `ρ_λ < P(η_x)`) with `ψ_{Ω₁}(A) = ρ_λ`, `A ∈ Cl(A, ψ_{Ω₁}(A))`.
The moved shift at the base `β` is `Y(β) = ψ_{Ω_{k+3}}(β + Ω_{k+3})` (`Vx.vxTe_OmK`).

* `vxImg0K` (**given `Θ(ψ₂(Y_{k+3})) = ψ₁(A + 1 + Y_{k+2})`: `Θ(T_{Ω_{k+3}}(0)) = ψ₁(A + 1 + Ω^{Y_{k+2}})`**, the image
  read from the base `0` is `Y_{k+2}`), `vxImg0` (**`k = 0`, UNCONDITIONAL beyond the restart: image `Y₂ = T(Y(0))`**,
  `vbT S λ Y₃ = Y₂`);
* `vxDyn_le0K` (**every dynamic top `Vt.VtTopDyn λ 0 Ω_{k+3} X̂ 0` has `Ω^{X̂(0)} ≤ Y_{k+2}`**, given the reading at
  `Y_{k+3}`), `vxDyn_gtOm3` (**every dynamic top `VtTopDyn λ 0 Ω₃ X̂ 0` has `Y₂ < Ω^{X̂(Ω₃)}`**);
* `vxDyn_nonconst` (**`X̂(0) ≠ X̂(Ω₃)`**: no dynamic top at `Ω₃` over the base `0` has an image that agrees at the
  transformed sub-base `0 + W^{Ω₃+0}·1 = Ω₃` with the image at `0`: the compatibility "`X̂(β + W^{X+e}·γ) = X̂(β)`"
  asked of the exponent of `Vq.vqStepA` fails for every image, `vxNoCompat`), `vxNoTop_Om3` (the constant case:
  `Vq.vqNoTop_Om3` again).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Vx

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Ro Googology.Trans.PoR.InaccPsi.R2.Rv
  Googology.Trans.PoR.InaccPsi.R2.Ug Googology.Trans.PoR.InaccPsi.R2.Uj Googology.Trans.PoR.InaccPsi.R2.Vk
  Googology.Trans.PoR.InaccPsi.R2.Vn Googology.Trans.PoR.InaccPsi.R2.Vq

variable {S : InaccSeq.{0}}

/-- **The image read from the base `0`**: given `Θ(ψ₂(Y_{k+3})) = ψ₁(A + 1 + Y_{k+2})`,
`Θ(T_{Ω_{k+3}}(0)) = ψ₁(A + 1 + Ω^{Y_{k+2}})`. -/
theorem vxImg0K {l A : Ordinal.{0}} (k : ℕ)
    (hYk : gxTh (upsilon l) (ldAtR S l) (S.psi (ujY S ((k : Ordinal.{0}) + 1)) (Om (1 + 1))) =
      S.psi (A + 1 + ujY S (k : Ordinal.{0})) (Om 1)) :
    gxTh (upsilon l) (ldAtR S l) (leTe S (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) 0) =
      S.psi (A + 1 + leOe (ujY S (k : Ordinal.{0}))) (Om 1) := by
  have hY : ujY S (k : Ordinal.{0}) = S.psi (Om ((k : Ordinal.{0}) + 1 + 1)) (Om ((k : Ordinal.{0}) + 1 + 1)) := rfl
  have h1 : Om 1 < ujY S (k : Ordinal.{0}) :=
    (Om_le_Om.2 (le_add_self : (1 : Ordinal.{0}) ≤ (k : Ordinal.{0}) + 1)).trans_lt (ujY_gt _)
  rw [Ua.uaOe_fix (gg_SC_eps (ujY_SC _)) h1, vxTe_OmK k 0, zero_add, zero_add]
  exact hYk

section Main

variable {l ηx A : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)

include hl hX hA hρ

/-- **`k = 0`: the image read from the base `0` is `Y₂ = T(Y(0))`**:
`Θ(T_{Ω₃}(0)) = ψ₁(A + 1 + Ω^{Y₂})` and `T(ψ₃(0 + Ω₃)) = Y₂`. -/
theorem vxImg0 :
    gxTh (upsilon l) (ldAtR S l) (leTe S (Om (1 + 1 + 1)) 0) =
        S.psi (A + 1 + leOe (S.psi (Om (1 + 1)) (Om (1 + 1)))) (Om 1) ∧
      Vb.vbT S l (S.psi (0 + Om (1 + 1 + 1)) (Om (1 + 1 + 1))) = S.psi (Om (1 + 1)) (Om (1 + 1)) := by
  have h := vxImg0K (S := S) (l := l) (A := A) 0 (vnTheta_hyp0 hl hX hA hρ)
  simp only [Nat.cast_zero, zero_add] at h
  rw [ujY_zero] at h
  refine ⟨h, ?_⟩
  rw [zero_add]
  exact Vb.vbT_Y hl hX

omit hl hX hρ in
theorem vxHatA1 : A + 1 ∈ S.CSet (A + 1) (S.psi (A + 1) (Om 1)) :=
  CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hA) (CSet.one_mem _ _)

/-- **Every dynamic top at `Ω_{k+3}` over the base `0` has `Ω^{X̂(0)} ≤ Y_{k+2}`** (given the reading at `Y_{k+3}`). -/
theorem vxDyn_le0K (k : ℕ)
    (hYk : gxTh (upsilon l) (ldAtR S l) (S.psi (ujY S ((k : Ordinal.{0}) + 1)) (Om (1 + 1))) =
      S.psi (A + 1 + ujY S (k : Ordinal.{0})) (Om 1))
    {Xh : Ordinal.{0} → Ordinal.{0}}
    (hT : Vt.VtTopDyn S l 0 (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) Xh 0) :
    leOe (Xh 0) ≤ ujY S (k : Ordinal.{0}) := by
  by_contra hgt
  push Not at hgt
  have hκ1 : S.InR (Om 1) := Low.InR_Om_one
  have hXω : Om ((k : Ordinal.{0}) + 1 + 1 + 1) < Om ω := Om_lt_Om.2 (vkNat_lt_omega k)
  have h := hT 0 (A + 1) (vkBase0 l hXω) le_rfl (vxHatA1 hA) (ldBlk_zero hA hρ)
  rw [add_zero, gxTh_zero, add_zero] at h
  have h0 := vxImg0K (S := S) (l := l) (A := A) k hYk
  have h1 : Om 1 < ujY S (k : Ordinal.{0}) :=
    (Om_le_Om.2 (le_add_self : (1 : Ordinal.{0}) ≤ (k : Ordinal.{0}) + 1)).trans_lt (ujY_gt _)
  rw [Ua.uaOe_fix (gg_SC_eps (ujY_SC _)) h1, h] at h0
  have hAω := vnA_ge hl hX hA hρ
  have hle : A ≤ A + 1 + leOe (Xh 0) := le_self_add.trans le_self_add
  have hlt : A + 1 + ujY S (k : Ordinal.{0}) < A + 1 + leOe (Xh 0) := (add_lt_add_iff_left _).2 hgt
  have hΩk : Om ((k : Ordinal.{0}) + 1 + 1) < A + 1 + leOe (Xh 0) :=
    ((Om_lt_Om.2 (Vb.vbNat_lt_omega k)).trans_le hAω).trans_le hle
  have hmem : A + 1 + ujY S (k : Ordinal.{0}) ∈ S.CSet (A + 1 + leOe (Xh 0)) (S.psi (A + 1 + leOe (Xh 0)) (Om 1)) :=
    CSet.add_mem (CSet.add_mem ((psi_mono (S := S) hκ1 hle).2 hA) (CSet.one_mem _ _))
      (CSet.psi_mem hΩk (InR_Om_succ ((k : Ordinal.{0}) + 1)) (vnOmK_mem k _ _) (vnOmK_mem k _ _))
  have h2 := psi_lt_psi_of_mem hκ1 hlt hmem
  rw [h0] at h2
  exact lt_irrefl _ h2

/-- `k = 0`: **every dynamic top `VtTopDyn λ 0 Ω₃ X̂ 0` has `Ω^{X̂(0)} ≤ Y₂`**. -/
theorem vxDyn_le0 {Xh : Ordinal.{0} → Ordinal.{0}} (hT : Vt.VtTopDyn S l 0 (Om (1 + 1 + 1)) Xh 0) :
    leOe (Xh 0) ≤ S.psi (Om (1 + 1)) (Om (1 + 1)) := by
  have hT' : Vt.VtTopDyn S l 0 (Om (((0 : ℕ) : Ordinal.{0}) + 1 + 1 + 1)) Xh 0 := by
    simpa only [Nat.cast_zero, zero_add] using hT
  have h := vxDyn_le0K hl hX hA hρ 0 (vnTheta_hyp0 hl hX hA hρ) hT'
  simpa only [Nat.cast_zero, ujY_zero] using h

/-- **Every dynamic top `VtTopDyn λ 0 Ω₃ X̂ 0` has `Y₂ < Ω^{X̂(Ω₃)}`.** -/
theorem vxDyn_gtOm3 {Xh : Ordinal.{0} → Ordinal.{0}} (hT : Vt.VtTopDyn S l 0 (Om (1 + 1 + 1)) Xh 0) :
    S.psi (Om (1 + 1)) (Om (1 + 1)) < leOe (Xh (Om (1 + 1 + 1))) := by
  by_contra hle
  push Not at hle
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

/-- **The image of every dynamic top at `Ω₃` over the base `0` is not constant**: `X̂(0) ≠ X̂(Ω₃)`. -/
theorem vxDyn_nonconst {Xh : Ordinal.{0} → Ordinal.{0}} (hT : Vt.VtTopDyn S l 0 (Om (1 + 1 + 1)) Xh 0) :
    Xh 0 ≠ Xh (Om (1 + 1 + 1)) := by
  intro he
  have h1 := vxDyn_le0 hl hX hA hρ hT
  have h2 := vxDyn_gtOm3 hl hX hA hρ hT
  rw [he] at h1
  exact absurd (h2.trans_le h1) (lt_irrefl _)

/-- **The compatibility asked of the exponent of `Vq.vqStepA` fails for every image**: for every dynamic top at
`Ω₃` over the base `0`, the image at the transformed sub-base `0 + W^{Ω₃+0}·1` differs from the image at `0`. -/
theorem vxNoCompat {Xh : Ordinal.{0} → Ordinal.{0}} (hT : Vt.VtTopDyn S l 0 (Om (1 + 1 + 1)) Xh 0) :
    Xh (0 + leWe (Om (1 + 1 + 1) + 0) * 1) ≠ Xh 0 := by
  rw [add_zero, vnWe_Om3, mul_one, zero_add]
  exact fun h => vxDyn_nonconst hl hX hA hρ hT h.symm

/-- The constant case: **`¬ RvTop λ 0 Ω₃ X̂ 0` for every `X̂`** (`Vq.vqNoTop_Om3`, from `vxDyn_nonconst`). -/
theorem vxNoTop_Om3 (Xh : Ordinal.{0}) : ¬ RvTop S l 0 (Om (1 + 1 + 1)) Xh 0 := fun h =>
  vxDyn_nonconst hl hX hA hρ (Vt.vtTopDyn_const h) rfl

end Main

#print axioms vxImg0K
#print axioms vxImg0
#print axioms vxDyn_le0K
#print axioms vxDyn_le0
#print axioms vxDyn_gtOm3
#print axioms vxDyn_nonconst
#print axioms vxNoCompat
#print axioms vxNoTop_Om3

end Googology.Trans.PoR.InaccPsi.R2.Vx
