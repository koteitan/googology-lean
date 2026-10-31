import Googology.Trans.PoR.InaccPsi.R2.WzLow

/-!
# The upper bound `Θ(ψ_{Ω₂}(a)) ≤ ψ_{Ω₁}(A + 1 + ψ_{Ω₂}(T a))` (open statement `WzUpU`) and the law at
`k = 0`, `β = Ω₃` from it

`Θ = gxTh ρ_λ (ldAtR λ)`, `T = Vb.vbT S λ` (the image one level down), `A = A_{η_λ}`, `X̂ = ψ_{Ω₂}(Ω₂ + Ω₂)`.

**`WzUpU S`**: at every restart `λ` with an own `A`, `ψ₁(A) = ρ_λ`, every normal member `a` of the domain of `T`
(`a ∈ D`, `a ∈ Cl(a, ψ₂(a))`) has `Θ(ψ₂(a)) ≤ ψ₁(A + 1 + ψ₂(T a))`.  At `a = β + Ω_{k+3}` the right-hand side is
`ψ₁(A + 1 + X̂⁰_k(β))` (`Wv.wvX0`), so `WzUpU` is the upper half of `skX0Law` wherever the base image is absorbed.

* `wzT_Om3` (`T(Ω₃) = Ω₂`), `wzD_Om33` (`Ω₃ + Ω₃ ∈ D`), `wzT_Om33` (`T(Ω₃ + Ω₃) = Ω₂ + Ω₂`);
* `wzUp_Om3_of` (**`WzUpU ⇒` the upper half `Θ(ψ₂(Ω₃·2)) ≤ ψ₁(A + X̂)`**), `wzLaw_of_U` (**`WzUpU ⇒` the candidate law
  at `k = 0`, `β = Ω₃`**, with `Wz.wzLaw_iff`);
* tests of `WzUpU` (REFUTE FIRST): `wzU_zero` (`a = 0`), `wzU_Om3` (`a = Ω₃`: equality, `Θ(ψ₂(Ω₃)) =
  ψ₁(A + 1 + ψ₂(T Ω₃))`), `wzU_Om33_low` (`a = Ω₃ + Ω₃`: the lower half `ψ₁(A + X̂) ≤ Θ` meets the bound
  `ψ₁(A + 1 + X̂) = ψ₁(A + X̂)`, so `WzUpU` is tight there), `wzU_lift` (`a = Ω₃ + κ ζ`, `ζ < X̂`: the lift gives
  `ψ₁(A + ζ) ≤ Θ`, the bound is `ψ₁(A + 1 + ψ₂(Ω₂ + ζ))`, and `ζ < ψ₂(Ω₂ + ζ)`: consistent).

No new axiom.  New definition: `WzUpU` (an open statement; no statement of the repo depends on it).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Wz

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Vk

variable {S : InaccSeq.{0}}

/-- **THE UPPER BOUND (open)**: `Θ(ψ₂(a)) ≤ ψ₁(A + 1 + ψ₂(T a))` for every normal member `a` of the domain of `T`. -/
def WzUpU (S : InaccSeq.{0}) : Prop :=
  ∀ (l ηx A a : Ordinal.{0}), IsRestartIdx l → upsilon l < Pv S ηx →
    A ∈ S.CSet A (S.psi A (Om 1)) → S.psi A (Om 1) = upsilon l →
    Vb.VbD S l a → a ∈ S.CSet a (S.psi a (Om (1 + 1))) →
    gxTh (upsilon l) (ldAtR S l) (S.psi a (Om (1 + 1))) ≤
      S.psi (A + 1 + S.psi (Vb.vbT S l a) (Om (1 + 1))) (Om 1)

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

theorem wzT_Om3 : Vb.vbT S l (Om (1 + 1 + 1)) = Om (1 + 1) := by
  have hO := Vb.vbT_Om (S := S) hl hX (k := 2) (by norm_num)
  rwa [wzTwo] at hO

omit hl hX in
theorem wzD_Om3 : Vb.VbD S l (Om (1 + 1 + 1)) := by
  have h := Vb.vbD_Om (S := S) (l := l) 2; rwa [wzTwo] at h

omit hl hX in
theorem wzD_Om33 : Vb.VbD S l (Om (1 + 1 + 1) + Om (1 + 1 + 1)) :=
  ⟨CSet.add_mem (wzD_Om3 (S := S) (l := l)).1 (wzD_Om3 (S := S) (l := l)).1,
    CSet.add_mem (wzD_Om3 (S := S) (l := l)).2.1 (wzD_Om3 (S := S) (l := l)).2.1,
    vkOmW.1.isPrincipal Ry.ryOm3_lt Ry.ryOm3_lt⟩

theorem wzT_Om33 : Vb.vbT S l (Om (1 + 1 + 1) + Om (1 + 1 + 1)) = Om (1 + 1) + Om (1 + 1) := by
  rw [Vh.vhT_add hl hX wzD_Om3 wzD_Om3, wzT_Om3 hl hX]

omit hl hX in
/-- `1 + X̂ = X̂`. -/
theorem wzOneX : 1 + S.psi (Om (1 + 1) + Om (1 + 1)) (Om (1 + 1)) = S.psi (Om (1 + 1) + Om (1 + 1)) (Om (1 + 1)) :=
  one_add_of_omega0_le (Lw.lw_omega_lt_SC (wzX_SC (S := S))).le

/-- **`WzUpU ⇒` the upper half at `k = 0`, `β = Ω₃`**: `Θ(ψ₂(Ω₃ + Ω₃)) ≤ ψ₁(A + X̂)`. -/
theorem wzUp_Om3_of (hU : WzUpU S) {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1)))
    (hρ : S.psi A (Om 1) = upsilon l) :
    gxTh (upsilon l) (ldAtR S l) (S.psi (Om (1 + 1 + 1) + Om (1 + 1 + 1)) (Om (1 + 1))) ≤
      S.psi (ConjT.Aη S (cdEta S l) + S.psi (Om (1 + 1) + Om (1 + 1)) (Om (1 + 1))) (Om 1) := by
  have h := hU l ηx A _ hl hX hA hρ wzD_Om33 (CSet.add_mem (Ry.ryOm3_mem _ _) (Ry.ryOm3_mem _ _))
  rw [wzT_Om33 hl hX, add_assoc A 1 (S.psi (Om (1 + 1) + Om (1 + 1)) (Om (1 + 1))), wzOneX] at h
  obtain ⟨-, rfl⟩ := Wg.wgOwnEta hl hX hA hρ
  exact h

/-- **`WzUpU ⇒` THE CANDIDATE LAW AT `k = 0`, `β = Ω₃`** (`skX0Law` at that point). -/
theorem wzLaw_of_U (hU : WzUpU S) {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1)))
    (hρ : S.psi A (Om 1) = upsilon l) :
    Wg.WgTopAt S l (Om (1 + 1 + 1)) (Wv.wvX0 S l 0 (Om (1 + 1 + 1))) 0 (Om (1 + 1 + 1)) :=
  (wzLaw_iff hl hX hA hρ).2 (wzUp_Om3_of hl hX hU hA hρ)

/-- **Test of `WzUpU` at `a = 0`.** -/
theorem wzU_zero {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l) :
    gxTh (upsilon l) (ldAtR S l) (S.psi 0 (Om (1 + 1))) ≤
      S.psi (A + 1 + S.psi (Vb.vbT S l 0) (Om (1 + 1))) (Om 1) := by
  rw [ldBlk_zero hA hρ]
  exact (psi_mono (S := S) Low.InR_Om_one le_self_add).1

/-- **Test of `WzUpU` at `a = Ω₃`: equality** (`Θ(ψ₂(Ω₃)) = ψ₁(A + 1 + Y₂)`, `T Ω₃ = Ω₂`). -/
theorem wzU_Om3 {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l) :
    gxTh (upsilon l) (ldAtR S l) (S.psi (Om (1 + 1 + 1)) (Om (1 + 1))) =
      S.psi (A + 1 + S.psi (Vb.vbT S l (Om (1 + 1 + 1))) (Om (1 + 1))) (Om 1) := by
  rw [wzT_Om3 hl hX]; exact wzBase hl hX hA hρ

/-- **Test of `WzUpU` at `a = Ω₃ + Ω₃`**: the proved lower half reaches the bound (`1 + X̂ = X̂`): `WzUpU` is tight
there, and at this `a` it is equivalent to the law (`wzLaw_iff`). -/
theorem wzU_Om33_low {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l) :
    S.psi (A + 1 + S.psi (Vb.vbT S l (Om (1 + 1 + 1) + Om (1 + 1 + 1))) (Om (1 + 1))) (Om 1) ≤
      gxTh (upsilon l) (ldAtR S l) (S.psi (Om (1 + 1 + 1) + Om (1 + 1 + 1)) (Om (1 + 1))) := by
  rw [wzT_Om33 hl hX, add_assoc A 1 (S.psi (Om (1 + 1) + Om (1 + 1)) (Om (1 + 1))), wzOneX]
  have h := wzLow hl hX hA hρ
  rwa [← (Wg.wgOwnEta hl hX hA hρ).2] at h

/-- **Test of `WzUpU` along the lift at the base `Ω₃`**: for every member `ζ < X̂` the lower bound of the lift is
below the bound of `WzUpU` at `a = Ω₃ + κ ζ` (`ψ₁(A + ζ) ≤ ψ₁(A + 1 + ψ₂(Ω₂ + ζ))`, from `ζ < ψ₂(Ω₂ + ζ)`). -/
theorem wzU_lift {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)
    {ζ : Ordinal.{0}} (hζX : ζ < S.psi (Om (1 + 1) + Om (1 + 1)) (Om (1 + 1))) :
    S.psi (A + ζ) (Om 1) ≤ S.psi (A + 1 + S.psi (Om (1 + 1) + ζ) (Om (1 + 1))) (Om 1) := by
  refine (psi_mono (S := S) Low.InR_Om_one ?_).1
  rw [add_assoc A 1 (S.psi (Om (1 + 1) + ζ) (Om (1 + 1)))]
  exact add_le_add le_rfl ((wzLtPsi hζX).le.trans le_add_self)

end Main

end Googology.Trans.PoR.InaccPsi.R2.Wz

#print axioms Googology.Trans.PoR.InaccPsi.R2.Wz.wzT_Om33
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wz.wzUp_Om3_of
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wz.wzLaw_of_U
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wz.wzU_zero
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wz.wzU_Om3
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wz.wzU_Om33_low
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wz.wzU_lift
