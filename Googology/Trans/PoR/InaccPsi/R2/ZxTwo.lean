import Googology.Trans.PoR.InaccPsi.R2.ZxJump

/-!
# Zx: THE TOP LAW AT EVERY EXPONENT `Ω_{k+3} + Ω₂·Ω₂ + e` (the first jump past the coefficients of `Ω₂`)

`Θ`, `T`, `A`, `W^x`, `Ω^x`, `Zd.ZdLaw` as in `Zd.zdSuccQ`; `W² = W^{1+1} = Ω₂·Ω₂`.  The jump `Zx.zxLawJ` at `h = 1`
over the shifts `Ω_{k+3} + Ω₂·u` of `Zw.zwChain` (their base condition `Zw.ZwQ` is the ownership of the iterates,
`Zx.zxU_own`) gives the law at `Ω_{k+3} + W²`; `X₂ = Ω_{k+3} + W²` is again a shift (`T X₂ = Ω_{k+2} + Ω^2`), so
`Zd.zdTopUpQ` gives every code `e`.

* `zxEx_one` (the exponent `h = 1`), `zxLaw2` (**the law at `Ω_{k+3} + Ω₂·Ω₂`** on every base of exponent `0`),
* `zxSh2` (**`Ω_{k+3} + Ω₂·Ω₂` is a shift**), `zxLaw2All` (**THE TOP LAW AT EVERY EXPONENT `Ω_{k+3} + Ω₂·Ω₂ + e`**:
  `Θ(ψ₂(β + W^{Ω_{k+3}+Ω₂·Ω₂+e})) = ψ₁(A + 1 + ψ₂(T(β + W^{Ω_{k+3}+Ω₂·Ω₂+e})))`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zx

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Vk
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Zd

variable {S : InaccSeq.{0}}

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- The exponent `h = 1`: `T 1 = 1`, threshold `0`. -/
theorem zxEx_one : ZxEx S l 1 1 0 := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  obtain ⟨h1D, hT1⟩ := Xi.xiSmall hl hX (gg_one_lt_of_SC hρSC).le (fun a b => CSet.one_mem a b)
  exact ⟨h1D, hT1, fun a c _ _ => CSet.one_mem a c,
    fun a c _ _ => by rw [mul_one]; exact CSet.Om_mem (CSet.one_mem _ _), GxCl.zero hρSC.1⟩

/-- **`Ω_{k+3} + Ω₂·Ω₂` is a shift**, `T(Ω_{k+3} + W²) = Ω_{k+2} + Ω^2`, threshold `0`. -/
theorem zxSh2 (k : ℕ) :
    ZdShQ S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + leWe (1 + 1)) (Om ((k : Ordinal.{0}) + 1 + 1) + leOe (1 + 1))
      0 := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hs0 := zdSh_Om hl hX (S := S) k
  obtain ⟨h1D, hT1⟩ := Xi.xiSmall hl hX (gg_one_lt_of_SC hρSC).le (fun a b => CSet.one_mem a b)
  have h2D : VbD S l (1 + 1) :=
    ⟨CSet.add_mem h1D.1 h1D.1, CSet.add_mem h1D.2.1 h1D.2.1, vkOmW.1.isPrincipal h1D.2.2 h1D.2.2⟩
  have hT2 : vbT S l (1 + 1) = 1 + 1 := by rw [Vh.vhT_add hl hX h1D h1D, hT1]
  obtain ⟨hW2D, hW2T⟩ := zxTW hl hX h2D
  have h2m : ∀ a c : Ordinal.{0}, (1 + 1 : Ordinal.{0}) ∈ S.CSet a c := fun a c =>
    CSet.add_mem (CSet.one_mem a c) (CSet.one_mem a c)
  have hKm : ∀ a c : Ordinal.{0}, upsilon l ≤ c →
      Om ((k : Ordinal.{0}) + 1 + 1) + leOe (1 + 1) ∈ S.CSet a c := fun a c h =>
    CSet.add_mem (hs0.Km a c h) (leOe_mem (h2m a c))
  refine ⟨fun a c h _ => CSet.add_mem (hs0.mem a c h) (leWe_mem (h2m a c)),
    vkOmW.1.isPrincipal hs0.lt hW2D.2.2, ?_, fun a c h _ => hKm a c h,
    fun a c h _ => ldMulK_mem Ph.ph_SC_Om1 (CSet.Om_mem (CSet.one_mem _ _)) (hKm a c h),
    hs0.Kpos.trans_le le_self_add, CSet.add_mem hs0.memH hW2D.1, GxCl.zero hρSC.1, (ConjT.SC_th S).1⟩
  rw [Vh.vhT_add hl hX hs0.D hW2D, hs0.T, hW2T, hT2]

variable {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)

include hA hρ

/-- **The law at `Ω_{k+3} + Ω₂·Ω₂`** on every base of exponent `0`. -/
theorem zxLaw2 (k : ℕ) {β : Ordinal.{0}} (hβD : VbD S l β)
    (hB : Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + leWe (1 + 1)) 0 β) :
    ZdLaw S l A (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + leWe (1 + 1)) 0 β := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  refine zxLawJ hl hX hA hρ ((zdSh_Om hl hX (S := S) k).toQ (leRho hl hX).1.1) (zxEx_one hl hX) hβD hB
    (SC_psi hκ2 _).1 (SC_psi hκ2 _).1 fun u hu huθ hown hBu => ?_
  have e1 : Om ((k : Ordinal.{0}) + 1 + 1 + 1) + leWe 1 * u = zdX k u := by unfold zdX; rw [leWe_one]
  rw [e1] at hBu ⊢
  exact Zw.zwChain hl hX hA hρ k u hu huθ 0 (GxCl.zero (leRho hl hX).1.1) ldOm2_SC.1 β hβD hBu
    fun ξ' hc hle => by have h := hown ξ' hc hle; unfold zdX; rwa [leWe_one] at h

/-- **THE TOP LAW AT EVERY EXPONENT `Ω_{k+3} + Ω₂·Ω₂ + e`** (`e` a code below `Ω₂`, `β ∈ D` a base of exponent `e`). -/
theorem zxLaw2All (k : ℕ) :
    ∀ e, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) → ∀ β, VbD S l β →
      Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + leWe (1 + 1)) e β →
        ZdLaw S l A (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + leWe (1 + 1)) e β := fun e hec he2 β hβD hB =>
  zdTopUpQ hl hX hA hρ (zxSh2 hl hX k) (fun _ => True) (fun _ _ => (SC_psi (InR_Om_succ 1) _).1)
    (fun _ _ _ _ => trivial) (fun _ hβD hB _ => zxLaw2 hl hX hA hρ k hβD hB) e hec he2 β hβD hB trivial

end Main

end Googology.Trans.PoR.InaccPsi.R2.Zx

#print axioms Googology.Trans.PoR.InaccPsi.R2.Zx.zxLaw2All
