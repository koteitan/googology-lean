import Googology.Trans.PoR.InaccPsi.R2.ZmRa

/-!
# ZmPast: THE LAYERS PAST `X` FROM ONE NAMED STATEMENT (ASSEMBLY FIRST)

`Zb.ZbLayAt` is the layer statement for the atom system `Zb.zbU` (bound `X`).  The same statement for any abstract
atom system `A : Zb.ZbAS` (`ZmLayA A S B`) gives UPPER ∧ LOWER ∧ CapV below `ι(Γ(B)·ω)` (`Zb.zbUV` is generic in the
atom system).  So the conclusions of `skLayLoFixX` and `skLayHiFixX` at a layer `X ≤ c < Ω₂` follow from
`ZmPastAt S c`: one atom system `A` with a layer for every atom index `B < Γ(c+1)`.

* `ZmLayA`, `zmLayA_zbU` (`ZmLayA zbU = ZbLayAt`), `zmUV_of_layA`;
* `ZmPastAt`, `zmLay_of_past` (**`ZmPastAt S c` ⇒ UPPER ∧ LOWER ∧ CapV at every range restart below
  `ι(Γ(φ(ℓ, Γ(c)+1))·ω)`, every `ℓ < Γ(c+1)`**); `ZmLayA zbU S B` for every `B_Γ ≤ B < ε_{B_Γ+ε₀}` is
  `Zm.zmDirectE0`, so the shape is satisfiable.

No new axiom.  New definitions: `ZmLayA`, `ZmPastAt`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zm

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Tf Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Yr Googology.Trans.PoR.InaccPsi.R2.Yw Googology.Trans.PoR.InaccPsi.R2.Gd
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Bt
  Googology.Trans.PoR.InaccPsi.R2.Zb

/-- **A layer for the atom index `B` with the atoms of an abstract atom system `A`.** -/
def ZmLayA (A : ZbAS) (S : InaccSeq.{0}) (B : Ordinal.{0}) : Prop :=
  ∃ L : GdB, ∃ T : Ordinal.{0}, gcG B ≤ T ∧ L.g < Td.tdK S ∧ T ≤ A.V ∧ Om 1 ≤ T ∧ ω ^ T = T ∧
    (∀ y, SC y → y < Om 1 → L.g < y → L.K.E y = gxTh y (A.At y) T) ∧ ZbPolyG A L.K.sys T ∧
    (∀ Z, SC Z → Td.tdK S ≤ Z → GxCl Z (A.At Z) T) ∧ (∀ x, InE x → x < Om1 → L.g < x → eN x < L.K.E x)

theorem zmLayA_zbU (S : InaccSeq.{0}) (B : Ordinal.{0}) : ZmLayA zbU S B ↔ ZbLayAt S B := Iff.rfl

/-- **UPPER ∧ LOWER ∧ CapV below `ι(Γ(B)·ω)` from a layer for `B` with any atom system.** -/
theorem zmUV_of_layA {A : ZbAS} {S : InaccSeq.{0}} [Fact (A.Ok S)] {B : Ordinal.{0}} (h : ZmLayA A S B) {l : Ordinal.{0}}
    (hr : CdRange S l) (hl : l < iota S (gcG B * ω)) : CdUpper S l ∧ CdLower S l ∧ CdCapV S l := by
  obtain ⟨L, T, hBT, hg, hT, hTO, hTE, htop, hP, hcl, htopE⟩ := h
  have hl' : l < iota S (ω ^ T * ω) := by
    rw [hTE]; exact hl.trans_le (iota_mono (S := S) _ _ (mul_le_mul_left hBT ω))
  exact zbUV A L S hg T hT htop hP hcl htopE hTO hr hl'

/-- **THE LAYER `c` PAST `X`**: one atom system, with its hull facts at `S`, with a layer for every atom index
`B < Γ(c+1)`. -/
def ZmPastAt (S : InaccSeq.{0}) (c : Ordinal.{0}) : Prop :=
  ∃ A : ZbAS, A.Ok S ∧ ∀ B, B < gcG (c + 1) → ZmLayA A S B

/-- **`ZmPastAt S c` ⇒ the conclusions of `skLayLoFixX` and `skLayHiFixX` at `c`.** -/
theorem zmLay_of_past {S : InaccSeq.{0}} {c : Ordinal.{0}} (h : ZmPastAt S c) :
    ∀ l, CdRange S l → (∃ ℓ, ℓ < gcG (c + 1) ∧ l < iota S (gcG (veblen ℓ (gcG c + 1)) * ω)) →
      CdUpper S l ∧ CdLower S l ∧ CdCapV S l := by
  rintro l hr ⟨ℓ, hℓ, hl⟩
  obtain ⟨A, hok, hA⟩ := h
  haveI : Fact (A.Ok S) := ⟨hok⟩
  exact zmUV_of_layA (hA _ (Yc.yc_veb_lt_next hℓ)) hr hl

end Googology.Trans.PoR.InaccPsi.R2.Zm
