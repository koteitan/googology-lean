import Googology.Trans.PoR.InaccPsi.R2.VnRound

/-!
# A shift own relative to the base (membership `X ∈ Cl(b + W^X, T_X(b))`), image relative to `A`

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `T_E(β) = ψ_{Ω₂}(β + W^E)`, `A` with `ψ_{Ω₁}(A) = ρ_λ`,
`A ∈ Cl(A, ψ_{Ω₁}(A))`.

**`VqSh S λ A b X X̂`**: the fields of `Vk.VkSh` with the two self-relative membership fields replaced by
base-relative ones: `X ∈ Cl(b + W^X, T_X(b))` and `X̂ ∈ Cl(A + Ω^{X̂}, Θ(T_X(b)))`.  The self-relative form
`X ∈ Cl(X, ·)` has no member in `[Y_{k+3}, Ω_{k+3})` (`Vn.vnNoSh`); the base-relative one has (`Vq.VqWit`).

* `vqSh_of_vk` (**every `Vk.VkSh` is a `VqSh`**, any `A`), `vqSh_mono` (in `b`), `vqSh_monoA` (in `A`);
* `vqMem`, `vqMemh`, `vqCl`, `vqClh` (the fields at larger bases);
* `vqHat_ge` (**every base image `Â` of a base, `Θ(ψ₂(β)) = ψ₁(Â)` with `Â` own, has `A + 1 ≤ Â`**), `vqHatA`,
  `vqA_le`, `vqA_le1` (so the image field is available at every `Â` the top law `Rv.RvTop` quantifies over).

No new axiom.  New definition: `VqSh`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Vq

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Ro Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Uj
  Googology.Trans.PoR.InaccPsi.R2.Vk

variable {S : InaccSeq.{0}}

/-- **A shift `X` own relative to the base `b`** (membership relative to `b + W^X`), with its level-1 image `X̂`
own relative to `A` (membership relative to `A + Ω^{X̂}`); no bound. -/
structure VqSh (S : InaccSeq.{0}) (l A b X Xh : Ordinal.{0}) : Prop where
  ne : X ≠ 0
  dvd : Om (1 + 1) ∣ X
  hull : X ∈ cdHull S l
  mem : X ∈ S.CSet (b + leWe X) (S.psi (b + leWe X) (Om (1 + 1)))
  memh : Xh ∈ S.CSet (A + leOe Xh) (gxTh (upsilon l) (ldAtR S l) (S.psi (b + leWe X) (Om (1 + 1))))
  cl : ∀ Q, SC Q → S.psi (b + leWe X) (Om (1 + 1)) ≤ Q → VkA (1 + 1) Q X
  clh : ∀ Q, SC Q → gxTh (upsilon l) (ldAtR S l) (S.psi (b + leWe X) (Om (1 + 1))) ≤ Q → VkA 1 Q Xh

/-- **Every `Vk.VkSh` is a `VqSh`** (for every `A`). -/
theorem vqSh_of_vk {l A b X Xh : Ordinal.{0}} (hs : VkSh S l b X Xh) : VqSh S l A b X Xh :=
  ⟨hs.ne, hs.dvd, hs.hull, CSet_mono ((ujLe_We X).trans le_add_self) le_rfl hs.mem,
    CSet_mono ((ujLe_Oe Xh).trans le_add_self) le_rfl hs.memh, hs.cl, hs.clh⟩

section Fields

variable {l A b X Xh : Ordinal.{0}} (hs : VqSh S l A b X Xh)
include hs

theorem vqMem {a c x : Ordinal.{0}} (ha : b + leWe X ≤ a) (hx : b + leWe X ≤ x)
    (hb : S.psi x (Om (1 + 1)) ≤ c) : X ∈ S.CSet a c :=
  CSet_mono ha ((psi_mono (S := S) (InR_Om_succ 1) hx).1.trans hb) hs.mem

theorem vqMemh {a c x : Ordinal.{0}} (ha : A + leOe Xh ≤ a) (hx : b + leWe X ≤ x)
    (hb : gxTh (upsilon l) (ldAtR S l) (S.psi x (Om (1 + 1))) ≤ c) : Xh ∈ S.CSet a c :=
  CSet_mono ha ((gxTh_mono (psi_mono (S := S) (InR_Om_succ 1) hx).1).trans hb) hs.memh

theorem vqCl {Q x : Ordinal.{0}} (hQ : SC Q) (hx : b + leWe X ≤ x) (hb : S.psi x (Om (1 + 1)) ≤ Q) :
    VkA (1 + 1) Q X :=
  hs.cl Q hQ ((psi_mono (S := S) (InR_Om_succ 1) hx).1.trans hb)

theorem vqClh {Q x : Ordinal.{0}} (hQ : SC Q) (hx : b + leWe X ≤ x)
    (hb : gxTh (upsilon l) (ldAtR S l) (S.psi x (Om (1 + 1))) ≤ Q) : VkA 1 Q Xh :=
  hs.clh Q hQ ((gxTh_mono (psi_mono (S := S) (InR_Om_succ 1) hx).1).trans hb)

/-- A shift own relative to `b` is own relative to every `b' ≥ b`. -/
theorem vqSh_mono {b' : Ordinal.{0}} (hbb : b ≤ b') : VqSh S l A b' X Xh := by
  have h0 : b + leWe X ≤ b' + leWe X := add_le_add_left hbb _
  have h1 : S.psi (b + leWe X) (Om (1 + 1)) ≤ S.psi (b' + leWe X) (Om (1 + 1)) :=
    (psi_mono (S := S) (InR_Om_succ 1) h0).1
  exact ⟨hs.ne, hs.dvd, hs.hull, vqMem hs h0 le_rfl h1, vqMemh hs le_rfl le_rfl (gxTh_mono h1),
    fun Q hQ hb => hs.cl Q hQ (h1.trans hb), fun Q hQ hb => hs.clh Q hQ ((gxTh_mono h1).trans hb)⟩

/-- The image `X̂` own relative to `A` is own relative to every `A' ≥ A`. -/
theorem vqSh_monoA {A' : Ordinal.{0}} (hAA : A ≤ A') : VqSh S l A' b X Xh :=
  ⟨hs.ne, hs.dvd, hs.hull, hs.mem, CSet_mono (add_le_add_left hAA _) le_rfl hs.memh, hs.cl, hs.clh⟩

end Fields

/-- **Every base image is above `A`**: `Θ(ψ₂(β)) = ψ₁(Â)` with `Â ∈ Cl(Â, ψ₁(Â))` gives `A + 1 ≤ Â`. -/
theorem vqHat_ge {l A β Â : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)
    (hÂ : Â ∈ S.CSet Â (S.psi Â (Om 1)))
    (hbase : gxTh (upsilon l) (ldAtR S l) (S.psi β (Om (1 + 1))) = S.psi Â (Om 1)) : A + 1 ≤ Â := by
  by_contra h
  push Not at h
  have h1 : S.psi (A + 1) (Om 1) ≤ S.psi Â (Om 1) := by
    rw [← ldBlk_zero hA hρ, ← hbase]
    exact gxTh_mono (psi_mono (S := S) (InR_Om_succ 1) zero_le).1
  have hmem : Â ∈ S.CSet (A + 1) (S.psi (A + 1) (Om 1)) := (psi_mono (S := S) Low.InR_Om_one h.le).2 hÂ
  exact absurd (psi_lt_psi_of_mem Low.InR_Om_one h hmem) (not_lt.2 h1)

theorem vqHatA {l A β Â : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)
    (hÂ : Â ∈ S.CSet Â (S.psi Â (Om 1)))
    (hbase : gxTh (upsilon l) (ldAtR S l) (S.psi β (Om (1 + 1))) = S.psi Â (Om 1)) : A ≤ Â :=
  le_self_add.trans (vqHat_ge hA hρ hÂ hbase)

theorem vqA_le1 {A Â : Ordinal.{0}} (h : A ≤ Â) (Xh y : Ordinal.{0}) : A + leOe Xh ≤ Â + leOe (Xh + y) :=
  add_le_add h (leOe_mono le_self_add)

theorem vqA_le {A Â : Ordinal.{0}} (h : A ≤ Â) (Xh y : Ordinal.{0}) {x : Ordinal.{0}} (hx : x ≠ 0) :
    A + leOe Xh ≤ Â + leOe (Xh + y) * x :=
  add_le_add h ((leOe_mono le_self_add).trans (Ordinal.le_mul_left _ (pos_iff_ne_zero.2 hx)))

end Googology.Trans.PoR.InaccPsi.R2.Vq
