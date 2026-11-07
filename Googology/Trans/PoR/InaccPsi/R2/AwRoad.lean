import Googology.Trans.PoR.InaccPsi.R2.AwBase

/-!
# AwRoad: the layers from `θ` on and the base, in the form of the road

* `aw_gcG_lt` (`Γ(c) < Ω₂` for `c < Ω₂`), `aw_layPast` (**UPPER, LOWER, CapV AT EVERY RANGE RESTART OF A LAYER `c < Ω₂`**).

No new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Aw

open Ordinal Order Cardinal Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Bt

variable {S : InaccSeq.{0}}

/-- `Γ(c) < Ω₂` for `c < Ω₂`. -/
theorem aw_gcG_lt {c : Ordinal.{0}} (hc : c < Om (1 + 1)) : Gc.gcG c < Om (1 + 1) := by
  have h2 : (1 + 1 : Ordinal.{0}) ≠ 0 := by rw [one_add_one_eq_two]; exact two_ne_zero
  have hreg : (ℵ_ (1 + 1 : Ordinal.{0})).IsRegular := isRegular_aleph_add_one 1
  have hunc : ℵ₀ < ℵ_ (1 + 1 : Ordinal.{0}) := by rw [← aleph_zero]; exact aleph_lt_aleph.2 (pos_iff_ne_zero.2 h2)
  rw [Tf.tf_gcG]
  have hO : Om1 + 1 < Om (1 + 1 : Ordinal.{0}) :=
    SC.add_one_lt Gg.gg_SC_Om2 (by rw [Rj.rj_Om1]; exact Gg.gg_Om1_lt_Om2)
  have hlt : Om1 + 1 + c < Om (1 + 1 : Ordinal.{0}) := Gg.gg_SC_Om2.isPrincipal hO hc
  rw [Om_eq_ord h2] at hlt ⊢
  exact Tf.tf_gamma_lt hreg hunc _ hlt

/-- **UPPER, LOWER, CapV at every range restart of a layer `c < Ω₂`.** -/
theorem aw_layPast {c l ℓ : Ordinal.{0}} (hc : c < Om (1 + 1)) (hr : CdRange S l) (hℓ : ℓ < Gc.gcG (c + 1))
    (hl : l < iota S (Gc.gcG (veblen ℓ (Gc.gcG c + 1)) * ω)) : CdUpper S l ∧ CdLower S l ∧ CdCapV S l := by
  have hS2 := Gg.gg_SC_Om2
  have hE2 : InE (Om (1 + 1 : Ordinal.{0})) := Low.opow_eq_self_of_SC hS2
  have hc1 : c + 1 < Om (1 + 1) := SC.add_one_lt hS2 hc
  have hℓ2 : ℓ < Om (1 + 1) := hℓ.trans (aw_gcG_lt hc1)
  have hG1 : Gc.gcG c + 1 < Om (1 + 1) := SC.add_one_lt hS2 (aw_gcG_lt hc)
  have hv : veblen ℓ (Gc.gcG c + 1) < Om (1 + 1) := hS2.2 _ hℓ2 _ hG1
  have hG : Gc.gcG (veblen ℓ (Gc.gcG c + 1)) * ω < Om (1 + 1) :=
    hE2.mul_lt (aw_gcG_lt hv) (omega0_lt_inE hE2)
  exact aw_UV hr (hl.trans_le (iota_mono _ _ hG.le))

end Googology.Trans.PoR.InaccPsi.R2.Aw
