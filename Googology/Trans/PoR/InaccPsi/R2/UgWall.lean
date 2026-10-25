import Googology.Trans.PoR.InaccPsi.R2.UgLaw

/-!
# The wall of the level systems at `Γ₂`: the closure condition asks codes, and codes stay below `Γ₂`

`W^E = Ω₂^E`, `Γ₂ = Ua.uaGam = ψ₃(0)`, codes `LeCl Ω₂ Q` (from the ordinals below `Q`, `Ω₂`, `+`, `φ`),
`CL = Sn.SnCL` (the closure condition: `E` is a code over every strongly critical `Q ≥ ψ₂(b + W^{X₀ + W^E})`).

* `ugLeCl_lt` (**a code over `Q ≤ Ω₂` is below `Γ₂`**);
* `ugSnCL_wall` (**THE CLOSURE CONDITION HOLDS ONLY BELOW `Γ₂`**: `Sn.SnCL S E b X₀ ⇒ E < Γ₂`);
* `ugStG_wall` (**every level of a family `St.StG` is below `Γ₂`**, whatever the bound `E_b` of the level system),
  `ugStG_X` (**every shift `X` of `St.stShG` is below `Γ₂`**), so the atoms `ψ₂(β + W^X)` that the level systems
  reach have `X < Γ₂ = ψ₃(0)`; the atoms `ψ₂(ψ₃(0)) ≤ s ≤ θ` of `Ud.UdAtMove25` need a closure condition with
  `ψ₃`-atoms (codes with the generator `Ω₂` and the atoms `ψ₃(d)`).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ug

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Sn
  Googology.Trans.PoR.InaccPsi.R2.Ua Googology.Trans.PoR.InaccPsi.R2.St

variable {S : InaccSeq.{0}}

/-- **A code over `Q ≤ Ω₂` is below `Γ₂`.** -/
theorem ugLeCl_lt {Q x : Ordinal.{0}} (hQ : Q ≤ Om (1 + 1)) (h : LeCl (Om (1 + 1)) Q x) : x < uaGam := by
  induction h with
  | small h => exact (h.trans_le hQ).trans uaGam_spec.2
  | om => exact uaGam_spec.2
  | add _ _ ihx ihy => exact uaGam_spec.1.isPrincipal ihx ihy
  | phi _ _ ihx ihy => exact uaGam_spec.1.2 _ ihx _ ihy

/-- **THE CLOSURE CONDITION HOLDS ONLY BELOW `Γ₂`.** -/
theorem ugSnCL_wall {E b X0 : Ordinal.{0}} (h : SnCL S E b X0) : E < uaGam :=
  ugLeCl_lt (psi_lt (InR_Om_succ 1) _).le (h _ (SC_psi (InR_Om_succ 1) _) le_rfl)

/-- **Every level of a family `St.StG` is below `Γ₂`.** -/
theorem ugStG_wall {l Eb β X Xh E : Ordinal.{0}} {Th : Ordinal.{0} → Ordinal.{0} → Ordinal.{0}}
    (h : StG S l Eb Th β X Xh E) : E < uaGam := by
  cases h with
  | one _ _ _ hcl _ _ _ => exact ugSnCL_wall hcl
  | add _ _ _ _ _ hcl _ _ _ => exact ugSnCL_wall hcl

/-- **Every shift of a family `St.StG` is below `Γ₂`.** -/
theorem ugStG_X {l Eb β X Xh E : Ordinal.{0}} {Th : Ordinal.{0} → Ordinal.{0} → Ordinal.{0}}
    (h : StG S l Eb Th β X Xh E) : X < uaGam := by
  have hG := uaGam_spec
  have hterm : ∀ {E' X0 ζ : Ordinal.{0}}, E' < uaGam → (∃ j, ζ < rvEE S X0 β E' j) → leWe E' * ζ < uaGam := by
    intro E' X0 ζ hE' hj
    obtain ⟨j, hj⟩ := hj
    exact (rvWe_lt_succ (hj.trans (rvEE_lt_Om2 j))).trans
      (leWe_lt_SC hG.1 hG.2 (hG.1.isSuccLimit.succ_lt hE')).1
  induction h with
  | @one E ζ _ _ _ hcl _ _ hj => exact hterm (ugSnCL_wall hcl) hj
  | @add X0 Xh0 E0 E ζ _ _ _ _ _ hcl _ _ hj ih => exact hG.1.isPrincipal ih (hterm (ugSnCL_wall hcl) hj)

/-- **Every shift of `St.stShG` is below `Γ₂`.** -/
theorem ugShG_X {l Eb b X Xh : Ordinal.{0}} {Th : Ordinal.{0} → Ordinal.{0} → Ordinal.{0}}
    (h : stShG S l Eb Th b X Xh) : X < uaGam := by
  obtain ⟨E, hE⟩ := h
  exact ugStG_X hE

end Googology.Trans.PoR.InaccPsi.R2.Ug
