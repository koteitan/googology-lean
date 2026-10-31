import Googology.Trans.PoR.InaccPsi.R2.WzLow

/-!
# The lift of `Rx.rxLift` at any base `β`, any `θ`-divisible offset `Â` and any level bound `L(ζ)`

`Θ = gxTh ρ_λ (ldAtR λ)`, `κ = rxL S ρ_λ At_λ W` (the level shift, `W = rxW ρ_λ At_λ`), `A = A_{η_λ}`, `θ = ψ_{Ω₂}(Ω_ω)`.

* `xdLift` (**THE GENERIC LIFT**): let `ψ₂(β)` be an atom, `ψ₁(Â) ≤ Θ(ψ₂(β))`, `θ ∣ Â`, `X_b ≤ θ`, `β ∈ H_λ`, and for
  every member `ζ < X_b` of the domain of `κ`: `β + κ ζ < A`, `β ∈ Cl(β + κ ζ, ψ₂(β + κ ζ))`, and a level bound
  `L(ζ)` in the domain with `κ L(ζ) ≤ β + κ ζ` and `x < ψ₂(L(ζ))` for every `x < ζ`.  Then
  `ψ₁(Â + ζ) ≤ Θ(ψ₂(β + κ ζ))` for every member `ζ < X_b` (`Wz.wzLift` is `β = Ω₃`, `Â = A`, `L(ζ) = Ω₂ + ζ`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Xd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ru Googology.Trans.PoR.InaccPsi.R2.Ld
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Rx Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Vk

variable {S : InaccSeq.{0}}

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **THE GENERIC LIFT.** -/
theorem xdLift {β Â Xb : Ordinal.{0}} (Lf : Ordinal.{0} → Ordinal.{0})
    (hβat : S.psi β (Om (1 + 1)) ∈ ldAtR S l)
    (hbase : S.psi Â (Om 1) ≤ gxTh (upsilon l) (ldAtR S l) (S.psi β (Om (1 + 1))))
    (hdvd : ConjT.th S ∣ Â) (hXθ : Xb ≤ ConjT.th S) (hβH : β ∈ cdHull S l)
    (hβA : ∀ ζ, RxE S (rxW (upsilon l) (ldAtR S l)) ζ → ζ < Xb →
      β + rxL S (upsilon l) (ldAtR S l) (rxW (upsilon l) (ldAtR S l)) ζ < ConjT.Aη S (cdEta S l))
    (hβn : ∀ ζ, RxE S (rxW (upsilon l) (ldAtR S l)) ζ → ζ < Xb →
      β ∈ S.CSet (β + rxL S (upsilon l) (ldAtR S l) (rxW (upsilon l) (ldAtR S l)) ζ)
        (S.psi (β + rxL S (upsilon l) (ldAtR S l) (rxW (upsilon l) (ldAtR S l)) ζ) (Om (1 + 1))))
    (hL : ∀ ζ, RxE S (rxW (upsilon l) (ldAtR S l)) ζ → ζ < Xb →
      RxE S (rxW (upsilon l) (ldAtR S l)) (Lf ζ) ∧
      rxL S (upsilon l) (ldAtR S l) (rxW (upsilon l) (ldAtR S l)) (Lf ζ) ≤
        β + rxL S (upsilon l) (ldAtR S l) (rxW (upsilon l) (ldAtR S l)) ζ ∧
      ∀ x, x < ζ → x < S.psi (Lf ζ) (Om (1 + 1))) :
    ∀ ζ, RxE S (rxW (upsilon l) (ldAtR S l)) ζ → ζ < Xb →
      S.psi (Â + ζ) (Om 1) ≤
        gxTh (upsilon l) (ldAtR S l)
          (S.psi (β + rxL S (upsilon l) (ldAtR S l) (rxW (upsilon l) (ldAtR S l)) ζ) (Om (1 + 1))) := by
  obtain ⟨hZ, hZ1⟩ := Le.leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  set W := rxW (upsilon l) (ldAtR S l) with hWdef
  set κ := rxL S (upsilon l) (ldAtR S l) W with hκdef
  have hW : SC W := rxW_SC hZ hZ1 hAt
  have hθSC := ConjT.SC_th S
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hθ2 : ConjT.th S < Om (1 + 1) := psi_lt hκ2 _
  have hθW : ConjT.th S < Om ω := hθ2.trans vkOmW.2
  have hWA : Om ω ≤ ConjT.Aη S (cdEta S l) := ConjT.OmW_le_A S _
  have hEθ : ∀ {T ζ : Ordinal.{0}}, RxN S T ζ → ζ < ConjT.th S → RxE S T ζ :=
    fun hN hζ => ⟨hN, CSet.of_lt hζ, hζ.trans hθW⟩
  have hκH : ∀ ζ, RxE S W ζ → κ ζ ∈ S.CSet (ConjT.Aη S (cdEta S l)) (upsilon l) :=
    fun ζ hζ => rxL_memH hZ hZ1 hAt hW le_rfl hWA (fun g hg => by
      obtain ⟨hcode, hlt2, -⟩ := ruInv_spec (hg.trans_le (min_le_left _ _))
      exact (ldHull_iff hl hX hlt2).2 hcode) ζ hζ
  have hat : ∀ ζ, RxE S W ζ → ζ < Xb → S.psi (β + κ ζ) (Om (1 + 1)) ∈ ldAtR S l :=
    fun ζ hζ hζX => ⟨_, CSet.add_mem hβH (hκH ζ hζ), hβA ζ hζ hζX, rfl⟩
  have hpos : ∀ ζ, RxE S W ζ → ζ < Xb → ζ ≠ 0 →
      S.psi β (Om (1 + 1)) < S.psi (β + κ ζ) (Om (1 + 1)) := fun ζ hζ hζX h0 =>
    psi_lt_psi_of_mem hκ2 (lt_add_of_pos_right _ (rxL_pos hZ hZ1 hAt hζ h0)) (hβn ζ hζ hζX)
  set D : Set Ordinal.{0} := {ζ | RxE S W ζ ∧ ζ < Xb} with hDdef
  have hcl : ∀ ζ ∈ D, gxTh (upsilon l) (ldAtR S l) (S.psi (β + κ ζ) (Om (1 + 1))) < Om 1 →
      ∀ e, HCl S (Â + ζ) (gxTh (upsilon l) (ldAtR S l) (S.psi (β + κ ζ) (Om (1 + 1)))) e →
      Â ≤ e → e < Â + ζ → e - Â ∈ D ∧
        β + κ (e - Â) ∈ S.CSet (β + κ ζ) (S.psi (β + κ ζ) (Om (1 + 1))) := by
    intro ζ hζD hcnt e he h1 h2
    set t := S.psi (β + κ ζ) (Om (1 + 1)) with htdef
    set Tt := gxTh (upsilon l) (ldAtR S l) t with hTtdef
    have htSC : SC Tt :=
      gxTh_SC hZ hAt (SC_psi hκ2 _) (hZ1.trans (psiS_bounds (S := S) _ 1).1)
    have hTZ : Tt ≤ gxTh (upsilon l) (ldAtR S l) (Om (1 + 1)) := gxTh_mono (psi_lt hκ2 _).le
    have hTW : Tt ≤ W := le_min hTZ hcnt.le
    have hlt : e - Â < ζ := Ry.rySub_lt h1 h2
    have hltX : e - Â < Xb := hlt.trans hζD.2
    have hltθ : e - Â < ConjT.th S := hltX.trans_le hXθ
    have hm : e % ConjT.th S = e - Â := by
      have e1 : e = Â + (e - Â) := (Ordinal.add_sub_cancel_of_le h1).symm
      conv_lhs => rw [e1]
      rw [ldModK_add_lt hθSC Â hltθ, Ordinal.mod_eq_zero_of_dvd hdvd, zero_add]
    have hN : RxN S Tt (e - Â) := by
      rw [← hm]; exact rxN_of_HCl hcnt.le (ruHCl_modK hθSC he)
    have hET : RxE S Tt (e - Â) := hEθ hN hltθ
    refine ⟨⟨hET.mono hTW, hltX⟩, CSet.add_mem (hβn ζ hζD.1 hζD.2) ?_⟩
    obtain ⟨hLE, hKL, hxL⟩ := hL ζ hζD.1 hζD.2
    exact Wz.wzL_memL hZ hZ1 hAt htSC hTW hLE hKL (fun g hg' => CSet.of_lt (ruInv_spec hg').2.1) _ hET
      ⟨Lf ζ, le_rfl, CSet.of_lt (hxL _ hlt)⟩
  have hLift := rxLift hZ hZ1 hAt hβat hbase (D := D)
    (fun ζ hζ ζ' hζ' h => rxL_mono hZ hZ1 hAt hζ'.1 hζ.1 h)
    (fun ζ hζ => hat ζ hζ.1 hζ.2) (fun ζ hζ h0 => hpos ζ hζ.1 hζ.2 h0) hcl
  exact fun ζ hζ hζX => hLift ζ ⟨hζ, hζX⟩

end Main

end Googology.Trans.PoR.InaccPsi.R2.Xd

#print axioms Googology.Trans.PoR.InaccPsi.R2.Xd.xdLift
