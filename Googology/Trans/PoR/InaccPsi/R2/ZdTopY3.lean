import Googology.Trans.PoR.InaccPsi.R2.ZdMove
import Googology.Trans.PoR.InaccPsi.R2.ZdY3Up

/-!
# THE ATOMS ABOVE THE TOP ATOMS OF EVERY SHIFT `X_ξ = Ω_{k+3} + Ω₂·ξ`, UP TO THE ψ₃-OFFSET `W^{Y₃+Ω₂}`

`t = β + W^{X_ξ+e}` (`ξ < ε₀`, `e` a code, `β ∈ D`, `Ro.RoBaseE λ X_ξ e β`), `Y₃ = ugY S`, "window", `A'`, "IH(s)"
as in `Zd.zdY3Up`.

* `zdTopMoveChainY3` (**EVERY ATOM `ψ₂(t) ≤ s < ψ₂(t + W^{Y₃+Ω₂})` MOVES** under IH(s): `t` is a base with a law at
  both ends (`Zd.zdTopBase` with the law `Zd.zdHL_chain`), `Ω₃ ∣ t`, `Ω₃ ∣ B_n t` (`Zd.zdBaseFacts`), and
  `Zd.zdPsi3OffW`); in particular the top atom `ψ₂(t)` itself moves (`Zd.zdTopMove`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Vk
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Yj Googology.Trans.PoR.InaccPsi.R2.Ug

variable {S : InaccSeq.{0}}

theorem zdOm3_le_X (k : ℕ) (ξ : Ordinal.{0}) : Om (1 + 1 + 1 : Ordinal.{0}) ≤ zdX k ξ :=
  (Yt.ytOm3_le_X k).trans le_self_add

section Win

variable {n : ℕ} {l l' A' : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
  (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l')
  (hA' : A' ∈ S.CSet A' (S.psi A' (Om 1))) (hρ' : S.psi A' (Om 1) = upsilon l')

include hR h1 hr hl' hB hA' hρ'

/-- **EVERY ATOM `ψ₂(t) ≤ s < ψ₂(t + W^{Y₃+Ω₂})` ABOVE EVERY TOP ATOM `t = β + W^{X_ξ+e}` MOVES** (`ξ < ε₀`). -/
theorem zdTopMoveChainY3 (k : ℕ) {ξ : Ordinal.{0}} (hξ : ξ < ε₀) {e β : Ordinal.{0}}
    (hec : GxCl (upsilon l) (ldAtR S l) e) (hβD : VbD S l β) (hbe : Ro.RoBaseE S l (zdX k ξ) e β)
    {s : Ordinal.{0}} (hs : s ∈ ldAtR S l)
    (hst : S.psi (β + leWe (zdX k ξ + e)) (Om (1 + 1)) ≤ s)
    (hsT : s < S.psi (β + leWe (zdX k ξ + e) + leWe (ugY S + Om (1 + 1))) (Om (1 + 1)))
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) := by
  set X := zdX k ξ with hXdef
  have hm : ZdMv S X := zdMv_chain k hξ
  have HL : ZdHL S X := zdHL_chain k hξ
  have IHt := fun x hx (hxs : x < S.psi (β + leWe (X + e)) (Om (1 + 1))) => IH x hx (hxs.trans_le hst)
  obtain ⟨hbt, hBt⟩ := zdTopBase hm hR h1 hr hl' hB HL hA' hρ' hec hβD hbe IHt
  obtain ⟨hdv', -⟩ := zdBaseFacts hm hR h1 hr hl' hB hec hβD hbe IHt
  have hW : ∀ e', Om (1 + 1 + 1) ∣ leWe (X + e') := fun e' => by
    have h := leWe_dvd ((zdOm3_le_X k ξ).trans (le_self_add : X ≤ X + e'))
    rwa [Vn.vnWe_Om3] at h
  have hd : Om (1 + 1 + 1) ∣ β + leWe (X + e) := dvd_add ((hW e).trans hbe.1) (hW e)
  have hd' : Om (1 + 1 + 1) ∣ Bc.bcB S n (β + leWe (X + e)) := by
    rw [hBt]; exact dvd_add ((hW _).trans hdv') (hW _)
  have h3 : Om (1 + 1 + 1) ≤ β + leWe (X + e) := by
    have hXle : X ≤ leWe (X + e) := (le_self_add : X ≤ X + e).trans
      ((Ordinal.le_mul_right _ ldOm2_SC.1).trans (Ordinal.right_le_opow _ one_lt_omega0))
    exact (zdOm3_le_X k ξ).trans (hXle.trans le_add_self)
  exact zdPsi3OffW hR h1 hr hl' hB hA' hρ' hbt hd hd' h3 hs hst hsT IH

end Win

end Googology.Trans.PoR.InaccPsi.R2.Zd
