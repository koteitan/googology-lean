import Googology.Trans.PoR.InaccPsi.R2.WbNoGo
import Googology.Trans.PoR.InaccPsi.R2.LwFix
import Googology.Trans.PoR.InaccPsi.R2.SfRst
import Googology.Trans.PoR.InaccPsi.R2.LdEQ

/-!
# The reading of `θ`: `Θ_λ(θ) ≤ ψ_{Ω₁}(A + θ)`, and `Θ_λ(θ) = ψ_{Ω₁}(A + θ)` from the lower half

`Θ = gxTh ρ_λ (ldAtR λ)`, `θ = ψ_{Ω₂}(Ω_ω)` (`ConjT.th`), `A_η = Ω_ω + θ·η` (`ConjT.Aη`).

* `wgOwnEta` (**an own `A` with `ψ_{Ω₁}(A) = ρ_λ` is `A_{η_λ}`, and `A_{η_λ}` is own**: `A_{η_λ} ≤ A < Λ`
  and the name is good, so `Sf.sfOwn` applies; then `Wb.wbA_unique`);
* `wgTheta_le` (**`Θ_λ(θ) ≤ ψ_{Ω₁}(A + θ)`** at every restart for every own `A` with `ψ_{Ω₁}(A) = ρ_λ`;
  sharpens `Wb.wbTheta_lt`, which has `A + θ + 1`);
* `wgThVal_of_low` (**`Θ_λ(θ) = ψ_{Ω₁}(A + θ)` ⇔ the lower half `ψ_{Ω₁}(A + θ) ≤ Θ_λ(θ)`**),
  `wgLow_of_all` (the lower half from `ψ_{Ω₁}(A + ζ) < Θ_λ(θ)` for every `ζ < θ`, by continuity of `ψ_{Ω₁}` at the
  limit `A + θ`, `Lw.lw_psi_limit`).

No new axiom.  The only new definition is the statement name `WgThLow` (the lower half).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Wg

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Cd
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Mx

variable {S : InaccSeq.{0}}

/-- The lower half of the reading of `θ` at a restart: `ψ_{Ω₁}(A_{η_λ} + θ) ≤ Θ_λ(θ)`. -/
def WgThLow (S : InaccSeq.{0}) (l : Ordinal.{0}) : Prop :=
  S.psi (ConjT.Aη S (cdEta S l) + ConjT.th S) (Om 1) ≤ gxTh (upsilon l) (ldAtR S l) (ConjT.th S)

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **An own `A` with `ψ_{Ω₁}(A) = ρ_λ` is `A_{η_λ}`, and `A_{η_λ}` is own.** -/
theorem wgOwnEta {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l) :
    ConjT.Aη S (cdEta S l) ∈ S.CSet (ConjT.Aη S (cdEta S l)) (S.psi (ConjT.Aη S (cdEta S l)) (Om 1)) ∧
      A = ConjT.Aη S (cdEta S l) := by
  obtain ⟨hg, -, -, hpv⟩ := cdEta_pv_spec (S := S) hl.1 hX
  have hpv' : S.psi (ConjT.Aη S (cdEta S l)) (Om 1) = upsilon l := hpv
  have hle : ConjT.Aη S (cdEta S l) ≤ A := by
    by_contra h
    push Not at h
    have hm : A ∈ S.CSet (ConjT.Aη S (cdEta S l)) (S.psi (ConjT.Aη S (cdEta S l)) (Om 1)) :=
      CSet_mono h.le (by rw [hρ, hpv']) hA
    have := psi_lt_psi_of_mem Low.InR_Om_one h hm
    rw [hρ, hpv'] at this
    exact lt_irrefl _ this
  have hown := Sf.sfOwn hg (hle.trans_lt (Sf.sfOwn_lt_Lam hA))
  exact ⟨hown, Wb.wbA_unique hl hX hown hA hρ⟩

/-- **`Θ_λ(θ) ≤ ψ_{Ω₁}(A + θ)`** for every own `A` with `ψ_{Ω₁}(A) = ρ_λ`. -/
theorem wgTheta_le {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l) :
    gxTh (upsilon l) (ldAtR S l) (ConjT.th S) ≤ S.psi (A + ConjT.th S) (Om 1) := by
  obtain ⟨hown, rfl⟩ := wgOwnEta hl hX hA hρ
  have hθ2 : ConjT.th S ≤ Om (1 + 1) := (psi_lt (InR_Om_succ 1) _).le
  rw [← ldTheta hl hX hθ2]
  exact ldTheta_le_psi hl hX hown _

/-- **`Θ_λ(θ) = ψ_{Ω₁}(A + θ)` from the lower half** (and conversely, `wgLow_of_val`). -/
theorem wgThVal_of_low {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)
    (hlow : WgThLow S l) :
    gxTh (upsilon l) (ldAtR S l) (ConjT.th S) = S.psi (A + ConjT.th S) (Om 1) := by
  refine le_antisymm (wgTheta_le hl hX hA hρ) ?_
  obtain ⟨-, rfl⟩ := wgOwnEta hl hX hA hρ
  exact hlow

omit hl hX in
/-- The value gives the lower half. -/
theorem wgLow_of_val
    (h : gxTh (upsilon l) (ldAtR S l) (ConjT.th S) = S.psi (ConjT.Aη S (cdEta S l) + ConjT.th S) (Om 1)) :
    WgThLow S l := h.symm.le

omit hl hX in
/-- **The lower half from the countable steps**: if `ψ_{Ω₁}(A + ζ) < Θ_λ(θ)` for every `ζ < θ`, then
`ψ_{Ω₁}(A + θ) ≤ Θ_λ(θ)` (continuity of `ψ_{Ω₁}` at the limit `A + θ`). -/
theorem wgLow_of_all
    (h : ∀ ζ, ζ < ConjT.th S →
      S.psi (ConjT.Aη S (cdEta S l) + ζ) (Om 1) < gxTh (upsilon l) (ldAtR S l) (ConjT.th S)) :
    WgThLow S l := by
  set A := ConjT.Aη S (cdEta S l) with hAdef
  have hθSC := ConjT.SC_th S
  have hlim : IsSuccLimit (A + ConjT.th S) := isSuccLimit_add _ hθSC.isSuccLimit
  unfold WgThLow
  rw [← hAdef, Lw.lw_psi_limit S Low.InR_Om_one hlim]
  refine ciSup_le' fun e => ?_
  rcases lt_or_ge e.1 A with h1 | h1
  · have h0 := h 0 hθSC.1
    rw [add_zero] at h0
    exact ((psi_mono (S := S) Low.InR_Om_one h1.le).1.trans_lt h0).le
  · have e1 : e.1 = A + (e.1 - A) := (Ordinal.add_sub_cancel_of_le h1).symm
    have hlt : e.1 - A < ConjT.th S := by
      have h2 := e.2
      change e.1 < A + ConjT.th S at h2
      rw [e1] at h2
      exact (add_lt_add_iff_left _).1 h2
    rw [e1]
    exact (h _ hlt).le

end Main

end Googology.Trans.PoR.InaccPsi.R2.Wg

#print axioms Googology.Trans.PoR.InaccPsi.R2.Wg.wgOwnEta
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wg.wgTheta_le
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wg.wgThVal_of_low
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wg.wgLow_of_all
