import Googology.Trans.PoR.InaccPsi.R2.SjWalk

/-!
# The top laws of `Sg` with the closure condition of the atom argument in place of `SgOwnT`

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `Θ̂ = Sg.sgThH`, `T_E(b) = ψ_{Ω₂}(b + W^{X₀ + W^E})`.
The closure condition of `E` at `b`: `E` is a code `LeCl Ω₂ Q` for every strongly critical `Q ≥ T_E(b)`.

* `sjLevT_all` (**THE TOP LAW AT EVERY `1 ≤ E < ε_{Ω₂+1}` OF `H_λ` FROM THE CLOSURE CONDITION AT `b`**:
  `Θ(ψ_{Ω₂}(β + W^{X₀ + W^E})) = ψ_{Ω₁}(Â + Ω^{X̂₀ + Ω^{Θ̂ E}})` at every base `β ≥ b`; `Sg.sgLevT_all` with its
  hypothesis `hT` discharged by `Sj.sjOwnT`);
* `sjTop0` (**the reading of the atoms `Θ(ψ_{Ω₂}(β + Ω₂^{Ω₂^E})) = ψ_{Ω₁}(Â + Ω₁^{Ω₁^{Θ̂ E}})`** under the closure
  condition at `β`; `Sg.sgTop0` without `hT`);
* `sjSh_all` (**the shift `(X₀ + W^E, X̂₀ + Ω^{Θ̂ E})` is own relative to a proper base `b`**, `Rv.RvSh`, from the
  closure condition; `Sg.sgSh_all` without `SgOwn`), `sjSh_top` (the same with the top law at every code
  exponent, `Rv.rvTopE`: the hypothesis `hSh` of `Rw.rwDigMove` for one member).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Sj

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Sg

variable {S : InaccSeq.{0}}

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **THE TOP LAW AT EVERY `1 ≤ E < ε_{Ω₂+1}` of `H_λ` from the closure condition at `b`.** -/
theorem sjLevT_all {E : Ordinal.{0}} (hEH : E ∈ cdHull S l) (hE1 : 1 ≤ E) (hE : E < veblen 1 (Om (1 + 1) + 1))
    {b X0 Xh0 : Ordinal.{0}} (hoff : RvOff S l b X0 Xh0) (hd : leWe E ∣ X0)
    (hG3 : X0 + leWe E + Om (1 + 1) < S.psi 0 (Om (1 + 1 + 1)))
    (hG : Xh0 + leOe (sgThH S l E) + Om 1 < S.psi 0 (Om (1 + 1)))
    (hEcl : ∀ Q, SC Q → S.psi (b + leWe (X0 + leWe E)) (Om (1 + 1)) ≤ Q → LeCl (Om (1 + 1)) Q E) :
    RvTop S l b (X0 + leWe E) (Xh0 + leOe (sgThH S l E)) 0 := by
  refine sgLevT_all hl hX hEH hE1 hE hoff hd hG3 hG fun β hbβ hβ => ?_
  obtain ⟨-, -, -, -, hX0cl, -⟩ := rvOff_data (rvOff_mono hbβ hoff)
  obtain ⟨hβd, -, -, hβown, -⟩ := hβ
  rw [add_zero] at hβd hβown
  exact sjOwnT hl hX hβd hβown hX0cl (le_self_add.trans_lt hG3)
    (fun Q hQ hQ' => hEcl Q hQ ((psi_mono (S := S) (InR_Om_succ 1) (add_le_add_left hbβ _)).1.trans hQ'))
    hEH hE

/-- **The reading of the atoms `Θ(ψ_{Ω₂}(β + Ω₂^{Ω₂^E})) = ψ_{Ω₁}(Â + Ω₁^{Ω₁^{Θ̂ E}})`** under the closure
condition of `E` at `β`. -/
theorem sjTop0 {E : Ordinal.{0}} (hEH : E ∈ cdHull S l) (hE1 : 1 ≤ E) (hE : E < veblen 1 (Om (1 + 1) + 1))
    (hG3 : leWe E + Om (1 + 1) < S.psi 0 (Om (1 + 1 + 1)))
    (hG : leOe (sgThH S l E) + Om 1 < S.psi 0 (Om (1 + 1))) {β Â : Ordinal.{0}}
    (hb : RoBaseE S l (leWe E) 0 β) (hÂ : Â ∈ S.CSet Â (S.psi Â (Om 1)))
    (hbase : gxTh (upsilon l) (ldAtR S l) (S.psi β (Om (1 + 1))) = S.psi Â (Om 1))
    (hEcl : ∀ Q, SC Q → S.psi (β + leWe (leWe E)) (Om (1 + 1)) ≤ Q → LeCl (Om (1 + 1)) Q E) :
    gxTh (upsilon l) (ldAtR S l) (S.psi (β + leWe (leWe E)) (Om (1 + 1))) =
      S.psi (Â + leOe (leOe (sgThH S l E))) (Om 1) := by
  refine sgTop0 hl hX hEH hE1 hE hG3 hG hb hÂ hbase fun β' hββ' hb' => ?_
  obtain ⟨hβd, -, -, hβown, -⟩ := hb'
  rw [add_zero] at hβd hβown
  refine sjOwnT hl hX (X0 := 0) (by rwa [zero_add]) (fun d hd => hβown d (by rwa [zero_add] at hd))
    (fun Q hQ _ => LeCl.zero hQ.1) (by rw [zero_add]; exact le_self_add.trans_lt hG3) (fun Q hQ hQ' => ?_) hEH hE
  rw [zero_add] at hQ'
  exact hEcl Q hQ ((psi_mono (S := S) (InR_Om_succ 1) (add_le_add_left hββ' _)).1.trans hQ')

/-- **The shift `(X₀ + W^E, X̂₀ + Ω^{Θ̂ E})` is own relative to a proper base `b`** from the closure condition. -/
theorem sjSh_all {E : Ordinal.{0}} (hEH : E ∈ cdHull S l) (hE1 : 1 ≤ E) (hE : E < veblen 1 (Om (1 + 1) + 1))
    {b X0 Xh0 : Ordinal.{0}} (hoff : RvOff S l b X0 Xh0)
    (hG3 : X0 + leWe E + Om (1 + 1) < S.psi 0 (Om (1 + 1 + 1)))
    (hG : Xh0 + leOe (sgThH S l E) + Om 1 < S.psi 0 (Om (1 + 1)))
    (hbd : leWe (X0 + leWe E) ∣ b)
    (hbown : ∀ d, d ≤ leWe (X0 + leWe E) → b ∈ S.CSet (b + d) (S.psi (b + d) (Om (1 + 1))))
    (hEcl : ∀ Q, SC Q → S.psi (b + leWe (X0 + leWe E)) (Om (1 + 1)) ≤ Q → LeCl (Om (1 + 1)) Q E) :
    RvSh S l b (X0 + leWe E) (Xh0 + leOe (sgThH S l E)) := by
  obtain ⟨-, -, hX0m, -, hX0cl, -⟩ := rvOff_data hoff
  exact sgSh_all hl hX hEH hE1 hE hoff hG3 hG
    (sjOwn hl hX hbd hbown hX0cl (le_self_add.trans_lt hG3) hEcl hEH hE hX0m)

/-- **One member of the derived family satisfies the hypothesis `hSh` of `Rw.rwDigMove`**: `RvSh` and the top law
at every code exponent. -/
theorem sjSh_top {E : Ordinal.{0}} (hEH : E ∈ cdHull S l) (hE1 : 1 ≤ E) (hE : E < veblen 1 (Om (1 + 1) + 1))
    {b X0 Xh0 : Ordinal.{0}} (hoff : RvOff S l b X0 Xh0) (hd : leWe E ∣ X0)
    (hG3 : X0 + leWe E + Om (1 + 1) < S.psi 0 (Om (1 + 1 + 1)))
    (hG : Xh0 + leOe (sgThH S l E) + Om 1 < S.psi 0 (Om (1 + 1)))
    (hbd : leWe (X0 + leWe E) ∣ b)
    (hbown : ∀ d, d ≤ leWe (X0 + leWe E) → b ∈ S.CSet (b + d) (S.psi (b + d) (Om (1 + 1))))
    (hEcl : ∀ Q, SC Q → S.psi (b + leWe (X0 + leWe E)) (Om (1 + 1)) ≤ Q → LeCl (Om (1 + 1)) Q E) :
    RvSh S l b (X0 + leWe E) (Xh0 + leOe (sgThH S l E)) ∧
      ∀ e, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) →
        RvTop S l b (X0 + leWe E) (Xh0 + leOe (sgThH S l E)) e := by
  have hs := sjSh_all hl hX hEH hE1 hE hoff hG3 hG hbd hbown hEcl
  exact ⟨hs, rvTopE hs hl hX (sjLevT_all hl hX hEH hE1 hE hoff hd hG3 hG hEcl)⟩

end Main

end Googology.Trans.PoR.InaccPsi.R2.Sj
