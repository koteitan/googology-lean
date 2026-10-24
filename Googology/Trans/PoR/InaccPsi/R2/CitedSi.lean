import Googology.Trans.PoR.InaccPsi.R2.CitedRk

set_option autoImplicit false

/-!
# `π` at the `ϑ₁`-terms `Ω₁·ω^b`, `b < ε_{Ω₁+1}` (no axiom: the cited fact now lives in `R2.Cited`)

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

Same conventions as `R2.CitedRj`, `R2.CitedRk` (`Ω₁ = Om1`, `Ω₂ = OmTwo`, `Tset τ = Tᵗ`, `Tᵗ[σ] = TB τ σ`,
`π_{σ,τ} = pi σ τ`, `Bases σ τ`: `σ < τ < Ω₁` are `ε`-numbers, `ε_{Ω₁+1} = Gg.ggE`).

`siOm1_opow_TB` was an axiom of this file ([W07a] Def 5.1 first and third clauses, Lemma 5.3 (b), Def 3.22, the
Remark after Cor 3.24, the remark after Def 3.1, Def 3.4 with Lemma 4.2 (`m = 1`), Def 3.28, Lemma 3.30 (`m = 1`)).
The same cited fact is now the axiom `R2.om1_opow_TB_all` of `R2.Cited`, with the bound `b < ε_{Ω₁+1}` written as
"`b` lies below every `ε`-number above `Ω₁`" (the literal texts and our steps are in its docstring); the former axiom
`R2.luOm1_opow_TB` (`b < σ`) is a theorem there.  Here `siOm1_opow_TB` is a theorem with its old statement
(`Gg.ggE_le`: `ε_{Ω₁+1}` is below every `ε`-number above `Ω₁`), so its users are unchanged.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal

/-- **[W07a] Def 5.1 (first and third clauses), …** (formerly an axiom; now from `R2.om1_opow_TB_all`): for bases
`σ < τ` and `b < ε_{Ω₁+1}`: `Ω₁·ω^b ∈ Tᵗ[σ]` iff `b ∈ Tᵗ[σ]`, and then `π_{σ,τ}(Ω₁·ω^b) = Ω₁·ω^{π_{σ,τ}(b)}`. -/
theorem siOm1_opow_TB {σ τ b : Ordinal.{0}} (h : Bases σ τ) (hbE : b < Gg.ggE) :
    (Om1 * ω ^ b ∈ TB τ σ ↔ b ∈ TB τ σ) ∧ (b ∈ TB τ σ → pi σ τ (Om1 * ω ^ b) = Om1 * ω ^ pi σ τ b) :=
  om1_opow_TB_all h fun e he he1 => hbE.trans_le (Gg.ggE_le he (by rw [← Rj.rj_Om1]; exact he1))

end Googology.Trans.PoR.InaccPsi.R2
