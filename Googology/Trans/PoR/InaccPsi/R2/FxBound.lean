import Googology.Trans.PoR.InaccPsi.R2.FxRoad

/-!
# Where `Λ_B⁺ = cpB1` lies: below `ν_C`, and below `L(ω+1)` when `ν_C ≤ L(ω+1)`

`L(ξ) = P(Ω_ω + P′·ξ)` (`Nc.ncL`, `Lw.lw_L_eq`), `ν_C` the least non-standard `≤₂`-right end (`nuC`).

* `fxB1_lt_nuC` (**`cpB1 ≤ ρ_{cpB1} < ν_C`**, unconditional): the left end `ρ_L` of the first non-standard
  pair has `cpB1 ≤ L` (`Cp.cpNuC_bound`);
* `fxB1_lt_L` (**`ν_C ≤ L(ω+1)` gives `ρ_{cpB1} < L(ω+1)`**, so `cpB1 < L(ω+1)` and every restart below `cpB1`
  has `ρ_λ < L(ω+1)`); `fxB1_lt_L_PQ`: the same from (P) and (Q) at `(L(ω), L(ω+1))` (`Lw.lw_upper_L`);
* `fxCov_nu` (**the covered part of the range**, given `ν_C ≤ L(ω+1)`): every restart `λ ∈ [B₀, cpB1)` that is
  not a limit of fixed points of `υ` is in the range, with `Θ_λ(m_λ) = VzOrec(λ)`, UPPER, LOWER and the caps.

No new axiom, no new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Fx

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Br Googology.Trans.PoR.InaccPsi.R2.Bt
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp

variable {S : InaccSeq.{0}}

/-- **`cpB1 ≤ ρ_{cpB1} < ν_C`.** -/
theorem fxB1_lt_nuC : cpB1 ≤ upsilon cpB1 ∧ upsilon cpB1 < nuC := by
  obtain ⟨L, -, -, -, -, -, h1, h2, -, -⟩ := cpNuC_bound
  exact ⟨upsilon_normal.strictMono.le_apply, h1.trans_lt h2⟩

/-- **`ν_C ≤ L(ω+1)` gives `cpB1 ≤ ρ_{cpB1} < L(ω+1)`**, and `ρ_λ < L(ω+1)` for every `λ < cpB1`. -/
theorem fxB1_lt_L (hν : nuC ≤ Nc.ncL S (ω + 1)) :
    cpB1 < Nc.ncL S (ω + 1) ∧ upsilon cpB1 < Nc.ncL S (ω + 1) ∧
      ∀ l < cpB1, upsilon l < Nc.ncL S (ω + 1) := by
  obtain ⟨h1, h2⟩ := fxB1_lt_nuC
  have h3 : upsilon cpB1 < Nc.ncL S (ω + 1) := h2.trans_le hν
  exact ⟨h1.trans_lt h3, h3, fun l hl => (upsilon_normal.strictMono hl).trans h3⟩

/-- **The same from (P) and (Q) at `(L(ω), L(ω+1))`.** -/
theorem fxB1_lt_L_PQ (hP : Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)))
    (hQ : ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1)) :
    nuC ≤ Nc.ncL S (ω + 1) ∧ cpB1 < Nc.ncL S (ω + 1) ∧ upsilon cpB1 < Nc.ncL S (ω + 1) := by
  obtain ⟨-, η, hη, he⟩ := Lw.lw_upper_L S hP hQ
  have hν : nuC ≤ Nc.ncL S (ω + 1) := by
    rw [he, Lw.lw_L_eq S (ω + 1)]; exact Pv_mono hη
  obtain ⟨h1, h2, -⟩ := fxB1_lt_L hν
  exact ⟨hν, h1, h2⟩

/-- **The covered part of the range**, given `ν_C ≤ L(ω+1)`: a restart `λ ∈ [B₀, cpB1)` that is not a limit
of fixed points of `υ` is in the range, with `Θ_λ(m_λ) = VzOrec(λ)`, UPPER, LOWER and the caps. -/
theorem fxCov_nu (hν : nuC ≤ Nc.ncL S (ω + 1)) {l : Ordinal.{0}} (hl : IsRestartIdx l) (hB : cdB0 ≤ l)
    (hlB : l < cpB1) (hcov : ¬ (upsilon l = l ∧ ¬ CpIso l)) :
    CdRange S l ∧ cdTheta S l (cdCode S l) = VzOrec l ∧ CdUpper S l ∧ CdLower S l ∧ CdCapV S l ∧
      CdCapAt S l := by
  have hX : upsilon l < Nc.ncL S (ω + 1) := (fxB1_lt_L hν).2.2 l hlB
  have hr : CdRange S l := by
    rcases (upsilon_normal.strictMono.le_apply : l ≤ upsilon l).lt_or_eq with hfix | hfix
    · exact cpRange_nonfix hl hB hfix hX
    · have hiso : CpIso l := by
        by_contra h
        exact hcov ⟨hfix.symm, h⟩
      exact fxIso_range hl hB hfix.symm hiso hX
  exact ⟨hr, fxEnum_range hr hlB hcov⟩

end Googology.Trans.PoR.InaccPsi.R2.Fx
