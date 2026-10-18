import Googology.Trans.PoR.InaccPsi.R2.GgInst

/-!
# The roads with the notation hypothesis asked only at the fixed points with `e(η_λ) > ε_{Ω₁+1}`

THEOREM UNI (`Gg.ggVz`, `Gg.ggLL`, `Gg.ggLyE`) gives `Θ_λ(m_λ) = O(λ)` at every fixed point `λ = υ_λ` of the
range with `e(η_λ) ≤ ggE = ε_{Ω₁+1}` (fixed points of `GG` included).  So:

* `ggRoad3` (**`Nn.nnRoad3` with its notation hypothesis asked only at the fixed points `λ < cpB1` of the range with
  `GG(λ) = λ` and `e(η_λ) > ε_{Ω₁+1}`**);
* `ggW2Road3` (**`Nn.nnW2Road3` with the notation hypothesis asked only there, below `Λ⁺_k`**);
* `ggLyERoad3` (**`Ly.lyERoad3` with the notation hypothesis asked only at the fixed points `λ < Λ⁺(lyEB)` with
  `e(η_λ) > ε_{Ω₁+1}`**);
* `ggEnum_cp`, `ggEnum_W2`, `ggEnum_lyE` (**ENUM-REACH, both halves, at every restart of the range below `cpB1`,
  `Λ_{ω²}`, resp. `Λ⁺(lyEB)`, except at the fixed points `λ = υ_λ` with `e(η_λ) > ε_{Ω₁+1}`**).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Gg

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd
  Googology.Trans.PoR.InaccPsi.R2.Cp Googology.Trans.PoR.InaccPsi.R2.Xt

variable {S : InaccSeq.{0}}

/-- **`Nn.nnRoad3` with the notation hypothesis asked only at the fixed points `λ < cpB1` of the range with
`GG(λ) = λ` and `e(η_λ) > ε_{Ω₁+1}`.** -/
theorem ggRoad3 (hU : CpUPPERhigh S) (hL : CpLOWERhigh S)
    (hT : ∀ l, CdRange S l → l < cpB1 → upsilon l = l → GG l = l → ggE < cdExp (cdEta S l) →
      cdTheta S l (cdCode S l) = VzOrec l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → CpOut2 l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  Nn.nnRoad3 hU hL (fun l hr hlB hfix hG => by
    rcases le_or_gt (cdExp (cdEta S l)) ggE with h | h
    · exact ggVz hr.1 hfix (cp_name_L hr.2.2.1) h
    · exact hT l hr hlB hfix hG h) hV hC hEQ hrest hB2

/-- **`Nn.nnW2Road3` with the notation hypothesis asked only at the fixed points of `GG` with
`e(η_λ) > ε_{Ω₁+1}`.** -/
theorem ggW2Road3 (hU : ∀ l, CdRange S l → xtFamW2.famSup ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → xtFamW2.famSup ≤ l → CdLower S l)
    (hT : ∀ k : ℕ, ∀ l, CdRange S l → l < xtFamW2.bd k → upsilon l = l → GG l = l →
      ggE < cdExp (cdEta S l) → cdTheta S l (cdCode S l) = xtFamW2.off k l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut xtFamW2.famSup l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  Nn.nnW2Road3 hU hL (fun k l hr hlk hfix hG => by
    rcases le_or_gt (cdExp (cdEta S l)) ggE with h | h
    · exact ggLL k hr.1 hfix (cp_name_L hr.2.2.1) h
    · exact hT k l hr hlk hfix hG h) hV hC hEQ hrest hB2

/-- **`Ly.lyERoad3` with the notation hypothesis asked only at the fixed points `λ < Λ⁺(lyEB)` with
`e(η_λ) > ε_{Ω₁+1}`.** -/
theorem ggLyERoad3 (hU : ∀ l, CdRange S l → xtB1 Ly.lyEB ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → xtB1 Ly.lyEB ≤ l → CdLower S l)
    (hT : ∀ l, CdRange S l → l < xtB1 Ly.lyEB → upsilon l = l → ggE < cdExp (cdEta S l) →
      cdTheta S l (cdCode S l) = xtOrec Ly.lyEB l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut (xtB1 Ly.lyEB) l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  Ly.lyERoad3 hU hL (fun l hr hlB hfix => by
    rcases le_or_gt (cdExp (cdEta S l)) ggE with h | h
    · exact ggLyE hr.1 hfix (cp_name_L hr.2.2.1) h
    · exact hT l hr hlB hfix h) hV hC hEQ hrest hB2

/-- **ENUM-REACH below `cpB1`** at every restart of the range except the fixed points with `e(η_λ) > ε_{Ω₁+1}`. -/
theorem ggEnum_cp {l : Ordinal.{0}} (hr : CdRange S l) (hlB : l < cpB1)
    (hl : ¬ (upsilon l = l ∧ ggE < cdExp (cdEta S l))) : CdUpper S l ∧ CdLower S l := by
  by_cases hfix : upsilon l = l
  · exact (cpExact_iff hr.1 hlB).2
      (ggVz hr.1 hfix (cp_name_L hr.2.2.1) (not_lt.1 fun h => hl ⟨hfix, h⟩))
  · exact ⟨(Fx.fxEnum_range hr hlB fun h => hfix h.1).2.1, (Fx.fxEnum_range hr hlB fun h => hfix h.1).2.2.1⟩

/-- **ENUM-REACH below `Λ_{ω²}`** at every restart of the range except the fixed points with
`e(η_λ) > ε_{Ω₁+1}`. -/
theorem ggEnum_W2 {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtFamW2.famSup)
    (hn : ¬ (upsilon l = l ∧ ggE < cdExp (cdEta S l))) : CdUpper S l ∧ CdLower S l := by
  rcases (upsilon_normal.strictMono.le_apply : l ≤ upsilon l).lt_or_eq with hnf | hfx
  · exact xtW2_init hr hl hnf
  · have hfix : upsilon l = l := hfx.symm
    obtain ⟨k, hk⟩ := xtFamW2.famLt hl
    exact (xtExact_iff (xtFamW2.spec k) hr.1 hk).2
      (ggLL k hr.1 hfix (cp_name_L hr.2.2.1) (not_lt.1 fun h => hn ⟨hfix, h⟩))

/-- **ENUM-REACH below `Λ⁺(lyEB)`** at every restart of the range except the fixed points with
`e(η_λ) > ε_{Ω₁+1}`. -/
theorem ggEnum_lyE {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtB1 Ly.lyEB)
    (hn : ¬ (upsilon l = l ∧ ggE < cdExp (cdEta S l))) : CdUpper S l ∧ CdLower S l := by
  rcases (upsilon_normal.strictMono.le_apply : l ≤ upsilon l).lt_or_eq with hnf | hfx
  · exact Ly.lyE_init hr hl hnf
  · have hfix : upsilon l = l := hfx.symm
    exact (Ly.lyE_iff hr.1 hl).2
      (ggLyE hr.1 hfix (cp_name_L hr.2.2.1) (not_lt.1 fun h => hn ⟨hfix, h⟩))

end Googology.Trans.PoR.InaccPsi.R2.Gg
