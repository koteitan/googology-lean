import Googology.Trans.PoR.InaccPsi.R2.HnPw
import Googology.Trans.PoR.InaccPsi.R2.VwRoad

/-!
# HnRoad: THE ROAD `Vw.vwRoad` WITH UPPER / LOWER / CapV ASKED ONLY ABOVE `ι(Γ(φ(Ω₁·Ω₁·2, G+1))·ω)`

`hnVwRoad`: the conclusion of `Vw.vwRoad` (`CdTC`, `CdEMB2`, `CdCL`, `CdC1`, `ν_C = L(ω+1)`, `L(ω) ≤ ν_C`,
`L(ω) <₂ L(ω+1)`, …) with the hypotheses `hU`, `hL`, `hV`, `hVt` asked only at range restarts
`λ ≥ ι(Γ(φ(Ω₁·Ω₁·2, G+1))·ω)` (below it they are `hnU_enum`, `hnU_capV`), and the other hypotheses of `Vw.vwRoad`
unchanged.  `hnVwRoad_hyp_iff`: the four new hypotheses are EQUIVALENT to the four of `Vw.vwRoad` (so the new road is
no stronger; NON-VACUITY relative to `Vw.vwRoad`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hn

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2

variable {S : InaccSeq.{0}}

/-- **THE ROAD WITH UPPER / LOWER / CapV ONLY ABOVE `ι(Γ(φ(Ω₁·Ω₁·2, G+1))·ω)`.** -/
theorem hnVwRoad
    (hUH : ∀ l, Cd.CdRange S l → Bt.iota S (Gc.gcG hnU.B * ω) ≤ l → Cd.CdUpper S l)
    (hLH : ∀ l, Cd.CdRange S l → Bt.iota S (Gc.gcG hnU.B * ω) ≤ l → Cd.CdLower S l)
    (hVH : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Bt.iota S (Gc.gcG hnU.B * ω) ≤ l → Cd.CdCapV S l)
    (hVt : ∀ l, Cd.CdRange S l → Nc.ncL S ω < upsilon l →
      Bt.iota S (Gc.gcG hnU.B * ω) ≤ l → Cd.CdCapV S l)
    (hEQtop : Cx.CxEQtop S) (htop : Cx.CxTCtopOff S) (hmove : Cx.CxStdMoveTop S)
    (h0 : ∀ l, IsRestartIdx l → Nc.ncL S 0 = upsilon l →
      Vr.VrVisGen S l (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Te.teW (Nc.ncL S 0))))
    (hn : ∀ n : ℕ, ∀ l, IsRestartIdx l → Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) = upsilon l →
      Vr.VrVisGen S l (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
        (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Te.teW (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))) :
    Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cd.CdCL S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S (k + 1)) (Nc.ncL S (ω + 1)) := by
  refine Vw.vwRoad (fun l hr _ => ?_) (fun l hr _ => ?_) (fun l hr hu _ => ?_) (fun l hr hu _ => ?_)
    hEQtop htop hmove h0 hn
  · rcases lt_or_ge l (Bt.iota S (Gc.gcG hnU.B * ω)) with h | h
    · exact (hnU_enum S hr h).1
    · exact hUH l hr h
  · rcases lt_or_ge l (Bt.iota S (Gc.gcG hnU.B * ω)) with h | h
    · exact (hnU_enum S hr h).2
    · exact hLH l hr h
  · rcases lt_or_ge l (Bt.iota S (Gc.gcG hnU.B * ω)) with h | h
    · exact hnU_capV S hr h
    · exact hVH l hr hu h
  · rcases lt_or_ge l (Bt.iota S (Gc.gcG hnU.B * ω)) with h | h
    · exact hnU_capV S hr h
    · exact hVt l hr hu h

/-- **NON-VACUITY (relative)**: the four hypotheses UPPER, LOWER, CapV (`υ_λ < L(ω)`), CapV (`L(ω) < υ_λ`) of
`hnVwRoad` are EQUIVALENT to those of `Vw.vwRoad`. -/
theorem hnVwRoad_hyp_iff (S : InaccSeq.{0}) :
    ((∀ l, Cd.CdRange S l → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → Cd.CdUpper S l) ↔
      (∀ l, Cd.CdRange S l → Bt.iota S (Gc.gcG hnU.B * ω) ≤ l → Cd.CdUpper S l)) ∧
    ((∀ l, Cd.CdRange S l → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → Cd.CdLower S l) ↔
      (∀ l, Cd.CdRange S l → Bt.iota S (Gc.gcG hnU.B * ω) ≤ l → Cd.CdLower S l)) ∧
    ((∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → Cd.CdCapV S l) ↔
      (∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Bt.iota S (Gc.gcG hnU.B * ω) ≤ l → Cd.CdCapV S l)) ∧
    ((∀ l, Cd.CdRange S l → Nc.ncL S ω < upsilon l → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → Cd.CdCapV S l) ↔
      (∀ l, Cd.CdRange S l → Nc.ncL S ω < upsilon l → Bt.iota S (Gc.gcG hnU.B * ω) ≤ l → Cd.CdCapV S l)) := by
  obtain ⟨h1, h2, h3⟩ := hnU_hyp_iff S
  have hle : Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ Bt.iota S (Gc.gcG hnU.B * ω) := (hnU_fr_order S).2.1
  refine ⟨h1, h2, h3, fun h l hr hu hl => h l hr hu (hle.trans hl), fun h l hr hu hl => ?_⟩
  rcases lt_or_ge l (Bt.iota S (Gc.gcG hnU.B * ω)) with h' | h'
  · exact hnU_capV S hr h'
  · exact h l hr hu h'

end Googology.Trans.PoR.InaccPsi.R2.Hn
