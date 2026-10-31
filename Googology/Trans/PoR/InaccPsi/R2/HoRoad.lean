import Googology.Trans.PoR.InaccPsi.R2.HoPU
import Googology.Trans.PoR.InaccPsi.R2.WaRoad

/-!
# HoRoad: THE ROAD `Wa.waRoad` WITH UPPER / LOWER / CapV ASKED ONLY ABOVE `ι(Γ(φ(Ω₁³, G+1))·ω)`

`hoWaRoad`: the conclusion of `Wa.waRoad` (`CdTC`, `CdEMB2`, `CdCL`, `CdC1`, `ν_C = L(ω+1)`, `L(ω) ≤ ν_C`,
`L(ω) <₂ L(ω+1)`, …) with the hypotheses `hUH`, `hLH`, `hVH`, `hVt` asked only at range restarts
`λ ≥ ι(Γ(φ(Ω₁³, G+1))·ω)` (below it they are `Ho.hoUf_enum`, `Ho.hoUf_capV`), and the other hypotheses of
`Wa.waRoad` (`CxEQtop`, `VrVisGen` at `m*` and every `L(n+1)`) unchanged.  `hoWaRoad_hyp_iff`: the four new hypotheses
are EQUIVALENT to the four of `Wa.waRoad` (NON-VACUITY relative to `Wa.waRoad`: the new road is no stronger).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ho

open Googology.Trans.PoR.InaccPsi.R2.Hn Googology.Trans.PoR.InaccPsi.R2.Hl
open Googology.Trans.PoR.InaccPsi.R2.Hj Googology.Trans.PoR.InaccPsi.R2.Hk
open Googology.Trans.PoR.InaccPsi.R2.Hi Googology.Trans.PoR.InaccPsi.R2.Hg
open Googology.Trans.PoR.InaccPsi.R2.Hf Googology.Trans.PoR.InaccPsi.R2.Hd Googology.Trans.PoR.InaccPsi.R2.He
open Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Hb
open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Lp Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Gd

variable {S : InaccSeq.{0}}

/-- **THE ROAD WITH UPPER / LOWER / CapV ONLY ABOVE `ι(Γ(φ(Ω₁³, G+1))·ω)`.** -/
theorem hoWaRoad
    (hUH : ∀ l, Cd.CdRange S l → Bt.iota S (Gc.gcG hoUf.B * ω) ≤ l → Cd.CdUpper S l)
    (hLH : ∀ l, Cd.CdRange S l → Bt.iota S (Gc.gcG hoUf.B * ω) ≤ l → Cd.CdLower S l)
    (hVH : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Bt.iota S (Gc.gcG hoUf.B * ω) ≤ l → Cd.CdCapV S l)
    (hVt : ∀ l, Cd.CdRange S l → Nc.ncL S ω < upsilon l →
      Bt.iota S (Gc.gcG hoUf.B * ω) ≤ l → Cd.CdCapV S l)
    (hEQtop : Cx.CxEQtop S)
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
  refine Wa.waRoad (fun l hr _ => ?_) (fun l hr _ => ?_) (fun l hr hu _ => ?_) (fun l hr hu _ => ?_) hEQtop h0 hn
  · rcases lt_or_ge l (Bt.iota S (Gc.gcG hoUf.B * ω)) with h | h
    · exact (hoUf_enum S hr h).1
    · exact hUH l hr h
  · rcases lt_or_ge l (Bt.iota S (Gc.gcG hoUf.B * ω)) with h | h
    · exact (hoUf_enum S hr h).2
    · exact hLH l hr h
  · rcases lt_or_ge l (Bt.iota S (Gc.gcG hoUf.B * ω)) with h | h
    · exact hoUf_capV S hr h
    · exact hVH l hr hu h
  · rcases lt_or_ge l (Bt.iota S (Gc.gcG hoUf.B * ω)) with h | h
    · exact hoUf_capV S hr h
    · exact hVt l hr hu h

/-- **NON-VACUITY (relative)**: the four hypotheses UPPER, LOWER, CapV (`υ_λ < L(ω)`), CapV (`L(ω) < υ_λ`) of
`hoWaRoad` are EQUIVALENT to those of `Wa.waRoad` (asked from `ι(Γ(φ(Ω₁·Ω₁, G+1))·ω)` on). -/
theorem hoWaRoad_hyp_iff (S : InaccSeq.{0}) :
    ((∀ l, Cd.CdRange S l → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → Cd.CdUpper S l) ↔
      (∀ l, Cd.CdRange S l → Bt.iota S (Gc.gcG hoUf.B * ω) ≤ l → Cd.CdUpper S l)) ∧
    ((∀ l, Cd.CdRange S l → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → Cd.CdLower S l) ↔
      (∀ l, Cd.CdRange S l → Bt.iota S (Gc.gcG hoUf.B * ω) ≤ l → Cd.CdLower S l)) ∧
    ((∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → Cd.CdCapV S l) ↔
      (∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Bt.iota S (Gc.gcG hoUf.B * ω) ≤ l → Cd.CdCapV S l)) ∧
    ((∀ l, Cd.CdRange S l → Nc.ncL S ω < upsilon l → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → Cd.CdCapV S l) ↔
      (∀ l, Cd.CdRange S l → Nc.ncL S ω < upsilon l → Bt.iota S (Gc.gcG hoUf.B * ω) ≤ l → Cd.CdCapV S l)) := by
  have hle : Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ Bt.iota S (Gc.gcG hoUf.B * ω) :=
    (hnU_fr_order S).2.1.trans (hoUf_fr_order S).2.1
  refine ⟨⟨fun h l hr hl => h l hr (hle.trans hl), fun h l hr hl => ?_⟩,
    ⟨fun h l hr hl => h l hr (hle.trans hl), fun h l hr hl => ?_⟩,
    ⟨fun h l hr hu hl => h l hr hu (hle.trans hl), fun h l hr hu hl => ?_⟩,
    ⟨fun h l hr hu hl => h l hr hu (hle.trans hl), fun h l hr hu hl => ?_⟩⟩
  · rcases lt_or_ge l (Bt.iota S (Gc.gcG hoUf.B * ω)) with h' | h'
    · exact (hoUf_enum S hr h').1
    · exact h l hr h'
  · rcases lt_or_ge l (Bt.iota S (Gc.gcG hoUf.B * ω)) with h' | h'
    · exact (hoUf_enum S hr h').2
    · exact h l hr h'
  · rcases lt_or_ge l (Bt.iota S (Gc.gcG hoUf.B * ω)) with h' | h'
    · exact hoUf_capV S hr h'
    · exact h l hr hu h'
  · rcases lt_or_ge l (Bt.iota S (Gc.gcG hoUf.B * ω)) with h' | h'
    · exact hoUf_capV S hr h'
    · exact h l hr hu h'

end Googology.Trans.PoR.InaccPsi.R2.Ho
