import Googology.Trans.PoR.InaccPsi.R2.WdSplit

/-!
# The joined road with the reading-move / far-EQ split

`L(ξ) = Nc.ncL S ξ`, `F = ι(Γ(φ(Ω₁·Ω₁, G+1))·ω)` (the frontier of `Hl.hlU`), `hν := L(ω+1) ≤ ν_C`.

* `wdRoadL`: the conclusion of `Wa.waRoad` with `Cx.CxEQtop` replaced by `WdThLow` (the reading move at the long
  codes read below `δ_λ·ω`) and `WdEQfar` (EQ at the long codes read at or above `δ_λ·ω`), each asked only under
  `hν` (which `Sh.shNu` gives from the road hypotheses);
* `wdRoad`: the conclusion of `Wa.waRoadUx` with `UxAtMove26`, `RnThMoveM`, `RnEQhi2` replaced by `WdAtWall`,
  `WdThHi`, `WdEQfar` (each under `hν`);
* `wdRoad_hyps` / `wdRoadL_hyps` (**non-vacuity**): `WdThLow`, `WdThHi`, `WdEQfar` follow from the road's own
  conclusion `CdEQ` (with `hν`), and `WdAtWall` from `Ud.UdAtMove25`.

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Wd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2

variable {S : InaccSeq.{0}}

/-- `hν` from the road hypotheses above the frontier (`Hl.hlU` below it, then `Sh.shNu`). -/
theorem wdNu
    (hUH : ∀ l, Cd.CdRange S l → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → Cd.CdUpper S l)
    (hLH : ∀ l, Cd.CdRange S l → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → Cd.CdLower S l)
    (hVH : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → Cd.CdCapV S l)
    (hVt : ∀ l, Cd.CdRange S l → Nc.ncL S ω < upsilon l →
      Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → Cd.CdCapV S l) :
    Nc.ncL S (ω + 1) ≤ nuC := by
  let F : Ordinal.{0} := Bt.iota S (Gc.gcG Hl.hlU.B * ω)
  have hUR : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdUpper S l := by
    intro l hr _
    by_cases h : F ≤ l
    · exact hUH l hr h
    · exact (Hl.hlU_enum S hr (lt_of_not_ge h)).1
  have hLR : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdLower S l := by
    intro l hr _
    by_cases h : F ≤ l
    · exact hLH l hr h
    · exact (Hl.hlU_enum S hr (lt_of_not_ge h)).2
  have hVlow : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → Cd.CdCapV S l := by
    intro l hr hu _
    by_cases h : F ≤ l
    · exact hVH l hr hu h
    · exact Hl.hlU_capV S hr (lt_of_not_ge h)
  have hVhigh : ∀ l, Cd.CdRange S l → Nc.ncL S ω < upsilon l → Cd.CdCapV S l := by
    intro l hr hu
    by_cases h : F ≤ l
    · exact hVt l hr hu h
    · exact Hl.hlU_capV S hr (lt_of_not_ge h)
  exact Sh.shNu hUR hVlow hVhigh hLR

/-- **The road with `CxEQtop` replaced by `WdThLow` and `WdEQfar`.** -/
theorem wdRoadL
    (hUH : ∀ l, Cd.CdRange S l → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → Cd.CdUpper S l)
    (hLH : ∀ l, Cd.CdRange S l → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → Cd.CdLower S l)
    (hVH : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → Cd.CdCapV S l)
    (hVt : ∀ l, Cd.CdRange S l → Nc.ncL S ω < upsilon l →
      Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → Cd.CdCapV S l)
    (hT : Nc.ncL S (ω + 1) ≤ nuC → WdThLow S)
    (hF : Nc.ncL S (ω + 1) ≤ nuC → WdEQfar S)
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
  have hν := wdNu hUH hLH hVH hVt
  exact Wa.waRoad hUH hLH hVH hVt ((wdEQtop_iff hν).2 ⟨hT hν, hF hν⟩) h0 hn

/-- **The road with the wall statement `WdAtWall`, the reading move `WdThHi` and the far EQ `WdEQfar`.** -/
theorem wdRoad
    (hUH : ∀ l, Cd.CdRange S l → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → Cd.CdUpper S l)
    (hLH : ∀ l, Cd.CdRange S l → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → Cd.CdLower S l)
    (hVH : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → Cd.CdCapV S l)
    (hVt : ∀ l, Cd.CdRange S l → Nc.ncL S ω < upsilon l →
      Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → Cd.CdCapV S l)
    (hat : Nc.ncL S (ω + 1) ≤ nuC → WdAtWall S)
    (hT : Nc.ncL S (ω + 1) ≤ nuC → WdThHi S)
    (hF : Nc.ncL S (ω + 1) ≤ nuC → WdEQfar S)
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
      ∀ k : ℕ, IsReach R2C (Nc.ncL S (k + 1)) (Nc.ncL S (ω + 1)) :=
  Wa.waRoadUx hUH hLH hVH hVt (fun hν => wdAtMove26_of_wall (hat hν))
    (fun hν => (wdRn_of hν (hT hν) (hF hν)).1) (fun hν => (wdRn_of hν (hT hν) (hF hν)).2) h0 hn

/-- **Non-vacuity of `wdRoadL`**: its two new hypotheses follow from the road's own conclusion `CdEQ`. -/
theorem wdRoadL_hyps (hEQ : Cd.CdEQ S) :
    (Nc.ncL S (ω + 1) ≤ nuC → WdThLow S) ∧ (Nc.ncL S (ω + 1) ≤ nuC → WdEQfar S) :=
  ⟨fun hν => ((wdEQtop_iff hν).1 (Wa.waEQtop_of_EQ hEQ)).1,
    fun hν => ((wdEQtop_iff hν).1 (Wa.waEQtop_of_EQ hEQ)).2⟩

/-- **Non-vacuity of `wdRoad`**: `WdThHi`, `WdEQfar` follow from `CdEQ`, `WdAtWall` from `Ud.UdAtMove25`. -/
theorem wdRoad_hyps (hEQ : Cd.CdEQ S) (hat : Nc.ncL S (ω + 1) ≤ nuC → Ud.UdAtMove25 S) :
    (Nc.ncL S (ω + 1) ≤ nuC → WdAtWall S) ∧ (Nc.ncL S (ω + 1) ≤ nuC → WdThHi S) ∧
      (Nc.ncL S (ω + 1) ≤ nuC → WdEQfar S) := by
  have hlj : Nc.ncL S (ω + 1) ≤ nuC → Lj.LjEQhi S := fun hν =>
    wdLj_of_long ((Wa.waEQtop_iff hν).1 (Wa.waEQtop_of_EQ hEQ))
  exact ⟨fun hν => wdWall_iff.2 (Ux.uxAtMove26_of25 (hat hν)), fun hν => (wdHi_of_lj hν (hlj hν)).1,
    fun hν => (wdHi_of_lj hν (hlj hν)).2⟩

end Googology.Trans.PoR.InaccPsi.R2.Wd
