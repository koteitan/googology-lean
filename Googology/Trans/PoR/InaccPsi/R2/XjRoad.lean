import Googology.Trans.PoR.InaccPsi.R2.XfFr
import Googology.Trans.PoR.InaccPsi.R2.XjShift

/-!
# The road `Xf.xfRoad` without the shift hypothesis

`Xf.xfRoad` / `Xf.xfRoadZ` ask `hS : Xb.XbShift S`.  It is now a theorem (`Xj.xbShift_holds`), so the roads
`xjRoad` / `xjRoadZ` keep only UPPER / LOWER / CapV past `F_G` (`hUH`, `hLH`, `hVH`, `hVt`), the reading and far-EQ
pieces under `L(ω+1) ≤ ν_C` (`hT`, `hF`) and the supply `Xb.XbVisGen` at `m*` and every `L(n+1)` (`h0`, `hn`).
`xjRoad_iff`: the hypotheses of `xjRoad` are exactly those of `Xf.xfRoad` with `hS` dropped (so
`xjRoad` is non-vacuous whenever `Xf.xfRoad` is; it asks strictly less).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Xj

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Xf

variable {S : InaccSeq.{0}}

/-- **THE ROAD `Xf.xfRoad` WITHOUT `Xb.XbShift`** (now `Xj.xbShift_holds`). -/
theorem xjRoad
    (hUH : ∀ l, CdRange S l → XfPast S l → CdUpper S l)
    (hLH : ∀ l, CdRange S l → XfPast S l → CdLower S l)
    (hVH : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XfPast S l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → XfPast S l → CdCapV S l)
    (hT : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdThLow S)
    (hF : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdEQfar S)
    (h0 : ∀ l, IsRestartIdx l → Nc.ncL S 0 = upsilon l →
      Xb.XbVisGen S l (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Te.teW (Nc.ncL S 0))))
    (hn : ∀ n : ℕ, ∀ l, IsRestartIdx l → Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) = upsilon l →
      Xb.XbVisGen S l (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
        (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Te.teW (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))) :
    CdTC S ∧ CdEMB2 S ∧ CdCL S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S (k + 1)) (Nc.ncL S (ω + 1)) :=
  xfRoad hUH hLH hVH hVt hT hF xbShift_holds h0 hn

/-- **The conclusion of `Xf.xfRoadZ` without `Xb.XbShift`.** -/
theorem xjRoadZ
    (hUH : ∀ l, CdRange S l → XfPast S l → CdUpper S l)
    (hLH : ∀ l, CdRange S l → XfPast S l → CdLower S l)
    (hVH : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XfPast S l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → XfPast S l → CdCapV S l)
    (hT : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdThLow S)
    (hF : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdEQfar S)
    (h0 : ∀ l, IsRestartIdx l → Nc.ncL S 0 = upsilon l →
      Xb.XbVisGen S l (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Te.teW (Nc.ncL S 0))))
    (hn : ∀ n : ℕ, ∀ l, IsRestartIdx l → Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) = upsilon l →
      Xb.XbVisGen S l (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
        (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Te.teW (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S (k + 1)) (Nc.ncL S (ω + 1)) :=
  xfRoadZ hUH hLH hVH hVt hT hF xbShift_holds h0 hn

/-- **NON-VACUITY (relative)**: `xjRoad`'s hypothesis set is that of `Xf.xfRoad` minus `hS`; the dropped hypothesis is
a theorem, so the two hypothesis sets are equivalent (`hS` adds nothing). -/
theorem xjRoad_iff : Xb.XbShift S ↔ True := ⟨fun _ => trivial, fun _ => xbShift_holds⟩

end Googology.Trans.PoR.InaccPsi.R2.Xj
