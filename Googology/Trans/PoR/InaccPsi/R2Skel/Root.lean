import Googology.Trans.PoR.InaccPsi.R2Skel.SkF
import Googology.Trans.PoR.InaccPsi.R2Skel.SkR
import Googology.Trans.PoR.InaccPsi.R2Skel.SkE
import Googology.Trans.PoR.InaccPsi.R2Skel.SkS

/-!
# Root of the R₂^C skeleton (round 115)

`skNuC`: the conclusion of `Wd.wdRoadL` (ν_C = L(ω+1), reaches L(ω) and L(k+1) to L(ω+1), …) from the four
parts only:
- frontier `SkF.skFront` → hUH, hLH, hVH, hVt;
- reading `SkR.skWall`, `SkR.skThHi` → the hypothesis `hRead` of `SkE.skEQ`;
- `SkE.skEQ hRead` → hT, hF;
- supply `SkS.skSup` → h0, hn.

`sorry` enters only through the OPEN / SUSPECT leaves of the parts (see STATUS.md).
-/

set_option autoImplicit false

namespace R2Skel.Root

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2

/-- STATUS: REDUCED (SkF.skFrontU/L/V/Vt, SkR.skWall, SkR.skThHi, SkE.skEQ, SkS.skSup, Wd.wdRoadL)
SIZE: L
The root: the conclusion of `Wd.wdRoadL` for every `S`. -/
theorem skNuC (S : InaccSeq.{0}) :
    Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cd.CdCL S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S (k + 1)) (Nc.ncL S (ω + 1)) := by
  have hRead : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdAtWall S ∧ Wd.WdThHi S := fun hν =>
    ⟨Googology.Trans.PoR.InaccPsi.R2Skel.SkR.skWall S hν,
      Googology.Trans.PoR.InaccPsi.R2Skel.SkR.skThHi S hν⟩
  have hE := _root_.R2Skel.SkE.skEQ hRead
  have hS := _root_.R2Skel.SkS.skSup (S := S)
  exact Wd.wdRoadL (_root_.R2Skel.SkF.skFrontU S) (_root_.R2Skel.SkF.skFrontL S)
    (_root_.R2Skel.SkF.skFrontV S) (_root_.R2Skel.SkF.skFrontVt S) hE.1 hE.2 hS.1 hS.2

end R2Skel.Root
