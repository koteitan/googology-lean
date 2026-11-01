import Googology.Trans.PoR.InaccPsi.R2Skel.SkF
import Googology.Trans.PoR.InaccPsi.R2Skel.SkR
import Googology.Trans.PoR.InaccPsi.R2Skel.SkE
import Googology.Trans.PoR.InaccPsi.R2Skel.SkS

/-!
# Root of the R₂^C skeleton (rounds 115–116)

`skNuC`: the conclusion of `Wf.wfRoad` / `Ww.wwRoad` (= that of `Wd.wdRoadL`; round 116: supply in the restricted form `WfVisGen`) (ν_C = L(ω+1), reaches L(ω) and L(k+1) to L(ω+1), …) from the four
parts only:
- frontier `SkF.skFront` → hUH, hLH, hVH, hVt;
- reading `SkR.skWall`, `SkR.skThHi` → the hypothesis `hRead` of `SkE.skEQ`;
- `SkE.skEQ hRead hUH hLH` → hT, hF (round 123: the EQ induction also uses ENUM-REACH, from `SkF.skFrontU/L`);
- supply `SkS.skSupX` → h0, hn, and `SkS.skShiftTh` → the shift (round 120: `Wf.wfRoad` is void, `Ww.wwRoad_false`;
  round 121: the bridge `Ww.WwRealB` of `Ww.wwRoad` is SUSPECT as stated, so the root applies `Xb.xbRoad`, which is
  `Ww.wwRoad` with `hB` replaced by `Xb.XbShift S` and the supply by `Xb.XbVisGen`;
  round 125: the root applies `Xo.xoRoadH`, the supply road with moving leaves: the bridge `SkS.skRealBXo`
  (`Xo.XoRealB`) and the supply `SkS.skSupXo` (`Xo.XoGen`, read with the repaired `Xo.XoR`)).

`sorry` enters only through the OPEN / SUSPECT leaves of the parts (see STATUS.md).
-/

set_option autoImplicit false

namespace R2Skel.Root

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2

/-- STATUS: REDUCED (SkF.skFrontU/L/V/Vt, SkR.skWall, SkR.skThHi, SkE.skEQ, SkS.skRealBXo, SkS.skSupXo, Xo.xoRoadH)
SIZE: L
The root: the conclusion of `Wf.wfRoad` (same as `Wd.wdRoadL`) for every `S`. -/
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
  have hE := _root_.R2Skel.SkE.skEQ hRead (_root_.R2Skel.SkF.skFrontU S) (_root_.R2Skel.SkF.skFrontL S)
  have hS := _root_.R2Skel.SkS.skSupXo (S := S)
  exact Xo.xoRoadH (_root_.R2Skel.SkF.skFrontU S) (_root_.R2Skel.SkF.skFrontL S)
    (_root_.R2Skel.SkF.skFrontV S) (_root_.R2Skel.SkF.skFrontVt S) hE.1 hE.2 (_root_.R2Skel.SkS.skRealBXo S) hS.1 hS.2

end R2Skel.Root
