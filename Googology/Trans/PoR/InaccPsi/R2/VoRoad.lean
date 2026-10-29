import Googology.Trans.PoR.InaccPsi.R2.VoTerm

/-!
# The long statements from the visible statements, and the vacuity of the decomposition road

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.

* `voLong_of_vis` (**the visible statements `Tk.TkVisI` at `m*` and every `L(n+1)` give (CL), `m* ≤₁ L(1)`,
  `∀ k, L(k) ≤₁ ν_C` and `Tk.TkSucc` at every `L(k)`**; `Tk.tkLong_iff_vis`, `Te.teLong_iff_nu`,
  `Tk.tkSucc_iff_nu`), `voVis_of_long` (the converse);
* `voVisI_of_gd` (the visible statement at `L(k)` from `Vl.VlGdTyVis`), `voLong_of_gd` (**the three from the
  hypotheses `h0`, `hn` of `Vl.vlGdTyRoad`**), `voGd_false` (**those hypotheses are inconsistent with the section
  hypotheses of the road**, `Vo.voNoGo_road`: so `voLong_of_gd` is vacuous; `voLong_of_vis` is not).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Vo

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Tk Googology.Trans.PoR.InaccPsi.R2.Vl

variable {S : InaccSeq.{0}}

section Road

variable (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
  (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
  (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
  (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
  (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
  (hEQ : Cx.CxEQtop S) (htop : Cx.CxTCtopOff S) (hmove : Cx.CxStdMoveTop S)
include hU hO hL hV hVt hEQ htop hmove

/-- **(F) from the visible statements**: `Tk.TkVisI` at `m*` and at every `L(n+1)` give (CL), `m* ≤₁ L(1)`,
`L(k) ≤₁ ν_C` for every `k`, and the block statements `Tk.TkSucc` at every `L(k)`. -/
theorem voLong_of_vis
    (h0 : TkVisI S (Nc.ncL S 0) (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Te.teW (Nc.ncL S 0))))
    (hn : ∀ n : ℕ, TkVisI S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
      (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Te.teW (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))) :
    (CdCL S ∧ le1 (Nc.ncL S 0) (Nc.ncL S 1)) ∧ (∀ k : ℕ, le1 (Nc.ncL S (k : Ordinal.{0})) nuC) ∧
      ∀ k : ℕ, TkSucc S (Nc.ncL S (k : Ordinal.{0})) (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}))
        (upsilon (Nc.ncL S (k : Ordinal.{0}) + Te.teW (Nc.ncL S (k : Ordinal.{0})))) := by
  have hlong := (tkLong_iff_vis hU hV hVt hL).2 ⟨h0, hn⟩
  have hnu := (Te.teLong_iff_nu hU hO hL hV hVt hEQ htop hmove).1 hlong
  exact ⟨hlong, hnu, (tkSucc_iff_nu hU hO hL hV hVt hEQ htop hmove).2 hnu⟩

/-- **The converse**: `L(k) ≤₁ ν_C` for every `k` gives the visible statements at `m*` and every `L(n+1)`. -/
theorem voVis_of_long (h : ∀ k : ℕ, le1 (Nc.ncL S (k : Ordinal.{0})) nuC) :
    TkVisI S (Nc.ncL S 0) (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Te.teW (Nc.ncL S 0))) ∧
      ∀ n : ℕ, TkVisI S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
        (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Te.teW (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})))) :=
  (tkVis_iff_nu hU hO hL hV hVt hEQ htop hmove).2 h

end Road

/-- **The visible statement at `L(k)` from `Vl.VlGdTyVis`** (the route of `Vl.vlRoadGen`: `Vl.vlTyVis_of_gd`,
`Vl.vlTyVis_gen`, `Vl.vlVisI_of_gen`). -/
theorem voVisI_of_gd (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l) {k : ℕ} {w : Ordinal.{0}} (hw : Ty.TyWin S k w)
    (h : VlGdTyVis S (Nc.ncL S (k : Ordinal.{0})) (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}))
      (upsilon (Nc.ncL S (k : Ordinal.{0}) + Te.teW (Nc.ncL S (k : Ordinal.{0})))) w) :
    TkVisI S (Nc.ncL S (k : Ordinal.{0})) (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}))
      (upsilon (Nc.ncL S (k : Ordinal.{0}) + Te.teW (Nc.ncL S (k : Ordinal.{0})))) := by
  have hν := Sh.shNu hU hV hVt hL
  have hstd : Cx.CxStdPairTop S := Tp.tpStdPairTop hν
  have hLW : CdLOWER S := Rz.rzLOWER_of_rest hL
  have hl := Te.teRst_L (S := S) k
  have hla : upsilon (Nc.ncL S (k : Ordinal.{0})) = Nc.ncL S (k : Ordinal.{0}) := Te.teUps_L k
  have hb : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ Nc.ncL S (ω + 1) := by
    rcases k with _ | n
    · simpa using ((Pp.ppL_lt_omega 0).trans (Qq.qqL_lt_succ S)).le
    · exact ((Pp.ppL_lt_omega (n + 1)).trans (Qq.qqL_lt_succ S)).le
  have hvis := vlTyVis_gen hU hL hw hla le_rfl (vlTyVis_of_gd hl h)
  have := vlVisI_of_gen hLW hl (hb.trans hν) hb hstd hvis
  rwa [hla] at this

/-- **(F) from the hypotheses of `Vl.vlGdTyRoad`** (vacuous by `voGd_false`). -/
theorem voLong_of_gd (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hEQ : Cx.CxEQtop S) (htop : Cx.CxTCtopOff S) (hmove : Cx.CxStdMoveTop S)
    (h0 : ∀ l, IsRestartIdx l → Nc.ncL S 0 = upsilon l →
      VlGdTyVis S l (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Te.teW (Nc.ncL S 0))) (upsilon Rz.rzLam))
    (hn : ∀ n : ℕ, ∀ l, IsRestartIdx l → Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) = upsilon l →
      VlGdTyVis S l (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
        (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Te.teW (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))
        (Nc.ncL S (n : Ordinal.{0}))) :
    (CdCL S ∧ le1 (Nc.ncL S 0) (Nc.ncL S 1)) ∧ (∀ k : ℕ, le1 (Nc.ncL S (k : Ordinal.{0})) nuC) ∧
      ∀ k : ℕ, TkSucc S (Nc.ncL S (k : Ordinal.{0})) (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}))
        (upsilon (Nc.ncL S (k : Ordinal.{0}) + Te.teW (Nc.ncL S (k : Ordinal.{0})))) := by
  refine voLong_of_vis hU hO hL hV hVt hEQ htop hmove ?_ fun n => ?_
  · have h := h0 _ (by simpa using Te.teRst_L (S := S) 0) (by simpa using (Te.teUps_L (S := S) 0).symm)
    have h' : VlGdTyVis S (Nc.ncL S ((0 : ℕ) : Ordinal.{0})) (Nc.ncL S ((0 + 1 : ℕ) : Ordinal.{0}))
        (upsilon (Nc.ncL S ((0 : ℕ) : Ordinal.{0}) + Te.teW (Nc.ncL S ((0 : ℕ) : Ordinal.{0}))))
        (upsilon Rz.rzLam) := by simpa using h
    simpa using voVisI_of_gd hU hV hVt hL Ty.tyWin_M h'
  · exact voVisI_of_gd hU hV hVt hL (Ty.tyWin_L n)
      (hn n _ (Te.teRst_L (n + 1)) (Te.teUps_L (n + 1)).symm)

/-- **The hypotheses of `Vl.vlGdTyRoad` are inconsistent with its section hypotheses `hU, hV, hVt, hL`.** -/
theorem voGd_false (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hn : ∀ n : ℕ, ∀ l, IsRestartIdx l → Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) = upsilon l →
      VlGdTyVis S l (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
        (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Te.teW (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))
        (Nc.ncL S (n : Ordinal.{0}))) : False :=
  (voNoGo_road hU hV hVt hL).2 0 (hn 0)

end Googology.Trans.PoR.InaccPsi.R2.Vo
