import Googology.Trans.PoR.InaccPsi.R2.ZbUni

/-!
# ZbLoc: WHERE THE FRONTIER OF A GATED LAYER WITH AN ABSTRACT TOP CODE LIES, AND UPPER ∧ LOWER ∧ CapV BELOW IT

For an atom system `A : Zb.ZbAS` and a gated layer `L : Gd.GdB` (gate below `K = ψ_{Ω₁}(Ω_ω)`) whose top reads a
top code `T` (`Ω₁ ≤ T ≤ V`, `T` a code over every strongly critical base `≥ K`) with the atoms of `A`, and which has
terms for every code below `T` (`ZbPolyG`): `Λ⁺ = ι(ω^T·ω)`, `P(ω^T·ω) < L(0)`, Theorem UNI at the fixed range
restarts, ENUM-REACH (fixed points included) and CapV below `ι(ω^T·ω)`.  The proofs are those of `Yr.YrLoc` with
`Yr.YrRS.gqL c` replaced by `L` and the atoms of `Gs.GsCS` by those of `A`.

* `ZbPolyG`, `zbLX`, `zbX`, `zbX_top`, `zbX_poly`, `zbX_topth`, `zbX_topE`;
* `zbLoc` (**`Λ⁺ = ι(ω^T·ω)`, `ρ` of it `= P(ω^T·ω) < L(0)`**), `zbFix` (THEOREM UNI), `zbEnum`, `zbCapV`, `zbUV`
  (**UPPER ∧ LOWER ∧ CapV at every range restart below `ι(ω^T·ω)`**).

No new axiom.  New definitions: `ZbPolyG`, `zbLX`, `zbX`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zb

open Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq Googology.Trans.PoR.InaccPsi.R2.Gr
  Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Xk
open Googology.Trans.PoR.InaccPsi.R2.Gi
open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Lp Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Gd Googology.Trans.PoR.InaccPsi.R2.Xx

/-- **Terms for the codes below `E` over the bases above the gate** (atoms of `A`). -/
def ZbPolyG (A : ZbAS) {g : Ordinal.{0}} (X : GdSys g) (E : Ordinal.{0}) : Prop :=
  ∀ Z c, g < Z → GxCl Z (A.At Z) c → c < E → ∃ s : X.Tm, ∀ y, SC y → y < Om 1 → Z ≤ y →
    X.CB s y ∧ X.val s y = gxTh y (A.At y) c

theorem ZbPolyG.mono {A : ZbAS} {g g' E : Ordinal.{0}} {X : GdSys g} (hP : ZbPolyG A X E) (h : g ≤ g') :
    ZbPolyG A (X.mono h) E := fun Z d hg hd hdE => hP Z d (h.trans_lt hg) hd hdE

theorem zbL_gU (L : GdB) (S : InaccSeq.{0}) (hg : L.g < Td.tdK S) : ∀ u, UpsPt u → L.g < u :=
  fun _ hu => hg.trans_le (gr_tdK_le_ups S hu)

/-- **The layer `L`**, patched below the gate. -/
noncomputable def zbLX (L : GdB) (S : InaccSeq.{0}) (hg : L.g < Td.tdK S) : XtLay := gqLayP L.K (zbL_gU L S hg)

/-- Its term system. -/
noncomputable def zbX (L : GdB) (S : InaccSeq.{0}) (hg : L.g < Td.tdK S) : XtSys := (zbLX L S hg).sys

theorem zbL_top (L : GdB) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hgx : L.g < x) : L.K.sys.top x = L.K.E x := by
  rw [L.K.top_eq x hx hx1 hgx]; exact L.ek x hx hx1 hgx

section Code

variable (A : ZbAS) (L : GdB) (S : InaccSeq.{0}) [Fact (A.Ok S)] (hg : L.g < Td.tdK S)
variable (T : Ordinal.{0}) (hT : T ≤ A.V)
  (htop : ∀ y, SC y → y < Om 1 → L.g < y → L.K.E y = gxTh y (A.At y) T)
  (hP : ZbPolyG A L.K.sys T) (hcl : ∀ Z, SC Z → Td.tdK S ≤ Z → GxCl Z (A.At Z) T)
  (htopE : ∀ x, InE x → x < Om1 → L.g < x → eN x < L.K.E x)

include hg in
theorem zbX_top {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hgx : L.g < x) :
    (zbX L S hg).top x = L.K.E x := by
  rw [show (zbX L S hg).top x = L.K.sys.top x from gqSysP_top (hgU := zbL_gU L S hg) hgx]
  exact zbL_top L hx hx1 hgx

include hg in
theorem zbX_pkg : XtTopPkg (zbX L S hg) := XtLay.topPkg (zbLX L S hg)

omit [Fact (A.Ok S)] in
include hP in
theorem zbX_poly : ZbPoly A (zbX L S hg) T L.g := by
  intro Z d hd hdE
  have hgZ : L.g < max Z (L.g + 1) := (lt_add_one _).trans_le (le_max_right _ _)
  obtain ⟨s, hs⟩ := hP (max Z (L.g + 1)) d hgZ (A.cl_mono (le_max_left _ _) hd) hdE
  refine ⟨.inl s, fun y hy hy1 hZy hgy => ?_⟩
  obtain ⟨h1, h2⟩ := hs y hy hy1 (max_le hZy (Order.add_one_le_of_lt hgy))
  exact ⟨⟨hgy, h1⟩, h2⟩

omit [Fact (A.Ok S)] in
include htop in
theorem zbX_topth : ∀ y, SC y → y < Om 1 → Td.tdK S ≤ y →
    (zbX L S hg).top y = gxTh y (A.At y) T := by
  intro y hy hy1 hKy
  have hyE := gg_SC_eps hy
  have hy1' := lp_y1 hy1
  have hgy : L.g < y := hg.trans_le hKy
  rw [zbX_top L S hg hyE hy1' hgy]
  exact htop y hy hy1 hgy

include htopE in
theorem zbX_topE : ∀ x, InE x → x < Om1 → eN x < (zbX L S hg).top x := by
  intro x hx hx1
  by_cases hgx : L.g < x
  · rw [zbX_top L S hg hx hx1 hgx]
    exact htopE x hx hx1 hgx
  · rw [show (zbX L S hg).top x = vzSys.top x from gqSysP_top_low (hgU := zbL_gU L S hg) hgx]
    exact gg_eN_lt_B hx hx1

include hg hT htop hP hcl htopE in
/-- **WHERE THE FRONTIER LIES**: `Λ⁺(zbX) = ι(ω^T·ω)`, `ρ` of it `= P(ω^T·ω) < L(0)`. -/
theorem zbLoc (hTO : Om 1 ≤ T) :
    xtB1 (zbX L S hg) = iota S (ω ^ T * ω) ∧
    upsilon (xtB1 (zbX L S hg)) = Pv S (ω ^ T * ω) ∧ Pv S (ω ^ T * ω) < Nc.ncL S 0 :=
  zbB1_eq (S := S) (A := A) hg hT (zbX_poly A L S hg T hP) (zbX_topth A L S hg T htop) hcl hTO
    (zbX_topE L S hg htopE) (zbX_pkg L S hg)

include hg hT htop hP hcl htopE in
/-- **`Θ_F(m_F) = O(F)` at every fixed range restart below `Λ⁺(zbX)`** (THEOREM UNI). -/
theorem zbFix (hTO : Om 1 ≤ T) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtB1 (zbX L S hg))
    (hfix : upsilon l = l) : cdTheta S l (cdCode S l) = xtOrec (zbX L S hg) l := by
  have hlt : l < iota S (ω ^ T * ω) := by rw [← (zbLoc A L S hg T hT htop hP hcl htopE hTO).1]; exact hl
  exact zbUniTh hg hT (zbX_poly A L S hg T hP) hr.1 hfix (cp_name_L hr.2.2.1)
    (phExp_le hr.1 hfix (cp_name_L hr.2.2.1) hlt)

include hg in
theorem zbX_nonfix : XtNonfix (xtOrec (zbX L S hg)) (xtB1 (zbX L S hg)) :=
  fun _ hμ hww hfix hμB => xtNonfix hμ hww hfix (hμB.trans (xtB1_lt_Om1 (zbX_pkg L S hg)))

include hg hT htop hP hcl htopE in
/-- **ENUM-REACH at every range restart below `ι(ω^T·ω)`, fixed points included.** -/
theorem zbEnum (hTO : Om 1 ≤ T) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (ω ^ T * ω)) :
    CdUpper S l ∧ CdLower S l := by
  rw [← (zbLoc A L S hg T hT htop hP hcl htopE hTO).1] at hl
  rcases (upsilon_normal.strictMono.le_apply : l ≤ upsilon l).lt_or_eq with hnf | hfx
  · exact xtInit (xtSpec1 (zbX_pkg L S hg)) (zbX_nonfix L S hg) hr hl hnf
  · exact (xtExact_iff (xtSpec1 (zbX_pkg L S hg)) hr.1 hl).2
      (zbFix A L S hg T hT htop hP hcl htopE hTO hr hl hfx.symm)

include hg hT htop hP hcl htopE in
/-- **CapV at every range restart below `ι(ω^T·ω)`, fixed points included.** -/
theorem zbCapV (hTO : Om 1 ≤ T) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (ω ^ T * ω)) :
    CdCapV S l := by
  have hl' := hl
  rw [← (zbLoc A L S hg T hT htop hP hcl htopE hTO).1] at hl'
  rcases (upsilon_normal.strictMono.le_apply : l ≤ upsilon l).lt_or_eq with hnf | hfx
  · have hww := cp_ww_lt_B0.trans_le hr.2.1
    exact xtCapV_nonfix (xtSpec1 (zbX_pkg L S hg)) hr.1 hww hnf hl' (cp_name_L hr.2.2.1)
      (zbX_nonfix L S hg l hr.1 hww hnf hl')
  · exact Lk.lkCapV_fix (zbX_pkg L S hg) hr hl' hfx.symm (zbEnum A L S hg T hT htop hP hcl htopE hTO hr hl)

include hg hT htop hP hcl htopE in
/-- **UPPER ∧ LOWER ∧ CapV at every range restart below `ι(ω^T·ω)`.** -/
theorem zbUV (hTO : Om 1 ≤ T) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (ω ^ T * ω)) :
    CdUpper S l ∧ CdLower S l ∧ CdCapV S l :=
  ⟨(zbEnum A L S hg T hT htop hP hcl htopE hTO hr hl).1, (zbEnum A L S hg T hT htop hP hcl htopE hTO hr hl).2,
    zbCapV A L S hg T hT htop hP hcl htopE hTO hr hl⟩

end Code

end Googology.Trans.PoR.InaccPsi.R2.Zb
