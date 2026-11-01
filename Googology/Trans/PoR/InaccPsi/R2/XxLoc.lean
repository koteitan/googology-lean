import Googology.Trans.PoR.InaccPsi.R2.XxRS
import Googology.Trans.PoR.InaccPsi.R2.GsLoc

/-!
# XxLoc: THE FRONTIER OF EVERY CODE OF A READING SYSTEM OVER `Γ(k)` WITH GATE BELOW `K`

`Gs.GsLoc` for the reading systems `Xx.XxRS k` (readings below `Γ_{x+2+k}`, `k + 1 < ε₀`); the proofs are those of
`Gs.GsLoc` (the gated frontier lemma `Gs.gsB1_eq` is stated for every code system `Gs.GsCS`, so it is used as it is).
`k = 0` is `Gs.GsLoc` (`Xx.XxRS.ofGs`).

* `xxLX`, `xxX` (**the layer of the code `c`, patched below the gate**), `xxX_top`, `xxX_pkg`, `xxT_le`, `xxX_cl`,
  `xxX_poly`, `xxX_topth`, `xxX_topE`;
* `xxLoc` (**`Λ⁺(xxX c) = ι(Γ(c)·ω)`, `P(Γ(c)·ω) < L(0)` for every code with gate below `K`**), `xxFix`, `xxEnum`,
  `xxCapV`, `xxBlk` (BLK^O, exact reaches, ENUM-REACH and CapV below it).

No new axiom.  New definitions: `xxLX`, `xxX`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Xx

open Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq Googology.Trans.PoR.InaccPsi.R2.Gr
  Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Xk
open Googology.Trans.PoR.InaccPsi.R2.Gi
open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Lp Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Gd

variable {k : Ordinal.{0}} (RS : XxRS k)

theorem xxL_gU {c : Ordinal.{0}} (h : gfE ≤ c) (hc : c < RS.K.B) (S : InaccSeq.{0}) (hg : RS.K.gt c < Td.tdK S) :
    ∀ u, UpsPt u → (RS.gqL c h hc).g < u := fun u hu => by
  rw [RS.gqL_g]; exact hg.trans_le (gr_tdK_le_ups S hu)

/-- **The layer of the code `c`** (gate below `K = ψ_{Ω₁}(Ω_ω)`), patched below the gate. -/
noncomputable def xxLX (c : Ordinal.{0}) (h : gfE ≤ c) (hc : c < RS.K.B) (S : InaccSeq.{0})
    (hg : RS.K.gt c < Td.tdK S) : XtLay :=
  gqLayP (RS.gqL c h hc).K (xxL_gU RS h hc S hg)

/-- Its term system. -/
noncomputable def xxX (c : Ordinal.{0}) (h : gfE ≤ c) (hc : c < RS.K.B) (S : InaccSeq.{0})
    (hg : RS.K.gt c < Td.tdK S) : XtSys :=
  (xxLX RS c h hc S hg).sys

section Code

variable (c : Ordinal.{0}) (h : gfE ≤ c) (hc : c < RS.K.B) (S : InaccSeq.{0}) (hg : RS.K.gt c < Td.tdK S)
include h hc hg

theorem xx_gx {y : Ordinal.{0}} (hy : Td.tdK S ≤ y) : RS.K.gt c < y := hg.trans_le hy

theorem xxX_top {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hgx : RS.K.gt c < x) :
    (xxX RS c h hc S hg).top x = gq (RS.R c x) x := by
  have hgx' : (RS.gqL c h hc).g < x := by rw [RS.gqL_g]; exact hgx
  rw [show (xxX RS c h hc S hg).top x = (RS.gqL c h hc).K.sys.top x from gqSysP_top (hgU := xxL_gU RS h hc S hg) hgx']
  exact RS.gqL_top h hc hx hx1 hgx

theorem xxX_pkg : XtTopPkg (xxX RS c h hc S hg) := XtLay.topPkg (xxLX RS c h hc S hg)

theorem xxT_le : gcG c ≤ RS.K.V := (gcG_lt hc).le

theorem xxX_cl : ∀ Z, SC Z → Td.tdK S ≤ Z → GxCl Z (RS.K.At Z) (gcG c) := fun Z _ hKZ =>
  RS.gqL_atom hc (xx_gx RS c h hc S hg hKZ)

theorem xxX_poly : GsPoly RS.K (xxX RS c h hc S hg) (gcG c) (RS.K.gt c) := by
  intro Z d hd hdE
  have hgZ : (RS.gqL c h hc).g < max Z (RS.K.gt c + 1) := by
    rw [RS.gqL_g]; exact (lt_add_one _).trans_le (le_max_right _ _)
  obtain ⟨s, hs⟩ := (RS.gqL_codes S c h hc).2 (max Z (RS.K.gt c + 1)) d hgZ
    (gsmCl_mono (le_max_left _ _) hd) hdE
  refine ⟨.inl s, fun y hy hy1 hZy hgy => ?_⟩
  have hgy' : (RS.gqL c h hc).g < y := by rw [RS.gqL_g]; exact hgy
  obtain ⟨h1, h2⟩ := hs y hy hy1 (max_le hZy (Order.add_one_le_of_lt hgy))
  exact ⟨⟨hgy', h1⟩, h2⟩

theorem xxX_topth : ∀ y, SC y → y < Om 1 → Td.tdK S ≤ y →
    (xxX RS c h hc S hg).top y = gxTh y (RS.K.At y) (gcG c) := by
  intro y hy hy1 hKy
  have hyE := gg_SC_eps hy
  have hy1' := lp_y1 hy1
  have hgy := xx_gx RS c h hc S hg hKy
  rw [xxX_top RS c h hc S hg hyE hy1' hgy, ← RS.gqL_E h hc hyE hy1' hgy]
  exact (RS.gqL_codes S c h hc).1 y hy hy1 hgy

theorem xxX_topE : ∀ x, InE x → x < Om1 → eN x < (xxX RS c h hc S hg).top x := by
  intro x hx hx1
  by_cases hgx : RS.K.gt c < x
  · rw [xxX_top RS c h hc S hg hx hx1 hgx]
    obtain ⟨hT, h1⟩ := xx_T hx hx1 RS.W_lt (RS.R_lt0' hx hx1 hc hgx)
    exact gmq_eN_lt hx hx1 hT h1
  · have hgx' : ¬ (RS.gqL c h hc).g < x := by rw [RS.gqL_g]; exact hgx
    rw [show (xxX RS c h hc S hg).top x = vzSys.top x from gqSysP_top_low (hgU := xxL_gU RS h hc S hg) hgx']
    exact gg_eN_lt_B hx hx1

/-- **WHERE THE FRONTIER OF A CODE WITH GATE BELOW `K = ψ_{Ω₁}(Ω_ω)` LIES**: `Λ⁺(xxX c) = ι(Γ_{Ω₁+1+c}·ω)`, `ρ` of
it `= P(Γ_{Ω₁+1+c}·ω) < L(0)` (the gated frontier lemma `gsB1_eq`). -/
theorem xxLoc :
    xtB1 (xxX RS c h hc S hg) = iota S (gcG c * ω) ∧
    upsilon (xtB1 (xxX RS c h hc S hg)) = Pv S (gcG c * ω) ∧ Pv S (gcG c * ω) < Nc.ncL S 0 := by
  have h' := gsB1_eq (S := S) hg (xxT_le RS c h hc S hg) (xxX_poly RS c h hc S hg) (xxX_topth RS c h hc S hg)
    (xxX_cl RS c h hc S hg) (gcG_Om1_lt _).le (xxX_topE RS c h hc S hg) (xxX_pkg RS c h hc S hg)
  rwa [geG_E] at h'

/-- **`Θ_F(m_F) = O(F)` at every fixed range restart below `Λ⁺(xxX c)`** (THEOREM UNI). -/
theorem xxFix {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtB1 (xxX RS c h hc S hg))
    (hfix : upsilon l = l) : cdTheta S l (cdCode S l) = xtOrec (xxX RS c h hc S hg) l := by
  have hlt : l < iota S (ω ^ gcG c * ω) := by rw [geG_E, ← (xxLoc RS c h hc S hg).1]; exact hl
  exact gsUniTh hg (xxT_le RS c h hc S hg) (xxX_poly RS c h hc S hg) hr.1 hfix (cp_name_L hr.2.2.1)
    (phExp_le hr.1 hfix (cp_name_L hr.2.2.1) hlt)

theorem xxX_nonfix : XtNonfix (xtOrec (xxX RS c h hc S hg)) (xtB1 (xxX RS c h hc S hg)) :=
  fun _ hμ hww hfix hμB => xtNonfix hμ hww hfix (hμB.trans (xtB1_lt_Om1 (xxX_pkg RS c h hc S hg)))

/-- **ENUM-REACH at every range restart below `ι(Γ_{Ω₁+1+c}·ω)`, fixed points included.** -/
theorem xxEnum {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG c * ω)) :
    CdUpper S l ∧ CdLower S l := by
  rw [← (xxLoc RS c h hc S hg).1] at hl
  rcases (upsilon_normal.strictMono.le_apply : l ≤ upsilon l).lt_or_eq with hnf | hfx
  · exact xtInit (xtSpec1 (xxX_pkg RS c h hc S hg)) (xxX_nonfix RS c h hc S hg) hr hl hnf
  · exact (xtExact_iff (xtSpec1 (xxX_pkg RS c h hc S hg)) hr.1 hl).2 (xxFix RS c h hc S hg hr hl hfx.symm)

/-- **CapV at every range restart below `ι(Γ_{Ω₁+1+c}·ω)`, fixed points included.** -/
theorem xxCapV {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG c * ω)) : CdCapV S l := by
  have hl' := hl
  rw [← (xxLoc RS c h hc S hg).1] at hl'
  rcases (upsilon_normal.strictMono.le_apply : l ≤ upsilon l).lt_or_eq with hnf | hfx
  · have hww := cp_ww_lt_B0.trans_le hr.2.1
    exact xtCapV_nonfix (xtSpec1 (xxX_pkg RS c h hc S hg)) hr.1 hww hnf hl' (cp_name_L hr.2.2.1)
      (xxX_nonfix RS c h hc S hg l hr.1 hww hnf hl')
  · exact Lk.lkCapV_fix (xxX_pkg RS c h hc S hg) hr hl' hfx.symm (xxEnum RS c h hc S hg hr hl)

/-- **Theorem BLK^O below `υ_{Λ⁺(xxX c)}`**, with the exact reaches `lh(ρ_λ) = δ_λ + O(λ)`. -/
theorem xxBlk :
    (∀ c' d, c' < d → d < upsilon (xtB1 (xxX RS c h hc S hg)) → (le2 c' d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < xtB1 (xxX RS c h hc S hg) ∧
        c' = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < xtB1 (xxX RS c h hc S hg) →
      (∀ c' < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c' g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec (xxX RS c h hc S hg) l)) ∧
    (∀ α < upsilon (xtB1 (xxX RS c h hc S hg)), ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  xtBlk1 (xxX_pkg RS c h hc S hg)

end Code

theorem xxGood_mul {c : Ordinal.{0}} (hc : c < RS.K.B) (S : InaccSeq.{0}) (hgc : RS.K.gt c < Td.tdK S) :
    Bt.Good S (gcG c * ω) := by
  refine gs_good (K := RS.K) fun Z hZ hKZ => ?_
  have e : gcG c * ω = ω ^ (gcG c + 1) := by rw [opow_add, opow_one, geG_E]
  rw [e]
  exact GxCl.opow hZ.1 (GxCl.add (RS.gqL_atom hc (hgc.trans_le hKZ))
    (GxCl.small (gg_one_lt_of_SC hZ)))

end Googology.Trans.PoR.InaccPsi.R2.Xx
