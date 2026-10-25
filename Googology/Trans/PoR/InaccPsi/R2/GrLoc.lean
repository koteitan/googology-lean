import Googology.Trans.PoR.InaccPsi.R2.GrUni

/-!
# THE LOCATION OF A CODE WITH GATE BELOW `K = ψ_{Ω₁}(Ω_ω)`

`Gq.GqRS.gqLoc` locates the codes of a reading system `RS : Gq.GqRS` whose gate is below `Γ₀`: the patched layer
(`Gq.gqLayP`) needs the gate below every `υ`-point, and the frontier lemma `Gm.gmB1_eq` needs the top code `Γ(c)` to
be a code over every strongly critical `Z` (only if the gate is below `Γ₀`).  With the gated frontier lemma
(`R2.GrUni`: demands only at the bases `≥ K`) and `K ≤` every `υ`-point (`gr_tdK_le_ups`), the same location holds for
every code with gate below `K`.

* `grL_gU`, `grLX`, `grX` (**the layer of the code `c`, patched below the gate**), `grX_top`, `grX_pkg`, `grT_le`,
  `grX_cl`, `grX_poly`, `grX_topth`, `grX_topE`;
* `grLoc` (**`Λ⁺(grX c) = ι(Γ(c)·ω)`, `P(Γ(c)·ω) < L(0)` for every code with gate below `K`**), `grFix`, `grEnum`,
  `grCapV`, `grBlk` (BLK^O, exact reaches, ENUM-REACH and CapV below it), `grGood_mul`.

No new axiom.  New definitions: `grLX`, `grX`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gr

open Googology.Trans.PoR.InaccPsi.R2.Gi Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Lp Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Gd

variable (RS : GqRS)

theorem grL_gU {c : Ordinal.{0}} (h : gfE ≤ c) (hc : c < RS.K.B) (S : InaccSeq.{0}) (hg : RS.K.gt c < Td.tdK S) :
    ∀ u, UpsPt u → (RS.gqL c h hc).g < u := fun u hu => by
  rw [RS.gqL_g]; exact hg.trans_le (gr_tdK_le_ups S hu)

/-- **The layer of the code `c`** (gate below `K = ψ_{Ω₁}(Ω_ω)`), patched below the gate. -/
noncomputable def grLX (c : Ordinal.{0}) (h : gfE ≤ c) (hc : c < RS.K.B) (S : InaccSeq.{0})
    (hg : RS.K.gt c < Td.tdK S) : XtLay :=
  gqLayP (RS.gqL c h hc).K (grL_gU RS h hc S hg)

/-- Its term system. -/
noncomputable def grX (c : Ordinal.{0}) (h : gfE ≤ c) (hc : c < RS.K.B) (S : InaccSeq.{0})
    (hg : RS.K.gt c < Td.tdK S) : XtSys :=
  (grLX RS c h hc S hg).sys

section Code

variable (c : Ordinal.{0}) (h : gfE ≤ c) (hc : c < RS.K.B) (S : InaccSeq.{0}) (hg : RS.K.gt c < Td.tdK S)
include h hc hg

theorem gr_gx {y : Ordinal.{0}} (hy : Td.tdK S ≤ y) : RS.K.gt c < y := hg.trans_le hy

theorem grX_top {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hgx : RS.K.gt c < x) :
    (grX RS c h hc S hg).top x = gq (RS.R c x) x := by
  have hgx' : (RS.gqL c h hc).g < x := by rw [RS.gqL_g]; exact hgx
  rw [show (grX RS c h hc S hg).top x = (RS.gqL c h hc).K.sys.top x from gqSysP_top (hgU := grL_gU RS h hc S hg) hgx']
  exact RS.gqL_top h hc hx hx1 hgx

theorem grX_pkg : XtTopPkg (grX RS c h hc S hg) := XtLay.topPkg (grLX RS c h hc S hg)

theorem grT_le : gcG c ≤ RS.K.V := (gcG_lt hc).le

theorem grX_cl : ∀ Z, SC Z → Td.tdK S ≤ Z → GxCl Z (RS.K.At Z) (gcG c) := fun Z _ hKZ =>
  RS.gqL_atom hc (gr_gx RS c h hc S hg hKZ)

theorem grX_poly : GrPoly RS.K (grX RS c h hc S hg) (gcG c) (RS.K.gt c) := by
  intro Z d hd hdE
  have hgZ : (RS.gqL c h hc).g < max Z (RS.K.gt c + 1) := by
    rw [RS.gqL_g]; exact (lt_add_one _).trans_le (le_max_right _ _)
  obtain ⟨s, hs⟩ := (RS.gqL_codes S c h hc).2 (max Z (RS.K.gt c + 1)) d hgZ
    (gmCl_mono (le_max_left _ _) hd) hdE
  refine ⟨.inl s, fun y hy hy1 hZy hgy => ?_⟩
  have hgy' : (RS.gqL c h hc).g < y := by rw [RS.gqL_g]; exact hgy
  obtain ⟨h1, h2⟩ := hs y hy hy1 (max_le hZy (Order.add_one_le_of_lt hgy))
  exact ⟨⟨hgy', h1⟩, h2⟩

theorem grX_topth : ∀ y, SC y → y < Om 1 → Td.tdK S ≤ y →
    (grX RS c h hc S hg).top y = gxTh y (RS.K.At y) (gcG c) := by
  intro y hy hy1 hKy
  have hyE := gg_SC_eps hy
  have hy1' := lp_y1 hy1
  have hgy := gr_gx RS c h hc S hg hKy
  rw [grX_top RS c h hc S hg hyE hy1' hgy, ← RS.gqL_E h hc hyE hy1' hgy]
  exact (RS.gqL_codes S c h hc).1 y hy hy1 hgy

theorem grX_topE : ∀ x, InE x → x < Om1 → eN x < (grX RS c h hc S hg).top x := by
  intro x hx hx1
  by_cases hgx : RS.K.gt c < x
  · rw [grX_top RS c h hc S hg hx hx1 hgx]
    obtain ⟨hT, h1⟩ := gm1_T hx hx1 (RS.R_lt0' hx hx1 hc hgx)
    exact gmq_eN_lt hx hx1 hT h1
  · have hgx' : ¬ (RS.gqL c h hc).g < x := by rw [RS.gqL_g]; exact hgx
    rw [show (grX RS c h hc S hg).top x = vzSys.top x from gqSysP_top_low (hgU := grL_gU RS h hc S hg) hgx']
    exact gg_eN_lt_B hx hx1

/-- **WHERE THE FRONTIER OF A CODE WITH GATE BELOW `K = ψ_{Ω₁}(Ω_ω)` LIES**: `Λ⁺(grX c) = ι(Γ_{Ω₁+1+c}·ω)`, `ρ` of
it `= P(Γ_{Ω₁+1+c}·ω) < L(0)` (the gated frontier lemma `grB1_eq`). -/
theorem grLoc :
    xtB1 (grX RS c h hc S hg) = iota S (gcG c * ω) ∧
    upsilon (xtB1 (grX RS c h hc S hg)) = Pv S (gcG c * ω) ∧ Pv S (gcG c * ω) < Nc.ncL S 0 := by
  have h' := grB1_eq (S := S) hg (grT_le RS c h hc S hg) (grX_poly RS c h hc S hg) (grX_topth RS c h hc S hg)
    (grX_cl RS c h hc S hg) (gcG_Om1_lt _).le (grX_topE RS c h hc S hg) (grX_pkg RS c h hc S hg)
  rwa [geG_E] at h'

/-- **`Θ_F(m_F) = O(F)` at every fixed range restart below `Λ⁺(grX c)`** (THEOREM UNI). -/
theorem grFix {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtB1 (grX RS c h hc S hg))
    (hfix : upsilon l = l) : cdTheta S l (cdCode S l) = xtOrec (grX RS c h hc S hg) l := by
  have hlt : l < iota S (ω ^ gcG c * ω) := by rw [geG_E, ← (grLoc RS c h hc S hg).1]; exact hl
  exact grUniTh hg (grT_le RS c h hc S hg) (grX_poly RS c h hc S hg) hr.1 hfix (cp_name_L hr.2.2.1)
    (phExp_le hr.1 hfix (cp_name_L hr.2.2.1) hlt)

theorem grX_nonfix : XtNonfix (xtOrec (grX RS c h hc S hg)) (xtB1 (grX RS c h hc S hg)) :=
  fun _ hμ hww hfix hμB => xtNonfix hμ hww hfix (hμB.trans (xtB1_lt_Om1 (grX_pkg RS c h hc S hg)))

/-- **ENUM-REACH at every range restart below `ι(Γ_{Ω₁+1+c}·ω)`, fixed points included.** -/
theorem grEnum {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG c * ω)) :
    CdUpper S l ∧ CdLower S l := by
  rw [← (grLoc RS c h hc S hg).1] at hl
  rcases (upsilon_normal.strictMono.le_apply : l ≤ upsilon l).lt_or_eq with hnf | hfx
  · exact xtInit (xtSpec1 (grX_pkg RS c h hc S hg)) (grX_nonfix RS c h hc S hg) hr hl hnf
  · exact (xtExact_iff (xtSpec1 (grX_pkg RS c h hc S hg)) hr.1 hl).2 (grFix RS c h hc S hg hr hl hfx.symm)

/-- **CapV at every range restart below `ι(Γ_{Ω₁+1+c}·ω)`, fixed points included.** -/
theorem grCapV {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG c * ω)) : CdCapV S l := by
  have hl' := hl
  rw [← (grLoc RS c h hc S hg).1] at hl'
  rcases (upsilon_normal.strictMono.le_apply : l ≤ upsilon l).lt_or_eq with hnf | hfx
  · have hww := cp_ww_lt_B0.trans_le hr.2.1
    exact xtCapV_nonfix (xtSpec1 (grX_pkg RS c h hc S hg)) hr.1 hww hnf hl' (cp_name_L hr.2.2.1)
      (grX_nonfix RS c h hc S hg l hr.1 hww hnf hl')
  · exact Lk.lkCapV_fix (grX_pkg RS c h hc S hg) hr hl' hfx.symm (grEnum RS c h hc S hg hr hl)

/-- **Theorem BLK^O below `υ_{Λ⁺(grX c)}`**, with the exact reaches `lh(ρ_λ) = δ_λ + O(λ)`. -/
theorem grBlk :
    (∀ c' d, c' < d → d < upsilon (xtB1 (grX RS c h hc S hg)) → (le2 c' d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < xtB1 (grX RS c h hc S hg) ∧
        c' = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < xtB1 (grX RS c h hc S hg) →
      (∀ c' < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c' g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec (grX RS c h hc S hg) l)) ∧
    (∀ α < upsilon (xtB1 (grX RS c h hc S hg)), ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  xtBlk1 (grX_pkg RS c h hc S hg)

end Code

theorem grGood_mul {c : Ordinal.{0}} (hc : c < RS.K.B) (S : InaccSeq.{0}) (hgc : RS.K.gt c < Td.tdK S) :
    Bt.Good S (gcG c * ω) := by
  refine gr_good (K := RS.K) fun Z hZ hKZ => ?_
  have e : gcG c * ω = ω ^ (gcG c + 1) := by rw [opow_add, opow_one, geG_E]
  rw [e]
  exact GxCl.opow hZ.1 (GxCl.add (RS.gqL_atom hc (hgc.trans_le hKZ))
    (GxCl.small (gg_one_lt_of_SC hZ)))

end Googology.Trans.PoR.InaccPsi.R2.Gr
