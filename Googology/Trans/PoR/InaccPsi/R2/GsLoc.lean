import Googology.Trans.PoR.InaccPsi.R2.GsUni

/-!
# (port of `R2.GrLoc` to `R2.GsD` / `GsCS`: the base read only above the gate)

Every proof is that of `R2.GrLoc` with the names of `R2.GsmAt` … `R2.GsLoc` (code system `GsCS`).

`GsRS.gqLoc` locates the codes of a reading system `RS : GsRS` whose gate is below `Γ₀`: the patched layer
(`Gq.gqLayP`) needs the gate below every `υ`-point, and the frontier lemma `gsmB1_eq` needs the top code `Γ(c)` to
be a code over every strongly critical `Z` (only if the gate is below `Γ₀`).  With the gated frontier lemma
(`R2.GrUni`: demands only at the bases `≥ K`) and `K ≤` every `υ`-point (`gr_tdK_le_ups`), the same location holds for
every code with gate below `K`.

* `gsL_gU`, `gsLX`, `gsX` (**the layer of the code `c`, patched below the gate**), `gsX_top`, `gsX_pkg`, `gsT_le`,
  `gsX_cl`, `gsX_poly`, `gsX_topth`, `gsX_topE`;
* `gsLoc` (**`Λ⁺(gsX c) = ι(Γ(c)·ω)`, `P(Γ(c)·ω) < L(0)` for every code with gate below `K`**), `gsFix`, `gsEnum`,
  `gsCapV`, `gsBlk` (BLK^O, exact reaches, ENUM-REACH and CapV below it), `gsGood_mul`.

No new axiom.  New definitions: `gsLX`, `gsX`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gs

open Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq Googology.Trans.PoR.InaccPsi.R2.Gr

open Googology.Trans.PoR.InaccPsi.R2.Gi Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Lp Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Gd

variable (RS : GsRS)

theorem gsL_gU {c : Ordinal.{0}} (h : gfE ≤ c) (hc : c < RS.K.B) (S : InaccSeq.{0}) (hg : RS.K.gt c < Td.tdK S) :
    ∀ u, UpsPt u → (RS.gqL c h hc).g < u := fun u hu => by
  rw [RS.gqL_g]; exact hg.trans_le (gr_tdK_le_ups S hu)

/-- **The layer of the code `c`** (gate below `K = ψ_{Ω₁}(Ω_ω)`), patched below the gate. -/
noncomputable def gsLX (c : Ordinal.{0}) (h : gfE ≤ c) (hc : c < RS.K.B) (S : InaccSeq.{0})
    (hg : RS.K.gt c < Td.tdK S) : XtLay :=
  gqLayP (RS.gqL c h hc).K (gsL_gU RS h hc S hg)

/-- Its term system. -/
noncomputable def gsX (c : Ordinal.{0}) (h : gfE ≤ c) (hc : c < RS.K.B) (S : InaccSeq.{0})
    (hg : RS.K.gt c < Td.tdK S) : XtSys :=
  (gsLX RS c h hc S hg).sys

section Code

variable (c : Ordinal.{0}) (h : gfE ≤ c) (hc : c < RS.K.B) (S : InaccSeq.{0}) (hg : RS.K.gt c < Td.tdK S)
include h hc hg

theorem gs_gx {y : Ordinal.{0}} (hy : Td.tdK S ≤ y) : RS.K.gt c < y := hg.trans_le hy

theorem gsX_top {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hgx : RS.K.gt c < x) :
    (gsX RS c h hc S hg).top x = gq (RS.R c x) x := by
  have hgx' : (RS.gqL c h hc).g < x := by rw [RS.gqL_g]; exact hgx
  rw [show (gsX RS c h hc S hg).top x = (RS.gqL c h hc).K.sys.top x from gqSysP_top (hgU := gsL_gU RS h hc S hg) hgx']
  exact RS.gqL_top h hc hx hx1 hgx

theorem gsX_pkg : XtTopPkg (gsX RS c h hc S hg) := XtLay.topPkg (gsLX RS c h hc S hg)

theorem gsT_le : gcG c ≤ RS.K.V := (gcG_lt hc).le

theorem gsX_cl : ∀ Z, SC Z → Td.tdK S ≤ Z → GxCl Z (RS.K.At Z) (gcG c) := fun Z _ hKZ =>
  RS.gqL_atom hc (gs_gx RS c h hc S hg hKZ)

theorem gsX_poly : GsPoly RS.K (gsX RS c h hc S hg) (gcG c) (RS.K.gt c) := by
  intro Z d hd hdE
  have hgZ : (RS.gqL c h hc).g < max Z (RS.K.gt c + 1) := by
    rw [RS.gqL_g]; exact (lt_add_one _).trans_le (le_max_right _ _)
  obtain ⟨s, hs⟩ := (RS.gqL_codes S c h hc).2 (max Z (RS.K.gt c + 1)) d hgZ
    (gsmCl_mono (le_max_left _ _) hd) hdE
  refine ⟨.inl s, fun y hy hy1 hZy hgy => ?_⟩
  have hgy' : (RS.gqL c h hc).g < y := by rw [RS.gqL_g]; exact hgy
  obtain ⟨h1, h2⟩ := hs y hy hy1 (max_le hZy (Order.add_one_le_of_lt hgy))
  exact ⟨⟨hgy', h1⟩, h2⟩

theorem gsX_topth : ∀ y, SC y → y < Om 1 → Td.tdK S ≤ y →
    (gsX RS c h hc S hg).top y = gxTh y (RS.K.At y) (gcG c) := by
  intro y hy hy1 hKy
  have hyE := gg_SC_eps hy
  have hy1' := lp_y1 hy1
  have hgy := gs_gx RS c h hc S hg hKy
  rw [gsX_top RS c h hc S hg hyE hy1' hgy, ← RS.gqL_E h hc hyE hy1' hgy]
  exact (RS.gqL_codes S c h hc).1 y hy hy1 hgy

theorem gsX_topE : ∀ x, InE x → x < Om1 → eN x < (gsX RS c h hc S hg).top x := by
  intro x hx hx1
  by_cases hgx : RS.K.gt c < x
  · rw [gsX_top RS c h hc S hg hx hx1 hgx]
    obtain ⟨hT, h1⟩ := gm1_T hx hx1 (RS.R_lt0' hx hx1 hc hgx)
    exact gmq_eN_lt hx hx1 hT h1
  · have hgx' : ¬ (RS.gqL c h hc).g < x := by rw [RS.gqL_g]; exact hgx
    rw [show (gsX RS c h hc S hg).top x = vzSys.top x from gqSysP_top_low (hgU := gsL_gU RS h hc S hg) hgx']
    exact gg_eN_lt_B hx hx1

/-- **WHERE THE FRONTIER OF A CODE WITH GATE BELOW `K = ψ_{Ω₁}(Ω_ω)` LIES**: `Λ⁺(gsX c) = ι(Γ_{Ω₁+1+c}·ω)`, `ρ` of
it `= P(Γ_{Ω₁+1+c}·ω) < L(0)` (the gated frontier lemma `gsB1_eq`). -/
theorem gsLoc :
    xtB1 (gsX RS c h hc S hg) = iota S (gcG c * ω) ∧
    upsilon (xtB1 (gsX RS c h hc S hg)) = Pv S (gcG c * ω) ∧ Pv S (gcG c * ω) < Nc.ncL S 0 := by
  have h' := gsB1_eq (S := S) hg (gsT_le RS c h hc S hg) (gsX_poly RS c h hc S hg) (gsX_topth RS c h hc S hg)
    (gsX_cl RS c h hc S hg) (gcG_Om1_lt _).le (gsX_topE RS c h hc S hg) (gsX_pkg RS c h hc S hg)
  rwa [geG_E] at h'

/-- **`Θ_F(m_F) = O(F)` at every fixed range restart below `Λ⁺(gsX c)`** (THEOREM UNI). -/
theorem gsFix {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtB1 (gsX RS c h hc S hg))
    (hfix : upsilon l = l) : cdTheta S l (cdCode S l) = xtOrec (gsX RS c h hc S hg) l := by
  have hlt : l < iota S (ω ^ gcG c * ω) := by rw [geG_E, ← (gsLoc RS c h hc S hg).1]; exact hl
  exact gsUniTh hg (gsT_le RS c h hc S hg) (gsX_poly RS c h hc S hg) hr.1 hfix (cp_name_L hr.2.2.1)
    (phExp_le hr.1 hfix (cp_name_L hr.2.2.1) hlt)

theorem gsX_nonfix : XtNonfix (xtOrec (gsX RS c h hc S hg)) (xtB1 (gsX RS c h hc S hg)) :=
  fun _ hμ hww hfix hμB => xtNonfix hμ hww hfix (hμB.trans (xtB1_lt_Om1 (gsX_pkg RS c h hc S hg)))

/-- **ENUM-REACH at every range restart below `ι(Γ_{Ω₁+1+c}·ω)`, fixed points included.** -/
theorem gsEnum {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG c * ω)) :
    CdUpper S l ∧ CdLower S l := by
  rw [← (gsLoc RS c h hc S hg).1] at hl
  rcases (upsilon_normal.strictMono.le_apply : l ≤ upsilon l).lt_or_eq with hnf | hfx
  · exact xtInit (xtSpec1 (gsX_pkg RS c h hc S hg)) (gsX_nonfix RS c h hc S hg) hr hl hnf
  · exact (xtExact_iff (xtSpec1 (gsX_pkg RS c h hc S hg)) hr.1 hl).2 (gsFix RS c h hc S hg hr hl hfx.symm)

/-- **CapV at every range restart below `ι(Γ_{Ω₁+1+c}·ω)`, fixed points included.** -/
theorem gsCapV {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG c * ω)) : CdCapV S l := by
  have hl' := hl
  rw [← (gsLoc RS c h hc S hg).1] at hl'
  rcases (upsilon_normal.strictMono.le_apply : l ≤ upsilon l).lt_or_eq with hnf | hfx
  · have hww := cp_ww_lt_B0.trans_le hr.2.1
    exact xtCapV_nonfix (xtSpec1 (gsX_pkg RS c h hc S hg)) hr.1 hww hnf hl' (cp_name_L hr.2.2.1)
      (gsX_nonfix RS c h hc S hg l hr.1 hww hnf hl')
  · exact Lk.lkCapV_fix (gsX_pkg RS c h hc S hg) hr hl' hfx.symm (gsEnum RS c h hc S hg hr hl)

/-- **Theorem BLK^O below `υ_{Λ⁺(gsX c)}`**, with the exact reaches `lh(ρ_λ) = δ_λ + O(λ)`. -/
theorem gsBlk :
    (∀ c' d, c' < d → d < upsilon (xtB1 (gsX RS c h hc S hg)) → (le2 c' d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < xtB1 (gsX RS c h hc S hg) ∧
        c' = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < xtB1 (gsX RS c h hc S hg) →
      (∀ c' < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c' g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec (gsX RS c h hc S hg) l)) ∧
    (∀ α < upsilon (xtB1 (gsX RS c h hc S hg)), ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  xtBlk1 (gsX_pkg RS c h hc S hg)

end Code

theorem gsGood_mul {c : Ordinal.{0}} (hc : c < RS.K.B) (S : InaccSeq.{0}) (hgc : RS.K.gt c < Td.tdK S) :
    Bt.Good S (gcG c * ω) := by
  refine gs_good (K := RS.K) fun Z hZ hKZ => ?_
  have e : gcG c * ω = ω ^ (gcG c + 1) := by rw [opow_add, opow_one, geG_E]
  rw [e]
  exact GxCl.opow hZ.1 (GxCl.add (RS.gqL_atom hc (hgc.trans_le hKZ))
    (GxCl.small (gg_one_lt_of_SC hZ)))

end Googology.Trans.PoR.InaccPsi.R2.Gs
