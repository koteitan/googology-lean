import Googology.Trans.PoR.InaccPsi.R2.YrRS
import Googology.Trans.PoR.InaccPsi.R2.XxLoc
import Googology.Trans.PoR.InaccPsi.R2.YcDirect

/-!
# YrLoc: THE FRONTIER OF EVERY CODE OF A READING SYSTEM WITH ADMISSIBLE READINGS, AND THE DIRECT ROUTE

`Xx.XxLoc` for the reading systems `Yr.YrRS` (readings admissible offsets, no constant bound); the proofs are those of
`Xx.XxLoc` (the gated frontier lemma `Gs.gsB1_eq` is stated for every code system).  Then the route (c) of
`Yc.YcDirect` with `Yr.YrRS` in place of `Xx.XxRS c`:

* `yrLX`, `yrX` (**the layer of the code `c`, patched below the gate**), `yrX_top`, `yrX_pkg`, `yrX_poly`,
  `yrX_topth`, `yrX_topE`, `yrLoc` (**`Λ⁺(yrX c) = ι(Γ(c)·ω)`, `P(Γ(c)·ω) < L(0)`**), `yrFix`, `yrEnum`, `yrCapV`;
* `YrDirect S B₀` (**codes cofinal below `B₀` in admissible reading systems, gates below `K`**), `yrUV_of_direct`
  (**UPPER ∧ LOWER ∧ CapV below `ι(Γ(B)·ω)`, `B < B₀`**), `yrDirect_of_yc` (`Yc.YcDirect S c B₀ ⇒ YrDirect S B₀`),
  `yrLay_of_direct` (**`YrDirect S Γ(c+1)` ⇒ the conclusions of `skLayLo` and `skLayHi` at `c`**).

No new axiom.  New definitions: `yrLX`, `yrX`, `YrDirect`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yr

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

variable (RS : YrRS)

theorem yrL_gU {c : Ordinal.{0}} (h : gfE ≤ c) (hc : c < RS.K.B) (S : InaccSeq.{0}) (hg : RS.K.gt c < Td.tdK S) :
    ∀ u, UpsPt u → (RS.gqL c h hc).g < u := fun u hu => by
  rw [RS.gqL_g]; exact hg.trans_le (gr_tdK_le_ups S hu)

/-- **The layer of the code `c`** (gate below `K = ψ_{Ω₁}(Ω_ω)`), patched below the gate. -/
noncomputable def yrLX (c : Ordinal.{0}) (h : gfE ≤ c) (hc : c < RS.K.B) (S : InaccSeq.{0})
    (hg : RS.K.gt c < Td.tdK S) : XtLay :=
  gqLayP (RS.gqL c h hc).K (yrL_gU RS h hc S hg)

/-- Its term system. -/
noncomputable def yrX (c : Ordinal.{0}) (h : gfE ≤ c) (hc : c < RS.K.B) (S : InaccSeq.{0})
    (hg : RS.K.gt c < Td.tdK S) : XtSys :=
  (yrLX RS c h hc S hg).sys

section Code

variable (c : Ordinal.{0}) (h : gfE ≤ c) (hc : c < RS.K.B) (S : InaccSeq.{0}) (hg : RS.K.gt c < Td.tdK S)
include h hc hg

theorem yr_gx {y : Ordinal.{0}} (hy : Td.tdK S ≤ y) : RS.K.gt c < y := hg.trans_le hy

theorem yrX_top {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hgx : RS.K.gt c < x) :
    (yrX RS c h hc S hg).top x = gq (RS.R c x) x := by
  have hgx' : (RS.gqL c h hc).g < x := by rw [RS.gqL_g]; exact hgx
  rw [show (yrX RS c h hc S hg).top x = (RS.gqL c h hc).K.sys.top x from gqSysP_top (hgU := yrL_gU RS h hc S hg) hgx']
  exact RS.gqL_top h hc hx hx1 hgx

theorem yrX_pkg : XtTopPkg (yrX RS c h hc S hg) := XtLay.topPkg (yrLX RS c h hc S hg)

theorem yrT_le : gcG c ≤ RS.K.V := (gcG_lt hc).le

theorem yrX_cl : ∀ Z, SC Z → Td.tdK S ≤ Z → GxCl Z (RS.K.At Z) (gcG c) := fun Z _ hKZ =>
  RS.gqL_atom hc (yr_gx RS c h hc S hg hKZ)

theorem yrX_poly : GsPoly RS.K (yrX RS c h hc S hg) (gcG c) (RS.K.gt c) := by
  intro Z d hd hdE
  have hgZ : (RS.gqL c h hc).g < max Z (RS.K.gt c + 1) := by
    rw [RS.gqL_g]; exact (lt_add_one _).trans_le (le_max_right _ _)
  obtain ⟨s, hs⟩ := (RS.gqL_codes S c h hc).2 (max Z (RS.K.gt c + 1)) d hgZ
    (gsmCl_mono (le_max_left _ _) hd) hdE
  refine ⟨.inl s, fun y hy hy1 hZy hgy => ?_⟩
  have hgy' : (RS.gqL c h hc).g < y := by rw [RS.gqL_g]; exact hgy
  obtain ⟨h1, h2⟩ := hs y hy hy1 (max_le hZy (Order.add_one_le_of_lt hgy))
  exact ⟨⟨hgy', h1⟩, h2⟩

theorem yrX_topth : ∀ y, SC y → y < Om 1 → Td.tdK S ≤ y →
    (yrX RS c h hc S hg).top y = gxTh y (RS.K.At y) (gcG c) := by
  intro y hy hy1 hKy
  have hyE := gg_SC_eps hy
  have hy1' := lp_y1 hy1
  have hgy := yr_gx RS c h hc S hg hKy
  rw [yrX_top RS c h hc S hg hyE hy1' hgy, ← RS.gqL_E h hc hyE hy1' hgy]
  exact (RS.gqL_codes S c h hc).1 y hy hy1 hgy

theorem yrX_topE : ∀ x, InE x → x < Om1 → eN x < (yrX RS c h hc S hg).top x := by
  intro x hx hx1
  by_cases hgx : RS.K.gt c < x
  · rw [yrX_top RS c h hc S hg hx hx1 hgx]
    obtain ⟨hT, h1⟩ := yr_T (RS.R_lt0' hx hx1 hc hgx)
    exact gmq_eN_lt hx hx1 hT h1
  · have hgx' : ¬ (RS.gqL c h hc).g < x := by rw [RS.gqL_g]; exact hgx
    rw [show (yrX RS c h hc S hg).top x = vzSys.top x from gqSysP_top_low (hgU := yrL_gU RS h hc S hg) hgx']
    exact gg_eN_lt_B hx hx1

/-- **WHERE THE FRONTIER OF A CODE WITH GATE BELOW `K = ψ_{Ω₁}(Ω_ω)` LIES**: `Λ⁺(yrX c) = ι(Γ_{Ω₁+1+c}·ω)`, `ρ` of
it `= P(Γ_{Ω₁+1+c}·ω) < L(0)` (the gated frontier lemma `gsB1_eq`). -/
theorem yrLoc :
    xtB1 (yrX RS c h hc S hg) = iota S (gcG c * ω) ∧
    upsilon (xtB1 (yrX RS c h hc S hg)) = Pv S (gcG c * ω) ∧ Pv S (gcG c * ω) < Nc.ncL S 0 := by
  have h' := gsB1_eq (S := S) hg (yrT_le RS c h hc S hg) (yrX_poly RS c h hc S hg) (yrX_topth RS c h hc S hg)
    (yrX_cl RS c h hc S hg) (gcG_Om1_lt _).le (yrX_topE RS c h hc S hg) (yrX_pkg RS c h hc S hg)
  rwa [geG_E] at h'

/-- **`Θ_F(m_F) = O(F)` at every fixed range restart below `Λ⁺(yrX c)`** (THEOREM UNI). -/
theorem yrFix {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtB1 (yrX RS c h hc S hg))
    (hfix : upsilon l = l) : cdTheta S l (cdCode S l) = xtOrec (yrX RS c h hc S hg) l := by
  have hlt : l < iota S (ω ^ gcG c * ω) := by rw [geG_E, ← (yrLoc RS c h hc S hg).1]; exact hl
  exact gsUniTh hg (yrT_le RS c h hc S hg) (yrX_poly RS c h hc S hg) hr.1 hfix (cp_name_L hr.2.2.1)
    (phExp_le hr.1 hfix (cp_name_L hr.2.2.1) hlt)

theorem yrX_nonfix : XtNonfix (xtOrec (yrX RS c h hc S hg)) (xtB1 (yrX RS c h hc S hg)) :=
  fun _ hμ hww hfix hμB => xtNonfix hμ hww hfix (hμB.trans (xtB1_lt_Om1 (yrX_pkg RS c h hc S hg)))

/-- **ENUM-REACH at every range restart below `ι(Γ_{Ω₁+1+c}·ω)`, fixed points included.** -/
theorem yrEnum {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG c * ω)) :
    CdUpper S l ∧ CdLower S l := by
  rw [← (yrLoc RS c h hc S hg).1] at hl
  rcases (upsilon_normal.strictMono.le_apply : l ≤ upsilon l).lt_or_eq with hnf | hfx
  · exact xtInit (xtSpec1 (yrX_pkg RS c h hc S hg)) (yrX_nonfix RS c h hc S hg) hr hl hnf
  · exact (xtExact_iff (xtSpec1 (yrX_pkg RS c h hc S hg)) hr.1 hl).2 (yrFix RS c h hc S hg hr hl hfx.symm)

/-- **CapV at every range restart below `ι(Γ_{Ω₁+1+c}·ω)`, fixed points included.** -/
theorem yrCapV {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG c * ω)) : CdCapV S l := by
  have hl' := hl
  rw [← (yrLoc RS c h hc S hg).1] at hl'
  rcases (upsilon_normal.strictMono.le_apply : l ≤ upsilon l).lt_or_eq with hnf | hfx
  · have hww := cp_ww_lt_B0.trans_le hr.2.1
    exact xtCapV_nonfix (xtSpec1 (yrX_pkg RS c h hc S hg)) hr.1 hww hnf hl' (cp_name_L hr.2.2.1)
      (yrX_nonfix RS c h hc S hg l hr.1 hww hnf hl')
  · exact Lk.lkCapV_fix (yrX_pkg RS c h hc S hg) hr hl' hfx.symm (yrEnum RS c h hc S hg hr hl)

/-- **Theorem BLK^O below `υ_{Λ⁺(yrX c)}`**, with the exact reaches `lh(ρ_λ) = δ_λ + O(λ)`. -/
theorem yrBlk :
    (∀ c' d, c' < d → d < upsilon (xtB1 (yrX RS c h hc S hg)) → (le2 c' d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < xtB1 (yrX RS c h hc S hg) ∧
        c' = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < xtB1 (yrX RS c h hc S hg) →
      (∀ c' < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c' g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec (yrX RS c h hc S hg) l)) ∧
    (∀ α < upsilon (xtB1 (yrX RS c h hc S hg)), ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  xtBlk1 (yrX_pkg RS c h hc S hg)

end Code

theorem yrGood_mul {c : Ordinal.{0}} (hc : c < RS.K.B) (S : InaccSeq.{0}) (hgc : RS.K.gt c < Td.tdK S) :
    Bt.Good S (gcG c * ω) := by
  refine gs_good (K := RS.K) fun Z hZ hKZ => ?_
  have e : gcG c * ω = ω ^ (gcG c + 1) := by rw [opow_add, opow_one, geG_E]
  rw [e]
  exact GxCl.opow hZ.1 (GxCl.add (RS.gqL_atom hc (hgc.trans_le hKZ))
    (GxCl.small (gg_one_lt_of_SC hZ)))

/-! ## The direct route with admissible reading systems -/

/-- **DIRECT READINGS BELOW `B₀`**: every `B < B₀` lies below a code `B' ≥ max(B, ε_{Ω₁+1})` of an admissible
reading system with gate below `K`. -/
def YrDirect (S : InaccSeq.{0}) (B₀ : Ordinal.{0}) : Prop :=
  ∀ B, B < B₀ → ∃ RS : YrRS, ∃ B', B ≤ B' ∧ gfE ≤ B' ∧ B' < RS.K.B ∧ RS.K.gt B' < Td.tdK S

/-- **UPPER ∧ LOWER ∧ CapV below `ι(Γ(B)·ω)` for every `B < B₀`** from direct readings below `B₀`. -/
theorem yrUV_of_direct {S : InaccSeq.{0}} {B₀ : Ordinal.{0}} (h : YrDirect S B₀) :
    ∀ l, Cd.CdRange S l → ∀ B, B < B₀ → l < Bt.iota S (gcG B * ω) →
      Cd.CdUpper S l ∧ Cd.CdLower S l ∧ Cd.CdCapV S l := by
  intro l hr B hB hl
  obtain ⟨RS, B', hBB, hE, hB', hg⟩ := h B hB
  have hl' : l < Bt.iota S (gcG B' * ω) :=
    hl.trans_le (Bt.iota_mono (S := S) _ _ (mul_le_mul_left (gcG_le hBB) ω))
  exact ⟨(yrEnum RS B' hE hB' S hg hr hl').1, (yrEnum RS B' hE hB' S hg hr hl').2, yrCapV RS B' hE hB' S hg hr hl'⟩

/-- **The old route is an instance**: `Yc.YcDirect S c B₀ ⇒ YrDirect S B₀`. -/
theorem yrDirect_of_yc {S : InaccSeq.{0}} {c B₀ : Ordinal.{0}} (h : Yc.YcDirect S c B₀) : YrDirect S B₀ := by
  intro B hB
  obtain ⟨RS, B', h1, h2, h3, h4⟩ := h B hB
  exact ⟨YrRS.ofXx RS, B', h1, h2, h3, h4⟩

/-- **THE WHOLE LAYER `c` FROM DIRECT READINGS BELOW `Γ(c+1)`**: the conclusions of `skLayLo` (levels `ℓ < Γ(c)`) and
of `skLayHi` (levels `Γ(c) ≤ ℓ < Γ(c+1)`) at `c`. -/
theorem yrLay_of_direct {S : InaccSeq.{0}} {c : Ordinal.{0}} (h : YrDirect S (gcG (c + 1))) :
    ∀ l, Cd.CdRange S l → (∃ ℓ, ℓ < gcG (c + 1) ∧ l < Bt.iota S (gcG (veblen ℓ (gcG c + 1)) * ω)) →
      Cd.CdUpper S l ∧ Cd.CdLower S l ∧ Cd.CdCapV S l := by
  rintro l hr ⟨ℓ, hℓ, hl⟩
  exact yrUV_of_direct h l hr _ (Yc.yc_veb_lt_next hℓ) hl

end Googology.Trans.PoR.InaccPsi.R2.Yr
