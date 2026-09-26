/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/NonTopMain.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.NonTopBound
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.StepInnerCleanRoot
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.LowerChainMain

set_option backward.do.legacy false

/-!
# The nodes that are not top copies: `StartRelNT`, `StartRootNT`, and `NonTopStep` over `Setting`

`LowerChain.lean` leaves three statements about the copied nodes that are not the top copy of
their origin in their column: `NonTopStep`, `StartRelNT`, `StartRootNT`.

## Every node that is not a top copy is a clean copy below a gap copy

* `clean_of_not_isTopAt`, `clean_of_not_topNode`: a non-cut copy that is not the top copy of its
  origin is a clean copy (`b = 0`). By `emitsT_order` (proved, `ChainCorrStepInner.lean`) two
  emits of a column with the same origin are copies of the root row; an upper copy keeps the row
  of its origin, and a plain copy has an origin below `τ`.
* `clean_row_kept`: a clean copy keeps the row of its origin (`SRCmp.rootCmp`).

## The statements

* **`startRelNT : StartRelNT`** (no hypothesis): the highest node `pe` of the image of the leg
  column at or below the row of `u` is the raw parent of `u` (`cleanX_parent_row`), the clean copy
  of the next generation `b = pa` of the origin (`lookupInnerX`).
* **`startRootNT : StartRootNT`** (no hypothesis): `pe` is the boundary node at the row of the
  origin, and `boundRoot` (`NonTopBound.lean`) gives the steps of `pa = (c_r, C)`.
* **`nonTopStepS : NonTopStepS`** (no hypothesis): `NonTopStep` in the setting of `KeyLeRest`
  (`Setting`, where the output is the canonical mountain of `s[n]`). The steps of `M(s)` from the
  origin `a` of a clean copy `v` land on the generation chain of `a`, or pass the end
  `g = (c_r, C)` of that chain (`Inner.CleanRoot.cleanParentReach`, proved); the output chain from
  `v` walks the clean copies of the generation chain to the boundary node (`walkX`), which follows
  the steps of `g` (`boundRoot`).

`NonTopStep` itself (`LowerChain.lean`) assumes only a successful run and `Recon.Top`, not that
the output is canonical; it is not proved outright. `NonTopRecon.lean` derives it from
`Dimension.BlockReconstruction` (`nonTopStep_of_reconstruction`). It is used only through
`LowerChain.rel_step` in `KeyLeRest`, where the output is canonical. `rel_stepS` replaces `rel_step` with
`nonTopStepS`, and the region lemmas of `LowerChain.lean` are restated with it:
**`keyLeRest_of_nonTop`**: `KeyLeRest` from `TopStep`, `TopStart`, `StepCut`, `CutJump`,
`CutStartCopyNT`, `CutStartRootNT` alone.

All declarations are in the namespace `ChainCorr.NonTop`.
-/

namespace OmegaY.Official.Classification.Proofs.ChainCorr.NonTop

open Canonical Reserve Official Descent Classification Proofs
open Recon Recon.RowLaw
open ChainCorr.Inner ChainCorr.Inner.Clean ChainCorr.Inner.CleanRoot ChainCorr.LowerChain

/-! ## A copy that is not the top copy is a clean copy -/

/-- Two emits of a column with the same origin are clean copies. -/
theorem clean_of_same_src {ctx : Context} {τ : Row} {es : List (Emit × Origin)}
    (hV : MountainValid ctx.source) (hes : emitsT ctx τ = .ok es) {j j' : Nat}
    (hj : j < es.length) (hj' : j' < es.length) (hlt : j < j')
    (hsrc : es[j'].2.src = es[j].2.src) : isCleanO es[j].2 = true := by
  have hord := emitsT_order hV hes
  obtain ⟨_, _, c, hc, _⟩ := emitsT_good hes es[j] (List.getElem_mem hj)
  have hc' : cell? ctx.source es[j'].2.src = some c := by rw [hsrc]; exact hc
  rcases List.pairwise_iff_getElem.mp hord j j' hj hj' hlt c c hc hc' with h1 | ⟨_, h2, _⟩
  · exact absurd h1 (lt_irrefl _)
  · exact h2

theorem clean_false_of_isCleanO {o : Origin} (h : isCleanO o = true) (hc : cutOrigin o = false) :
    ∃ a, o = .clean a false := by
  cases o with
  | plain r => simp [isCleanO] at h
  | upper r => simp [isCleanO] at h
  | clean r b =>
      cases b
      · exact ⟨r, rfl⟩
      · simp [cutOrigin] at hc

/-- **A non-cut emit that is not the top copy of its origin is a clean copy.** -/
theorem clean_of_not_isTopAt {ctx : Context} {τ : Row} {es : List (Emit × Origin)}
    (hV : MountainValid ctx.source) (hes : emitsT ctx τ = .ok es) {j : Nat}
    (hj : j < es.length) (hnc : cutOrigin es[j].2 = false) (hnt : ¬ IsTopAt es j) :
    ∃ a, es[j].2 = .clean a false := by
  unfold IsTopAt at hnt
  push Not at hnt
  obtain ⟨j', hj', _, hlt, hsrc⟩ := hnt
  exact clean_false_of_isCleanO (clean_of_same_src hV hes hj hj' hlt hsrc) hnc

/-- **A copy node that is not the top copy is a clean copy** (when its origin has a raw parent). -/
theorem clean_of_not_topNode {s : List Nat} {n D : Nat} {M : Mountain}
    {out : List Nat} {ρ : Root} {R : Mountain} {col : Column} {t : Cell}
    (hS : Setting s n D M out ρ R col t) {i : Nat} (hi0 : 0 < i) (hi : i < n + 1) {v m : Ref}
    (hc : CopyNode M R n ρ.cr ρ.x0 (official t.row) i v m)
    (hnt : ¬ TopNode M R n ρ.cr ρ.x0 (official t.row) t.row i v m) (hpar : rawParent M m ≠ none) :
    CopyAt M R n ρ.cr ρ.x0 (official t.row) i v (.clean m false) := by
  have hV := build_valid_of_success hS.splice.build
  obtain ⟨root, hTop, _, _⟩ := top_of_setting hS
  obtain ⟨y, es, j, hcy, hyx, hyb, hvc, hvi, hes, hj, hsrc, hcut⟩ := hc
  have hnc : cutOrigin es[j].2 = false := by
    rcases hcut with h | h
    · exact h
    · exact absurd h hpar
  have hat : CopyAt M R n ρ.cr ρ.x0 (official t.row) i v es[j].2 :=
    ⟨y, es, j, hcy, hyx, hyb, hvc, hvi, hes, hj, rfl⟩
  by_cases hcl : isCleanO es[j].2 = true
  · obtain ⟨a, ha⟩ := clean_false_of_isCleanO hcl hnc
    have ham : a = m := by rw [← hsrc, ha]; rfl
    subst ham
    rw [ha] at hat
    exact hat
  · exfalso
    apply hnt
    refine ⟨⟨y, es, j, hcy, hyx, hyb, hvc, hvi, hes, hj, hsrc⟩, ?_, ?_⟩
    · -- no copy of `m` above `v`
      intro v' hv'c hv'i _ hcopy
      obtain ⟨y', es', j', hcy', hyx', hyb', hv'c', hv'i', hes', hj', hsrc'⟩ := hcopy
      have hyy : y' = y := by
        have := block_unique (x' := y') (i' := i) (by omega) hcy hyx hyb'
          (by rw [← hvc, ← hv'c, hv'c']) hi0
        exact this.2
      subst hyy
      have hee : es' = es := by
        rw [hv'c, hes] at hes'
        exact (Except.ok.inj hes').symm
      subst hee
      have hlt : j < j' := by omega
      exact hcl (clean_of_same_src (ctx := ctxAt M R y' i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 v.column) hV hes
        hj hj' hlt (by rw [hsrc, hsrc']))
    · -- the row of an upper copy
      intro cm cv hcm hcv hθ
      cases ho : es[j].2 with
      | clean r b => rw [ho] at hcl; simp [isCleanO] at hcl
      | upper r =>
          have hr : r = m := by rw [← hsrc, ho]; rfl
          subst hr
          rw [ho] at hat
          exact Inner.upper_row hS hi0 hi hat hcv hcm
      | plain r =>
          exfalso
          obtain ⟨c, hc', hclt⟩ := SRParts.lower_src_lt hes hj (by rw [ho]; rfl)
          have hc'' : cell? M m = some c := by rw [← hsrc]; exact hc'
          have e : c = cm := Option.some.inj (hc''.symm.trans hcm)
          subst e
          have := row_lt_of_official hTop.row_one_le hclt
          exact absurd hθ (not_le.mpr this)

/-- **A clean copy keeps the row of its origin.** -/
theorem clean_row_kept {s : List Nat} {n D : Nat} {M : Mountain}
    {out : List Nat} {ρ : Root} {R : Mountain} {col : Column} {t : Cell}
    (hS : Setting s n D M out ρ R col t) {i : Nat} (hi0 : 0 < i) (hi : i < n + 1) {v a : Ref}
    (hva : CopyAtX M R n ρ.cr ρ.x0 (official t.row) i v (.clean a false)) {cv ca : Cell}
    (hcv : cell? R v = some cv) (hca : cell? M a = some ca) :
    cv.row = ca.row ∧ CleanRowOK M ρ.cr (official t.row) (official ca.row) := by
  have hV := build_valid_of_success hS.splice.build
  have hd := CopyShape.spliceData_of_setting hS
  obtain ⟨_, ha1, _⟩ := cleanX_src hva
  obtain ⟨y, es, j, hj, ho, ⟨hvc, _, _, _⟩, hyb, _, hes, cv', hcv', hrow, _⟩ :=
    copyAtX_cell hS hi0 hi hva
  have e : cv' = cv := Option.some.inj (hcv'.symm.trans hcv)
  subst e
  have hes' : blockEmits M R ρ.cr ρ.x0 (official t.row) i y = .ok es := by
    simp only [blockEmits, ← hvc]; exact hes
  have hC : CleanRowOK M ρ.cr (official t.row) (official ca.row) := by
    have := cleanRowOK_of_emit hes (List.getElem_mem hj) ho (c0 := ca)
      (by simp only [ctxAt]; exact hca)
    simpa [ctxAt] using this
  have hcmp := SRCmp.rootCmp s n D M out ρ R t hd i hi y hyb es hes' es[j] (List.getElem_mem hj)
    ca (by rw [ho]; exact hca) (official ca.row) hC.rootRow
  have hnc : cutOrigin es[j].2 = false := by rw [ho]; rfl
  have h2 := (hcmp.1 hnc).2.1 rfl
  refine ⟨?_, hC⟩
  rw [hrow, h2, stored_official (one_le_row hV hca ha1)]

/-- The column of a clean copy is the image of the column of its origin. -/
theorem copyAtX_column {M R : Mountain} {n cr x0 : Nat} {τ : Row} {i : Nat} {v a : Ref}
    {b : Bool} (h : CopyAtX M R n cr x0 τ i v (.clean a b)) :
    v.column = a.column + (x0 - cr) * i := by
  obtain ⟨y, es, j, _, _, _, hvc, _, hes, hj, ho⟩ := h
  obtain ⟨hcol, _⟩ := emitsT_good hes es[j] (List.getElem_mem hj)
  rw [ho] at hcol
  simp only [Origin.isUpper, Bool.false_eq_true, if_false, Origin.src, ctxAt] at hcol
  rw [hvc, hcol]

/-- A generation chain stays on its row. -/
theorem genChain_row {M : Mountain} {cr : Nat} {a g : Ref} {ca cg : Cell}
    (h : Relation.TransGen (GenStep M cr) a g) (hca : cell? M a = some ca)
    (hcg : cell? M g = some cg) : cg.row = ca.row := by
  induction h generalizing cg with
  | single hab =>
      obtain ⟨_, _, ca', cb, _, hca', _, _, hcb, hrow⟩ := hab
      rw [hca] at hca'; cases hca'
      rw [hcg] at hcb; cases hcb
      exact hrow
  | tail _ hbc ih =>
      obtain ⟨_, _, cb, cc, _, hcb, _, _, hcc, hrow⟩ := hbc
      rw [hcg] at hcc; cases hcc
      rw [hrow]
      exact ih hcb

/-- A generation chain goes left. -/
theorem genChain_col_le {M : Mountain} (hV : MountainValid M) {cr : Nat} {b g : Ref}
    (h : Relation.ReflTransGen (GenStep M cr) b g) : g.column ≤ b.column := by
  induction h with
  | refl => exact le_refl _
  | tail _ hcd ih =>
      obtain ⟨_, _, cc, cd, l, hcc, hl, hdl, _, _⟩ := hcd
      have := left_lt_of_valid hV hcc hl
      omega

/-! ## `NonTopStep` in the setting of `KeyLeRest` -/

/-- `NonTopStep` (`LowerChain.lean`) over `Setting`: the output is the canonical mountain of
`s[n]`. -/
def NonTopStepS : Prop :=
  ∀ s n D M out ρ R (col : Column) (t : Cell), Setting s n D M out ρ R col t →
    ∀ i, 0 < i → i < n + 1 → ∀ v m, CopyNode M R n ρ.cr ρ.x0 (official t.row) i v m →
      ¬ TopNode M R n ρ.cr ρ.x0 (official t.row) t.row i v m →
      ∀ k m', MStep M k m m' →
        Next R M k ρ.cr ((ρ.x0 - ρ.cr) * i) (Rel M R n ρ.cr ρ.x0 (official t.row) t.row i) v m'

/-- **`NonTopStepS` holds.** -/
theorem nonTopStepS : NonTopStepS := by
  intro s n D M out ρ R col t hS i hi0 hi v m hc hnt k m' hst
  have hV := build_valid_of_success hS.splice.build
  have hd := CopyShape.spliceData_of_setting hS
  obtain ⟨_, hcrx, hinv, _⟩ := SRParts.spliceData_facts hd
  have hA : AgreeBelow M R ρ.x0 := hinv.1
  have hpar : rawParent M m ≠ none := by rw [hst.1]; simp
  have hva := clean_of_not_topNode hS hi0 hi hc hnt hpar
  have hvaX := copyAtX_of_copyAt hva
  have hmx : m.column < ρ.x0 := by
    obtain ⟨y, es, j, _, hyx, _, _, _, hes, hj, ho⟩ := hva
    obtain ⟨hcol, _⟩ := emitsT_good hes es[j] (List.getElem_mem hj)
    rw [ho] at hcol
    simp only [Origin.isUpper, Bool.false_eq_true, if_false, Origin.src, ctxAt] at hcol
    omega
  obtain ⟨cv, hcv, _, hall⟩ := walkX hS hi0 hi m.column v m rfl hvaX
  obtain ⟨_, hm1, cm, hcm⟩ := cleanX_src hvaX
  obtain ⟨hcvrow, hC⟩ := clean_row_kept hS hi0 hi hvaX hcv hcm
  -- the end of the generation chain follows the steps of the root node
  have hend : ∀ g, Relation.TransGen (GenStep M ρ.cr) m g → g.column = ρ.cr →
      ∃ P, ScaleReach R 0 v P ∧ P.column = ρ.cr + (ρ.x0 - ρ.cr) * i ∧
        ∀ kk m'', MStep M kk g m'' → ScaleReach R kk P m'' := by
    intro g hmg hgc
    obtain ⟨_, _, h3⟩ := hall g hmg.to_reflTransGen
    obtain ⟨P, cP, hr, hPc, hcP, hProw⟩ := h3 hgc
    obtain ⟨g1, hg1, hgg⟩ := Relation.TransGen.tail'_iff.mp hmg
    have hg1' := hgg
    obtain ⟨_, hgi, _, cg, _, _, _, _, hcg, _⟩ := hg1'
    have hcgrow := genChain_row hmg hcm hcg
    refine ⟨P, hr, hPc, fun kk m'' hst' => ?_⟩
    exact boundRoot hS i hi0 hi P g cP cg hPc hcP hgc hgi hcg (by rw [hProw, hcvrow, hcgrow])
      (by rw [hcgrow]; exact hC) kk m'' hst'
  rcases cleanParentReach s n D M out ρ R col t hS i hi0 hi v m hva k m' hst with
    hmm' | ⟨g, g1, hmg, hgc, hgg1, hg1m'⟩
  · -- `m'` is on the generation chain of `m`
    obtain ⟨hcr, h2, _⟩ := hall m' hmm'.to_reflTransGen
    refine ⟨fun h => absurd h (by omega), fun h => ?_, fun h => ?_⟩
    · obtain ⟨P, hr, hPc, hP⟩ := hend m' hmm' h
      exact ⟨P, reach_mono hr (Nat.zero_le _), le_of_eq hPc, fun m'' hst' => hP k m'' hst'⟩
    · obtain ⟨v', hr, hv'⟩ := h2 h
      have hm'm : m'.column < m.column := by
        obtain ⟨b, hmb, hbm'⟩ := Relation.TransGen.head'_iff.mp hmm'
        have hlt1 : b.column < m.column := by
          obtain ⟨_, _, ca, cb, l, hca, hl, hbl, _, _⟩ := hmb
          rw [hbl]; exact left_lt_of_valid hV hca hl
        have : m'.column ≤ b.column := genChain_col_le hV hbm'
        omega
      have hv'col := copyAtX_column hv'
      have hv'at := copyAt_of_copyAtX hv' (by rw [hv'col]; omega)
      exact ⟨v', reach_mono hr (Nat.zero_le _), Or.inl (copyNode_of_copyAt hv'at rfl)⟩
  · -- `m'` is reached from the end `g` of the chain, left of `c_r`
    obtain ⟨P, hr, _, hP⟩ := hend g hmg hgc
    have hg1c : g1.column < ρ.cr := by rw [← hgc]; exact hgg1.column_lt
    have hm'c : m'.column < ρ.cr := lt_of_le_of_lt hg1m'.column_le hg1c
    have hreach : ScaleReach R k v m' :=
      ScaleReach.trans (reach_mono hr (Nat.zero_le _))
        (ScaleReach.trans (hP k g1 hgg1) (SRParts.reach_transfer hA hg1m' (by omega)))
    exact ⟨fun _ => hreach, fun h => absurd h (by omega), fun h => absurd h (by omega)⟩

/-! ## The starts of the region nodes that are not top copies -/

/-- The data of a region node that is not a top copy: the setting, the clean copy `u` of the
origin `a`, the raw parent `pe` of `u` at its row, the next generation `pa` of `a`. -/
theorem site_nonTop {s : List Nat} {n D : Nat} {M : Mountain} {out : List Nat} {ρ : Root}
    {R : Mountain} {t : Cell} {X x i : Nat} {es : List (Emit × Origin)}
    (hS : Site s n D M out ρ R t X x i es) {j : Nat} (hj : j < es.length)
    (hnc : cutOrigin es[j].2 = false) (hnt : ¬ IsTopAt es j)
    {cu cv : Cell} {ref l pe pa : Ref} {cpe cpa : Cell}
    (hL : Legs M R X j es[j].2 cu cv ref l pe pa cpe cpa) :
    ∃ (col : Column) (a : Ref), Setting s n D M out ρ R col t ∧
      CopyAtX M R n ρ.cr ρ.x0 (official t.row) i ⟨X, j + 1⟩ (.clean a false) ∧
      GenStep M ρ.cr a pa ∧ ρ.cr ≤ pa.column ∧ pa.column = l.column ∧
      rawParent R ⟨X, j + 1⟩ = some pe ∧ cpe.row = cpa.row ∧
      CleanRowOK M ρ.cr (official t.row) (official cpa.row) := by
  obtain ⟨col, hcol, ht⟩ := hS.last
  have hS' : Setting s n D M out ρ R col t := ⟨hS.splice, hS.deg, hS.run, hS.canon, hcol, ht⟩
  have hV := build_valid_of_success hS.splice.build
  have hi0 := hS.iPos
  have hi := hS.iLt
  obtain ⟨hcx, hxx⟩ := mem_blockColumns_pos hS.xMem hi0
  obtain ⟨a, ha⟩ := clean_of_not_isTopAt (ctx := ctxAt M R x i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 X) hV
    hS.emits hj hnc hnt
  have hva : CopyAtX M R n ρ.cr ρ.x0 (official t.row) i ⟨X, j + 1⟩ (.clean a false) :=
    ⟨x, es, j, hcx, hxx, hS.xMem, hS.Xeq, rfl, hS.emits, hj, ha⟩
  have hcv := hL.hcv
  rw [ha] at hcv
  simp only [Origin.src] at hcv
  obtain ⟨ca, l', cu', v1, c1, hca, hl', hcu', hraw, hc1, hrow1, hham⟩ :=
    cleanX_parent_row hS' hi0 hi hva
  have e1 : ca = cv := Option.some.inj (hca.symm.trans hcv)
  subst e1
  have e2 : l' = l := Option.some.inj (hl'.symm.trans hL.hl)
  subst e2
  have e3 : cu' = cu := Option.some.inj (hcu'.symm.trans hL.hcu)
  subst e3
  have himg := leg_image hS hj hL
  have hpe := hL.hpe
  rw [himg, hham] at hpe
  have e4 : v1 = pe := Option.some.inj hpe
  subst e4
  have e5 : c1 = cpe := Option.some.inj (hc1.symm.trans hL.hcpe)
  subst e5
  obtain ⟨b, hab, hb⟩ := chainX_first_step hS' hva
  have hab' := hab
  obtain ⟨_, hb1, ca', cb, l2, hca', hl2, hbl, hcb, hbrow⟩ := hab'
  have e6 : ca' = ca := Option.some.inj (hca'.symm.trans hca)
  subst e6
  have e7 : l2 = l' := Option.some.inj (hl2.symm.trans hl')
  subst e7
  have hpa : highestAtMost M l2.column ca'.row = some b := by
    rw [← hbl, ← hbrow]
    exact hAM_self hV (by omega) hcb
  have e8 : b = pa := Option.some.inj (hpa.symm.trans hL.hpa)
  subst e8
  have e9 : cb = cpa := Option.some.inj (hcb.symm.trans hL.hcpa)
  subst e9
  obtain ⟨hkept, hC⟩ := clean_row_kept hS' hi0 hi hva hcu' hca'
  refine ⟨col, a, hS', hva, hab, hb, hbl, hraw, ?_, ?_⟩
  · rw [hrow1, hkept, hbrow]
  · rw [hbrow]; exact hC

/-- **`StartRelNT` holds.** -/
theorem startRelNT : StartRelNT := by
  intro s n D M out ρ R t X x i es hS j hj hnc hnt cu cv ref l pe pa cpe cpa hL hlt
  obtain ⟨col, a, hS', hva, hab, _, hpal, hraw, _, _⟩ := site_nonTop hS hj hnc hnt hL
  have hcpa : ρ.cr < pa.column := by rw [hpal]; exact hlt
  have := lookupInnerX hS' hS.iPos hS.iLt hva hab hcpa hraw
  exact Or.inl (copyNode_of_copyAt this rfl)

/-- **`StartRootNT` holds.** -/
theorem startRootNT : StartRootNT := by
  intro s n D M out ρ R t X x i es hS j hj hnc hnt cu cv ref l pe pa cpe cpa hL heq k m'' _ hst
  obtain ⟨col, a, hS', hva, hab, _, hpal, hraw, hrow, hC⟩ := site_nonTop hS hj hnc hnt hL
  have hV := build_valid_of_success hS.splice.build
  obtain ⟨_, hb1, _, _, _, _, _, _, _, _⟩ := hab
  have hpec : pe.column = ρ.cr + (ρ.x0 - ρ.cr) * i := by
    have := highestAtMost_column hL.hpe
    rw [this, leg_image hS hj hL, heq, mapColumn_of_ge (le_refl _)]
  exact boundRoot hS' i hS.iPos hS.iLt pe pa cpe cpa hpec hL.hcpe (by rw [hpal, heq]) hb1
    hL.hcpa hrow hC k m'' hst

/-! ## `KeyLeRest` with `NonTopStepS` in place of `NonTopStep` -/

/-- **Every step from a `Rel` pair is matched over `Rel`** (`LowerChain.rel_step` with
`nonTopStepS`, in the setting of `KeyLeRest`). -/
theorem rel_stepS (hTS : TopStep) {s : List Nat} {n D : Nat} {M : Mountain} {out : List Nat}
    {ρ : Root} {R : Mountain} {col : Column} {t : Cell} (hS : Setting s n D M out ρ R col t)
    {i : Nat} (hi0 : 0 < i) (hi : i < n + 1) {k : Nat} {v m m' : Ref}
    (h : Rel M R n ρ.cr ρ.x0 (official t.row) t.row i v m) (hst : MStep M k m m') :
    Next R M k ρ.cr ((ρ.x0 - ρ.cr) * i) (Rel M R n ρ.cr ρ.x0 (official t.row) t.row i) v m' := by
  classical
  by_cases htop : TopNode M R n ρ.cr ρ.x0 (official t.row) t.row i v m
  · obtain ⟨root, hTop, hroot, hx0⟩ := top_of_setting hS
    rw [← hroot, hx0] at htop ⊢
    obtain ⟨hpar, c, cq, hc, hcq, hj, _⟩ := hst
    obtain ⟨A, hvA, hSt⟩ := hTS s n R M t root i hS.run hTop hi0 (by omega) v m htop m' c cq hpar
      hc hcq
    exact next_of_stand (MStep.mono hvA hj) hSt
  · rcases h with h | h
    · exact nonTopStepS s n D M out ρ R col t hS i hi0 hi v m h htop k m' hst
    · exact absurd h htop

/-- The step and the top start of a region node, in the notation of `ρ`. -/
theorem region_toolsS (hTS : TopStep) (hTSt : TopStart)
    {s : List Nat} {n D : Nat} {M : Mountain} {out : List Nat} {ρ : Root} {R : Mountain}
    {t : Cell} {X x i : Nat} {es : List (Emit × Origin)}
    (hS : Site s n D M out ρ R t X x i es) {j : Nat} (hj : j < es.length)
    {cu cv : Cell} {ref l pe pa : Ref} {cpe cpa : Cell}
    (hL : Legs M R X j es[j].2 cu cv ref l pe pa cpe cpa) :
    (∀ k v m m', Rel M R n ρ.cr ρ.x0 (official t.row) t.row i v m → MStep M k m m' →
      Next R M k ρ.cr ((ρ.x0 - ρ.cr) * i) (Rel M R n ρ.cr ρ.x0 (official t.row) t.row i) v m') ∧
    (IsTopAt es j → Stand M R n ρ.cr ρ.x0 (official t.row) t.row i pe pa) := by
  obtain ⟨col, hcol, ht⟩ := hS.last
  obtain ⟨rt, hTop, hcr, hx0⟩ := top_of_splice hS.splice hS.run hcol ht
  have hi : i ≤ n := by have := hS.iLt; omega
  have himg := leg_image hS hj hL
  refine ⟨fun k v m m' h hst => ?_, fun htop => ?_⟩
  · exact rel_stepS hTS ⟨hS.splice, hS.deg, hS.run, hS.canon, hcol, ht⟩ hS.iPos hS.iLt h hst
  · have hes' := hS.emits
    have hx' := hS.xMem
    have hcu' := hL.hcu
    have hpe' := hL.hpe
    rw [himg] at hpe'
    rw [hS.Xeq] at hes' hcu'
    rw [hcr, hx0] at hes' hx' hcu' hpe' ⊢
    exact hTSt s n R M t rt i x hS.run hTop hS.iPos hi hx' es hes' j hj htop cu cv l pe pa hcu'
      hL.hcv hL.hl hL.hpa hpe'

/-- **A region lemma (origins that are not gap copies) from the shared family.** -/
theorem keyLeRegion_of_lowerS (sel : Nat → Nat → Origin → Prop)
    (hsel : ∀ x x0 o, sel x x0 o → cutOrigin o = false)
    (hTS : TopStep) (hTSt : TopStart) : KeyLeRegion sel := by
  have hRel := startRelNT
  have hRoot := startRootNT
  have hLeft := leftStart_holds
  have hJump := startJumpGe_holds
  classical
  intro s n D M out ρ R col t hc hdeg hRun hRb hcol ht X x i hX0 hXR hXeq hi hx hipos hcopy es
    hes j hj e a he ha hnot hs _
  obtain ⟨hS, cu, cv, ref, l, pe, pa, cpe, cpa, hL, hpec, hpac, hek, hak, hap⟩ :=
    Skip.region_unpack hc hdeg hRun hRb hcol ht hX0 hXR hXeq hi hx hipos hcopy hes hj he ha
  rw [hek, hak]
  have hnc := hsel _ _ _ hs
  obtain ⟨_, _, _, _, _, hcrx, hinv⟩ := spliceCase_data hc hRun
  have hA : AgreeBelow M R ρ.x0 := hinv.1
  have hnot' : ¬ (es[j].2.isUpper = true ∧ l.column < ρ.cr) := by
    rw [hap] at hnot
    exact hnot
  have himg := leg_image hS hj hL
  obtain ⟨hstep, hstand⟩ := region_toolsS hTS hTSt hS hj hL
  by_cases hcrl : ρ.cr ≤ l.column
  · have hjump := hJump s n D M out ρ R t X x i es hS j hj hnc cu cv ref l pe pa cpe cpa hL
      hnot' hcrl
    apply keyLe_keyAt_of_scale hL.hcpe hL.hcpa hjump
    intro k hk _
    show (root R k pe).column ≤ mapColumn ρ.cr ((ρ.x0 - ρ.cr) * i) (root M k pa).column
    rcases Nat.lt_or_eq_of_le hcrl with hlt | heq
    · -- a leg right of the root column: the simulation over `Rel`, without skips
      have hrel : Rel M R n ρ.cr ρ.x0 (official t.row) t.row i pe pa := by
        by_cases htop : IsTopAt es j
        · exact Or.inr ((hstand htop).2.2 (by rw [hpac]; exact hlt))
        · exact hRel s n D M out ρ R t X x i es hS j hj hnc htop cu cv ref l pe pa cpe cpa hL hlt
      exact bound_of_sim hA (le_of_lt hcrx) (Rel M R n ρ.cr ρ.x0 (official t.row) t.row i)
        (fun v m h => rel_column h) (fun v m m' h hst => hstep k v m m' h hst) pe pa hrel
    · -- the leg is the root column
      have hpe' : pe.column ≤ ρ.cr + (ρ.x0 - ρ.cr) * i := by
        rw [hpec, himg, ← heq, mapColumn_of_ge (le_refl _)]
      refine bound_root hA (le_of_lt hcrx) (by rw [hpac]; exact heq.symm) hpe' (fun m'' hst => ?_)
      by_cases htop : IsTopAt es j
      · obtain ⟨_, heqS, _⟩ := hstand htop
        obtain ⟨_, _, hch⟩ := heqS (by rw [hpac]; exact heq.symm)
        obtain ⟨hpar, ca, cb, hca, hcb, hjj, _⟩ := hst
        exact reach_mono (hch m'' ca cb hpar hca hcb) hjj
      · exact hRoot s n D M out ρ R t X x i es hS j hj hnc htop cu cv ref l pe pa cpe cpa hL
          heq.symm k m'' hk hst
  · -- a leg left of the root column: the chains in the shared columns
    have hlt : l.column < ρ.cr := by omega
    obtain ⟨hjump, hmeet⟩ := hLeft s n D M out ρ R t X x i es hS j hj hnc cu cv ref l pe pa cpe
      cpa hL hnot' hlt
    apply keyLe_keyAt_of_scale hL.hcpe hL.hcpa hjump
    intro k hk _
    show (root R k pe).column ≤ mapColumn ρ.cr ((ρ.x0 - ρ.cr) * i) (root M k pa).column
    obtain ⟨q, hq1, hq2⟩ := hmeet k hk
    have hpecol : pe.column < ρ.x0 := by
      rw [hpec, himg, mapColumn_of_lt hlt]
      omega
    have hqcol : q.column < ρ.x0 := lt_of_le_of_lt hq1.column_le hpecol
    rw [root_of_reach hq1, root_of_reach hq2, root_congr hA k hqcol]
    exact le_mapColumn _ _ _

/-- **A gap-copy region lemma from the shared family** (the lexicographic simulation over
`Rel ∨ CutNode`). -/
theorem keyLeRegion_of_lowerCutS (sel : Nat → Nat → Origin → Prop)
    (hsel : ∀ x x0 o, sel x x0 o → cutOrigin o = true)
    (hTS : TopStep) (hTSt : TopStart) (hCut : StepCut) (hJump : CutJump)
    (hCopy : CutStartCopyNT) (hRoot : CutStartRootNT) : KeyLeRegion sel := by
  classical
  intro s n D M out ρ R col t hc hdeg hRun hRb hcol ht X x i hX0 hXR hXeq hi hx hipos hcopy es
    hes j hj e a he ha hnot hs _
  obtain ⟨hS, cu, cv, ref, l, pe, pa, cpe, cpa, hL, hpec, hpac, hek, hak, hap⟩ :=
    Skip.region_unpack hc hdeg hRun hRb hcol ht hX0 hXR hXeq hi hx hipos hcopy hes hj he ha
  rw [hek, hak]
  have hnc := hsel _ _ _ hs
  obtain ⟨_, _, _, _, _, hcrx, hinv⟩ := spliceCase_data hc hRun
  have hA : AgreeBelow M R ρ.x0 := hinv.1
  have hcrl := cutLeg s n D M out ρ R t X x i es hS j hj hnc cu cv ref l pe pa cpe cpa hL
  have himg := leg_image hS hj hL
  obtain ⟨hstep, hstand⟩ := region_toolsS hTS hTSt hS hj hL
  apply keyLe_keyAt_of_lex hL.hcpe hL.hcpa
  intro k hk hkD
  by_cases hde : Row.jump cu.row cpe.row ≤ k
  · rcases Nat.lt_or_eq_of_le hcrl with hlt | heq
    · -- a leg right of the root column: the lexicographic simulation
      have hrel : Rel M R n ρ.cr ρ.x0 (official t.row) t.row i pe pa ∨
          CutNode M R n ρ.cr ρ.x0 (official t.row) i pe pa := by
        by_cases htop : IsTopAt es j
        · exact Or.inl (Or.inr ((hstand htop).2.2 (by rw [hpac]; exact hlt)))
        · exact Or.inr (hCopy s n D M out ρ R t X x i es hS j hj hnc htop cu cv ref l pe pa cpe
            cpa hL hlt)
      have hsim := lex_of_sim (D := D) hA (le_of_lt hcrx)
        (fun v m => Rel M R n ρ.cr ρ.x0 (official t.row) t.row i v m ∨
          CutNode M R n ρ.cr ρ.x0 (official t.row) i v m)
        (fun v m h => by
          rcases h with h | h
          · exact rel_column h
          · exact le_of_eq (cutNode_column h))
        (by
          rintro v m m' (hvm | hvm) hst
          · exact Or.inl (next_mono (fun _ _ h => Or.inl h) (hstep k v m m' hvm hst))
          · rcases hCut s n D M out ρ R col t hc hdeg hRun hRb hcol ht i hipos hi v m hvm k m' hkD
              hst with h' | h'
            · refine Or.inl (next_mono (fun _ _ h => ?_) h')
              rcases h with h | h
              · exact Or.inl (Or.inl h)
              · exact Or.inr h
            · exact Or.inr h')
        pe pa hrel
      rcases hsim with hb | ⟨k', hk', hk'D, hlt'⟩
      · exact Or.inl ⟨hde, hb⟩
      · exact Or.inr ⟨k', hk', hk'D, by omega, by omega, hlt'⟩
    · -- the leg is the root column
      have hpe' : pe.column ≤ ρ.cr + (ρ.x0 - ρ.cr) * i := by
        rw [hpec, himg, ← heq, mapColumn_of_ge (le_refl _)]
      refine Or.inl ⟨hde, bound_root hA (le_of_lt hcrx) (by rw [hpac]; exact heq.symm) hpe'
        (fun m'' hst => ?_)⟩
      by_cases htop : IsTopAt es j
      · obtain ⟨_, heqS, _⟩ := hstand htop
        obtain ⟨_, _, hch⟩ := heqS (by rw [hpac]; exact heq.symm)
        obtain ⟨hpar, ca, cb, hca, hcb, hjj, _⟩ := hst
        exact reach_mono (hch m'' ca cb hpar hca hcb) hjj
      · exact hRoot s n D M out ρ R t X x i es hS j hj hnc htop cu cv ref l pe pa cpe cpa hL
          heq.symm k m'' hk hkD hst
  · rcases hJump s n D M out ρ R t X x i es hS j hj hnc cu cv ref l pe pa cpe cpa hL with
      hle | ⟨k', h1, h2, h3, h4⟩
    · omega
    · exact Or.inr ⟨k', by omega, h3, h1, h2, h4⟩


/-- **`Control.KeyLeRest` from `TopStep`, `TopStart` and the gap-copy statements** (`NonTopStep`,
`StartRelNT`, `StartRootNT` are no longer hypotheses: `nonTopStepS`, `startRelNT`,
`startRootNT`). -/
theorem keyLeRest_of_nonTop (hTS : TopStep) (hTSt : TopStart) (hCut : StepCut)
    (hCJump : CutJump) (hCCopy : CutStartCopyNT) (hCRoot : CutStartRootNT) : KeyLeRest :=
  keyLeRest_of_regions
    (keyLeRegion_of_lowerS _ (fun _ _ o h => by cases o <;> simp_all [Origin.isUpper, cutOrigin])
      hTS hTSt)
    (keyLeRegion_of_lowerS _ (fun _ _ o h => by obtain ⟨⟨r, rfl⟩, _⟩ := h; rfl) hTS hTSt)
    (keyLeRegion_of_lowerS _ (fun _ _ o h => by obtain ⟨⟨r, rfl⟩, _⟩ := h; rfl) hTS hTSt)
    (keyLeRegion_of_lowerS _ (fun _ _ o h => by obtain ⟨⟨r, rfl⟩, _⟩ := h; rfl) hTS hTSt)
    (keyLeRegion_of_lowerS _ (fun _ _ o h => by obtain ⟨⟨r, rfl⟩, _⟩ := h; rfl) hTS hTSt)
    (keyLeRegion_of_lowerCutS _ (fun _ _ o h => by obtain ⟨⟨r, rfl⟩, _⟩ := h; rfl)
      hTS hTSt hCut hCJump hCCopy hCRoot)
    (keyLeRegion_of_lowerCutS _ (fun _ _ o h => by obtain ⟨⟨r, rfl⟩, _⟩ := h; rfl)
      hTS hTSt hCut hCJump hCCopy hCRoot)

/-- **Well-foundedness of the official expansion** from the reconstruction, `TopStep`, `TopStart`
and the gap-copy statements. -/
theorem wellFounded_of_nonTop (hrec : Dimension.BlockReconstruction) (hTS : TopStep)
    (hTSt : TopStart) (hCut : StepCut) (hCJump : CutJump) (hCCopy : CutStartCopyNT)
    (hCRoot : CutStartRootNT) : WellFounded Step :=
  wellFounded_of_block hrec ControlProof.controlDominates
    (keyLeRest_of_nonTop hTS hTSt hCut hCJump hCCopy hCRoot)

/-! ## The targets, with fully qualified statements -/

theorem startRelNT_holds : OmegaY.Official.Classification.Proofs.ChainCorr.LowerChain.StartRelNT :=
  startRelNT

theorem startRootNT_holds :
    OmegaY.Official.Classification.Proofs.ChainCorr.LowerChain.StartRootNT :=
  startRootNT

theorem keyLeRest_holds_of (hTS : OmegaY.Official.Classification.Proofs.ChainCorr.LowerChain.TopStep)
    (hTSt : OmegaY.Official.Classification.Proofs.ChainCorr.LowerChain.TopStart)
    (hCut : OmegaY.Official.Classification.Proofs.ChainCorr.StepCut)
    (hCJump : OmegaY.Official.Classification.Proofs.ChainCorr.CutJump)
    (hCCopy : OmegaY.Official.Classification.Proofs.ChainCorr.LowerChain.CutStartCopyNT)
    (hCRoot : OmegaY.Official.Classification.Proofs.ChainCorr.LowerChain.CutStartRootNT) :
    OmegaY.Official.Classification.KeyLeRest :=
  keyLeRest_of_nonTop hTS hTSt hCut hCJump hCCopy hCRoot

end OmegaY.Official.Classification.Proofs.ChainCorr.NonTop

#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.NonTop.nonTopStepS
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.NonTop.startRelNT
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.NonTop.startRootNT
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.NonTop.keyLeRest_of_nonTop
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.NonTop.wellFounded_of_nonTop
