/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/StepInnerCleanRootLookup.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.StepInnerCleanBoundary
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CutGapRunLow
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CopyShapeNoMA
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.StartRootFixCmp
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.StartRootFixPa
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.StartRootPartsB0
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.StepInnerCleanRoot

set_option backward.do.legacy false

/-!
# `LookupInner` (proved) and `LookupRoot` (from `StartRoot`)

The two open statements of `StepInnerCleanLookup.lean` (namespace `ChainCorr.Inner.Clean`).
Let `v` be a clean copy (`b = 0`) in block `i ≥ 1` of `a = (y, C)`, and `a → b` the first step
of the generation chain of `a` (`b` is the node of the leg column of `a` at the row `C`).

## `LookupInner` (proved: `lookupInner`)

If `b` is right of `c_r`, the raw parent `v₁` of `v` in the output is a clean copy (`b = 0`) of
`b` in block `i`. The argument is the one of `CutGap.cutRunLow_of_facts` (`CutGapRunLow.lean`)
with a clean copy in place of a gap copy:

* `C` is the row of the root top `ρ` of its level-2 region and lies in a first item of level
  `≥ 2` (`CutGap.emitsT_cleanTop`); `y` passes the ascension test of `C` (`emitsT_cleanRoot`), so
  the leg column `l = col b` passes it too (`CutGap.ascLeg`): `l` ascends at `ρ`.
* The copy of the column `l` in block `i` has a non-cut emit of `b`
  (`CopyShape.NoMA.inner_copyEmitted`). It is not an upper copy (`C < τ`), and not a plain copy
  (`CutGap.emitsT_plainAsc`: a plain copy of `C` needs a first item of level 1 containing `C`, or
  a column that does not ascend at `ρ`). So it is the clean copy `.clean b false`.
* A non-cut emit whose origin row is a row of the root column keeps that row
  (`ChainCorr.SRCmp.rootCmp`). So both `v` and the clean copy of `b` are at the row `C`; the
  raw parent `v₁` of `v` is the node of the column `φ(l)` at the row of `v`
  (`clean_parent_row`), hence it is that clean copy.

## `LookupRoot` (from `StartRoot`: `lookupRoot_of_startRoot`)

If `b` is on the root column, `LookupRoot` is the statement `ChainCorr.StartRoot`
(`ChainCorrRegions.lean`) at the node `v`: the leg of `a` is `l` with `col l = c_r`, the
highest node of `l` at or below the row of `a` is `b` itself (same row, so the jump condition
`jump(row a, row b) = 0 ≤ k` is empty), and the highest node of the image column `c_r + w·i` at
or below the row of `v` is `v₁` (`clean_parent_row`). With `startRoot_of_parts` and the proved
`SRFixPa.originReach`: `lookupRoot_of_boundaryChain : BoundaryChain → LookupRoot`.

`BoundaryChain` (open, `ChainCorrStartRoot.lean`; reduced in `StartRootFixChain.lean`) is used
only at the block `i` of `v`: the chain of the boundary column `x₀ + w·(i - 1)`, the copy of `x₀`
made by block `i - 1` (`BoundaryChainAt i`, `startRoot_at`, `lookupRootAt_of`). At `i = 1` it is
proved (`SRParts.boundaryChain_one`), so **`LookupRoot` holds in block `1`** (`lookupRootAt_one`).

## Results

* **`lookupInner : LookupInner`** (no hypothesis).
* **`lookupRoot_of_startRoot : ChainCorr.StartRoot → LookupRoot`**,
  **`lookupRoot_of_boundaryChain : ChainCorr.BoundaryChain → LookupRoot`**.
* **`cleanLookup_of_startRoot : ChainCorr.StartRoot → CleanLookup`**,
  **`cleanLookup_of_boundaryChain : ChainCorr.BoundaryChain → CleanLookup`**.
* **`lookupRootAt_one : LookupRootAt 1`** (no hypothesis), and
  **`cleanLookup_of_boundaryChainAt : (∀ i, 2 ≤ i → BoundaryChainAt i) → CleanLookup`**.
* `stepInner_of_legLookup : LegLookup → BumpCopyLower → (∀ i, 2 ≤ i → BoundaryChainAt i) →
  StepInner` (with `StepInnerCleanRoot.lean`). Note that `StepInner` itself is numerically false
  (`LegPartsSkip.lean`); this only records that its clean part needs nothing but
  `BoundaryChainAt`.

All declarations are in the namespace `ChainCorr.Inner.CleanRoot`.
-/

namespace OmegaY.Official.Classification.Proofs.ChainCorr.Inner.CleanRoot

open Canonical Reserve Official Descent Classification Proofs
open Recon Recon.RowLaw
open ChainCorr.Inner.Clean

/-! ## The emits of a column of a block -/

/-- Every inner column `z` of a block `i ≥ 1` is copied: its emits exist, and the output
cells of that column are the assembled emits. -/
theorem inner_emits {s : List Nat} {n D : Nat} {M : Mountain} {out : List Nat} {ρ : Root}
    {R : Mountain} {col : Column} {t : Cell} (hS : Setting s n D M out ρ R col t) {i : Nat}
    (hi0 : 0 < i) (hi : i < n + 1) {z : Nat} (hcz : ρ.cr < z) (hzx : z < ρ.x0) :
    z ∈ blockColumns ρ.cr ρ.x0 n i ∧ ∃ es,
      emitsT (ctxAt M R z i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 (z + (ρ.x0 - ρ.cr) * i)) (official t.row) =
        .ok es := by
  obtain ⟨col', t', hcol', ht', _, hcrx, hinv⟩ := spliceCase_data hS.splice hS.run
  have hcc : col' = col := Option.some.inj (hcol'.symm.trans hS.hcol)
  subst hcc
  have htt : t' = t := Option.some.inj (ht'.symm.trans hS.ht)
  subst htt
  have hRs : R.size = ρ.x0 + n * (ρ.x0 - ρ.cr) := by
    rw [build_size hS.canon]
    exact Reconstruction.expand_length_splice hS.splice.build hS.splice.run hS.splice.root
      hS.splice.copies
  have hwi : (ρ.x0 - ρ.cr) * i ≤ n * (ρ.x0 - ρ.cr) := by
    rw [Nat.mul_comm n]; exact Nat.mul_le_mul_left _ (by omega)
  have hw1 : ρ.x0 - ρ.cr ≤ (ρ.x0 - ρ.cr) * i := Nat.le_mul_of_pos_right _ hi0
  have hmem : z ∈ blockColumns ρ.cr ρ.x0 n i := by
    unfold blockColumns
    rw [if_neg (by omega)]
    simp only [List.mem_range'_1]
    split <;> omega
  refine ⟨hmem, ?_⟩
  have hXR : z + (ρ.x0 - ρ.cr) * i < R.size := by omega
  have hX0 : ρ.x0 ≤ z + (ρ.x0 - ρ.cr) * i := by omega
  obtain ⟨i', x', _, hx', hXeq, hcopy⟩ := hinv.2.2 _ hXR hX0
  obtain ⟨hii, hxx⟩ := block_unique hcrx hcz hzx hx' hXeq hi0
  subst hii
  subst hxx
  obtain ⟨es, hes, _⟩ := copyColumn_emitsT hcopy
  exact ⟨es, hes⟩

/-- The highest node of a column at or below the row of one of its nodes is that node. -/
theorem hAM_self {M : Mountain} (hV : MountainValid M) {b : Ref} {cb : Cell} (hb0 : 0 < b.index)
    (hcb : cell? M b = some cb) : highestAtMost M b.column cb.row = some b := by
  refine highestAtMost_of_max rfl hb0 hcb le_rfl ?_
  intro j c hc hj0 hle
  by_contra hn
  have hlt : b.index < j := lt_of_not_ge hn
  unfold cell? at hc hcb
  cases hcM : M[b.column]? with
  | none => simp [hcM] at hcb
  | some colm =>
      simp only [hcM, Option.bind_eq_bind, Option.bind_some] at hc hcb
      have hcs : b.column < M.size := by
        rcases Nat.lt_or_ge b.column M.size with h' | h'
        · exact h'
        · simp [Array.getElem?_eq_none h'] at hcM
      have hcolEq : M[b.column] = colm := by
        have := hcM; rw [Array.getElem?_eq_getElem hcs] at this; exact Option.some.inj this
      have hCV := hV b.column hcs
      rw [hcolEq] at hCV
      have := hCV.rows_strict _ _ _ _ hcb hc hlt
      exact absurd (lt_of_lt_of_le this hle) (lt_irrefl _)

/-! ## `LookupInner` -/

open CutGap in
/-- **`LookupInner` holds.** -/
theorem lookupInner : LookupInner := by
  intro s n D M out ρ R col t hS i hi0 hi v a hva b hab hlb v1 hraw
  have hb := hS.splice.build
  have hV := build_valid_of_success hb
  have hVR := build_valid_of_success hS.canon
  have hdat : ChainCorr.SpliceData s n D M out ρ R t := CopyShape.spliceData_of_setting hS
  have hva' := hva
  obtain ⟨y, es, j, hcy, hyx, hyb, hvc, hvi, hes, hj, ho⟩ := hva'
  have hes' : emitsT (ctxAt M R y i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 (y + (ρ.x0 - ρ.cr) * i))
      (official t.row) = .ok es := by rw [← hvc]; exact hes
  -- the step `a → b`
  obtain ⟨_, hb1, ca, cb, l, hca, hl, hbl, hcb, hbrow⟩ := hab
  have hlcr : ρ.cr < l.column := by rw [← hbl]; exact hlb
  -- the copied row `C` of `v`: the row of `a`, ascension test of `y`
  obtain ⟨C, cs, hcs, ⟨refx, clx, hnx, hrx⟩, hroot⟩ :=
    emitsT_cleanRoot hes' es[j] (List.getElem_mem hj) a false ho
  simp only [ctxAt] at hcs hnx hrx hroot
  obtain ⟨hac, ha1, hacell, harow⟩ := Classification.nodeAt_spec hcs
  simp only at hac ha1 hacell harow
  have hcsa : cs = ca := Option.some.inj (hacell.symm.trans hca)
  subst hcsa
  -- `C` is the row of the root top of its level-2 region, in a first item of level `≥ 2`
  obtain ⟨⟨qx, hqx, hqx2, hqxin⟩, ρr, ρc, hρ, hρrow⟩ :=
    emitsT_cleanTop hes' es[j] (List.getElem_mem hj) a false ho cs hacell
  simp only [ctxAt] at hρ
  -- the leg column ascends at `ρ`
  have hyl : l.column < y := by
    have := left_lt_of_valid hV hacell hl
    rw [hac] at this
    exact this
  obtain ⟨refl, cll, hnl, hrl⟩ := ascLeg hb hcy (by rw [← harow] at hnx; exact hnx) hrx
    (by rw [← harow] at hcs; exact hcs) hl hlcr
  have hascl : ascends (ctxAt M R l.column i ρ.cr (ρ.x0 - ρ.cr) ρ.x0
      (l.column + (ρ.x0 - ρ.cr) * i)) (some (ρr, ρc)) = .ok true := by
    apply ascends_of_reach (ref := refl) (cl := cll)
    · simp only [ctxAt]
      rw [hρrow]
      exact hnl
    · simpa [ctxAt] using hrl
  -- the emits of the column `l`
  obtain ⟨hlmem, esl, hesl⟩ := inner_emits hS hi0 hi hlcr (by omega)
  -- the non-cut emit of `b` in the column `l`
  obtain ⟨k0, hk0, hk0src, hk0nc⟩ := CopyShape.NoMA.inner_copyEmitted s n D M out ρ R col t hS
    i hi0 hi l.column esl hlcr (by omega) hesl b cb hbl hb1 hcb
  have hCτ : official cs.row < official t.row :=
    (lowerItems_below (official t.row) _ hqx).1 _ hqxin
  have hbC : official cb.row = official cs.row := by rw [hbrow]
  have hclean : esl[k0].2 = .clean b false := by
    have hlowl := emitsT_plainAsc (ctx := ctxAt M R l.column i ρ.cr (ρ.x0 - ρ.cr) ρ.x0
      (l.column + (ρ.x0 - ρ.cr) * i)) (τ := official t.row) hesl
    have hupl := emitsT_upperRow (ctx := ctxAt M R l.column i ρ.cr (ρ.x0 - ρ.cr) ρ.x0
      (l.column + (ρ.x0 - ρ.cr) * i)) (τ := official t.row) hesl
    generalize hE : esl[k0].2 = o at hk0src hk0nc
    cases o with
    | clean r' bb =>
        cases bb
        · have : r' = b := hk0src
          rw [this]
        · simp [cutOrigin] at hk0nc
    | upper r' =>
        exfalso
        have hr' : r' = b := hk0src
        rw [hr'] at hE
        have := hupl esl[k0] (List.getElem_mem hk0) b hE cb hcb
        rw [hbC] at this
        exact absurd hCτ (not_lt.mpr this)
    | plain r' =>
        exfalso
        have hr' : r' = b := hk0src
        rw [hr'] at hE
        rcases hlowl esl[k0] (List.getElem_mem hk0) b hE cb hcb with
          ⟨q1, hq1, hq11, hq1in⟩ | hP
        · have hq1in' : inRegion q1.1 q1.2.source (official cs.row) = true := by
            rw [← hbC]; exact hq1in
          have := Recon.JumpLaw.lowerItems_eq_of_common hqx hq1 hqxin hq1in'
          rw [this] at hqx2
          omega
        · have hρ' : topIn M ρ.cr 2 (official cb.row) = some (ρr, ρc) := by
            rw [hbC]; exact hρ
          have hρrow' : official ρc.row = official cb.row := by rw [hbC]; exact hρrow
          have hf : ascends (ctxAt M R l.column i ρ.cr (ρ.x0 - ρ.cr) ρ.x0
              (l.column + (ρ.x0 - ρ.cr) * i)) (some (ρr, ρc)) = .ok false :=
            hP b hE cb hcb ρr ρc hρ' hρrow'
          rw [hascl] at hf
          cases hf
  -- the copy node of `b`
  let v2 : Ref := ⟨l.column + (ρ.x0 - ρ.cr) * i, k0 + 1⟩
  have hv2 : CopyAt M R n ρ.cr ρ.x0 (official t.row) i v2 (.clean b false) :=
    ⟨l.column, esl, k0, hlcr, by omega, hlmem, rfl, rfl, hesl, hk0, hclean⟩
  -- both copies keep the row `C`
  have hRR : ChainCorr.SRCmp.RootRow M ρ.cr (official cs.row) :=
    ⟨(ρr, ρc), (topIn_spec hρ).1, hρrow⟩
  have hrowv : es[j].1.row = official cs.row := by
    have hcmp := ChainCorr.SRCmp.rootCmp s n D M out ρ R t hdat i hi y hyb es hes' es[j]
      (List.getElem_mem hj) cs (by rw [ho]; exact hacell) (official cs.row) hRR
    rw [ho] at hcmp
    exact (hcmp.1 rfl).2.1 rfl
  have hrowv2 : esl[k0].1.row = official cs.row := by
    have hcmp := ChainCorr.SRCmp.rootCmp s n D M out ρ R t hdat i hi l.column hlmem esl hesl
      esl[k0] (List.getElem_mem hk0) cb (by rw [hclean]; exact hcb) (official cs.row) hRR
    rw [hclean] at hcmp
    exact ((hcmp.1 rfl).2.1 hbC.symm)
  -- the cells in the output
  obtain ⟨y1, es1, j1, hj1, ho1, ⟨hvc1, hcy1, hyx1, _⟩, hvi1, hes1, cv, hcv, hcvrow, _⟩ :=
    copyAt_cell hS hi0 hi hva
  obtain ⟨y2, es2, j2, hj2, ho2, ⟨hvc2, hcy2, hyx2, _⟩, hvi2, hes2, cv2, hcv2, hcv2row, _⟩ :=
    copyAt_cell hS hi0 hi hv2
  have hy1 : y1 = y := by
    have := block_unique (x' := y) (i' := i) (by omega) hcy1 hyx1 hyb (by rw [← hvc1, hvc]) hi0
    exact this.2.symm
  subst hy1
  have he1 : es1 = es := by
    rw [hvc, hes'] at hes1
    exact (Except.ok.inj hes1).symm
  subst he1
  have hjj : j1 = j := by omega
  subst hjj
  have hy2 : y2 = l.column := by
    have := block_unique (x' := l.column) (i' := i) (by omega) hcy2 hyx2 hlmem (by rw [← hvc2]) hi0
    exact this.2.symm
  subst hy2
  have he2 : es2 = esl := by
    have e : v2.column = l.column + (ρ.x0 - ρ.cr) * i := rfl
    rw [e, hesl] at hes2
    exact (Except.ok.inj hes2).symm
  subst he2
  have hkk : j2 = k0 := by simp [v2] at hvi2; omega
  subst hkk
  -- the raw parent of `v` is the node of `φ(l)` at the row of `v`
  obtain ⟨ca', l', cv', v1', c1, hca', hl', hcv', hraw', hc1, hrow1, hham⟩ :=
    clean_parent_row boundaryRows hS hi0 hi hva
  have e1 : v1' = v1 := Option.some.inj (hraw'.symm.trans hraw)
  subst e1
  have e2 : cv' = cv := Option.some.inj (hcv'.symm.trans hcv)
  subst e2
  have e3 : ca' = cs := Option.some.inj (hca'.symm.trans hacell)
  subst e3
  have e4 : l' = l := Option.some.inj (hl'.symm.trans hl)
  subst e4
  have hv1col : v1'.column = l'.column + (ρ.x0 - ρ.cr) * i := by
    have := highestAtMost_column hham
    rw [this, mapColumn_of_ge (le_of_lt hlcr)]
  have hrows : c1.row = cv2.row := by
    rw [hrow1, hcvrow, hcv2row, hrowv, hrowv2]
  have hv1 : v1' = v2 := cell?_eq_of_index hVR (by rw [hv1col]) hc1 hcv2 hrows
  rw [hv1]
  exact hv2

/-! ## `LookupRoot` -/

/-- **`LookupRoot` from `StartRoot`.** -/
theorem lookupRoot_of_startRoot (hSR : ChainCorr.StartRoot) : LookupRoot := by
  intro s n D M out ρ R col t hS i hi0 hi v a hva b hab hbc v1 hraw k m'' hst
  have hV := build_valid_of_success hS.splice.build
  obtain ⟨cu, ref, co, l, hcu, hrefl, hco, hl, hrefc⟩ := copyAt_left hS hi0 hi hva
  obtain ⟨ca', l', cv', v1', c1, hca', hl', hcv', hraw', hc1, _, hham⟩ :=
    clean_parent_row boundaryRows hS hi0 hi hva
  have e1 : v1' = v1 := Option.some.inj (hraw'.symm.trans hraw)
  subst e1
  have e2 : cv' = cu := Option.some.inj (hcv'.symm.trans hcu)
  subst e2
  have e3 : ca' = co := Option.some.inj (hca'.symm.trans hco)
  subst e3
  have e4 : l' = l := Option.some.inj (hl'.symm.trans hl)
  subst e4
  obtain ⟨_, hb1, ca, cb, l2, hca, hl2, hbl, hcb, hbrow⟩ := hab
  have e5 : ca = ca' := Option.some.inj (hca.symm.trans hco)
  subst e5
  have e6 : l2 = l' := Option.some.inj (hl2.symm.trans hl)
  subst e6
  have hpa : highestAtMost M l2.column ca.row = some b := by
    rw [← hbl, ← hbrow]
    exact hAM_self hV (by omega) hcb
  have hva' := hva
  obtain ⟨y, es, j, hcy, hyx, hyb, hvc, hvi, hes, hj, ho⟩ := hva'
  have hSite := siteOf hS hi0 hi hcy hyx hyb hvc hes
  have hvref : v = ⟨v.column, j + 1⟩ := by
    cases v
    simp only at hvi ⊢
    rw [hvi]
  have hL : ChainCorr.Legs M R v.column j es[j].2 cv' ca ref l2 v1' b c1 cb := by
    refine ⟨by rw [← hvref]; exact hcu, hrefl, by rw [ho]; exact hco, hl, ?_, hpa, hc1, hcb⟩
    rw [hrefc]
    exact hham
  exact hSR s n D M out ρ R t v.column y i es hSite j hj (by rw [ho]; rfl) cv' ca ref l2 v1' b c1 cb
    hL (by rw [← hbl]; exact hbc) k m'' (by rw [hbrow, Row.jump_self]; exact Nat.zero_le _) hst

/-- **`LookupRoot` from `BoundaryChain`** (`OriginReach` is proved, `SRFixPa.originReach`). -/
theorem lookupRoot_of_boundaryChain (hBC : ChainCorr.BoundaryChain) : LookupRoot :=
  lookupRoot_of_startRoot (ChainCorr.startRoot_of_parts hBC ChainCorr.SRFixPa.originReach)

/-! ## `CleanLookup` -/

/-- **`CleanLookup` from `StartRoot`.** -/
theorem cleanLookup_of_startRoot (hSR : ChainCorr.StartRoot) : CleanLookup :=
  cleanLookup_of_lookups lookupInner (lookupRoot_of_startRoot hSR)

/-- **`CleanLookup` from `BoundaryChain`.** -/
theorem cleanLookup_of_boundaryChain (hBC : ChainCorr.BoundaryChain) : CleanLookup :=
  cleanLookup_of_lookups lookupInner (lookupRoot_of_boundaryChain hBC)

/-! ## Block by block: `LookupRoot` in block `1` -/

/-- `ChainCorr.BoundaryChain` at one block `i`. -/
def BoundaryChainAt (i : Nat) : Prop :=
  ∀ s n D M out ρ R t, ChainCorr.SpliceData s n D M out ρ R t → 0 < i → i < n + 1 →
    ∀ esB, ChainCorr.blockEmits M R ρ.cr ρ.x0 (official t.row) (i - 1) ρ.x0 = .ok esB →
      ∀ k (hk : k < esB.length) kk (m : Ref), m.column < ρ.cr →
        ScaleReach M kk esB[k].2.src m →
        ScaleReach R kk ⟨ρ.x0 + (ρ.x0 - ρ.cr) * (i - 1), k + 1⟩ m

theorem boundaryChainAt_of (h : ChainCorr.BoundaryChain) (i : Nat) : BoundaryChainAt i :=
  fun s n D M out ρ R t hd hi0 hi => h s n D M out ρ R t hd i hi0 hi

/-- **`BoundaryChain` at the block `1`** (`SRParts.boundaryChain_one`). -/
theorem boundaryChainAt_one : BoundaryChainAt 1 := by
  intro s n D M out ρ R t hd _ _ esB hes k hk kk m hm hr
  exact ChainCorr.SRParts.boundaryChain_one hd hes hk hm hr

/-- `ChainCorr.StartRoot` at the nodes of one block `i` (the proof of `startRoot_of_parts`, with
`BoundaryChain` used only at the block `i`). -/
theorem startRoot_at {i : Nat} (hB : BoundaryChainAt i) :
    ∀ s n D M out ρ R t X x es, ChainCorr.Site s n D M out ρ R t X x i es →
    ∀ j (hj : j < es.length), cutOrigin es[j].2 = false →
    ∀ cu cv ref l pe pa cpe cpa, ChainCorr.Legs M R X j es[j].2 cu cv ref l pe pa cpe cpa →
      l.column = ρ.cr → ∀ k m'', Row.jump cv.row cpa.row ≤ k → MStep M k pa m'' →
        ScaleReach R k pe m'' := by
  intro s n D M out ρ R t X x es hS j hj hnc cu cv ref l pe pa cpe cpa hL heq kk m'' hk hst
  have hdat := hS.data
  obtain ⟨col', t', hcol', ht', _, hcrx, hinv⟩ := spliceCase_data hS.splice hS.run
  have htt : t' = t := by
    obtain ⟨col, hcol, ht⟩ := hS.last
    have : col' = col := Option.some.inj (hcol'.symm.trans hcol)
    subst this
    exact Option.some.inj (ht'.symm.trans ht)
  subst t'
  have hipos := hS.iPos
  have himg := ChainCorr.leg_image hS hj hL
  rw [heq, mapColumn_of_ge (le_refl _), ChainCorr.boundary_eq hcrx hipos] at himg
  obtain ⟨hpecol, hpe0, colB, hcolB, hpeB, _, _⟩ := highestAtMost_spec hL.hpe
  obtain ⟨hBsz, _⟩ := column_of_getElem? hcolB
  have hB0 : ρ.x0 ≤ ref.column := by rw [himg]; omega
  obtain ⟨i', x', hi', hx', hBeq, hcopyB⟩ := hinv.2.2 ref.column hBsz hB0
  obtain ⟨hii, hxx⟩ := ChainCorr.block_unique_boundary hcrx hx' (by rw [← himg]; exact hBeq)
  subst i' x'
  have hcolB' : R[ref.column]? = some R[ref.column] := Array.getElem?_eq_getElem hBsz
  have hcc : colB = R[ref.column] := Option.some.inj (hcolB.symm.trans hcolB')
  obtain ⟨esB, hesB, _⟩ := copyColumn_emitsT hcopyB
  obtain ⟨hszB, _⟩ := ChainCorr.cells_of_copy hcolB' hcopyB hesB
  have hbl : ChainCorr.blockEmits M R ρ.cr ρ.x0 (official t.row) (i - 1) ρ.x0 = .ok esB := by
    have h' : ρ.x0 + (ρ.x0 - ρ.cr) * (i - 1) = ref.column := himg.symm
    simp only [ChainCorr.blockEmits, h']
    exact hesB
  have hksl : pe.index - 1 < esB.length := by
    have : pe.index < colB.size := hpeB
    rw [hcc, hszB] at this
    omega
  have hpeidx : pe.index = pe.index - 1 + 1 := by omega
  have hreachM := ChainCorr.SRFixPa.originReach s n D M out ρ R t X x i es hS j hj hnc cu cv ref
    l pe pa cpe cpa hL heq esB hbl (pe.index - 1) hksl hpeidx kk m'' hk hst
  have hpacol : pa.column = ρ.cr := by
    rw [(highestAtMost_spec hL.hpa).1, heq]
  have hm'' : m''.column < ρ.cr := hpacol ▸ hst.column_lt
  have hreachR := hB s n D M out ρ R t hdat hipos hS.iLt esB hbl (pe.index - 1) hksl kk m''
    hm'' hreachM
  have hpe : pe = ⟨ρ.x0 + (ρ.x0 - ρ.cr) * (i - 1), pe.index - 1 + 1⟩ :=
    ChainCorr.ref_eq_of (by rw [hpecol, himg]) hpeidx
  rw [hpe]
  exact hreachR

/-- `LookupRoot` at the nodes of one block `i`. -/
def LookupRootAt (i : Nat) : Prop :=
  ∀ s n D M out ρ R (col : Column) (t : Cell), Setting s n D M out ρ R col t →
    0 < i → i < n + 1 → ∀ v a,
      CopyAt M R n ρ.cr ρ.x0 (official t.row) i v (.clean a false) →
      ∀ b, GenStep M ρ.cr a b → b.column = ρ.cr →
      ∀ v1, rawParent R v = some v1 →
        ∀ k m'', MStep M k b m'' → ScaleReach R k v1 m''

/-- **`LookupRoot` at the block `i` from `BoundaryChain` at the block `i`.** -/
theorem lookupRootAt_of {i : Nat} (hB : BoundaryChainAt i) : LookupRootAt i := by
  intro s n D M out ρ R col t hS hi0 hi v a hva b hab hbc v1 hraw k m'' hst
  have hV := build_valid_of_success hS.splice.build
  obtain ⟨cu, ref, co, l, hcu, hrefl, hco, hl, hrefc⟩ := copyAt_left hS hi0 hi hva
  obtain ⟨ca', l', cv', v1', c1, hca', hl', hcv', hraw', hc1, _, hham⟩ :=
    clean_parent_row boundaryRows hS hi0 hi hva
  have e1 : v1' = v1 := Option.some.inj (hraw'.symm.trans hraw)
  subst e1
  have e2 : cv' = cu := Option.some.inj (hcv'.symm.trans hcu)
  subst e2
  have e3 : ca' = co := Option.some.inj (hca'.symm.trans hco)
  subst e3
  have e4 : l' = l := Option.some.inj (hl'.symm.trans hl)
  subst e4
  obtain ⟨_, hb1, ca, cb, l2, hca, hl2, hbl, hcb, hbrow⟩ := hab
  have e5 : ca = ca' := Option.some.inj (hca.symm.trans hco)
  subst e5
  have e6 : l2 = l' := Option.some.inj (hl2.symm.trans hl)
  subst e6
  have hpa : highestAtMost M l2.column ca.row = some b := by
    rw [← hbl, ← hbrow]
    exact hAM_self hV (by omega) hcb
  have hva' := hva
  obtain ⟨y, es, j, hcy, hyx, hyb, hvc, hvi, hes, hj, ho⟩ := hva'
  have hSite := siteOf hS hi0 hi hcy hyx hyb hvc hes
  have hvref : v = ⟨v.column, j + 1⟩ := by
    cases v
    simp only at hvi ⊢
    rw [hvi]
  have hL : ChainCorr.Legs M R v.column j es[j].2 cv' ca ref l2 v1' b c1 cb := by
    refine ⟨by rw [← hvref]; exact hcu, hrefl, by rw [ho]; exact hco, hl, ?_, hpa, hc1, hcb⟩
    rw [hrefc]
    exact hham
  exact startRoot_at hB s n D M out ρ R t v.column y es hSite j hj (by rw [ho]; rfl) cv' ca ref l2
    v1' b c1 cb hL (by rw [← hbl]; exact hbc) k m'' (by rw [hbrow, Row.jump_self]; exact Nat.zero_le _)
    hst

/-- **`LookupRoot` holds in the block `1`** (no hypothesis). -/
theorem lookupRootAt_one : LookupRootAt 1 := lookupRootAt_of boundaryChainAt_one

/-- `LookupRoot` is `LookupRootAt i` for every block `i`. -/
theorem lookupRoot_of_at (h : ∀ i, 2 ≤ i → LookupRootAt i) : LookupRoot := by
  intro s n D M out ρ R col t hS i hi0 hi
  rcases Nat.lt_or_ge i 2 with h1 | h2
  · obtain rfl : i = 1 := by omega
    exact lookupRootAt_one s n D M out ρ R col t hS hi0 hi
  · exact h i h2 s n D M out ρ R col t hS hi0 hi

/-- **`LookupRoot` from `BoundaryChain` at the blocks `i ≥ 2`.** -/
theorem lookupRoot_of_boundaryChainAt (h : ∀ i, 2 ≤ i → BoundaryChainAt i) : LookupRoot :=
  lookupRoot_of_at fun i hi => lookupRootAt_of (h i hi)

/-- **`CleanLookup` from `BoundaryChain` at the blocks `i ≥ 2`.** -/
theorem cleanLookup_of_boundaryChainAt (h : ∀ i, 2 ≤ i → BoundaryChainAt i) : CleanLookup :=
  cleanLookup_of_lookups lookupInner (lookupRoot_of_boundaryChainAt h)

/-! ## `StepInner`: what is left of the clean part -/

/-- **`StepInner` from `LegLookup`, `BumpCopyLower` and `BoundaryChain` at the blocks `i ≥ 2`**:
the clean statements `CleanNext`, `CleanLookup`, `CleanParent` are no longer hypotheses
(`CleanNext` proved, `CleanLookup` from `BoundaryChainAt`, `CleanParent` replaced by the proved
`CleanParentReach`); `CopyEmitted`, `CopyFirst` are proved (`CopyShapeNoMA.lean`). -/
theorem stepInner_of_legLookup (hLeg : LegLookup) (hBump : BumpCopyLower)
    (hBC : ∀ i, 2 ≤ i → BoundaryChainAt i) : StepInner :=
  stepInner_of_rest_noCP CopyShape.NoMA.inner_copyEmitted CopyShape.NoMA.inner_copyFirst hLeg hBump
    (cleanNext_of_boundaryRows boundaryRows) (cleanLookup_of_boundaryChainAt hBC)

end OmegaY.Official.Classification.Proofs.ChainCorr.Inner.CleanRoot

#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.Inner.CleanRoot.lookupInner
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.Inner.CleanRoot.lookupRoot_of_startRoot
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.Inner.CleanRoot.lookupRoot_of_boundaryChain
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.Inner.CleanRoot.cleanLookup_of_startRoot
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.Inner.CleanRoot.cleanLookup_of_boundaryChain
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.Inner.CleanRoot.lookupRootAt_one
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.Inner.CleanRoot.cleanLookup_of_boundaryChainAt
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.Inner.CleanRoot.stepInner_of_legLookup
