/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/ParentBelowLowerProfile.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.ParentBelow
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.KeyWitness
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Regions
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.KeyBlockZero

set_option backward.do.legacy false

/-!
# `LowerParentBelowHolds`: the profile of a block

`LowerParentBelowHolds` (`ParentBelow.lean`) asks, in a new column `X` of a successful run,
for consecutive nodes `u`, `u⁺` with `row u < τ` and `row u⁺ = bump (row u) e`, `e ≥ 1`,
that the column `q` of the parent `p = π(u⁺)` has no node strictly between `row u` and
`row u⁺` (`parentBelow_of_gap`). It is proved from statements about the copies made by one
block `i ≥ 1` (the *profile* of the block, this file) and from the canonical shape of `M(s)`
(`shadow`, this file):

* `ParentBelowLowerCore.lean`: two comparisons inside a block (`sameRow`, `legOrder`);
* `ParentBelowLowerCols.lean`: the columns of the output read through the traced copies,
  and block `0` (`ColData.emitted0`, from `JumpLaw.lower_id`);
* `ParentBelowLowerMain.lean`: the case analysis and `lowerParentBelowHolds_of_profile`;
* `ParentBelowLowerLeg.lean`: `LegRight` from `LegBelowTop` (`ChainCorrStartLegJump.lean`),
  and `lowerParentBelowHolds_of_parts`.

## The copies of a block

Fix a run with root column `cr`, last column `x₀`, width `w = x₀ - cr` and top row `τ`.
For a block `i` and a source column `y ∈ [cr, x₀]`, the traced lower part
`lowerT ctx τ` of a context `ctx` of block `i` with `ctx.x = y` (`BCtx`) lists the copies
of the nodes of `y` below `τ`, each with its origin (a node of `y`). For `y > cr` and a
column that exists, this is the lower part of the column `y + w·i` of the output. For
`y = cr` (and `y = x₀` in the last block) it is a copy the rule does not make; `lowerT`
reads the output only at the boundary column `cr + w·i`, which `BCtx` fixes. The boundary
column (the copy of `x₀` made by block `i - 1`) has the rows of the copy of `cr`
(`Boundary`).

A copy is *cut* when it is a gap copy (`Origin.clean _ true`). The numerical tests
(`reference/official/parent-below-lower.cjs`) show a simple profile, the same in every column
of a block `i ≥ 1` (all statements below are open and are stated for `i ≥ 1` only):

* `NonCutOrder`: the row of a non-cut copy depends only on the row of its origin, in an
  increasing way (`CopyOrder` of `ChainCorrStartCopy.lean` is the case of two columns of
  the block; here `y` may also be `cr`, or `x₀` in the last block);
* `CutBetween`: a gap copy of an origin `C` lies strictly above the non-cut copies of
  origins `≤ C` and strictly below those of origins `> C`;
* `CutOrder`: gap copies of a lower origin lie below gap copies of a higher origin;
* `CutLeg`: if `ℓ` is the leg column of a node `(x, a)` of `M(s)` (`x > cr`, the bottom node
  included), every gap copy of an origin `C < a` made in the copy of `ℓ` has a gap copy at
  the same row made in the copy of `x` (and for `C = a` when the copy of `x` makes a gap
  copy of `(x, a)` at all);
* `Emitted`: in the copy of `y > cr`, every node of `y` below `τ` is the origin of a
  non-cut copy (`CopyEmitted` of `ChainCorrStartCopy.lean` is the case `cr < y < x₀`);
* `Lift`: a non-cut copy is not below its origin;
* `LegRight`: in the copy of `y > cr`, every emitted leg column is at least `cr` (implied
  by `LegBelowTop` in `ParentBelowLowerLeg.lean`). **`LegRight` is false**, and so is
  `LegBelowTop` (`LegBelowTopFalse.lean`): in `(1,2,4,8,10,8)[1]`, block `1`, the copy of
  `y = 4` emits a lower node with leg column `1 < c_r = 2` (`not_legRight_of_check` in
  `ParentBelowLowerLeg.lean`). So `Profile` is false, and `caseLower` misses the case
  `ℓ < c_r` in blocks `i ≥ 1`;
* `Boundary`: every row below `τ` of the boundary column `cr + w·i` is the row of a copy
  made by the hypothetical copy of `cr` in block `i`.

In block `0` the copies are the identity (`emitsT_block0`) and every node of `x₀` below `τ`
is copied (`ColData.emitted0`); nothing is assumed there.
-/

namespace OmegaY.Official.Recon.LowerPB

open Canonical Expansion Geometry Frame Classification Reserve

/-! ## The profile of a block -/

/-- A gap copy. -/
def cutO : Origin → Bool
  | .clean _ b => b
  | _ => false

/-- A copy context of block `i` of a run with root column `cr` and last column `x₀`: the
source column `ctx.x ∈ [cr, x₀]`, and the result agrees with `R` at the boundary column
`cr + w·i`. -/
structure BCtx (M R : Mountain) (cr x0 i : Nat) (ctx : Context) : Prop where
  source : ctx.source = M
  root : ctx.rootColumn = cr
  width : ctx.width = x0 - cr
  last : ctx.lastColumn = x0
  block : ctx.block = i
  xge : cr ≤ ctx.x
  xle : ctx.x ≤ x0
  bnd : ctx.result[cr + (x0 - cr) * i]? = R[cr + (x0 - cr) * i]?

/-- (open) Non-cut copies: the row depends only on the row of the origin, increasingly. -/
def NonCutOrder : Prop :=
  ∀ s n R, Official.expandDiagram s n = .ok R → ∀ M t root, Top s M t root →
    ∀ i, 1 ≤ i → i ≤ n → ∀ ctx ctx', BCtx M R root.column (M.size - 1) i ctx →
      BCtx M R root.column (M.size - 1) i ctx' →
      ∀ es es', lowerT ctx (official t.row) = .ok es → lowerT ctx' (official t.row) = .ok es' →
        ∀ e ∈ es, ∀ e' ∈ es', cutO e.2 = false → cutO e'.2 = false →
          ∀ c c', cell? M e.2.src = some c → cell? M e'.2.src = some c' →
            (c.row < c'.row → e.1.row < e'.1.row) ∧ (c.row = c'.row → e.1.row = e'.1.row)

/-- (open) A gap copy of `C` lies above the non-cut copies of origins `≤ C` and below those of
origins `> C`. -/
def CutBetween : Prop :=
  ∀ s n R, Official.expandDiagram s n = .ok R → ∀ M t root, Top s M t root →
    ∀ i, 1 ≤ i → i ≤ n → ∀ ctx ctx', BCtx M R root.column (M.size - 1) i ctx →
      BCtx M R root.column (M.size - 1) i ctx' →
      ∀ es es', lowerT ctx (official t.row) = .ok es → lowerT ctx' (official t.row) = .ok es' →
        ∀ e ∈ es, ∀ e' ∈ es', cutO e.2 = true → cutO e'.2 = false →
          ∀ c c', cell? M e.2.src = some c → cell? M e'.2.src = some c' →
            (c'.row ≤ c.row → e'.1.row < e.1.row) ∧ (c.row < c'.row → e.1.row < e'.1.row)

/-- (open) Gap copies of a lower origin lie below gap copies of a higher origin. -/
def CutOrder : Prop :=
  ∀ s n R, Official.expandDiagram s n = .ok R → ∀ M t root, Top s M t root →
    ∀ i, 1 ≤ i → i ≤ n → ∀ ctx ctx', BCtx M R root.column (M.size - 1) i ctx →
      BCtx M R root.column (M.size - 1) i ctx' →
      ∀ es es', lowerT ctx (official t.row) = .ok es → lowerT ctx' (official t.row) = .ok es' →
        ∀ e ∈ es, ∀ e' ∈ es', cutO e.2 = true → cutO e'.2 = true →
          ∀ c c', cell? M e.2.src = some c → cell? M e'.2.src = some c' →
            c.row < c'.row → e.1.row < e'.1.row

/-- (open) If `ℓ = ctx'.x` is the leg column of the node `(x, k)` of `M(s)` (`x = ctx.x`), every
gap copy made by the copy of `ℓ` of an origin below `(x, k)` is made by the copy of `x`; so is
every gap copy of an origin at the row of `(x, k)`, when the copy of `x` makes a gap copy of
`(x, k)`. -/
def CutLeg : Prop :=
  ∀ s n R, Official.expandDiagram s n = .ok R → ∀ M t root, Top s M t root →
    ∀ i, 1 ≤ i → i ≤ n → ∀ ctx ctx', BCtx M R root.column (M.size - 1) i ctx →
      BCtx M R root.column (M.size - 1) i ctx' → root.column < ctx.x →
      ∀ k cp r, 1 ≤ k → cell? M ⟨ctx.x, k⟩ = some cp → cp.left = some r → r.column = ctx'.x →
      ∀ es es', lowerT ctx (official t.row) = .ok es → lowerT ctx' (official t.row) = .ok es' →
        ∀ e' ∈ es', cutO e'.2 = true → ∀ c', cell? M e'.2.src = some c' →
          (c'.row < cp.row ∨
            (c'.row = cp.row ∧ ∃ e ∈ es, cutO e.2 = true ∧ e.2.src = ⟨ctx.x, k⟩)) →
          ∃ e ∈ es, cutO e.2 = true ∧ e.1.row = e'.1.row

/-- (open) In the copy of `y > cr`, every node of `y` below `τ` is the origin of a non-cut
copy. -/
def Emitted : Prop :=
  ∀ s n R, Official.expandDiagram s n = .ok R → ∀ M t root, Top s M t root →
    ∀ i, 1 ≤ i → i ≤ n → ∀ ctx, BCtx M R root.column (M.size - 1) i ctx → root.column < ctx.x →
      ∀ es, lowerT ctx (official t.row) = .ok es →
        ∀ k c, 1 ≤ k → cell? M ⟨ctx.x, k⟩ = some c → official c.row < official t.row →
          ∃ e ∈ es, cutO e.2 = false ∧ e.2.src = ⟨ctx.x, k⟩

/-- (open) A non-cut copy is not below its origin. -/
def Lift : Prop :=
  ∀ s n R, Official.expandDiagram s n = .ok R → ∀ M t root, Top s M t root →
    ∀ i, 1 ≤ i → i ≤ n → ∀ ctx, BCtx M R root.column (M.size - 1) i ctx →
      ∀ es, lowerT ctx (official t.row) = .ok es →
        ∀ e ∈ es, cutO e.2 = false → ∀ c, cell? M e.2.src = some c → official c.row ≤ e.1.row

/-- In the copy of `y > cr`, every emitted leg column is at least `cr` (follows from
`LegBelowTop`: `legRight_of_legBelowTop`). **False**: see `not_legRight_of_check`. -/
def LegRight : Prop :=
  ∀ s n R, Official.expandDiagram s n = .ok R → ∀ M t root, Top s M t root →
    ∀ i, 1 ≤ i → i ≤ n → ∀ ctx, BCtx M R root.column (M.size - 1) i ctx → root.column < ctx.x →
      ∀ es, lowerT ctx (official t.row) = .ok es →
        ∀ e ∈ es, ∀ l, e.1.leftColumn = some l → root.column ≤ l

/-- (open) The rows below `τ` of the boundary column `cr + w·i` (`i ≥ 1`) are rows of the
copy of `cr` in block `i`. -/
def Boundary : Prop :=
  ∀ s n R, Official.expandDiagram s n = .ok R → ∀ M t root, Top s M t root →
    ∀ i, 1 ≤ i → i ≤ n →
      ∃ es, lowerT ⟨M, R, root.column, i, root.column, M.size - 1 - root.column, M.size - 1⟩
          (official t.row) = .ok es ∧
        ∀ (hB : root.column + (M.size - 1 - root.column) * i < R.size) k
          (hk : k < R[root.column + (M.size - 1 - root.column) * i].size), 1 ≤ k →
          official R[root.column + (M.size - 1 - root.column) * i][k].row < official t.row →
          ∃ e ∈ es, e.1.row = official R[root.column + (M.size - 1 - root.column) * i][k].row

/-- The profile of a block. -/
structure Profile : Prop where
  nonCutOrder : NonCutOrder
  cutBetween : CutBetween
  cutOrder : CutOrder
  cutLeg : CutLeg
  emitted : Emitted
  lift : Lift
  legRight : LegRight
  boundary : Boundary

/-! ## Arithmetic -/

theorem repr_unique' {w a b i j : Nat} (ha : 0 < a) (ha' : a ≤ w) (hb : 0 < b) (hb' : b ≤ w)
    (h : a + w * i = b + w * j) : a = b := by
  rcases Nat.lt_trichotomy i j with hij | rfl | hij
  · have : w * (i + 1) ≤ w * j := Nat.mul_le_mul_left w hij
    rw [Nat.mul_succ] at this
    omega
  · omega
  · have : w * (j + 1) ≤ w * i := Nat.mul_le_mul_left w hij
    rw [Nat.mul_succ] at this
    omega

/-! ## The canonical shadow -/

/-- **Same-row shadow of a leg.** In a canonical mountain, let the node `(c, k)` have its left
endpoint in the column `ℓ`. Every real node of `ℓ` with row at most the row of `(c, k)` has a
real node of the same row in the column `c`. -/
theorem shadow {s : List Nat} {M : Mountain} (hM : Canonical.build s = .ok M)
    {c k : Nat} {co : Cell} (hk : 1 ≤ k) (hco : cell? M ⟨c, k⟩ = some co)
    {r : Ref} (hl : co.left = some r) {k' : Nat} {cw : Cell} (hk' : 1 ≤ k')
    (hcw : cell? M ⟨r.column, k'⟩ = some cw) (hle : cw.row ≤ co.row) :
    ∃ k'' cv, 1 ≤ k'' ∧ cell? M ⟨c, k''⟩ = some cv ∧ cv.row = cw.row := by
  rcases eq_or_lt_of_le hle with heq | hlt
  · exact ⟨k, co, hk, hco, heq.symm⟩
  have hN := build_normal_of_legal (build_success_legal hM) hM
  have hO := hN.toOrdered
  obtain ⟨hc, hki, hkc⟩ := Proofs.canon_cell?_some_iff.mp hco
  obtain ⟨hrc, hk'i, hk'c⟩ := Proofs.canon_cell?_some_iff.mp hcw
  let no : (Frame.ofMountain M).Node := ⟨⟨c, hc⟩, ⟨k, hki⟩⟩
  let nw : (Frame.ofMountain M).Node := ⟨⟨r.column, hrc⟩, ⟨k', hk'i⟩⟩
  have hnw : Frame.Real nw := hk'
  have hnoc : (Frame.ofMountain M).cell no = co := hkc
  have hnwc : (Frame.ofMountain M).cell nw = cw := hk'c
  rcases Nat.lt_or_ge 1 k with hk2 | hk1
  · -- `k ≥ 2`: the edge below `(c, k)` and its canonical parent
    have hki' : k < M[c].size := hki
    let nu : (Frame.ofMountain M).Node := ⟨⟨c, hc⟩, ⟨k - 1, by change k - 1 < M[c].size; omega⟩⟩
    have hnu : Frame.Real nu := by show 0 < k - 1; omega
    have hup : (Frame.ofMountain M).upper nu = some no :=
      ControlProof.upper_eq_of_index rfl (show k = k - 1 + 1 by omega)
    have hleft : ((Frame.ofMountain M).cell no).left = some r := by rw [hnoc]; exact hl
    obtain ⟨np, hlk, _, _⟩ := hO.stored_valid no r hleft
    have hnp : Frame.ref np = r := Frame.lookup_spec hlk
    have hraw : (Frame.ofMountain M).rawParent nu = some np :=
      Frame.rawParent_eq_of_upper_left hup (by rw [hnp]; exact hleft)
    obtain ⟨_, hmax⟩ := Proofs.Normal.rawParent_highest_below hN hnu hup hraw
    have hnpc : np.1.val = r.column := by rw [← hnp]; rfl
    have hw1 : nw.1 = np.1 := Fin.ext (by simp [nw, hnpc])
    have hwle : nw.2.val ≤ np.2.val :=
      hmax nw hw1 (by
        show ((Frame.ofMountain M).cell nw).row < ((Frame.ofMountain M).cell no).row
        rw [hnwc, hnoc]
        exact hlt)
    have hwh : (Frame.ofMountain M).height nw ≤ (Frame.ofMountain M).height np :=
      ControlProof.height_le_of_index hO hw1 hwle
    have hP : (Frame.ofMountain M).P nu = some np := (hN.rawParent_eq_P hnu).symm.trans hraw
    obtain ⟨v, hv, hvc, _, hvh, _⟩ := P_rowShadow hN hP nw hnw hw1 hwh
    refine ⟨v.2.val, (Frame.ofMountain M).cell v, hv, ?_, ?_⟩
    · have hvc' : v.1.val = c := by rw [hvc]
      obtain ⟨vc, vi⟩ := v
      simp only at hvc'
      subst hvc'
      exact ControlProof.cell?_ref ⟨vc, vi⟩
    · exact hvh.trans (congrArg Cell.row hnwc)
  · -- `k = 1`: the bottom node; the rows of real nodes are at least `1`
    have hk1' : k = 1 := by omega
    subst hk1'
    have hbot : co.row = 1 := by
      rw [← hnoc]
      exact hO.bottom_row ⟨c, hc⟩ hki
    have h1 : (1 : Row) ≤ cw.row := by
      rw [← hnwc]
      exact Frame.one_le_height hO hnw
    rw [hbot] at hlt
    exact absurd (lt_of_le_of_lt h1 hlt) (lt_irrefl _)

/-! ## The traced lower and upper parts -/

theorem lowerT_mem {ctx : Context} {τ : Row} {lo : List (Emit × Origin)}
    (h : lowerT ctx τ = .ok lo) {e : Emit × Origin} (he : e ∈ lo) :
    ∃ p ∈ lowerItems τ, ∃ out, runItemT ctx p.1 p.2 = .ok out ∧ e ∈ out := by
  unfold lowerT at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i outs houts
    cases h
    obtain ⟨out, hout, heo⟩ := List.mem_flatten.mp he
    obtain ⟨q, hq, hqo⟩ := mem_of_mapM houts hout
    exact ⟨q, hq, out, hqo, heo⟩

/-- A lower copy is not an upper copy, and its origin is a real node of the source column. -/
theorem lowerT_good {ctx : Context} {τ : Row} {lo : List (Emit × Origin)}
    (h : lowerT ctx τ = .ok lo) : ∀ e ∈ lo, Good ctx e ∧ e.2.isUpper = false := by
  intro e he
  obtain ⟨p, _, out, hout, heo⟩ := lowerT_mem h he
  exact ⟨runItemT_good ctx p.1 p.2 out hout e heo, runItemT_not_upper ctx p.1 p.2 out hout e heo⟩

/-- The origin of a lower copy is a node of the source column below `τ`. -/
theorem lowerT_below {ctx : Context} {τ : Row} {lo : List (Emit × Origin)}
    (h : lowerT ctx τ = .ok lo) :
    ∀ e ∈ lo, ∃ cv, cell? ctx.source e.2.src = some cv ∧ official cv.row < τ := by
  intro e he
  obtain ⟨p, hp, out, hout, heo⟩ := lowerT_mem h he
  exact runItemT_below ctx τ p.1 p.2 out (lowerItems_below τ p hp) hout e heo

/-- The source of a lower copy: a real node of the source column with a cell, and its emitted
leg is the column of the left endpoint of that cell (none only for a copy of the bottom row). -/
theorem lowerT_src {ctx : Context} {τ : Row} {lo : List (Emit × Origin)}
    (h : lowerT ctx τ = .ok lo) {e : Emit × Origin} (he : e ∈ lo) :
    ∃ k cv, e.2.src = ⟨ctx.x, k⟩ ∧ 1 ≤ k ∧ cell? ctx.source ⟨ctx.x, k⟩ = some cv ∧
      ((∃ l : Ref, cv.left = some l ∧ e.1.leftColumn = some l.column) ∨
        (e.1.leftColumn = none ∧ official cv.row = 0)) := by
  obtain ⟨⟨hcol, hidx, cv, hcv, hleft⟩, hup⟩ := lowerT_good h e he
  rw [hup] at hcol
  simp only [Bool.false_eq_true, if_false] at hcol
  have hsrc : e.2.src = ⟨ctx.x, e.2.src.index⟩ := by
    rw [← hcol]
  refine ⟨e.2.src.index, cv, hsrc, hidx, by rw [← hsrc]; exact hcv, ?_⟩
  rcases hleft with hl | ⟨hn, h0, _⟩
  · exact Or.inl hl
  · exact Or.inr ⟨hn, h0⟩

/-- The rows of the lower copies of a column of a run are below `τ`. -/
theorem lowerT_rows_lt {s : List Nat} {ctx : Context} {t : Cell} {root : Ref}
    (hctx : RunCtx s ctx t root) {lo : List (Emit × Origin)}
    (h : lowerT ctx (official t.row) = .ok lo) : ∀ e ∈ lo, e.1.row < official t.row := by
  intro e he
  obtain ⟨p, hp, out, hout, heo⟩ := lowerT_mem h he
  obtain ⟨hIt, hst, hd1, _⟩ := RowLaw.lower_itemOK (ctx := ctx) hp
  have hrun : runItem ctx p.1 p.2 = .ok (out.map Prod.fst) := by
    rw [← runItemT_fst ctx p.1 p.2, hout]
    rfl
  have hg := RowLaw.runItem_good hctx p.1 hd1 p.2 hIt _ hrun
  have hreg := hg.1.2.1 e.1 (List.mem_map_of_mem heo)
  exact hIt.below e.1.row (by rw [hst]; exact hreg)

theorem emitsT_split {ctx : Context} {τ : Row} {es : List (Emit × Origin)}
    (h : emitsT ctx τ = .ok es) :
    ∃ lo us, lowerT ctx τ = .ok lo ∧ upperT ctx τ = .ok us ∧ es = lo ++ us := by
  unfold emitsT at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i lo hlo
    split at h
    · cases h
    · rename_i us hus
      cases h
      exact ⟨lo, us, hlo, hus, rfl⟩

/-- The upper copies: the nodes of the column `x'` at or above `τ`, with their rows and legs. -/
theorem upperT_spec {ctx : Context} {τ : Row} {us : List (Emit × Origin)}
    (h : upperT ctx τ = .ok us) :
    (∀ e ∈ us, ∃ k c, 1 ≤ k ∧ cell? ctx.source ⟨upperColumn ctx, k⟩ = some c ∧
      e.2 = .upper ⟨upperColumn ctx, k⟩ ∧ e.1.row = official c.row ∧ τ ≤ official c.row ∧
      ∃ l : Ref, c.left = some l ∧ e.1.leftColumn = some l.column) ∧
    (∀ k c, 1 ≤ k → cell? ctx.source ⟨upperColumn ctx, k⟩ = some c → τ ≤ official c.row →
      ∃ e ∈ us, e.1.row = official c.row) := by
  unfold upperT at h
  refine ⟨?_, ?_⟩
  · intro e he
    obtain ⟨q, hq, hqe⟩ := mem_of_mapM h he
    obtain ⟨hqm, hqτ⟩ := List.mem_filter.mp hq
    obtain ⟨hqc, hqi, hqcell⟩ := mem_realNodes hqm
    simp only [bind, Except.bind, pure, Except.pure] at hqe
    cases hlc : leftColumn q.2 with
    | error err => rw [hlc] at hqe; cases hqe
    | ok v =>
        rw [hlc] at hqe
        cases hqe
        obtain ⟨l, hl, hlv⟩ := leftColumn_ok hlc
        have hq1 : q.1 = ⟨upperColumn ctx, q.1.index⟩ := by rw [← hqc]
        refine ⟨q.1.index, q.2, hqi, by rw [← hq1]; exact hqcell, by rw [← hq1], rfl,
          by simpa using hqτ, l, hl, by simp [hlv]⟩
  · intro k c hk hc hτ
    have hmem : ((⟨upperColumn ctx, k⟩ : Ref), c) ∈ realNodes ctx.source (upperColumn ctx) := by
      obtain ⟨colv, hcolv, hcv⟩ := cell?_spec hc
      simp only at hcolv hcv
      unfold realNodes
      rw [hcolv]
      simp only [List.mem_map]
      obtain ⟨hks, hkc⟩ := Array.getElem?_eq_some_iff.mp hcv
      refine ⟨(k, c), ?_, rfl⟩
      rw [List.mem_iff_getElem]
      refine ⟨k - 1, by simp; omega, ?_⟩
      simp only [List.getElem_drop, List.getElem_zip, List.getElem_range, Array.getElem_toList]
      simp only [show 1 + (k - 1) = k by omega, hkc]
    have hf : ((⟨upperColumn ctx, k⟩ : Ref), c) ∈ (realNodes ctx.source (upperColumn ctx)).filter
        (fun p => decide (τ ≤ official p.2.row)) := List.mem_filter.mpr ⟨hmem, by simpa using hτ⟩
    obtain ⟨hlen, hall⟩ := mapM_except_spec _ _ _ h
    obtain ⟨m, hm, hme⟩ := List.getElem_of_mem hf
    have hm' : m < us.length := by omega
    have hf' := hall m hm hm'
    rw [hme] at hf'
    simp only [bind, Except.bind, pure, Except.pure] at hf'
    cases hlc : leftColumn c with
    | error err => rw [hlc] at hf'; cases hf'
    | ok v =>
        rw [hlc] at hf'
        have hum := (Except.ok.inj hf').symm
        exact ⟨us[m], List.getElem_mem _, by rw [hum]⟩

/-- In a successful `assemble`, an emitted node without a leg is on the bottom row. -/
theorem assemble_none_row {ctx : Context} {emits : List Emit} {col : Column}
    (h : assemble ctx emits = .ok col) : ∀ em ∈ emits, em.leftColumn = none → em.row = 0 := by
  intro em hem hnone
  unfold assemble at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i cells hcells
        obtain ⟨_, hall⟩ := mapM_except_spec _ _ _ hcells
        obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hem
        have hf := hall m hm (by
          obtain ⟨hlen, _⟩ := mapM_except_spec _ _ _ hcells
          omega)
        simp only [hnone] at hf
        by_contra hne
        rw [if_neg hne] at hf
        simp [throw, throwThe, MonadExceptOf.throw] at hf

/-! ## Columns of a run -/

theorem extract_getElem?_lt {R : Mountain} {X q : Nat} (hq : q < X) :
    (R.extract 0 X)[q]? = R[q]? := by
  simp only [Array.getElem?_extract]
  by_cases hs : q < R.size
  · simp [hq, hs]
  · rw [Array.getElem?_eq_none (by omega)]
    simp [hq]
    omega

/-- The context of an existing column is a block context. -/
theorem bctx_ctxAt {M R : Mountain} {cr x0 i x X : Nat} (hx1 : cr ≤ x) (hx2 : x ≤ x0)
    (hX : cr + (x0 - cr) * i < X) :
    BCtx M R cr x0 i (ctxAt M R x i cr (x0 - cr) x0 X) :=
  ⟨rfl, rfl, rfl, rfl, rfl, hx1, hx2, extract_getElem?_lt hX⟩

/-- The hypothetical copy of `cr` in block `i`. -/
theorem bctx_root (M R : Mountain) (cr x0 i : Nat) (h : cr ≤ x0) :
    BCtx M R cr x0 i ⟨M, R, cr, i, cr, x0 - cr, x0⟩ :=
  ⟨rfl, rfl, rfl, rfl, rfl, le_rfl, h, rfl⟩

/-- The block and the source column of a column are unique. -/
theorem block_unique {cr x0 x y i j : Nat} (hx1 : cr < x) (hx2 : x ≤ x0) (hy1 : cr < y)
    (hy2 : y ≤ x0) (h : x + (x0 - cr) * i = y + (x0 - cr) * j) : i = j ∧ x = y := by
  have hw : 0 < x0 - cr := by omega
  have h' : (x - cr) + (x0 - cr) * i = (y - cr) + (x0 - cr) * j := by omega
  have hxy := LowerPB.repr_unique' (by omega) (by omega) (by omega) (by omega) h'
  refine ⟨?_, by omega⟩
  have hij : (x0 - cr) * i = (x0 - cr) * j := by omega
  exact Nat.eq_of_mul_eq_mul_left hw hij

/-- **A column `X ≥ x₀` of a splice run**, with the traced lower and upper copies. -/
theorem colView {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}
    (hCI : ColumnsInv M n root.column (M.size - 1 - root.column) (M.size - 1)
      (official t.row) R)
    {X : Nat} (hX : X < R.size) (hx : M.size - 1 ≤ X) :
    ∃ i x lo us, i < n + 1 ∧ x ∈ blockColumns root.column (M.size - 1) n i ∧
      X = x + (M.size - 1 - root.column) * i ∧
      lowerT (ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1) X)
        (official t.row) = .ok lo ∧
      upperT (ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1) X)
        (official t.row) = .ok us ∧
      assemble (ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1) X)
        ((lo ++ us).map Prod.fst) = .ok R[X] := by
  obtain ⟨i, x, hi, hxb, hXeq, hcopy⟩ := hCI.2.2 X hX hx
  obtain ⟨es, hes, hasm⟩ := copyColumn_emitsT hcopy
  obtain ⟨lo, us, hlo, hus, rfl⟩ := emitsT_split hes
  exact ⟨i, x, lo, us, hi, hxb, hXeq, hlo, hus, hasm⟩

/-! ## Rows -/

theorem lt_of_stored_lt {a b : Row} (h : stored a < stored b) : a < b := by
  by_contra hn
  exact absurd h (not_lt.mpr (stored_mono (le_of_not_gt hn)))

theorem official_stored' (ρ : Row) : official (stored ρ) = ρ := by
  have h1 : (1 : Row) ≤ stored ρ := row_one_le_of_ne_zero (stored_ne_zero ρ)
  have h := stored_official h1
  by_contra hn
  rcases lt_or_gt_of_ne hn with hlt | hgt
  · have := stored_strictMono hlt
    rw [h] at this
    exact lt_irrefl _ this
  · have := stored_strictMono hgt
    rw [h] at this
    exact lt_irrefl _ this

theorem lt_of_official_lt {a b : Row} (hb : (1 : Row) ≤ b) (h : official a < official b) :
    a < b := row_lt_of_official hb h

/-- The top `t` of the last column is the node `(x₀, k)` for some real index `k`. -/
theorem top_node {s : List Nat} {M : Mountain} {t : Cell} {root : Ref}
    (hTop : Top s M t root) : ∃ k, 1 ≤ k ∧ cell? M ⟨M.size - 1, k⟩ = some t := by
  have hV := build_valid_of_success hTop.build
  have htop := hTop.top
  have hMs : 0 < M.size := by have := hTop.lt; omega
  rw [Array.getElem?_eq_getElem (show M.size - 1 < M.size by omega)] at htop
  simp only [Option.bind_some] at htop
  have h2 := (hV (M.size - 1) (by omega)).size_ge_two
  refine ⟨M[M.size - 1].size - 1, by omega, ?_⟩
  rw [Array.back?_eq_getElem?] at htop
  simp only [cell?, Array.getElem?_eq_getElem (show M.size - 1 < M.size by omega)]
  exact htop

end OmegaY.Official.Recon.LowerPB

#print axioms OmegaY.Official.Recon.LowerPB.shadow
