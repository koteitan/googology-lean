/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/ChainCorrStartLegJump.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.ChainCorrCutLeg
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.ChainCorrStartCopy
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.ChainsCanonParent
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.RowLawColumn
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.RootCut

set_option backward.do.legacy false

/-!
# `StartLeg` and `StartJump`

This file works on the two start statements of `ChainCorrRegions.lean` for a node
`u = (X, j + 1)` of a copied column `X = x + w·i` (block `i ≥ 1`) whose origin `o`
(`Trace.lean`) is not a gap copy, with leg column `l` of `o` (`Legs`).

## `StartLeg`

`startLeg_of_legBelowTop : LegBelowTop → StartLeg`. Upper origins are excluded by the
hypothesis of `StartLeg`; clean copies of the root row are `cleanLeg`
(`ChainCorrCutLeg.lean`); a plain origin is a node `(x, σ)` of the source column with
`σ < τ` (`emitsT_plainBelow`, an induction over the items). What remains is a fact about the
canonical mountain `M(s)` alone:

* `LegBelowTop` (open): every node of a column `c_r < c ≤ x₀` whose row is below the row of
  the top `t` of the last column has its leg at or right of `c_r`.

## `StartJump`

Both mountains are canonical. The highest node `q` of a leg column at or below the row of a
node `u` is either at the row of `u` (then the jump is `0`), or it is the left end of `u`,
and then `jump(row u, row q) = jump(row u, row u⁻)` by the row law (`jump_highest_zero`,
`jump_highest_step`). So `StartJump` follows from (`startJump_of_parts`)

* `LegRowMatch`: if the leg column `l` of `M(s)` has a node at the row of `o`, the output leg
  column `φ(l)` has a node at the row of `u`;
* `StepJumpLe`: otherwise `jump(row u, row u⁻) ≤ jump(row o, row o⁻)`.

`StepJumpLe` is **proved** (`stepJumpLe`; in general form `stepJump_general`). In both
columns consecutive rows are bump steps (`bumpChainHolds` for the output, the row law for
`M(s)`), so each jump is one more than the lowest nonzero coefficient of the upper row. For
an upper origin the rows are equal. For a plain origin or a clean copy the lowest nonzero
coefficient of the copy is at most that of the origin (`emitsT_nonCutLow`): at every level of
the item recursion a slot `h ≥ 1` goes to a slot `j ≥ 1` unless the child has a cut bottom,
and the non-cut origins emitted under a cut bottom are not the base of their source region
(`childProps`, `runItemT_nonCutLow`); a copied root row `C` is the row of the top of the
root column in the source region (`childItems_cleanTop`).

`LegRowMatch` is proved from `StartLeg`, the block profile `CopyOrder`, `CopyEmitted` of
`ChainCorrStartCopy.lean` (open there) and the root-column case
(`legRowMatch_of_parts`); the root-column case is proved for upper origins
(`legRowMatchRoot_upper`: the boundary column `cr + w·i` copies the upper part of the root
column). What remains is

* `LegRowMatchRootLower` (open): for a plain or clean origin with leg `c_r` whose row is a
  row of the root column, the boundary column `cr + w·i` has a node at the row of `u`.
  Numerically the copy then keeps the row of its origin, and the boundary column has at that
  row the copy (block `i - 1`) of the node of `x₀` at that row.

Summary: `startLeg_startJump : LegBelowTop → CopyOrder → CopyEmitted →
LegRowMatchRootLower → StartLeg ∧ StartJump`.

## Numerical tests

`reference/official/startleg-jump.cjs` (counts: nodes of `M(s)` for `LegBelowTop`, output
nodes otherwise; `StepJump` and `Low` are the proved statements, tested before the proof):

| sample | expansions | `LegBelowTop` | `LegRowMatchRootLower` | `StepJump` | `Low` | failures |
|---|---:|---:|---:|---:|---:|---:|
| standard S1–S3, S6, `n = 1,2,3` | 39090 | 162844 | 250215 | 704529 | 549396 | 0 |
| legal, length ≤ 6, entries ≤ 6 | 23325 | 32213 | 45468 | 184119 | 63540 | 0 |
| legal, length ≤ 5, entries ≤ 8 | 12285 | 21379 | 24861 | 132963 | 53925 | 0 |
| random legal (`--random 20000,10,10,7`) | 37926 | 85212 | 87804 | 594162 | 228738 | 0 |

In every `LegRowMatchRootLower` case the copy has the row of its origin.
-/

namespace OmegaY.Official.Classification.Proofs.ChainCorr.LegJump

open Canonical Reserve Official Descent Classification Proofs

/-! ## The sources of the children of an item are slots of its source -/

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
set_option linter.unnecessarySeqFocus false in
theorem childItems_source {ctx : Context} {d : Nat} {it : Item} {cs : List Item}
    (h : childItems ctx d it = .ok cs) : ∀ c ∈ cs, ∃ j, c.source = slot d it.source j := by
  unfold childItems at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  generalize topIn ctx.source ctx.rootColumn d it.source = rho at h
  split at h
  · obtain rfl := Except.ok.inj h
    simp
  · split at h
    · cases h
    · rename_i v hv
      split at h
      · split at h
        · simp [throw, throwThe, MonadExceptOf.throw] at h
        · obtain rfl := Except.ok.inj h
          intro c hc
          simp only [List.mem_map, List.mem_range] at hc
          obtain ⟨j, _, rfl⟩ := hc
          exact ⟨_, rfl⟩
      · rename_i hasc
        have hvt : v = true := by simpa using hasc
        subst hvt
        have hsome : ∃ r cl, rho = some (r, cl) := by
          cases rho with
          | none => simp [ascends, pure, Except.pure] at hv
          | some p => exact ⟨p.1, p.2, rfl⟩
        obtain ⟨r, cl, rfl⟩ := hsome
        simp only at h
        split at h
        · split at h
          · obtain rfl := Except.ok.inj h
            intro c hc
            simp only [List.mem_map, List.mem_range] at hc
            obtain ⟨j, _, rfl⟩ := hc
            (try split_ifs) <;> exact ⟨_, rfl⟩
          · obtain rfl := Except.ok.inj h
            intro c hc
            simp only [List.mem_map, List.mem_filter, List.mem_range] at hc
            obtain ⟨j, _, rfl⟩ := hc
            (try split_ifs) <;> exact ⟨_, rfl⟩
        · split at h
          · simp [throw, throwThe, MonadExceptOf.throw] at h
          · split at h
            · cases h
            · split at h
              · simp [throw, throwThe, MonadExceptOf.throw] at h
              · obtain rfl := Except.ok.inj h
                intro c hc
                simp only [List.mem_map, List.mem_range] at hc
                obtain ⟨j, _, rfl⟩ := hc
                (try split_ifs) <;> exact ⟨_, rfl⟩

/-! ## Plain origins lie below the top row -/

/-- The rows of the source region of an item of level `d` are below `τ`. -/
def Below (τ : Row) (d : Nat) (it : Item) : Prop :=
  ∀ r, inRegion d it.source r = true → r < τ

/-- A plain origin is a node of the source column whose official row is below `τ`. -/
def PlainBelow (ctx : Context) (τ : Row) (p : Emit × Origin) : Prop :=
  ∀ r, p.2 = .plain r → ∃ c, (r, c) ∈ realNodes ctx.source ctx.x ∧ official c.row < τ

theorem levelOneT_plainBelow {ctx : Context} {τ : Row} {it : Item} (hit : Below τ 1 it)
    {ps : List (Emit × Origin)} (h : levelOneT ctx it = .ok ps) :
    ∀ p ∈ ps, PlainBelow ctx τ p := by
  unfold levelOneT at h
  cases hsrc : nodeAt ctx.source ctx.x it.source with
  | none => simp [hsrc, pure, Except.pure] at h; subst h; simp
  | some q =>
      obtain ⟨srcRef, src⟩ := q
      obtain ⟨hmem, hrow⟩ := Recon.RowLaw.nodeAt_spec hsrc
      have hlt : official src.row < τ := by
        rw [hrow]
        exact hit it.source (Recon.RowLaw.self_inRegion 1 it.source)
      simp only [hsrc] at h
      cases hC : it.clean with
      | some C =>
          simp only [hC] at h
          cases hcs : nodeAt ctx.source ctx.x C with
          | none => simp [hcs, throw, throwThe, MonadExceptOf.throw] at h
          | some q' =>
              obtain ⟨csRef, cs⟩ := q'
              simp only [hcs, bind, Except.bind, pure, Except.pure] at h
              split at h
              · cases h
              · cases h
                intro p hp
                simp only [List.mem_singleton] at hp
                subst hp
                intro r hr
                cases hr
      | none =>
          simp only [hC] at h
          split at h
          · simp only [pure, Except.pure, Except.ok.injEq] at h
            subst h
            intro p hp
            simp only [List.mem_singleton] at hp
            subst hp
            intro r hr
            simp only [Origin.plain.injEq] at hr
            subst hr
            exact ⟨src, hmem, hlt⟩
          · simp only [bind, Except.bind, pure, Except.pure] at h
            split at h
            · cases h
            · cases h
              intro p hp
              simp only [List.mem_singleton] at hp
              subst hp
              intro r hr
              simp only [Origin.plain.injEq] at hr
              subst hr
              exact ⟨src, hmem, hlt⟩

theorem runItemT_plainBelow (ctx : Context) (τ : Row) :
    ∀ (d : Nat) (it : Item) (ps : List (Emit × Origin)), Below τ d it →
      runItemT ctx d it = .ok ps → ∀ p ∈ ps, PlainBelow ctx τ p
  | 0, _, ps, _, h => by simp [runItemT, pure, Except.pure] at h; subst h; simp
  | 1, it, ps, hit, h => levelOneT_plainBelow hit (by simpa [runItemT] using h)
  | d + 2, it, ps, hit, h => by
      simp only [runItemT, bind, Except.bind, pure, Except.pure] at h
      split at h
      · cases h
      · rename_i children hch
        split at h
        · cases h
        · rename_i outs houts
          cases h
          intro p hp
          obtain ⟨out, hout, hpo⟩ := List.mem_flatten.mp hp
          obtain ⟨c, hc, hco⟩ := mem_of_mapM houts hout
          have hcb : Below τ (d + 1) c := by
            obtain ⟨j, hj⟩ := childItems_source hch c hc
            intro r hr
            rw [hj] at hr
            exact hit r (Recon.RowLaw.inRegion_of_slot hr)
          exact runItemT_plainBelow ctx τ (d + 1) c out hcb hco p hpo

/-- **Every plain origin of a copied column is a node of the source column below `τ`.** -/
theorem emitsT_plainBelow {ctx : Context} {τ : Row} {es : List (Emit × Origin)}
    (h : emitsT ctx τ = .ok es) : ∀ p ∈ es, PlainBelow ctx τ p := by
  unfold emitsT at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i lower hlower
    split at h
    · cases h
    · rename_i upper hupper
      cases h
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · unfold lowerT at hlower
        simp only [bind, Except.bind, pure, Except.pure] at hlower
        split at hlower
        · cases hlower
        · rename_i outs houts
          cases hlower
          obtain ⟨out, hout, hpo⟩ := List.mem_flatten.mp hp
          obtain ⟨q, hq, hqo⟩ := mem_of_mapM houts hout
          exact runItemT_plainBelow ctx τ q.1 q.2 out
            (Recon.RowLaw.lower_itemOK (ctx := ctx) hq).1.below hqo p hpo
      · unfold upperT at hupper
        obtain ⟨q, _, hqp⟩ := mem_of_mapM hupper hp
        simp only [bind, Except.bind, pure, Except.pure] at hqp
        split at hqp
        · cases hqp
        · cases hqp
          intro r hr
          cases hr

/-! ## The top of the last column and the root -/

/-- The top `t` of a `Site` is a real top whose left endpoint is in the root column. -/
theorem site_top {s : List Nat} {n D : Nat} {M : Mountain} {out : List Nat} {ρ : Root}
    {R : Mountain} {t : Cell} {X x i : Nat} {es : List (Emit × Origin)}
    (hS : Site s n D M out ρ R t X x i es) :
    ∃ root, Recon.Top s M t root ∧ root.column = ρ.cr ∧ ρ.x0 = M.size - 1 := by
  have hV := build_valid_of_success hS.splice.build
  obtain ⟨col, hcol, ht⟩ := hS.last
  obtain ⟨M', hM', hcases⟩ := expandDiagram_spec hS.run
  rw [hS.splice.build] at hM'
  cases hM'
  have hx := (root?_spec hV hS.splice.root).1
  have hsz := build_size hS.splice.build
  rcases hcases with ⟨he, _⟩ | ⟨col', t', hcol', ht', hbr⟩
  · have : s = [] := List.isEmpty_iff.mp he
    subst this
    simp only [List.length_nil] at hsz
    omega
  · have hcc : col' = col := Option.some.inj (hcol'.symm.trans hcol)
    subst hcc
    have htt : t' = t := Option.some.inj (ht'.symm.trans ht)
    subst htt
    rcases hbr with ⟨hdel, _⟩ | ⟨hsp, root, htl, hlt, _, _⟩
    · rcases hdel with h0 | h0
      · have hr := hS.splice.root
        rw [root?_none_of_official_zero hV D hcol' ht' h0] at hr
        cases hr
      · exact absurd h0 hS.splice.copies
    · obtain ⟨ρ', hr', hx0, hcr'⟩ :=
        root?_of_official_ne_zero hV D hcol' ht' (fun h0 => hsp (Or.inl h0)) htl
      have hρ : ρ' = ρ := Option.some.inj (hr'.symm.trans hS.splice.root)
      subst hρ
      refine ⟨root, ⟨hS.splice.build, by rw [hcol']; exact ht', fun h0 => hsp (Or.inl h0), htl,
        hlt⟩, hcr'.symm, hx0⟩

/-! ## `StartLeg` from a fact about `M(s)` -/

/-- (open) **Legs below the top row.** In the canonical mountain `M(s)` with top `t` of the
last column `x₀ = M.size - 1` and root `r = left(t)`, every node `u` of a column
`c_r < c ≤ x₀` whose row is below the row of `t` has its leg (left endpoint) at or right of
the root column. -/
def LegBelowTop : Prop :=
  ∀ (s : List Nat) (M : Mountain) (t : Cell) (root : Ref), Recon.Top s M t root →
    ∀ (u : Ref) (cu : Cell) (l : Ref), root.column < u.column → u.column ≤ M.size - 1 →
      cell? M u = some cu → cu.left = some l → cu.row < t.row → root.column ≤ l.column

theorem cell?_of_mem_realNodes {M : Mountain} {c : Nat} {r : Ref} {cell : Cell}
    (h : (r, cell) ∈ realNodes M c) : cell? M r = some cell := by
  obtain ⟨col, k, hc, hcell, hr⟩ := Recon.mem_realNodes_iff.mp h
  simp only at hr hcell
  rw [hr]
  simp [cell?, hc, hcell]

/-- **`StartLeg` from `LegBelowTop`.** Upper origins are excluded by hypothesis, copies of
the root row are `cleanLeg` (`ChainCorrCutLeg.lean`), and a plain origin is a node of the
source column below the top row (`emitsT_plainBelow`). -/
theorem startLeg_of_legBelowTop (hT : LegBelowTop) : StartLeg := by
  intro s n D M out ρ R t X x i es hS j hj hcut cu cv ref l pe pa cpe cpa hL hnot
  obtain ⟨root, hTop, hroot, hx0⟩ := site_top hS
  obtain ⟨hcx, hxx⟩ := mem_blockColumns_pos hS.xMem hS.iPos
  cases ho : es[j].2 with
  | upper r =>
      rw [ho] at hnot
      simp only [Origin.isUpper, true_and] at hnot
      omega
  | clean r b =>
      exact cleanLeg hS hj ho hL
  | plain r =>
      obtain ⟨c, hmem, hlt⟩ := emitsT_plainBelow hS.emits es[j] (List.getElem_mem hj) r ho
      have hcell := cell?_of_mem_realNodes hmem
      have hcv := hL.hcv
      rw [ho] at hcv
      simp only [Origin.src] at hcv
      have hcc : cv = c := Option.some.inj (hcv.symm.trans hcell)
      subst hcc
      obtain ⟨hrc, _⟩ := Recon.RowLaw.realNodes_column hmem
      simp only [ctxAt] at hrc
      rw [← hroot]
      refine hT s M t root hTop r cv l (by rw [hrc, hroot]; exact hcx) (by rw [hrc]; omega)
        hcell hL.hl ?_
      exact Recon.row_lt_of_official hTop.row_one_le hlt


/-- Column `c` of `N` has a real node at the row `row`. -/
def SameRow (N : Mountain) (c : Nat) (row : Row) : Prop :=
  ∃ j cell, 0 < j ∧ cell? N ⟨c, j⟩ = some cell ∧ cell.row = row

theorem getLast_max {l : List Nat} (hl : l.Pairwise (· < ·)) {x : Nat}
    (hx : l.getLast? = some x) {y : Nat} (hy : y ∈ l) : y ≤ x := by
  obtain ⟨front, rfl⟩ := List.getLast?_eq_some_iff.mp hx
  rw [List.pairwise_append] at hl
  rcases List.mem_append.mp hy with hy | hy
  · exact le_of_lt (hl.2.2 y hy x (by simp))
  · rw [List.mem_singleton.mp hy]

/-- The highest real node of a column at or below a row. -/
theorem hAM_spec {N : Mountain} {l : Nat} {row : Row} {p : Ref}
    (h : highestAtMost N l row = some p) :
    p.column = l ∧ 0 < p.index ∧ (∃ cp, cell? N p = some cp ∧ cp.row ≤ row) ∧
      ∀ j c, cell? N ⟨l, j⟩ = some c → 0 < j → c.row ≤ row → j ≤ p.index := by
  simp only [highestAtMost, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨col, hcol, j, hj, rfl⟩ := h
  have hmem := List.mem_of_getLast? hj
  simp only [List.mem_filter, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at hmem
  obtain ⟨hjs, hj0, hjc⟩ := hmem
  refine ⟨rfl, hj0, ?_, ?_⟩
  · rw [Array.getElem?_eq_getElem hjs] at hjc
    simp only [decide_eq_true_eq] at hjc
    exact ⟨col[j], by simp [cell?, hcol, Array.getElem?_eq_getElem hjs], hjc⟩
  · intro j' c hc hj'0 hcr
    simp only [cell?, hcol, Option.bind_eq_bind, Option.bind_some] at hc
    have hj's : j' < col.size := by
      by_contra hn
      rw [Array.getElem?_eq_none (by omega)] at hc
      cases hc
    apply getLast_max ((List.pairwise_lt_range).filter _) hj
    simp only [List.mem_filter, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨hj's, hj'0, ?_⟩
    rw [hc]
    simpa using hcr

/-- A same-row node makes the highest node at or below the row sit at that row. -/
theorem hAM_row_of_sameRow {N : Mountain} (hV : MountainValid N) {l : Nat} {row : Row}
    {p : Ref} {cp : Cell} (h : highestAtMost N l row = some p) (hcp : cell? N p = some cp)
    (hs : SameRow N l row) : cp.row = row := by
  obtain ⟨hpl, _, ⟨cp', hcp', hle⟩, hmax⟩ := hAM_spec h
  rw [hcp] at hcp'
  cases hcp'
  obtain ⟨j, c, hj0, hc, hcr⟩ := hs
  have hjp := hmax j c hc hj0 (le_of_eq hcr)
  apply le_antisymm hle
  rw [← hcr]
  obtain ⟨colc, hcolc, hcc⟩ := cell?_spec hc
  obtain ⟨colp, hcolp, hcpp⟩ := cell?_spec hcp
  rw [hpl] at hcolp
  have hce : colp = colc := Option.some.inj (hcolp.symm.trans hcolc)
  subst hce
  obtain ⟨hl, hcolEq⟩ := column_of_getElem? hcolc
  have hCV := hV l hl
  rw [hcolEq] at hCV
  rcases Nat.lt_or_eq_of_le hjp with hlt | heq
  · exact le_of_lt (hCV.rows_strict j p.index c cp hcc hcpp hlt)
  · simp only at hcc
    rw [heq] at hcc
    rw [Option.some.inj (hcc.symm.trans hcpp)]

theorem jump_highest_zero {N : Mountain} (hV : MountainValid N) {l : Nat} {row : Row}
    {p : Ref} {cp : Cell} (h : highestAtMost N l row = some p) (hcp : cell? N p = some cp)
    (hs : SameRow N l row) : Row.jump row cp.row = 0 := by
  rw [hAM_row_of_sameRow hV h hcp hs, Row.jump_self]

theorem jump_B_right (a b : Row) : Row.jump (Row.B a b) b = Row.jump (Row.B a b) a := by
  have h1 : Row.jump a (Row.B a b) = Row.jump a b + 1 := by
    unfold Row.B
    exact Row.jump_bump a _
  have h2 : Row.jump b (Row.B a b) = Row.jump a b + 1 := by
    rw [B_from_right]
    exact Row.jump_bump b _
  rw [Row.jump_comm (Row.B a b) b, h2, Row.jump_comm (Row.B a b) a, h1]

theorem cell_index_lt {N : Mountain} {c j : Nat} {cell : Cell}
    (h : cell? N ⟨c, j⟩ = some cell) : ∃ col, N[c]? = some col ∧ j < col.size ∧ col[j]? = some cell := by
  obtain ⟨col, hcol, hc⟩ := cell?_spec h
  simp only at hcol hc
  refine ⟨col, hcol, ?_, hc⟩
  by_contra hn
  rw [Array.getElem?_eq_none (by omega)] at hc
  cases hc

/-- **The highest node at or below the row of a node, in a canonical mountain.** If the
leg column of a real node `u` has no node at the row of `u`, then `u` is not a bottom node,
the highest node `q` of the leg column at or below `row u` is the left end of `u`, and
`jump(row u, row q) = jump(row u, row u⁻)` (the row law). -/
theorem jump_highest_step {s' : List Nat} {N : Mountain} (hb : Canonical.build s' = .ok N)
    {u : Ref} {cu : Cell} {l q : Ref} {cq : Cell} (hcu : cell? N u = some cu)
    (hu0 : 0 < u.index) (hl : cu.left = some l)
    (hq : highestAtMost N l.column cu.row = some q) (hcq : cell? N q = some cq)
    (hns : ¬ SameRow N l.column cu.row) :
    ∃ k cd, u.index = k + 2 ∧ cell? N ⟨u.column, k + 1⟩ = some cd ∧
      Row.jump cu.row cq.row = Row.jump cu.row cd.row := by
  have hV := build_valid_of_success hb
  obtain ⟨colu, hcolu, hus, hcuu⟩ := cell_index_lt (c := u.column) (j := u.index) hcu
  obtain ⟨hcs, hcolEq⟩ := column_of_getElem? hcolu
  have hCV := hV u.column hcs
  rw [hcolEq] at hCV
  have hb1 : 1 < colu.size := by have := hCV.size_ge_two; omega
  obtain ⟨bot, hbot⟩ : ∃ bot, colu[1]? = some bot := ⟨colu[1], Array.getElem?_eq_getElem hb1⟩
  have hbrow := hCV.bottom_row bot hbot
  have hc0 : 0 < u.column := by
    have := (hCV.stored_valid u.index cu l hcuu hl).1
    omega
  rcases Nat.lt_or_ge u.index 2 with hlt2 | hge2
  · -- a bottom node: its leg column has a bottom node
    exfalso
    have hi1 : u.index = 1 := by omega
    have hleft := bottom_left hb hcu hi1 (by omega)
    rw [hl] at hleft
    obtain rfl := Option.some.inj hleft
    have hcu1 : cu = bot := by
      rw [hi1] at hcuu
      exact Option.some.inj (hcuu.symm.trans hbot)
    subst hcu1
    have hlc : u.column - 1 < N.size := by omega
    have hCV' := hV (u.column - 1) hlc
    have hb1' : 1 < N[u.column - 1].size := by have := hCV'.size_ge_two; omega
    apply hns
    refine ⟨1, N[u.column - 1][1], by omega, ?_, ?_⟩
    · simp [cell?, Array.getElem?_eq_getElem hlc, Array.getElem?_eq_getElem hb1']
    · rw [hCV'.bottom_row _ (Array.getElem?_eq_getElem hb1'), hbrow]
  · obtain ⟨k, hk⟩ : ∃ k, u.index = k + 2 := ⟨u.index - 2, by omega⟩
    have hks : k + 1 < colu.size := by omega
    let cd := colu[k + 1]
    have hcd : colu[k + 1]? = some cd := Array.getElem?_eq_getElem hks
    have hcd' : cell? N ⟨u.column, k + 1⟩ = some cd := by simp [cell?, hcolu, hcd]
    have hcu2 : colu[k + 1 + 1]? = some cu := by rw [show k + 1 + 1 = u.index by omega]; exact hcuu
    -- the raw parent of `u⁻` is `l`
    have hraw : rawParent N ⟨u.column, k + 1⟩ = some l := by
      simp [rawParent, hcolu, hcu2, hl]
    have hcu' : cell? N ⟨u.column, k + 1 + 1⟩ = some cu := by simp [cell?, hcolu, hcu2]
    obtain ⟨cp, hcp, hcplt, hmaxp⟩ := canonical_rawParent_highest_below
      (build_success_legal hb) hb hcu' hraw
    obtain ⟨hql, hq0, ⟨cq', hcq', hcqle⟩, hmaxq⟩ := hAM_spec hq
    rw [hcq] at hcq'
    obtain rfl := Option.some.inj hcq'
    have hcqlt : cq.row < cu.row := by
      rcases lt_or_eq_of_le hcqle with h | h
      · exact h
      · exfalso
        apply hns
        refine ⟨q.index, cq, hq0, ?_, h⟩
        rw [← hql]
        exact hcq
    have hqref : q = ⟨l.column, q.index⟩ := by rw [← hql]
    have h1 : q.index ≤ l.index := hmaxp q.index cq (by rw [← hqref]; exact hcq) hcqlt
    -- `l` is a real node
    have hl0 : 0 < l.index := by
      have hbot' : 1 < cu.row := by
        rw [← hbrow]
        exact hCV.rows_strict 1 u.index bot cu hbot hcuu (by omega)
      obtain ⟨coll, hcoll, hls, hlc⟩ := cell_index_lt (c := l.column) (j := l.index)
        (by simpa using hcp)
      obtain ⟨hlcs, hcollEq⟩ := column_of_getElem? hcoll
      have hCVl := hV l.column hlcs
      rw [hcollEq] at hCVl
      have hb1l : 1 < coll.size := by have := hCVl.size_ge_two; omega
      have := hmaxp 1 coll[1] (by simp [cell?, hcoll, Array.getElem?_eq_getElem hb1l])
        (by rw [hCVl.bottom_row _ (Array.getElem?_eq_getElem hb1l)]; exact hbot')
      omega
    have h2 : l.index ≤ q.index := hmaxq l.index cp (by simpa using hcp) hl0 (le_of_lt hcplt)
    have hqe : q = l := by
      rw [hqref]
      cases l
      simp only [Ref.mk.injEq, true_and]
      simp only at h1 h2
      omega
    subst hqe
    rw [hcp] at hcq
    obtain rfl := Option.some.inj hcq
    -- the row law
    obtain ⟨_, parentRef, parent, _, _, hread, hrow, _, hleft⟩ :=
      build_steps hb u.column hcs (k + 1) cd cu (by rw [hcolEq]; exact hcd)
        (by rw [hcolEq]; exact hcu2) (by omega)
    rw [hl] at hleft
    obtain rfl := Option.some.inj hleft
    have hpc : cell? N q = some parent := by
      obtain ⟨colp, hcolp, hcellp⟩ := cellAt_ok_iff.mp hread
      simp [cell?, hcolp, hcellp]
    rw [hcp] at hpc
    obtain rfl := Option.some.inj hpc
    refine ⟨k, cd, hk, hcd', ?_⟩
    rw [hrow, jump_B_right]

/-! ## `StartJump` from two statements about the copied rows -/

/-- (reduced: `legRowMatch_of_parts`) **The leg row matches.** If the leg column of the
origin has a node at the row of the origin (in particular when the origin is a bottom node),
the output leg column has a node at the row of the copy. -/
def LegRowMatch : Prop :=
  ∀ s n D M out ρ R t X x i es, Site s n D M out ρ R t X x i es →
    ∀ j (hj : j < es.length), cutOrigin es[j].2 = false →
    ∀ cu cv ref l pe pa cpe cpa, Legs M R X j es[j].2 cu cv ref l pe pa cpe cpa →
      ¬ (es[j].2.isUpper = true ∧ l.column < ρ.cr) →
      SameRow M l.column cv.row → SameRow R ref.column cu.row

/-- (proved: `stepJumpLe`) **The step into a copy jumps no higher than the step into its
origin.** For a copy `u = (X, j + 1)` with `j ≥ 1` of an origin `o` whose leg column has no
node at the row of `o`: `jump(row u, row u⁻) ≤ jump(row o, row o⁻)`. -/
def StepJumpLe : Prop :=
  ∀ s n D M out ρ R t X x i es, Site s n D M out ρ R t X x i es →
    ∀ j (hj : j < es.length), cutOrigin es[j].2 = false →
    ∀ cu cv ref l pe pa cpe cpa, Legs M R X j es[j].2 cu cv ref l pe pa cpe cpa →
      ¬ (es[j].2.isUpper = true ∧ l.column < ρ.cr) →
      ¬ SameRow M l.column cv.row → 0 < j →
      ∀ cd cvd : Cell, cell? R ⟨X, j⟩ = some cd →
        cell? M ⟨es[j].2.src.column, es[j].2.src.index - 1⟩ = some cvd →
        Row.jump cu.row cd.row ≤ Row.jump cv.row cvd.row

/-- **`StartJump` from `LegRowMatch` and `StepJumpLe`.** Both mountains are canonical: the
highest node of a leg column at or below the row of a node `u` is either at the row of `u`
(jump `0`) or it is the left end of `u`, and then the jump is the jump of the step
`u⁻ → u` (`jump_highest_zero`, `jump_highest_step`). -/
theorem startJump_of_parts (hA : LegRowMatch) (hB : StepJumpLe) : StartJump := by
  intro s n D M out ρ R t X x i es hS j hj hcut cu cv ref l pe pa cpe cpa hL hnot
  have hVR := build_valid_of_success hS.canon
  by_cases hsm : SameRow M l.column cv.row
  · have hsr := hA s n D M out ρ R t X x i es hS j hj hcut cu cv ref l pe pa cpe cpa hL hnot hsm
    rw [jump_highest_zero hVR hL.hpe hL.hcpe hsr]
    exact Nat.zero_le _
  · obtain ⟨_, hidx, _⟩ := emitsT_good hS.emits es[j] (List.getElem_mem hj)
    obtain ⟨k, cvd, hk, hcvd, hRHS⟩ := jump_highest_step hS.splice.build hL.hcv (by omega)
      hL.hl hL.hpa hL.hcpa hsm
    rw [hRHS]
    by_cases hsr : SameRow R ref.column cu.row
    · rw [jump_highest_zero hVR hL.hpe hL.hcpe hsr]
      exact Nat.zero_le _
    · obtain ⟨k', cd, hk', hcd, hLHS⟩ := jump_highest_step hS.canon hL.hcu (by simp)
        hL.href hL.hpe hL.hcpe hsr
      simp only at hk' hcd
      rw [hLHS]
      have hj' : j = k' + 1 := by omega
      subst hj'
      exact hB s n D M out ρ R t X x i es hS (k' + 1) hj hcut cu cv ref l pe pa cpe cpa hL hnot
        hsm (by omega) cd cvd hcd (by rw [hk]; simpa using hcvd)

/-! ## `LegRowMatch` for a leg right of the root column -/

/-- (reduced: `legRowMatchRoot_of_lower`) `LegRowMatch` for the leg in the root column
(`φ(cr) = cr + w·i` is the boundary column of block `i - 1`). -/
def LegRowMatchRoot : Prop :=
  ∀ s n D M out ρ R t X x i es, Site s n D M out ρ R t X x i es →
    ∀ j (hj : j < es.length), cutOrigin es[j].2 = false →
    ∀ cu cv ref l pe pa cpe cpa, Legs M R X j es[j].2 cu cv ref l pe pa cpe cpa →
      ¬ (es[j].2.isUpper = true ∧ l.column < ρ.cr) → l.column = ρ.cr →
      SameRow M l.column cv.row → SameRow R ref.column cu.row

/-- **`LegRowMatch` for a leg right of the root column, from the block profile of
`ChainCorrStartCopy.lean`.** The node of the leg column `l` at the row `σ` of the origin has
a non-cut copy in the column `l + w·i` (`CopyEmitted`), and its row is the row of the copy
of the origin, since both origins have the row `σ` (`CopyOrder`). -/
theorem legRowMatch_inner (hA : CopyOrder) (hB : CopyEmitted) :
    ∀ s n D M out ρ R t X x i es, Site s n D M out ρ R t X x i es →
    ∀ j (hj : j < es.length), cutOrigin es[j].2 = false →
    ∀ cu cv ref l pe pa cpe cpa, Legs M R X j es[j].2 cu cv ref l pe pa cpe cpa →
      ρ.cr < l.column → SameRow M l.column cv.row → SameRow R ref.column cu.row := by
  intro s n D M out ρ R t X x i es hS j hj hnc cu cv ref l pe pa cpe cpa hL hlt hsm
  obtain ⟨jn, cn, hjn0, hcn, hcnrow⟩ := hsm
  have hdat := hS.data
  have hV := build_valid_of_success hS.splice.build
  obtain ⟨col', t', hcol', ht', _, hcrx, hinv⟩ := spliceCase_data hS.splice hS.run
  have htt : t' = t := by
    obtain ⟨col, hcol, ht⟩ := hS.last
    have : col' = col := Option.some.inj (hcol'.symm.trans hcol)
    subst this
    exact Option.some.inj (ht'.symm.trans ht)
  subst t'
  obtain ⟨hcx, hxx⟩ := mem_blockColumns_pos hS.xMem hS.iPos
  have hipos := hS.iPos
  have hblx : blockEmits M R ρ.cr ρ.x0 (official t.row) i x = .ok es := by
    simp only [blockEmits, ← hS.Xeq]
    exact hS.emits
  have himg := leg_image hS hj hL
  rw [mapColumn_of_ge (le_of_lt hlt)] at himg
  obtain ⟨hsrc, _, _, _, _⟩ := emitsT_good hS.emits es[j] (List.getElem_mem hj)
  have hly : l.column < es[j].2.src.column := left_lt_of_valid hV hL.hcv hL.hl
  have hsrcle : es[j].2.src.column ≤ ρ.x0 := by
    rw [hsrc]
    split
    · exact upperColumn_le hcrx.le hxx
    · exact hxx
  have hyx : l.column < ρ.x0 := by omega
  have hymem : l.column ∈ blockColumns ρ.cr ρ.x0 n i := by
    unfold blockColumns
    rw [if_neg (by omega)]
    simp only [List.mem_range'_1]
    split <;> omega
  -- the output column `l + w·i`
  obtain ⟨_, _, colL, hcolL, _, _, _⟩ := highestAtMost_spec hL.hpe
  have hL0 : ρ.x0 ≤ ref.column := by
    rw [himg]
    have : ρ.x0 - ρ.cr ≤ (ρ.x0 - ρ.cr) * i := Nat.le_mul_of_pos_right _ hipos
    omega
  obtain ⟨hLsz, _⟩ := column_of_getElem? hcolL
  obtain ⟨i', x', _, hx', hLeq, hcopyL⟩ := hinv.2.2 ref.column hLsz hL0
  obtain ⟨hii, hxy⟩ := blockCol_unique_inner hcrx hlt hyx hipos hx' (by rw [← himg]; exact hLeq)
  subst i' x'
  have hcolL' : R[ref.column]? = some R[ref.column] := Array.getElem?_eq_getElem hLsz
  obtain ⟨esl, hesl, _⟩ := copyColumn_emitsT hcopyL
  obtain ⟨_, hcellsL⟩ := cells_of_copy hcolL' hcopyL hesl
  have hbl : blockEmits M R ρ.cr ρ.x0 (official t.row) i l.column = .ok esl := by
    have h' : l.column + (ρ.x0 - ρ.cr) * i = ref.column := himg.symm
    simp only [blockEmits, h']
    exact hesl
  -- the row of `u`
  obtain ⟨cX, hRX, hcopyX⟩ := hS.copy
  obtain ⟨_, hcellsX⟩ := cells_of_copy hRX hcopyX hS.emits
  obtain ⟨cellu, hcellu, hrowu⟩ := hcellsX j hj
  have hrowcu : cu.row = stored es[j].1.row := by
    rw [Option.some.inj (hL.hcu.symm.trans hcellu)]
    exact hrowu
  -- the non-cut copy of the node `(l, σ)`
  obtain ⟨k, hk, hksrc, hknc⟩ := hB s n D M out ρ R t hdat i hipos hS.iLt l.column esl hlt hyx
    hbl ⟨l.column, jn⟩ cn rfl hjn0 hcn
  have hcnk : cell? M esl[k].2.src = some cn := by rw [hksrc]; exact hcn
  have hA' := hA s n D M out ρ R t hdat i hipos hS.iLt x l.column es esl hS.xMem hymem hblx hbl
    j hj k hk hnc hknc cv cn hL.hcv hcnk
  have hrowe := hA'.2 hcnrow.symm
  obtain ⟨cell, hcell, hrow⟩ := hcellsL k hk
  exact ⟨k + 1, cell, by omega, hcell, by rw [hrow, hrowcu, hrowe]⟩

/-- **`LegRowMatch` from `StartLeg`, the block profile and the root-column case.** -/
theorem legRowMatch_of_parts (hLeg : StartLeg) (hA : CopyOrder) (hB : CopyEmitted)
    (hR : LegRowMatchRoot) : LegRowMatch := by
  intro s n D M out ρ R t X x i es hS j hj hnc cu cv ref l pe pa cpe cpa hL hnot hsm
  have hcr := hLeg s n D M out ρ R t X x i es hS j hj hnc cu cv ref l pe pa cpe cpa hL hnot
  rcases Nat.lt_or_eq_of_le hcr with h | h
  · exact legRowMatch_inner hA hB s n D M out ρ R t X x i es hS j hj hnc cu cv ref l pe pa cpe
      cpa hL h hsm
  · exact hR s n D M out ρ R t X x i es hS j hj hnc cu cv ref l pe pa cpe cpa hL hnot h.symm hsm

/-! ## The upper part: `LegRowMatchRoot` for upper origins -/

/-- Every node of the column `x'` at or above `τ` is copied at its row. -/
theorem emitsT_upper_mem {ctx : Context} {τ : Row} {es : List (Emit × Origin)}
    (h : emitsT ctx τ = .ok es) {p : Ref × Cell}
    (hp : p ∈ realNodes ctx.source (upperColumn ctx)) (hτ : τ ≤ official p.2.row) :
    ∃ k, ∃ hk : k < es.length, es[k].1.row = official p.2.row := by
  unfold emitsT at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i lower hlower
    split at h
    · cases h
    · rename_i upper hupper
      cases h
      unfold upperT at hupper
      have hmem : p ∈ (realNodes ctx.source (upperColumn ctx)).filter
          (fun p => decide (τ ≤ official p.2.row)) := List.mem_filter.mpr ⟨hp, by simpa using hτ⟩
      obtain ⟨i, hi, hpi⟩ := List.getElem_of_mem hmem
      obtain ⟨hlen, hall⟩ := mapM_except_spec _ _ _ hupper
      have hi' : i < upper.length := by omega
      have hf := hall i hi hi'
      rw [hpi] at hf
      simp only [bind, Except.bind, pure, Except.pure] at hf
      cases hlc : leftColumn p.2 with
      | error e => rw [hlc] at hf; cases hf
      | ok v =>
        rw [hlc] at hf
        refine ⟨lower.length + i, by simp; omega, ?_⟩
        rw [List.getElem_append_right (by omega)]
        simp only [Nat.add_sub_cancel_left]
        rw [← (Except.ok.inj hf)]

/-- The rows of the upper part are at or above `τ`. -/
theorem emitsT_upper_ge {ctx : Context} {τ : Row} {es : List (Emit × Origin)}
    (h : emitsT ctx τ = .ok es) : ∀ p ∈ es, p.2.isUpper = true → τ ≤ p.1.row := by
  unfold emitsT at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i lower hlower
    split at h
    · cases h
    · rename_i upper hupper
      cases h
      intro p hp hup
      rcases List.mem_append.mp hp with hp | hp
      · unfold lowerT at hlower
        simp only [bind, Except.bind, pure, Except.pure] at hlower
        split at hlower
        · cases hlower
        · rename_i outs houts
          cases hlower
          obtain ⟨out, hout, hpo⟩ := List.mem_flatten.mp hp
          obtain ⟨q, _, hq⟩ := mem_of_mapM houts hout
          rw [runItemT_not_upper ctx q.1 q.2 out hq p hpo] at hup
          cases hup
      · unfold upperT at hupper
        obtain ⟨q, hq, hqp⟩ := mem_of_mapM hupper hp
        have hqτ := (List.mem_filter.mp hq).2
        simp only [decide_eq_true_eq] at hqτ
        simp only [bind, Except.bind, pure, Except.pure] at hqp
        cases hlc : leftColumn q.2 with
        | error e => rw [hlc] at hqp; cases hqp
        | ok v =>
            rw [hlc] at hqp
            cases hqp
            exact hqτ

theorem mem_realNodes_of_cell {M : Mountain} {c j : Nat} {cell : Cell}
    (h : cell? M ⟨c, j⟩ = some cell) (hj : 0 < j) : (⟨c, j⟩, cell) ∈ realNodes M c := by
  obtain ⟨col, hcol, _, hc⟩ := cell_index_lt h
  apply Recon.mem_realNodes_iff.mpr
  refine ⟨col, j - 1, hcol, ?_, ?_⟩
  · rw [show j - 1 + 1 = j by omega]; exact hc
  · simp only [Ref.mk.injEq, true_and]; omega

/-- The boundary column `cr + w·i` of the output (`i ≥ 1`) is the copy of `x₀` in block
`i - 1`; its upper part reads the root column. -/
theorem boundary_x {cr x0 n i i' x' : Nat} (hcr : cr < x0) (hi : 0 < i)
    (hx' : x' ∈ blockColumns cr x0 n i') (heq : cr + (x0 - cr) * i = x' + (x0 - cr) * i') :
    x' = x0 := by
  have hw : 0 < x0 - cr := by omega
  unfold blockColumns at hx'
  split at hx'
  · simpa using hx'
  · rename_i hi'
    simp only [List.mem_range'_1] at hx'
    have hx'le : cr < x' ∧ x' ≤ x0 := by split at hx' <;> omega
    rcases Nat.lt_or_ge i' i with h | h
    · obtain ⟨d, rfl⟩ : ∃ d, i = i' + d + 1 := ⟨i - i' - 1, by omega⟩
      have h1 : (x0 - cr) * (i' + d + 1) = (x0 - cr) * i' + (x0 - cr) * (d + 1) := by
        rw [show i' + d + 1 = i' + (d + 1) by omega, Nat.mul_add]
      have h2 : x0 - cr ≤ (x0 - cr) * (d + 1) := Nat.le_mul_of_pos_right _ (by omega)
      omega
    · have h1 : (x0 - cr) * i ≤ (x0 - cr) * i' := Nat.mul_le_mul_left _ h
      omega

/-- **`LegRowMatchRoot` for upper origins.** The upper part of the boundary column
`cr + w·i` copies the nodes of the root column at their rows. -/
theorem legRowMatchRoot_upper :
    ∀ s n D M out ρ R t X x i es, Site s n D M out ρ R t X x i es →
    ∀ j (hj : j < es.length),
    ∀ cu cv ref l pe pa cpe cpa, Legs M R X j es[j].2 cu cv ref l pe pa cpe cpa →
      es[j].2.isUpper = true → l.column = ρ.cr →
      SameRow M l.column cv.row → SameRow R ref.column cu.row := by
  intro s n D M out ρ R t X x i es hS j hj cu cv ref l pe pa cpe cpa hL hup hl hsm
  obtain ⟨jn, cn, hjn0, hcn, hcnrow⟩ := hsm
  have hV := build_valid_of_success hS.splice.build
  obtain ⟨col', t', hcol', ht', _, hcrx, hinv⟩ := spliceCase_data hS.splice hS.run
  have htt : t' = t := by
    obtain ⟨col, hcol, ht⟩ := hS.last
    have : col' = col := Option.some.inj (hcol'.symm.trans hcol)
    subst this
    exact Option.some.inj (ht'.symm.trans ht)
  subst t'
  have hipos := hS.iPos
  have himg := leg_image hS hj hL
  rw [hl, mapColumn_of_ge (le_refl _)] at himg
  -- the row of `u` is the row of its origin
  obtain ⟨cv', hcv', hrowj⟩ := emitsT_upper_row hS.emits es[j] (List.getElem_mem hj) hup
  simp only [ctxAt] at hcv'
  rw [hL.hcv] at hcv'
  obtain rfl := Option.some.inj hcv'
  have hτ := emitsT_upper_ge hS.emits es[j] (List.getElem_mem hj) hup
  rw [hrowj] at hτ
  obtain ⟨_, hidx, _⟩ := emitsT_good hS.emits es[j] (List.getElem_mem hj)
  have hcv1 : (1 : Row) ≤ cv.row := one_le_row hV hL.hcv (by omega)
  obtain ⟨cX, hRX, hcopyX⟩ := hS.copy
  obtain ⟨_, hcellsX⟩ := cells_of_copy hRX hcopyX hS.emits
  obtain ⟨cellu, hcellu, hrowu⟩ := hcellsX j hj
  have hrowcu : cu.row = cv.row := by
    rw [Option.some.inj (hL.hcu.symm.trans hcellu), hrowu, hrowj, stored_official hcv1]
  -- the boundary column
  obtain ⟨_, _, colL, hcolL, _, _, _⟩ := highestAtMost_spec hL.hpe
  have hL0 : ρ.x0 ≤ ref.column := by
    rw [himg]
    have : ρ.x0 - ρ.cr ≤ (ρ.x0 - ρ.cr) * i := Nat.le_mul_of_pos_right _ hipos
    omega
  obtain ⟨hLsz, _⟩ := column_of_getElem? hcolL
  obtain ⟨i', x', _, hx', hLeq, hcopyL⟩ := hinv.2.2 ref.column hLsz hL0
  have hxx := boundary_x hcrx hipos hx' (by rw [← himg]; exact hLeq)
  subst hxx
  have hcolL' : R[ref.column]? = some R[ref.column] := Array.getElem?_eq_getElem hLsz
  obtain ⟨esl, hesl, _⟩ := copyColumn_emitsT hcopyL
  obtain ⟨_, hcellsL⟩ := cells_of_copy hcolL' hcopyL hesl
  have hupc : upperColumn (ctxAt M R ρ.x0 i' ρ.cr (ρ.x0 - ρ.cr) ρ.x0 ref.column) = ρ.cr := by
    simp [upperColumn, ctxAt]
  have hmem := mem_realNodes_of_cell hcn hjn0
  rw [hl, ← hupc] at hmem
  have hτn : official t.row ≤ official cn.row := by rw [hcnrow]; exact hτ
  obtain ⟨k, hk, hrowk⟩ := emitsT_upper_mem hesl hmem hτn
  obtain ⟨cell, hcell, hrow⟩ := hcellsL k hk
  have hcn1 : (1 : Row) ≤ cn.row := one_le_row hV hcn (by show 1 ≤ jn; omega)
  refine ⟨k + 1, cell, by omega, hcell, ?_⟩
  rw [hrow, hrowk, stored_official hcn1, hcnrow, hrowcu]

/-! ## `StepJumpLe` for upper origins -/

/-- The exponent of a bump step is determined by its result. -/
theorem bump_exp_unique {a b : Row} {e f : Nat} (h : Row.bump a e = Row.bump b f) : e = f := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have h1 := congrArg (fun r => Row.coeff r e) h
    simp only [Row.coeff_bump_at, Row.coeff_bump_low hlt] at h1
    omega
  · have h1 := congrArg (fun r => Row.coeff r f) h
    simp only [Row.coeff_bump_at, Row.coeff_bump_low hlt] at h1
    omega

theorem jump_bump_left (a : Row) (e : Nat) : Row.jump (Row.bump a e) a = e + 1 := by
  rw [Row.jump_comm]
  exact Row.jump_bump a e

theorem cell_getElem {N : Mountain} {c j : Nat} {cell : Cell} (h : cell? N ⟨c, j⟩ = some cell) :
    ∃ hc : c < N.size, N[c][j]? = some cell := by
  obtain ⟨col, hcol, hcj⟩ := cell?_spec h
  obtain ⟨hc, hcolEq⟩ := column_of_getElem? hcol
  exact ⟨hc, by rw [hcolEq]; exact hcj⟩

/-- **`StepJumpLe` for upper origins.** The copy has the row of its origin, and in both
columns consecutive rows are bump steps (`bumpChainHolds` for the output, the row law for
`M(s)`): the exponent of a bump step is determined by its result. -/
theorem stepJumpLe_upper :
    ∀ s n D M out ρ R t X x i es, Site s n D M out ρ R t X x i es →
    ∀ j (hj : j < es.length),
    ∀ cu cv ref l pe pa cpe cpa, Legs M R X j es[j].2 cu cv ref l pe pa cpe cpa →
      es[j].2.isUpper = true → ¬ SameRow M l.column cv.row → 0 < j →
      ∀ cd cvd : Cell, cell? R ⟨X, j⟩ = some cd →
        cell? M ⟨es[j].2.src.column, es[j].2.src.index - 1⟩ = some cvd →
        Row.jump cu.row cd.row ≤ Row.jump cv.row cvd.row := by
  intro s n D M out ρ R t X x i es hS j hj cu cv ref l pe pa cpe cpa hL hup hsm hj0 cd cvd hcd
    hcvd
  have hV := build_valid_of_success hS.splice.build
  obtain ⟨_, _, hx0⟩ := site_top hS
  -- the row of `u` is the row of its origin
  obtain ⟨cv', hcv', hrowj⟩ := emitsT_upper_row hS.emits es[j] (List.getElem_mem hj) hup
  simp only [ctxAt] at hcv'
  rw [hL.hcv] at hcv'
  obtain rfl := Option.some.inj hcv'
  obtain ⟨_, hidx, _⟩ := emitsT_good hS.emits es[j] (List.getElem_mem hj)
  have hcv1 : (1 : Row) ≤ cv.row := one_le_row hV hL.hcv (by omega)
  obtain ⟨cX, hRX, hcopyX⟩ := hS.copy
  obtain ⟨_, hcellsX⟩ := cells_of_copy hRX hcopyX hS.emits
  obtain ⟨cellu, hcellu, hrowu⟩ := hcellsX j hj
  have hrowcu : cu.row = cv.row := by
    rw [Option.some.inj (hL.hcu.symm.trans hcellu), hrowu, hrowj, stored_official hcv1]
  -- the output step `u⁻ → u`
  obtain ⟨hXs, hRd⟩ := cell_getElem hcd
  obtain ⟨_, hRu⟩ := cell_getElem hL.hcu
  have hsz := build_size hS.splice.build
  have hX0 := hS.X0
  obtain ⟨e1, he1⟩ := Recon.RowLaw.bumpChainHolds s n R hS.run X hXs (by omega) j cd cu hRd
    hRu hj0
  -- the source step `o⁻ → o`
  obtain ⟨k, cvd', hk, hcvd', _⟩ := jump_highest_step hS.splice.build hL.hcv (by omega) hL.hl
    hL.hpa hL.hcpa hsm
  rw [hk, show k + 2 - 1 = k + 1 by omega] at hcvd
  rw [hcvd] at hcvd'
  obtain rfl := Option.some.inj hcvd'
  obtain ⟨hMs, hMd⟩ := cell_getElem hcvd
  have hsrc : es[j].2.src = ⟨es[j].2.src.column, k + 1 + 1⟩ := by
    rw [← hk]
  have hcv2 := hL.hcv
  rw [hsrc] at hcv2
  obtain ⟨_, hMu⟩ := cell_getElem hcv2
  obtain ⟨_, _, _, _, _, _, hrow, _, _⟩ :=
    build_steps hS.splice.build es[j].2.src.column hMs (k + 1) cvd cv hMd hMu (by omega)
  unfold Row.B at hrow
  have he : e1 = Row.jump cvd.row _ := bump_exp_unique (he1.symm.trans (hrowcu.trans hrow))
  rw [he1, hrow, jump_bump_left, jump_bump_left, he]

/-- What the plain rows need from one child `c` of an item `it` of level `d + 2`: its source
and target are the slots `h` and `j`; a child without cut bottom sends a slot `h ≥ 1` to a
slot `j ≥ 1`; a child of an item with cut bottom has cut bottom or a slot `h ≥ 1`; a plain
child of level `1` has no cut bottom. -/
def ChildProp (d : Nat) (it c : Item) : Prop :=
  ∃ h j, c.source = slot (d + 2) it.source h ∧ c.target = slot (d + 2) it.target j ∧
    (c.cutBottom = false → 1 ≤ h → 1 ≤ j) ∧
    (it.cutBottom = true → c.cutBottom = true ∨ 1 ≤ h) ∧
    (d = 0 → c.clean = none → c.cutBottom = false)

open Recon Recon.RowLaw Dimension in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
set_option linter.unnecessarySeqFocus false in
/-- **The children of an item, for the plain rows.** -/
theorem childProps {s : List Nat} {ctx : Context} {t : Cell} {root : Ref}
    (hctx : RunCtx s ctx t root) {d : Nat} {it : Item}
    (hit : ItemOK ctx (official t.row) (d + 2) it) :
    Ok (childItems ctx (d + 2) it) (fun cs => ∀ c ∈ cs, ChildProp d it c) := by
  have hb : Canonical.build s = .ok ctx.source := hctx.top.build
  unfold childItems
  dsimp only
  split
  · refine ok_pure ?_
    intro c hc
    simp at hc
  · rename_i aRef aCell hA
    refine ok_bind (ok_eq _) (fun asc hasc => ?_)
    split
    · -- case 1: not ascending
      split
      · exact ok_throw_bind _ _
      · rename_i hflags
        have hcb : it.cutBottom = false := by
          cases h : it.cutBottom
          · rfl
          · exact absurd (Or.inr (Or.inr h)) hflags
        refine ok_pure ?_
        intro c hc
        simp only [List.mem_map, List.mem_range] at hc
        obtain ⟨j, _, rfl⟩ := hc
        exact ⟨j, j, rfl, rfl, fun _ h => h, fun h => (by rw [hcb] at h; cases h), fun _ _ => rfl⟩
    · rename_i hasc'
      have hasc_true : asc = true := by simpa using hasc'
      subst hasc_true
      obtain ⟨⟨ρRef, ρCell⟩, hρ, p, hp, hprow⟩ := node_of_ascends hctx hasc
      obtain ⟨_, hρin, _⟩ := topIn_spec hρ
      rw [hρ]
      generalize heightOf (d + 2) (topIn ctx.result ctx.boundary (d + 2) it.target) = hB
      simp only [heightOf, height_eq]
      split
      · rename_i hcl
        split
        · -- case 2: lift
          rename_i hcut
          have hρ' : topIn ctx.source root.column (d + 2) it.source = some (ρRef, ρCell) := by
            rw [← hctx.rootc]; exact hρ
          obtain ⟨⟨κRef, κCell⟩, hκ, hle⟩ := Top.rootCut_region hctx.top hit.below hρ'
          have hκ' : topIn ctx.source ctx.lastColumn (d + 2) it.source = some (κRef, κCell) := by
            rw [hctx.last]; exact hκ
          have hRK : (official ρCell.row).coeff d ≤ (official κCell.row).coeff d :=
            coeff_le_of_inRegion hρin (topIn_spec hκ).2.1 hle
          rw [hκ']
          have hlift : (0 : Int) ≤ ((((official κCell.row).coeff d : Nat) : Int) -
              (((official ρCell.row).coeff d : Nat) : Int)) * ctx.block :=
            Int.mul_nonneg (by omega) (Int.natCast_nonneg _)
          have hcb : it.cutBottom = false := by simpa using hcut
          generalize ((((official κCell.row).coeff d : Nat) : Int) -
              (((official ρCell.row).coeff d : Nat) : Int)) * ctx.block = lift at hlift ⊢
          generalize (official ρCell.row).coeff d = hR
          generalize hedef : (if d + 2 = 2 then 1 else 0 : Int) = e
          have he : 0 ≤ e := by rw [← hedef]; split <;> omega
          have he0 : d = 0 → e = 1 := by intro h0; rw [← hedef]; simp [h0]
          refine ok_pure ?_
          intro c hc
          simp only [List.mem_map, List.mem_range] at hc
          obtain ⟨j, _, rfl⟩ := hc
          by_cases h1 : j < hR
          · simp only [h1, if_true]
            exact ⟨j, j, rfl, rfl, fun _ h => h, fun h => (by rw [hcb] at h; cases h),
              fun _ _ => rfl⟩
          · simp only [h1, if_false]
            by_cases h2 : (j : Int) < hR + lift + e
            · simp only [h2, if_true]
              refine ⟨hR, j, rfl, rfl, ?_, fun h => (by rw [hcb] at h; cases h), fun _ h => (by cases h)⟩
              intro hb' hh
              simp only [decide_eq_false_iff_not] at hb'
              omega
            · simp only [h2, if_false]
              refine ⟨((j : Int) - lift).toNat, j, rfl, rfl, ?_, fun h => (by rw [hcb] at h; cases h),
                ?_⟩
              · intro _ hh
                omega
              · intro h0 _
                have := he0 h0
                simp only [decide_eq_false_iff_not]
                omega
        · -- case 3: cut bottom
          rename_i hcut
          have hcb : it.cutBottom = true := by simpa using hcut
          generalize (official ρCell.row).coeff d = hR
          generalize hedef : (if d + 2 = 2 then 1 else 0 : Int) = e
          have he : 0 ≤ e := by rw [← hedef]; split <;> omega
          have he0 : d = 0 → e = 1 := by intro h0; rw [← hedef]; simp [h0]
          refine ok_pure ?_
          intro c hc
          simp only [List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq] at hc
          obtain ⟨j, ⟨_, hjR⟩, rfl⟩ := hc
          by_cases h2 : (j : Int) < hB + hR + e
          · simp only [h2, if_true]
            exact ⟨hR, j - hR, rfl, rfl, fun h => (by cases h), fun _ => Or.inl rfl,
              fun _ h => (by cases h)⟩
          · simp only [h2, if_false]
            refine ⟨j - hB, j - hR, rfl, rfl, ?_, ?_, ?_⟩
            · intro hb' _
              simp only [decide_eq_false_iff_not] at hb'
              omega
            · intro _
              by_cases h3 : j = hB + hR
              · left; simp [h3]
              · right; omega
            · intro h0 _
              have := he0 h0
              simp only [decide_eq_false_iff_not]
              omega
      · -- case 4: a copied root row
        rename_i C hC
        split
        · exact ok_throw_bind _ _
        · rename_i q hq
          obtain ⟨csRef, cs⟩ := q
          simp only [pure, Except.pure, bind, Except.bind]
          cases hg : generations ctx.source ctx.rootColumn C (ctx.x + 1) csRef cs 0 with
          | error _ => intro _ h; cases h
          | ok g =>
            simp only
            split
            · intro _ h; cases h
            · generalize (official ρCell.row).coeff d = hR
              intro children hch
              simp only [Except.ok.injEq] at hch
              subst hch
              intro c hc
              simp only [List.mem_map, List.mem_range] at hc
              obtain ⟨j, _, rfl⟩ := hc
              by_cases hcb : it.cutBottom = true
              · simp only [hcb, if_true]
                exact ⟨hR, j, rfl, rfl, fun h => (by cases h), fun _ => Or.inl rfl,
                  fun _ h => (by cases h)⟩
              · have hcb' : it.cutBottom = false := by simpa using hcb
                simp only [hcb', Bool.false_eq_true, if_false]
                by_cases h1 : j < hR
                · simp only [h1, if_true]
                  exact ⟨j, j, rfl, rfl, fun _ h => h, fun h => (by rw [hcb'] at h; cases h),
                    fun _ _ => rfl⟩
                · simp only [h1, if_false]
                  refine ⟨hR, j, rfl, rfl, ?_, fun h => (by rw [hcb'] at h; cases h),
                    fun _ h => (by cases h)⟩
                  intro hb' hh
                  simp only [decide_eq_false_iff_not] at hb'
                  omega

/-- A copied root row `C` of an item is the row of the top of the root column in the source
region of the item. -/
def CleanTop (ctx : Context) (d : Nat) (it : Item) : Prop :=
  ∀ C, it.clean = some C → ∃ ρ, topIn ctx.source ctx.rootColumn d it.source = some ρ ∧
    official ρ.2.row = C

theorem cleanTop_slot {ctx : Context} {d : Nat} {S : Row} {ρ : Ref × Cell}
    (h : topIn ctx.source ctx.rootColumn (d + 2) S = some ρ) :
    topIn ctx.source ctx.rootColumn (d + 1) (slot (d + 2) S (height (d + 2) (official ρ.2.row))) =
      some ρ := by
  obtain ⟨_, hin, _⟩ := Recon.RowLaw.topIn_spec h
  refine Recon.topIn_sub h (fun r hr => Recon.RowLaw.inRegion_of_slot hr) ?_
  exact Recon.RowLaw.inRegion_slot_iff.mpr ⟨hin, by rw [Recon.RowLaw.height_eq]⟩

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
set_option linter.unnecessarySeqFocus false in
theorem childItems_cleanTop {ctx : Context} {d : Nat} {it : Item} {cs : List Item}
    (h : childItems ctx (d + 2) it = .ok cs) (hit : CleanTop ctx (d + 2) it) :
    ∀ c ∈ cs, CleanTop ctx (d + 1) c := by
  unfold childItems at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  generalize hrho : topIn ctx.source ctx.rootColumn (d + 2) it.source = rho at h
  split at h
  · obtain rfl := Except.ok.inj h
    simp
  · split at h
    · cases h
    · rename_i v hv
      split at h
      · split at h
        · simp [throw, throwThe, MonadExceptOf.throw] at h
        · obtain rfl := Except.ok.inj h
          intro c hc
          simp only [List.mem_map, List.mem_range] at hc
          obtain ⟨j, _, rfl⟩ := hc
          intro C' hC'
          simp at hC'
      · rename_i hasc
        have hvt : v = true := by simpa using hasc
        subst hvt
        have hsome : ∃ r cl, rho = some (r, cl) := by
          cases rho with
          | none => simp [ascends, pure, Except.pure] at hv
          | some p => exact ⟨p.1, p.2, rfl⟩
        obtain ⟨r, cl, rfl⟩ := hsome
        have hsl := cleanTop_slot hrho
        simp only at h hsl
        split at h
        · rename_i hclean
          split at h
          · obtain rfl := Except.ok.inj h
            intro c hc
            simp only [List.mem_map, List.mem_range] at hc
            obtain ⟨j, _, rfl⟩ := hc
            (try split_ifs) <;> intro C' hC' <;>
              simp only [Option.some.injEq, reduceCtorEq] at hC' <;> subst hC' <;>
              exact ⟨_, hsl, rfl⟩
          · obtain rfl := Except.ok.inj h
            intro c hc
            simp only [List.mem_map, List.mem_filter, List.mem_range] at hc
            obtain ⟨j, _, rfl⟩ := hc
            (try split_ifs) <;> intro C' hC' <;>
              simp only [Option.some.injEq, reduceCtorEq] at hC' <;> subst hC' <;>
              exact ⟨_, hsl, rfl⟩
        · rename_i C hclean
          obtain ⟨ρ0, hρ0, hρ0row⟩ := hit C hclean
          rw [hrho] at hρ0
          obtain rfl := Option.some.inj hρ0
          split at h
          · simp [throw, throwThe, MonadExceptOf.throw] at h
          · split at h
            · cases h
            · split at h
              · simp [throw, throwThe, MonadExceptOf.throw] at h
              · obtain rfl := Except.ok.inj h
                intro c hc
                simp only [List.mem_map, List.mem_range] at hc
                obtain ⟨j, _, rfl⟩ := hc
                (try split_ifs) <;> intro C' hC' <;>
                  simp only [Option.some.injEq, reduceCtorEq] at hC' <;> (try subst hC') <;>
                  exact ⟨_, hsl, hρ0row⟩

/-! ## The lowest coefficients of non-cut copies -/

/-- The origin `o` is plain or a clean (non-gap) copy of the node `r`. -/
def NonCut (o : Origin) (r : Ref) : Prop := o = .plain r ∨ o = .clean r false

/-- A non-cut origin (row `σ`) and its copy (row `θ`, official rows) in an item of level
`d`: `σ` lies in the source region and `θ` in the target region; below the level, a nonzero
coefficient of `σ` at `e` gives a nonzero coefficient of `θ` at some `k ≤ e`; under a cut
bottom, `σ` is not the base of the source region. -/
def NonCutLow (ctx : Context) (d : Nat) (it : Item) (p : Emit × Origin) : Prop :=
  ∀ r, NonCut p.2 r → ∃ c, cell? ctx.source r = some c ∧ r.column = ctx.x ∧ 1 ≤ r.index ∧
    inRegion d it.source (official c.row) = true ∧ inRegion d it.target p.1.row = true ∧
    (∀ e, e + 1 < d → (official c.row).coeff e ≠ 0 → ∃ k, k ≤ e ∧ p.1.row.coeff k ≠ 0) ∧
    (it.cutBottom = true → ∃ e, e + 1 < d ∧ (official c.row).coeff e ≠ 0)

theorem levelOneT_nonCutLow {ctx : Context} {it : Item}
    (hcb : it.clean = none → it.cutBottom = false) (hct : CleanTop ctx 1 it)
    {ps : List (Emit × Origin)} (h : levelOneT ctx it = .ok ps) :
    ∀ p ∈ ps, NonCutLow ctx 1 it p := by
  unfold levelOneT at h
  cases hsrc : nodeAt ctx.source ctx.x it.source with
  | none => simp [hsrc, pure, Except.pure] at h; subst h; simp
  | some q =>
      obtain ⟨srcRef, src⟩ := q
      obtain ⟨hcol, hidx, hcell, hrow⟩ := Classification.nodeAt_spec hsrc
      simp only [hsrc] at h
      cases hC : it.clean with
      | some C =>
          simp only [hC] at h
          cases hcs : nodeAt ctx.source ctx.x C with
          | none => simp [hcs, throw, throwThe, MonadExceptOf.throw] at h
          | some q' =>
              obtain ⟨csRef, cs⟩ := q'
              obtain ⟨hcol', hidx', hcell', hrow'⟩ := Classification.nodeAt_spec hcs
              obtain ⟨ρ, hρ, hρrow⟩ := hct C hC
              obtain ⟨_, hρin, _⟩ := Recon.RowLaw.topIn_spec hρ
              simp only [hcs, bind, Except.bind, pure, Except.pure] at h
              split at h
              · cases h
              · cases h
                intro p hp
                simp only [List.mem_singleton] at hp
                subst hp
                intro r hr
                rcases hr with hr | hr
                · cases hr
                · simp only [Origin.clean.injEq] at hr
                  obtain ⟨rfl, hcbf⟩ := hr
                  refine ⟨cs, hcell', hcol', hidx', ?_, ?_, fun e he => by omega, ?_⟩
                  · rw [hrow', ← hρrow]; exact hρin
                  · exact Recon.RowLaw.self_inRegion 1 it.target
                  · intro h'; rw [hcbf] at h'; cases h'
      | none =>
          have hcb' := hcb hC
          simp only [hC] at h
          have key : ∀ (em : Emit), em.row = it.target →
              NonCutLow ctx 1 it (em, .plain srcRef) := by
            intro em hem r hr
            rcases hr with hr | hr
            · simp only [Origin.plain.injEq] at hr
              subst hr
              refine ⟨src, hcell, hcol, hidx, ?_, ?_, fun e he => by omega, ?_⟩
              · rw [hrow]; exact Recon.RowLaw.self_inRegion 1 it.source
              · rw [hem]; exact Recon.RowLaw.self_inRegion 1 it.target
              · intro h'; rw [hcb'] at h'; cases h'
            · cases hr
          split at h
          · simp only [pure, Except.pure, Except.ok.injEq] at h
            subst h
            intro p hp
            simp only [List.mem_singleton] at hp
            subst hp
            exact key _ rfl
          · simp only [bind, Except.bind, pure, Except.pure] at h
            split at h
            · cases h
            · cases h
              intro p hp
              simp only [List.mem_singleton] at hp
              subst hp
              exact key _ rfl

open Recon Recon.RowLaw Dimension in
/-- **The non-cut rows of a processed item.** -/
theorem runItemT_nonCutLow {s : List Nat} {ctx : Context} {t : Cell} {root : Ref}
    (hctx : RunCtx s ctx t root) :
    ∀ d, 1 ≤ d → ∀ it, ItemOK ctx (official t.row) d it →
      (d = 1 → it.clean = none → it.cutBottom = false) → CleanTop ctx d it →
      ∀ ps, runItemT ctx d it = .ok ps → ∀ p ∈ ps, NonCutLow ctx d it p := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hd1 it hit hcb1 hct ps h
    match d, ih, hd1, hcb1, hit, hct, h with
    | 1, _, _, hcb1, _, hct, h =>
      exact levelOneT_nonCutLow (hcb1 rfl) hct (by simpa [runItemT] using h)
    | d + 2, ih, _, _, hit, hct, h =>
      simp only [runItemT, bind, Except.bind, pure, Except.pure] at h
      split at h
      · cases h
      · rename_i children hch
        split at h
        · cases h
        · rename_i outs houts
          cases h
          have hspec := childSpec hctx hit children hch
          have hprops := childProps hctx hit children hch
          have hcts := childItems_cleanTop hch hct
          obtain ⟨n, F, σ, hcs, htgt, hsrc, _, _, hoff⟩ := hspec
          intro p hp
          obtain ⟨out, hout, hpo⟩ := List.mem_flatten.mp hp
          obtain ⟨c, hc, hco⟩ := mem_of_mapM houts hout
          have hcok : ItemOK ctx (official t.row) (d + 1) c := by
            rw [hcs] at hc
            obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hc
            have hj' : j < n := List.mem_range.mp hj
            refine ⟨?_, ?_, hoff j hj'⟩
            · rw [htgt j]
              exact slot_zeroBelow d it.target j
            · intro r hr
              rw [hsrc j] at hr
              exact hit.below r (inRegion_of_slot hr)
          obtain ⟨hh, jj, hs, ht, hmap, hbp, hl1⟩ := hprops c hc
          have hIH := ih (d + 1) (by omega) (by omega) c hcok
            (fun h1 => hl1 (by omega)) (hcts c hc) out hco p hpo
          intro r hr
          obtain ⟨cc, hcell, hcol, hidx, hin, htg, hA, hB⟩ := hIH r hr
          rw [hs] at hin
          rw [ht] at htg
          obtain ⟨hin', hσd⟩ := inRegion_slot_iff.mp hin
          obtain ⟨htg', hθd⟩ := inRegion_slot_iff.mp htg
          refine ⟨cc, hcell, hcol, hidx, hin', htg', ?_, ?_⟩
          · intro e he hne
            rcases Nat.lt_or_ge e d with hlt | hge
            · exact hA e (by omega) hne
            · have hed : e = d := by omega
              subst hed
              have hh1 : 1 ≤ hh := by rw [← hσd]; omega
              cases hcbc : c.cutBottom
              · have := hmap hcbc hh1
                exact ⟨e, le_refl _, by rw [hθd]; omega⟩
              · obtain ⟨e', he', hne'⟩ := hB hcbc
                obtain ⟨k, hk, hk'⟩ := hA e' he' hne'
                exact ⟨k, by omega, hk'⟩
          · intro hcbt
            rcases hbp hcbt with hc' | hh1
            · obtain ⟨e', he', hne'⟩ := hB hc'
              exact ⟨e', by omega, hne'⟩
            · exact ⟨d, by omega, by rw [hσd]; omega⟩

open Recon Recon.RowLaw Dimension in
/-- **The lowest nonzero coefficient of a non-cut copy of the lower part is at most that of
its origin.** -/
theorem emitsT_nonCutLow {s : List Nat} {ctx : Context} {t : Cell} {root : Ref}
    (hctx : RunCtx s ctx t root) {es : List (Emit × Origin)}
    (h : emitsT ctx (official t.row) = .ok es) :
    ∀ p ∈ es, ∀ r, NonCut p.2 r → ∃ c, cell? ctx.source r = some c ∧ r.column = ctx.x ∧
      1 ≤ r.index ∧ ∀ e, (official c.row).coeff e ≠ 0 → ∃ k, k ≤ e ∧ p.1.row.coeff k ≠ 0 := by
  unfold emitsT at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i lower hlower
    split at h
    · cases h
    · rename_i upper hupper
      cases h
      intro p hp r hr
      rcases List.mem_append.mp hp with hp | hp
      · unfold lowerT at hlower
        simp only [bind, Except.bind, pure, Except.pure] at hlower
        split at hlower
        · cases hlower
        · rename_i outs houts
          cases hlower
          obtain ⟨out, hout, hpo⟩ := List.mem_flatten.mp hp
          obtain ⟨q, hq, hqo⟩ := mem_of_mapM houts hout
          obtain ⟨hok, hst, hq1, _⟩ := lower_itemOK (ctx := ctx) hq
          have hq' : q.2.cutBottom = false ∧ q.2.clean = none := by
            obtain ⟨k, j, _, _, rfl⟩ := mem_lowerItems hq
            exact ⟨rfl, rfl⟩
          have hctq : CleanTop ctx q.1 q.2 := by
            intro C hC; rw [hq'.2] at hC; cases hC
          obtain ⟨c, hcell, hcol, hidx, hin, htg, hA, _⟩ :=
            runItemT_nonCutLow hctx q.1 hq1 q.2 hok (fun _ _ => hq'.1) hctq out hqo p hpo r hr
          refine ⟨c, hcell, hcol, hidx, ?_⟩
          intro e hne
          rcases Nat.lt_or_ge (e + 1) q.1 with hlt | hge
          · exact hA e hlt hne
          · refine ⟨e, le_refl _, ?_⟩
            rw [hst] at hin
            have h1 := (inRegion_iff'.mp hin) e (by omega)
            have h2 := (inRegion_iff'.mp htg) e (by omega)
            rw [h2, ← h1]
            exact hne
      · unfold upperT at hupper
        obtain ⟨q, _, hqp⟩ := mem_of_mapM hupper hp
        simp only [bind, Except.bind, pure, Except.pure] at hqp
        split at hqp
        · cases hqp
        · cases hqp
          rcases hr with hr | hr <;> cases hr

/-! ## The remaining lower-part statements -/

/-- (open) `LegRowMatchRoot` for origins of the lower part (plain or clean). Numerically the
copy then has the row of its origin, and the boundary column `cr + w·i` has at that row the
copy (in block `i - 1`) of the node of `x₀` at that row. -/
def LegRowMatchRootLower : Prop :=
  ∀ s n D M out ρ R t X x i es, Site s n D M out ρ R t X x i es →
    ∀ j (hj : j < es.length), cutOrigin es[j].2 = false →
    ∀ cu cv ref l pe pa cpe cpa, Legs M R X j es[j].2 cu cv ref l pe pa cpe cpa →
      es[j].2.isUpper = false → l.column = ρ.cr →
      SameRow M l.column cv.row → SameRow R ref.column cu.row

theorem legRowMatchRoot_of_lower (h : LegRowMatchRootLower) : LegRowMatchRoot := by
  intro s n D M out ρ R t X x i es hS j hj hnc cu cv ref l pe pa cpe cpa hL hnot hl hsm
  cases hup : es[j].2.isUpper
  · exact h s n D M out ρ R t X x i es hS j hj hnc cu cv ref l pe pa cpe cpa hL hup hl hsm
  · exact legRowMatchRoot_upper s n D M out ρ R t X x i es hS j hj cu cv ref l pe pa cpe cpa hL
      hup hl hsm

/-- (proved: `stepJumpLeLower`) `StepJumpLe` for origins of the lower part (plain or clean,
not a gap copy). -/
def StepJumpLeLower : Prop :=
  ∀ s n D M out ρ R t X x i es, Site s n D M out ρ R t X x i es →
    ∀ j (hj : j < es.length), cutOrigin es[j].2 = false →
    ∀ cu cv ref l pe pa cpe cpa, Legs M R X j es[j].2 cu cv ref l pe pa cpe cpa →
      es[j].2.isUpper = false → ¬ SameRow M l.column cv.row → 0 < j →
      ∀ cd cvd : Cell, cell? R ⟨X, j⟩ = some cd →
        cell? M ⟨es[j].2.src.column, es[j].2.src.index - 1⟩ = some cvd →
        Row.jump cu.row cd.row ≤ Row.jump cv.row cvd.row

theorem stepJumpLe_of_lower (h : StepJumpLeLower) : StepJumpLe := by
  intro s n D M out ρ R t X x i es hS j hj hnc cu cv ref l pe pa cpe cpa hL hnot hsm hj0 cd cvd
    hcd hcvd
  cases hup : es[j].2.isUpper
  · exact h s n D M out ρ R t X x i es hS j hj hnc cu cv ref l pe pa cpe cpa hL hup hsm hj0 cd
      cvd hcd hcvd
  · exact stepJumpLe_upper s n D M out ρ R t X x i es hS j hj cu cv ref l pe pa cpe cpa hL hup
      hsm hj0 cd cvd hcd hcvd

/-! ## `StepJumpLe` for non-cut origins of the lower part -/

theorem site_runCtx {s : List Nat} {n D : Nat} {M : Mountain} {out : List Nat} {ρ : Root}
    {R : Mountain} {t : Cell} {X x i : Nat} {es : List (Emit × Origin)}
    (hS : Site s n D M out ρ R t X x i es) :
    ∃ root, Recon.RunCtx s (ctxAt M R x i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 X) t root := by
  obtain ⟨root, hTop, hroot, hx0⟩ := site_top hS
  obtain ⟨hcx, hxx⟩ := mem_blockColumns_pos hS.xMem hS.iPos
  refine ⟨root, ⟨hTop, hx0, hroot.symm, hcx, hxx, ?_⟩⟩
  simp only [ctxAt, Array.size_extract]
  have := hS.XR
  have := hS.Xeq
  omega

/-- A row whose stored form has a nonzero coefficient at `e₂`: a row `θ` whose lowest
nonzero coefficient is at most that of `σ` has a stored nonzero coefficient at some
`m ≤ e₂`. -/
theorem stored_low {σ θ : Row} (hσ : σ ≠ 0)
    (hlow : ∀ e, σ.coeff e ≠ 0 → ∃ k, k ≤ e ∧ θ.coeff k ≠ 0) {e2 : Nat}
    (h : (stored σ).coeff e2 ≠ 0) : ∃ m, m ≤ e2 ∧ (stored θ).coeff m ≠ 0 := by
  rw [Recon.RowLaw.coeff_stored] at h
  rcases Nat.eq_zero_or_pos e2 with he | he
  · subst he
    refine ⟨0, le_refl _, ?_⟩
    rw [Recon.RowLaw.coeff_stored]
    by_cases hfθ : isFinite θ = true
    · simp [hfθ]
    · simp only [hfθ]
      have hσ0 : σ.coeff 0 ≠ 0 := by
        by_cases hfσ : isFinite σ = true
        · intro h0
          apply hσ
          apply Recon.row_ext
          intro k
          rcases Nat.eq_zero_or_pos k with hk | hk
          · subst hk; rw [h0]; simp
          · rw [(Recon.isFinite_iff' σ).mp hfσ k hk]; simp
        · simpa [hfσ] using h
      obtain ⟨k, hk, hk'⟩ := hlow 0 hσ0
      have : k = 0 := by omega
      subst this
      exact hk'
  · have hσe : σ.coeff e2 ≠ 0 := by
      have hne : ¬ (e2 = 0 ∧ isFinite σ = true) := fun h' => by omega
      simpa [hne] using h
    obtain ⟨k, hk, hk'⟩ := hlow e2 hσe
    refine ⟨k, hk, ?_⟩
    rw [Recon.RowLaw.coeff_stored]
    split
    · omega
    · exact hk'

/-- **`StepJumpLe` for plain and clean origins.** In both columns consecutive rows are bump
steps, so each jump is one more than the lowest nonzero coefficient of the upper row; for a
non-cut copy this coefficient is not higher than for its origin (`emitsT_nonCutLow`). -/
theorem stepJumpLe_nonCut :
    ∀ s n D M out ρ R t X x i es, Site s n D M out ρ R t X x i es →
    ∀ j (hj : j < es.length),
    ∀ cu cv ref l pe pa cpe cpa, Legs M R X j es[j].2 cu cv ref l pe pa cpe cpa →
      (∃ r, NonCut es[j].2 r) → ¬ SameRow M l.column cv.row → 0 < j →
      ∀ cd cvd : Cell, cell? R ⟨X, j⟩ = some cd →
        cell? M ⟨es[j].2.src.column, es[j].2.src.index - 1⟩ = some cvd →
        Row.jump cu.row cd.row ≤ Row.jump cv.row cvd.row := by
  intro s n D M out ρ R t X x i es hS j hj cu cv ref l pe pa cpe cpa hL hpl hsm hj0 cd cvd hcd
    hcvd
  have hV := build_valid_of_success hS.splice.build
  obtain ⟨_, _, hx0⟩ := site_top hS
  obtain ⟨root, hctx⟩ := site_runCtx hS
  obtain ⟨r, ho⟩ := hpl
  obtain ⟨c, hcell, _, _, hlow⟩ := emitsT_nonCutLow hctx hS.emits es[j] (List.getElem_mem hj) r ho
  simp only [ctxAt] at hcell
  have hcv := hL.hcv
  have hsrcr : es[j].2.src = r := by rcases ho with h | h <;> rw [h] <;> rfl
  rw [hsrcr] at hcv
  have hcc : c = cv := Option.some.inj (hcell.symm.trans hcv)
  subst c
  -- the copy
  obtain ⟨cX, hRX, hcopyX⟩ := hS.copy
  obtain ⟨_, hcellsX⟩ := cells_of_copy hRX hcopyX hS.emits
  obtain ⟨cellu, hcellu, hrowu⟩ := hcellsX j hj
  have hrowcu : cu.row = stored es[j].1.row := by
    rw [Option.some.inj (hL.hcu.symm.trans hcellu)]
    exact hrowu
  obtain ⟨hXs, hRd⟩ := cell_getElem hcd
  obtain ⟨_, hRu⟩ := cell_getElem hL.hcu
  have hsz := build_size hS.splice.build
  have hX0 := hS.X0
  obtain ⟨e1, he1⟩ := Recon.RowLaw.bumpChainHolds s n R hS.run X hXs (by omega) j cd cu hRd
    hRu hj0
  -- the origin
  obtain ⟨_, hidx, _⟩ := emitsT_good hS.emits es[j] (List.getElem_mem hj)
  obtain ⟨k, cvd', hk, hcvd', _⟩ := jump_highest_step hS.splice.build hL.hcv (by omega) hL.hl
    hL.hpa hL.hcpa hsm
  rw [hk, show k + 2 - 1 = k + 1 by omega] at hcvd
  rw [hcvd] at hcvd'
  obtain rfl := Option.some.inj hcvd'
  obtain ⟨hMs, hMd⟩ := cell_getElem hcvd
  have hsrc : es[j].2.src = ⟨es[j].2.src.column, k + 1 + 1⟩ := by
    rw [← hk]
  have hcv2 := hL.hcv
  rw [hsrc] at hcv2
  obtain ⟨_, hMu⟩ := cell_getElem hcv2
  obtain ⟨_, _, _, _, _, _, hrow, _, _⟩ :=
    build_steps hS.splice.build es[j].2.src.column hMs (k + 1) cvd cv hMd hMu (by omega)
  unfold Row.B at hrow
  rw [he1, hrow, jump_bump_left, jump_bump_left]
  generalize Row.jump cvd.row _ = e2 at hrow ⊢
  -- the lowest coefficients
  have hcv1 : (1 : Row) ≤ cv.row := one_le_row hV hL.hcv (by omega)
  have hcvne : (cv.row).coeff e2 ≠ 0 := by rw [hrow, Row.coeff_bump_at]; omega
  rw [← stored_official hcv1] at hcvne
  have hσ : official cv.row ≠ 0 := by
    intro h0
    have h1 := (Recon.official_zero_iff hcv1).mp h0
    have hlt : cvd.row < cv.row := by rw [hrow]; exact Row.lt_bump _ _
    have hc1 : (1 : Row) ≤ cvd.row := one_le_row hV hcvd (by simp)
    rw [h1] at hlt
    exact absurd (lt_of_le_of_lt hc1 hlt) (lt_irrefl _)
  obtain ⟨m, hm, hm'⟩ := stored_low hσ hlow hcvne
  rw [← hrowcu, he1] at hm'
  have : e1 ≤ m := by
    by_contra hn
    exact hm' (Row.coeff_bump_low (by omega))
  omega

/-- **`StepJumpLeLower` holds.** -/
theorem stepJumpLeLower : StepJumpLeLower := by
  intro s n D M out ρ R t X x i es hS j hj hnc cu cv ref l pe pa cpe cpa hL hup hsm hj0 cd cvd
    hcd hcvd
  have hnc' : ∃ r, NonCut es[j].2 r := by
    cases ho : es[j].2 with
    | plain r => exact ⟨r, Or.inl rfl⟩
    | clean r b =>
        cases b
        · exact ⟨r, Or.inr rfl⟩
        · rw [ho] at hnc; cases hnc
    | upper r => rw [ho] at hup; cases hup
  exact stepJumpLe_nonCut s n D M out ρ R t X x i es hS j hj cu cv ref l pe pa cpe cpa hL hnc'
    hsm hj0 cd cvd hcd hcvd

/-- **`StepJumpLe` holds.** -/
theorem stepJumpLe : StepJumpLe := stepJumpLe_of_lower stepJumpLeLower


/-! ## The step into a copy, for every non-cut origin -/

/-- **The step into a non-cut copy jumps no higher than the step into its origin.** For the
node `u = (X, j + 1)`, `j ≥ 1`, of a copied column whose origin `o` is not a gap copy and not
a bottom node: `jump(row u, row u⁻) ≤ jump(row o, row o⁻)`. For an upper origin the two jumps
are equal. (This is `StepJumpLe` without the hypothesis on the leg column; it also gives the
consecutive-pair statement `BumpCopy` of `ChainCorrStepInner.lean` whenever the upper copy
of the pair is not a gap copy.) -/
theorem stepJump_general {s : List Nat} {n D : Nat} {M : Mountain} {out : List Nat} {ρ : Root}
    {R : Mountain} {t : Cell} {X x i : Nat} {es : List (Emit × Origin)}
    (hS : Site s n D M out ρ R t X x i es) {j : Nat} (hj : j < es.length)
    (hnc : cutOrigin es[j].2 = false) {cu cv cd cvd : Cell}
    (hcu : cell? R ⟨X, j + 1⟩ = some cu) (hcv : cell? M es[j].2.src = some cv)
    (h2 : 2 ≤ es[j].2.src.index) (hj0 : 0 < j) (hcd : cell? R ⟨X, j⟩ = some cd)
    (hcvd : cell? M ⟨es[j].2.src.column, es[j].2.src.index - 1⟩ = some cvd) :
    Row.jump cu.row cd.row ≤ Row.jump cv.row cvd.row := by
  have hV := build_valid_of_success hS.splice.build
  obtain ⟨_, _, hx0⟩ := site_top hS
  -- the copy
  obtain ⟨cX, hRX, hcopyX⟩ := hS.copy
  obtain ⟨_, hcellsX⟩ := cells_of_copy hRX hcopyX hS.emits
  obtain ⟨cellu, hcellu, hrowu⟩ := hcellsX j hj
  have hrowcu : cu.row = stored es[j].1.row := by
    rw [Option.some.inj (hcu.symm.trans hcellu)]
    exact hrowu
  obtain ⟨hXs, hRd⟩ := cell_getElem hcd
  obtain ⟨_, hRu⟩ := cell_getElem hcu
  have hsz := build_size hS.splice.build
  have hX0 := hS.X0
  obtain ⟨e1, he1⟩ := Recon.RowLaw.bumpChainHolds s n R hS.run X hXs (by omega) j cd cu hRd
    hRu hj0
  -- the origin
  obtain ⟨k, hk⟩ : ∃ k, es[j].2.src.index = k + 2 := ⟨es[j].2.src.index - 2, by omega⟩
  rw [hk, show k + 2 - 1 = k + 1 by omega] at hcvd
  obtain ⟨hMs, hMd⟩ := cell_getElem hcvd
  have hsrc : es[j].2.src = ⟨es[j].2.src.column, k + 1 + 1⟩ := by
    rw [← hk]
  have hcv2 := hcv
  rw [hsrc] at hcv2
  obtain ⟨_, hMu⟩ := cell_getElem hcv2
  obtain ⟨_, _, _, _, _, _, hrow, _, _⟩ :=
    build_steps hS.splice.build es[j].2.src.column hMs (k + 1) cvd cv hMd hMu (by omega)
  unfold Row.B at hrow
  rw [he1, hrow, jump_bump_left, jump_bump_left]
  generalize Row.jump cvd.row _ = e2 at hrow ⊢
  have hcv1 : (1 : Row) ≤ cv.row := one_le_row hV hcv (by omega)
  cases hup : es[j].2.isUpper
  · -- a plain origin or a clean copy
    have hnc' : ∃ r, NonCut es[j].2 r := by
      cases ho : es[j].2 with
      | plain r => exact ⟨r, Or.inl rfl⟩
      | clean r b =>
          cases b
          · exact ⟨r, Or.inr rfl⟩
          · rw [ho] at hnc; cases hnc
      | upper r => rw [ho] at hup; cases hup
    obtain ⟨_, hctx⟩ := site_runCtx hS
    obtain ⟨r, ho⟩ := hnc'
    obtain ⟨c, hcell, _, _, hlow⟩ :=
      emitsT_nonCutLow hctx hS.emits es[j] (List.getElem_mem hj) r ho
    simp only [ctxAt] at hcell
    have hsrcr : es[j].2.src = r := by rcases ho with h | h <;> rw [h] <;> rfl
    have hcv' := hcv
    rw [hsrcr] at hcv'
    have hcc : c = cv := Option.some.inj (hcell.symm.trans hcv')
    subst c
    have hcvne : (cv.row).coeff e2 ≠ 0 := by rw [hrow, Row.coeff_bump_at]; omega
    rw [← stored_official hcv1] at hcvne
    have hσ : official cv.row ≠ 0 := by
      intro h0
      have h1 := (Recon.official_zero_iff hcv1).mp h0
      have hlt : cvd.row < cv.row := by rw [hrow]; exact Row.lt_bump _ _
      have hc1 : (1 : Row) ≤ cvd.row := one_le_row hV hcvd (by simp)
      rw [h1] at hlt
      exact absurd (lt_of_le_of_lt hc1 hlt) (lt_irrefl _)
    obtain ⟨m, hm, hm'⟩ := stored_low hσ hlow hcvne
    rw [← hrowcu, he1] at hm'
    have : e1 ≤ m := by
      by_contra hn
      exact hm' (Row.coeff_bump_low (by omega))
    omega
  · -- an upper origin: the copy has the row of its origin
    obtain ⟨cv', hcv', hrowj⟩ := emitsT_upper_row hS.emits es[j] (List.getElem_mem hj) hup
    simp only [ctxAt] at hcv'
    rw [hcv] at hcv'
    obtain rfl := Option.some.inj hcv'
    have hrowe : cu.row = cv.row := by rw [hrowcu, hrowj, stored_official hcv1]
    have he : e1 = e2 := bump_exp_unique (he1.symm.trans (hrowe.trans hrow))
    omega

/-! ## Summary -/

/-- **`StartJump` from `StartLeg`, the block profile and the root-column case.** -/
theorem startJump_of_open (hLeg : StartLeg) (hA : CopyOrder) (hB : CopyEmitted)
    (hR : LegRowMatchRootLower) : StartJump :=
  startJump_of_parts (legRowMatch_of_parts hLeg hA hB (legRowMatchRoot_of_lower hR)) stepJumpLe

/-- **`StartLeg` and `StartJump` from the open statements.** `CopyOrder` and `CopyEmitted` are
the open statements (A) and (B) of `ChainCorrStartCopy.lean`. -/
theorem startLeg_startJump (hT : LegBelowTop) (hA : CopyOrder) (hB : CopyEmitted)
    (hR : LegRowMatchRootLower) : StartLeg ∧ StartJump :=
  ⟨startLeg_of_legBelowTop hT, startJump_of_open (startLeg_of_legBelowTop hT) hA hB hR⟩

end OmegaY.Official.Classification.Proofs.ChainCorr.LegJump

#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.LegJump.startLeg_of_legBelowTop
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.LegJump.startJump_of_parts
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.LegJump.legRowMatch_of_parts
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.LegJump.legRowMatchRoot_upper
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.LegJump.stepJumpLe_upper
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.LegJump.stepJumpLe
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.LegJump.stepJump_general
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.LegJump.startJump_of_open
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.LegJump.startLeg_startJump
