/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/ChainCorrStepInner.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
Port change: in `highestAtMost_of_max` the last step is `erw [hL]; rfl` instead of `simp` (the `match` written in the proof is a different matcher from the one in `highestAtMost`).
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.ChainCorrRegions
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.ChainsCanonParent
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.Regions
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.RowLawRows

set_option backward.do.legacy false

/-!
# `StepInner` (`ChainCorrRegions.lean`) from local statements

`ChainCorrRegions.StepInner` asks: for a copy node `v` (block `i ≥ 1`, inner column
`y + w·i`, `cr < y < x₀`) of a node `m` of `M(s)` and a step `m → m'` of the scale-`k` chain
of `M(s)`, the scale-`k` chain of the output from `v` matches the step (`Next`).
All declarations of this file are in the namespace `ChainCorr.Inner`.

## Part 1: the reduction (`stepInner_of_parts`)

`StepInner` follows from five statements, split by the origin of `v`.

* Plain and upper origins take one output step per step of `M(s)`. With `m⁺ = up m` (so
  `m' = left(m⁺)`): `NextCopy` (`up v` is a copy node of `m⁺`), `LeftCopy` (for the two
  consecutive copy pairs `(v, m)`, `(up v, up m)`, the raw parent `pe = left(up v)` of `v`
  matches `pa = left(up m)`: `pe = pa` left of `cr`, `CopyNode pe pa` right of `cr`, in the
  root column `pe` is in the boundary column `cr + w·i` and its chain reaches the next node
  of the chain of `pa`), `JumpCopy` (`jump(row v, row pe) ≤ jump(row m, row pa)`).
* A clean copy `v` (`b = 0`) of `a = (y, C)` is followed by gap copies of `a`, whose leg is the
  leg of `a`. The output chain from `v` walks along the generation chain of notes/03 §2.4
  (case 4) in the row `C`, `(y, C) → (g₁, C) → … → (cr, C)` (`GenStep`), one output step per
  generation, each in the same row, landing on the clean copy of the next generation and
  finally in the boundary column `cr + w·i` (`CleanStep`, proved as a walk in `clean_walk`).
  The step `m → m'` of `M(s)` lands on this chain, or, when `m'` is left of `cr`, it is the step
  from `(cr, C)` (`CleanParent`).

## Parts 2–4: proved pieces (both mountains are canonical in the setting of `StepInner`)

* `nextCopy_upper`: `NextCopy` for upper origins (the upper part lists the source nodes at rows
  `≥ τ` in order). Left: `NextCopyPlain`.
* `canon_rowLaw`: row law `row u⁺ = B(row u, row π(u⁺))` of a canonical mountain, so
  `jump(row u, row u⁺) = jump(row u, row π(u⁺)) + 1`, and `jumpCopy_of_bumpCopy`: `JumpCopy`
  from the one-column statement `BumpCopy` (`jump(row v, row v⁺) ≤ jump(row m, row m⁺)`);
  `bumpCopy_of_lower` proves it for two upper origins (an upper copy has the row of its
  origin, `upper_row`). Left: `BumpCopyLower`.
* `canon_rawParent_hAM`: in a canonical mountain the raw parent of a real node `v` is the
  highest node of its column at or below `row v`. Hence `LeftCopy` is a lookup at the row of
  `v` (`LegLookup`, `leftCopy_of_legLookup`, the same kind of statement as `StartCopy` /
  `StartRoot` at another column), and `CleanStep` is `CleanNext` (after a clean copy comes a
  gap copy of the same origin) and a lookup `CleanLookup` (`cleanStep_of_parts`).

## Parts 5–6: the profile of a column

* `nextCopyPlain_of_profile`: `NextCopyPlain` from `CopyEmitted`, `CopyMono`, `CopyFirst`
  (the same statements as in `ChainCorrStartCopy.lean`) and `PlainOnce`.
* **`copyMono_holds`, `plainOnce_holds` (proved).** In every column the origins of the emits
  come in row order, and two emits with origins at the same row are copies of the root row
  (`emitsT_order`, by induction over the items: `childItems_order`, `runItemT_order`).

## What is left (`stepInner_of_rest`)

`StepInner` follows from `CopyEmitted`, `CopyFirst` (shared with `StartCopy`), `LegLookup`,
`BumpCopyLower`, `CleanNext`, `CleanLookup` and `CleanParent`. The first four and `CleanNext`
are about the rule; they need facts about `M(s)` (for example that a clean copy at level 2 is
followed by a gap copy needs `h_κ > h_ρ`, notes/03 §2.4) and about the boundary column (the
heights `h_q`). `CleanParent` is about `M(s)` only, in the context of a clean copy: the
parent search from `(y, C)` follows the generation chain; the statement fails for general
nodes (for example `(1,2,3,2)`, node `(3,0)`: its parent `(0,0)` is neither on the chain
`(3,0) → (2,0)` nor the parent `(1,0)` of `(2,0)`).

## Numerical tests (`reference/official/step-inner.cjs`)

Counts: tested nodes. No failure.

| statement | standard S1–S3, S6 | legal ≤ 6, ≤ 6 | legal ≤ 5, ≤ 8 | random `20000,10,10,7` |
|---|---:|---:|---:|---:|
| `NextCopyPlain` | 342882 | 68634 | 43920 | 196974 |
| `PlainOnce` (proved) | 352056 | 73302 | 46596 | 211932 |
| `BumpCopyLower` | 342882 | 68634 | 43920 | 196974 |
| `LegLookup` (`pa <, =, > cr`) | 368052 | 124668 | 88548 | 422862 |
| `CleanNext` | 77388 | 25854 | 19722 | 80604 |
| `CleanLookup` | 77388 | 25854 | 19722 | 80604 |
| `CleanParent` (on the chain / via `(cr, C)`) | 77316 / 0 | 25782 / 0 | 19686 / 0 | 80136 / 24 |

Both consecutive hypotheses are needed: `LeftCopy` fails for a copy node whose lower
neighbour is a gap copy (40800 plain nodes of the standard samples), and "`m'` is on the
generation chain" alone fails on 24 random expansions, e.g. `(1,9,5,6,3,8,10,8)[1]`, where
`m = (6,1)` and `m' = (0,0)` is the next node of `(4,1)` (`cr = 4`).
-/

namespace OmegaY.Official.Classification.Proofs.ChainCorr.Inner

open Canonical Reserve Official Descent Classification Proofs

/-! ## Definitions -/

/-- The node above a node. -/
def up (r : Ref) : Ref := ⟨r.column, r.index + 1⟩

/-- The hypotheses of `StepInner`. -/
structure Setting (s : List Nat) (n D : Nat) (M : Mountain) (out : List Nat) (ρ : Root)
    (R : Mountain) (col : Column) (t : Cell) : Prop where
  splice : SpliceCase s n D M out ρ
  deg : DegreeOK s D
  run : Official.expandDiagram s n = .ok R
  canon : Canonical.build out = .ok R
  hcol : M[M.size - 1]? = some col
  ht : col.back? = some t

/-- `v` is the node of an inner column `y + w·i` of block `i` emitted with origin `o`. -/
def CopyAt (M R : Mountain) (n cr x0 : Nat) (τ : Row) (i : Nat) (v : Ref) (o : Origin) :
    Prop :=
  ∃ y es j, cr < y ∧ y < x0 ∧ y ∈ blockColumns cr x0 n i ∧ v.column = y + (x0 - cr) * i ∧
    v.index = j + 1 ∧ emitsT (ctxAt M R y i cr (x0 - cr) x0 v.column) τ = .ok es ∧
    ∃ hj : j < es.length, es[j].2 = o

/-- One step of the generation chain in the row of `a` (notes/03 §2.4, case 4): from a
node `a` right of `cr` to the node `b` of the leg column of `a` at the row of `a`. -/
def GenStep (M : Mountain) (cr : Nat) (a b : Ref) : Prop :=
  cr < a.column ∧ 1 ≤ b.index ∧ ∃ ca cb l, cell? M a = some ca ∧ ca.left = some l ∧
    b.column = l.column ∧ cell? M b = some cb ∧ cb.row = ca.row

/-! ## The five statements -/

/-- (open) Above a copy node with a plain or upper origin `m` lies a copy node of the node
above `m`. -/
def NextCopy : Prop :=
  ∀ s n D M out ρ R (col : Column) (t : Cell), Setting s n D M out ρ R col t →
    ∀ i, 0 < i → i < n + 1 → ∀ v m,
      (CopyAt M R n ρ.cr ρ.x0 (official t.row) i v (.plain m) ∨
        CopyAt M R n ρ.cr ρ.x0 (official t.row) i v (.upper m)) →
      (∃ c, cell? M (up m) = some c) →
      CopyNode M R n ρ.cr ρ.x0 (official t.row) i (up v) (up m)

/-- (open) For two consecutive copy pairs, the raw parents correspond. -/
def LeftCopy : Prop :=
  ∀ s n D M out ρ R (col : Column) (t : Cell), Setting s n D M out ρ R col t →
    ∀ i, 0 < i → i < n + 1 → ∀ v m,
      CopyNode M R n ρ.cr ρ.x0 (official t.row) i v m →
      CopyNode M R n ρ.cr ρ.x0 (official t.row) i (up v) (up m) →
      ∀ pa, rawParent M m = some pa →
      ∃ pe, rawParent R v = some pe ∧
        (pa.column < ρ.cr → pe = pa) ∧
        (pa.column = ρ.cr → pe.column = ρ.cr + (ρ.x0 - ρ.cr) * i ∧
          ∀ k m'', MStep M k m pa → MStep M k pa m'' → ScaleReach R k pe m'') ∧
        (ρ.cr < pa.column → CopyNode M R n ρ.cr ρ.x0 (official t.row) i pe pa)

/-- (open) For two consecutive copy pairs, the jump to the raw parent does not grow. -/
def JumpCopy : Prop :=
  ∀ s n D M out ρ R (col : Column) (t : Cell), Setting s n D M out ρ R col t →
    ∀ i, 0 < i → i < n + 1 → ∀ v m,
      CopyNode M R n ρ.cr ρ.x0 (official t.row) i v m →
      CopyNode M R n ρ.cr ρ.x0 (official t.row) i (up v) (up m) →
      ∀ pe pa (cv cm cpe cpa : Cell), rawParent R v = some pe → rawParent M m = some pa →
        cell? R v = some cv → cell? M m = some cm → cell? R pe = some cpe →
        cell? M pa = some cpa → Row.jump cv.row cpe.row ≤ Row.jump cm.row cpa.row

/-- (open) From a clean copy (`b = 0`) of `a`, one output step in the same row reaches the
clean copy of the next generation `b`, or, when `b` is in the root column, a node of the
boundary column whose chain follows the chain of `b`. -/
def CleanStep : Prop :=
  ∀ s n D M out ρ R (col : Column) (t : Cell), Setting s n D M out ρ R col t →
    ∀ i, 0 < i → i < n + 1 → ∀ v a,
      CopyAt M R n ρ.cr ρ.x0 (official t.row) i v (.clean a false) →
      ∃ v1 b, rawParent R v = some v1 ∧ GenStep M ρ.cr a b ∧ ρ.cr ≤ b.column ∧
        (∃ c1 c2 : Cell, cell? R v = some c1 ∧ cell? R v1 = some c2 ∧ c2.row = c1.row) ∧
        (ρ.cr < b.column → CopyAt M R n ρ.cr ρ.x0 (official t.row) i v1 (.clean b false)) ∧
        (b.column = ρ.cr → v1.column = ρ.cr + (ρ.x0 - ρ.cr) * i ∧
          ∀ k m'', MStep M k b m'' → ScaleReach R k v1 m'')

/-- (open) The step of `M(s)` from the source `a` of a clean copy lands on the generation
chain of `a`, or it is the step from the end `(cr, C)` of that chain. -/
def CleanParent : Prop :=
  ∀ s n D M out ρ R (col : Column) (t : Cell), Setting s n D M out ρ R col t →
    ∀ i, 0 < i → i < n + 1 → ∀ v a,
      CopyAt M R n ρ.cr ρ.x0 (official t.row) i v (.clean a false) →
      ∀ k m', MStep M k a m' →
        Relation.TransGen (GenStep M ρ.cr) a m' ∨
        ∃ g, Relation.TransGen (GenStep M ρ.cr) a g ∧ g.column = ρ.cr ∧ MStep M k g m'

/-! ## Mountain lemmas -/

theorem rawParent_eq_some {M : Mountain} {r p : Ref} :
    rawParent M r = some p ↔ ∃ c, cell? M (up r) = some c ∧ c.left = some p := by
  unfold rawParent cell? up
  cases h1 : M[r.column]? with
  | none => simp
  | some col =>
      simp only [Option.bind_eq_bind, Option.bind_some]
      cases h2 : col[r.index + 1]? with
      | none => simp
      | some c => simp

theorem cell_of_up {M : Mountain} {r : Ref} {c : Cell} (h : cell? M (up r) = some c) :
    ∃ c', cell? M r = some c' := by
  unfold cell? up at *
  cases h1 : M[r.column]? with
  | none => simp [h1] at h
  | some col =>
      simp only [h1, Option.bind_eq_bind, Option.bind_some] at h ⊢
      have hlt : r.index + 1 < col.size := by
        rcases Nat.lt_or_ge (r.index + 1) col.size with h' | h'
        · exact h'
        · simp [Array.getElem?_eq_none h'] at h
      exact ⟨col[r.index], Array.getElem?_eq_getElem (by omega)⟩

/-- The left end of a node of a valid mountain has a cell and lies left of the node. -/
theorem left_cell {M : Mountain} (hV : MountainValid M) {u : Ref} {cu : Cell} {l : Ref}
    (hu : cell? M u = some cu) (hl : cu.left = some l) :
    ∃ cl, cell? M l = some cl ∧ l.column < u.column := by
  unfold cell? at hu
  cases hcol : M[u.column]? with
  | none => simp [hcol] at hu
  | some col =>
      simp only [hcol, Option.bind_eq_bind, Option.bind_some] at hu
      have hc : u.column < M.size := by
        rcases Nat.lt_or_ge u.column M.size with h' | h'
        · exact h'
        · simp [Array.getElem?_eq_none h'] at hcol
      have hcolEq : M[u.column] = col := by
        have := hcol; rw [Array.getElem?_eq_getElem hc] at this; exact Option.some.inj this
      have hCV := hV u.column hc
      rw [hcolEq] at hCV
      obtain ⟨hlt, parent, hpar, _⟩ := hCV.stored_valid u.index cu l hu hl
      obtain ⟨column, h1, h2⟩ := cellAt_ok_iff.mp hpar
      exact ⟨parent, by simp [cell?, h1, h2], hlt⟩

/-- A raw parent of a node of a valid mountain: both cells exist and the parent is left. -/
theorem rawParent_cells {M : Mountain} (hV : MountainValid M) {r p : Ref}
    (h : rawParent M r = some p) :
    (∃ c, cell? M r = some c) ∧ (∃ cp, cell? M p = some cp) ∧ p.column < r.column := by
  obtain ⟨c, hc, hl⟩ := rawParent_eq_some.mp h
  obtain ⟨cp, hcp, hlt⟩ := left_cell hV hc hl
  exact ⟨cell_of_up hc, ⟨cp, hcp⟩, hlt⟩

/-- One raw-parent step with a small jump is a step of the scale-`k` chain. -/
theorem reach_one {M : Mountain} (hV : MountainValid M) {k : Nat} {r p : Ref} {c cp : Cell}
    (h : rawParent M r = some p) (hc : cell? M r = some c) (hcp : cell? M p = some cp)
    (hj : Row.jump c.row cp.row ≤ k) : ScaleReach M k r p :=
  ScaleReach.step h hc hcp hj (rawParent_cells hV h).2.2 (ScaleReach.refl p)

theorem cell?_eq_of_index {M : Mountain} (hV : MountainValid M) {a b : Ref} {ca cb : Cell}
    (hcol : a.column = b.column) (ha : cell? M a = some ca) (hb : cell? M b = some cb)
    (hrow : ca.row = cb.row) : a = b := by
  unfold cell? at ha hb
  rw [hcol] at ha
  cases hcM : M[b.column]? with
  | none => simp [hcM] at ha
  | some col =>
      simp only [hcM, Option.bind_eq_bind, Option.bind_some] at ha hb
      have hc : b.column < M.size := by
        rcases Nat.lt_or_ge b.column M.size with h' | h'
        · exact h'
        · simp [Array.getElem?_eq_none h'] at hcM
      have hcolEq : M[b.column] = col := by
        have := hcM; rw [Array.getElem?_eq_getElem hc] at this; exact Option.some.inj this
      have hCV := hV b.column hc
      rw [hcolEq] at hCV
      have hidx : a.index = b.index := by
        rcases Nat.lt_trichotomy a.index b.index with h' | h' | h'
        · have := hCV.rows_strict _ _ _ _ ha hb h'
          rw [hrow] at this
          exact absurd this (lt_irrefl _)
        · exact h'
        · have := hCV.rows_strict _ _ _ _ hb ha h'
          rw [hrow] at this
          exact absurd this (lt_irrefl _)
      cases a
      cases b
      simp_all

/-- The generation chain is deterministic. -/
theorem GenStep.unique {M : Mountain} (hV : MountainValid M) {cr : Nat} {a b b' : Ref}
    (h : GenStep M cr a b) (h' : GenStep M cr a b') : b = b' := by
  obtain ⟨_, _, ca, cb, l, hca, hl, hbc, hcb, hrow⟩ := h
  obtain ⟨_, _, ca', cb', l', hca', hl', hbc', hcb', hrow'⟩ := h'
  have hcc : ca = ca' := Option.some.inj (hca.symm.trans hca')
  subst hcc
  have hll : l = l' := Option.some.inj (hl.symm.trans hl')
  subst hll
  exact cell?_eq_of_index hV (by rw [hbc, hbc']) hcb hcb' (by rw [hrow, hrow'])

theorem transGen_head {α : Type} {r : α → α → Prop} {a b : α} (h : Relation.TransGen r a b) :
    ∃ c, r a c := by
  induction h with
  | single h => exact ⟨_, h⟩
  | tail _ _ ih => exact ih

/-! ## Copy nodes and their origins -/

theorem copyNode_of_copyAt {M R : Mountain} {n cr x0 : Nat} {τ : Row} {i : Nat} {v : Ref}
    {o : Origin} (h : CopyAt M R n cr x0 τ i v o) (hc : cutOrigin o = false) :
    CopyNode M R n cr x0 τ i v o.src := by
  obtain ⟨y, es, j, h1, h2, h3, h4, h5, h6, hj, ho⟩ := h
  exact ⟨y, es, j, h1, h2, h3, h4, h5, h6, hj, by rw [ho], Or.inl (by rw [ho]; exact hc)⟩

theorem copyAt_of_copyNode {M R : Mountain} {n cr x0 : Nat} {τ : Row} {i : Nat} {v m : Ref}
    (h : CopyNode M R n cr x0 τ i v m) :
    ∃ o, CopyAt M R n cr x0 τ i v o ∧ o.src = m ∧ (cutOrigin o = false ∨ rawParent M m = none) := by
  obtain ⟨y, es, j, h1, h2, h3, h4, h5, h6, hj, hsrc, hcut⟩ := h
  exact ⟨es[j].2, ⟨y, es, j, h1, h2, h3, h4, h5, h6, hj, rfl⟩, hsrc, hcut⟩

/-! ## The walk along the generation chain -/

/-- The end of a walk from a clean copy of `a` to `m'` along the generation chain. -/
def WalkEnd (M R : Mountain) (n cr x0 : Nat) (τ : Row) (i k : Nat) (m' v' : Ref) : Prop :=
  (cr < m'.column ∧ CopyAt M R n cr x0 τ i v' (.clean m' false)) ∨
  (m'.column = cr ∧ v'.column = cr + (x0 - cr) * i ∧
    ∀ m'', MStep M k m' m'' → ScaleReach R k v' m'')

theorem clean_walk (hstep : CleanStep) {s : List Nat} {n D : Nat} {M : Mountain}
    {out : List Nat} {ρ : Root} {R : Mountain} {col : Column} {t : Cell}
    (hS : Setting s n D M out ρ R col t) {i : Nat} (hi0 : 0 < i) (hi : i < n + 1) (k : Nat)
    {a m' : Ref} (hg : Relation.TransGen (GenStep M ρ.cr) a m') :
    ∀ va, CopyAt M R n ρ.cr ρ.x0 (official t.row) i va (.clean a false) →
      ∃ v', ScaleReach R k va v' ∧ WalkEnd M R n ρ.cr ρ.x0 (official t.row) i k m' v' := by
  have hVM := build_valid_of_success hS.splice.build
  have hVR := build_valid_of_success hS.canon
  -- one step of the walk
  have one : ∀ a b va, GenStep M ρ.cr a b →
      CopyAt M R n ρ.cr ρ.x0 (official t.row) i va (.clean a false) →
      ∃ v1, ScaleReach R k va v1 ∧ ρ.cr ≤ b.column ∧
        (ρ.cr < b.column → CopyAt M R n ρ.cr ρ.x0 (official t.row) i v1 (.clean b false)) ∧
        (b.column = ρ.cr → v1.column = ρ.cr + (ρ.x0 - ρ.cr) * i ∧
          ∀ m'', MStep M k b m'' → ScaleReach R k v1 m'') := by
    intro a b va hab hva
    obtain ⟨v1, b', hpar, hab', hcrb, ⟨c1, c2, hc1, hc2, hrow⟩, hin, hroot⟩ :=
      hstep s n D M out ρ R col t hS i hi0 hi va a hva
    have hbb := GenStep.unique hVM hab' hab
    subst hbb
    refine ⟨v1, reach_one hVR hpar hc1 hc2 (by rw [hrow, Row.jump_self]; exact Nat.zero_le _),
      hcrb, hin, fun h => ⟨(hroot h).1, (hroot h).2 k⟩⟩
  induction hg using Relation.TransGen.head_induction_on with
  | single hab =>
      intro va hva
      obtain ⟨v1, hr, hcrb, hin, hroot⟩ := one _ _ va hab hva
      refine ⟨v1, hr, ?_⟩
      rcases Nat.lt_or_eq_of_le hcrb with hlt | heq
      · exact Or.inl ⟨hlt, hin hlt⟩
      · exact Or.inr ⟨heq.symm, hroot heq.symm⟩
  | head hac hcb ih =>
      intro va hva
      obtain ⟨_, hnext⟩ := transGen_head hcb
      obtain ⟨v1, hr, _, hin, _⟩ := one _ _ va hac hva
      obtain ⟨v', hr', hend⟩ := ih v1 (hin hnext.1)
      exact ⟨v', ScaleReach.trans hr hr', hend⟩

/-! ## The reduction -/

/-- **`StepInner` from the five local statements.** -/
theorem stepInner_of_parts (hNext : NextCopy) (hLeft : LeftCopy) (hJump : JumpCopy)
    (hClean : CleanStep) (hCP : CleanParent) : StepInner := by
  intro s n D M out ρ R col t hc hdeg hRun hRb hcol ht i hi0 hi v m hvm k m' hst
  have hS : Setting s n D M out ρ R col t := ⟨hc, hdeg, hRun, hRb, hcol, ht⟩
  have hVM := build_valid_of_success hc.build
  have hVR := build_valid_of_success hRb
  obtain ⟨o, hvo, hsrc, hcut⟩ := copyAt_of_copyNode hvm
  obtain ⟨hpar, cm, cm', hcm, hcm', hj, hlt⟩ := hst
  have hst : MStep M k m m' := ⟨hpar, cm, cm', hcm, hcm', hj, hlt⟩
  -- the plain and upper origins: one step
  have plain : (CopyAt M R n ρ.cr ρ.x0 (official t.row) i v (.plain m) ∨
      CopyAt M R n ρ.cr ρ.x0 (official t.row) i v (.upper m)) →
      Next R M k ρ.cr ((ρ.x0 - ρ.cr) * i) (CopyNode M R n ρ.cr ρ.x0 (official t.row) i) v m' := by
    intro hpu
    obtain ⟨cu, hcu, _⟩ := rawParent_eq_some.mp hpar
    have hup := hNext s n D M out ρ R col t hS i hi0 hi v m hpu ⟨cu, hcu⟩
    obtain ⟨pe, hpe, hlow, hroot, hcopy⟩ :=
      hLeft s n D M out ρ R col t hS i hi0 hi v m hvm hup m' hpar
    obtain ⟨⟨cv, hcv⟩, ⟨cpe, hcpe⟩, _⟩ := rawParent_cells hVR hpe
    have hjump := hJump s n D M out ρ R col t hS i hi0 hi v m hvm hup pe m' cv cm cpe cm'
      hpe hpar hcv hcm hcpe hcm'
    have hr : ScaleReach R k v pe := reach_one hVR hpe hcv hcpe (le_trans hjump hj)
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    · rw [← hlow h]; exact hr
    · obtain ⟨hpc, hnext⟩ := hroot h
      exact ⟨pe, hr, le_of_eq hpc, fun m'' h'' => hnext k m'' hst h''⟩
    · exact ⟨pe, hr, hcopy h⟩
  cases o with
  | plain r =>
      simp only [Origin.src] at hsrc
      subst hsrc
      exact plain (Or.inl hvo)
  | upper r =>
      simp only [Origin.src] at hsrc
      subst hsrc
      exact plain (Or.inr hvo)
  | clean r cut =>
      simp only [Origin.src] at hsrc
      subst hsrc
      cases cut with
      | true =>
          rcases hcut with h | h
          · simp [cutOrigin] at h
          · rw [h] at hpar; cases hpar
      | false =>
          rcases hCP s n D M out ρ R col t hS i hi0 hi v r hvo k m' hst with hg | ⟨g, hg, hgc, hgst⟩
          · obtain ⟨v', hr, hend⟩ := clean_walk hClean hS hi0 hi k hg v hvo
            rcases hend with ⟨hlt', hcp⟩ | ⟨heq, hvc, hnext⟩
            · refine ⟨fun h => absurd h (by omega), fun h => absurd h (by omega), fun _ => ?_⟩
              exact ⟨v', hr, copyNode_of_copyAt hcp rfl⟩
            · refine ⟨fun h => absurd h (by omega), fun _ => ?_, fun h => absurd h (by omega)⟩
              exact ⟨v', hr, le_of_eq hvc, hnext⟩
          · obtain ⟨v', hr, hend⟩ := clean_walk hClean hS hi0 hi k hg v hvo
            have hm'lt : m'.column < ρ.cr := hgc ▸ hgst.column_lt
            rcases hend with ⟨hlt', _⟩ | ⟨_, _, hnext⟩
            · omega
            · refine ⟨fun _ => ScaleReach.trans hr (hnext m' hgst), fun h => absurd h (by omega),
                fun h => absurd h (by omega)⟩

/-- **Five region lemmas** from the local statements of `StepInner` and the four start
statements. -/
theorem wellFounded_of_local (hrec : Dimension.BlockReconstruction) (hNext : NextCopy)
    (hLeft : LeftCopy) (hJump : JumpCopy) (hClean : CleanStep) (hCP : CleanParent)
    (hLeg : StartLeg) (hJ : StartJump) (hCopy : StartCopy) (hRoot : StartRoot)
    (hKB : RegionCutBoundary) (hKI : RegionCutInner) : WellFounded Step :=
  wellFounded_of_chains hrec (stepInner_of_parts hNext hLeft hJump hClean hCP) hLeg hJ hCopy
    hRoot hKB hKI

/-! # Part 2: local pieces (upper origins, the row law) -/

/-! ## Columns of the output -/

theorem block_unique {cr x0 n i i' y x' : Nat} (hcr : cr < x0) (hy : cr < y) (hyx : y < x0)
    (hx' : x' ∈ blockColumns cr x0 n i') (heq : y + (x0 - cr) * i = x' + (x0 - cr) * i')
    (hi : 0 < i) : i' = i ∧ x' = y := by
  have hw : 0 < x0 - cr := by omega
  have hwi : x0 - cr ≤ (x0 - cr) * i := Nat.le_mul_of_pos_right _ hi
  rcases Nat.eq_zero_or_pos i' with h0 | hpos
  · subst h0
    simp [blockColumns] at hx'
    omega
  · obtain ⟨hcx, hxx⟩ := mem_blockColumns_pos hx' hpos
    rcases Nat.lt_trichotomy i i' with hlt | heq' | hlt
    · have : (x0 - cr) * i + (x0 - cr) ≤ (x0 - cr) * i' := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hlt
      omega
    · subst heq'
      exact ⟨rfl, by omega⟩
    · have : (x0 - cr) * i' + (x0 - cr) ≤ (x0 - cr) * i := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hlt
      omega

/-- The cell of an output node with a traced origin: its row is the stored emitted row and
its left end is in the emitted leg column. -/
theorem copyAt_cell {s : List Nat} {n D : Nat} {M : Mountain} {out : List Nat} {ρ : Root}
    {R : Mountain} {col : Column} {t : Cell} (hS : Setting s n D M out ρ R col t) {i : Nat}
    (hi0 : 0 < i) (hi : i < n + 1) {v : Ref} {o : Origin}
    (h : CopyAt M R n ρ.cr ρ.x0 (official t.row) i v o) :
    ∃ y es j, ∃ hj : j < es.length, es[j].2 = o ∧
      (v.column = y + (ρ.x0 - ρ.cr) * i ∧ ρ.cr < y ∧ y < ρ.x0 ∧ v.column < R.size) ∧
      v.index = j + 1 ∧
      emitsT (ctxAt M R y i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 v.column) (official t.row) = .ok es ∧
      ∃ cv, cell? R v = some cv ∧ cv.row = stored es[j].1.row ∧ ∃ ref : Ref, cv.left = some ref ∧
        ref.column = legColumn (ctxAt M R y i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 v.column) es[j].1 := by
  obtain ⟨y, es, j, hcy, hyx, hyb, hvc, hvi, hes, hj, ho⟩ := h
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
  have hXR : v.column < R.size := by omega
  have hX0 : ρ.x0 ≤ v.column := by omega
  obtain ⟨i', x', _, hx', hXeq, hcopy⟩ := hinv.2.2 v.column hXR hX0
  obtain ⟨hii, hxx⟩ := block_unique hcrx hcy hyx hx' (hvc.symm.trans hXeq) hi0
  subst hii
  subst hxx
  obtain ⟨es', hes', hasm⟩ := copyColumn_emitsT hcopy
  have hee : es' = es := Except.ok.inj (hes'.symm.trans hes)
  subst hee
  obtain ⟨_, hcells⟩ := assemble_spec hasm
  obtain ⟨cell, hcellX, hrow, ref, hrefl, hrefc⟩ := hcells j (by simpa using hj)
  simp only [List.getElem_map] at hrow hrefc
  refine ⟨x', es', j, hj, ho, ⟨hvc, hcy, hyx, hXR⟩, hvi, hes, cell, ?_, hrow, ref, hrefl, hrefc⟩
  simp only [cell?, Array.getElem?_eq_getElem hXR, Option.bind_eq_bind, Option.bind_some, hvi]
  exact hcellX

/-! ## The row law of a canonical mountain -/

/-- **Row law.** In a canonical mountain, the row of the node above a real node `r` is
`B(row r, row p)` for the left end `p` of that node. -/
theorem canon_rowLaw {s : List Nat} {M : Mountain} (hB : build s = .ok M) {r p : Ref}
    {c cu cp : Cell} (hr0 : 0 < r.index) (hr : cell? M r = some c)
    (hu : cell? M (up r) = some cu) (hl : cu.left = some p) (hp : cell? M p = some cp) :
    cu.row = Row.B c.row cp.row := by
  have hN := build_normal_of_success hB
  obtain ⟨hc, hvi, hvc⟩ := canon_cell?_some_iff.mp hu
  obtain ⟨hc', hri, hrc⟩ := canon_cell?_some_iff.mp hr
  let nu := canonNodeOf (M := M) r hc' hri
  let nv := canonNodeOf (M := M) (up r) hc hvi
  have hup : (Geometry.Frame.ofMountain M).upper nu = some nv :=
    ControlProof.upper_eq_of_index rfl rfl
  obtain ⟨q, _, hrow, _, hleft⟩ := hN.upper_step nu nv (show Geometry.Frame.Real nu from hr0) hup
  have hcv : (Geometry.Frame.ofMountain M).cell nv = cu := hvc
  have hcu : (Geometry.Frame.ofMountain M).cell nu = c := hrc
  rw [hcv, hl] at hleft
  have hq : p = Geometry.Frame.ref q := Option.some.inj hleft
  have hcq := ControlProof.cell?_ref q
  rw [← hq, hp] at hcq
  have hcq' : (Geometry.Frame.ofMountain M).cell q = cp := (Option.some.inj hcq).symm
  have e1 : (Geometry.Frame.ofMountain M).height nv = cu.row := by
    simp only [Geometry.Frame.height, hcv]
  have e2 : (Geometry.Frame.ofMountain M).height nu = c.row := by
    simp only [Geometry.Frame.height, hcu]
  have e3 : (Geometry.Frame.ofMountain M).height q = cp.row := by
    simp only [Geometry.Frame.height, hcq']
  rw [← e1, ← e2, ← e3]
  exact hrow

theorem jump_up_of_rowLaw {s : List Nat} {M : Mountain} (hB : build s = .ok M) {r p : Ref}
    {c cu cp : Cell} (hr0 : 0 < r.index) (hr : cell? M r = some c)
    (hu : cell? M (up r) = some cu) (hl : cu.left = some p) (hp : cell? M p = some cp) :
    Row.jump c.row cu.row = Row.jump c.row cp.row + 1 := by
  rw [canon_rowLaw hB hr0 hr hu hl hp, Row.B, Row.jump_bump]

/-! ## `JumpCopy` from the rows of one column -/

/-- (open) For two consecutive copy pairs, the step `v → v⁺` of the output column jumps at
most as high as the step `m → m⁺` of the source column. -/
def BumpCopy : Prop :=
  ∀ s n D M out ρ R (col : Column) (t : Cell), Setting s n D M out ρ R col t →
    ∀ i, 0 < i → i < n + 1 → ∀ v m,
      CopyNode M R n ρ.cr ρ.x0 (official t.row) i v m →
      CopyNode M R n ρ.cr ρ.x0 (official t.row) i (up v) (up m) →
      ∀ cv cv' cm cm' : Cell, cell? R v = some cv → cell? R (up v) = some cv' →
        cell? M m = some cm → cell? M (up m) = some cm' →
        Row.jump cv.row cv'.row ≤ Row.jump cm.row cm'.row

theorem copyNode_index_pos {M R : Mountain} {n cr x0 : Nat} {τ : Row} {i : Nat} {v m : Ref}
    (h : CopyNode M R n cr x0 τ i v m) : 0 < v.index ∧ 0 < m.index := by
  obtain ⟨y, es, j, _, _, _, _, hvi, hes, hj, hsrc, _⟩ := h
  obtain ⟨_, hidx, _⟩ := emitsT_good hes es[j] (List.getElem_mem hj)
  rw [hsrc] at hidx
  omega

/-- **`JumpCopy` from `BumpCopy`** (both mountains are canonical). -/
theorem jumpCopy_of_bumpCopy (h : BumpCopy) : JumpCopy := by
  intro s n D M out ρ R col t hS i hi0 hi v m hvm hup pe pa cv cm cpe cpa hpe hpa hcv hcm hcpe
    hcpa
  obtain ⟨cv', hcv', hlv⟩ := rawParent_eq_some.mp hpe
  obtain ⟨cm', hcm', hlm⟩ := rawParent_eq_some.mp hpa
  obtain ⟨hv0, hm0⟩ := copyNode_index_pos hvm
  have h1 := jump_up_of_rowLaw hS.canon hv0 hcv hcv' hlv hcpe
  have h2 := jump_up_of_rowLaw hS.splice.build hm0 hcm hcm' hlm hcpa
  have h3 := h s n D M out ρ R col t hS i hi0 hi v m hvm hup cv cv' cm cm' hcv hcv' hcm hcm'
  omega

/-! ## The upper part lists the source nodes in order -/

theorem filter_cons_cons {α : Type} (P : α → Bool) (A B : List α) (a b : α) (ha : P a = true)
    (hb : P b = true) :
    (A ++ a :: b :: B).filter P = A.filter P ++ a :: b :: B.filter P := by
  simp [List.filter_append, ha, hb]

theorem mid_getElem {α : Type} {L F G : List α} {a b : α} (h : L = F ++ a :: b :: G) :
    ∃ (h1 : F.length < L.length) (h2 : F.length + 1 < L.length),
      L[F.length] = a ∧ L[F.length + 1] = b := by
  subst h
  exact ⟨by simp, by simp, by simp, by simp⟩

/-- In the upper part, the node after the upper copy of `m` is the upper copy of `m⁺`. -/
theorem upperT_next {ctx : Context} {τ : Row} {us : List (Emit × Origin)}
    (hV : MountainValid ctx.source) (h : upperT ctx τ = .ok us) {q : Nat} (hq : q < us.length)
    {m : Ref} (hm : us[q].2 = .upper m) {c' : Cell} (hc' : cell? ctx.source (up m) = some c') :
    ∃ hq' : q + 1 < us.length, us[q + 1].2 = .upper (up m) := by
  unfold upperT at h
  generalize hN : realNodes ctx.source (upperColumn ctx) = N at h
  generalize hP : (fun p : Ref × Cell => decide (τ ≤ official p.2.row)) = P at h
  obtain ⟨hlen, hall⟩ := mapM_except_spec _ _ _ h
  -- the r-th output is the upper copy of the r-th filtered node
  have hfq : ∀ r (hr : r < (N.filter P).length) (hr' : r < us.length),
      us[r].2 = .upper (N.filter P)[r].1 := by
    intro r hr hr'
    have := hall r hr hr'
    simp only [bind, Except.bind, pure, Except.pure] at this
    split at this
    · cases this
    · rw [← Except.ok.inj this]
  have hq1 : q < (N.filter P).length := by omega
  have hmq : (N.filter P)[q].1 = m := by
    have := hfq q hq1 hq
    rw [hm] at this
    exact (Origin.upper.inj this).symm
  -- m and m⁺ are consecutive real nodes of the column
  have hmem : (N.filter P)[q] ∈ N := List.mem_of_mem_filter (List.getElem_mem hq1)
  have hPm : P (N.filter P)[q] = true := (List.mem_filter.mp (List.getElem_mem hq1)).2
  have hmem' : (N.filter P)[q] ∈ realNodes ctx.source (upperColumn ctx) := by
    rw [hN]; exact hmem
  obtain ⟨colm, k, hcolm, hcellk, hk⟩ := Recon.mem_realNodes_iff.mp hmem'
  rw [hmq] at hk
  have hsz : upperColumn ctx < ctx.source.size := by
    rcases Nat.lt_or_ge (upperColumn ctx) ctx.source.size with h' | h'
    · exact h'
    · simp [Array.getElem?_eq_none h'] at hcolm
  have hcolEq : ctx.source[upperColumn ctx] = colm := by
    have := hcolm; rw [Array.getElem?_eq_getElem hsz] at this; exact Option.some.inj this
  have hup : colm[k + 2]? = some c' := by
    have := hc'
    simp only [cell?, up, hk, Option.bind_eq_bind] at this
    rw [hcolm] at this
    simpa using this
  have hNk? := Recon.realNodes_getElem? ctx.source (upperColumn ctx) k
  have hNk1? := Recon.realNodes_getElem? ctx.source (upperColumn ctx) (k + 1)
  rw [hcolm, hN] at hNk? hNk1?
  simp only [Option.bind_some, hcellk, Option.map_some] at hNk?
  simp only [Option.bind_some, hup, Option.map_some] at hNk1?
  obtain ⟨hk1, hNk⟩ := List.getElem?_eq_some_iff.mp hNk?
  obtain ⟨hk2, hNk1⟩ := List.getElem?_eq_some_iff.mp hNk1?
  have hNkm : N[k].1 = m := by rw [hNk, hk]
  have hNk1m : N[k + 1].1 = up m := by rw [hNk1, hk]; rfl
  -- the node above has a larger row, so it passes the filter
  have hCV := hV (upperColumn ctx) hsz
  rw [hcolEq] at hCV
  have hPk : P N[k] = true := by
    have : N[k] = (N.filter P)[q] := by
      rw [hNk]; exact Prod.ext (by rw [hmq, hk]) rfl
    rw [this]; exact hPm
  have hPk1 : P N[k + 1] = true := by
    rw [← hP] at hPk ⊢
    simp only [decide_eq_true_eq] at hPk ⊢
    rw [hNk] at hPk
    rw [hNk1]
    have hlt : (N.filter P)[q].2.row < c'.row :=
      hCV.rows_strict (k + 1) (k + 2) _ _ hcellk hup (by omega)
    have hcellm : cell? ctx.source ⟨upperColumn ctx, k + 1⟩ = some (N.filter P)[q].2 := by
      simp [cell?, hcolm, hcellk]
    have h1 : (1 : Row) ≤ (N.filter P)[q].2.row := one_le_row hV hcellm (by simp)
    exact le_trans hPk (Recon.official_mono h1 hlt.le)
  -- split the list at m
  have hsplit : N = N.take k ++ N[k] :: N[k + 1] :: N.drop (k + 2) := by
    conv_lhs => rw [← List.take_append_drop k N]
    congr 1
    rw [List.drop_eq_getElem_cons hk1, List.drop_eq_getElem_cons (by omega)]
  have hfil : N.filter P = (N.take k).filter P ++ N[k] :: N[k + 1] :: (N.drop (k + 2)).filter P := by
    conv_lhs => rw [hsplit]
    exact filter_cons_cons P _ _ _ _ hPk hPk1
  obtain ⟨hFl, hFl1, hFm, hFm1⟩ := mid_getElem hfil
  generalize ((N.take k).filter P).length = f at hFl hFl1 hFm hFm1
  -- the position of m in the filtered list is `f`
  have hpw : (N.filter P).Pairwise (fun p q => p.1.index < q.1.index) := by
    rw [← hN]
    exact List.Pairwise.filter _ (Recon.realNodes_pairwise ctx.source (upperColumn ctx))
  have hqF : q = f := by
    rcases Nat.lt_trichotomy q f with hlt | heq | hlt
    · have := List.pairwise_iff_getElem.mp hpw q f hq1 hFl hlt
      rw [hmq, hFm, hNkm] at this; omega
    · exact heq
    · have := List.pairwise_iff_getElem.mp hpw f q hFl hq1 hlt
      rw [hmq, hFm, hNkm] at this; omega
  subst hqF
  have hq' : q + 1 < us.length := by omega
  refine ⟨hq', ?_⟩
  rw [hfq (q + 1) hFl1 hq', hFm1, hNk1m]

/-- In a column, the emitted node after the upper copy of `m` is the upper copy of `m⁺`. -/
theorem emitsT_upper_next {ctx : Context} {τ : Row} {es : List (Emit × Origin)}
    (hV : MountainValid ctx.source) (h : emitsT ctx τ = .ok es) {j : Nat} (hj : j < es.length)
    {m : Ref} (hm : es[j].2 = .upper m) {c' : Cell} (hc' : cell? ctx.source (up m) = some c') :
    ∃ hj' : j + 1 < es.length, es[j + 1].2 = .upper (up m) := by
  unfold emitsT at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i lower hlower
    split at h
    · cases h
    · rename_i us hus
      cases h
      -- the lower part has no upper origin
      have hnot : ∀ p ∈ lower, p.2.isUpper = false := by
        intro p hp
        unfold lowerT at hlower
        simp only [bind, Except.bind, pure, Except.pure] at hlower
        split at hlower
        · cases hlower
        · rename_i outs houts
          cases hlower
          obtain ⟨out, hout, hpo⟩ := List.mem_flatten.mp hp
          obtain ⟨c, _, hc⟩ := mem_of_mapM houts hout
          exact runItemT_not_upper ctx c.1 c.2 out hc p hpo
      have hjL : lower.length ≤ j := by
        by_contra hlt
        push Not at hlt
        have := hnot lower[j] (List.getElem_mem hlt)
        rw [List.getElem_append_left hlt] at hm
        rw [hm] at this
        simp [Origin.isUpper] at this
      have hq : j - lower.length < us.length := by simp at hj; omega
      have hm' : us[j - lower.length].2 = .upper m := by
        rw [List.getElem_append_right hjL] at hm
        exact hm
      obtain ⟨hq', hnext⟩ := upperT_next hV hus hq hm' hc'
      refine ⟨by simp; omega, ?_⟩
      rw [List.getElem_append_right (by omega)]
      have : j + 1 - lower.length = j - lower.length + 1 := by omega
      simp only [this]
      exact hnext

/-! ## `NextCopy` for upper origins -/

/-- (open) `NextCopy` for plain origins. -/
def NextCopyPlain : Prop :=
  ∀ s n D M out ρ R (col : Column) (t : Cell), Setting s n D M out ρ R col t →
    ∀ i, 0 < i → i < n + 1 → ∀ v m,
      CopyAt M R n ρ.cr ρ.x0 (official t.row) i v (.plain m) →
      (∃ c, cell? M (up m) = some c) →
      CopyNode M R n ρ.cr ρ.x0 (official t.row) i (up v) (up m)

/-- **`NextCopy` for upper origins.** -/
theorem nextCopy_upper {s : List Nat} {n D : Nat} {M : Mountain} {out : List Nat} {ρ : Root}
    {R : Mountain} {col : Column} {t : Cell} (hS : Setting s n D M out ρ R col t) {i : Nat}
    {v m : Ref} (h : CopyAt M R n ρ.cr ρ.x0 (official t.row) i v (.upper m)) {c : Cell}
    (hc : cell? M (up m) = some c) :
    CopyNode M R n ρ.cr ρ.x0 (official t.row) i (up v) (up m) := by
  obtain ⟨y, es, j, hcy, hyx, hyb, hvc, hvi, hes, hj, ho⟩ := h
  have hV := build_valid_of_success hS.splice.build
  obtain ⟨hj', hnext⟩ := emitsT_upper_next (ctx := ctxAt M R y i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 v.column)
    hV hes hj ho hc
  refine ⟨y, es, j + 1, hcy, hyx, hyb, hvc, by simp [up, hvi], hes, hj', ?_, Or.inl ?_⟩
  · rw [hnext]; rfl
  · rw [hnext]; rfl

/-- **`NextCopy` from its plain case.** -/
theorem nextCopy_of_plain (h : NextCopyPlain) : NextCopy := by
  intro s n D M out ρ R col t hS i hi0 hi v m hpu hc
  rcases hpu with hp | hu
  · exact h s n D M out ρ R col t hS i hi0 hi v m hp hc
  · obtain ⟨c, hc⟩ := hc
    exact nextCopy_upper hS hu hc

/-! ## `BumpCopy` for two upper origins -/

/-- (open) `BumpCopy` for pairs where one of the two origins is in the lower part. -/
def BumpCopyLower : Prop :=
  ∀ s n D M out ρ R (col : Column) (t : Cell), Setting s n D M out ρ R col t →
    ∀ i, 0 < i → i < n + 1 → ∀ v m,
      CopyNode M R n ρ.cr ρ.x0 (official t.row) i v m →
      CopyNode M R n ρ.cr ρ.x0 (official t.row) i (up v) (up m) →
      ¬ (CopyAt M R n ρ.cr ρ.x0 (official t.row) i v (.upper m) ∧
        CopyAt M R n ρ.cr ρ.x0 (official t.row) i (up v) (.upper (up m))) →
      ∀ cv cv' cm cm' : Cell, cell? R v = some cv → cell? R (up v) = some cv' →
        cell? M m = some cm → cell? M (up m) = some cm' →
        Row.jump cv.row cv'.row ≤ Row.jump cm.row cm'.row

/-- An upper copy has the row of its origin. -/
theorem upper_row {s : List Nat} {n D : Nat} {M : Mountain} {out : List Nat} {ρ : Root}
    {R : Mountain} {col : Column} {t : Cell} (hS : Setting s n D M out ρ R col t) {i : Nat}
    (hi0 : 0 < i) (hi : i < n + 1) {v m : Ref}
    (h : CopyAt M R n ρ.cr ρ.x0 (official t.row) i v (.upper m)) {cv cm : Cell}
    (hcv : cell? R v = some cv) (hcm : cell? M m = some cm) : cv.row = cm.row := by
  have hV := build_valid_of_success hS.splice.build
  obtain ⟨y, es, j, hj, ho, _, _, hes, cv', hcv', hrow, _⟩ := copyAt_cell hS hi0 hi h
  rw [hcv] at hcv'
  cases hcv'
  obtain ⟨cu, hcu, hrowu⟩ := emitsT_upper_row hes es[j] (List.getElem_mem hj) (by rw [ho]; rfl)
  simp only [ho, Origin.src, ctxAt] at hcu
  rw [hcm] at hcu
  cases hcu
  obtain ⟨_, hidx, _⟩ := emitsT_good hes es[j] (List.getElem_mem hj)
  simp only [ho, Origin.src] at hidx
  rw [hrow, hrowu, stored_official (one_le_row hV hcm hidx)]

/-- **`BumpCopy` from its lower case.** -/
theorem bumpCopy_of_lower (h : BumpCopyLower) : BumpCopy := by
  intro s n D M out ρ R col t hS i hi0 hi v m hvm hup cv cv' cm cm' hcv hcv' hcm hcm'
  by_cases hboth : CopyAt M R n ρ.cr ρ.x0 (official t.row) i v (.upper m) ∧
      CopyAt M R n ρ.cr ρ.x0 (official t.row) i (up v) (.upper (up m))
  · rw [upper_row hS hi0 hi hboth.1 hcv hcm, upper_row hS hi0 hi hboth.2 hcv' hcm']
  · exact h s n D M out ρ R col t hS i hi0 hi v m hvm hup hboth cv cv' cm cm' hcv hcv' hcm hcm'

/-- **`StepInner` from the remaining local statements.** -/
theorem stepInner_of_local (hNext : NextCopyPlain) (hLeft : LeftCopy) (hBump : BumpCopyLower)
    (hClean : CleanStep) (hCP : CleanParent) : StepInner :=
  stepInner_of_parts (nextCopy_of_plain hNext) hLeft
    (jumpCopy_of_bumpCopy (bumpCopy_of_lower hBump)) hClean hCP

/-! # Part 3: raw parents of a canonical mountain as lookups -/

theorem highestAtMost_of_max {M : Mountain} {l : Nat} {row : Row} {p : Ref} {cp : Cell}
    (hpc : p.column = l) (hp0 : 0 < p.index) (hcp : cell? M p = some cp) (hle : cp.row ≤ row)
    (hmax : ∀ j c, cell? M ⟨l, j⟩ = some c → 0 < j → c.row ≤ row → j ≤ p.index) :
    highestAtMost M l row = some p := by
  subst hpc
  unfold cell? at hcp
  cases hcol : M[p.column]? with
  | none => simp [hcol] at hcp
  | some col =>
    simp only [hcol, Option.bind_eq_bind, Option.bind_some] at hcp
    have hpi : p.index < col.size := by
      rcases Nat.lt_or_ge p.index col.size with h' | h'
      · exact h'
      · simp [Array.getElem?_eq_none h'] at hcp
    unfold highestAtMost
    simp only [hcol, Option.bind_eq_bind, Option.bind_some]
    have hPp : (0 < p.index && (match col[p.index]? with
        | some c => decide (c.row ≤ row) | none => false)) = true := by
      simp [hcp, hp0, hle]
    cases hL : ((List.range col.size).filter fun j => 0 < j && (match col[j]? with
        | some c => decide (c.row ≤ row) | none => false)).getLast? with
    | none =>
        exfalso
        rw [List.getLast?_eq_none_iff] at hL
        have hmem : p.index ∈ (List.range col.size).filter fun j => 0 < j && (match col[j]? with
            | some c => decide (c.row ≤ row) | none => false) :=
          List.mem_filter.mpr ⟨List.mem_range.mpr hpi, hPp⟩
        rw [hL] at hmem
        cases hmem
    | some j =>
        obtain ⟨hjn, hPj, hmaxj⟩ := ControlProof.getLast?_filter_range hL
        have h1 := hmaxj p.index hpi hPp
        have hj0 : 0 < j := by
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hPj
          exact hPj.1
        have hcj : col[j]? = some col[j] := Array.getElem?_eq_getElem hjn
        have hrj : col[j].row ≤ row := by
          simp only [hcj, Bool.and_eq_true, decide_eq_true_eq] at hPj
          exact hPj.2
        have h2 := hmax j col[j] (by simp [cell?, hcol, hcj]) hj0 hrj
        have hjp : j = p.index := by omega
        subst hjp
        erw [hL]
        rfl

/-- In a canonical mountain the raw parent of a real node is not above it. -/
theorem canon_parent_le {s : List Nat} {M : Mountain} (hB : build s = .ok M) {v pe : Ref}
    {cv cpe : Cell} (hv0 : 0 < v.index) (hcv : cell? M v = some cv)
    (hpe : rawParent M v = some pe) (hcpe : cell? M pe = some cpe) : cpe.row ≤ cv.row := by
  have hN := build_normal_of_success hB
  obtain ⟨cu, hcu, hl⟩ := rawParent_eq_some.mp hpe
  obtain ⟨hc, hvi, hvc⟩ := canon_cell?_some_iff.mp hcu
  obtain ⟨hc', hri, hrc⟩ := canon_cell?_some_iff.mp hcv
  let nu := canonNodeOf (M := M) v hc' hri
  let nv := canonNodeOf (M := M) (up v) hc hvi
  have hup : (Geometry.Frame.ofMountain M).upper nu = some nv :=
    ControlProof.upper_eq_of_index rfl rfl
  obtain ⟨q, hP, _, _, hleft⟩ := hN.upper_step nu nv (show Geometry.Frame.Real nu from hv0) hup
  have hcvv : (Geometry.Frame.ofMountain M).cell nv = cu := hvc
  have hcu' : (Geometry.Frame.ofMountain M).cell nu = cv := hrc
  rw [hcvv, hl] at hleft
  have hq : pe = Geometry.Frame.ref q := Option.some.inj hleft
  have hcq := ControlProof.cell?_ref q
  rw [← hq, hcpe] at hcq
  have hcq' : (Geometry.Frame.ofMountain M).cell q = cpe := (Option.some.inj hcq).symm
  have hle := Geometry.Frame.P_height_le hN.toOrdered hP
  simp only [Geometry.Frame.height, hcq', hcu'] at hle
  exact hle

/-- **The raw parent of a real node of a canonical mountain is the highest node of its
column at or below the row of the node.** -/
theorem canon_rawParent_hAM {s : List Nat} {M : Mountain} (hB : build s = .ok M) {v pe : Ref}
    {cv : Cell} (hv0 : 0 < v.index) (hcv : cell? M v = some cv)
    (hpe : rawParent M v = some pe) : highestAtMost M pe.column cv.row = some pe := by
  have hV := build_valid_of_success hB
  have hLeg := build_success_legal hB
  obtain ⟨cu, hcu, hl⟩ := rawParent_eq_some.mp hpe
  obtain ⟨cpe, hcpe, hlt, hmax⟩ :=
    canonical_rawParent_highest_below hLeg hB (u := v) (cv := cu) hcu hpe
  have hle := canon_parent_le hB hv0 hcv hpe hcpe
  -- rows of the column of `v`
  have hvu : cv.row < cu.row := by
    unfold cell? at hcv hcu
    cases hcol : M[v.column]? with
    | none => simp [hcol] at hcv
    | some col =>
        simp only [up, hcol, Option.bind_eq_bind, Option.bind_some] at hcv hcu
        have hc : v.column < M.size := by
          rcases Nat.lt_or_ge v.column M.size with h' | h'
          · exact h'
          · simp [Array.getElem?_eq_none h'] at hcol
        have hCV := hV v.column hc
        rw [show M[v.column] = col from by
          have := hcol; rw [Array.getElem?_eq_getElem hc] at this; exact Option.some.inj this]
          at hCV
        exact hCV.rows_strict v.index (v.index + 1) cv cu hcv hcu (by omega)
  -- the parent is a real node: the bottom node of its column is below `row v⁺`
  have hpe0 : 0 < pe.index := by
    by_contra h0
    have h0' : pe.index = 0 := by omega
    obtain ⟨colp, hcolp, _⟩ := cell?_spec hcpe
    obtain ⟨hcp, hcolEq⟩ := column_of_getElem? hcolp
    have hCV := hV pe.column hcp
    rw [hcolEq] at hCV
    have hsz : 1 < colp.size := by have := hCV.size_ge_two; omega
    have hb1 : colp[1]? = some (colp[1]'hsz) := Array.getElem?_eq_getElem hsz
    have hrow1 := hCV.bottom_row (colp[1]'hsz) hb1
    have h1v : (1 : Row) ≤ cv.row := one_le_row hV hcv hv0
    have := hmax 1 (colp[1]'hsz) (by simp [cell?, hcolp, hb1])
      (by rw [hrow1]; exact lt_of_le_of_lt h1v hvu)
    omega
  exact highestAtMost_of_max rfl hpe0 hcpe hle
    (fun j c hc _ hcr => hmax j c hc (lt_of_le_of_lt hcr hvu))

/-! # Part 4: `LeftCopy` and `CleanStep` as lookups -/

/-- The left end of a copied node is in the image of the leg column of its origin. -/
theorem copyAt_left {s : List Nat} {n D : Nat} {M : Mountain} {out : List Nat} {ρ : Root}
    {R : Mountain} {col : Column} {t : Cell} (hS : Setting s n D M out ρ R col t) {i : Nat}
    (hi0 : 0 < i) (hi : i < n + 1) {u : Ref} {o : Origin}
    (h : CopyAt M R n ρ.cr ρ.x0 (official t.row) i u o) :
    ∃ (cu : Cell) (ref : Ref) (co : Cell) (l : Ref), cell? R u = some cu ∧ cu.left = some ref ∧
      cell? M o.src = some co ∧ co.left = some l ∧
      ref.column = mapColumn ρ.cr ((ρ.x0 - ρ.cr) * i) l.column := by
  have hV := build_valid_of_success hS.splice.build
  obtain ⟨y, es, j, hj, ho, ⟨hvc, hcy, hyx, hXR⟩, hvi, hes, cu, hcu, _, ref, hrefl, hrefc⟩ :=
    copyAt_cell hS hi0 hi h
  obtain ⟨hsc, hsi, co, hco, hleft⟩ := emitsT_good hes es[j] (List.getElem_mem hj)
  rw [ho] at hsc hsi hco hleft
  rcases hleft with ⟨l, hl, hlc⟩ | ⟨hnone, h0, hnu⟩
  · refine ⟨cu, ref, co, l, hcu, hrefl, hco, hl, ?_⟩
    rw [hrefc]
    simp only [legColumn, hlc, ctxAt, mapColumn]
    by_cases hh : ρ.cr ≤ l.column
    · simp [hh, show ¬ l.column < ρ.cr by omega]
    · simp [hh, show l.column < ρ.cr by omega]
  · -- a bottom node: its leg is the phantom of the previous column
    rw [hnu] at hsc
    simp only [Bool.false_eq_true, if_false, ctxAt] at hsc
    have hi1 := index_one_of_official_zero hV hco hsi h0
    have hbl := bottom_left hS.splice.build hco hi1 (by omega)
    refine ⟨cu, ref, co, ⟨o.src.column - 1, 0⟩, hcu, hrefl, hco, hbl, ?_⟩
    rw [hrefc]
    simp only [legColumn, hnone, ctxAt, Array.size_extract]
    rw [hsc, mapColumn_of_ge (by omega), hvc]
    omega

/-- (open) `LeftCopy` as a lookup: the highest node of the output leg column at or below the
row of `v` matches the raw parent `pa` of `m`. -/
def LegLookup : Prop :=
  ∀ s n D M out ρ R (col : Column) (t : Cell), Setting s n D M out ρ R col t →
    ∀ i, 0 < i → i < n + 1 → ∀ v m,
      CopyNode M R n ρ.cr ρ.x0 (official t.row) i v m →
      CopyNode M R n ρ.cr ρ.x0 (official t.row) i (up v) (up m) →
      ∀ pa, rawParent M m = some pa → ∀ cv, cell? R v = some cv →
      ∃ pe, highestAtMost R (mapColumn ρ.cr ((ρ.x0 - ρ.cr) * i) pa.column) cv.row = some pe ∧
        (pa.column < ρ.cr → pe = pa) ∧
        (pa.column = ρ.cr → ∀ k m'', MStep M k m pa → MStep M k pa m'' → ScaleReach R k pe m'') ∧
        (ρ.cr < pa.column → CopyNode M R n ρ.cr ρ.x0 (official t.row) i pe pa)

/-- **`LeftCopy` from `LegLookup`** (the output mountain is canonical). -/
theorem leftCopy_of_legLookup (h : LegLookup) : LeftCopy := by
  intro s n D M out ρ R col t hS i hi0 hi v m hvm hup pa hpa
  have hVR := build_valid_of_success hS.canon
  obtain ⟨o', hvo', hsrc', _⟩ := copyAt_of_copyNode hup
  obtain ⟨cu, ref, co, l, hcu, hrefl, hco, hl, hrefc⟩ := copyAt_left hS hi0 hi hvo'
  rw [hsrc'] at hco
  obtain ⟨c, hc, hcl⟩ := rawParent_eq_some.mp hpa
  have hcc : c = co := Option.some.inj (hc.symm.trans hco)
  subst hcc
  have hll : l = pa := Option.some.inj (hl.symm.trans hcl)
  subst hll
  have hraw : rawParent R v = some ref := rawParent_eq_some.mpr ⟨cu, hcu, hrefl⟩
  obtain ⟨⟨cv, hcv⟩, _, _⟩ := rawParent_cells hVR hraw
  have hv0 := (copyNode_index_pos hvm).1
  have hham := canon_rawParent_hAM hS.canon hv0 hcv hraw
  obtain ⟨pe, hpe, hlow, hroot, hcopy⟩ := h s n D M out ρ R col t hS i hi0 hi v m hvm hup l hpa cv hcv
  rw [hrefc] at hham
  have hpr : pe = ref := Option.some.inj (hpe.symm.trans hham)
  subst hpr
  refine ⟨pe, hraw, hlow, fun hcr => ⟨?_, hroot hcr⟩, hcopy⟩
  rw [hrefc, hcr, mapColumn_of_ge (le_refl _)]

/-- (open) After a clean copy (`b = 0`) of `a` the column continues with a gap copy of `a`. -/
def CleanNext : Prop :=
  ∀ s n D M out ρ R (col : Column) (t : Cell), Setting s n D M out ρ R col t →
    ∀ i, 0 < i → i < n + 1 → ∀ v a,
      CopyAt M R n ρ.cr ρ.x0 (official t.row) i v (.clean a false) →
      CopyAt M R n ρ.cr ρ.x0 (official t.row) i (up v) (.clean a true)

/-- (open) `CleanStep` as a lookup: the highest node of the image of the leg column of `a`
at or below the row of the clean copy `v` of `a` is at the same row, and it is the clean copy
of the next generation `b`, or, in the root column, a node whose chain follows `b`. -/
def CleanLookup : Prop :=
  ∀ s n D M out ρ R (col : Column) (t : Cell), Setting s n D M out ρ R col t →
    ∀ i, 0 < i → i < n + 1 → ∀ v a,
      CopyAt M R n ρ.cr ρ.x0 (official t.row) i v (.clean a false) →
      ∀ (ca : Cell) (l : Ref) (cv : Cell), cell? M a = some ca → ca.left = some l →
        cell? R v = some cv →
      ∃ b v1, ∃ c1 : Cell, GenStep M ρ.cr a b ∧ ρ.cr ≤ b.column ∧
        highestAtMost R (mapColumn ρ.cr ((ρ.x0 - ρ.cr) * i) l.column) cv.row = some v1 ∧
        cell? R v1 = some c1 ∧ c1.row = cv.row ∧
        (ρ.cr < b.column → CopyAt M R n ρ.cr ρ.x0 (official t.row) i v1 (.clean b false)) ∧
        (b.column = ρ.cr → ∀ k m'', MStep M k b m'' → ScaleReach R k v1 m'')

theorem highestAtMost_column {M : Mountain} {l : Nat} {row : Row} {p : Ref}
    (h : highestAtMost M l row = some p) : p.column = l := by
  unfold highestAtMost at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨_, _, _, _, rfl⟩ := h
  rfl

/-- **`CleanStep` from `CleanNext` and `CleanLookup`** (the output mountain is canonical). -/
theorem cleanStep_of_parts (hN : CleanNext) (hL : CleanLookup) : CleanStep := by
  intro s n D M out ρ R col t hS i hi0 hi v a hva
  have hVR := build_valid_of_success hS.canon
  have hup := hN s n D M out ρ R col t hS i hi0 hi v a hva
  obtain ⟨cu, ref, ca, l, hcu, hrefl, hca, hl, hrefc⟩ := copyAt_left hS hi0 hi hup
  simp only [Origin.src] at hca
  have hraw : rawParent R v = some ref := rawParent_eq_some.mpr ⟨cu, hcu, hrefl⟩
  obtain ⟨⟨cv, hcv⟩, _, _⟩ := rawParent_cells hVR hraw
  have hv0 : 0 < v.index := by
    obtain ⟨_, _, j, _, _, _, _, hvi, _⟩ := hva
    omega
  have hham := canon_rawParent_hAM hS.canon hv0 hcv hraw
  obtain ⟨b, v1, c1, hgen, hcrb, hv1, hc1, hrow, hin, hroot⟩ :=
    hL s n D M out ρ R col t hS i hi0 hi v a hva ca l cv hca hl hcv
  rw [hrefc] at hham
  have hvr : v1 = ref := Option.some.inj (hv1.symm.trans hham)
  subst hvr
  refine ⟨v1, b, hraw, hgen, hcrb, ⟨cv, c1, hcv, hc1, hrow⟩, hin, fun hbc => ⟨?_, hroot hbc⟩⟩
  obtain ⟨_, _, _, _, l', hca', hl', hbl, _⟩ := hgen
  have hcc : ca = _ := Option.some.inj (hca.symm.trans hca')
  subst hcc
  have hll : l = l' := Option.some.inj (hl.symm.trans hl')
  subst hll
  rw [hrefc, ← hbl, hbc, mapColumn_of_ge (le_refl _)]

/-- **`StepInner` from the one-column statements and the lookups.** -/
theorem stepInner_of_lookups (hNext : NextCopyPlain) (hLeg : LegLookup) (hBump : BumpCopyLower)
    (hCN : CleanNext) (hCL : CleanLookup) (hCP : CleanParent) : StepInner :=
  stepInner_of_local hNext (leftCopy_of_legLookup hLeg) hBump (cleanStep_of_parts hCN hCL) hCP

/-! # Part 5: `NextCopyPlain` from the profile of a column

The statements `CopyEmitted`, `CopyMono`, `CopyFirst` below have the same content as the
open statements of the same names in `ChainCorrStartCopy.lean` (the profile of a block used
for `StartCopy`); they are restated here over `Setting` so that this file does not depend on
that one. With them, `NextCopyPlain` needs one more one-column statement, `PlainOnce`: a plain
origin is emitted once in its column. `CopyMono` and `PlainOnce` are proved in Part 6. -/

/-- (open, = `ChainCorrStartCopy.CopyEmitted`) In an inner column every node is the origin of
a non-cut copy. -/
def CopyEmitted : Prop :=
  ∀ s n D M out ρ R (col : Column) (t : Cell), Setting s n D M out ρ R col t →
    ∀ i, 0 < i → i < n + 1 → ∀ y es, ρ.cr < y → y < ρ.x0 →
      emitsT (ctxAt M R y i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 (y + (ρ.x0 - ρ.cr) * i)) (official t.row) =
        .ok es →
      ∀ (p : Ref) c, p.column = y → 1 ≤ p.index → cell? M p = some c →
        ∃ k, ∃ hk : k < es.length, es[k].2.src = p ∧ cutOrigin es[k].2 = false

/-- (open, = `ChainCorrStartCopy.CopyMono`) In an inner column the origin rows of the emits
do not decrease. -/
def CopyMono : Prop :=
  ∀ s n D M out ρ R (col : Column) (t : Cell), Setting s n D M out ρ R col t →
    ∀ i, 0 < i → i < n + 1 → ∀ y es, ρ.cr < y → y < ρ.x0 →
      emitsT (ctxAt M R y i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 (y + (ρ.x0 - ρ.cr) * i)) (official t.row) =
        .ok es →
      ∀ k k' (hk : k < es.length) (hk' : k' < es.length), k ≤ k' →
        ∀ c c', cell? M es[k].2.src = some c → cell? M es[k'].2.src = some c' → c.row ≤ c'.row

/-- (open, = `ChainCorrStartCopy.CopyFirst`) In an inner column the first emit of every
origin is not a gap copy. -/
def CopyFirst : Prop :=
  ∀ s n D M out ρ R (col : Column) (t : Cell), Setting s n D M out ρ R col t →
    ∀ i, 0 < i → i < n + 1 → ∀ y es, ρ.cr < y → y < ρ.x0 →
      emitsT (ctxAt M R y i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 (y + (ρ.x0 - ρ.cr) * i)) (official t.row) =
        .ok es →
      ∀ k (hk : k < es.length),
        (∀ k' (hk' : k' < es.length), k' < k → es[k'].2.src ≠ es[k].2.src) →
        cutOrigin es[k].2 = false

/-- (open) In an inner column a plain origin is emitted once. -/
def PlainOnce : Prop :=
  ∀ s n D M out ρ R (col : Column) (t : Cell), Setting s n D M out ρ R col t →
    ∀ i, 0 < i → i < n + 1 → ∀ y es, ρ.cr < y → y < ρ.x0 →
      emitsT (ctxAt M R y i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 (y + (ρ.x0 - ρ.cr) * i)) (official t.row) =
        .ok es →
      ∀ j (hj : j < es.length) m, es[j].2 = .plain m →
        ∀ k (hk : k < es.length), es[k].2.src = m → k = j

theorem ref_ext {a b : Ref} (h1 : a.column = b.column) (h2 : a.index = b.index) : a = b := by
  cases a
  cases b
  simp_all

/-- In a valid mountain, a node of a column whose row is at most the row of another node of
the same column is not above it. -/
theorem index_le_of_row_le {M : Mountain} (hV : MountainValid M) {a b : Ref} {ca cb : Cell}
    (hcol : a.column = b.column) (ha : cell? M a = some ca) (hb : cell? M b = some cb)
    (hr : ca.row ≤ cb.row) : a.index ≤ b.index := by
  by_contra hlt
  push Not at hlt
  unfold cell? at ha hb
  rw [hcol] at ha
  cases hcM : M[b.column]? with
  | none => simp [hcM] at ha
  | some col =>
      simp only [hcM, Option.bind_eq_bind, Option.bind_some] at ha hb
      have hc : b.column < M.size := by
        rcases Nat.lt_or_ge b.column M.size with h' | h'
        · exact h'
        · simp [Array.getElem?_eq_none h'] at hcM
      have hCV := hV b.column hc
      rw [show M[b.column] = col from by
        have := hcM; rw [Array.getElem?_eq_getElem hc] at this; exact Option.some.inj this] at hCV
      have := hCV.rows_strict _ _ _ _ hb ha hlt
      exact absurd (lt_of_lt_of_le this hr) (lt_irrefl _)

/-- The origin of an emit of an inner column is a real node of that column. -/
theorem src_inner {M R : Mountain} {y i cr x0 X : Nat} {τ : Row} {es : List (Emit × Origin)}
    (hyx : y < x0) (hes : emitsT (ctxAt M R y i cr (x0 - cr) x0 X) τ = .ok es) (k : Nat)
    (hk : k < es.length) :
    es[k].2.src.column = y ∧ 1 ≤ es[k].2.src.index ∧ ∃ c, cell? M es[k].2.src = some c := by
  obtain ⟨hcol, hidx, c, hc, _⟩ := emitsT_good hes es[k] (List.getElem_mem hk)
  refine ⟨?_, hidx, c, hc⟩
  rw [hcol]
  split
  · simp [upperColumn, ctxAt, show y ≠ x0 by omega]
  · simp [ctxAt]

/-- **`NextCopyPlain` from the profile of a column and `PlainOnce`.** -/
theorem nextCopyPlain_of_profile (hB : CopyEmitted) (hC1 : CopyMono) (hC2 : CopyFirst)
    (hP : PlainOnce) : NextCopyPlain := by
  intro s n D M out ρ R col t hS i hi0 hi v m hvp hup
  obtain ⟨cp, hcp⟩ := hup
  have hV := build_valid_of_success hS.splice.build
  obtain ⟨y, es, j, hcy, hyx, hyb, hvc, hvi, hes, hj, ho⟩ := hvp
  rw [hvc] at hes
  obtain ⟨hmc, hmi, cm, hcm⟩ := src_inner hyx hes j hj
  simp only [ho, Origin.src] at hmc hmi hcm
  -- the copy of `m⁺`
  obtain ⟨k, hk, hks, hknc⟩ := hB s n D M out ρ R col t hS i hi0 hi y es hcy hyx hes (up m) cp
    (by simp [up, hmc]) (by simp [up]) hcp
  have hmm : cm.row < cp.row := by
    unfold cell? at hcm hcp
    cases hcM : M[m.column]? with
    | none => simp [hcM] at hcm
    | some colm =>
        simp only [up, hcM, Option.bind_eq_bind, Option.bind_some] at hcm hcp
        have hc : m.column < M.size := by
          rcases Nat.lt_or_ge m.column M.size with h' | h'
          · exact h'
          · simp [Array.getElem?_eq_none h'] at hcM
        have hCV := hV m.column hc
        rw [show M[m.column] = colm from by
          have := hcM; rw [Array.getElem?_eq_getElem hc] at this; exact Option.some.inj this] at hCV
        exact hCV.rows_strict _ _ _ _ hcm hcp (by omega)
  have hmsrc : cell? M es[j].2.src = some cm := by rw [ho]; exact hcm
  have hksrc : cell? M es[k].2.src = some cp := by rw [hks]; exact hcp
  have hjk : j < k := by
    by_contra hle
    push Not at hle
    have := hC1 s n D M out ρ R col t hS i hi0 hi y es hcy hyx hes k j hk hj hle cp cm hksrc hmsrc
    exact absurd (lt_of_lt_of_le hmm this) (lt_irrefl _)
  have hj1 : j + 1 < es.length := by omega
  -- the origin of the next emit
  obtain ⟨hsc, hsi, c1, hc1⟩ := src_inner hyx hes (j + 1) hj1
  have h1 := hC1 s n D M out ρ R col t hS i hi0 hi y es hcy hyx hes j (j + 1) hj hj1 (by omega)
    cm c1 hmsrc hc1
  have h2 := hC1 s n D M out ρ R col t hS i hi0 hi y es hcy hyx hes (j + 1) k hj1 hk (by omega)
    c1 cp hc1 hksrc
  have hi1 := index_le_of_row_le hV (by rw [hmc, hsc]) hcm hc1 h1
  have hi2 := index_le_of_row_le hV (by rw [hsc]; simp [up, hmc]) hc1 hcp h2
  simp only [up] at hi2
  have hsrc : es[j + 1].2.src = up m := by
    rcases Nat.lt_or_eq_of_le hi1 with hlt | heq
    · exact ref_ext (by rw [hsc]; simp [up, hmc]) (by simp [up]; omega)
    · exfalso
      have hsm : es[j + 1].2.src = m := ref_ext (by rw [hsc, hmc]) heq.symm
      have := hP s n D M out ρ R col t hS i hi0 hi y es hcy hyx hes j hj m ho (j + 1) hj1 hsm
      omega
  -- it is the first emit of `m⁺`, so it is not a gap copy
  have hnc : cutOrigin es[j + 1].2 = false := by
    apply hC2 s n D M out ρ R col t hS i hi0 hi y es hcy hyx hes (j + 1) hj1
    intro k' hk' hlt heq
    have hk'c : cell? M es[k'].2.src = some cp := by rw [heq, hsrc]; exact hcp
    have := hC1 s n D M out ρ R col t hS i hi0 hi y es hcy hyx hes k' j hk' hj (by omega)
      cp cm hk'c hmsrc
    exact absurd (lt_of_lt_of_le hmm this) (lt_irrefl _)
  refine ⟨y, es, j + 1, hcy, hyx, hyb, by simp [up, hvc], by simp [up, hvi], ?_, hj1, hsrc,
    Or.inl hnc⟩
  simp only [up]
  rw [hvc]
  exact hes

/-- **`StepInner` from the profile of a column and the remaining statements.** -/
theorem stepInner_of_profile (hB : CopyEmitted) (hC1 : CopyMono) (hC2 : CopyFirst)
    (hP : PlainOnce) (hLeg : LegLookup) (hBump : BumpCopyLower) (hCN : CleanNext)
    (hCL : CleanLookup) (hCP : CleanParent) : StepInner :=
  stepInner_of_lookups (nextCopyPlain_of_profile hB hC1 hC2 hP) hLeg hBump hCN hCL hCP

/-! # Part 6: the origins of a column come in row order

In every column made by `copyColumn`, the origins of the lower part come in increasing row
order, and two emits with origins at the same row are both copies of the root row
(`Origin.clean`): the gap copies repeat the origin of the clean copy just before them
(`lowerT_order`). With the upper part (rows `≥ τ`, in order) this gives `CopyMono` and
`PlainOnce` (`copyMono_holds`, `plainOnce_holds`). The proof is an induction over the item
recursion of notes/03 §2.3–§2.4 that tracks, for every item, the region of its origins and
their position relative to the copied root row `C` (below `C` for a clean item with `b = 0`,
at `C` for `b = 1`, above the top of the root column for a cut item without `C`). -/

def isPlainO : Origin → Bool
  | .plain _ => true
  | _ => false

def isCleanO : Origin → Bool
  | .clean _ _ => true
  | _ => false

theorem not_plain_and_clean (o : Origin) (h1 : isPlainO o = true) (h2 : isCleanO o = true) :
    False := by
  cases o <;> simp [isPlainO, isCleanO] at h1 h2

/-- `p` comes before `q`: its origin row is lower, or both are copies of the same root row. -/
def SrcRel (M : Mountain) (p q : Emit × Origin) : Prop :=
  ∀ cp cq : Cell, cell? M p.2.src = some cp → cell? M q.2.src = some cq →
    official cp.row < official cq.row ∨
      (official cp.row = official cq.row ∧ isCleanO p.2 = true ∧ isCleanO q.2 = true)

/-- What an item of level `d` guarantees about each of its emits. -/
def EmitOK (M : Mountain) (cr d : Nat) (it : Item) (p : Emit × Origin) : Prop :=
  (isPlainO p.2 = true ∨ isCleanO p.2 = true) ∧ ∃ c, cell? M p.2.src = some c ∧
    inRegion d it.source (official c.row) = true ∧
    (∀ C, it.clean = some C → it.cutBottom = false →
      official c.row ≤ C ∧ (isPlainO p.2 = true → official c.row < C)) ∧
    (∀ C, it.clean = some C → it.cutBottom = true → official c.row = C ∧ isCleanO p.2 = true) ∧
    (it.clean = none → it.cutBottom = true → 2 ≤ d → ∀ r ρc,
      topIn M cr d it.source = some (r, ρc) →
        official ρc.row ≤ official c.row ∧ (isPlainO p.2 = true → official ρc.row < official c.row))

/-- The copied root row of an item is the row of the top of the root column in its region. -/
def ItemInvC (M : Mountain) (cr d : Nat) (it : Item) : Prop :=
  ∀ C, it.clean = some C → ∃ r ρc, topIn M cr d it.source = some (r, ρc) ∧ official ρc.row = C

/-- How two sibling items are separated. -/
def ChildSep (M : Mountain) (cr d : Nat) (S : Row) (a b : Item) : Prop :=
  (∃ j j', a.source = slot (d + 2) S j ∧ b.source = slot (d + 2) S j' ∧ j < j') ∨
  (∃ C, a.clean = some C ∧ ((b.clean = some C ∧ b.cutBottom = true) ∨
    (b.clean = none ∧ b.cutBottom = true ∧ 1 ≤ d ∧
      ∃ r ρc, topIn M cr (d + 1) b.source = some (r, ρc) ∧ official ρc.row = C)))

theorem slot_rows_lt {d : Nat} {S r r' : Row} {j j' : Nat}
    (h : inRegion (d + 1) (slot (d + 2) S j) r = true)
    (h' : inRegion (d + 1) (slot (d + 2) S j') r' = true) (hjj : j < j') : r < r' := by
  obtain ⟨hS, hd⟩ := Recon.RowLaw.inRegion_slot_iff.mp h
  obtain ⟨hS', hd'⟩ := Recon.RowLaw.inRegion_slot_iff.mp h'
  refine Row.lt_iff.mpr ⟨d, ?_, by omega⟩
  intro q hq
  rw [Recon.RowLaw.inRegion_iff'.mp hS q (by omega), Recon.RowLaw.inRegion_iff'.mp hS' q (by omega)]

/-- An item whose origins are at or below `C`, plain ones strictly below. -/
theorem emitOK_lower {M : Mountain} {cr d : Nat} {a : Item} {C : Row} (ha : a.clean = some C)
    {p : Emit × Origin} {c : Cell} (hc : cell? M p.2.src = some c) (hp : EmitOK M cr d a p) :
    official c.row ≤ C ∧ (isPlainO p.2 = true → official c.row < C) := by
  obtain ⟨_, c', hc', _, h0, h1, _⟩ := hp
  rw [hc] at hc'
  cases hc'
  cases hb : a.cutBottom
  · exact h0 C ha hb
  · obtain ⟨heq, hcl⟩ := h1 C ha hb
    exact ⟨le_of_eq heq, fun hpl => absurd (not_plain_and_clean _ hpl hcl) id⟩

theorem sep_rel {M : Mountain} {cr d : Nat} {S : Row} {a b : Item} (hs : ChildSep M cr d S a b)
    {p q : Emit × Origin} (hp : EmitOK M cr (d + 1) a p) (hq : EmitOK M cr (d + 1) b q) :
    SrcRel M p q := by
  intro cp cq hcp hcq
  rcases hs with ⟨j, j', hja, hjb, hjj⟩ | ⟨C, haC, hb⟩
  · obtain ⟨_, c, hc, hreg, _⟩ := hp
    obtain ⟨_, c', hc', hreg', _⟩ := hq
    rw [hcp] at hc; cases hc
    rw [hcq] at hc'; cases hc'
    rw [hja] at hreg
    rw [hjb] at hreg'
    exact Or.inl (slot_rows_lt hreg hreg' hjj)
  · obtain ⟨hle, hpl⟩ := emitOK_lower haC hcp hp
    -- `q` is at or above `C`, plain ones strictly above
    have hup : C ≤ official cq.row ∧ (isPlainO q.2 = true → C < official cq.row) := by
      obtain ⟨_, c', hc', _, _, h1, h2⟩ := hq
      rw [hcq] at hc'; cases hc'
      rcases hb with ⟨hbC, hbb⟩ | ⟨hbn, hbb, hd, r, ρc, hρ, hρC⟩
      · obtain ⟨heq, hcl⟩ := h1 C hbC hbb
        exact ⟨le_of_eq heq.symm, fun hpl' => absurd (not_plain_and_clean _ hpl' hcl) id⟩
      · obtain ⟨h3, h4⟩ := h2 hbn hbb (by omega) r ρc hρ
        rw [hρC] at h3 h4
        exact ⟨h3, h4⟩
    rcases lt_or_eq_of_le (le_trans hle hup.1) with hlt | heq
    · exact Or.inl hlt
    · right
      refine ⟨heq, ?_, ?_⟩
      · rcases hp.1 with hpl' | hcl
        · exact absurd (lt_of_lt_of_le (hpl hpl') hup.1) (by rw [heq]; exact lt_irrefl _)
        · exact hcl
      · rcases hq.1 with hpl' | hcl
        · exact absurd (lt_of_le_of_lt hle (hup.2 hpl')) (by rw [heq]; exact lt_irrefl _)
        · exact hcl

theorem getLast?_filter_sub {α : Type} {l : List α} {P Q : α → Bool} {x : α}
    (hQP : ∀ a, Q a = true → P a = true) (h : (l.filter P).getLast? = some x)
    (hx : Q x = true) : (l.filter Q).getLast? = some x := by
  have hfil : l.filter Q = (l.filter P).filter Q := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro a _
    cases hq : Q a
    · simp
    · simp [hQP a hq]
  rw [hfil]
  obtain ⟨L, hL⟩ := List.getLast?_eq_some_iff.mp h
  rw [hL, List.filter_append]
  simp [hx]

/-- The top of a column in a region is its top in the slot of the region that contains it. -/
theorem topIn_slot {M : Mountain} {c d : Nat} {S : Row} {r : Ref} {cl : Cell}
    (h : topIn M c (d + 2) S = some (r, cl)) :
    topIn M c (d + 1) (slot (d + 2) S ((official cl.row).coeff d)) = some (r, cl) := by
  have hreg := topIn_inRegion h
  unfold topIn at h ⊢
  exact getLast?_filter_sub (fun p hp => Recon.RowLaw.inRegion_of_slot hp) h
    (Recon.RowLaw.inRegion_slot_iff.mpr ⟨hreg, rfl⟩)

theorem levelOneT_order {ctx : Context} {it : Item} {ps : List (Emit × Origin)}
    (h : levelOneT ctx it = .ok ps) (hinv : ItemInvC ctx.source ctx.rootColumn 1 it) :
    ps.Pairwise (SrcRel ctx.source) ∧ ∀ p ∈ ps, EmitOK ctx.source ctx.rootColumn 1 it p := by
  unfold levelOneT at h
  cases hsrc : nodeAt ctx.source ctx.x it.source with
  | none => simp [hsrc, pure, Except.pure] at h; subst h; simp
  | some q =>
      obtain ⟨srcRef, src⟩ := q
      obtain ⟨_, _, hscell, hsrow⟩ := nodeAt_spec hsrc
      simp only at hscell hsrow
      simp only [hsrc] at h
      cases hC : it.clean with
      | some C =>
          simp only [hC] at h
          cases hcs : nodeAt ctx.source ctx.x C with
          | none => simp [hcs, throw, throwThe, MonadExceptOf.throw] at h
          | some q' =>
              obtain ⟨csRef, cs⟩ := q'
              obtain ⟨_, _, hccell, hcrow⟩ := nodeAt_spec hcs
              simp only at hccell hcrow
              simp only [hcs, bind, Except.bind, pure, Except.pure] at h
              split at h
              · cases h
              · cases h
                refine ⟨List.pairwise_singleton _ _, ?_⟩
                intro p hp
                simp only [List.mem_singleton] at hp
                subst hp
                obtain ⟨r, ρc, hρ, hρC⟩ := hinv C hC
                have hreg := topIn_inRegion hρ
                rw [hρC] at hreg
                refine ⟨Or.inr rfl, cs, hccell, by rw [hcrow]; exact hreg, ?_, ?_, ?_⟩
                · intro C' hC' _
                  rw [hC] at hC'; cases hC'
                  exact ⟨le_of_eq hcrow, fun h' => by simp [isPlainO] at h'⟩
                · intro C' hC' _
                  rw [hC] at hC'; cases hC'
                  exact ⟨hcrow, rfl⟩
                · intro hn; rw [hC] at hn; cases hn
      | none =>
          simp only [hC] at h
          have fin : ∀ ps' : List (Emit × Origin), (∀ p ∈ ps', p.2 = .plain srcRef) →
              ps'.length ≤ 1 →
              ps'.Pairwise (SrcRel ctx.source) ∧
                ∀ p ∈ ps', EmitOK ctx.source ctx.rootColumn 1 it p := by
            intro ps' hall hlen
            refine ⟨?_, ?_⟩
            · match ps', hlen with
              | [], _ => exact List.Pairwise.nil
              | [_], _ => exact List.pairwise_singleton _ _
            · intro p hp
              have hpo := hall p hp
              refine ⟨Or.inl (by rw [hpo]; rfl), src, by rw [hpo]; exact hscell,
                by rw [hsrow]; exact inRegion_self 1 _, ?_, ?_, ?_⟩
              · intro C' hC'; rw [hC] at hC'; cases hC'
              · intro C' hC'; rw [hC] at hC'; cases hC'
              · intro _ _ h2; omega
          split at h
          · simp only [pure, Except.pure, Except.ok.injEq] at h
            subst h
            exact fin _ (by simp) (by simp)
          · simp only [bind, Except.bind, pure, Except.pure] at h
            split at h
            · cases h
            · cases h
              exact fin _ (by simp) (by simp)

theorem emitOK_parent {M : Mountain} {cr d : Nat} {it c : Item} {p : Emit × Origin} {j : Nat}
    (hsrc : c.source = slot (d + 2) it.source j) (hp : EmitOK M cr (d + 1) c p)
    (h1 : ∀ C, it.clean = some C → it.cutBottom = false → ∀ c0 : Cell,
      cell? M p.2.src = some c0 → official c0.row ≤ C ∧ (isPlainO p.2 = true → official c0.row < C))
    (h2 : ∀ C, it.clean = some C → it.cutBottom = true → ∀ c0 : Cell,
      cell? M p.2.src = some c0 → official c0.row = C ∧ isCleanO p.2 = true)
    (h3 : it.clean = none → it.cutBottom = true → ∀ c0 : Cell, cell? M p.2.src = some c0 →
      ∀ r ρc, topIn M cr (d + 2) it.source = some (r, ρc) →
        official ρc.row ≤ official c0.row ∧ (isPlainO p.2 = true → official ρc.row < official c0.row)) :
    EmitOK M cr (d + 2) it p := by
  obtain ⟨hk, c0, hc0, hreg, _⟩ := hp
  rw [hsrc] at hreg
  exact ⟨hk, c0, hc0, Recon.RowLaw.inRegion_of_slot hreg, fun C hC hb => h1 C hC hb c0 hc0,
    fun C hC hb => h2 C hC hb c0 hc0, fun hn hb _ r ρc hρ => h3 hn hb c0 hc0 r ρc hρ⟩

theorem childItems_order {ctx : Context} {d : Nat} {it : Item} {cs : List Item}
    (h : childItems ctx (d + 2) it = .ok cs)
    (hinv : ItemInvC ctx.source ctx.rootColumn (d + 2) it) :
    (∀ c ∈ cs, ItemInvC ctx.source ctx.rootColumn (d + 1) c) ∧
    cs.Pairwise (ChildSep ctx.source ctx.rootColumn d it.source) ∧
    (∀ c ∈ cs, ∀ p, EmitOK ctx.source ctx.rootColumn (d + 1) c p →
      EmitOK ctx.source ctx.rootColumn (d + 2) it p) := by
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
      · -- case 1: the region does not ascend
        rename_i hnv
        split at h
        · simp [throw, throwThe, MonadExceptOf.throw] at h
        · rename_i hcond
          obtain rfl := Except.ok.inj h
          have hcl : it.clean = none := by
            cases hc : it.clean
            · rfl
            · exact absurd (Or.inl (by simp [hc])) hcond
          have hcb : it.cutBottom = false := by
            cases hb : it.cutBottom
            · rfl
            · exact absurd (Or.inr (Or.inr hb)) hcond
          refine ⟨?_, ?_, ?_⟩
          · intro c hc C hC
            simp only [List.mem_map] at hc
            obtain ⟨j, _, rfl⟩ := hc
            cases hC
          · rw [List.pairwise_map]
            exact List.pairwise_lt_range.imp fun {j j'} hjj => Or.inl ⟨j, j', rfl, rfl, hjj⟩
          · intro c hc p hp
            simp only [List.mem_map] at hc
            obtain ⟨j, _, rfl⟩ := hc
            refine emitOK_parent rfl hp ?_ ?_ ?_
            · intro C hC; rw [hcl] at hC; cases hC
            · intro C hC; rw [hcl] at hC; cases hC
            · intro _ hb; rw [hcb] at hb; cases hb
      · -- the region ascends: the top of the root column exists
        rename_i hvt
        have hvt' : v = true := by simpa using hvt
        subst hvt'
        obtain ⟨ρr, ρc, rfl⟩ : ∃ a b, rho = some (a, b) := by
          cases rho with
          | none => simp [ascends, pure, Except.pure] at hv
          | some q => exact ⟨q.1, q.2, rfl⟩
        have hhR : heightOf (d + 2) (some (ρr, ρc)) = (official ρc.row).coeff d := by
          simp [heightOf, Recon.RowLaw.height_eq]
        have hsub := topIn_slot hrho
        rw [← hhR] at hsub
        have hρreg := topIn_inRegion hrho
        simp only at h
        generalize heightOf (d + 2) (some (ρr, ρc)) = hR at h hhR hsub
        split at h
        · -- clean = none
          rename_i hcl
          split at h
          · -- case 2
            rename_i hcb'
            have hcb : it.cutBottom = false := by simpa using hcb'
            have hl0 : ctx.block = 0 →
                (((heightOf (d + 2) (topIn ctx.source ctx.lastColumn (d + 2) it.source) : Nat) : Int)
                  - (hR : Int)) * (ctx.block : Int) = 0 := by
              intro h0; simp [h0]
            generalize (((heightOf (d + 2) (topIn ctx.source ctx.lastColumn (d + 2) it.source) : Nat) :
                Int) - (hR : Int)) * (ctx.block : Int) = lift at h hl0
            have he : ((if d + 2 = 2 then (1 : Int) else 0) = 1 ∧ d = 0) ∨
                ((if d + 2 = 2 then (1 : Int) else 0) = 0 ∧ 1 ≤ d) := by
              by_cases hd : d = 0
              · left; simp [hd]
              · right; simp [hd]; omega
            generalize (if d + 2 = 2 then (1 : Int) else 0) = e at h he
            obtain rfl := Except.ok.inj h
            refine ⟨?_, ?_, ?_⟩
            · intro c hc C hC
              simp only [List.mem_map] at hc
              obtain ⟨j, _, rfl⟩ := hc
              split_ifs at hC ⊢ with h1 h2
              all_goals (injection hC with hC'; exact ⟨ρr, ρc, hsub, hC'⟩)
            · rw [List.pairwise_map]
              refine List.pairwise_lt_range.imp fun {j j'} hjj => ?_
              by_cases a1 : j < hR
              · by_cases b1 : j' < hR
                · rw [if_pos a1, if_pos b1]
                  exact Or.inl ⟨j, j', rfl, rfl, hjj⟩
                · by_cases b2 : (j' : Int) < (hR : Int) + lift + e
                  · rw [if_pos a1, if_neg b1, if_pos b2]
                    exact Or.inl ⟨j, hR, rfl, rfl, a1⟩
                  · rw [if_pos a1, if_neg b1, if_neg b2]
                    exact Or.inl ⟨j, _, rfl, rfl, by omega⟩
              · have b1 : ¬ j' < hR := by omega
                by_cases a2 : (j : Int) < (hR : Int) + lift + e
                · by_cases b2 : (j' : Int) < (hR : Int) + lift + e
                  · rw [if_neg a1, if_pos a2, if_neg b1, if_pos b2]
                    exact Or.inr ⟨_, rfl, Or.inl ⟨rfl, by simp; omega⟩⟩
                  · rw [if_neg a1, if_pos a2, if_neg b1, if_neg b2]
                    -- a gap child before a lifted child
                    by_cases hs : hR < ((j' : Int) - lift).toNat
                    · exact Or.inl ⟨hR, _, rfl, rfl, hs⟩
                    · have hs' : ((j' : Int) - lift).toNat = hR := by omega
                      have hpos : 0 < lift := by omega
                      have hblk : ctx.block ≠ 0 := fun h0 => by
                        rw [hl0 h0] at hpos; exact lt_irrefl _ hpos
                      have he0 : e = 0 ∧ 1 ≤ d := by
                        rcases he with ⟨he1, hd0⟩ | ⟨he0, hd⟩
                        · exfalso; omega
                        · exact ⟨he0, hd⟩
                      have hj' : (j' : Int) = hR + lift := by omega
                      refine Or.inr ⟨_, rfl, Or.inr ⟨rfl, by simp [hblk, hj'], he0.2, ρr, ρc, ?_, rfl⟩⟩
                      rw [hs']; exact hsub
                · have b2 : ¬ (j' : Int) < (hR : Int) + lift + e := by omega
                  rw [if_neg a1, if_neg a2, if_neg b1, if_neg b2]
                  exact Or.inl ⟨_, _, rfl, rfl, by omega⟩
            · intro c hc p hp
              simp only [List.mem_map] at hc
              obtain ⟨j, _, rfl⟩ := hc
              split_ifs at hp
              all_goals
                refine emitOK_parent rfl hp ?_ ?_ ?_
                · intro C hC; rw [hcl] at hC; cases hC
                · intro C hC; rw [hcl] at hC; cases hC
                · intro _ hb; rw [hcb] at hb; cases hb
          · -- case 3
            rename_i hcb'
            have hcb : it.cutBottom = true := by simpa using hcb'
            have he : ((if d + 2 = 2 then (1 : Int) else 0) = 1 ∧ d = 0) ∨
                ((if d + 2 = 2 then (1 : Int) else 0) = 0 ∧ 1 ≤ d) := by
              by_cases hd : d = 0
              · left; simp [hd]
              · right; simp [hd]; omega
            generalize (if d + 2 = 2 then (1 : Int) else 0) = e at h he
            generalize heightOf (d + 2) (topIn ctx.result ctx.boundary (d + 2) it.target) = hB at h
            obtain rfl := Except.ok.inj h
            have hρslot : inRegion (d + 1) (slot (d + 2) it.source hR) (official ρc.row) = true :=
              Recon.RowLaw.inRegion_slot_iff.mpr ⟨hρreg, hhR.symm⟩
            refine ⟨?_, ?_, ?_⟩
            · intro c hc C hC
              simp only [List.mem_map] at hc
              obtain ⟨j, _, rfl⟩ := hc
              split_ifs at hC ⊢ with h1
              all_goals (injection hC with hC'; exact ⟨ρr, ρc, hsub, hC'⟩)
            · rw [List.pairwise_map]
              refine (List.pairwise_lt_range.filter _).imp fun {j j'} hjj => ?_
              by_cases a1 : (j : Int) < (hB : Int) + hR + e
              · by_cases b1 : (j' : Int) < (hB : Int) + hR + e
                · rw [if_pos a1, if_pos b1]
                  exact Or.inr ⟨_, rfl, Or.inl ⟨rfl, rfl⟩⟩
                · rw [if_pos a1, if_neg b1]
                  by_cases hs : hR < j' - hB
                  · exact Or.inl ⟨hR, _, rfl, rfl, hs⟩
                  · have hs' : j' - hB = hR := by omega
                    have he0 : e = 0 ∧ 1 ≤ d := by
                      rcases he with ⟨he1, hd0⟩ | ⟨he0, hd⟩
                      · exfalso; omega
                      · exact ⟨he0, hd⟩
                    refine Or.inr ⟨_, rfl, Or.inr ⟨rfl, by simp; omega, he0.2, ρr, ρc, ?_, rfl⟩⟩
                    rw [hs']; exact hsub
              · have b1 : ¬ (j' : Int) < (hB : Int) + hR + e := by omega
                rw [if_neg a1, if_neg b1]
                exact Or.inl ⟨_, _, rfl, rfl, by omega⟩
            · intro c hc p hp
              simp only [List.mem_map, List.mem_filter] at hc
              obtain ⟨j, _, rfl⟩ := hc
              by_cases a1 : (j : Int) < (hB : Int) + hR + e
              · rw [if_pos a1] at hp
                refine emitOK_parent rfl hp ?_ ?_ ?_
                · intro C hC; rw [hcl] at hC; cases hC
                · intro C hC; rw [hcl] at hC; cases hC
                · intro _ _ c0 hc0 r ρc' hρ'
                  rw [hrho] at hρ'
                  cases hρ'
                  obtain ⟨_, c1, hc1, _, _, h2, _⟩ := hp
                  rw [hc0] at hc1; cases hc1
                  obtain ⟨heq, hcl'⟩ := h2 _ rfl rfl
                  exact ⟨le_of_eq heq.symm, fun hpl => absurd (not_plain_and_clean _ hpl hcl') id⟩
              · rw [if_neg a1] at hp
                refine emitOK_parent rfl hp ?_ ?_ ?_
                · intro C hC; rw [hcl] at hC; cases hC
                · intro C hC; rw [hcl] at hC; cases hC
                · intro _ _ c0 hc0 r ρc' hρ'
                  rw [hrho] at hρ'
                  cases hρ'
                  by_cases hs : hR < j - hB
                  · obtain ⟨_, c1, hc1, hreg1, _⟩ := hp
                    rw [hc0] at hc1; cases hc1
                    have := slot_rows_lt hρslot hreg1 hs
                    exact ⟨le_of_lt this, fun _ => this⟩
                  · have hs' : j - hB = hR := by omega
                    have hj : j = hB + hR := by omega
                    have he0 : e = 0 ∧ 1 ≤ d := by
                      rcases he with ⟨he1, hd0⟩ | ⟨he0, hd⟩
                      · exfalso; omega
                      · exact ⟨he0, hd⟩
                    obtain ⟨_, c1, hc1, _, _, _, h3⟩ := hp
                    rw [hc0] at hc1; cases hc1
                    have hsub' := hsub
                    rw [← hs'] at hsub'
                    exact h3 rfl (by simp [hj]) (by omega) ρr ρc hsub'
        · -- case 4: a copy of the root row
          rename_i C hclC
          obtain ⟨r0, ρ0, hρ0, hρ0C⟩ := hinv C hclC
          rw [hrho] at hρ0
          injection hρ0 with hρ0'
          injection hρ0' with _ hρρ
          subst hρρ
          have hρslot : inRegion (d + 1) (slot (d + 2) it.source hR) (official ρc.row) = true :=
            Recon.RowLaw.inRegion_slot_iff.mpr ⟨hρreg, hhR.symm⟩
          split at h
          · simp [throw, throwThe, MonadExceptOf.throw] at h
          · split at h
            · cases h
            · split at h
              · simp [throw, throwThe, MonadExceptOf.throw] at h
              · obtain rfl := Except.ok.inj h
                refine ⟨?_, ?_, ?_⟩
                · intro c hc C' hC'
                  simp only [List.mem_map] at hc
                  obtain ⟨j, _, rfl⟩ := hc
                  split_ifs at hC' ⊢
                  all_goals (injection hC' with hC''; exact ⟨ρr, ρc, hsub, hρ0C.trans hC''⟩)
                · rw [List.pairwise_map]
                  refine List.pairwise_lt_range.imp fun {j j'} hjj => ?_
                  by_cases hb : it.cutBottom = true
                  · rw [if_pos hb, if_pos hb]
                    exact Or.inr ⟨C, rfl, Or.inl ⟨rfl, rfl⟩⟩
                  · rw [if_neg hb, if_neg hb]
                    by_cases a1 : j < hR
                    · by_cases b1 : j' < hR
                      · rw [if_pos a1, if_pos b1]
                        exact Or.inl ⟨j, j', rfl, rfl, hjj⟩
                      · rw [if_pos a1, if_neg b1]
                        exact Or.inl ⟨j, hR, rfl, rfl, a1⟩
                    · have b1 : ¬ j' < hR := by omega
                      rw [if_neg a1, if_neg b1]
                      exact Or.inr ⟨C, rfl, Or.inl ⟨rfl, by simp; omega⟩⟩
                · intro c hc p hp
                  simp only [List.mem_map] at hc
                  obtain ⟨j, _, rfl⟩ := hc
                  by_cases hb : it.cutBottom = true
                  · rw [if_pos hb] at hp
                    refine emitOK_parent rfl hp ?_ ?_ ?_
                    · intro _ _ hb'; rw [hb] at hb'; cases hb'
                    · intro C' hC' _ c0 hc0
                      rw [hclC] at hC'; cases hC'
                      obtain ⟨_, c1, hc1, _, _, h2, _⟩ := hp
                      rw [hc0] at hc1; cases hc1
                      exact h2 _ rfl rfl
                    · intro hn; rw [hclC] at hn; cases hn
                  · by_cases a1 : j < hR
                    · rw [if_neg hb, if_pos a1] at hp
                      refine emitOK_parent rfl hp ?_ ?_ ?_
                      · intro C' hC' _ c0 hc0
                        rw [hclC] at hC'; cases hC'
                        obtain ⟨_, c1, hc1, hreg1, _⟩ := hp
                        rw [hc0] at hc1; cases hc1
                        have := slot_rows_lt hreg1 hρslot a1
                        rw [hρ0C] at this
                        exact ⟨le_of_lt this, fun _ => this⟩
                      · intro _ _ hb'; exact absurd hb' hb
                      · intro hn; rw [hclC] at hn; cases hn
                    · rw [if_neg hb, if_neg a1] at hp
                      refine emitOK_parent rfl hp ?_ ?_ ?_
                      · intro C' hC' _ c0 hc0
                        rw [hclC] at hC'; cases hC'
                        exact emitOK_lower rfl hc0 hp
                      · intro _ _ hb'; exact absurd hb' hb
                      · intro hn; rw [hclC] at hn; cases hn

theorem runItemT_order (ctx : Context) :
    ∀ (d : Nat) (it : Item) (ps : List (Emit × Origin)), runItemT ctx d it = .ok ps →
      ItemInvC ctx.source ctx.rootColumn d it →
      ps.Pairwise (SrcRel ctx.source) ∧ ∀ p ∈ ps, EmitOK ctx.source ctx.rootColumn d it p
  | 0, _, ps, h, _ => by simp [runItemT, pure, Except.pure] at h; subst h; simp
  | 1, it, ps, h, hinv => levelOneT_order (by simpa [runItemT] using h) hinv
  | d + 2, it, ps, h, hinv => by
      simp only [runItemT, bind, Except.bind, pure, Except.pure] at h
      split at h
      · cases h
      · rename_i children hch
        split at h
        · cases h
        · rename_i outs houts
          cases h
          obtain ⟨hinvc, hsep, hup⟩ := childItems_order hch hinv
          obtain ⟨hlen, hall⟩ := mapM_except_spec _ _ _ houts
          have hIH : ∀ a (ha : a < outs.length), outs[a].Pairwise (SrcRel ctx.source) ∧
              ∀ p ∈ outs[a], EmitOK ctx.source ctx.rootColumn (d + 1) (children[a]'(by omega)) p :=
            fun a ha => runItemT_order ctx (d + 1) _ _ (hall a (by omega) ha)
              (hinvc _ (List.getElem_mem _))
          refine ⟨?_, ?_⟩
          · rw [List.pairwise_flatten]
            constructor
            · intro l hl
              obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hl
              exact (hIH a ha).1
            · rw [List.pairwise_iff_getElem]
              intro a b ha hb hab p hp q hq
              have hs := List.pairwise_iff_getElem.mp hsep a b (by omega) (by omega) hab
              exact sep_rel hs ((hIH a ha).2 p hp) ((hIH b hb).2 q hq)
          · intro p hp
            obtain ⟨l, hl, hpl⟩ := List.mem_flatten.mp hp
            obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hl
            exact hup _ (List.getElem_mem _) p ((hIH a ha).2 p hpl)

/-- The first items are ordered: every row of an earlier region is below every row of a
later one. -/
theorem lowerItems_sep (τ : Row) :
    (lowerItems τ).Pairwise (fun a b => ∀ r r', inRegion a.1 a.2.source r = true →
      inRegion b.1 b.2.source r' = true → r < r') := by
  unfold lowerItems
  rw [List.pairwise_flatMap]
  constructor
  · intro k _
    rw [List.pairwise_map]
    refine List.pairwise_lt_range.imp fun {j j'} hjj => ?_
    intro r r' hr hr'
    exact slot_rows_lt hr hr' hjj
  · rw [List.pairwise_reverse]
    refine List.pairwise_lt_range.imp fun {k' k} hkk => ?_
    intro x hx y hy r r' hr hr'
    simp only [List.mem_map, List.mem_range] at hx hy
    obtain ⟨j, hj, rfl⟩ := hx
    obtain ⟨j', _, rfl⟩ := hy
    obtain ⟨hS, hd⟩ := Recon.RowLaw.inRegion_slot_iff.mp hr
    obtain ⟨hS', _⟩ := Recon.RowLaw.inRegion_slot_iff.mp hr'
    refine Row.lt_iff.mpr ⟨k, ?_, ?_⟩
    · intro q hq
      rw [Recon.RowLaw.inRegion_iff'.mp hS q (by omega),
        Recon.RowLaw.inRegion_iff'.mp hS' q (by omega)]
    · rw [hd, Recon.RowLaw.inRegion_iff'.mp hS' k (by omega)]
      exact hj

theorem lowerItems_clean (τ : Row) : ∀ p ∈ lowerItems τ, p.2.clean = none := by
  intro p hp
  simp only [lowerItems, List.mem_flatMap, List.mem_map] at hp
  obtain ⟨_, _, _, _, rfl⟩ := hp
  rfl

/-- **The lower part of a column is in origin-row order.** -/
theorem lowerT_order {ctx : Context} {τ : Row} {lower : List (Emit × Origin)}
    (h : lowerT ctx τ = .ok lower) : lower.Pairwise (SrcRel ctx.source) := by
  unfold lowerT at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i outs houts
    cases h
    obtain ⟨hlen, hall⟩ := mapM_except_spec _ _ _ houts
    have hIH : ∀ a (ha : a < outs.length), outs[a].Pairwise (SrcRel ctx.source) ∧
        ∀ p ∈ outs[a], EmitOK ctx.source ctx.rootColumn ((lowerItems τ)[a]'(by omega)).1
          ((lowerItems τ)[a]'(by omega)).2 p := by
      intro a ha
      refine runItemT_order ctx _ _ _ (hall a (by omega) ha) ?_
      intro C hC
      rw [lowerItems_clean τ _ (List.getElem_mem _)] at hC
      cases hC
    rw [List.pairwise_flatten]
    constructor
    · intro l hl
      obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hl
      exact (hIH a ha).1
    · rw [List.pairwise_iff_getElem]
      intro a b ha hb hab p hp q hq cp cq hcp hcq
      obtain ⟨_, c, hc, hreg, _⟩ := (hIH a ha).2 p hp
      obtain ⟨_, c', hc', hreg', _⟩ := (hIH b hb).2 q hq
      rw [hcp] at hc; cases hc
      rw [hcq] at hc'; cases hc'
      exact Or.inl (List.pairwise_iff_getElem.mp (lowerItems_sep τ) a b (by omega) (by omega) hab
        _ _ hreg hreg')

/-- **A column is in origin-row order** (lower part, then the upper part bottom to top). -/
theorem emitsT_order {ctx : Context} {τ : Row} {es : List (Emit × Origin)}
    (hV : MountainValid ctx.source) (h : emitsT ctx τ = .ok es) :
    es.Pairwise (SrcRel ctx.source) := by
  have hbelow := emitsT_lower_below h
  unfold emitsT at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i lower hlower
    split at h
    · cases h
    · rename_i us hus
      cases h
      have hlo := lowerT_order hlower
      -- the upper part
      unfold upperT at hus
      obtain ⟨hlen, hall⟩ := mapM_except_spec _ _ _ hus
      generalize hN : realNodes ctx.source (upperColumn ctx) = N at hus hall hlen
      have hsrc : ∀ a (ha : a < us.length), ∃ ha' : a < (N.filter
          (fun p : Ref × Cell => decide (τ ≤ official p.2.row))).length,
          us[a].2 = .upper ((N.filter (fun p : Ref × Cell => decide (τ ≤ official p.2.row)))[a]'ha').1 := by
        intro a ha
        refine ⟨by omega, ?_⟩
        have := hall a (by omega) ha
        simp only [bind, Except.bind, pure, Except.pure] at this
        split at this
        · cases this
        · rw [← Except.ok.inj this]
      have hpw : (N.filter (fun p : Ref × Cell => decide (τ ≤ official p.2.row))).Pairwise
          (fun p q => p.1.index < q.1.index) := by
        rw [← hN]
        exact List.Pairwise.filter _ (Recon.realNodes_pairwise ctx.source (upperColumn ctx))
      have hmemN : ∀ a (ha : a < (N.filter (fun p : Ref × Cell => decide (τ ≤ official p.2.row))).length),
          (N.filter (fun p : Ref × Cell => decide (τ ≤ official p.2.row)))[a] ∈
            realNodes ctx.source (upperColumn ctx) ∧
          τ ≤ official ((N.filter (fun p : Ref × Cell => decide (τ ≤ official p.2.row)))[a]).2.row := by
        intro a ha
        have hm := List.getElem_mem ha
        rw [List.mem_filter] at hm
        refine ⟨by rw [hN]; exact hm.1, by simpa using hm.2⟩
      rw [List.pairwise_append]
      refine ⟨hlo, ?_, ?_⟩
      · -- upper part: strictly increasing rows
        rw [List.pairwise_iff_getElem]
        intro a b ha hb hab cp cq hcp hcq
        left
        obtain ⟨ha', hsa⟩ := hsrc a ha
        obtain ⟨hb', hsb⟩ := hsrc b hb
        rw [hsa] at hcp
        rw [hsb] at hcq
        simp only [Origin.src] at hcp hcq
        have hidx := List.pairwise_iff_getElem.mp hpw a b ha' hb' hab
        obtain ⟨hma, _⟩ := hmemN a ha'
        obtain ⟨hmb, _⟩ := hmemN b hb'
        obtain ⟨hca, hia, _⟩ := mem_realNodes hma
        obtain ⟨hcb, hib, _⟩ := mem_realNodes hmb
        -- rows strictly increase with the index in a column
        have hlt : cp.row < cq.row := by
          by_contra hn
          push Not at hn
          have := index_le_of_row_le hV (by rw [hca, hcb]) hcq hcp hn
          omega
        exact Recon.official_strictMono (one_le_row hV hcp hia) hlt
      · intro p hp q hq cp cq hcp hcq
        left
        obtain ⟨cv, hcv, hlt⟩ := hbelow p (List.mem_append_left _ hp) (by
          have := List.mem_append_left us hp
          obtain ⟨b, hb, rfl⟩ := List.getElem_of_mem hq
          -- lower emits are not upper
          unfold lowerT at hlower
          simp only [bind, Except.bind, pure, Except.pure] at hlower
          split at hlower
          · cases hlower
          · rename_i outs houts
            cases hlower
            obtain ⟨out, hout, hpo⟩ := List.mem_flatten.mp hp
            obtain ⟨c, _, hc⟩ := mem_of_mapM houts hout
            exact runItemT_not_upper ctx c.1 c.2 out hc p hpo)
        rw [hcp] at hcv; cases hcv
        obtain ⟨b, hb, rfl⟩ := List.getElem_of_mem hq
        obtain ⟨hb', hsb⟩ := hsrc b hb
        rw [hsb] at hcq
        simp only [Origin.src] at hcq
        obtain ⟨hmb, hτ⟩ := hmemN b hb'
        obtain ⟨_, _, hcell⟩ := mem_realNodes hmb
        rw [hcq] at hcell; cases hcell
        exact lt_of_lt_of_le hlt hτ

/-! ### `CopyMono` and `PlainOnce` -/

/-- **`CopyMono` holds.** -/
theorem copyMono_holds : CopyMono := by
  intro s n D M out ρ R col t hS i hi0 hi y es hcy hyx hes k k' hk hk' hkk c c' hc hc'
  have hV := build_valid_of_success hS.splice.build
  have hord := emitsT_order (ctx := ctxAt M R y i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 (y + (ρ.x0 - ρ.cr) * i))
    hV hes
  rcases Nat.lt_or_eq_of_le hkk with hlt | heq
  · have hrel := List.pairwise_iff_getElem.mp hord k k' hk hk' hlt c c' hc hc'
    have hofs : official c.row ≤ official c'.row := by
      rcases hrel with h1 | ⟨h1, _⟩
      · exact le_of_lt h1
      · exact le_of_eq h1
    obtain ⟨_, hidx', _⟩ := src_inner hyx hes k' hk'
    by_contra hn
    push Not at hn
    exact absurd hofs (not_le.mpr (Recon.official_strictMono (one_le_row hV hc' hidx') hn))
  · subst heq
    rw [hc] at hc'
    cases hc'
    exact le_refl _

/-- **`PlainOnce` holds.** -/
theorem plainOnce_holds : PlainOnce := by
  intro s n D M out ρ R col t hS i hi0 hi y es hcy hyx hes j hj m hm k hk hkm
  have hV := build_valid_of_success hS.splice.build
  have hord := emitsT_order (ctx := ctxAt M R y i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 (y + (ρ.x0 - ρ.cr) * i))
    hV hes
  obtain ⟨_, _, c, hc⟩ := src_inner hyx hes j hj
  have hck : cell? M es[k].2.src = some c := by rw [hkm, ← hc, hm]; rfl
  have hpl : isPlainO es[j].2 = true := by rw [hm]; rfl
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · rcases List.pairwise_iff_getElem.mp hord k j hk hj hlt c c hck hc with h1 | ⟨_, _, h2⟩
    · exact lt_irrefl _ h1
    · exact not_plain_and_clean _ hpl h2
  · rcases List.pairwise_iff_getElem.mp hord j k hj hk hlt c c hc hck with h1 | ⟨_, h2, _⟩
    · exact lt_irrefl _ h1
    · exact not_plain_and_clean _ hpl h2

/-- **`StepInner` without the two statements proved here.** -/
theorem stepInner_of_rest (hB : CopyEmitted) (hC2 : CopyFirst) (hLeg : LegLookup)
    (hBump : BumpCopyLower) (hCN : CleanNext) (hCL : CleanLookup) (hCP : CleanParent) :
    StepInner :=
  stepInner_of_profile hB copyMono_holds hC2 plainOnce_holds hLeg hBump hCN hCL hCP

end OmegaY.Official.Classification.Proofs.ChainCorr.Inner

#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.Inner.stepInner_of_parts
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.Inner.wellFounded_of_local

#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.Inner.nextCopy_of_plain
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.Inner.jumpCopy_of_bumpCopy
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.Inner.bumpCopy_of_lower
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.Inner.stepInner_of_local
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.Inner.stepInner_of_lookups
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.Inner.nextCopyPlain_of_profile
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.Inner.stepInner_of_profile
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.Inner.copyMono_holds
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.Inner.plainOnce_holds
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.Inner.stepInner_of_rest
