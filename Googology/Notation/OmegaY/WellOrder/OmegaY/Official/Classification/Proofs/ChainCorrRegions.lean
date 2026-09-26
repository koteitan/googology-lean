/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/ChainCorrRegions.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.KeyRegions
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.ControlDominates
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.ChainCorrCore

set_option backward.do.legacy false

/-!
# Five region lemmas from a chain correspondence

This file applies the simulation theorem of `ChainCorrCore.lean` to the expansion. It
proves the five region lemmas whose origin is not a gap copy of the root row
(`RegionUpper`, `RegionPlainBoundary`, `RegionPlainInner`, `RegionCleanBoundary`,
`RegionCleanInner`) from five open statements about the expansion
(`keyLeRegion_of_chains`, `region*_of_chains`), and well-foundedness from these five
statements, the reconstruction and the two gap-copy regions (`wellFounded_of_chains`).

## The correspondence

Fix a block `i ≥ 1`, `w = x₀ - cr` and `φ = mapColumn cr (w·i)`.

* `CopyNode i v m`: `v` is the node `(y + w·i, j + 1)` of an inner column of block `i`
  (`cr < y < x₀`) whose emitted origin (`Trace.lean`) is `m`, and the origin is not a
  gap copy (`b = 1`) unless `m` has no raw parent.
* `StepInner`: from a `CopyNode` pair `(v, m)`, every step `m → m'` of the scale-`k`
  chain of `M(s)` is matched by the scale-`k` chain of the output from `v` (`Next`):
  it reaches `m'` itself when `m'` is left of `cr`; it reaches a node `v'` of the
  boundary column `cr + w·i` whose chain reaches the next node `m''` when `m'` is in
  the root column; it reaches a `CopyNode` of `m'` when `m'` is right of `cr`.

The naive correspondence (the root of `v` is the image of the root of its origin) fails
at the boundary columns `x₀ + w·b`: their lower part is the copy of the lower part of the
column `x₀`, but their upper part is the upper part of the root column `cr`, so the top
node of the lower part has a raw parent that the corresponding node of `x₀` does not have.
`Next` therefore never asks for a node of the column `cr + w·i` to be a copy of a node of
`M(s)`: it asks only that its chain reach the next node `m''` of the chain of `M(s)`, which
is left of `cr`, where the two mountains agree. Inside a block the naive correspondence
holds for every node that is not a gap copy (tested on all nodes of inner columns).

## The starting point

For a node `u = (X, j + 1)` of a region, with origin `o` (a node of `M(s)`), let `l` be
the leg of `o`, `pa` the highest node of the column `l` at or below the row of `o`, and
`pe` the highest node of the output leg column `φ(l)` at or below the row of `u`
(the parents of the key templates of the two leg atoms). The output leg column is
`φ(l)` (`leg_image`, proved). The key bound `keyLe_keyAt_of_scale` needs

* `StartLeg`: `l ≥ cr` (the leg of an origin below `τ` is at or right of the root);
* `StartJump`: `jump(row u, row pe) ≤ jump(row o, row pa)`;
* `StartCopy`: for `l > cr`, `CopyNode i pe pa`;
* `StartRoot`: for `l = cr`, the chain of `pe` reaches the next node of the chain of
  `pa` at every scale `k ≥ jump(row o, row pa)`.

## Numerical tests

`reference/official/chain-corr.cjs` tests the five statements, with the rule of
`omegay-trace.cjs` (counts: node-scale pairs for `StepInner`, nodes otherwise).

| sample | expansions | `StepInner` | `StartCopy` | `StartRoot` | `StartJump` | `StartLeg` | failures |
|---|---:|---:|---:|---:|---:|---:|---:|
| standard S1–S3, S6, `n = 1,2,3` | 39090 | 1826376 | 402654 | 426954 | 829608 | 1628868 | 0 |
| legal, length ≤ 6, entries ≤ 6 | 23325 | 710304 | 70725 | 185304 | 256029 | 371948 | 0 |
| legal, length ≤ 5, entries ≤ 8 | 12285 | 586128 | 37146 | 132336 | 169482 | 564832 | 0 |
| random legal (`--random 20000,10,10,7`) | 37926 | 3312834 | 210480 | 532794 | 743274 | 4343082 | 0 |

## Towards `StepInner` (numerical, `chain-corr.cjs --steps`)

* From a plain or upper node `v` with origin `m`, one step of the chain of `M(s)` is one
  step of the output chain (1469 k node-scale pairs, all one step). The node above `v`
  exists exactly when the node `m⁺` above `m` exists, its origin is `m⁺`, and the jump of
  the step is the same. So `v` and `m` read the leg column `φ(leg m⁺)` and `leg m⁺` below
  the rows of `v⁺` and `m⁺`: the same lookup as `StartCopy` / `StartRoot`, with `<`.
* From a clean copy `v` of the root-row node `m = (y, C)` (`b = 0`), the output chain may
  take several steps (up to 7 in the samples) through other clean copies of the root row
  in the columns of the generation chain `y → leg(y, C) → …` (notes/03 §2.4, case 4),
  while `M(s)` jumps directly to the raw parent of `m`.

The two gap-copy regions (`RegionCutBoundary`, `RegionCutInner`) are left out: there the
chain of `pe` loses the chain of `pa` at small scales, and the key is only
lexicographically below (`keylerest-regions.cjs`); they need a strict entry at a higher
scale, not the entrywise bound of `keyLe_keyAt_of_scale`.
-/

namespace OmegaY.Official.Classification.Proofs.ChainCorr

open Canonical Reserve Official Descent Classification Proofs

/-- A gap copy of the root row (`b = 1`). -/
def cutOrigin : Origin → Bool
  | .clean _ true => true
  | _ => false

/-- `v` is the node of an inner column `y + w·i` of block `i` whose origin is `m`; the
origin is not a gap copy unless `m` has no raw parent. -/
def CopyNode (M R : Mountain) (n cr x0 : Nat) (τ : Row) (i : Nat) (v m : Ref) : Prop :=
  ∃ y es j, cr < y ∧ y < x0 ∧ y ∈ blockColumns cr x0 n i ∧ v.column = y + (x0 - cr) * i ∧
    v.index = j + 1 ∧ emitsT (ctxAt M R y i cr (x0 - cr) x0 v.column) τ = .ok es ∧
    ∃ hj : j < es.length, es[j].2.src = m ∧ (cutOrigin es[j].2 = false ∨ rawParent M m = none)

theorem copyNode_column {M R : Mountain} {n cr x0 : Nat} {τ : Row} {i : Nat} {v m : Ref}
    (h : CopyNode M R n cr x0 τ i v m) :
    v.column = mapColumn cr ((x0 - cr) * i) m.column := by
  obtain ⟨y, es, j, hcy, hyx, _, hv, _, hes, hj, hsrc, _⟩ := h
  obtain ⟨hcol, _⟩ := emitsT_good hes es[j] (List.getElem_mem hj)
  have hm : m.column = y := by
    rw [← hsrc, hcol]
    have hne : ¬ y = x0 := by omega
    split
    · simp [upperColumn, ctxAt, hne]
    · simp [ctxAt]
  rw [hm, mapColumn_of_ge (by omega), hv]

/-- **The chain correspondence** (open): one step of the chain of `M(s)` from the origin
of a copied node is matched by the chain of the output from the node. -/
def StepInner : Prop :=
  ∀ s n D M out ρ R (col : Column) (t : Cell), SpliceCase s n D M out ρ → DegreeOK s D →
    Official.expandDiagram s n = .ok R → Canonical.build out = .ok R →
    M[M.size - 1]? = some col → col.back? = some t →
    ∀ i, 0 < i → i < n + 1 → ∀ v m, CopyNode M R n ρ.cr ρ.x0 (official t.row) i v m →
      ∀ k m', MStep M k m m' →
        Next R M k ρ.cr ((ρ.x0 - ρ.cr) * i) (CopyNode M R n ρ.cr ρ.x0 (official t.row) i) v m'

/-- A node `(X, j+1)` of a copied column `X = x + w·i` with `i ≥ 1` and its emits: the
hypotheses of `KeyLeRegion` before the atoms. -/
structure Site (s : List Nat) (n D : Nat) (M : Mountain) (out : List Nat) (ρ : Root)
    (R : Mountain) (t : Cell) (X x i : Nat) (es : List (Emit × Origin)) : Prop where
  splice : SpliceCase s n D M out ρ
  deg : DegreeOK s D
  run : Official.expandDiagram s n = .ok R
  canon : Canonical.build out = .ok R
  last : ∃ col : Column, M[M.size - 1]? = some col ∧ col.back? = some t
  X0 : ρ.x0 ≤ X
  XR : X < R.size
  Xeq : X = x + (ρ.x0 - ρ.cr) * i
  iLt : i < n + 1
  xMem : x ∈ blockColumns ρ.cr ρ.x0 n i
  iPos : 0 < i
  copy : ∃ c, R[X]? = some c ∧
    copyColumn (ctxAt M R x i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 X) (official t.row) = .ok c
  emits : emitsT (ctxAt M R x i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 X) (official t.row) = .ok es

/-- The legs of a node `(X, j+1)` and of its origin `o`, and the highest nodes of the leg
columns at or below the rows (the parents of the key templates of the two leg atoms). -/
structure Legs (M R : Mountain) (X j : Nat) (o : Origin) (cu cv : Cell) (ref l pe pa : Ref)
    (cpe cpa : Cell) : Prop where
  hcu : cell? R ⟨X, j + 1⟩ = some cu
  href : cu.left = some ref
  hcv : cell? M o.src = some cv
  hl : cv.left = some l
  hpe : highestAtMost R ref.column cu.row = some pe
  hpa : highestAtMost M l.column cv.row = some pa
  hcpe : cell? R pe = some cpe
  hcpa : cell? M pa = some cpa

/-- (open) The leg of an origin that is not a gap copy is at or right of `cr` (for the
upper part this is the case `KeyLeRest` asks about). -/
def StartLeg : Prop :=
  ∀ s n D M out ρ R t X x i es, Site s n D M out ρ R t X x i es →
    ∀ j (hj : j < es.length), cutOrigin es[j].2 = false →
    ∀ cu cv ref l pe pa cpe cpa, Legs M R X j es[j].2 cu cv ref l pe pa cpe cpa →
      ¬ (es[j].2.isUpper = true ∧ l.column < ρ.cr) → ρ.cr ≤ l.column

/-- (open) The jump of the output key template is at most the jump of the origin's. -/
def StartJump : Prop :=
  ∀ s n D M out ρ R t X x i es, Site s n D M out ρ R t X x i es →
    ∀ j (hj : j < es.length), cutOrigin es[j].2 = false →
    ∀ cu cv ref l pe pa cpe cpa, Legs M R X j es[j].2 cu cv ref l pe pa cpe cpa →
      ¬ (es[j].2.isUpper = true ∧ l.column < ρ.cr) →
      Row.jump cu.row cpe.row ≤ Row.jump cv.row cpa.row

/-- (open) For a leg right of `cr`, the parent of the output key template is the copy of
the parent of the origin's key template. -/
def StartCopy : Prop :=
  ∀ s n D M out ρ R t X x i es, Site s n D M out ρ R t X x i es →
    ∀ j (hj : j < es.length), cutOrigin es[j].2 = false →
    ∀ cu cv ref l pe pa cpe cpa, Legs M R X j es[j].2 cu cv ref l pe pa cpe cpa →
      ρ.cr < l.column → CopyNode M R n ρ.cr ρ.x0 (official t.row) i pe pa

/-- (open) For the leg `cr`, the chain of the output parent reaches the next node of the
chain of the origin's parent, at every scale where the origin's key has an entry. -/
def StartRoot : Prop :=
  ∀ s n D M out ρ R t X x i es, Site s n D M out ρ R t X x i es →
    ∀ j (hj : j < es.length), cutOrigin es[j].2 = false →
    ∀ cu cv ref l pe pa cpe cpa, Legs M R X j es[j].2 cu cv ref l pe pa cpe cpa →
      l.column = ρ.cr → ∀ k m'', Row.jump cv.row cpa.row ≤ k → MStep M k pa m'' →
        ScaleReach R k pe m''

/-! ## The output leg column is the image of the origin's leg column -/

theorem mem_blockColumns_pos {cr x0 n i x : Nat} (hx : x ∈ blockColumns cr x0 n i)
    (hi : 0 < i) : cr < x ∧ x ≤ x0 := by
  unfold blockColumns at hx
  rw [if_neg (by omega)] at hx
  simp only [List.mem_range'_1] at hx
  split at hx <;> omega

theorem leg_image {s : List Nat} {n D : Nat} {M : Mountain} {out : List Nat} {ρ : Root}
    {R : Mountain} {t : Cell} {X x i : Nat} {es : List (Emit × Origin)}
    (hS : Site s n D M out ρ R t X x i es) {j : Nat} (hj : j < es.length)
    {cu cv : Cell} {ref l pe pa : Ref} {cpe cpa : Cell}
    (hL : Legs M R X j es[j].2 cu cv ref l pe pa cpe cpa) :
    ref.column = mapColumn ρ.cr ((ρ.x0 - ρ.cr) * i) l.column := by
  have hV := build_valid_of_success hS.splice.build
  obtain ⟨_, _, _, _, _, hcrx, _⟩ := spliceCase_data hS.splice hS.run
  obtain ⟨hcx, hxx⟩ := mem_blockColumns_pos hS.xMem hS.iPos
  obtain ⟨c, hRX, hcopy⟩ := hS.copy
  obtain ⟨es', hes', hasm⟩ := copyColumn_emitsT hcopy
  have hee : es' = es := Except.ok.inj (hes'.symm.trans hS.emits)
  subst hee
  obtain ⟨_, hcells⟩ := assemble_spec hasm
  obtain ⟨cell, hcellX, _, ref', hrefl, hrefc⟩ := hcells j (by simpa using hj)
  simp only [List.getElem_map] at hrefc
  -- the assembled cell is `cu`
  have hcu' : cell? R ⟨X, j + 1⟩ = some cell := by
    simp only [cell?, hRX, Option.bind_eq_bind, Option.bind_some]
    exact hcellX
  have hcc : cu = cell := Option.some.inj (hL.hcu.symm.trans hcu')
  subst hcc
  have hrr : ref = ref' := Option.some.inj (hL.href.symm.trans hrefl)
  subst hrr
  rw [hrefc]
  obtain ⟨hvcol, hvidx, cv', hcv', hleft⟩ := emitsT_good hS.emits es'[j] (List.getElem_mem hj)
  have hcvv : cv' = cv := Option.some.inj (hcv'.symm.trans hL.hcv)
  subst hcvv
  rcases hleft with ⟨l', hl', hlc⟩ | ⟨hnone, h0, hlow⟩
  · have hll : l' = l := Option.some.inj (hl'.symm.trans hL.hl)
    subst hll
    simp only [legColumn, hlc, ctxAt]
    unfold mapColumn
    by_cases h : ρ.cr ≤ l'.column
    · have h' : ¬ l'.column < ρ.cr := by omega
      simp [h, h']
    · have h' : l'.column < ρ.cr := by omega
      simp [h, h']
  · -- a node of the bottom row: its leg is the phantom of the previous column
    rw [hlow] at hvcol
    simp only [Bool.false_eq_true, if_false, ctxAt] at hvcol
    have hi1 := index_one_of_official_zero hV hL.hcv hvidx h0
    have hbl := bottom_left hS.splice.build hL.hcv hi1 (by omega)
    have hll : l = ⟨es'[j].2.src.column - 1, 0⟩ := Option.some.inj (hL.hl.symm.trans hbl)
    rw [hll]
    simp only [legColumn, hnone, ctxAt, Array.size_extract]
    rw [hvcol, mapColumn_of_ge (by omega)]
    have h1 := hS.XR
    have h2 := hS.Xeq
    omega

/-! ## The reduction -/

/-- **A region lemma from the chain correspondence**, for any selection of origins that
are not gap copies. -/
theorem keyLeRegion_of_chains (sel : Nat → Nat → Origin → Prop)
    (hsel : ∀ x x0 o, sel x x0 o → cutOrigin o = false)
    (hStep : StepInner) (hLeg : StartLeg) (hJump : StartJump) (hCopy : StartCopy)
    (hRoot : StartRoot) : KeyLeRegion sel := by
  intro s n D M out ρ R col t hc hdeg hRun hRb hcol ht X x i hX0 hXR hXeq hi hx hipos hcopy es
    hes j hj e a he ha hnot hs _
  have hS : Site s n D M out ρ R t X x i es :=
    ⟨hc, hdeg, hRun, hRb, ⟨col, hcol, ht⟩, hX0, hXR, hXeq, hi, hx, hipos,
      ⟨R[X], Array.getElem?_eq_getElem hXR, hcopy⟩, hes⟩
  have hnc := hsel _ _ _ hs
  obtain ⟨_, _, _, _, _, hcrx, hinv⟩ := spliceCase_data hc hRun
  have hA : AgreeBelow M R ρ.x0 := hinv.1
  -- unfold the two leg atoms
  unfold legAtom? at he ha
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at he ha
  obtain ⟨cu, hcu, ref, href, pe, hpe, rfl⟩ := he
  obtain ⟨cv, hcv, l, hl, pa, hpa, rfl⟩ := ha
  obtain ⟨hpec, cpe, hcpe⟩ := highestAtMost_cell hpe
  obtain ⟨hpac, cpa, hcpa⟩ := highestAtMost_cell hpa
  have hL : Legs M R X j es[j].2 cu cv ref l pe pa cpe cpa :=
    ⟨hcu, href, hcv, hl, hpe, hpa, hcpe, hcpa⟩
  have hnot' : ¬ (es[j].2.isUpper = true ∧ l.column < ρ.cr) := hnot
  have hcrl := hLeg s n D M out ρ R t X x i es hS j hj hnc cu cv ref l pe pa cpe cpa hL hnot'
  have hjump := hJump s n D M out ρ R t X x i es hS j hj hnc cu cv ref l pe pa cpe cpa hL hnot'
  have himg := leg_image hS hj hL
  apply keyLe_keyAt_of_scale hcpe hcpa hjump
  intro k hk _
  show (root R k pe).column ≤ mapColumn ρ.cr ((ρ.x0 - ρ.cr) * i) (root M k pa).column
  rcases Nat.lt_or_eq_of_le hcrl with hlt | heq
  · -- a leg right of the root column: the simulation
    have hcp := hCopy s n D M out ρ R t X x i es hS j hj hnc cu cv ref l pe pa cpe cpa hL hlt
    refine bound_of_sim hA (le_of_lt hcrx) (CopyNode M R n ρ.cr ρ.x0 (official t.row) i)
      (fun v m h => le_of_eq (copyNode_column h)) ?_ pe pa hcp
    intro v m m' hvm hst
    exact hStep s n D M out ρ R col t hc hdeg hRun hRb hcol ht i hipos hi v m hvm k m' hst
  · -- the leg is the root column
    have hpe' : pe.column ≤ ρ.cr + (ρ.x0 - ρ.cr) * i := by
      rw [hpec, himg, ← heq, mapColumn_of_ge (le_refl _)]
    exact bound_root hA (le_of_lt hcrx) (by rw [hpac]; exact heq.symm) hpe'
      (fun m'' hst => hRoot s n D M out ρ R t X x i es hS j hj hnc cu cv ref l pe pa cpe cpa hL
        heq.symm k m'' hk hst)

theorem regionUpper_of_chains (hStep : StepInner) (hLeg : StartLeg) (hJump : StartJump)
    (hCopy : StartCopy) (hRoot : StartRoot) : RegionUpper :=
  keyLeRegion_of_chains _ (fun _ _ o h => by cases o <;> simp_all [Origin.isUpper, cutOrigin])
    hStep hLeg hJump hCopy hRoot

theorem regionPlainBoundary_of_chains (hStep : StepInner) (hLeg : StartLeg)
    (hJump : StartJump) (hCopy : StartCopy) (hRoot : StartRoot) : RegionPlainBoundary :=
  keyLeRegion_of_chains _ (fun _ _ o h => by obtain ⟨⟨r, rfl⟩, _⟩ := h; rfl)
    hStep hLeg hJump hCopy hRoot

theorem regionPlainInner_of_chains (hStep : StepInner) (hLeg : StartLeg)
    (hJump : StartJump) (hCopy : StartCopy) (hRoot : StartRoot) : RegionPlainInner :=
  keyLeRegion_of_chains _ (fun _ _ o h => by obtain ⟨⟨r, rfl⟩, _⟩ := h; rfl)
    hStep hLeg hJump hCopy hRoot

theorem regionCleanBoundary_of_chains (hStep : StepInner) (hLeg : StartLeg)
    (hJump : StartJump) (hCopy : StartCopy) (hRoot : StartRoot) : RegionCleanBoundary :=
  keyLeRegion_of_chains _ (fun _ _ o h => by obtain ⟨⟨r, rfl⟩, _⟩ := h; rfl)
    hStep hLeg hJump hCopy hRoot

theorem regionCleanInner_of_chains (hStep : StepInner) (hLeg : StartLeg)
    (hJump : StartJump) (hCopy : StartCopy) (hRoot : StartRoot) : RegionCleanInner :=
  keyLeRegion_of_chains _ (fun _ _ o h => by obtain ⟨⟨r, rfl⟩, _⟩ := h; rfl)
    hStep hLeg hJump hCopy hRoot

/-- **Well-foundedness of the official expansion** from the reconstruction, the chain
correspondence and the two gap-copy regions. -/
theorem wellFounded_of_chains (hrec : Dimension.BlockReconstruction) (hStep : StepInner)
    (hLeg : StartLeg) (hJump : StartJump) (hCopy : StartCopy) (hRoot : StartRoot)
    (hKB : RegionCutBoundary) (hKI : RegionCutInner) : WellFounded Step :=
  wellFounded_of_regions hrec ControlProof.controlDominates
    (regionUpper_of_chains hStep hLeg hJump hCopy hRoot)
    (regionPlainBoundary_of_chains hStep hLeg hJump hCopy hRoot)
    (regionPlainInner_of_chains hStep hLeg hJump hCopy hRoot)
    (regionCleanBoundary_of_chains hStep hLeg hJump hCopy hRoot)
    (regionCleanInner_of_chains hStep hLeg hJump hCopy hRoot) hKB hKI

end OmegaY.Official.Classification.Proofs.ChainCorr

#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.keyLeRegion_of_chains
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.wellFounded_of_chains
