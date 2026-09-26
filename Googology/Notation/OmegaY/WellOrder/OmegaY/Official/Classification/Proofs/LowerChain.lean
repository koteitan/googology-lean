/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/LowerChain.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.ChainSkip
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.RootCut

set_option backward.do.legacy false

/-!
# The chain correspondence in the lower part of copied columns (one shared family)

Two routes need the same fact: in a block `i ≥ 1` of `s[n]`, the chain of stored parents of
the output `R` from a copy of a node `z` of `M = M(s)` follows the chain of `M` from `z`.

* `KeyLeRest` (`Control.KeyLeRest`) follows the scale-`k` chains (steps of jump `≤ k`):
  `keyLeRegion_of_chains`, `keyLeRegion_of_cut` (`ChainCorrRegions.lean`, `ChainCorrCut.lean`)
  and the versions with skips (`ChainSkip.lean`).
* The parent chain of the reconstruction follows the chains of stored parents:
  `CrossUpperSim.CopyStepLow`, `CrossUpperSim.CopyQLower` (`Recon/CrossUpperSim*.lean`), and
  through `CrossUpperSim.cp_chain` and `CrossPlainPos.QStand` also `CrossLexPos`
  (`Recon/CrossPlainBlock0.lean`, `Recon/CrossPlainPosSim.lean`).

This file states the fact **once**, for the diagram `R = expandDiagram s n` (it does not assume
that `R` is the canonical mountain of `s[n]`, which the reconstruction has to prove), and derives
the `KeyLeRest` side from it. `LowerChainRecon.lean` derives the parent-chain side.

Notation: `c_r = col root`, `x₀ = |M| - 1`, `w = x₀ - c_r`, `φ(c) = c` (`c < c_r`),
`c + w·i` (`c ≥ c_r`), `τ` the row of the top `t` of the column `x₀`.

## The relations

* `CopyOf i v m`: `v` is a node of an inner column `y + w·i` (`c_r < y < x₀`) of block `i`
  whose emitted origin (`Trace.lean`) has the source `m` (any kind: plain, clean, gap copy,
  upper).
* `TopNode i v m` (**the top copy**): `CopyOf i v m`, no node above `v` in its column is a copy
  of `m`, and `row v = row m` when `row m ≥ τ`.
* `Rel i v m := CopyNode i v m ∨ TopNode i v m` (`CopyNode`, `ChainCorrRegions.lean`: a copy
  that is not a gap copy, unless `m` has no raw parent).
* `Stand i A a` (the stand-in relation of `CrossUpperSim.Cp`, in `Ref` form, with the chain
  clause at the scale of the step):
  - `col a < c_r`: `A = a`;
  - `col a = c_r`: `col A = c_r + w·i`; if the node `a⁺` above `a` has `row a⁺ ≥ τ`, the node
    `A⁺` above `A` has the row of `a⁺`; if `a` has a raw parent `b`, the scale-`jump(a, b)`
    chain of `R` from `A` reaches `b`;
  - `col a > c_r`: `TopNode i A a`.

## The shared open statements

* `TopStep` (both routes): for a top copy `Z` of `z` and the raw parent `a` of `z`, the raw
  parent `A` of `Z` is one step of the scale-`jump(z, a)` chain of `R` (`MStep`), and
  `Stand i A a`.
* `TopStart` (both routes): for the top copy `u` (in its column `X = x + w·i`, `x` in block
  `i`, the column `x₀ + w·i` included) of its origin `o`, with the leg `l` of `o`,
  `pa = hAM_M(l, row o)` and `pe = hAM_R(φ(l), row u)` (the parents of the key templates of the
  two leg atoms, and the candidates `Q` of `u` and `o`): `Stand i pe pa`.

## The open statements used only by `KeyLeRest`

* `NonTopStep`: from a `CopyNode` pair `(v, m)` where `v` is not the top copy, every step of the
  scale-`k` chain of `M` is matched (`Next`) over `Rel`. (Numerically these `v` are all clean
  copies below a gap copy of the same node.)
* `StartRelNT`, `StartRootNT`: `StartCopy` (with `Rel` for `CopyNode`), `StartRoot` for the
  region nodes that are not top copies.
* `CutStartCopyNT`, `CutStartRootNT`: `CutStartCopy`, `CutStartRoot` for the gap-copy region
  nodes that are not top copies.
* unchanged: `StepCut`, `CutJump` (`ChainCorrCut.lean`); `LeftRow` (from the proved
  `LiftLegRight`) and `StartJumpGe` (from the proved `LegRowMatchInner`).

## Results

* `next_of_stand`, `rel_step`: `TopStep` and `NonTopStep` match every step from a `Rel` pair;
  so the simulation `bound_of_sim` needs no skips.
* `keyLeRegion_of_lower`, `keyLeRegion_of_lowerCut`, `keyLeRest_of_lower`,
  `wellFounded_of_lower`.

## Numerical tests (`reference/official/lower-chain.cjs`, the rule of `omegay-trace.cjs`)

`n = 1, 2, 3`; an input is not expanded for a larger `n` once its output has more than 800
nodes or a column with more than 80 nodes. Counts: `TopStep` top-copy steps (every node of an
inner column of every block with a raw parent), `TopStart` top-copy nodes of the copied
columns, `NonTopStep` (`CopyStepRel` in the script) the `CopyNode` pairs with a raw parent,
each for every scale from the jump up to `D + 2` (in parentheses: pairs that are not top
copies), `StartRelNT` (`StartRel`) region nodes with a leg right of `c_r` (top or not).
No failure anywhere.

| sample | inputs | expansions | `TopStep` | `TopStart` | `NonTopStep` | `StartRelNT` |
|---|---:|---:|---:|---:|---:|---:|
| all of length `≤ 6`, entries `≤ 12` | 248831 | 720307 | 10661368 | 15660881 | 10661368 (1656126) | 3691400 |
| uniform sample, length 6, entries `≤ 12`, with K and B | 33877 | 98010 | 5965687 | 8759585 | 5965687 (918558) | 2084500 |
| random, length `≤ 7`, entries `≤ 40` (28 of 30 chunks) | 2648 | 5610 | 188243 | 236159 | 188243 (14031) | 35000 |
| random, length `≤ 8`, entries `≤ 20` | 2726 | 7119 | 144827 | 198245 | 144827 (17209) | 38747 |
| K: `samples/known-counterexamples.json` | 17 | 51 | 1020 | 1563 | 1020 (246) | 576 |
| B: `samples/legbelowtop-bad64.json` | 64 | 192 | 3066 | 4782 | 3066 (954) | 1140 |

The script also reports that the stronger start `Top(pe, pa)` for every region node is
**false** (e.g. `(1,3,9,11,16,8)[1]`, the clean copy `u = (7, 1)` of `(3, 1)`: `pe` is the
clean copy of `pa = (2, 1)`, below its top copy, a gap copy); this is why the starts of the
nodes that are not top copies use `Rel`. The other statements used here (`StartRoot`,
`StepCut`, `CutJump`, `CutStartCopy`, `CutStartRoot`) have no failure on the large-value
samples of notes/05-large-value-audit.md.
-/

namespace OmegaY.Official.Classification.Proofs.ChainCorr.LowerChain

open Canonical Reserve Official Descent Classification Proofs

/-! ## Definitions -/

/-- The node above a node. -/
def above (r : Ref) : Ref := ⟨r.column, r.index + 1⟩

/-- `v` is a copy of `m` in an inner column of block `i` (any origin kind). -/
def CopyOf (M R : Mountain) (n cr x0 : Nat) (τ : Row) (i : Nat) (v m : Ref) : Prop :=
  ∃ y es j, cr < y ∧ y < x0 ∧ y ∈ blockColumns cr x0 n i ∧ v.column = y + (x0 - cr) * i ∧
    v.index = j + 1 ∧ emitsT (ctxAt M R y i cr (x0 - cr) x0 v.column) τ = .ok es ∧
    ∃ hj : j < es.length, es[j].2.src = m

/-- `v` is the top copy of `m`: a copy with no copy of `m` above it in its column, at the row
of `m` when `m` is in the upper part (`row m ≥ θ`). -/
def TopNode (M R : Mountain) (n cr x0 : Nat) (τ θ : Row) (i : Nat) (v m : Ref) : Prop :=
  CopyOf M R n cr x0 τ i v m ∧
  (∀ v' : Ref, v'.column = v.column → v.index < v'.index → (∃ c, cell? R v' = some c) →
    ¬ CopyOf M R n cr x0 τ i v' m) ∧
  (∀ cm cv, cell? M m = some cm → cell? R v = some cv → θ ≤ cm.row → cv.row = cm.row)

/-- The relation of the simulation: a copy that is not a gap copy, or the top copy. -/
def Rel (M R : Mountain) (n cr x0 : Nat) (τ θ : Row) (i : Nat) (v m : Ref) : Prop :=
  CopyNode M R n cr x0 τ i v m ∨ TopNode M R n cr x0 τ θ i v m

/-- The stand-in relation (the `Ref` form of `CrossUpperSim.Cp`, with the chain clause at the
scale of the step). -/
def Stand (M R : Mountain) (n cr x0 : Nat) (τ θ : Row) (i : Nat) (A a : Ref) : Prop :=
  (a.column < cr → A = a) ∧
  (a.column = cr → A.column = cr + (x0 - cr) * i ∧
    (∀ ca, cell? M (above a) = some ca → θ ≤ ca.row →
      ∃ cA, cell? R (above A) = some cA ∧ cA.row = ca.row) ∧
    (∀ b ca cb, rawParent M a = some b → cell? M a = some ca → cell? M b = some cb →
      ScaleReach R (Row.jump ca.row cb.row) A b)) ∧
  (cr < a.column → TopNode M R n cr x0 τ θ i A a)

/-- The emit `j` of a column is the top copy of its source: no emit above it has the same
source. -/
def IsTopAt (es : List (Emit × Origin)) (j : Nat) : Prop :=
  ∀ j' (hj' : j' < es.length) (hj : j < es.length), j < j' → es[j'].2.src ≠ es[j].2.src

/-! ## The shared open statements -/

/-- **Open (shared).** One step from a top copy: the raw parent `A` of the top copy `Z` of `z`
is one step of the scale-`jump(z, a)` chain of `R`, and it stands for the raw parent `a` of
`z`. -/
def TopStep : Prop :=
  ∀ (s : List Nat) (n : Nat) (R M : Mountain) (t : Cell) (root : Ref) (i : Nat),
    Official.expandDiagram s n = .ok R → Recon.Top s M t root → 0 < i → i ≤ n →
    ∀ Z z, TopNode M R n root.column (M.size - 1) (official t.row) t.row i Z z →
    ∀ a cz ca, rawParent M z = some a → cell? M z = some cz → cell? M a = some ca →
      ∃ A, MStep R (Row.jump cz.row ca.row) Z A ∧
        Stand M R n root.column (M.size - 1) (official t.row) t.row i A a

/-- **Open (shared).** The start from a top copy: for the top copy `u = (x + w·i, j + 1)` of
its origin `o` (with emits `es` of the column), the highest node `pe` of the column `φ(l)` at
or below `row u` stands for the highest node `pa` of the leg column `l` of `o` at or below
`row o`. -/
def TopStart : Prop :=
  ∀ (s : List Nat) (n : Nat) (R M : Mountain) (t : Cell) (root : Ref) (i x : Nat),
    Official.expandDiagram s n = .ok R → Recon.Top s M t root → 0 < i → i ≤ n →
    x ∈ blockColumns root.column (M.size - 1) n i →
    ∀ es, emitsT (ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1)
        (x + (M.size - 1 - root.column) * i)) (official t.row) = .ok es →
    ∀ j (hj : j < es.length), IsTopAt es j →
    ∀ cu cv l pe pa,
      cell? R ⟨x + (M.size - 1 - root.column) * i, j + 1⟩ = some cu →
      cell? M es[j].2.src = some cv → cv.left = some l →
      highestAtMost M l.column cv.row = some pa →
      highestAtMost R (mapColumn root.column ((M.size - 1 - root.column) * i) l.column) cu.row =
        some pe →
      Stand M R n root.column (M.size - 1) (official t.row) t.row i pe pa

/-! ## The open statements used only by `KeyLeRest` -/

/-- **Open.** From a copy pair `(v, m)` that is not a gap copy, where `v` is not the top copy,
every step of the scale-`k` chain of `M` is matched over `Rel`. -/
def NonTopStep : Prop :=
  ∀ (s : List Nat) (n : Nat) (R M : Mountain) (t : Cell) (root : Ref) (i : Nat),
    Official.expandDiagram s n = .ok R → Recon.Top s M t root → 0 < i → i ≤ n →
    ∀ v m, CopyNode M R n root.column (M.size - 1) (official t.row) i v m →
      ¬ TopNode M R n root.column (M.size - 1) (official t.row) t.row i v m →
      ∀ k m', MStep M k m m' →
        Next R M k root.column ((M.size - 1 - root.column) * i)
          (Rel M R n root.column (M.size - 1) (official t.row) t.row i) v m'

/-- **Open.** `StartCopy` (with `Rel`) for the region nodes that are not top copies. -/
def StartRelNT : Prop :=
  ∀ s n D M out ρ R t X x i es, Site s n D M out ρ R t X x i es →
    ∀ j (hj : j < es.length), cutOrigin es[j].2 = false → ¬ IsTopAt es j →
    ∀ cu cv ref l pe pa cpe cpa, Legs M R X j es[j].2 cu cv ref l pe pa cpe cpa →
      ρ.cr < l.column → Rel M R n ρ.cr ρ.x0 (official t.row) t.row i pe pa

/-- **Open.** `StartRoot` for the region nodes that are not top copies. -/
def StartRootNT : Prop :=
  ∀ s n D M out ρ R t X x i es, Site s n D M out ρ R t X x i es →
    ∀ j (hj : j < es.length), cutOrigin es[j].2 = false → ¬ IsTopAt es j →
    ∀ cu cv ref l pe pa cpe cpa, Legs M R X j es[j].2 cu cv ref l pe pa cpe cpa →
      l.column = ρ.cr → ∀ k m'', Row.jump cv.row cpa.row ≤ k → MStep M k pa m'' →
        ScaleReach R k pe m''

/-- **Open.** `CutStartCopy` for the gap-copy region nodes that are not top copies. -/
def CutStartCopyNT : Prop :=
  ∀ s n D M out ρ R t X x i es, Site s n D M out ρ R t X x i es →
    ∀ j (hj : j < es.length), cutOrigin es[j].2 = true → ¬ IsTopAt es j →
    ∀ cu cv ref l pe pa cpe cpa, Legs M R X j es[j].2 cu cv ref l pe pa cpe cpa →
      ρ.cr < l.column → CutNode M R n ρ.cr ρ.x0 (official t.row) i pe pa

/-- **Open.** `CutStartRoot` for the gap-copy region nodes that are not top copies. -/
def CutStartRootNT : Prop :=
  ∀ s n D M out ρ R t X x i es, Site s n D M out ρ R t X x i es →
    ∀ j (hj : j < es.length), cutOrigin es[j].2 = true → ¬ IsTopAt es j →
    ∀ cu cv ref l pe pa cpe cpa, Legs M R X j es[j].2 cu cv ref l pe pa cpe cpa →
      l.column = ρ.cr → ∀ k m'', Row.jump cv.row cpa.row ≤ k → k ≤ D → MStep M k pa m'' →
        ScaleReach R k pe m''

/-! ## The old statements imply the restricted ones -/

theorem startRootNT_of_startRoot (h : StartRoot) : StartRootNT :=
  fun s n D M out ρ R t X x i es hS j hj hc _ cu cv ref l pe pa cpe cpa hL heq =>
    h s n D M out ρ R t X x i es hS j hj hc cu cv ref l pe pa cpe cpa hL heq

theorem cutStartCopyNT_of_cutStartCopy (h : CutStartCopy) : CutStartCopyNT :=
  fun s n D M out ρ R t X x i es hS j hj hc _ cu cv ref l pe pa cpe cpa hL hlt =>
    h s n D M out ρ R t X x i es hS j hj hc cu cv ref l pe pa cpe cpa hL hlt

theorem cutStartRootNT_of_cutStartRoot (h : CutStartRoot) : CutStartRootNT :=
  fun s n D M out ρ R t X x i es hS j hj hc _ cu cv ref l pe pa cpe cpa hL heq =>
    h s n D M out ρ R t X x i es hS j hj hc cu cv ref l pe pa cpe cpa hL heq

theorem startRelNT_of_startCopy (h : StartCopy) : StartRelNT :=
  fun s n D M out ρ R t X x i es hS j hj hc _ cu cv ref l pe pa cpe cpa hL hlt =>
    Or.inl (h s n D M out ρ R t X x i es hS j hj hc cu cv ref l pe pa cpe cpa hL hlt)

/-! ## Generic lemmas -/

theorem MStep.mono {M : Mountain} {k k' : Nat} {p q : Ref} (h : MStep M k p q) (hk : k ≤ k') :
    MStep M k' p q := by
  obtain ⟨hpar, c, cq, hc, hcq, hj, hlt⟩ := h
  exact ⟨hpar, c, cq, hc, hcq, le_trans hj hk, hlt⟩

theorem copyOf_column {M R : Mountain} {n cr x0 : Nat} {τ : Row} {i : Nat} {v m : Ref}
    (h : CopyOf M R n cr x0 τ i v m) :
    v.column = mapColumn cr ((x0 - cr) * i) m.column := by
  obtain ⟨y, es, j, hcy, hyx, _, hv, _, hes, hj, hsrc⟩ := h
  obtain ⟨hcol, _⟩ := emitsT_good hes es[j] (List.getElem_mem hj)
  have hm : m.column = y := by
    rw [← hsrc, hcol]
    have hne : ¬ y = x0 := by omega
    split
    · simp [upperColumn, ctxAt, hne]
    · simp [ctxAt]
  rw [hm, mapColumn_of_ge (by omega), hv]

theorem copyOf_src_column {M R : Mountain} {n cr x0 : Nat} {τ : Row} {i : Nat} {v m : Ref}
    (h : CopyOf M R n cr x0 τ i v m) : cr < m.column ∧ m.column < x0 := by
  obtain ⟨y, es, j, hcy, hyx, _, hv, _, hes, hj, hsrc⟩ := h
  obtain ⟨hcol, _⟩ := emitsT_good hes es[j] (List.getElem_mem hj)
  have hm : m.column = y := by
    rw [← hsrc, hcol]
    have hne : ¬ y = x0 := by omega
    split
    · simp [upperColumn, ctxAt, hne]
    · simp [ctxAt]
  omega

theorem rel_column {M R : Mountain} {n cr x0 : Nat} {τ θ : Row} {i : Nat} {v m : Ref}
    (h : Rel M R n cr x0 τ θ i v m) : v.column ≤ mapColumn cr ((x0 - cr) * i) m.column := by
  rcases h with h | h
  · exact le_of_eq (copyNode_column h)
  · exact le_of_eq (copyOf_column h.1)

/-- **One step to a stand-in node is a matched step.** -/
theorem next_of_stand {R M : Mountain} {n cr x0 : Nat} {τ θ : Row} {i k : Nat} {v A a : Ref}
    (hvA : MStep R k v A) (hS : Stand M R n cr x0 τ θ i A a) :
    Next R M k cr ((x0 - cr) * i) (Rel M R n cr x0 τ θ i) v a := by
  obtain ⟨hlt, heq, hgt⟩ := hS
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [← hlt h]
    exact hvA.reach
  · obtain ⟨hcol, _, hch⟩ := heq h
    refine ⟨A, hvA.reach, le_of_eq hcol, fun m'' hst => ?_⟩
    obtain ⟨hpar, ca, cb, hca, hcb, hj, _⟩ := hst
    exact reach_mono (hch m'' ca cb hpar hca hcb) hj
  · exact ⟨A, hvA.reach, Or.inr (hgt h)⟩

/-- **Every step from a `Rel` pair is matched over `Rel`** (from `TopStep`, `NonTopStep`). -/
theorem rel_step (hTS : TopStep) (hNS : NonTopStep) {s : List Nat} {n : Nat} {R M : Mountain}
    {t : Cell} {root : Ref} {i : Nat} (hrun : Official.expandDiagram s n = .ok R)
    (hTop : Recon.Top s M t root) (hi0 : 0 < i) (hi : i ≤ n) {k : Nat} {v m m' : Ref}
    (h : Rel M R n root.column (M.size - 1) (official t.row) t.row i v m)
    (hst : MStep M k m m') :
    Next R M k root.column ((M.size - 1 - root.column) * i)
      (Rel M R n root.column (M.size - 1) (official t.row) t.row i) v m' := by
  classical
  by_cases htop : TopNode M R n root.column (M.size - 1) (official t.row) t.row i v m
  · obtain ⟨hpar, c, cq, hc, hcq, hj, _⟩ := hst
    obtain ⟨A, hvA, hS⟩ := hTS s n R M t root i hrun hTop hi0 hi v m htop m' c cq hpar hc hcq
    exact next_of_stand (MStep.mono hvA hj) hS
  · rcases h with h | h
    · exact hNS s n R M t root i hrun hTop hi0 hi v m h htop k m' hst
    · exact absurd h htop

/-! ## The root data of a splice case -/

/-- The data of `Recon.Top` from a splice case. -/
theorem top_of_splice {s out : List Nat} {n D : Nat} {M : Mountain} {ρ : Root}
    (hc : SpliceCase s n D M out ρ) {R : Mountain} (hR : Official.expandDiagram s n = .ok R)
    {col : Column} {t : Cell} (hcol : M[M.size - 1]? = some col) (ht : col.back? = some t) :
    ∃ root, Recon.Top s M t root ∧ ρ.cr = root.column ∧ ρ.x0 = M.size - 1 := by
  obtain ⟨M', hM', hcases⟩ := expandDiagram_spec hR
  rw [hc.build] at hM'
  cases hM'
  have hV := build_valid_of_success hc.build
  have hsz := build_size hc.build
  have hx := (root?_spec hV hc.root).1
  rcases hcases with ⟨he, _⟩ | ⟨col', t', hcol', ht', hbr⟩
  · have : s = [] := List.isEmpty_iff.mp he
    subst this
    simp only [List.length_nil] at hsz
    omega
  · have hcc : col = col' := Option.some.inj (hcol.symm.trans hcol')
    subst hcc
    have htt : t = t' := Option.some.inj (ht.symm.trans ht')
    subst htt
    rcases hbr with ⟨hdel, _⟩ | ⟨hsp, root, htl, hlt, _, _⟩
    · rcases hdel with h0 | h0
      · have hr := hc.root
        rw [root?_none_of_official_zero hV D hcol ht h0] at hr
        cases hr
      · exact absurd h0 hc.copies
    · obtain ⟨ρ', hr', hx0, hcr'⟩ :=
        root?_of_official_ne_zero hV D hcol ht (fun h0 => hsp (Or.inl h0)) htl
      have hρ : ρ' = ρ := Option.some.inj (hr'.symm.trans hc.root)
      subst hρ
      refine ⟨root, ⟨hc.build, ?_, fun h0 => hsp (Or.inl h0), htl, hlt⟩, hcr', hx0⟩
      rw [hcol]
      exact ht

/-! ## The region lemmas -/

/-- The step and the top start of a region node, in the notation of `ρ`. -/
theorem region_tools (hTS : TopStep) (hNS : NonTopStep) (hTSt : TopStart)
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
  · rw [hcr, hx0] at h ⊢
    exact rel_step hTS hNS hS.run hTop hS.iPos hi h hst
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
theorem keyLeRegion_of_lower (sel : Nat → Nat → Origin → Prop)
    (hsel : ∀ x x0 o, sel x x0 o → cutOrigin o = false)
    (hTS : TopStep) (hNS : NonTopStep) (hTSt : TopStart) (hRel : StartRelNT)
    (hRoot : StartRootNT) (hLeft : Skip.LeftStart) (hJump : Skip.StartJumpGe) :
    KeyLeRegion sel := by
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
  obtain ⟨hstep, hstand⟩ := region_tools hTS hNS hTSt hS hj hL
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
theorem keyLeRegion_of_lowerCut (sel : Nat → Nat → Origin → Prop)
    (hsel : ∀ x x0 o, sel x x0 o → cutOrigin o = true)
    (hTS : TopStep) (hNS : NonTopStep) (hTSt : TopStart) (hCut : StepCut) (hJump : CutJump)
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
  obtain ⟨hstep, hstand⟩ := region_tools hTS hNS hTSt hS hj hL
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

/-- **`Control.KeyLeRest` from the shared family** (`TopStep`, `TopStart`) and the statements
used only by `KeyLeRest`. -/
theorem keyLeRest_of_lower (hTS : TopStep) (hTSt : TopStart) (hNS : NonTopStep)
    (hRel : StartRelNT) (hRoot : StartRootNT) (hLeft : Skip.LeftStart)
    (hJump : Skip.StartJumpGe) (hCut : StepCut) (hCJump : CutJump) (hCCopy : CutStartCopyNT)
    (hCRoot : CutStartRootNT) : KeyLeRest :=
  keyLeRest_of_regions
    (keyLeRegion_of_lower _ (fun _ _ o h => by cases o <;> simp_all [Origin.isUpper, cutOrigin])
      hTS hNS hTSt hRel hRoot hLeft hJump)
    (keyLeRegion_of_lower _ (fun _ _ o h => by obtain ⟨⟨r, rfl⟩, _⟩ := h; rfl)
      hTS hNS hTSt hRel hRoot hLeft hJump)
    (keyLeRegion_of_lower _ (fun _ _ o h => by obtain ⟨⟨r, rfl⟩, _⟩ := h; rfl)
      hTS hNS hTSt hRel hRoot hLeft hJump)
    (keyLeRegion_of_lower _ (fun _ _ o h => by obtain ⟨⟨r, rfl⟩, _⟩ := h; rfl)
      hTS hNS hTSt hRel hRoot hLeft hJump)
    (keyLeRegion_of_lower _ (fun _ _ o h => by obtain ⟨⟨r, rfl⟩, _⟩ := h; rfl)
      hTS hNS hTSt hRel hRoot hLeft hJump)
    (keyLeRegion_of_lowerCut _ (fun _ _ o h => by obtain ⟨⟨r, rfl⟩, _⟩ := h; rfl)
      hTS hNS hTSt hCut hCJump hCCopy hCRoot)
    (keyLeRegion_of_lowerCut _ (fun _ _ o h => by obtain ⟨⟨r, rfl⟩, _⟩ := h; rfl)
      hTS hNS hTSt hCut hCJump hCCopy hCRoot)

/-- **Well-foundedness of the official expansion** from the reconstruction and the statements
of `keyLeRest_of_lower`. -/
theorem wellFounded_of_lower (hrec : Dimension.BlockReconstruction) (hTS : TopStep)
    (hTSt : TopStart) (hNS : NonTopStep) (hRel : StartRelNT) (hRoot : StartRootNT)
    (hLeft : Skip.LeftStart) (hJump : Skip.StartJumpGe) (hCut : StepCut) (hCJump : CutJump)
    (hCCopy : CutStartCopyNT) (hCRoot : CutStartRootNT) : WellFounded Step :=
  wellFounded_of_block hrec ControlProof.controlDominates
    (keyLeRest_of_lower hTS hTSt hNS hRel hRoot hLeft hJump hCut hCJump hCCopy hCRoot)

end OmegaY.Official.Classification.Proofs.ChainCorr.LowerChain

#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.LowerChain.rel_step
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.LowerChain.top_of_splice
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.LowerChain.keyLeRegion_of_lower
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.LowerChain.keyLeRegion_of_lowerCut
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.LowerChain.keyLeRest_of_lower
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.LowerChain.wellFounded_of_lower
