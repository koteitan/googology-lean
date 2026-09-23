/-
Adapted from Phyrion, 1Y-Well-Ordering-Lean, formalization/OneY/Expansion.lean,
revision 6533b2975f3cafb3582dc8f8127e9ea7144d7e69 (Apache-2.0).
Changes: none besides this header (the file refers to no BMS-layer name).
Taken from koteitan, 1y-wo-por, `OneY/Expansion.lean` (https://github.com/koteitan/1y-wo-por,
revision db86f2d13c2e18a8e2c2fae5e083d00fc4d48a78, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.Y.WellOrder.`.
Port change: in `reconstructedValues_legal` the proof `by decide` of `0 < 1` is replaced by `Nat.one_pos`.
-/
import Googology.Notation.Y.WellOrder.OneY.RootSearch
import Googology.Notation.Y.WellOrder.OneY.ActiveGeometry
import Googology.Notation.Y.WellOrder.OneY.LowerCopyNesting
import Googology.Notation.Y.WellOrder.OneY.TerminalCopyNumeric
import Googology.Notation.Y.WellOrder.OneY.OrdinaryCopy
import Googology.Notation.Y.WellOrder.OneY.TowerReconstruction
import Googology.Notation.Y.WellOrder.ZeroY.Expansion

/-!
# The concrete graph-copy and numerical-reconstruction algorithm

All graph contexts are constructed from a computed bad root. This file
defines actual expansion and proves its output is a legal sequence.
It does not yet claim that independently rebuilding the output recovers
the prescribed copied graphs, or that iterated expansion is well-founded.
-/

namespace OneY.Numeric

def expandedMountain (a : RootedRow) {K d x y : Nat}
    (hbad : BadAt a K d x y) (k : Nat) : RootGeometry.RowMountain :=
  if hk : k < K then (badAtLowerContext a hbad hk).toRowMountain
  else if k = K then badAtTerminalMountain a hbad
  else (OrdinaryCopy.Context.mk (mountain (layers a k).row (layers a k).positive)
    ⟨y, x, (rows (layers a K).row d).forest.parent_left hbad.1⟩).toRowMountain

def expandedGraphs (a : RootedRow) {K d x y : Nat}
    (hbad : BadAt a K d x y) (bound : Nat) : List RootGeometry.RowMountain :=
  (List.range bound).map (expandedMountain a hbad)

def reconstructedValues (graphs : List RootGeometry.RowMountain) (width : Nat) : List Nat :=
  (List.range width).map (TowerReconstruction.assemble graphs (fun _ => 1))

theorem reconstructedValues_legal (graphs : List RootGeometry.RowMountain) (width : Nat) :
    ZeroY.Legal (reconstructedValues graphs width) := by
  constructor
  · intro v hv
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hv
    exact TowerReconstruction.assemble_positive graphs (fun _ => 1) (fun _ => Nat.one_pos) c
  · by_cases hw : width = 0
    · exact Or.inl (by simp [reconstructedValues, hw])
    · right
      simp only [reconstructedValues, List.head?_map, List.head?_range, hw, ↓reduceIte,
        Option.map_some, TowerReconstruction.assemble_first]

def expandValues (s : List Nat) (hs : ZeroY.Legal s) (N : Nat) : List Nat :=
  let x := s.length-1
  match hz : findBadRoot s hs x with
  | none => s.take x
  | some z =>
      let hbad := (findBadRoot_sound s hs x hz).2
      reconstructedValues (expandedGraphs (rootedSequence s hs) hbad (sequenceBound s))
        (x + N*(x-z.column))

theorem expandValues_legal (s : List Nat) (hs : ZeroY.Legal s) (N : Nat) :
    ZeroY.Legal (expandValues s hs N) := by
  unfold expandValues
  dsimp only
  split
  · exact ZeroY.legal_take hs _
  · exact reconstructedValues_legal _ _

def expand (s : ZeroY.Expr) (N : Nat) : ZeroY.Expr :=
  ⟨expandValues s.values s.legal N, expandValues_legal s.values s.legal N⟩

theorem expandValues_of_no_parent (s : List Nat) (hs : ZeroY.Legal s) (N : Nat)
    (hp : (ofSequence s).forest.parent (s.length-1) = none) :
    expandValues s hs N = s.take (s.length-1) := by
  have hn := (findBadRoot_none_iff s hs (s.length-1)).mpr hp
  unfold expandValues
  dsimp only
  split
  · rfl
  · rename_i z hz
    rw [hn] at hz
    contradiction

end OneY.Numeric

#print axioms OneY.Numeric.expandedMountain
#print axioms OneY.Numeric.expandValues_legal
