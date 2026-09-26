/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/RawForest.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/RawForest.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.RawParent
import Googology.Notation.OmegaY.WellOrder.OmegaY.Forests.DepthValues

set_option backward.do.legacy false

/-!
# A finite natural-number forest for the entire actual raw-parent graph

Node codes preserve column order and retain every node's actual within-column
index. Decoding is inverse on actual nodes; unused codes have no parent.
Consequently this is an encoding of the full graph, not a projection which
identifies distinct rows in one column.

Numerical backfill becomes a sum equation on the encoded vertices. Raw parent
depth is bounded by the node value; it is not identified with that value.
The finite event frontiers and their synchronization needed by DepthValues
are not supplied by this encoding.
-/

namespace OmegaY.Geometry.Frame

def nodeStride (F : Frame) : Nat := Fintype.card F.Node + 1

theorem index_lt_nodeStride (F : Frame) (u : F.Node) : u.2.val < F.nodeStride := by
  have hInjective : Function.Injective (fun i : Fin (F.length u.1) => (⟨u.1, i⟩ : F.Node)) := by
    intro i j h
    cases h
    rfl
  have hCard := Fintype.card_le_of_injective _ hInjective
  simp only [Fintype.card_fin] at hCard
  exact u.2.isLt.trans_le (hCard.trans (Nat.le_succ _))

def nodeCode (F : Frame) (u : F.Node) : Nat :=
  u.1.val * F.nodeStride + u.2.val

theorem nodeCode_lt_of_column_lt {F : Frame} {u v : F.Node}
    (hColumn : u.1.val < v.1.val) : F.nodeCode u < F.nodeCode v := by
  calc
    F.nodeCode u < (u.1.val + 1) * F.nodeStride := by
      simp only [nodeCode, Nat.add_mul, Nat.one_mul]
      exact Nat.add_lt_add_left (F.index_lt_nodeStride u) _
    _ ≤ v.1.val * F.nodeStride := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hColumn)
    _ ≤ F.nodeCode v := Nat.le_add_right _ _

theorem nodeCode_lt_bound (F : Frame) (u : F.Node) :
    F.nodeCode u < F.width * F.nodeStride := by
  calc
    F.nodeCode u < (u.1.val + 1) * F.nodeStride := by
      simp only [nodeCode, Nat.add_mul, Nat.one_mul]
      exact Nat.add_lt_add_left (F.index_lt_nodeStride u) _
    _ ≤ F.width * F.nodeStride := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt u.1.isLt)

theorem nodeCode_injective (F : Frame) : Function.Injective F.nodeCode := by
  intro u v hCode
  have hColumn : u.1.val = v.1.val := by
    rcases Nat.lt_trichotomy u.1.val v.1.val with h | h | h
    · have := nodeCode_lt_of_column_lt (F := F) (u := u) (v := v) h
      omega
    · exact h
    · have := nodeCode_lt_of_column_lt (F := F) (u := v) (v := u) h
      omega
  have hIndex : u.2.val = v.2.val := by
    simp only [nodeCode, hColumn] at hCode
    exact Nat.add_left_cancel hCode
  apply (Executable.ref_injective F)
  cases u with
  | mk uc ui =>
    cases v with
    | mk vc vi =>
      simp only [ref]
      exact congrArg₂ Canonical.Ref.mk hColumn hIndex

noncomputable def nodeAtCode (F : Frame) (code : Nat) : Option F.Node :=
  if h : ∃ u, F.nodeCode u = code then some (Classical.choose h) else none

theorem nodeAtCode_spec {F : Frame} {code : Nat} {u : F.Node}
    (h : F.nodeAtCode code = some u) : F.nodeCode u = code := by
  classical
  unfold nodeAtCode at h
  split at h
  · rename_i hExists
    have hEq : Classical.choose hExists = u := Option.some.inj h
    exact hEq ▸ Classical.choose_spec hExists
  · cases h

@[simp] theorem nodeAtCode_nodeCode (F : Frame) (u : F.Node) :
    F.nodeAtCode (F.nodeCode u) = some u := by
  classical
  have hExists : ∃ v, F.nodeCode v = F.nodeCode u := ⟨u, rfl⟩
  have hEq : Classical.choose hExists = u :=
    F.nodeCode_injective (Classical.choose_spec hExists)
  simp only [nodeAtCode, dif_pos hExists, hEq]

noncomputable def rawForest (F : Frame) : ZeroY.ParentMap :=
  fun code => (F.nodeAtCode code).bind fun u => (F.rawParent u).map F.nodeCode

noncomputable def rawForestValue (F : Frame) (code : Nat) : Nat :=
  ((F.nodeAtCode code).map F.value).getD 0

@[simp] theorem rawForest_nodeCode (F : Frame) (u : F.Node) :
    F.rawForest (F.nodeCode u) = (F.rawParent u).map F.nodeCode := by
  simp [rawForest]

@[simp] theorem rawForestValue_nodeCode (F : Frame) (u : F.Node) :
    F.rawForestValue (F.nodeCode u) = F.value u := by
  simp [rawForestValue]

theorem rawForest_some_iff {F : Frame} {code parentCode : Nat} :
    F.rawForest code = some parentCode ↔
      ∃ u parent, F.nodeAtCode code = some u ∧ F.rawParent u = some parent ∧
        F.nodeCode parent = parentCode := by
  cases hNode : F.nodeAtCode code with
  | none => simp [rawForest, hNode]
  | some u =>
    cases hParent : F.rawParent u with
    | none => simp [rawForest, hNode, hParent]
    | some parent =>
      constructor
      · intro h
        have hCode : F.nodeCode parent = parentCode := by
          simpa [rawForest, hNode, hParent] using h
        exact ⟨u, parent, rfl, hParent, hCode⟩
      · rintro ⟨v, p, hV, hP, hCode⟩
        have hVU : v = u := Option.some.inj hV.symm
        subst v
        have hPP : p = parent := Option.some.inj (hP.symm.trans hParent)
        subst p
        simp [rawForest, hNode, hParent, hCode]

/-- Exact preservation of every raw edge, with no identification of rows. -/
theorem rawForest_edge_iff {F : Frame} {u parent : F.Node} :
    F.rawForest (F.nodeCode u) = some (F.nodeCode parent) ↔ F.rawParent u = some parent := by
  rw [rawForest_nodeCode]
  cases hRaw : F.rawParent u with
  | none => simp
  | some actual =>
    simp only [Option.map_some, Option.some.injEq]
    exact ⟨fun h => F.nodeCode_injective h, congrArg F.nodeCode⟩

theorem rawForest_leftward {F : Frame} (hF : F.Ordered) : ZeroY.Forest.Leftward F.rawForest := by
  intro code parentCode h
  obtain ⟨u, parent, hNode, hParent, hParentCode⟩ := rawForest_some_iff.mp h
  rw [← nodeAtCode_spec hNode, ← hParentCode]
  exact nodeCode_lt_of_column_lt (rawParent_column_lt hF hParent)

/-- The forest is extended by absent vertices outside an explicit finite bound. -/
theorem rawForest_none_above_bound (F : Frame) {code : Nat}
    (hBound : F.width * F.nodeStride ≤ code) : F.rawForest code = none := by
  cases hNode : F.nodeAtCode code with
  | none => simp [rawForest, hNode]
  | some u =>
    have hCode := nodeAtCode_spec hNode
    have hLt := F.nodeCode_lt_bound u
    omega

end OmegaY.Geometry.Frame

namespace OmegaY.Expansion

open Canonical Geometry ZeroY ZeroY.Forest

/-- An existing raw edge on a real node has a real smaller-valued target.
The edge is the actual stored upper endpoint, not a recovered P assertion. -/
theorem MountainSums.rawParent_value_lt {mountain : Mountain}
    (hSums : MountainSums mountain) (hValid : MountainValid mountain)
    {u parent : (Frame.ofMountain mountain).Node} (hReal : Frame.Real u)
    (hParent : (Frame.ofMountain mountain).rawParent u = some parent) :
    Frame.Real parent ∧ (Frame.ofMountain mountain).value parent < (Frame.ofMountain mountain).value u := by
  obtain ⟨upper, hUpper, _⟩ := Frame.rawParent_spec hParent
  obtain ⟨actual, hActual, _, hPositive, hSmall, _⟩ := hSums.rawParent_upper hValid hReal hUpper
  have hEq : actual = parent := Option.some.inj (hActual.symm.trans hParent)
  subst actual
  exact ⟨Frame.real_of_value_pos hValid.toOrdered hPositive, hSmall⟩

/-- The entire raw forest gives a strict lower bound on positive node values.
Its unweighted depth generally does not equal the node value. -/
theorem MountainSums.rawForest_depth_lt_value {mountain : Mountain}
    (hSums : MountainSums mountain) (hValid : MountainValid mountain)
    {u : (Frame.ofMountain mountain).Node} (hReal : Frame.Real u) :
    parentDepth (Frame.ofMountain mountain).rawForest ((Frame.ofMountain mountain).nodeCode u) <
      (Frame.ofMountain mountain).value u := by
  generalize hCode : (Frame.ofMountain mountain).nodeCode u = code
  induction code using Nat.strongRecOn generalizing u with
  | ind code ih =>
    have hLeft : Leftward (Frame.ofMountain mountain).rawForest :=
      Frame.rawForest_leftward hValid.toOrdered
    cases hParent : (Frame.ofMountain mountain).rawParent u with
    | none =>
      have hForest : (Frame.ofMountain mountain).rawForest code = none := by
        rw [← hCode, Frame.rawForest_nodeCode, hParent]
        rfl
      rw [parentDepth_none (parent := (Frame.ofMountain mountain).rawForest) hForest]
      exact hValid.toOrdered.real_positive u hReal
    | some parent =>
      have hForest : (Frame.ofMountain mountain).rawForest code =
          some ((Frame.ofMountain mountain).nodeCode parent) := by
        rw [← hCode, Frame.rawForest_nodeCode, hParent]
        rfl
      obtain ⟨hParentReal, hValue⟩ := hSums.rawParent_value_lt hValid hReal hParent
      have hIH := ih ((Frame.ofMountain mountain).nodeCode parent) (hLeft hForest) hParentReal rfl
      rw [parentDepth_some (parent := (Frame.ofMountain mountain).rawForest) hLeft hForest]
      omega

/-- Actual array backfill is retained verbatim in the natural-number forest.
Both the upper node and the parent keep their distinct full-node codes. -/
theorem MountainSums.rawForest_upper_sum {mountain : Mountain}
    (hSums : MountainSums mountain) (hValid : MountainValid mountain)
    {u upper : (Frame.ofMountain mountain).Node} (hReal : Frame.Real u)
    (hUpper : (Frame.ofMountain mountain).upper u = some upper) :
    ∃ parentCode,
      (Frame.ofMountain mountain).rawForest ((Frame.ofMountain mountain).nodeCode u) = some parentCode ∧
      0 < (Frame.ofMountain mountain).rawForestValue parentCode ∧
      (Frame.ofMountain mountain).rawForestValue ((Frame.ofMountain mountain).nodeCode u) =
        (Frame.ofMountain mountain).rawForestValue ((Frame.ofMountain mountain).nodeCode upper) +
        (Frame.ofMountain mountain).rawForestValue parentCode := by
  obtain ⟨parent, hParent, _, hPositive, _, hValue, _⟩ := hSums.rawParent_upper hValid hReal hUpper
  refine ⟨(Frame.ofMountain mountain).nodeCode parent, ?_, ?_, ?_⟩
  · exact Frame.rawForest_edge_iff.mpr hParent
  · simpa only [Frame.rawForestValue_nodeCode] using hPositive
  · simpa only [Frame.rawForestValue_nodeCode] using hValue

/-- The encoded forest and its numerical laws exist for every actual finite
expansion. This is an internal graph forest, not an expansion-ranking map. -/
theorem expandDiagram_rawForest {values : List Nat} (hLegal : Canonical.Legal values)
    {copies : Nat} {mountain : Mountain} (hRun : expandDiagram values copies = .ok mountain) :
    Leftward (Frame.ofMountain mountain).rawForest ∧
    (∀ u, Frame.Real u →
      parentDepth (Frame.ofMountain mountain).rawForest ((Frame.ofMountain mountain).nodeCode u) <
        (Frame.ofMountain mountain).value u) ∧
    ∀ u upper, Frame.Real u → (Frame.ofMountain mountain).upper u = some upper →
      ∃ parentCode,
        (Frame.ofMountain mountain).rawForest ((Frame.ofMountain mountain).nodeCode u) = some parentCode ∧
        0 < (Frame.ofMountain mountain).rawForestValue parentCode ∧
        (Frame.ofMountain mountain).rawForestValue ((Frame.ofMountain mountain).nodeCode u) =
          (Frame.ofMountain mountain).rawForestValue ((Frame.ofMountain mountain).nodeCode upper) +
          (Frame.ofMountain mountain).rawForestValue parentCode := by
  obtain ⟨actual, hActual, hValid, hSums, _⟩ := expandDiagram_total_with_equations hLegal copies
  have hEq : actual = mountain := Except.ok.inj (hActual.symm.trans hRun)
  subst actual
  exact ⟨Frame.rawForest_leftward hValid.toOrdered,
    fun _ hReal => hSums.rawForest_depth_lt_value hValid hReal,
    fun _ _ hReal hUpper => hSums.rawForest_upper_sum hValid hReal hUpper⟩

end OmegaY.Expansion

#print axioms OmegaY.Geometry.Frame.nodeCode_injective
#print axioms OmegaY.Geometry.Frame.nodeAtCode_nodeCode
#print axioms OmegaY.Geometry.Frame.rawForest_edge_iff
#print axioms OmegaY.Geometry.Frame.rawForest_leftward
#print axioms OmegaY.Geometry.Frame.rawForest_none_above_bound
#print axioms OmegaY.Expansion.MountainSums.rawParent_value_lt
#print axioms OmegaY.Expansion.MountainSums.rawForest_depth_lt_value
#print axioms OmegaY.Expansion.MountainSums.rawForest_upper_sum
#print axioms OmegaY.Expansion.expandDiagram_rawForest
