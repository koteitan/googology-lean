/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Geometry/MountainKeys.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Geometry/MountainKeys.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.RawFrameGeometry
import Googology.Notation.OmegaY.WellOrder.OmegaY.Model

set_option backward.do.legacy false

/-!
# Actual finite root keys of stored mountain edges

At scale `k` a stored parent edge is retained exactly when all row
coefficients at exponents at least `k` agree. The root below is computed
by well-founded recursion on the actual column, not supplied as an oracle.
The finite template reads those roots from high scale to low scale and
uses the genuine infinity marker below the edge's jump exponent.

This module does not prove vertical strict growth, copy-key transport,
canonical reconstruction, or descent of expansion representations.
-/

namespace OmegaY.Geometry.Frame

universe u

def scaleParent (F : Frame) (k : Nat) (u : F.Node) : Option F.Node :=
  (F.rawParent u).bind fun parent =>
    if Row.jump (F.height u) (F.height parent) ≤ k then some parent else none

theorem scaleParent_some_iff {F : Frame} {k : Nat} {u parent : F.Node} :
    F.scaleParent k u = some parent ↔
      F.rawParent u = some parent ∧ Row.jump (F.height u) (F.height parent) ≤ k := by
  unfold scaleParent
  cases hp : F.rawParent u with
  | none => simp
  | some p =>
      simp only [Option.bind_some]
      split
      · rename_i h
        simp only [Option.some.injEq]
        constructor
        · rintro rfl
          exact ⟨rfl, h⟩
        · exact fun h => h.1
      · rename_i hn
        constructor
        · intro h
          cases h
        · rintro ⟨he, hScale⟩
          have heq := Option.some.inj he
          subst parent
          exact (hn hScale).elim

theorem scaleParent_column_lt {F : Frame} (hF : F.Ordered)
    {k : Nat} {u parent : F.Node} (h : F.scaleParent k u = some parent) :
    parent.1.val < u.1.val :=
  rawParent_column_lt hF (scaleParent_some_iff.mp h).1

def scaleRoot {F : Frame} (hF : F.Ordered) (k : Nat) (u : F.Node) : F.Node :=
  match _hp : F.scaleParent k u with
  | none => u
  | some parent => scaleRoot hF k parent
termination_by u.1.val
decreasing_by exact scaleParent_column_lt hF _hp

theorem scaleRoot_eq_of_none {F : Frame} (hF : F.Ordered) {k : Nat} {u : F.Node}
    (h : F.scaleParent k u = none) : scaleRoot hF k u = u := by
  rw [scaleRoot, h]

theorem scaleRoot_eq_of_parent {F : Frame} (hF : F.Ordered) {k : Nat} {u parent : F.Node}
    (h : F.scaleParent k u = some parent) :
    scaleRoot hF k u = scaleRoot hF k parent := by
  rw [scaleRoot, h]

theorem scaleRoot_column_le {F : Frame} (hF : F.Ordered) (k : Nat) (u : F.Node) :
    (scaleRoot hF k u).1.val ≤ u.1.val := by
  cases hp : F.scaleParent k u with
  | none => rw [scaleRoot_eq_of_none hF hp]
  | some parent =>
      rw [scaleRoot_eq_of_parent hF hp]
      exact (scaleRoot_column_le hF k parent).trans (scaleParent_column_lt hF hp).le
termination_by u.1.val
decreasing_by exact scaleParent_column_lt hF hp

theorem scaleRoot_parent_none {F : Frame} (hF : F.Ordered) (k : Nat) (u : F.Node) :
    F.scaleParent k (scaleRoot hF k u) = none := by
  cases hp : F.scaleParent k u with
  | none => simpa only [scaleRoot_eq_of_none hF hp] using hp
  | some parent =>
      rw [scaleRoot_eq_of_parent hF hp]
      exact scaleRoot_parent_none hF k parent
termination_by u.1.val
decreasing_by exact scaleParent_column_lt hF hp

theorem scaleRoot_same_block {F : Frame} (hF : F.Ordered) (k : Nat) (u : F.Node) :
    Row.jump (F.height u) (F.height (scaleRoot hF k u)) ≤ k := by
  cases hp : F.scaleParent k u with
  | none => simp only [scaleRoot_eq_of_none hF hp, Row.jump_self, Nat.zero_le]
  | some parent =>
      rw [scaleRoot_eq_of_parent hF hp]
      exact (Row.jump_triangle _ (F.height parent) _).trans
        (max_le (scaleParent_some_iff.mp hp).2 (scaleRoot_same_block hF k parent))
termination_by u.1.val
decreasing_by exact scaleParent_column_lt hF hp

theorem scaleRoot_eq_of_raw {F : Frame} (hF : F.Ordered)
    {u parent : F.Node} (hParent : F.rawParent u = some parent) {k : Nat}
    (hScale : Row.jump (F.height u) (F.height parent) ≤ k) :
    scaleRoot hF k u = scaleRoot hF k parent :=
  scaleRoot_eq_of_parent hF (scaleParent_some_iff.mpr ⟨hParent, hScale⟩)

theorem scaleRoot_parent_column_le {F : Frame} (hF : F.Ordered)
    {u parent : F.Node} (hParent : F.rawParent u = some parent) (k : Nat) :
    (scaleRoot hF k parent).1.val ≤ (scaleRoot hF k u).1.val := by
  by_cases hScale : Row.jump (F.height u) (F.height parent) ≤ k
  · rw [scaleRoot_eq_of_raw hF hParent hScale]
  · have hNone : F.scaleParent k u = none := by simp [scaleParent, hParent, hScale]
    rw [scaleRoot_eq_of_none hF hNone]
    exact (scaleRoot_column_le hF k parent).trans (rawParent_column_lt hF hParent).le

/-- Coarser scales keep at least all finer-scale edges, so their actual
roots are no farther right. -/
theorem scaleRoot_scale_antitone {F : Frame} (hF : F.Ordered)
    {fine coarse : Nat} (hScale : fine ≤ coarse) (u : F.Node) :
    (scaleRoot hF coarse u).1.val ≤ (scaleRoot hF fine u).1.val := by
  cases hp : F.scaleParent fine u with
  | none =>
      rw [scaleRoot_eq_of_none hF hp]
      exact scaleRoot_column_le hF coarse u
  | some parent =>
      have h := scaleParent_some_iff.mp hp
      rw [scaleRoot_eq_of_parent hF hp, scaleRoot_eq_of_raw hF h.1 (h.2.trans hScale)]
      exact scaleRoot_scale_antitone hF hScale parent
termination_by u.1.val
decreasing_by exact scaleParent_column_lt hF hp

/-- A real vertical edge, with its parent read from the actual upper cell.
No numerical first-smaller equation or representation is a field. -/
structure RealStoredEdge (F : Frame) where
  lower : F.Node
  upper : F.Node
  parent : F.Node
  lower_real : Real lower
  upper_eq : F.upper lower = some upper
  parent_eq : F.rawParent lower = some parent

/-- Finitely many actual nodes each have finite Cantor support. A common
finite dimension exists, including for the empty frame. -/
theorem exists_key_dimension (F : Frame) :
    ∃ D : Nat, ∀ u : F.Node, ∀ i, D < i → Row.coeff (F.height u) i = 0 := by
  classical
  let D := (Finset.univ : Finset F.Node).sup
    (fun u => (F.height u).coeffs.support.sup id)
  refine ⟨D, ?_⟩
  intro u i hHigh
  by_contra hn
  have hi : i ∈ (F.height u).coeffs.support := Finsupp.mem_support_iff.mpr hn
  have hiBound : i ≤ (F.height u).coeffs.support.sup id := Finset.le_sup (f := id) hi
  have huBound : (F.height u).coeffs.support.sup id ≤ D :=
    Finset.le_sup (f := fun v : F.Node => (F.height v).coeffs.support.sup id)
      (Finset.mem_univ u)
  omega

namespace RealStoredEdge

variable {F : Frame} (e : RealStoredEdge F)

def degree : Nat := Row.jump (F.height e.lower) (F.height e.parent)

theorem row_eq (hRaw : F.RawRowGeometry) :
    F.height e.upper = Row.bump (F.height e.lower) e.degree := by
  obtain ⟨parent, hp, _, _, hB⟩ := hRaw e.lower e.upper e.lower_real e.upper_eq
  have he : parent = e.parent := Option.some.inj (hp.symm.trans e.parent_eq)
  subst parent
  exact hB

theorem degree_from_vertical_jump (hRaw : F.RawRowGeometry) :
    Row.jump (F.height e.lower) (F.height e.upper) = e.degree + 1 := by
  rw [e.row_eq hRaw, Row.jump_bump]

/-- Coefficient support at `D` is the exact finite-Cantor dimension bound;
it is not a bound on the numerical values or ordinary row height. -/
theorem degree_le (hRaw : F.RawRowGeometry) {D : Nat}
    (hSupported : ∀ i, D < i → Row.coeff (F.height e.upper) i = 0) :
    e.degree ≤ D := by
  by_contra hn
  have hZero := hSupported e.degree (lt_of_not_ge hn)
  rw [e.row_eq hRaw, Row.coeff_bump_at] at hZero
  omega

def keyTemplate (hF : F.Ordered) (D : Nat) : Keys.Template (D + 1) F.width :=
  fun i => if e.degree ≤ D - i.val then
    some (scaleRoot hF (D - i.val) e.parent).1 else none

theorem keyTemplate_finite (hF : F.Ordered) {D : Nat} (i : Fin (D + 1))
    (hi : e.degree ≤ D - i.val) :
    e.keyTemplate hF D i = some (scaleRoot hF (D - i.val) e.parent).1 := by
  simp only [keyTemplate, if_pos hi]

theorem keyTemplate_infinity (hF : F.Ordered) {D : Nat} (i : Fin (D + 1))
    (hi : D - i.val < e.degree) : e.keyTemplate hF D i = none := by
  simp only [keyTemplate, if_neg (not_le_of_gt hi)]

/-- Every named finite parameter is a genuine root column at or left of
the actual parent; in particular no child or virtual top is named. -/
theorem keyTemplate_column_bound (hF : F.Ordered) {D : Nat} {i : Fin (D + 1)}
    {column : Fin F.width} (h : e.keyTemplate hF D i = some column) :
    column.val ≤ e.parent.1.val ∧ column.val < e.lower.1.val := by
  unfold keyTemplate at h
  split at h
  · have he := Option.some.inj h
    rw [← he]
    exact ⟨scaleRoot_column_le hF _ _,
      (scaleRoot_column_le hF _ _).trans_lt (rawParent_column_lt hF e.parent_eq)⟩
  · cases h

/-- The finite part can equally be read on the lower endpoint. This is
the bridge used before comparing successive vertical-edge keys. -/
theorem keyTemplate_lower_root (hF : F.Ordered) {D : Nat} (i : Fin (D + 1))
    (hi : e.degree ≤ D - i.val) :
    e.keyTemplate hF D i = some (scaleRoot hF (D - i.val) e.lower).1 := by
  rw [e.keyTemplate_finite hF i hi, scaleRoot_eq_of_raw hF e.parent_eq hi]

/-- Exact agreement with the previously formalized high-to-low truncated
key. There are `D+1-degree` finite coordinates and `degree` infinities. -/
theorem eval_keyTemplate_eq_truncate {Label : Type u} [LinearOrder Label]
    (hF : F.Ordered) {D : Nat} (hDegree : e.degree ≤ D) (f : Fin F.width → Label) :
    Keys.eval (e.keyTemplate hF D) f =
      Keys.truncate (fun i : Fin (D + 1) => f (scaleRoot hF (D - i.val) e.parent).1)
        (D + 1 - e.degree) := by
  apply funext
  intro i
  have hIndex := i.isLt
  have hIff : e.degree ≤ D - i.val ↔ i.val < D + 1 - e.degree := by omega
  simp only [Keys.eval, keyTemplate, Keys.truncate, Pi.toLex_apply]
  by_cases h : e.degree ≤ D - i.val
  · simp only [if_pos h, if_pos (hIff.mp h)]
  · simp only [if_neg h, if_neg (fun hi => h (hIff.mpr hi))]

def atom (hF : F.Ordered) (D : Nat) : Model.InternalAtom (D + 1) F.width where
  key := e.keyTemplate hF D
  parent := e.parent.1
  child := e.lower.1
  parent_lt_child := rawParent_column_lt hF e.parent_eq

end RealStoredEdge

/-- Every real stored edge is one of finitely many triples of actual
nodes. Proof fields add no vertices or hidden graph data. -/
noncomputable instance realStoredEdge_fintype (F : Frame) : Fintype (RealStoredEdge F) :=
  Fintype.ofInjective (fun e : RealStoredEdge F => (e.lower, e.upper, e.parent)) (by
    intro a b h
    have hl := congrArg (fun t => t.1) h
    have hu := congrArg (fun t => t.2.1) h
    have hp := congrArg (fun t => t.2.2) h
    cases a
    cases b
    cases hl
    cases hu
    cases hp
    rfl)

/-- Initial supply for the entire actual finite stored-edge diagram.
The list is generated from all actual edges, with their computed keys.
This is initial representability only, not an expansion decrease. -/
theorem actual_keys_initially_represented {F : Frame} (hF : F.Ordered) (D : Nat) :
    ∃ beta : Model.Label, beta < Reflection.OrdinalSupply.top ∧
      ∃ f : Fin F.width → Model.Label,
        StrictMono f ∧ Reflection.Bounded f beta ∧
        ∀ e : RealStoredEdge F,
          Model.R (D + 1) (Keys.eval (e.keyTemplate hF D) f)
            (f e.parent.1) (f e.lower.1) := by
  classical
  let edges := (Finset.univ : Finset (RealStoredEdge F)).toList
  obtain ⟨beta, hBeta, f, hMono, hBound, hGraph, _⟩ :=
    Model.initial_finite_graph (edges.map (fun e => e.atom hF D)) []
  refine ⟨beta, hBeta, f, hMono, hBound, ?_⟩
  intro e
  exact hGraph (e.atom hF D) (List.mem_map.mpr ⟨e, by simp [edges], rfl⟩)

end OmegaY.Geometry.Frame

#print axioms OmegaY.Geometry.Frame.scaleRoot_column_le
#print axioms OmegaY.Geometry.Frame.scaleRoot_parent_none
#print axioms OmegaY.Geometry.Frame.scaleRoot_same_block
#print axioms OmegaY.Geometry.Frame.scaleRoot_scale_antitone
#print axioms OmegaY.Geometry.Frame.exists_key_dimension
#print axioms OmegaY.Geometry.Frame.RealStoredEdge.degree_le
#print axioms OmegaY.Geometry.Frame.RealStoredEdge.keyTemplate_column_bound
#print axioms OmegaY.Geometry.Frame.RealStoredEdge.keyTemplate_lower_root
#print axioms OmegaY.Geometry.Frame.RealStoredEdge.eval_keyTemplate_eq_truncate
#print axioms OmegaY.Geometry.Frame.actual_keys_initially_represented
