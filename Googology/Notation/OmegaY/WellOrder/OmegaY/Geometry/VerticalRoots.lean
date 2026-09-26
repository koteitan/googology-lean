/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Geometry/VerticalRoots.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Geometry/VerticalRoots.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Geometry.RootVectors

set_option backward.do.legacy false

/-!
# Strong vertical growth of the complete actual root vector

The conclusion compares every retained high prefix that reaches the
highest differing row coefficient. Its proof uses actual source Normal
rules and numerical Q/P searches. No vertical comparison of the current
column is a field of Normal or an external assumption of the final result.
-/

namespace OmegaY.Geometry.Frame

universe u

private theorem same_column_lt {F : Frame} (hF : F.Ordered) {u v : F.Node}
    (hc : u.1 = v.1) (hi : u.2.val < v.2.val) : F.height u < F.height v := by
  rcases u with ⟨c, i⟩
  rcases v with ⟨d, j⟩
  dsimp only at hc hi
  subst d
  exact hF.rows_strict c hi

private theorem same_column_le {F : Frame} (hF : F.Ordered) {u v : F.Node}
    (hc : u.1 = v.1) (hi : u.2.val ≤ v.2.val) : F.height u ≤ F.height v := by
  rcases u with ⟨c, i⟩
  rcases v with ⟨d, j⟩
  dsimp only at hc hi
  subst d
  exact (hF.rows_strict c).monotone hi

private theorem same_column_index_eq {F : Frame} {u v : F.Node}
    (hc : u.1 = v.1) (hi : u.2.val = v.2.val) : u = v := by
  rcases u with ⟨c, i⟩
  rcases v with ⟨d, j⟩
  dsimp only at hc hi
  subst d
  obtain rfl := Fin.ext hi
  rfl

private theorem upper_of_next_index {F : Frame} {u v : F.Node}
    (hc : u.1 = v.1) (hi : v.2.val = u.2.val + 1) : F.upper u = some v := by
  rcases u with ⟨c, i⟩
  rcases v with ⟨d, j⟩
  dsimp only at hc hi
  subst d
  have he : j = ⟨i.val + 1, by omega⟩ := Fin.ext hi
  simp only [upper, dif_pos (show i.val + 1 < F.length c by omega), he]

private theorem jump_pos_of_lt {a b : Row} (h : a < b) : 0 < Row.jump a b := by
  by_contra hn
  have he : Row.jump a b = 0 := by omega
  exact (ne_of_lt h) (Row.jump_eq_zero.mp he)

/-- Full high-prefix vertical comparison; scales above the actual finite
dimension contribute zero coordinates and are not silently dropped. -/
def RootVertical {F : Frame} (hF : F.Ordered) (D : Nat) (u v : F.Node) : Prop :=
  ∀ k, k < Row.jump (F.height u) (F.height v) →
    rootPrefix hF D k u < rootPrefix hF D k v

private theorem vertical_prefix_le {F : Frame} (hF : F.Ordered) {D : Nat}
    {u v : F.Node} (hHeight : F.height u < F.height v)
    (h : RootVertical hF D u v) (k : Nat) :
    rootPrefix hF D k u ≤ rootPrefix hF D k v :=
  rootPrefix_le_coarser hF (Nat.zero_le k)
    (h 0 (jump_pos_of_lt hHeight)).le

/-- The adjacent case only uses strong vertical comparisons in strictly
earlier columns. The main theorem below supplies this premise by induction. -/
private theorem Normal.rootVertical_adjacent {F : Frame} (hF : F.Normal)
    {D : Nat} (hSupported : ∀ w : F.Node, ∀ i, D < i → Row.coeff (F.height w) i = 0)
    {u v : F.Node} (hReal : Real u) (hUpper : F.upper u = some v)
    (hLeft : ∀ a b : F.Node, a.1.val < u.1.val → Real a → a.1 = b.1 →
      a.2.val < b.2.val → RootVertical hF.toOrdered D a b) :
    RootVertical hF.toOrdered D u v := by
  obtain ⟨p, hP, hRow, _, hStored⟩ := hF.upper_step u v hReal hUpper
  have hRaw : F.rawParent u = some p := (hF.rawParent_eq_P hReal).trans hP
  let d := Row.jump (F.height u) (F.height p)
  have hRow' : F.height v = Row.bump (F.height u) d := hRow
  have hPReal := real_of_value_pos hF.toOrdered (P_value hF.toOrdered hP).1
  have hPColumn := P_column_lt hF.toOrdered hP
  have hPHeight := P_height_le hF.toOrdered hP
  have hVReal : Real v := by
    have hv := (upper_spec hUpper).2
    unfold Real at *
    omega
  have hVDegree : d ≤ D :=
    (RealStoredEdge.mk u v p hReal hUpper hRaw).degree_le hF.rawRowGeometry (hSupported v)
  obtain ⟨q, hQ⟩ := Q_exists_of_left hF.toOrdered ⟨ref p, hStored⟩
  obtain ⟨left, hLeftStored, _, _, hQColumn, hQIndex, hQHeight, _⟩ := Q_spec hF.toOrdered hQ
  have hLeftEq : left = p := by
    apply Option.some.inj
    rw [← F.lookup_ref left, ← F.lookup_ref p]
    exact congrArg F.lookup (Option.some.inj (hLeftStored.symm.trans hStored))
  subst left
  have hPQHeight := same_column_le hF.toOrdered hQColumn.symm hQIndex
  have hPQ : rootPrefix hF.toOrdered D d p ≤ rootPrefix hF.toOrdered D d q := by
    by_cases he : p.2.val = q.2.val
    · obtain rfl := same_column_index_eq hQColumn.symm he
      exact le_rfl
    · have hi : p.2.val < q.2.val := by omega
      exact vertical_prefix_le hF.toOrdered
        (same_column_lt hF.toOrdered hQColumn.symm hi)
        (hLeft p q hPColumn hPReal hQColumn.symm hi) d
  have hQV := hF.rootPrefix_candidate_le hVReal hQ D d
  have hUP := rootPrefix_eq_of_raw hF.toOrdered hRaw (D := D) (Nat.le_refl d)
  have hStrict : rootPrefix hF.toOrdered D d p < rootPrefix hF.toOrdered D d v := by
    rcases lt_or_eq_of_le hPQ with hLess | hEqual
    · exact lt_of_lt_of_le hLess hQV
    · have hOutside : d < Row.jump (F.height v) (F.height q) := by
        by_contra hn
        have hInside : Row.jump (F.height q) (F.height v) ≤ d := by
          simpa only [Row.jump_comm] using le_of_not_gt hn
        have hPV : Row.jump (F.height p) (F.height v) = d + 1 := by
          rw [hRow', Row.bump_eq_of_jump_le (show Row.jump (F.height u) (F.height p) ≤ d from le_rfl)]
          exact Row.jump_bump _ _
        have hMax := Row.jump_max hPQHeight hQHeight
        have hJump : d < Row.jump (F.height p) (F.height q) := by omega
        have hIndex : p.2.val < q.2.val := by
          by_contra hn
          have he : p = q := same_column_index_eq hQColumn.symm (by omega)
          subst q
          simp only [Row.jump_self] at hJump
          omega
        have hContrad := hLeft p q hPColumn hPReal hQColumn.symm hIndex d hJump
        exact (ne_of_lt hContrad) hEqual
      have hSelf := hF.scaleRoot_self_of_candidate_outside hVReal hQ hOutside
      apply lt_of_le_of_ne (hPQ.trans hQV)
      intro he
      have heAt := congrArg (fun a : Row => Row.coeff a d) he
      simp only [coeff_rootPrefix, le_refl, hVDegree, and_self, if_true] at heAt
      rw [hSelf] at heAt
      have hRootBound := scaleRoot_column_le hF.toOrdered d p
      have hVColumn := (upper_spec hUpper).1
      have hVCol : v.1.val = u.1.val := congrArg Fin.val hVColumn
      omega
  intro k hk
  have hJumpUV : Row.jump (F.height u) (F.height v) = d + 1 := by
    rw [hRow', Row.jump_bump]
  have hkD : k ≤ d := by omega
  apply rootPrefix_strict_finer hF.toOrdered hkD
  rw [hUP]
  exact hStrict

/-- Strong vertical theorem (V) for every actual source-normal frame.
For two real levels in one column, the complete root prefix is strictly
increasing whenever that prefix includes the highest differing row digit.

The recursion is on `(column, vertical index distance)`: the adjacent
argument invokes only earlier columns, and the nonadjacent argument
splits into two shorter vertical intervals. -/
theorem Normal.rootVertical {F : Frame} (hF : F.Normal) {D : Nat}
    (hSupported : ∀ w : F.Node, ∀ i, D < i → Row.coeff (F.height w) i = 0)
    {u v : F.Node} (hReal : Real u) (hColumn : u.1 = v.1)
    (hIndex : u.2.val < v.2.val) : RootVertical hF.toOrdered D u v := by
  by_cases hAdjacent : v.2.val = u.2.val + 1
  · apply hF.rootVertical_adjacent hSupported hReal (upper_of_next_index hColumn hAdjacent)
    intro a b hLeft hAReal hABColumn hABIndex
    exact hF.rootVertical hSupported hAReal hABColumn hABIndex
  · let w : F.Node := ⟨v.1, ⟨v.2.val - 1, by have := v.2.isLt; omega⟩⟩
    have hUWColumn : u.1 = w.1 := hColumn
    have hWVColumn : w.1 = v.1 := rfl
    have hUWIndex : u.2.val < w.2.val := by dsimp only [w]; omega
    have hWVIndex : w.2.val < v.2.val := by dsimp only [w]; omega
    have hWReal : Real w := by unfold Real at *; omega
    have hUW := hF.rootVertical hSupported hReal hUWColumn hUWIndex
    have hWV := hF.rootVertical hSupported hWReal hWVColumn hWVIndex
    have hUWHeight := same_column_lt hF.toOrdered hUWColumn hUWIndex
    have hWVHeight := same_column_lt hF.toOrdered hWVColumn hWVIndex
    have hJump := Row.jump_max hUWHeight.le hWVHeight.le
    intro k hk
    have hEither : k < Row.jump (F.height u) (F.height w) ∨
        k < Row.jump (F.height w) (F.height v) := by omega
    rcases hEither with hFirst | hSecond
    · exact lt_of_lt_of_le (hUW k hFirst)
        (vertical_prefix_le hF.toOrdered hWVHeight hWV k)
    · exact lt_of_le_of_lt (vertical_prefix_le hF.toOrdered hUWHeight hUW k)
        (hWV k hSecond)
termination_by (u.1.val, v.2.val - u.2.val)
decreasing_by
  all_goals omega

/-- The actual complete root vectors are strictly increasing up every
real column. This weaker consequence does not replace the cutoff-sensitive
strong theorem above. -/
theorem Normal.rootVector_strict {F : Frame} (hF : F.Normal) {D : Nat}
    (hSupported : ∀ w : F.Node, ∀ i, D < i → Row.coeff (F.height w) i = 0)
    {u v : F.Node} (hReal : Real u) (hColumn : u.1 = v.1)
    (hIndex : u.2.val < v.2.val) :
    rootVector hF.toOrdered D u < rootVector hF.toOrdered D v := by
  have h := hF.rootVertical hSupported hReal hColumn hIndex
    0 (jump_pos_of_lt (same_column_lt hF.toOrdered hColumn hIndex))
  simpa only [rootPrefix, Row.cut_zero] using h

/-- Literal finite/infinity version of (V), valid for every strictly
increasing column-label assignment. This is the key domain used by Model,
including its universe-one ordinal labels. -/
theorem Normal.truncated_rootKeys_strict {F : Frame} (hF : F.Normal) {D : Nat}
    (hSupported : ∀ w : F.Node, ∀ i, D < i → Row.coeff (F.height w) i = 0)
    {u v : F.Node} (hReal : Real u) (hColumn : u.1 = v.1)
    (hIndex : u.2.val < v.2.val) {k : Nat}
    (hScale : k < Row.jump (F.height u) (F.height v))
    {Label : Type u} [LinearOrder Label] (f : Fin F.width → Label) (hf : StrictMono f) :
    Keys.truncate (fun i : Fin (D + 1) => f (scaleRoot hF.toOrdered (D - i.val) u).1)
        (D + 1 - k) <
      Keys.truncate (fun i : Fin (D + 1) => f (scaleRoot hF.toOrdered (D - i.val) v).1)
        (D + 1 - k) :=
  rootPrefix_lt_truncate hF.toOrdered f hf
    (hF.rootVertical hSupported hReal hColumn hIndex k hScale)

/-- Every finite normal mountain admits a dimension in which the full
strong vertical theorem holds for all pairs of real column nodes. -/
theorem Normal.exists_rootVertical_dimension {F : Frame} (hF : F.Normal) :
    ∃ D : Nat, (∀ w : F.Node, ∀ i, D < i → Row.coeff (F.height w) i = 0) ∧
      ∀ u v : F.Node, Real u → u.1 = v.1 → u.2.val < v.2.val →
        RootVertical hF.toOrdered D u v := by
  obtain ⟨D, hSupported⟩ := F.exists_key_dimension
  exact ⟨D, hSupported, fun _ _ hReal hColumn hIndex =>
    hF.rootVertical hSupported hReal hColumn hIndex⟩

end OmegaY.Geometry.Frame

#print axioms OmegaY.Geometry.Frame.Normal.rootVertical
#print axioms OmegaY.Geometry.Frame.Normal.rootVector_strict
#print axioms OmegaY.Geometry.Frame.Normal.truncated_rootKeys_strict
#print axioms OmegaY.Geometry.Frame.Normal.exists_rootVertical_dimension
