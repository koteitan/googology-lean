/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Geometry/CanonicalRootKeys.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Geometry/CanonicalRootKeys.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Geometry.MountainKeys
import Googology.Notation.OmegaY.WellOrder.OmegaY.Geometry.RowShadow
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.CanonicalFrontier

set_option backward.do.legacy false

/-!
# Scale roots on actual canonical candidate chains

The candidate-root dichotomy follows from actual numerical record-path
compression plus convexity of a high-coefficient block. This avoids
assuming a minimum-value characterization of the roots. Normality below
is only source-frame normality; nothing about copied output is presumed.
-/

namespace OmegaY.Geometry.Frame

theorem ParentPath.scaleRoot_eq {F : Frame} (hF : F.Normal)
    {u p : F.Node} (path : ParentPath F u p) (hReal : Real u) {k : Nat}
    (hBlock : Row.jump (F.height u) (F.height p) ≤ k) :
    scaleRoot hF.toOrdered k u = scaleRoot hF.toOrdered k p := by
  induction path with
  | refl _ => rfl
  | @cons u q p hParent rest ih =>
      have hQReal : Real q := real_of_value_pos hF.toOrdered (P_value hF.toOrdered hParent).1
      have hBetween := Row.jump_le_between (rest.height_le hF.toOrdered)
        (P_height_le hF.toOrdered hParent)
        (by simpa only [Row.jump_comm] using hBlock)
      have hUQ : Row.jump (F.height u) (F.height q) ≤ k := by
        simpa only [Row.jump_comm] using hBetween.2
      have hQP : Row.jump (F.height q) (F.height p) ≤ k := by
        simpa only [Row.jump_comm] using hBetween.1
      exact (scaleRoot_eq_of_raw hF.toOrdered
        ((hF.rawParent_eq_P hReal).trans hParent) hUQ).trans (ih hQReal hQP)

/-- If the current retained edge reaches `p`, the actual numerical record
path from its Q candidate stays in that same high-coefficient block. -/
theorem Normal.scaleRoot_candidate_of_retained {F : Frame} (hF : F.Normal)
    {u q parent : F.Node} (hReal : Real u) (hQ : F.Q u = some q) {k : Nat}
    (hRetained : F.scaleParent k u = some parent) :
    scaleRoot hF.toOrdered k u = scaleRoot hF.toOrdered k q := by
  obtain ⟨hRaw, hBlock⟩ := scaleParent_some_iff.mp hRetained
  have hParent := (hF.rawParent_eq_P hReal).symm.trans hRaw
  obtain ⟨actualQ, hActualQ, trace⟩ := (P_iff hF.toOrdered).mp hParent
  have hEq : actualQ = q := Option.some.inj (hActualQ.symm.trans hQ)
  subst actualQ
  have hQReal := Q_real hF.toOrdered hReal hQ
  have path := trace.parentPath hF.toOrdered (hF.real_positive q hQReal)
  have hBetween := Row.jump_le_between (trace.height_le hF.toOrdered)
    (Q_height_le hF.toOrdered hQ)
    (by simpa only [Row.jump_comm] using hBlock)
  have hQP : Row.jump (F.height q) (F.height parent) ≤ k := by
    simpa only [Row.jump_comm] using hBetween.1
  exact (scaleRoot_eq_of_parent hF.toOrdered hRetained).trans
    (path.scaleRoot_eq hF hQReal hQP).symm

/-- The actual scale root is either this node or the candidate's scale
root. In particular it is not merely an arbitrary earlier column. -/
theorem Normal.scaleRoot_candidate_cases {F : Frame} (hF : F.Normal)
    {u q : F.Node} (hReal : Real u) (hQ : F.Q u = some q) (k : Nat) :
    scaleRoot hF.toOrdered k u = u ∨
      scaleRoot hF.toOrdered k u = scaleRoot hF.toOrdered k q := by
  cases hp : F.scaleParent k u with
  | none => exact Or.inl (scaleRoot_eq_of_none hF.toOrdered hp)
  | some parent => exact Or.inr (hF.scaleRoot_candidate_of_retained hReal hQ hp)

theorem Normal.scaleRoot_candidate_column_le {F : Frame} (hF : F.Normal)
    {u q : F.Node} (hReal : Real u) (hQ : F.Q u = some q) (k : Nat) :
    (scaleRoot hF.toOrdered k q).1.val ≤ (scaleRoot hF.toOrdered k u).1.val := by
  rcases hF.scaleRoot_candidate_cases hReal hQ k with he | he
  · rw [he]
    exact (scaleRoot_column_le hF.toOrdered k q).trans (Q_column_lt hF.toOrdered hQ).le
  · rw [he]

/-- Once the immediate candidate is outside the current high block,
every later numerical candidate is outside it too. -/
theorem Normal.scaleRoot_self_of_candidate_outside {F : Frame} (hF : F.Normal)
    {u q : F.Node} (hReal : Real u) (hQ : F.Q u = some q) {k : Nat}
    (hOutside : k < Row.jump (F.height u) (F.height q)) :
    scaleRoot hF.toOrdered k u = u := by
  cases hp : F.scaleParent k u with
  | none => exact scaleRoot_eq_of_none hF.toOrdered hp
  | some parent =>
      obtain ⟨hRaw, hBlock⟩ := scaleParent_some_iff.mp hp
      have hParent := (hF.rawParent_eq_P hReal).symm.trans hRaw
      obtain ⟨actualQ, hActualQ, trace⟩ := (P_iff hF.toOrdered).mp hParent
      have hEq : actualQ = q := Option.some.inj (hActualQ.symm.trans hQ)
      subst actualQ
      have hBetween := Row.jump_le_between (trace.height_le hF.toOrdered)
        (Q_height_le hF.toOrdered hQ)
        (by simpa only [Row.jump_comm] using hBlock)
      have hInside : Row.jump (F.height u) (F.height q) ≤ k := by
        simpa only [Row.jump_comm] using hBetween.2
      exact (not_lt_of_ge hInside hOutside).elim

end OmegaY.Geometry.Frame

#print axioms OmegaY.Geometry.Frame.ParentPath.scaleRoot_eq
#print axioms OmegaY.Geometry.Frame.Normal.scaleRoot_candidate_cases
#print axioms OmegaY.Geometry.Frame.Normal.scaleRoot_candidate_column_le
#print axioms OmegaY.Geometry.Frame.Normal.scaleRoot_self_of_candidate_outside
