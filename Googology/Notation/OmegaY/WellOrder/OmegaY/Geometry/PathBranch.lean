/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Geometry/PathBranch.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Geometry/PathBranch.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Geometry.RowShadow

set_option backward.do.legacy false

/-! Determinism and intermediate-node interfaces for actual numerical
parent paths. Endpoint comparability uses only that `P` is a function.
Column and height consequences require `Ordered`, but never `Normal` or
an assumed copied-output closure property. -/

namespace OmegaY.Geometry.Frame

/-- Two paths from the same node cannot choose distinct next parents.
Their endpoints therefore lie on one ancestry chain. -/
theorem ParentPath.comparable {F : Frame} {u v w : F.Node}
    (first : ParentPath F u v) (second : ParentPath F u w) :
    ParentPath F v w ∨ ParentPath F w v := by
  induction first generalizing w with
  | refl _ => exact Or.inl second
  | @cons u q v hp rest ih =>
    cases second with
    | refl => exact Or.inr (.cons hp rest)
    | @cons _ r _ hq tail =>
      have he : q = r := Option.some.inj (hp.symm.trans hq)
      subst r
      exact ih tail

theorem ParentPath.eq_or_column_lt {F : Frame} (hF : F.Ordered) {u v : F.Node}
    (path : ParentPath F u v) : u = v ∨ v.1.val < u.1.val := by
  cases path with
  | refl _ => exact Or.inl rfl
  | cons hp rest => exact Or.inr ((rest.column_le hF).trans_lt (P_column_lt hF hp))

/-- A nontrivial path strictly changes its column; in particular a path
whose endpoint has the source column must be the reflexive one. -/
theorem ParentPath.eq_of_column_eq {F : Frame} (hF : F.Ordered) {u v : F.Node}
    (path : ParentPath F u v) (hColumn : u.1.val = v.1.val) : u = v := by
  rcases path.eq_or_column_lt hF with he | hlt
  · exact he
  · omega

theorem ParentPath.antisymm {F : Frame} (hF : F.Ordered) {u v : F.Node}
    (first : ParentPath F u v) (second : ParentPath F v u) : u = v :=
  first.eq_of_column_eq hF (Nat.le_antisymm (second.column_le hF) (first.column_le hF))

/-- Among two paths from one source, the endpoint farther to the right
has an actual path to the endpoint farther to the left. This produces the
missing suffix rather than asserting only an order comparison. -/
theorem ParentPath.suffix_of_column_le {F : Frame} (hF : F.Ordered) {u v w : F.Node}
    (toMiddle : ParentPath F u v) (toEnd : ParentPath F u w)
    (hColumn : w.1.val ≤ v.1.val) : ParentPath F v w := by
  rcases toMiddle.comparable toEnd with hForward | hBackward
  · exact hForward
  · have he : w = v := hBackward.eq_of_column_eq hF
      (Nat.le_antisymm hColumn (hBackward.column_le hF))
    rw [he]
    exact .refl _

/-- In a same-height path every intermediate node has that height. The
two supplied paths identify an actual splitting node, so a mere row
occurrence in another column cannot satisfy this interface. -/
theorem ParentPath.height_eq_of_split {F : Frame} (hF : F.Ordered) {u v w : F.Node}
    (before : ParentPath F u v) (after : ParentPath F v w)
    (hHeight : F.height u = F.height w) : F.height v = F.height u := by
  apply le_antisymm (before.height_le hF)
  rw [hHeight]
  exact after.height_le hF

/-- A prefix ending no farther left than the final endpoint is genuinely
inside that same-height path, by determinism. -/
theorem ParentPath.height_eq_of_prefix {F : Frame} (hF : F.Ordered) {u v w : F.Node}
    (whole : ParentPath F u w) (prefixPath : ParentPath F u v)
    (hColumn : w.1.val ≤ v.1.val) (hHeight : F.height u = F.height w) :
    F.height v = F.height u :=
  prefixPath.height_eq_of_split hF (prefixPath.suffix_of_column_le hF whole hColumn) hHeight

end OmegaY.Geometry.Frame

#print axioms OmegaY.Geometry.Frame.ParentPath.comparable
#print axioms OmegaY.Geometry.Frame.ParentPath.suffix_of_column_le
#print axioms OmegaY.Geometry.Frame.ParentPath.height_eq_of_split
#print axioms OmegaY.Geometry.Frame.ParentPath.height_eq_of_prefix
