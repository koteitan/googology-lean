/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Geometry/Decrement.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Geometry/Decrement.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Geometry.FatherUpperBound

set_option backward.do.legacy false

/-!
# The two local cases in decrementing a current value

These results concern the actual candidate and numerical-parent relations of
a finite normal frame. Lowering a search threshold by one either retains its
old parent or skips an equal-valued parent and continues at that parent's own
parent. In the latter case the next cell exactly matches the father's upper
cell, including its row, value, and stored left endpoint.

This proves the local seam, not yet the synchronization of the two complete
executable builds or the reproduction of the entire grafted suffix.
-/

namespace OmegaY.Geometry.Frame

/-- Lowering a threshold preserves a hit which still passes the new test. -/
theorem Hit.tighten {F : Frame} {small large : Nat} {q p : F.Node}
    (trace : Hit F large q p) (hle : small ≤ large) (hp : F.value p < small) :
    Hit F small q p := by
  induction trace with
  | here hpos _ => exact .here hpos hp
  | next hreject hQ _ ih =>
    exact .next (fun h => hreject ⟨h.1, lt_of_lt_of_le h.2 hle⟩) hQ (ih hp)

/-- Replace the old first hit by a further search at a smaller threshold.
Every earlier rejected candidate remains rejected. -/
theorem Hit.replace_tail {F : Frame} {small large : Nat} {q p r : F.Node}
    (trace : Hit F large q p) (hle : small ≤ large) (tail : Hit F small p r) :
    Hit F small q r := by
  induction trace with
  | here _ _ => exact tail
  | next hreject hQ _ ih =>
    exact .next (fun h => hreject ⟨h.1, lt_of_lt_of_le h.2 hle⟩) hQ (ih tail)

/-- The first hit at threshold b+1 is either already below b, or has value b.
In the second case threshold b continues along the actual parent of that hit.
The assumption b>1 ensures this second parent exists. -/
theorem decrement_hit_dichotomy {F : Frame} (hF : F.Normal)
    {b : Nat} (hb : 1 < b) {q p : F.Node} (trace : Hit F (b + 1) q p) :
    (F.value p < b ∧ Hit F b q p) ∨
      (F.value p = b ∧ ∃ r, F.P p = some r ∧ Hit F b q r) := by
  have hval := trace.result
  by_cases hsmall : F.value p < b
  · exact Or.inl ⟨hsmall, trace.tighten (Nat.le_succ b) hsmall⟩
  · have heq : F.value p = b := by omega
    have hpval : 1 < F.value p := by omega
    obtain ⟨r, hr⟩ := hF.parent_exists hpval
    obtain ⟨next, hQ, rest⟩ := (P_iff hF.toOrdered).mp hr
    have tail : Hit F b p r := by
      apply Hit.next (fun h => by omega) hQ
      simpa only [heq] using rest
    exact Or.inr ⟨heq, r, hr, trace.replace_tail (Nat.le_succ b) tail⟩

/-- The dichotomy applies to the actual fixed-threshold search starting at
the old child's Q candidate. It does not identify this with the child's P,
whose definition still uses the old, larger value. -/
theorem decrement_search {F : Frame} (hF : F.Normal)
    {u p : F.Node} {b : Nat} (hb : 1 < b) (hu : F.value u = b + 1)
    (hp : F.P u = some p) :
    ∃ r, (F.Q u).bind (F.seek b u.1.val) = some r ∧
      ((r = p ∧ F.value p < b) ∨ (F.value p = b ∧ F.P p = some r)) := by
  obtain ⟨q, hQ, trace⟩ := (P_iff hF.toOrdered).mp hp
  have tr : Hit F (b + 1) q p := by simpa only [hu] using trace
  have hqcol := Q_column_lt hF.toOrdered hQ
  rcases decrement_hit_dichotomy hF hb tr with ⟨hsmall, same⟩ | ⟨heq, r, hr, next⟩
  · refine ⟨p, ?_, Or.inl ⟨rfl, hsmall⟩⟩
    rw [hQ, Option.bind_some]
    exact same.run hF.toOrdered u.1.val hqcol
  · refine ⟨r, ?_, Or.inr ⟨heq, hr⟩⟩
    rw [hQ, Option.bind_some]
    exact next.run hF.toOrdered u.1.val hqcol

/-- At the equal-value seam the recomputed row exactly equals the father's
upper row. The father upper bound is used here in its proved direction. -/
theorem decrement_seam_row {F : Frame} (hF : F.Normal)
    {u p r pplus : F.Node} (hp : F.P u = some p) (hr : F.P p = some r)
    (hplus : F.upper p = some pplus) :
    Row.B (F.height u) (F.height r) = F.height pplus := by
  have hD := father_upper_bound hF hp
    (hF.upper_nontrivial p pplus
      (real_of_value_pos hF.toOrdered (P_value hF.toOrdered hp).1) hplus)
  rw [hF.above_row hp, hF.above_row hr] at hD
  rw [Row.B_max (P_height_le hF.toOrdered hp) (P_height_le hF.toOrdered hr),
    max_eq_right hD]
  exact (hF.above_row hr).symm.trans (aboveHeight_of_upper hplus)

/-- The newly produced seam cell is identical as a Cell, not merely equal
in height. Its own column index is external to Cell and can be different. -/
theorem decrement_seam_cell {F : Frame} (hF : F.Normal)
    {u p r pplus : F.Node} (hp : F.P u = some p) (hr : F.P p = some r)
    (hplus : F.upper p = some pplus) :
    (⟨Row.B (F.height u) (F.height r), F.value p - F.value r,
      some (ref r)⟩ : Canonical.Cell) = F.cell pplus := by
  have hreal := real_of_value_pos hF.toOrdered (P_value hF.toOrdered hp).1
  obtain ⟨s, hs, _hrow, hvalue, hleft⟩ := hF.upper_step p pplus hreal hplus
  have heq : s = r := Option.some.inj (hs.symm.trans hr)
  subst s
  have hrow := decrement_seam_row hF hp hr hplus
  calc
    _ = ⟨F.height pplus, F.value pplus, (F.cell pplus).left⟩ := by
      rw [hrow, hvalue, hleft]
    _ = F.cell pplus := rfl

end OmegaY.Geometry.Frame

#print axioms OmegaY.Geometry.Frame.decrement_hit_dichotomy
#print axioms OmegaY.Geometry.Frame.decrement_search
#print axioms OmegaY.Geometry.Frame.decrement_seam_cell
