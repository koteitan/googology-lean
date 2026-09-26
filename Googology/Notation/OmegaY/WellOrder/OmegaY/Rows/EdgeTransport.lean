/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Rows/EdgeTransport.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Rows/EdgeTransport.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Rows.Lift

set_option backward.do.legacy false

/-!
# Row formulas for the three endpoint-transport cases

These are arithmetic implications only.  The separate mountain-geometry
argument must establish which interval case applies to each actual edge.
-/

namespace OmegaY.Row

theorem B_le_cap_of_same_interval {root a b : Row} {e : Nat}
    (hra : root ≤ a) (ha : a < bump root e)
    (hrb : root ≤ b) (hb : b < bump root e) : B a b ≤ bump root e := by
  have hj := jump_le_of_same_interval hra ha hrb hb
  have hroot : jump a root ≤ e := by
    rw [jump_comm]
    exact jump_le_of_lt_bump hra ha
  calc
    B a b ≤ bump a e := bump_mono_exponent a hj
    _ = bump root e := bump_eq_of_jump_le hroot

/-- An edge leaving the lift interval keeps its original upper row when its
father is at or below the root and that father is held fixed. -/
theorem B_lift_fixed_parent {root t a b : Row} {e : Nat}
    (ht : root ≤ t) (htc : t < bump root e)
    (ha : root ≤ a) (hac : a < bump root e)
    (hb : b ≤ root) (hcap : bump root e ≤ B a b) :
    B (lift root t a) b = B a b := by
  have ha' := lift_mem_interval ht htc ha hac
  have haa' := lift_ge_source ht ha
  rw [B_max haa' (hb.trans ha)]
  exact max_eq_right ((B_le_cap_of_same_interval ha'.1 ha'.2 ha hac).trans hcap)

theorem lift_B_fixed_parent {root t a b : Row} {e : Nat}
    (ht : root ≤ t) (htc : t < bump root e)
    (ha : root ≤ a) (hac : a < bump root e)
    (hb : b ≤ root) (hcap : bump root e ≤ B a b) :
    lift root t (B a b) = B (lift root t a) b := by
  rw [lift_eq_of_ge_cap ht htc hcap, B_lift_fixed_parent ht htc ha hac hb hcap]

/-- Moving a father inside an interval lying entirely below the unchanged
child does not change the edge's next-row formula. -/
theorem B_fixed_child_lift_parent {root t a b : Row} {e : Nat}
    (ht : root ≤ t) (htc : t < bump root e)
    (hb : root ≤ b) (hbc : b < bump root e) (ha : bump root e ≤ a) :
    B a (lift root t b) = B a b := by
  have hb' := lift_mem_interval ht htc hb hbc
  have hbb' := lift_ge_source ht hb
  have hb'a : lift root t b ≤ a := (le_of_lt hb'.2).trans ha
  have hsmall : B (lift root t b) b ≤ B a (lift root t b) :=
    (B_le_cap_of_same_interval hb'.1 hb'.2 hb hbc).trans
      (ha.trans (le_of_lt (lt_B a (lift root t b))))
  rw [B_max hb'a hbb', max_eq_left hsmall]

end OmegaY.Row

#print axioms OmegaY.Row.B_lift_fixed_parent
#print axioms OmegaY.Row.lift_B_fixed_parent
#print axioms OmegaY.Row.B_fixed_child_lift_parent
