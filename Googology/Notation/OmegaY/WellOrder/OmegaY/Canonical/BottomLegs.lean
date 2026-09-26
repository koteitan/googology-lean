/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Canonical/BottomLegs.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Canonical/BottomLegs.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.Values

set_option backward.do.legacy false

/-! The stored left leg of each actual bottom cell is exactly the preceding
column's phantom (and absent in column zero).  This is proved for successful
executions; there is no geometric or parent-search assumption. -/

namespace OmegaY.Canonical

def BottomLegs (mountain : Mountain) : Prop :=
  ∀ c (hc : c < mountain.size), ∃ bottom : Cell,
    mountain[c][1]? = some bottom ∧
    bottom.left = if c = 0 then none else some ⟨c - 1, 0⟩

theorem bottomLegs_empty : BottomLegs #[] := by
  intro c hc
  simp at hc

theorem BottomLegs.push {mountain : Mountain} {column : Column} {value : Nat}
    (hLegs : BottomLegs mountain) (hBuild : buildColumn mountain value = .ok column) :
    BottomLegs (mountain.push column) := by
  intro c hc
  by_cases he : c = mountain.size
  · subst c
    refine ⟨initialBottom mountain.size value, ?_, rfl⟩
    simpa only [Array.getElem_push_eq] using buildColumn_bottom hBuild
  · have hOld : c < mountain.size := by simp only [Array.size_push] at hc; omega
    simpa only [Array.getElem_push_lt hOld] using hLegs c hOld

theorem buildFrom_bottom_legs {mountain result : Mountain} {values : List Nat}
    (hLegs : BottomLegs mountain) (hBuild : buildFrom mountain values = .ok result) :
    BottomLegs result := by
  induction values generalizing mountain with
  | nil =>
      have he : mountain = result := by simpa only [buildFrom, Except.ok.injEq] using hBuild
      exact he ▸ hLegs
  | cons value rest ih =>
      cases hb : buildColumn mountain value with
      | error e => simp [buildFrom, hb] at hBuild
      | ok column =>
          apply ih (hLegs.push hb)
          simpa only [buildFrom, hb, except_bind_ok] using hBuild

theorem build_bottom_legs {values : List Nat} {mountain : Mountain}
    (hBuild : build values = .ok mountain) : BottomLegs mountain :=
  buildFrom_bottom_legs bottomLegs_empty (buildFrom_of_build hBuild)

/-- A typed-array version usable directly with `Frame.Ordered`. -/
theorem build_bottom_left {values : List Nat} {mountain : Mountain}
    (hBuild : build values = .ok mountain) (c : Fin mountain.size)
    (hi : 1 < (Geometry.Frame.ofMountain mountain).length c) :
    ((Geometry.Frame.ofMountain mountain).cells c ⟨1, hi⟩).left =
      if c.val = 0 then none else some ⟨c.val - 1, 0⟩ := by
  obtain ⟨bottom, hRead, hLeft⟩ := build_bottom_legs hBuild c.val c.isLt
  have hi' : 1 < mountain[c.val].size := hi
  have hCell : mountain[c.val][1] = bottom := by
    simpa only [Array.getElem?_eq_getElem hi', Option.some.injEq] using hRead
  change mountain[c.val][1].left = _
  rw [hCell]
  exact hLeft

end OmegaY.Canonical

#print axioms OmegaY.Canonical.build_bottom_legs
#print axioms OmegaY.Canonical.build_bottom_left
