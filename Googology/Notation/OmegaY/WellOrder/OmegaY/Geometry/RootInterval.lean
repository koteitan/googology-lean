/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Geometry/RootInterval.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Geometry/RootInterval.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Geometry.RowShadow

set_option backward.do.legacy false

/-!
# Parent closure and exit barriers inside a root interval

All cones below use actual numerical-parent paths at the root's own row.
Rows are sparse: no interval-continuity assumption is made. The root upper
barrier is an explicit source-side hypothesis; output normality is not used.
-/

namespace OmegaY.Geometry.Frame

def RootCone (F : Frame) (root u : F.Node) : Prop :=
  ∃ low : F.Node, Real low ∧ low.1 = u.1 ∧
    F.height low = F.height root ∧ ParentPath F low root

def RootInterval (F : Frame) (root : F.Node) (cap : Row) (u : F.Node) : Prop :=
  RootCone F root u ∧ F.height root ≤ F.height u ∧ F.height u < cap

def BeforeRoot (F : Frame) (root u : F.Node) : Prop :=
  u.1.val < root.1.val ∧ F.height u < F.height root

theorem RootCone.same_column {F : Frame} {root u v : F.Node}
    (hu : RootCone F root u) (hc : u.1 = v.1) : RootCone F root v := by
  obtain ⟨low, hl, hlc, hlh, hlp⟩ := hu
  exact ⟨low, hl, hlc.trans hc, hlh, hlp⟩

theorem RootCone.column_le {F : Frame} (hF : F.Ordered) {root u : F.Node}
    (hu : RootCone F root u) : root.1.val ≤ u.1.val := by
  obtain ⟨low, _, hc, _, path⟩ := hu
  simpa only [hc] using path.column_le hF

theorem BeforeRoot.not_in_interval {F : Frame} {root u : F.Node} {cap : Row}
    (hu : BeforeRoot F root u) : ¬ RootInterval F root cap u := by
  intro h
  exact not_lt_of_ge h.2.1 hu.2

theorem ParentPath.first_exit {F : Frame} {inside : F.Node → Prop} {u p : F.Node}
    (path : ParentPath F u p) (hu : inside u) (hp : ¬ inside p) :
    ∃ z r : F.Node, ParentPath F u z ∧ F.P z = some r ∧
      ParentPath F r p ∧ inside z ∧ ¬ inside r := by
  induction path with
  | refl _ => exact False.elim (hp hu)
  | @cons u q p hq rest ih =>
    by_cases hqi : inside q
    · obtain ⟨z, r, hpre, hedge, hpost, hz, hr⟩ := ih hqi hp
      exact ⟨z, r, .cons hq hpre, hedge, hpost, hz, hr⟩
    · exact ⟨u, q, .refl _, hq, rest, hu, hqi⟩

theorem B_subinterval {a z r p : Row} (hza : z ≤ a) (hrz : r ≤ z) (hpr : p ≤ r) :
    Row.B z r ≤ Row.B a p := by
  rw [Row.B_max hza (hpr.trans hrz), Row.B_max hrz hpr]
  exact (le_max_left _ _).trans (le_max_right _ _)

/-- Transfer the first actual exit on a left-column record path to its end.
The exit barrier persists even if further parent records are skipped. -/
theorem ParentPath.root_interval_exit {F : Frame} (hF : F.Normal)
    {root u q p : F.Node} {cap : Row}
    (ih : ∀ z r : F.Node, z.1.val < u.1.val → F.P z = some r →
      RootInterval F root cap z →
      RootInterval F root cap r ∨
        (BeforeRoot F root r ∧ cap ≤ F.aboveHeight z))
    (path : ParentPath F q p) (hqleft : q.1.val < u.1.val)
    (hqh : F.height q ≤ F.height u) (hq : RootInterval F root cap q)
    (hp : ¬ RootInterval F root cap p) :
    BeforeRoot F root p ∧ cap ≤ Row.B (F.height u) (F.height p) := by
  obtain ⟨z, r, hpre, hedge, hpost, hz, hr⟩ := path.first_exit hq hp
  have hzleft := (hpre.column_le hF.toOrdered).trans_lt hqleft
  rcases ih z r hzleft hedge hz with hri | ⟨hre, hbarrier⟩
  · exact False.elim (hr hri)
  · refine ⟨⟨(hpost.column_le hF.toOrdered).trans_lt hre.1,
        (hpost.height_le hF.toOrdered).trans_lt hre.2⟩, ?_⟩
    rw [hF.above_row hedge] at hbarrier
    exact hbarrier.trans (B_subinterval
      ((hpre.height_le hF.toOrdered).trans hqh)
      (P_height_le hF.toOrdered hedge) (hpost.height_le hF.toOrdered))

/-- Internal parents stay in the same root cone, or exit both below and to
the left of the root. Every such exit has its upper endpoint at the cap or
above. This is proved simultaneously by column and node-index induction. -/
theorem root_interval_parent {F : Frame} (hF : F.Normal)
    {root : F.Node} {cap : Row} (hRootReal : Real root)
    (hCap : Row.bump (F.height root) 0 < cap)
    (hRootBarrier : ∀ upper, F.upper root = some upper → cap ≤ F.height upper)
    {u p : F.Node} (hp : F.P u = some p) (hu : RootInterval F root cap u) :
    RootInterval F root cap p ∨ (BeforeRoot F root p ∧ cap ≤ F.aboveHeight u) := by
  generalize hc : u.1.val = c
  induction c using Nat.strongRecOn generalizing u p with
  | ind c outer =>
    generalize hi : u.2.val = i
    induction i using Nat.strongRecOn generalizing u p with
    | ind i inner =>
      rcases lt_or_eq_of_le hu.2.1 with hHigher | hAtRoot
      · obtain ⟨v, hv, hvu, hvc, hvi⟩ :=
          real_lower_of_height_lt hF.toOrdered hRootReal hHigher
        obtain ⟨low, hl, hlc, hlh, hlp⟩ := hu.1
        have hlv : F.height low ≤ F.height v :=
          height_le_lower_of_lt_upper hF.toOrdered hvu hlc (hlh ▸ hHigher)
        have hvuHeight : F.height v < F.height u := by
          obtain ⟨hcuv, hiuv⟩ := upper_spec hvu
          rcases u with ⟨cc, ii⟩
          dsimp only at hcuv
          subst cc
          change ii.val = v.2.val + 1 at hiuv
          exact hF.rows_strict v.1 (by change v.2.val < ii.val; omega)
        have hvInside : RootInterval F root cap v :=
          ⟨RootCone.same_column hu.1 hvc.symm, hlh ▸ hlv, hvuHeight.trans hu.2.2⟩
        obtain ⟨qold, hold, _⟩ := hF.upper_step v u hv hvu
        have hvc' : v.1.val = c := by rw [hvc, hc]
        have hqold : RootInterval F root cap qold := by
          rcases inner v.2.val (by omega) hold hvInside hvc' rfl with hq | ⟨_, hb⟩
          · exact hq
          · rw [aboveHeight_of_upper hvu] at hb
            exact False.elim (not_lt_of_ge hb hu.2.2)
        obtain ⟨q, hQ, trace⟩ := (P_iff hF.toOrdered).mp hp
        have hq : RootInterval F root cap q := by
          rcases candidate_after_upper hF hold hvu with hsame | ⟨qplus, hplus, he, hsame⟩
          · have heq : q = qold := Option.some.inj (hQ.symm.trans hsame)
            exact heq ▸ hqold
          · have heq : q = qplus := Option.some.inj (hQ.symm.trans hsame)
            subst q
            exact ⟨RootCone.same_column hqold.1 (upper_spec hplus).1.symm,
              he ▸ hu.2.1, he ▸ hu.2.2⟩
        by_cases hpInside : RootInterval F root cap p
        · exact Or.inl hpInside
        · have hureal := real_of_value_pos hF.toOrdered
            ((P_value hF.toOrdered hp).1.trans (P_value hF.toOrdered hp).2)
          have path := trace.parentPath hF.toOrdered
            (hF.real_positive q (Q_real hF.toOrdered hureal hQ))
          obtain ⟨hBefore, hBarrier⟩ := path.root_interval_exit hF
            (fun z r hz hr hzi => outer z.1.val (by omega) hr hzi rfl)
            (Q_column_lt hF.toOrdered hQ) (Q_height_le hF.toOrdered hQ) hq hpInside
          exact Or.inr ⟨hBefore, (hF.above_row hp).symm ▸ hBarrier⟩
      · obtain ⟨low, hl, hlc, hlh, path⟩ := hu.1
        have hlu : low = u := node_eq_of_column_height hF.toOrdered hlc (hlh.trans hAtRoot)
        subst low
        cases path with
        | refl root =>
          obtain ⟨upper, hUpper⟩ := hF.upper_of_parent hp
          have hBarrier : cap ≤ F.aboveHeight root := by
            rw [aboveHeight_of_upper hUpper]
            exact hRootBarrier upper hUpper
          have hParentHeight : F.height p < F.height root := by
            rcases lt_or_eq_of_le (P_height_le hF.toOrdered hp) with hlt | heq
            · exact hlt
            · rw [hF.above_row hp, heq, Row.B_self] at hBarrier
              exact False.elim (not_lt_of_ge hBarrier hCap)
          exact Or.inr ⟨⟨P_column_lt hF.toOrdered hp, hParentHeight⟩, hBarrier⟩
        | @cons u next root hNext rest =>
          have heq : next = p := Option.some.inj (hNext.symm.trans hp)
          subst next
          have hpreal := real_of_value_pos hF.toOrdered (P_value hF.toOrdered hp).1
          have hpheight : F.height p = F.height root := le_antisymm
            ((P_height_le hF.toOrdered hp).trans hAtRoot.ge)
            (rest.height_le hF.toOrdered)
          exact Or.inl ⟨⟨p, hpreal, rfl, hpheight, rest⟩,
            hpheight.ge, hpheight ▸ (hAtRoot ▸ hu.2.2)⟩

/-- If the actual upper endpoint is still below the cap, its parent has
the root row in its column and belongs to the same same-row descendant cone. -/
theorem root_interval_internal_parent {F : Frame} (hF : F.Normal)
    {root : F.Node} {cap : Row} (hRootReal : Real root)
    (hCap : Row.bump (F.height root) 0 < cap)
    (hRootBarrier : ∀ upper, F.upper root = some upper → cap ≤ F.height upper)
    {u p upper : F.Node} (hp : F.P u = some p) (hu : RootInterval F root cap u)
    (hUpper : F.upper u = some upper) (hInside : F.height upper < cap) :
    RootInterval F root cap p := by
  rcases root_interval_parent hF hRootReal hCap hRootBarrier hp hu with h | ⟨_, hb⟩
  · exact h
  · rw [aboveHeight_of_upper hUpper] at hb
    exact False.elim (not_lt_of_ge hb hInside)

/-- Inside the interval, a parent at or right of the root cannot skip the
root row. This conclusion requires the child interval hypothesis. -/
theorem root_interval_parent_iff_column {F : Frame} (hF : F.Normal)
    {root : F.Node} {cap : Row} (hRootReal : Real root)
    (hCap : Row.bump (F.height root) 0 < cap)
    (hRootBarrier : ∀ upper, F.upper root = some upper → cap ≤ F.height upper)
    {u p : F.Node} (hp : F.P u = some p) (hu : RootInterval F root cap u) :
    RootInterval F root cap p ↔ root.1.val ≤ p.1.val := by
  constructor
  · intro hi
    exact RootCone.column_le hF.toOrdered hi.1
  · intro hc
    rcases root_interval_parent hF hRootReal hCap hRootBarrier hp hu with hi | ⟨he, _⟩
    · exact hi
    · exact False.elim (not_lt_of_ge hc he.1)

theorem root_interval_parent_iff_height {F : Frame} (hF : F.Normal)
    {root : F.Node} {cap : Row} (hRootReal : Real root)
    (hCap : Row.bump (F.height root) 0 < cap)
    (hRootBarrier : ∀ upper, F.upper root = some upper → cap ≤ F.height upper)
    {u p : F.Node} (hp : F.P u = some p) (hu : RootInterval F root cap u) :
    RootInterval F root cap p ↔ F.height root ≤ F.height p := by
  constructor
  · exact fun hi => hi.2.1
  · intro hh
    rcases root_interval_parent hF hRootReal hCap hRootBarrier hp hu with hi | ⟨he, _⟩
    · exact hi
    · exact False.elim (not_lt_of_ge hh he.2)

theorem root_interval_parent_bump {F : Frame} (hF : F.Normal)
    {root : F.Node} {degree : Nat} (hRootReal : Real root) (hDegree : 0 < degree)
    (hRootBarrier : ∀ upper, F.upper root = some upper →
      Row.bump (F.height root) degree ≤ F.height upper)
    {u p : F.Node} (hp : F.P u = some p)
    (hu : RootInterval F root (Row.bump (F.height root) degree) u) :
    RootInterval F root (Row.bump (F.height root) degree) p ∨
      (BeforeRoot F root p ∧ Row.bump (F.height root) degree ≤ F.aboveHeight u) :=
  root_interval_parent hF hRootReal
    (Row.bump_strictMono_exponent (F.height root) hDegree) hRootBarrier hp hu

#print axioms root_interval_parent
#print axioms root_interval_internal_parent
#print axioms root_interval_parent_iff_column
#print axioms root_interval_parent_bump

end OmegaY.Geometry.Frame
