/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Geometry/RowShadow.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Geometry/RowShadow.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Geometry.RowSupport

set_option backward.do.legacy false

/-!
# Same-row shadows of numerical-parent paths

The witnesses are actual stored nodes and the paths consist of actual `P`
edges. Row support alone would not give these paths. Normality is used only
for the source frame; this module does not assume normality of copied output.
-/

namespace OmegaY.Geometry.Frame

theorem node_eq_of_column_height {F : Frame} (hF : F.Ordered) {u v : F.Node}
    (hc : u.1 = v.1) (hh : F.height u = F.height v) : u = v := by
  rcases u with ⟨c, i⟩
  rcases v with ⟨d, j⟩
  dsimp only at hc
  subst d
  have hij : i = j := (hF.rows_strict c).injective hh
  subst j
  rfl

theorem ParentPath.trans {F : Frame} {u v w : F.Node}
    (first : ParentPath F u v) (second : ParentPath F v w) : ParentPath F u w := by
  induction first with
  | refl _ => exact second
  | cons hp _ ih => exact .cons hp (ih second)

theorem ParentPath.height_le {F : Frame} (hF : F.Ordered) {u v : F.Node}
    (path : ParentPath F u v) : F.height v ≤ F.height u := by
  induction path with
  | refl _ => exact le_rfl
  | cons hp _ ih => exact ih.trans (P_height_le hF hp)

/-- Every real node below the parent has a same-row ancestor path from an
actual node below the child. Endpoint equality and monotonicity of `P`
heights imply that all nodes on this path have this same row. -/
def RowShadow (F : Frame) (u p : F.Node) : Prop :=
  ∀ w : F.Node, Real w → w.1 = p.1 → F.height w ≤ F.height p →
    ∃ v : F.Node, Real v ∧ v.1 = u.1 ∧ F.height v ≤ F.height u ∧
      F.height v = F.height w ∧ ParentPath F v w

theorem RowShadow.refl {F : Frame} (u : F.Node) : RowShadow F u u := by
  intro w hw hc hh
  exact ⟨w, hw, hc, hh, rfl, .refl _⟩

theorem RowShadow.trans {F : Frame} {u v w : F.Node}
    (first : RowShadow F u v) (second : RowShadow F v w) : RowShadow F u w := by
  intro z hz hc hh
  obtain ⟨y, hy, hyc, hyh, hye, hyp⟩ := second z hz hc hh
  obtain ⟨x, hx, hxc, hxh, hxe, hxp⟩ := first y hy hyc hyh
  exact ⟨x, hx, hxc, hxh, hxe.trans hye, hxp.trans hyp⟩

theorem ParentPath.rowShadow_of_left {F : Frame} (hF : F.Ordered) {bound : Nat}
    (ih : ∀ u p : F.Node, u.1.val < bound → F.P u = some p → RowShadow F u p)
    {u p : F.Node} (path : ParentPath F u p) (hu : u.1.val < bound) :
    RowShadow F u p := by
  induction path with
  | refl _ => exact RowShadow.refl _
  | @cons u q p hp rest hrest =>
    exact (ih u q hu hp).trans (hrest ((P_column_lt hF hp).trans hu))

theorem real_lower_of_height_lt {F : Frame} (hF : F.Ordered)
    {u w : F.Node} (hw : Real w) (hh : F.height w < F.height u) :
    ∃ v : F.Node, Real v ∧ F.upper v = some u ∧ v.1 = u.1 ∧
      v.2.val < u.2.val := by
  have hui : 1 < u.2.val := by
    by_contra hn
    have hlen := hF.length_ge_two u.1
    have hle : u.2 ≤ (⟨1, by omega⟩ : Fin (F.length u.1)) := by
      change u.2.val ≤ 1
      omega
    have hrow := (hF.rows_strict u.1).monotone hle
    have hbottom := hF.bottom_row u.1 (by omega)
    have hwrow := one_le_height hF hw
    change F.height u ≤ (F.cells u.1 ⟨1, by omega⟩).row at hrow
    rw [hbottom] at hrow
    exact not_lt_of_ge (hwrow.trans' hrow) hh
  let v : F.Node := ⟨u.1, ⟨u.2.val - 1, by have := u.2.isLt; omega⟩⟩
  refine ⟨v, by unfold Real; dsimp [v]; omega, ?_, rfl, by dsimp [v]; omega⟩
  have he : u.2.val - 1 + 1 = u.2.val := by omega
  simp [upper, v, he, u.2.isLt]

theorem height_le_lower_of_lt_upper {F : Frame} (hF : F.Ordered)
    {p q w : F.Node} (hUpper : F.upper p = some q) (hc : w.1 = q.1)
    (hh : F.height w < F.height q) : F.height w ≤ F.height p := by
  obtain ⟨hcol, hindex⟩ := upper_spec hUpper
  rcases w with ⟨c, i⟩
  have hcp : c = p.1 := hc.trans hcol
  subst c
  have hile : i ≤ p.2 := by
    by_contra hn
    have hiq : q.2.val ≤ i.val := by change ¬ i.val ≤ p.2.val at hn; omega
    have hqh : F.height q ≤ F.height ⟨p.1, i⟩ := by
      rcases q with ⟨c, j⟩
      dsimp only at hcol
      subst c
      exact (hF.rows_strict p.1).monotone hiq
    exact not_lt_of_ge hqh hh
  exact (hF.rows_strict p.1).monotone hile

/-- Same-row ancestry, by source-column induction and then bottom-up node
induction. The only vertical candidate step used is the established
`candidate_after_upper` theorem on the canonical source frame. -/
theorem P_rowShadow {F : Frame} (hF : F.Normal) {u p : F.Node}
    (hp : F.P u = some p) : RowShadow F u p := by
  generalize hc : u.1.val = c
  induction c using Nat.strongRecOn generalizing u p with
  | ind c outer =>
    generalize hi : u.2.val = i
    induction i using Nat.strongRecOn generalizing u p with
    | ind i inner =>
      intro w hw hwc hwh
      have hwle : F.height w ≤ F.height u := hwh.trans (P_height_le hF.toOrdered hp)
      rcases lt_or_eq_of_le hwle with hwlt | hweq
      · obtain ⟨v, hv, hvu, hvc, hvi⟩ := real_lower_of_height_lt hF.toOrdered hw hwlt
        obtain ⟨oldParent, hold, _⟩ := hF.upper_step v u hv hvu
        obtain ⟨q, hQ, trace⟩ := (P_iff hF.toOrdered).mp hp
        have hureal := real_of_value_pos hF.toOrdered
          ((P_value hF.toOrdered hp).1.trans (P_value hF.toOrdered hp).2)
        have path := trace.parentPath hF.toOrdered
          (hF.real_positive q (Q_real hF.toOrdered hureal hQ))
        have hqleft : q.1.val < c := by simpa [hc] using Q_column_lt hF.toOrdered hQ
        have hshadow := path.rowShadow_of_left hF.toOrdered
          (fun a b ha hab => outer a.1.val ha hab rfl) hqleft
        obtain ⟨z, hz, hzc, hzh, hze, hzp⟩ := hshadow w hw hwc hwh
        have hzOld : z.1 = oldParent.1 ∧ F.height z ≤ F.height oldParent := by
          rcases candidate_after_upper hF hold hvu with hsame | ⟨up, hup, huph, hqup⟩
          · have he : q = oldParent := Option.some.inj (hQ.symm.trans hsame)
            exact ⟨hzc.trans (congrArg Sigma.fst he), he ▸ hzh⟩
          · have he : q = up := Option.some.inj (hQ.symm.trans hqup)
            have hzup : z.1 = up.1 := hzc.trans (congrArg Sigma.fst he)
            have hzlt : F.height z < F.height up := by rw [hze, huph]; exact hwlt
            exact ⟨hzup.trans (upper_spec hup).1,
              height_le_lower_of_lt_upper hF.toOrdered hup hzup hzlt⟩
        have hvc' : v.1.val = c := by rw [hvc, hc]
        obtain ⟨x, hx, hxc, hxh, hxe, hxp⟩ :=
          inner v.2.val (by omega) hold hvc' rfl z hz hzOld.1 hzOld.2
        have hvle : F.height v ≤ F.height u := by
          obtain ⟨huvc, huvindex⟩ := upper_spec hvu
          rcases u with ⟨cc, ii⟩
          dsimp only at huvc
          subst cc
          change ii.val = v.2.val + 1 at huvindex
          exact (hF.rows_strict v.1).monotone (by change v.2.val ≤ ii.val; omega)
        exact ⟨x, hx, hxc.trans hvc, hxh.trans hvle, hxe.trans hze, hxp.trans hzp⟩
      · have hwp : w = p := node_eq_of_column_height hF.toOrdered hwc
          (le_antisymm hwh (by rw [hweq]; exact P_height_le hF.toOrdered hp))
        have hureal := real_of_value_pos hF.toOrdered
          ((P_value hF.toOrdered hp).1.trans (P_value hF.toOrdered hp).2)
        refine ⟨u, hureal, rfl, le_rfl, hweq.symm, ?_⟩
        rw [hwp]
        exact .cons hp (.refl _)

theorem ParentPath.rowShadow {F : Frame} (hF : F.Normal) {u p : F.Node}
    (path : ParentPath F u p) : RowShadow F u p := by
  induction path with
  | refl _ => exact RowShadow.refl _
  | cons hp _ ih => exact (P_rowShadow hF hp).trans ih

#print axioms P_rowShadow
#print axioms ParentPath.rowShadow

end OmegaY.Geometry.Frame
