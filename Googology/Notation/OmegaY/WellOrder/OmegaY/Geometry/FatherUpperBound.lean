/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Geometry/FatherUpperBound.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Geometry/FatherUpperBound.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Geometry.Frame

set_option backward.do.legacy false

/-!
# Father upper-neighbour bound for finite canonical frames

The local certificate below states the actual adjacent difference rule and
the value-one stopping rule. The cross-column upper bound is a theorem proved
by strong induction on the source column, using a separately proved record
path compression. It is not included in the certificate.

Connecting `Normal` to every successful executable build is a separate
invariant-preservation task; this module does not assert that bridge.
-/

namespace OmegaY.Geometry.Frame

/-- Exact local construction rules for all real adjacent cells. -/
structure Normal (F : Frame) : Prop extends Ordered F where
  upper_exists : ∀ u, Real u → 1 < F.value u → ∃ v, F.upper u = some v
  upper_nontrivial : ∀ u v, Real u → F.upper u = some v → 1 < F.value u
  upper_step : ∀ u v, Real u → F.upper u = some v →
    ∃ p, F.P u = some p ∧ F.height v = Row.B (F.height u) (F.height p) ∧
      F.value v = F.value u - F.value p ∧ (F.cell v).left = some (ref p)

inductive ParentPath (F : Frame) : F.Node → F.Node → Prop
  | refl (u : F.Node) : ParentPath F u u
  | cons {u q p : F.Node} (hp : F.P u = some q) (rest : ParentPath F q p) :
      ParentPath F u p

/-- A first threshold hit is reached by numerical-parent records, allowing
zero records when the starting candidate is already the hit. -/
theorem Hit.parentPath {F : Frame} (hF : F.Ordered) {threshold : Nat}
    {q p : F.Node} (hpos : 0 < F.value q) (trace : Hit F threshold q p) :
    ParentPath F q p := by
  generalize hc : q.1.val = c
  induction c using Nat.strongRecOn generalizing q with
  | ind c ih =>
    cases trace with
    | here _ _ => exact .refl _
    | @next q next p hreject hQ rest =>
      have hthreshold : threshold ≤ F.value q := by
        by_contra hn
        exact hreject ⟨hpos, Nat.lt_of_not_ge hn⟩
      obtain ⟨r, wide, tail⟩ := rest.loosen hthreshold
      have hparent : F.P q = some r := (P_iff hF).mpr ⟨next, hQ, wide⟩
      have hrcol : r.1.val < c := by simpa [hc] using P_column_lt hF hparent
      exact .cons hparent (ih r.1.val hrcol (P_value hF hparent).1 tail rfl)

theorem ParentPath.value_le {F : Frame} (hF : F.Ordered) {q p : F.Node}
    (path : ParentPath F q p) : F.value p ≤ F.value q := by
  induction path with
  | refl _ => exact le_rfl
  | cons hp _ ih => exact ih.trans (P_value hF hp).2.le

theorem ParentPath.column_le {F : Frame} (hF : F.Ordered) {q p : F.Node}
    (path : ParentPath F q p) : p.1.val ≤ q.1.val := by
  induction path with
  | refl _ => exact le_rfl
  | cons hp _ ih => exact ih.trans (P_column_lt hF hp).le

theorem Normal.parent_exists {F : Frame} (hF : F.Normal) {u : F.Node}
    (hu : 1 < F.value u) : ∃ p, F.P u = some p := by
  have hreal := real_of_value_pos hF.toOrdered (Nat.zero_lt_of_lt hu)
  obtain ⟨v, hv⟩ := hF.upper_exists u hreal hu
  obtain ⟨p, hp, _⟩ := hF.upper_step u v hreal hv
  exact ⟨p, hp⟩

theorem Normal.upper_of_parent {F : Frame} (hF : F.Normal) {u p : F.Node}
    (hp : F.P u = some p) : ∃ v, F.upper u = some v := by
  have hvalues := P_value hF.toOrdered hp
  have hu : 1 < F.value u := by omega
  exact hF.upper_exists u (real_of_value_pos hF.toOrdered (by omega)) hu

theorem Normal.above_row {F : Frame} (hF : F.Normal) {u p : F.Node}
    (hp : F.P u = some p) : F.aboveHeight u = Row.B (F.height u) (F.height p) := by
  obtain ⟨v, hv⟩ := hF.upper_of_parent hp
  have hvalues := P_value hF.toOrdered hp
  have hreal := real_of_value_pos hF.toOrdered (Nat.lt_trans hvalues.1 hvalues.2)
  obtain ⟨r, hr, hrow, _⟩ := hF.upper_step u v hreal hv
  have he : r = p := Option.some.inj (hr.symm.trans hp)
  rw [aboveHeight_of_upper hv, hrow, he]

/-- Transport already proved strict-left column bounds along an actual P path.
The only induction hypothesis parameter is restricted to columns below `c`. -/
theorem ParentPath.above_le_of_left_induction {F : Frame} (hF : F.Ordered)
    {c : Nat}
    (ih : ∀ u p : F.Node, u.1.val < c → F.P u = some p → 1 < F.value p →
      F.aboveHeight u ≤ F.aboveHeight p)
    {q p : F.Node} (path : ParentPath F q p) (hleft : q.1.val < c)
    (hp : 1 < F.value p) : F.aboveHeight q ≤ F.aboveHeight p := by
  induction path with
  | refl _ => exact le_rfl
  | @cons u q p hu rest hrest =>
    have hq : 1 < F.value q := lt_of_lt_of_le hp (rest.value_le hF)
    have hqleft := Nat.lt_trans (P_column_lt hF hu) hleft
    exact (ih u q hleft hu hq).trans (hrest hqleft hp)

/-- Lemma D: the father upper neighbour is never below the child upper
neighbour. Only strictly earlier columns are used in the induction. -/
theorem father_upper_bound {F : Frame} (hF : F.Normal) {u p : F.Node}
    (hp : F.P u = some p) (hpval : 1 < F.value p) :
    F.aboveHeight u ≤ F.aboveHeight p := by
  generalize hc : u.1.val = c
  induction c using Nat.strongRecOn generalizing u p with
  | ind c ih =>
    obtain ⟨q, hQ, trace⟩ := (P_iff hF.toOrdered).mp hp
    have hvalues := P_value hF.toOrdered hp
    have hureal := real_of_value_pos hF.toOrdered (Nat.lt_trans hvalues.1 hvalues.2)
    have hqreal := Q_real hF.toOrdered hureal hQ
    have path := trace.parentPath hF.toOrdered (hF.real_positive q hqreal)
    have hqval : 1 < F.value q := lt_of_lt_of_le hpval (path.value_le hF.toOrdered)
    obtain ⟨qplus, hqplus⟩ := hF.upper_exists q hqreal hqval
    have hqhigh : F.height u < F.aboveHeight q := by
      rw [aboveHeight_of_upper hqplus]
      exact Q_upper_gt hF.toOrdered hQ hqplus
    have hqleft : q.1.val < c := by simpa [hc] using Q_column_lt hF.toOrdered hQ
    have hchain : F.aboveHeight q ≤ F.aboveHeight p :=
      path.above_le_of_left_induction hF.toOrdered
        (fun x y hx hxy hy => ih x.1.val hx hxy hy rfl) hqleft hpval
    have huph : F.height u < F.aboveHeight p := lt_of_lt_of_le hqhigh hchain
    obtain ⟨r, hr⟩ := hF.parent_exists hpval
    rw [hF.above_row hp, hF.above_row hr]
    apply Row.interval_bound (P_height_le hF.toOrdered hp)
    simpa only [hF.above_row hr] using huph

/-- A version naming the actual adjacent nodes instead of the total helper. -/
theorem father_upper_bound_nodes {F : Frame} (hF : F.Normal)
    {u p uplus pplus : F.Node} (hp : F.P u = some p)
    (huplus : F.upper u = some uplus) (hpplus : F.upper p = some pplus) :
    F.height uplus ≤ F.height pplus := by
  have hpreal := real_of_value_pos hF.toOrdered (P_value hF.toOrdered hp).1
  have h := father_upper_bound hF hp (hF.upper_nontrivial p pplus hpreal hpplus)
  simpa only [aboveHeight_of_upper huplus, aboveHeight_of_upper hpplus] using h

/-- At an upper cell, the actual candidate climbs from the stored father
either zero vertical edges or exactly one edge ending at the current height. -/
theorem candidate_after_upper {F : Frame} (hF : F.Normal)
    {u p v : F.Node} (hp : F.P u = some p) (hv : F.upper u = some v) :
    F.Q v = some p ∨
      ∃ pplus, F.upper p = some pplus ∧ F.height pplus = F.height v ∧
        F.Q v = some pplus := by
  have hvalues := P_value hF.toOrdered hp
  have hureal := real_of_value_pos hF.toOrdered (Nat.lt_trans hvalues.1 hvalues.2)
  obtain ⟨r, hr, _, _, hleft⟩ := hF.upper_step u v hureal hv
  have he : r = p := Option.some.inj (hr.symm.trans hp)
  subst r
  have hrow : F.height p ≤ F.height v := by
    have hlt : F.height u < F.height v := by
      rw [← aboveHeight_of_upper hv, hF.above_row hp]
      exact Row.lt_B _ _
    exact (P_height_le hF.toOrdered hp).trans hlt.le
  cases hpp : F.upper p with
  | none =>
    exact Or.inl (Q_eq_left_of_barrier hF.toOrdered hleft hrow (by
      intro w hw
      rw [hpp] at hw
      cases hw))
  | some pplus =>
    have hD := father_upper_bound_nodes hF hp hv hpp
    rcases lt_or_eq_of_le hD with hlt | heq
    · refine Or.inl (Q_eq_left_of_barrier hF.toOrdered hleft hrow ?_)
      intro w hw
      have hew : w = pplus := Option.some.inj (hw.symm.trans hpp)
      exact hew ▸ hlt
    · exact Or.inr ⟨pplus, rfl, heq.symm,
        Q_eq_upper_at_equal hF.toOrdered hleft hpp heq.symm⟩

#print axioms Hit.parentPath
#print axioms father_upper_bound
#print axioms father_upper_bound_nodes
#print axioms candidate_after_upper

end OmegaY.Geometry.Frame
