/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Geometry/RowSupport.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Geometry/RowSupport.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Geometry.FatherUpperBound

set_option backward.do.legacy false

/-!
# Real rows below candidates and numerical parents

Rows are the actual finite column entries, not all ordinals below a bound.
The main induction is ordered first by column and then by the node index.
No ancestor-closure or interval-barrier statement is used here.
-/

namespace OmegaY.Geometry.Frame

/-- The real row labels in the stored column prefix ending at `u`. -/
def rowsBelow (F : Frame) (u : F.Node) : Set Row :=
  {row | ∃ i : Fin (F.length u.1), 0 < i.val ∧ i ≤ u.2 ∧
    F.height ⟨u.1, i⟩ = row}

theorem mem_rowsBelow_iff_height {F : Frame} (hF : F.Ordered) {u : F.Node} {row : Row} :
    row ∈ F.rowsBelow u ↔ ∃ w : F.Node,
      Real w ∧ w.1 = u.1 ∧ F.height w ≤ F.height u ∧ F.height w = row := by
  constructor
  · rintro ⟨i, hi, hle, hrow⟩
    exact ⟨⟨u.1, i⟩, hi, rfl, (hF.rows_strict u.1).monotone hle, hrow⟩
  · rintro ⟨⟨c, i⟩, hi, hc, hle, hrow⟩
    dsimp only at hc
    subst c
    refine ⟨i, hi, ?_, hrow⟩
    by_contra hn
    exact not_lt_of_ge hle (hF.rows_strict u.1 (lt_of_not_ge hn))

theorem height_mem_rowsBelow {F : Frame} {u : F.Node} (hu : Real u) :
    F.height u ∈ F.rowsBelow u := ⟨u.2, hu, le_rfl, rfl⟩

theorem rowsBelow_upper {F : Frame} {u v : F.Node} (hv : F.upper u = some v) :
    F.rowsBelow v = insert (F.height v) (F.rowsBelow u) := by
  obtain ⟨hc, hi⟩ := upper_spec hv
  cases v with
  | mk c j =>
    dsimp only at hc
    subst c
    change j.val = u.2.val + 1 at hi
    ext row
    constructor
    · rintro ⟨i, hireal, hile, hirow⟩
      by_cases hlu : i ≤ u.2
      · exact Or.inr ⟨i, hireal, hlu, hirow⟩
      · have he : i = j := by apply Fin.ext; change i.val ≤ j.val at hile; change ¬ i.val ≤ u.2.val at hlu; omega
        exact Or.inl (hirow ▸ congrArg (fun k => F.height ⟨u.1, k⟩) he)
    · rintro (he | ⟨i, hireal, hile, hirow⟩)
      · exact ⟨j, by omega, le_rfl, he.symm⟩
      · exact ⟨i, hireal, by change i.val ≤ j.val; change i.val ≤ u.2.val at hile; omega, hirow⟩

theorem rowsBelow_mono_upper {F : Frame} {u v : F.Node} (hv : F.upper u = some v) :
    F.rowsBelow u ⊆ F.rowsBelow v := by
  rw [rowsBelow_upper hv]
  exact Set.subset_insert _ _

/-- At a bottom node all eligible real rows have height one. In particular,
this base case does not require a rule naming the stored bottom left leg. -/
theorem Q_rowsBelow_bottom {F : Frame} (hF : F.Ordered) {u q : F.Node}
    (hu : u.2.val = 1) (hq : F.Q u = some q) : F.rowsBelow q ⊆ F.rowsBelow u := by
  intro row hrow
  obtain ⟨w, hw, _, hle, hwrow⟩ := (mem_rowsBelow_iff_height hF).mp hrow
  have hub : F.height u = 1 := by
    have hlen : 1 < F.length u.1 := by rw [← hu]; exact u.2.isLt
    have he : u.2 = ⟨1, hlen⟩ := Fin.ext hu
    change (F.cells u.1 u.2).row = 1
    rw [he]
    exact hF.bottom_row u.1 hlen
  have hupper : F.height w ≤ 1 := by
    exact hle.trans ((Q_height_le hF hq).trans hub.le)
  have he : F.height w = 1 := le_antisymm hupper (one_le_height hF hw)
  have hroweq : row = F.height u := hwrow.symm.trans (he.trans hub.symm)
  rw [hroweq]
  exact height_mem_rowsBelow (by unfold Real; omega)

/-- Composing a threshold trace uses candidate supports only in columns
strictly below the explicit bound. This is the noncircular outer IH adapter. -/
theorem Hit.rowsBelow_of_left_support {F : Frame} (hF : F.Ordered) {bound : Nat}
    (hsupport : ∀ (u q : F.Node), u.1.val < bound → Real u → F.Q u = some q →
      F.rowsBelow q ⊆ F.rowsBelow u)
    {threshold : Nat} {q p : F.Node} (trace : Hit F threshold q p)
    (hqreal : Real q) (hqleft : q.1.val < bound) : F.rowsBelow p ⊆ F.rowsBelow q := by
  induction trace with
  | here _ _ => exact Set.Subset.refl _
  | @next q next p _ hQ _ ih =>
    have hnextreal := Q_real hF hqreal hQ
    have hnextleft := Nat.lt_trans (Q_column_lt hF hQ) hqleft
    exact (ih hnextreal hnextleft).trans (hsupport q next hqleft hqreal hQ)

/-- A current node needs its own first Q support and the already proved
supports in strictly earlier columns; it never needs a higher node here. -/
theorem P_rowsBelow_of_first_and_left {F : Frame} (hF : F.Ordered) {u p : F.Node}
    (hu : Real u)
    (hfirst : ∀ q, F.Q u = some q → F.rowsBelow q ⊆ F.rowsBelow u)
    (hleft : ∀ (v q : F.Node), v.1.val < u.1.val → Real v → F.Q v = some q →
      F.rowsBelow q ⊆ F.rowsBelow v)
    (hp : F.P u = some p) : F.rowsBelow p ⊆ F.rowsBelow u := by
  obtain ⟨q, hq, trace⟩ := (P_iff hF).mp hp
  exact (trace.rowsBelow_of_left_support hF hleft
    (Q_real hF hu hq) (Q_column_lt hF hq)).trans (hfirst q hq)

private theorem exists_real_lower {F : Frame} {v : F.Node} (hv : 1 < v.2.val) :
    ∃ u : F.Node, Real u ∧ F.upper u = some v ∧ u.1 = v.1 ∧ u.2.val < v.2.val := by
  let u : F.Node := ⟨v.1, ⟨v.2.val - 1, by have := v.2.isLt; omega⟩⟩
  refine ⟨u, by unfold Real; dsimp [u]; omega, ?_, rfl, by dsimp [u]; omega⟩
  have he : v.2.val - 1 + 1 = v.2.val := by omega
  simp [upper, u, he, v.2.isLt]

/-- Q-support, proved by column induction and then by the current column's
node order. The upper case uses D only through `candidate_after_upper`. -/
theorem Q_rowsBelow {F : Frame} (hF : F.Normal) {v q : F.Node}
    (hvreal : Real v) (hQ : F.Q v = some q) : F.rowsBelow q ⊆ F.rowsBelow v := by
  generalize hc : v.1.val = c
  induction c using Nat.strongRecOn generalizing v q with
  | ind c outer =>
    generalize hi : v.2.val = i
    induction i using Nat.strongRecOn generalizing v q with
    | ind i inner =>
      by_cases hbottom : v.2.val = 1
      · exact Q_rowsBelow_bottom hF.toOrdered hbottom hQ
      · have hvhigh : 1 < v.2.val := by unfold Real at hvreal; omega
        obtain ⟨u, hureal, huv, hucol, hui⟩ := exists_real_lower hvhigh
        obtain ⟨p, hp, _⟩ := hF.upper_step u v hureal huv
        have huc : u.1.val = c := by rw [hucol, hc]
        have hpu : F.rowsBelow p ⊆ F.rowsBelow u :=
          P_rowsBelow_of_first_and_left hF.toOrdered hureal
            (fun r hr => inner u.2.val (by omega) hureal hr huc rfl)
            (fun w r hw hwr hwrQ => outer w.1.val (by omega) hwr hwrQ rfl) hp
        rcases candidate_after_upper hF hp huv with hqp | ⟨pplus, hpp, hheight, hqp⟩
        · have he : q = p := Option.some.inj (hQ.symm.trans hqp)
          rw [he]
          exact hpu.trans (rowsBelow_mono_upper huv)
        · have he : q = pplus := Option.some.inj (hQ.symm.trans hqp)
          rw [he, rowsBelow_upper hpp, rowsBelow_upper huv, hheight]
          exact Set.insert_subset_insert hpu

/-- Numerical-parent support is obtained by composing the now established
Q-support along the complete finite threshold trace. -/
theorem P_rowsBelow {F : Frame} (hF : F.Normal) {v p : F.Node}
    (hp : F.P v = some p) : F.rowsBelow p ⊆ F.rowsBelow v := by
  have hvreal : Real v := real_of_value_pos hF.toOrdered
    (Nat.lt_trans (P_value hF.toOrdered hp).1 (P_value hF.toOrdered hp).2)
  exact P_rowsBelow_of_first_and_left hF.toOrdered hvreal
    (fun _ hq => Q_rowsBelow hF hvreal hq)
    (fun _ _ _ hr hq => Q_rowsBelow hF hr hq) hp

#print axioms Q_rowsBelow
#print axioms P_rowsBelow

end OmegaY.Geometry.Frame
