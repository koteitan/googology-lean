/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/WeakTotality.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/WeakTotality.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.WeakPaths
import Googology.Notation.OmegaY.WellOrder.OmegaY.Geometry.Frame

set_option backward.do.legacy false

/-!
# Total weak-marker recognition from local stored-edge validity

The premises describe actual array cells and their stored left references.
No success or totality property of `weakParent` is assumed.
-/

namespace OmegaY.Expansion

open Canonical

@[simp] private theorem bind_ok {α β : Type} (a : α) (f : α → Result β) :
    (Except.ok a >>= f) = f a := rfl
@[simp] private theorem bind_error {α β : Type} (e : Error) (f : α → Result β) :
    (Except.error e >>= f) = Except.error e := rfl
@[simp] private theorem pure_eq {α : Type} (a : α) :
    (pure a : Result α) = Except.ok a := rfl
@[simp] private theorem throw_eq {α : Type} (e : Error) :
    (throw e : Result α) = Except.error e := rfl

/-- Actual cell membership, independent of the weak-search algorithm. -/
def CellAt (mountain : Mountain) (ref : Ref) (cell : Cell) : Prop :=
  ∃ column, mountain[ref.column]? = some column ∧ column[ref.index]? = some cell

def ValidRef (mountain : Mountain) (ref : Ref) : Prop := ∃ cell, CellAt mountain ref cell

theorem lookup_ok_iff {mountain : Mountain} {ref : Ref} {cell : Cell} :
    lookup mountain ref = .ok cell ↔ CellAt mountain ref cell := by
  unfold lookup Canonical.cellAt CellAt
  cases hc : mountain[ref.column]? with
  | none => simp [Except.mapError]
  | some column =>
    cases hi : column[ref.index]? with
    | none => simp [hi, Except.mapError]
    | some result => simp [hi, Except.mapError]

/-- Every actual upper neighbor in a positive column has a valid left leg.
This is local graph data, with no numeric, height, or search hypothesis. -/
def WeakLocal (mountain : Mountain) : Prop :=
  ∀ (current : Ref) (column : Column) (upper : Cell),
    mountain[current.column]? = some column →
    column[current.index + 1]? = some upper → 0 < current.column →
    ∃ parent, upper.left = some parent ∧ parent.column < current.column ∧
      ValidRef mountain parent

/-- One forward two-leg edge: go up a reversed stored left leg and immediately
down the adjacent right leg, preserving the endpoint row. -/
def TwoLeg (mountain : Mountain) (parent current : Ref) : Prop :=
  ∃ column cell upper parentCell,
    mountain[current.column]? = some column ∧ column[current.index]? = some cell ∧
    column[current.index + 1]? = some upper ∧ upper.left = some parent ∧
    parent.column < current.column ∧ CellAt mountain parent parentCell ∧
    parentCell.row = cell.row

theorem weakParent_iff_twoLeg {mountain : Mountain} {current parent : Ref} :
    weakParent mountain current = .ok (some parent) ↔ TwoLeg mountain parent current := by
  constructor
  · intro h
    cases hc : mountain[current.column]? with
    | none => simp [weakParent, columnAt, hc] at h
    | some column =>
      cases hi : column[current.index]? with
      | none => simp [weakParent, columnAt, lookup, Canonical.cellAt, hc, hi, Except.mapError] at h
      | some cell =>
        have hlook : lookup mountain current = .ok cell := lookup_ok_iff.mpr ⟨column, hc, hi⟩
        cases hu : column[current.index + 1]? with
        | none => simp [weakParent, columnAt, hc, hlook, hu] at h
        | some upper =>
          cases hl : upper.left with
          | none => simp [weakParent, columnAt, hc, hlook, hu, leftOf, hl] at h
          | some left =>
            by_cases hlt : left.column < current.column
            · have hnot := Nat.not_le_of_lt hlt
              cases hp : lookup mountain left with
              | error e => simp [weakParent, columnAt, hc, hlook, hu, leftOf, hl, hnot, hp] at h
              | ok parentCell =>
                by_cases heq : parentCell.row = cell.row
                · have he : left = parent := by
                    simpa [weakParent, columnAt, hc, hlook, hu, leftOf, hl, hnot, hp, heq] using h
                  subst parent
                  exact ⟨column, cell, upper, parentCell, hc, hi, hu, hl, hlt,
                    lookup_ok_iff.mp hp, heq⟩
                · simp [weakParent, columnAt, hc, hlook, hu, leftOf, hl, hnot, hp, heq] at h
            · have hle := Nat.le_of_not_gt hlt
              simp [weakParent, columnAt, hc, hlook, hu, leftOf, hl, hle] at h
  · rintro ⟨column, cell, upper, parentCell, hc, hi, hu, hl, hlt, hp, heq⟩
    have hlook : lookup mountain current = .ok cell := lookup_ok_iff.mpr ⟨column, hc, hi⟩
    have hparent := lookup_ok_iff.mpr hp
    simp [weakParent, columnAt, hc, hlook, hu, leftOf, hl, hlt, hparent, heq]

theorem weakParent_total {mountain : Mountain} (hlocal : WeakLocal mountain)
    {current : Ref} (hcurrent : ValidRef mountain current) (hpos : 0 < current.column) :
    ∃ result, weakParent mountain current = .ok result ∧
      ∀ parent, result = some parent → ValidRef mountain parent := by
  obtain ⟨cell, column, hc, hi⟩ := hcurrent
  have hlook : lookup mountain current = .ok cell := lookup_ok_iff.mpr ⟨column, hc, hi⟩
  cases hu : column[current.index + 1]? with
  | none =>
    exact ⟨none, by simp [weakParent, columnAt, hc, hlook, hu], by simp⟩
  | some upper =>
    obtain ⟨parent, hl, hlt, hp⟩ := hlocal current column upper hc hu hpos
    obtain ⟨parentCell, hpc⟩ := hp
    have hparent := lookup_ok_iff.mpr hpc
    by_cases heq : parentCell.row = cell.row
    · refine ⟨some parent, ?_, ?_⟩
      · simp [weakParent, columnAt, hc, hlook, hu, leftOf, hl, hlt, hparent, heq]
      · intro p he
        cases Option.some.inj he
        exact ⟨parentCell, hpc⟩
    · exact ⟨none, by simp [weakParent, columnAt, hc, hlook, hu, leftOf, hl, hlt,
        hparent, heq], by simp⟩

/-- The strict fuel bound includes one final stop in column zero. -/
theorem weakReaches_total {mountain : Mountain} (hlocal : WeakLocal mountain)
    {root current : Ref} {fuel : Nat} (hcurrent : ValidRef mountain current)
    (hf : current.column < fuel) :
    ∃ result : Bool, weakReaches mountain root fuel current = .ok result := by
  induction fuel generalizing current with
  | zero => omega
  | succ fuel ih =>
    by_cases he : current = root
    · exact ⟨true, by simp [weakReaches, he]⟩
    · by_cases hcol : current.column ≤ root.column
      · exact ⟨false, by simp [weakReaches, he, hcol]⟩
      · obtain ⟨next, hn, hv⟩ := weakParent_total hlocal hcurrent (by omega)
        cases next with
        | none => exact ⟨false, by simp [weakReaches, he, hcol, hn]⟩
        | some parent =>
          have hlt := weakParent_column_lt hn
          obtain ⟨result, hr⟩ := ih (hv parent rfl) (by omega)
          exact ⟨result, by simpa [weakReaches, he, hcol, hn] using hr⟩

/-- Forward reachability is defined entirely from the explicit two-leg graph. -/
inductive ForwardWeakPath (mountain : Mountain) (root : Ref) : Ref → Prop
  | root : ForwardWeakPath mountain root root
  | step {parent current : Ref} (previous : ForwardWeakPath mountain root parent)
      (edge : TwoLeg mountain parent current) : ForwardWeakPath mountain root current

theorem forwardWeakPath_iff {mountain : Mountain} {root current : Ref} :
    ForwardWeakPath mountain root current ↔ WeakPath mountain root current := by
  constructor
  · intro path
    induction path with
    | root => exact .root
    | step _ edge ih => exact .step ih (weakParent_iff_twoLeg.mpr edge)
  · intro path
    induction path with
    | root => exact .root
    | step _ edge ih => exact .step ih (weakParent_iff_twoLeg.mp edge)

theorem weakReaches_forward_iff {mountain : Mountain} {root current : Ref} {fuel : Nat}
    (hf : current.column ≤ fuel) :
    weakReaches mountain root fuel current = .ok true ↔
      ForwardWeakPath mountain root current := by
  rw [weakReaches_iff hf, forwardWeakPath_iff]

theorem weakReaches_false_iff {mountain : Mountain} (hlocal : WeakLocal mountain)
    {root current : Ref} {fuel : Nat} (hcurrent : ValidRef mountain current)
    (hf : current.column < fuel) :
    weakReaches mountain root fuel current = .ok false ↔
      ¬ ForwardWeakPath mountain root current := by
  have hiff := weakReaches_forward_iff (mountain := mountain) (root := root) (Nat.le_of_lt hf)
  obtain ⟨result, hr⟩ := weakReaches_total (root := root) hlocal hcurrent hf
  cases result <;> simp_all

theorem frame_ref_cellAt (mountain : Mountain) (u : (Geometry.Frame.ofMountain mountain).Node) :
    CellAt mountain (Geometry.Frame.ref u) ((Geometry.Frame.ofMountain mountain).cell u) := by
  refine ⟨mountain[u.1.val], Array.getElem?_eq_getElem u.1.isLt, ?_⟩
  exact Array.getElem?_eq_getElem u.2.isLt

theorem frame_node_of_cellAt {mountain : Mountain} {ref : Ref} {cell : Cell}
    (h : CellAt mountain ref cell) :
    ∃ u : (Geometry.Frame.ofMountain mountain).Node,
      Geometry.Frame.ref u = ref ∧ (Geometry.Frame.ofMountain mountain).cell u = cell := by
  obtain ⟨column, hc, hi⟩ := h
  obtain ⟨hcb, hce⟩ := Array.getElem?_eq_some_iff.mp hc
  rw [← hce] at hi
  obtain ⟨hib, hie⟩ := Array.getElem?_eq_some_iff.mp hi
  exact ⟨⟨⟨ref.column, hcb⟩, ⟨ref.index, hib⟩⟩, rfl, hie⟩

/-- The existing ordered-frame interface supplies the local conditions from
ordinary stored-edge validity and existence of real left legs. -/
theorem weakLocal_of_ordered {mountain : Mountain}
    (hF : (Geometry.Frame.ofMountain mountain).Ordered)
    (hleft : ∀ u : (Geometry.Frame.ofMountain mountain).Node,
      Geometry.Frame.Real u → 0 < u.1.val →
      ∃ r, ((Geometry.Frame.ofMountain mountain).cell u).left = some r) :
    WeakLocal mountain := by
  intro current column upper hc hu hpos
  obtain ⟨u, href, hcell⟩ := frame_node_of_cellAt
    (show CellAt mountain ⟨current.column, current.index + 1⟩ upper from ⟨column, hc, hu⟩)
  have huindex : u.2.val = current.index + 1 := congrArg Ref.index href
  have hucol : u.1.val = current.column := congrArg Ref.column href
  have hreal : Geometry.Frame.Real u := by
    change 0 < u.2.val
    omega
  obtain ⟨r, hr⟩ := hleft u hreal (by omega)
  obtain ⟨left, hl, hlt, _⟩ := hF.stored_valid u r hr
  have hlref := Geometry.Frame.lookup_spec hl
  have hlcol : left.1.val = r.column := congrArg Ref.column hlref
  refine ⟨r, ?_, ?_, ?_⟩
  · simpa only [hcell] using hr
  · omega
  · refine ⟨(Geometry.Frame.ofMountain mountain).cell left, ?_⟩
    rw [← hlref]
    exact frame_ref_cellAt mountain left

/-- A concrete typed-node version uses exactly the allowance passed by markers. -/
theorem weakReaches_total_ordered {mountain : Mountain}
    (hF : (Geometry.Frame.ofMountain mountain).Ordered)
    (hleft : ∀ u : (Geometry.Frame.ofMountain mountain).Node,
      Geometry.Frame.Real u → 0 < u.1.val →
      ∃ r, ((Geometry.Frame.ofMountain mountain).cell u).left = some r)
    (root : Ref) (u : (Geometry.Frame.ofMountain mountain).Node) :
    ∃ result : Bool,
      weakReaches mountain root (u.1.val + 1) (Geometry.Frame.ref u) = .ok result := by
  apply weakReaches_total (weakLocal_of_ordered hF hleft)
    ⟨_, frame_ref_cellAt mountain u⟩
  exact Nat.lt_succ_self _

end OmegaY.Expansion

#print axioms OmegaY.Expansion.weakParent_iff_twoLeg
#print axioms OmegaY.Expansion.weakReaches_total
#print axioms OmegaY.Expansion.weakReaches_false_iff
#print axioms OmegaY.Expansion.weakLocal_of_ordered
#print axioms OmegaY.Expansion.weakReaches_total_ordered
