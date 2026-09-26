/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/MarkerCompleteness.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/MarkerCompleteness.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.MarkerMembership
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.LoopCoverage

set_option backward.do.legacy false

/-! Completeness of membership in the actual finite marker loops. -/

namespace OmegaY.Expansion

open Canonical

@[simp] private theorem bind_ok {α β : Type} (a : α) (f : α → Result β) :
    (Except.ok a >>= f) = f a := rfl
@[simp] private theorem pure_eq {α : Type} (a : α) :
    (pure a : Result α) = Except.ok a := rfl

/-- A successful marker predicate forces the row test used by the loop. -/
theorem marker_path_same_row {mountain : Mountain} {root ref : Ref}
    (path : ForwardWeakPath mountain root ref) {rootCell cell : Cell}
    (hr : lookup mountain root = .ok rootCell) (hc : lookup mountain ref = .ok cell) :
    cell.row = rootCell.row := path.row_eq (lookup_ok_iff.mp hr) (lookup_ok_iff.mp hc)

theorem markers_member_complete {mountain : Mountain} (hlocal : WeakLocal mountain)
    {root : Ref} (hroot : ValidRef mountain root) {marked : Array (List Ref)}
    (hresult : markers mountain root = .ok marked) {bucket : Nat} {ref : Ref}
    (hspec : MarkerSpec mountain root bucket ref) : BucketMem marked bucket ref := by
  obtain ⟨hbucket, hright, href, rootIndex, hri, path⟩ := hspec
  subst bucket
  obtain ⟨targetCell, targetColumn, htargetColumn, htargetCell⟩ := href
  obtain ⟨targetColumnBound, htargetColumnEq⟩ := Array.getElem?_eq_some_iff.mp htargetColumn
  obtain ⟨targetIndexBound, _⟩ := Array.getElem?_eq_some_iff.mp htargetCell
  let inv := fun state : Array (List Ref) => state.size = mountain.size
  let present := fun state : Array (List Ref) => BucketMem state ref.column ref
  have hrootVisit : rootIndex ∈ (List.range (root.index + 1)).reverse := by
    apply List.mem_reverse.mpr
    exact List.mem_range.mpr (by omega)
  have hcoverage : ∃ result,
      markers mountain root = .ok result ∧ inv result ∧ present result := by
    change Returns (markers mountain root) (fun result => inv result ∧ present result)
    unfold markers
    apply returns_bind (post := fun result => inv result ∧ present result)
    · apply returns_forIn_hit (invariant := inv) (present := present)
        (event := fun index => index = rootIndex)
      · simp [inv]
      · exact ⟨rootIndex, hrootVisit, rfl⟩
      · intro rowIndex hrowVisit state hstate
        have hrowIndex : rowIndex ≤ root.index := by
          have h := List.mem_range.mp (List.mem_reverse.mp hrowVisit)
          omega
        obtain ⟨rootCell, hrootCell⟩ := hroot.lookup_below_index hrowIndex
        dsimp only
        rw [hrootCell]
        simp only [bind_ok]
        apply forIn_yield_cover (invariant := inv) (present := present)
          (event := fun c => c = ref.column ∧ rowIndex = rootIndex)
          (obligation := rowIndex = rootIndex) (hinit := hstate)
        · intro he
          exact ⟨ref.column, List.mem_range.mpr targetColumnBound, rfl, he⟩
        · intro column hcol state hstate
          have hcb : column < mountain.size := List.mem_range.mp hcol
          by_cases hright' : root.column < column
          · simp only [hright', ↓reduceIte]
            have hc := Array.getElem?_eq_getElem hcb
            have hnodes : columnAt mountain column = .ok mountain[column] := by
              simp [columnAt, hc]
            rw [hnodes]
            simp only [bind_ok]
            apply forIn_yield_cover (invariant := inv) (present := present)
              (event := fun i => i = ref.index ∧ column = ref.column ∧ rowIndex = rootIndex)
              (obligation := column = ref.column ∧ rowIndex = rootIndex) (hinit := hstate)
            · rintro ⟨hcolumn, hrowIndex⟩
              refine ⟨ref.index, List.mem_range.mpr ?_, rfl, hcolumn, hrowIndex⟩
              subst column
              simpa only [htargetColumnEq] using targetIndexBound
            · intro index hindex state hstate
              have hib : index < mountain[column].size := List.mem_range.mp hindex
              have hat : CellAt mountain ⟨column, index⟩ mountain[column][index] :=
                ⟨mountain[column], hc, Array.getElem?_eq_getElem hib⟩
              have hcell := lookup_ok_iff.mpr hat
              rw [hcell]
              simp only [bind_ok]
              have hvisit : (index = ref.index ∧ column = ref.column ∧ rowIndex = rootIndex) →
                  mountain[column][index].row = rootCell.row ∧
                    weakReaches mountain ⟨root.column, rowIndex⟩ (column + 1)
                      ⟨column, index⟩ = .ok true := by
                rintro ⟨hi, hc', hr⟩
                subst index
                subst column
                subst rowIndex
                have htrue : weakReaches mountain ⟨root.column, rootIndex⟩
                    (ref.column + 1) ref = .ok true :=
                  (weakReaches_forward_iff (Nat.le_succ ref.column)).mpr path
                exact ⟨marker_path_same_row path hrootCell hcell, htrue⟩
              by_cases hrow : mountain[column][index].row = rootCell.row
              · simp only [hrow, ↓reduceIte]
                obtain ⟨found, hfound⟩ := weakReaches_total
                  (root := ⟨root.column, rowIndex⟩) hlocal ⟨_, hat⟩ (Nat.lt_succ_self column)
                rw [hfound]
                simp only [bind_ok]
                cases found with
                | false =>
                  refine ⟨state, rfl, hstate, id, ?_⟩
                  intro hevent
                  have htrue := (hvisit hevent).2
                  rw [hfound] at htrue
                  cases htrue
                | true =>
                  refine ⟨state.modify column (fun refs => refs ++ [⟨column, index⟩]),
                    rfl, ?_, ?_, ?_⟩
                  · simpa only [inv, Array.size_modify] using hstate
                  · intro hold
                    apply (bucketMem_append (by change state.size = mountain.size at hstate; omega)).mpr
                    exact Or.inl hold
                  · rintro ⟨hi, hc', _⟩
                    apply (bucketMem_append (by change state.size = mountain.size at hstate; omega)).mpr
                    exact Or.inr ⟨hc'.symm, by cases ref; simp_all⟩
              · simp only [hrow, ↓reduceIte]
                refine ⟨state, rfl, hstate, id, ?_⟩
                intro hevent
                exact False.elim (hrow (hvisit hevent).1)
          · simp only [hright', ↓reduceIte]
            refine ⟨state, rfl, hstate, id, ?_⟩
            rintro ⟨he, _⟩
            subst column
            exact False.elim (hright' hright)
    · intro result hresult
      exact returns_pure hresult
  obtain ⟨result, hr, _, hp⟩ := hcoverage
  have he : result = marked := Except.ok.inj (hr.symm.trans hresult)
  exact he ▸ hp

theorem markers_member_iff {mountain : Mountain} (hlocal : WeakLocal mountain)
    {root : Ref} (hroot : ValidRef mountain root) {marked : Array (List Ref)}
    (hresult : markers mountain root = .ok marked) {bucket : Nat} {ref : Ref} :
    BucketMem marked bucket ref ↔ MarkerSpec mountain root bucket ref :=
  ⟨markers_member_sound hlocal hroot hresult, markers_member_complete hlocal hroot hresult⟩

/-- Every source column to the right contributes its actual phantom marker. -/
theorem markers_phantom_mem {mountain : Mountain} (hlocal : WeakLocal mountain)
    {root : Ref} (hroot : ValidRef mountain root) {marked : Array (List Ref)}
    (hresult : markers mountain root = .ok marked) (hchain : PhantomChain mountain)
    {column : Nat} (hright : root.column < column) (hc : column < mountain.size) :
    BucketMem marked column ⟨column, 0⟩ := by
  apply markers_member_complete hlocal hroot hresult
  exact ⟨rfl, hright, ⟨phantom, hchain.phantom_at column hc⟩, 0, Nat.zero_le _,
    hchain.reachable (Nat.le_of_lt hright) hc⟩

/-- The weak parent closure now concerns the actual output array, not only an
abstract path predicate.  Its parent is a root-prefix node or an earlier
member of that same output array. -/
theorem markers_upper_parent {mountain : Mountain} (hlocal : WeakLocal mountain)
    {root : Ref} (hroot : ValidRef mountain root) {marked : Array (List Ref)}
    (hresult : markers mountain root = .ok marked) {bucket : Nat} {ref : Ref}
    (hmem : BucketMem marked bucket ref) :
    ∃ rootIndex parent cell upper parentCell,
      rootIndex ≤ root.index ∧ CellAt mountain ref cell ∧
      CellAt mountain ⟨ref.column, ref.index + 1⟩ upper ∧
      upper.left = some parent ∧ parent.column < ref.column ∧
      CellAt mountain parent parentCell ∧ parentCell.row = cell.row ∧
      (parent = ⟨root.column, rootIndex⟩ ∨ BucketMem marked parent.column parent) := by
  obtain ⟨_, hright, _, rootIndex, hi, path⟩ := markers_member_sound hlocal hroot hresult hmem
  have descendant : WeakDescendant mountain ⟨root.column, rootIndex⟩ ref := ⟨path, hright⟩
  obtain ⟨parent, cell, upper, parentCell, hc, hu, hl, hlt, hp, heq, hparent⟩ :=
    descendant.upper_parent
  refine ⟨rootIndex, parent, cell, upper, parentCell, hi, hc, hu, hl, hlt, hp, heq, ?_⟩
  rcases hparent with he | hdesc
  · exact Or.inl he
  · apply Or.inr
    apply markers_member_complete hlocal hroot hresult
    exact ⟨rfl, hdesc.2, ⟨parentCell, hp⟩, rootIndex, hi, hdesc.1⟩

theorem markers_member_iff_ordered {mountain : Mountain}
    (hF : (Geometry.Frame.ofMountain mountain).Ordered)
    (hleft : ∀ u : (Geometry.Frame.ofMountain mountain).Node,
      Geometry.Frame.Real u → 0 < u.1.val →
      ∃ r, ((Geometry.Frame.ofMountain mountain).cell u).left = some r)
    (root : (Geometry.Frame.ofMountain mountain).Node) {marked : Array (List Ref)}
    (hresult : markers mountain (Geometry.Frame.ref root) = .ok marked)
    {bucket : Nat} {ref : Ref} :
    BucketMem marked bucket ref ↔ MarkerSpec mountain (Geometry.Frame.ref root) bucket ref :=
  markers_member_iff (weakLocal_of_ordered hF hleft)
    ⟨_, frame_ref_cellAt mountain root⟩ hresult

end OmegaY.Expansion

#print axioms OmegaY.Expansion.markers_member_complete
#print axioms OmegaY.Expansion.markers_member_iff
#print axioms OmegaY.Expansion.markers_phantom_mem
#print axioms OmegaY.Expansion.markers_upper_parent
