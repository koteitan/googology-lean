/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/MarkerMembership.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/MarkerMembership.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.Markers
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.LoopInvariant

set_option backward.do.legacy false

/-! Soundness of membership in the actual marker array. -/

namespace OmegaY.Expansion

open Canonical

@[simp] private theorem bind_ok {α β : Type} (a : α) (f : α → Result β) :
    (Except.ok a >>= f) = f a := rfl

def BucketMem (marked : Array (List Ref)) (column : Nat) (ref : Ref) : Prop :=
  ref ∈ marked[column]?.getD []

theorem bucketMem_append {marked : Array (List Ref)} {column bucket : Nat} {ref entry : Ref}
    (hc : column < marked.size) :
    BucketMem (marked.modify column (fun refs => refs ++ [entry])) bucket ref ↔
      BucketMem marked bucket ref ∨ (bucket = column ∧ ref = entry) := by
  by_cases he : column = bucket
  · subst bucket
    simp [BucketMem, Array.getElem?_modify, Array.getElem?_eq_getElem hc]
  · simp [BucketMem, Array.getElem?_modify, he, Ne.symm he]

/-- The path starts at an actual root-prefix cell; the output entry itself is
an actual source reference in the strictly rightward bucket. -/
def MarkerSpec (mountain : Mountain) (root : Ref) (bucket : Nat) (ref : Ref) : Prop :=
  ref.column = bucket ∧ root.column < ref.column ∧ ValidRef mountain ref ∧
    ∃ rootIndex, rootIndex ≤ root.index ∧
      ForwardWeakPath mountain ⟨root.column, rootIndex⟩ ref

def MarkerInvariant (mountain : Mountain) (root : Ref) (marked : Array (List Ref)) : Prop :=
  marked.size = mountain.size ∧ ∀ bucket ref, BucketMem marked bucket ref →
    MarkerSpec mountain root bucket ref

theorem markerInvariant_initial (mountain : Mountain) (root : Ref) :
    MarkerInvariant mountain root (Array.replicate mountain.size []) := by
  refine ⟨by simp, ?_⟩
  intro bucket ref hmem
  have hfalse : ¬ BucketMem (Array.replicate mountain.size []) bucket ref := by
    simp only [BucketMem, Array.getElem?_replicate]
    split <;> simp
  exact False.elim (hfalse hmem)

theorem MarkerInvariant.append {mountain : Mountain} {root : Ref}
    {marked : Array (List Ref)} (hinv : MarkerInvariant mountain root marked)
    {column : Nat} {ref : Ref} (hc : column < mountain.size)
    (hspec : MarkerSpec mountain root column ref) :
    MarkerInvariant mountain root (marked.modify column (fun refs => refs ++ [ref])) := by
  refine ⟨by simpa using hinv.1, ?_⟩
  intro bucket entry hm
  have hbound : column < marked.size := by rw [hinv.1]; exact hc
  rcases (bucketMem_append hbound).mp hm with hold | ⟨hbucket, he⟩
  · exact hinv.2 bucket entry hold
  · subst bucket
    subst entry
    exact hspec

/-- The invariant is established on the actual three nested loops. -/
theorem markers_returns_invariant {mountain : Mountain} (hlocal : WeakLocal mountain)
    {root : Ref} (hroot : ValidRef mountain root) :
    Returns (markers mountain root) (MarkerInvariant mountain root) := by
  unfold markers
  apply returns_bind (post := MarkerInvariant mountain root)
  · apply returns_forIn _ _ _ _ (markerInvariant_initial mountain root)
    intro rootIndex hri state hstate
    have hri' : rootIndex ≤ root.index := by
      have h := List.mem_range.mp (List.mem_reverse.mp hri)
      omega
    obtain ⟨rootCell, hrootCell⟩ := hroot.lookup_below_index hri'
    dsimp only
    rw [hrootCell]
    simp only [bind_ok]
    apply returns_bind (post := MarkerInvariant mountain root)
    · apply returns_forIn _ _ _ _ hstate
      intro column hcol state hstate
      have hcb : column < mountain.size := List.mem_range.mp hcol
      by_cases hright : root.column < column
      · simp only [hright, ↓reduceIte]
        have hc := Array.getElem?_eq_getElem hcb
        have hnodes : columnAt mountain column = .ok mountain[column] := by
          simp [columnAt, hc]
        rw [hnodes]
        simp only [bind_ok]
        apply returns_bind (post := MarkerInvariant mountain root)
        · apply returns_forIn _ _ _ _ hstate
          intro index hindex state hstate
          have hib : index < mountain[column].size := List.mem_range.mp hindex
          have hat : CellAt mountain ⟨column, index⟩ mountain[column][index] :=
            ⟨mountain[column], hc, Array.getElem?_eq_getElem hib⟩
          have hcell := lookup_ok_iff.mpr hat
          rw [hcell]
          simp only [bind_ok]
          by_cases hrow : mountain[column][index].row = rootCell.row
          · simp only [hrow, ↓reduceIte]
            obtain ⟨found, hfound⟩ := weakReaches_total
              (root := ⟨root.column, rootIndex⟩) hlocal ⟨_, hat⟩ (Nat.lt_succ_self column)
            rw [hfound]
            simp only [bind_ok]
            cases found with
            | false => exact returns_pure hstate
            | true =>
              apply returns_pure
              apply hstate.append hcb
              exact ⟨rfl, hright, ⟨_, hat⟩, rootIndex, hri',
                forwardWeakPath_iff.mpr (weakReaches_sound hfound)⟩
          · simp only [hrow, ↓reduceIte]
            exact returns_pure hstate
        · intro result hresult
          exact returns_pure hresult
      · simp only [hright, ↓reduceIte]
        exact returns_pure hstate
    · intro result hresult
      exact returns_pure hresult
  · intro result hresult
    exact returns_pure hresult

theorem markers_invariant {mountain : Mountain} (hlocal : WeakLocal mountain)
    {root : Ref} (hroot : ValidRef mountain root) {marked : Array (List Ref)}
    (hresult : markers mountain root = .ok marked) : MarkerInvariant mountain root marked := by
  obtain ⟨result, hr, hinv⟩ := markers_returns_invariant hlocal hroot
  have he : result = marked := Except.ok.inj (hr.symm.trans hresult)
  exact he ▸ hinv

theorem markers_size {mountain : Mountain} (hlocal : WeakLocal mountain)
    {root : Ref} (hroot : ValidRef mountain root) {marked : Array (List Ref)}
    (hresult : markers mountain root = .ok marked) : marked.size = mountain.size :=
  (markers_invariant hlocal hroot hresult).1

theorem markers_member_sound {mountain : Mountain} (hlocal : WeakLocal mountain)
    {root : Ref} (hroot : ValidRef mountain root) {marked : Array (List Ref)}
    (hresult : markers mountain root = .ok marked) {bucket : Nat} {ref : Ref}
    (hmem : BucketMem marked bucket ref) : MarkerSpec mountain root bucket ref :=
  (markers_invariant hlocal hroot hresult).2 bucket ref hmem

end OmegaY.Expansion

#print axioms OmegaY.Expansion.markers_returns_invariant
#print axioms OmegaY.Expansion.markers_size
#print axioms OmegaY.Expansion.markers_member_sound
