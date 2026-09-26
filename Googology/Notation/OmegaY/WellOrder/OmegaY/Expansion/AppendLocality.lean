/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/AppendLocality.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/AppendLocality.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.PreparedReferenceAt

set_option backward.do.legacy false

/-! References computed at block start and frozen source columns remain
unchanged when completed columns are appended. These equalities concern the
actual selectors, without normality assumptions on appended columns. -/

namespace OmegaY.Expansion

open Canonical

def PreservesColumns (before after : Mountain) : Prop :=
  ∀ column, column < before.size → after[column]? = before[column]?

theorem PreservesColumns.push (before : Mountain) (column : Column) :
    PreservesColumns before (before.push column) := by
  intro i hi
  simp [Array.getElem?_push, Nat.ne_of_lt hi]

theorem PreservesColumns.size_le {before after : Mountain}
    (h : PreservesColumns before after) : before.size ≤ after.size := by
  by_cases hz : before.size = 0
  · omega
  · have hi : before.size - 1 < before.size := by omega
    have hRead : after[before.size - 1]? = some before[before.size - 1] :=
      (h _ hi).trans (Array.getElem?_eq_getElem hi)
    have hBound := (Array.getElem?_eq_some_iff.mp hRead).1
    omega

theorem PreservesColumns.trans {first middle last : Mountain}
    (hFirst : PreservesColumns first middle) (hLast : PreservesColumns middle last) :
    PreservesColumns first last := by
  intro column hc
  exact (hLast column (Nat.lt_of_lt_of_le hc hFirst.size_le)).trans (hFirst column hc)

theorem PreservesColumns.lookup {before after : Mountain}
    (h : PreservesColumns before after) {ref : Ref} (hc : ref.column < before.size) :
    lookup after ref = lookup before ref := by
  unfold OmegaY.Expansion.lookup
  rw [cellAt_eq_of_column_eq (ref := ref) (h ref.column hc)]

theorem PreservesColumns.validRef {before after : Mountain}
    (h : PreservesColumns before after) {ref : Ref} (hRef : ValidRef before ref) :
    ValidRef after ref := by
  obtain ⟨cell, hCell⟩ := hRef
  obtain ⟨nodes, hColumn, hIndex⟩ := hCell
  have hc := (Array.getElem?_eq_some_iff.mp hColumn).1
  exact ⟨cell, lookup_ok_iff.mp ((h.lookup hc).trans (lookup_ok_iff.mpr ⟨nodes, hColumn, hIndex⟩))⟩

/-- Strict-below selection in an unchanged complete column is identical,
including any error result. Other columns do not enter its search. -/
theorem PreservesColumns.below {before after : Mountain}
    (h : PreservesColumns before after) {column : Nat} (hc : column < before.size)
    (ceiling : Row) : below after column ceiling = below before column ceiling := by
  simp only [OmegaY.Expansion.below, columnAt, OmegaY.Expansion.lookup, Canonical.cellAt, h column hc]

theorem PreservesColumns.referenceCandidates {before after : Mountain}
    (h : PreservesColumns before after) {references : List Ref}
    (hRefs : ∀ ref ∈ references, ValidRef before ref) (row : Row) :
    referenceCandidates after references row = referenceCandidates before references row := by
  apply List.filterMap_congr
  intro ref hMem
  obtain ⟨cell, nodes, hColumn, _⟩ := hRefs ref hMem
  rw [h.lookup (Array.getElem?_eq_some_iff.mp hColumn).1]

/-- Every reference is still read, in the same list order, after appending.
This supplies stability of actual block-start target selection. -/
theorem PreservesColumns.referenceAt {before after : Mountain}
    (h : PreservesColumns before after) {references : List Ref}
    (hRefs : ∀ ref ∈ references, ValidRef before ref) (row : Row) :
    referenceAt after references row = referenceAt before references row := by
  have hAfter : ∀ ref ∈ references, ValidRef after ref := fun ref hm => h.validRef (hRefs ref hm)
  rw [referenceAt_eq_getLast hAfter, referenceAt_eq_getLast hRefs, h.referenceCandidates hRefs row]

end OmegaY.Expansion

#print axioms OmegaY.Expansion.PreservesColumns.below
#print axioms OmegaY.Expansion.PreservesColumns.referenceAt
