/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ReferencePartition.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/ReferencePartition.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.PreparedReferenceAt

set_option backward.do.legacy false

/-!
# Exact selection from a partition of actual references

The real referenceAt loop selects the final qualifying read. A successful
boundary mapM supplies the corresponding list partition; every later boundary
at or below the requested row produces a strictly lower, ineligible reference.
No root-boundary partition or referenceAt success is assumed implicitly.
-/

namespace OmegaY.Expansion

open Canonical

theorem referenceCandidates_append (mountain : Mountain) (earlier later : List Ref) (row : Row) :
    referenceCandidates mountain (earlier ++ later) row =
      referenceCandidates mountain earlier row ++ referenceCandidates mountain later row := by
  simp only [referenceCandidates, List.filterMap_append]

theorem referenceCandidates_qualifying_cons {mountain : Mountain} {chosen : Ref} {cell : Cell}
    (hRead : lookup mountain chosen = .ok cell) {row : Row} (hBound : row ≤ cell.row)
    (later : List Ref) :
    referenceCandidates mountain (chosen :: later) row =
      cell.row :: referenceCandidates mountain later row := by
  simp [referenceCandidates, hRead, Except.toOption, hBound]

theorem referenceCandidates_empty_of_below {mountain : Mountain} {references : List Ref}
    {row : Row}
    (hBelow : ∀ ref ∈ references, ∀ cell, lookup mountain ref = .ok cell → cell.row < row) :
    referenceCandidates mountain references row = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro height hHeight
  obtain ⟨ref, hRef, cell, hRead, hQualifies, _⟩ := mem_referenceCandidates.mp hHeight
  exact (not_le_of_gt (hBelow ref hRef cell hRead)) hQualifies

/-- Earlier entries may qualify or fail the row test. All reads must be
valid, and every entry after the chosen one must fail that test. -/
theorem referenceAt_last_qualifying {mountain : Mountain} {references earlier later : List Ref}
    {chosen : Ref} {cell : Cell} {row : Row}
    (hPartition : references = earlier ++ chosen :: later)
    (hValid : ∀ ref ∈ references, ValidRef mountain ref)
    (hRead : lookup mountain chosen = .ok cell) (hQualifies : row ≤ cell.row)
    (hLater : ∀ ref ∈ later, ∀ laterCell,
      lookup mountain ref = .ok laterCell → laterCell.row < row) :
    referenceAt mountain references row = .ok cell.row := by
  apply (referenceAt_iff_getLast hValid).mpr
  rw [hPartition, referenceCandidates_append,
    referenceCandidates_qualifying_cons hRead hQualifies,
    referenceCandidates_empty_of_below hLater]
  simp

/-- The output split is derived from Forall₂ over the actual mapM result. -/
theorem forall₂_append_cons_partition {α β : Type} {relation : α → β → Prop}
    {earlier later : List α} {chosen : α} {output : List β}
    (hPaired : List.Forall₂ relation (earlier ++ chosen :: later) output) :
    ∃ before selected after, output = before ++ selected :: after ∧
      List.Forall₂ relation earlier before ∧ relation chosen selected ∧
      List.Forall₂ relation later after := by
  induction earlier generalizing output with
  | nil =>
    cases hPaired with
    | cons hSelected hAfter => exact ⟨[], _, _, rfl, .nil, hSelected, hAfter⟩
  | cons first rest ih =>
    cases hPaired with
    | @cons _ item _ output hFirst hRest =>
      obtain ⟨before, selected, after, hOutput, hBefore, hSelected, hAfter⟩ := ih hRest
      exact ⟨item :: before, selected, after, by simp [hOutput],
        .cons hFirst hBefore, hSelected, hAfter⟩

theorem below_reference_mem {mountain : Mountain} {column : Nat}
    {boundaries : List Row} {references : List Ref}
    (hPaired : List.Forall₂ (fun ceiling ref => below mountain column ceiling = .ok ref)
      boundaries references) {ref : Ref} (hRef : ref ∈ references) :
    ∃ ceiling ∈ boundaries, below mountain column ceiling = .ok ref := by
  induction hPaired with
  | nil => cases hRef
  | @cons ceiling first boundaries references hFirst hPaired ih =>
    rcases List.mem_cons.mp hRef with rfl | hRef
    · exact ⟨ceiling, by simp, hFirst⟩
    · obtain ⟨bound, hBound, hBelow⟩ := ih hRef
      exact ⟨bound, by simp [hBound], hBelow⟩

theorem below_lookup_row_lt {mountain : Mountain} {column : Nat} {nodes : Column}
    (hColumn : mountain[column]? = some nodes) {ceiling : Row} {ref : Ref} {cell : Cell}
    (hBelow : below mountain column ceiling = .ok ref)
    (hRead : lookup mountain ref = .ok cell) : cell.row < ceiling := by
  obtain ⟨hSameColumn, found, hFoundIndex, hBound⟩ := below_result hColumn hBelow
  have hFoundRead : lookup mountain ref = .ok found := lookup_ok_iff.mpr
    ⟨nodes, by simpa only [hSameColumn] using hColumn, hFoundIndex⟩
  have he : cell = found := Except.ok.inj (hRead.symm.trans hFoundRead)
  exact he ▸ hBound

/-- A chosen boundary yields exactly the returned target if its selected
reference qualifies and every subsequent boundary is at or below the input
row. All output references and their partition come from successful mapM. -/
theorem referenceAt_boundary_partition {mountain : Mountain} {column : Nat} {nodes : Column}
    (hColumn : mountain[column]? = some nodes)
    {earlier later : List Row} {ceiling row : Row} {references : List Ref}
    (hMap : (earlier ++ ceiling :: later).mapM (below mountain column) = .ok references)
    {chosen : Ref} {cell : Cell} (hChosen : below mountain column ceiling = .ok chosen)
    (hRead : lookup mountain chosen = .ok cell) (hQualifies : row ≤ cell.row)
    (hLater : ∀ bound ∈ later, bound ≤ row) :
    referenceAt mountain references row = .ok cell.row := by
  have hPaired := below_mapM_pairing hMap
  have hValid := below_references_valid hColumn hPaired
  obtain ⟨before, selected, after, hPartition, _hBefore, hSelected, hAfter⟩ :=
    forall₂_append_cons_partition hPaired
  have he : selected = chosen := Except.ok.inj (hSelected.symm.trans hChosen)
  subst selected
  apply referenceAt_last_qualifying hPartition hValid hRead hQualifies
  intro ref hRef laterCell hLaterRead
  obtain ⟨bound, hBound, hBelow⟩ := below_reference_mem hAfter hRef
  exact (below_lookup_row_lt hColumn hBelow hLaterRead).trans_le (hLater bound hBound)

/-- An explicit boundary-list equation is enough; its partition need not
be baked into the executable input expression. -/
theorem referenceAt_of_boundary_partition {mountain : Mountain} {column : Nat} {nodes : Column}
    (hColumn : mountain[column]? = some nodes)
    {boundaries earlier later : List Row} {ceiling row : Row} {references : List Ref}
    (hPartition : boundaries = earlier ++ ceiling :: later)
    (hMap : boundaries.mapM (below mountain column) = .ok references)
    {chosen : Ref} {cell : Cell} (hChosen : below mountain column ceiling = .ok chosen)
    (hRead : lookup mountain chosen = .ok cell) (hQualifies : row ≤ cell.row)
    (hLater : ∀ bound ∈ later, bound ≤ row) :
    referenceAt mountain references row = .ok cell.row :=
  referenceAt_boundary_partition hColumn (hPartition ▸ hMap) hChosen hRead hQualifies hLater

theorem referenceAt_boundary_interval {mountain : Mountain} {column : Nat} {nodes : Column}
    (hColumn : mountain[column]? = some nodes)
    {earlier later : List Row} {ceiling row : Row} {references : List Ref}
    (hMap : (earlier ++ ceiling :: later).mapM (below mountain column) = .ok references)
    {chosen : Ref} {cell : Cell} (hChosen : below mountain column ceiling = .ok chosen)
    (hRead : lookup mountain chosen = .ok cell) (hQualifies : row ≤ cell.row)
    (hLater : ∀ bound ∈ later, bound ≤ row) :
    referenceAt mountain references row = .ok cell.row ∧ row ≤ cell.row ∧ cell.row < ceiling :=
  ⟨referenceAt_boundary_partition hColumn hMap hChosen hRead hQualifies hLater,
    hQualifies, below_lookup_row_lt hColumn hChosen hRead⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.referenceAt_last_qualifying
#print axioms OmegaY.Expansion.referenceAt_boundary_partition
#print axioms OmegaY.Expansion.referenceAt_boundary_interval
