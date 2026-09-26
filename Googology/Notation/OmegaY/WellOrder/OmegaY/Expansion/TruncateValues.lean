/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/TruncateValues.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/TruncateValues.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.ExpansionPrepared

set_option backward.do.legacy false

/-! The final cut and extraction of bottom values preserve legality. The
first value is proved to be one from MountainValid.first_values; it is not
assumed from an input sequence. These results need no copied normality. -/

namespace OmegaY.Canonical

theorem MountainValid.of_push {mountain : Mountain} {column : Column}
    (hValid : MountainValid (mountain.push column)) : MountainValid mountain := by
  intro c hc
  have hAfter : c < (mountain.push column).size := by simp only [Array.size_push]; omega
  have hColumn : ColumnValid (mountain.push column) c mountain[c] := by
    simpa only [Array.getElem_push_lt hc] using hValid c hAfter
  exact hColumn.transport (fun ref hr => cellAt_push_left (hr.trans hc))

theorem MountainValid.pop {mountain : Mountain} (hValid : MountainValid mountain) :
    MountainValid mountain.pop := by
  intro c hc
  have hOld : c < mountain.size := by simp only [Array.size_pop] at hc; omega
  rw [Array.getElem_pop hc]
  apply (hValid c hOld).transport
  intro ref hRef
  have hBeforeCut : ref.column < mountain.size - 1 := by simp only [Array.size_pop] at hc; omega
  apply cellAt_eq_of_column_eq
  simp only [Array.getElem?_pop, hBeforeCut, ↓reduceIte]

end OmegaY.Canonical

namespace OmegaY.Expansion

open Canonical

def bottomValues (mountain : Mountain) : List Nat :=
  mountain.toList.map (fun column => (column[1]?.getD phantom).value)

private theorem mapM_eq_map_of_success {α β : Type} (f : α → Result β) (g : α → β)
    (xs : List α) (hSuccess : ∀ x ∈ xs, f x = .ok (g x)) :
    xs.mapM f = .ok (xs.map g) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hHead := hSuccess x (by simp)
    have hTail := ih (fun a ha => hSuccess a (by simp [ha]))
    simp [List.mapM_cons, hHead, hTail]

theorem bottomValues_length (mountain : Mountain) : (bottomValues mountain).length = mountain.size := by
  simp [bottomValues]

private theorem valid_column_of_mem {mountain : Mountain} (hValid : MountainValid mountain)
    {column : Column} (hColumn : column ∈ mountain.toList) :
    ∃ index, ColumnValid mountain index column := by
  obtain ⟨index, hRead⟩ := List.mem_iff_getElem?.mp hColumn
  have hArray : mountain[index]? = some column := by simpa only [Array.getElem?_toList] using hRead
  obtain ⟨hc, hNodes⟩ := Array.getElem?_eq_some_iff.mp hArray
  exact ⟨index, hNodes ▸ hValid index hc⟩

theorem valuesOf_eq_bottomValues {mountain : Mountain} (hValid : MountainValid mountain) :
    valuesOf mountain = .ok (bottomValues mountain) := by
  unfold valuesOf bottomValues
  apply mapM_eq_map_of_success
  intro column hColumn
  obtain ⟨index, hColumnValid⟩ := valid_column_of_mem hValid hColumn
  have hb : 1 < column.size := by have := hColumnValid.size_ge_two; omega
  simp only [Array.getElem?_eq_getElem hb, Option.getD_some]

theorem bottomValues_positive {mountain : Mountain} (hValid : MountainValid mountain) :
    ∀ value ∈ bottomValues mountain, 0 < value := by
  intro value hValue
  obtain ⟨column, hColumn, hValueEq⟩ := List.mem_map.mp hValue
  obtain ⟨index, hColumnValid⟩ := valid_column_of_mem hValid hColumn
  have hb : 1 < column.size := by have := hColumnValid.size_ge_two; omega
  have hPositive := hColumnValid.real_positive 1 column[1] (Array.getElem?_eq_getElem hb) (by omega)
  have hValue : column[1].value = value := by
    simpa only [Array.getElem?_eq_getElem hb, Option.getD_some] using hValueEq
  exact hValue ▸ hPositive

theorem bottomValues_head_one {mountain : Mountain} (hValid : MountainValid mountain)
    (hNonempty : 0 < mountain.size) : (bottomValues mountain)[0]? = some 1 := by
  let column := mountain[0]
  have hColumn : mountain[0]? = some column := Array.getElem?_eq_getElem hNonempty
  have hColumnValid : ColumnValid mountain 0 column := hValid 0 hNonempty
  have hb : 1 < column.size := by have := hColumnValid.size_ge_two; omega
  have hOne := hColumnValid.first_values 1 column[1] (Array.getElem?_eq_getElem hb) (by omega) rfl
  simp only [bottomValues, List.getElem?_map, Array.getElem?_toList, hColumn,
    Option.map_some, Array.getElem?_eq_getElem hb, Option.getD_some, hOne]

theorem bottomValues_legal {mountain : Mountain} (hValid : MountainValid mountain) :
    Legal (bottomValues mountain) := by
  cases hValues : bottomValues mountain with
  | nil => exact Or.inl rfl
  | cons first rest =>
    have hLength := bottomValues_length mountain
    rw [hValues] at hLength
    have hNonempty : 0 < mountain.size := by simp only [List.length_cons] at hLength; omega
    have hFirst := bottomValues_head_one hValid hNonempty
    have hFirstEq : first = 1 := Option.some.inj (by simpa only [hValues, List.getElem?_cons_zero] using hFirst)
    subst first
    refine Or.inr ⟨rest, rfl, ?_⟩
    intro value hValue
    exact bottomValues_positive hValid value (by rw [hValues]; simp [hValue])

/-- Both the executable result and standard sequence legality are proved.
The harmless default in bottomValues is unreachable for every valid column. -/
theorem valuesOf_total_legal {mountain : Mountain} (hValid : MountainValid mountain) :
    ∃ values, valuesOf mountain = .ok values ∧ Legal values ∧ values.length = mountain.size :=
  ⟨bottomValues mountain, valuesOf_eq_bottomValues hValid, bottomValues_legal hValid,
    bottomValues_length mountain⟩

theorem Preparation.expandDiagram_of_blocks {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) {copies : Nat} (hCopies : 0 < copies)
    {result : Mountain}
    (hLoop : (forIn (List.range copies) p.reduced (fun block ambient => do
      let next ← copyBlock ambient p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok result) :
    expandDiagram (front ++ [last]) copies = .ok result.pop := by
  rw [p.expandDiagram_eq_blocks hLast hCopies, hLoop]
  rfl

/-- Once the actual outer loop supplies a valid result, the final pop and
the actual value extractor succeed and return a legal sequence. -/
theorem Preparation.expand_of_blocks {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) {copies : Nat} (hCopies : 0 < copies)
    {result : Mountain}
    (hLoop : (forIn (List.range copies) p.reduced (fun block ambient => do
      let next ← copyBlock ambient p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok result)
    (hValid : MountainValid result) :
    MountainValid result.pop ∧ ∃ values,
      expand (front ++ [last]) copies = .ok values ∧ Legal values ∧ values.length = result.pop.size := by
  have hPopped := hValid.pop
  obtain ⟨values, hValues, hLegal, hLength⟩ := valuesOf_total_legal hPopped
  refine ⟨hPopped, values, ?_, hLegal, hLength⟩
  simp only [expand, p.expandDiagram_of_blocks hLast hCopies hLoop]
  exact hValues

end OmegaY.Expansion

#print axioms OmegaY.Canonical.MountainValid.pop
#print axioms OmegaY.Expansion.valuesOf_total_legal
#print axioms OmegaY.Expansion.Preparation.expand_of_blocks
