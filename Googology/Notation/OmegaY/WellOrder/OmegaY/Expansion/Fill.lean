/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/Fill.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/Fill.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.LoopInvariant
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.WeakTotality
import Googology.Notation.OmegaY.WellOrder.OmegaY.Rows.FillLadder

set_option backward.do.legacy false

/-!
# Exact output of the executable reference-fill loop

The hypotheses refer to actual array reads and strict row order. An actual
cap node bounds `high`; every required successor read is derived from it.
No successful-loop or successful-successor oracle is a hypothesis.
-/

namespace OmegaY.Expansion

open Canonical

@[simp] private theorem bind_ok {α β : Type} (a : α) (f : α → Result β) :
    (Except.ok a >>= f) = f a := rfl
@[simp] private theorem pure_eq {α : Type} (a : α) :
    (pure a : Result α) = Except.ok a := rfl
@[simp] private theorem throw_eq {α : Type} (e : Error) :
    (throw e : Result α) = Except.error e := rfl

/-- Strict order expressed entirely in actual array reads. -/
def FillRowsStrict (nodes : Column) : Prop :=
  ∀ (i j : Nat) (a b : Cell), nodes[i]? = some a → nodes[j]? = some b →
    i < j → a.row < b.row

/-- A real cap node forces every eligible parent to have a real successor. -/
theorem fill_successor {nodes : Column} (hstrict : FillRowsStrict nodes)
    {capIndex i : Nat} {cap parent : Cell} {high : Row}
    (hcap : nodes[capIndex]? = some cap) (hhigh : high ≤ cap.row)
    (hparent : nodes[i]? = some parent) (heligible : parent.row < high) :
    ∃ upper, nodes[i + 1]? = some upper ∧ parent.row < upper.row ∧ upper.row ≤ cap.row := by
  have hik : i < capIndex := by
    by_contra h
    have hki : capIndex ≤ i := by omega
    rcases eq_or_lt_of_le hki with he | hl
    · subst i
      have heq : parent = cap := Option.some.inj (hparent.symm.trans hcap)
      subst parent
      exact (not_lt_of_ge hhigh) heligible
    · exact (not_lt_of_ge hhigh) ((hstrict _ _ _ _ hcap hparent hl).trans heligible)
  obtain ⟨hk, _⟩ := Array.getElem?_eq_some_iff.mp hcap
  have hi : i + 1 < nodes.size := by omega
  have hread : nodes[i + 1]? = some nodes[i + 1] := Array.getElem?_eq_getElem hi
  refine ⟨nodes[i + 1], hread, hstrict _ _ _ _ hparent hread (by omega), ?_⟩
  rcases eq_or_lt_of_le (show i + 1 ≤ capIndex by omega) with he | hl
  · have heq : nodes[i + 1] = cap := by
      apply Option.some.inj
      exact hread.symm.trans (he ▸ hcap)
    exact le_of_eq (congrArg Cell.row heq)
  · exact le_of_lt (hstrict _ _ _ _ hread hcap hl)

/-- A generic equation for the actual `forIn` append loop. -/
theorem forIn_append_chunks {α β : Type} (xs : List α) (initial : List β)
    (body : α → List β → Result (ForInStep (List β))) (chunk : α → List β)
    (hbody : ∀ item ∈ xs, ∀ state,
      body item state = .ok (.yield (state ++ chunk item))) :
    (forIn xs initial body : Result (List β)) = .ok (initial ++ xs.flatMap chunk) := by
  induction xs generalizing initial with
  | nil => simp
  | cons item rest ih =>
    rw [List.forIn_cons, hbody item (by simp) initial]
    change (forIn rest (initial ++ chunk item) body : Result (List β)) = _
    rw [ih _ (fun item hi state => hbody item (by simp [hi]) state)]
    simp only [List.flatMap_cons, List.append_assoc]

def fillChunk (nodes : Column) (column : Nat) (low high : Row) (i : Nat) : List Cell :=
  let parent := nodes[i]?.getD phantom
  let upper := nodes[i + 1]?.getD phantom
  if low ≤ parent.row ∧ parent.row < high then
    (Row.fillLadder parent.row upper.row).map fun row => ⟨row, 0, some ⟨column, i⟩⟩
  else []

def fillCells (nodes : Column) (column : Nat) (low high : Row) : List Cell :=
  (List.range nodes.size).flatMap (fillChunk nodes column low high)

/-- Exact success of both real loops, derived from a finite strict column and
one actual cap. `high` need not itself occur in the column. -/
theorem fill_eq_cells {mountain : Mountain} {source : Ref} {sourceCell : Cell}
    {sourceParent : Ref} {shift : Nat} {nodes : Column} {low high : Row}
    {capIndex : Nat} {cap : Cell}
    (hsource : lookup mountain source = .ok sourceCell)
    (hleft : sourceCell.left = some sourceParent)
    (hnodes : mountain[sourceParent.column + shift]? = some nodes)
    (hstrict : FillRowsStrict nodes)
    (hcap : nodes[capIndex]? = some cap) (hhigh : high ≤ cap.row)
    (hleftward : sourceParent.column + shift < source.column + shift) :
    fill mountain source shift low high =
      .ok (fillCells nodes (sourceParent.column + shift) low high) := by
  unfold fill
  rw [hsource]
  simp only [bind_ok, leftOf, hleft]
  have hcolumn : columnAt mountain (sourceParent.column + shift) = .ok nodes := by
    simp [columnAt, hnodes]
  rw [hcolumn]
  simp only [bind_ok]
  have hloop := forIn_append_chunks (List.range nodes.size) []
    (fun index result => do
      let parentRef : Ref := ⟨sourceParent.column + shift, index⟩
      let parent ← lookup mountain parentRef
      if low ≤ parent.row ∧ parent.row < high then
        if ¬ sourceParent.column + shift < source.column + shift then throw .nonLeftward
        let upper ← lookup mountain ⟨sourceParent.column + shift, index + 1⟩
        if ¬ parent.row < upper.row then throw .nonIncreasingRows
        let result ← forIn (List.range (Row.jump parent.row upper.row)).reverse result
          (fun d result => pure (.yield (result ++ [⟨Row.bump parent.row d, 0, some parentRef⟩])))
        pure (.yield result)
      else pure (.yield result))
    (fillChunk nodes (sourceParent.column + shift) low high) (by
      intro index hindex result
      have hi := List.mem_range.mp hindex
      have hread : nodes[index]? = some nodes[index] := Array.getElem?_eq_getElem hi
      have hlookup := lookup_ok_iff.mpr
        (show CellAt mountain ⟨sourceParent.column + shift, index⟩ nodes[index] from
          ⟨nodes, hnodes, hread⟩)
      dsimp only
      rw [hlookup]
      simp only [bind_ok, fillChunk, hread, Option.getD_some]
      by_cases heligible : low ≤ nodes[index].row ∧ nodes[index].row < high
      · obtain ⟨upper, hupper, hrow, _⟩ :=
          fill_successor hstrict hcap hhigh hread heligible.2
        have hlookupUpper := lookup_ok_iff.mpr
          (show CellAt mountain ⟨sourceParent.column + shift, index + 1⟩ upper from
            ⟨nodes, hnodes, hupper⟩)
        simp only [heligible, ↓reduceIte, hleftward, not_true_eq_false]
        rw [hlookupUpper]
        simp only [bind_ok, hrow, not_true_eq_false, ↓reduceIte, hupper, Option.getD_some]
        have hinner := forIn_append_chunks (β := Cell) (List.range (Row.jump nodes[index].row upper.row)).reverse
          result (fun d state => Except.ok (.yield
            (state ++ [Cell.mk (Row.bump nodes[index].row d) 0 (some ⟨sourceParent.column + shift, index⟩)])))
          (fun d => [⟨Row.bump nodes[index].row d, 0, some ⟨sourceParent.column + shift, index⟩⟩])
          (by intros; rfl)
        simp only [and_self, ↓reduceIte, pure_eq]
        rw [hinner]
        simp [Row.fillLadder, ← List.map_eq_flatMap, List.map_map, Function.comp_def]
      · simp [heligible])
  change ((forIn (List.range nodes.size) [] _ : Result (List Cell)) >>= _) = _
  rw [hloop]
  rfl

end OmegaY.Expansion

#print axioms OmegaY.Expansion.fill_eq_cells
