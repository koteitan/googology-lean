/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Canonical/Locality.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Canonical/Locality.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.Prefix

set_option backward.do.legacy false

/-!
# Locality of actual canonical parent search

The executable search reads the current cell and complete columns strictly
to its left. Its own guard enforces this fact; no validity or ordered-frame
hypothesis is needed. These lemmas preserve the exact exception as well as
every successful answer.
-/

namespace OmegaY.Canonical

theorem nextCandidate_eq_of_left_columns {before after : Mountain} {current : Ref}
    (hCurrent : cellAt before current = cellAt after current)
    (hColumns : ∀ c, c < current.column → before[c]? = after[c]?) :
    nextCandidate before current = nextCandidate after current := by
  cases hc : cellAt after current with
  | error e => simp [nextCandidate, hCurrent, hc]
  | ok cell =>
    cases hl : cell.left with
    | none => simp [nextCandidate, hCurrent, hc, hl]
    | some left =>
      by_cases hlt : left.column < current.column
      · have hCell := cellAt_eq_of_column_eq (ref := left) (hColumns left.column hlt)
        simp only [nextCandidate, hCurrent, hc, except_bind_ok, hl,
          hlt, not_true_eq_false, ↓reduceIte]
        rw [hCell, hColumns left.column hlt]
      · have hle : current.column ≤ left.column := Nat.le_of_not_gt hlt
        simp [nextCandidate, hCurrent, hc, hl, hle]

theorem findParentAux_eq_of_left_columns {before after : Mountain} {current : Ref}
    (hCurrent : cellAt before current = cellAt after current)
    (hColumns : ∀ c, c < current.column → before[c]? = after[c]?)
    (threshold fuel : Nat) :
    findParentAux before threshold fuel current =
      findParentAux after threshold fuel current := by
  induction fuel generalizing current with
  | zero => rfl
  | succ fuel ih =>
    have hNext := nextCandidate_eq_of_left_columns hCurrent hColumns
    cases hn : nextCandidate after current with
    | error e => simp [findParentAux, hNext, hn]
    | ok next =>
      have hlt := nextCandidate_column_lt hn
      have hCell := cellAt_eq_of_column_eq (ref := next) (hColumns next.column hlt)
      have hRec := ih hCell (fun c hc => hColumns c (Nat.lt_trans hc hlt))
      simp only [findParentAux, hNext, hn, except_bind_ok, hCell, hRec]

/-- Numerical parents depend on the current cell and complete earlier columns. -/
theorem findParent_eq_of_left_columns {before after : Mountain} {current : Ref}
    (hCurrent : cellAt before current = cellAt after current)
    (hColumns : ∀ c, c < current.column → before[c]? = after[c]?) :
    findParent before current = findParent after current := by
  cases hc : cellAt after current with
  | error e => simp [findParent, hCurrent, hc]
  | ok cell =>
    simpa only [findParent, hCurrent, hc, except_bind_ok] using
      findParentAux_eq_of_left_columns hCurrent hColumns cell.value current.column

theorem nextCandidate_eq_of_columns {before after : Mountain} {current : Ref}
    (hColumns : ∀ c, c ≤ current.column → before[c]? = after[c]?) :
    nextCandidate before current = nextCandidate after current :=
  nextCandidate_eq_of_left_columns
    (cellAt_eq_of_column_eq (hColumns current.column le_rfl))
    (fun c hc => hColumns c (Nat.le_of_lt hc))

theorem findParent_eq_of_columns {before after : Mountain} {current : Ref}
    (hColumns : ∀ c, c ≤ current.column → before[c]? = after[c]?) :
    findParent before current = findParent after current :=
  findParent_eq_of_left_columns
    (cellAt_eq_of_column_eq (hColumns current.column le_rfl))
    (fun c hc => hColumns c (Nat.le_of_lt hc))

/-- Appending an arbitrary later column leaves every earlier Q step unchanged. -/
theorem nextCandidate_push {mountain : Mountain} {column : Column} {current : Ref}
    (hc : current.column < mountain.size) :
    nextCandidate (mountain.push column) current = nextCandidate mountain current := by
  apply nextCandidate_eq_of_columns
  intro c hcle
  have hlt := Nat.lt_of_le_of_lt hcle hc
  simp [Array.getElem?_push, Nat.ne_of_lt hlt]

/-- Appending an arbitrary later column leaves every earlier parent unchanged. -/
theorem findParent_push {mountain : Mountain} {column : Column} {current : Ref}
    (hc : current.column < mountain.size) :
    findParent (mountain.push column) current = findParent mountain current := by
  apply findParent_eq_of_columns
  intro c hcle
  have hlt := Nat.lt_of_le_of_lt hcle hc
  simp [Array.getElem?_push, Nat.ne_of_lt hlt]

/-- More generally, modifying only cells above an old last-column node cannot
change that node's parent; agreement at its own index is all that is needed. -/
theorem findParent_last_column {left : Mountain} {before after : Column} {i : Nat}
    (hCell : before[i]? = after[i]?) :
    findParent (left.push before) ⟨left.size, i⟩ =
      findParent (left.push after) ⟨left.size, i⟩ := by
  apply findParent_eq_of_left_columns
  · simp [cellAt, hCell]
  · intro c hc
    simp [Array.getElem?_push, Nat.ne_of_lt hc]

theorem findParent_push_cell {left : Mountain} {column : Column} {next : Cell} {i : Nat}
    (hi : i < column.size) :
    findParent (left.push (column.push next)) ⟨left.size, i⟩ =
      findParent (left.push column) ⟨left.size, i⟩ := by
  apply findParent_last_column
  simp [Array.getElem?_push, Nat.ne_of_lt hi]

/-- Successful completion of any later input leaves existing parents fixed. -/
theorem buildFrom_preserves_parent {mountain result : Mountain} {values : List Nat}
    (h : buildFrom mountain values = .ok result) {current : Ref}
    (hc : current.column < mountain.size) :
    findParent result current = findParent mountain current := by
  apply findParent_eq_of_columns
  intro c hcle
  exact buildFrom_preserves_columns h (Nat.lt_of_le_of_lt hcle hc)

/-- Completing a partial column retains every existing cell exactly. -/
theorem growColumn_preserves_cells {left : Mountain} {fuel : Nat}
    {column result : Column} (h : growColumn left fuel column = .ok result)
    {i : Nat} (hi : i < column.size) : result[i]? = column[i]? := by
  induction fuel generalizing column with
  | zero =>
    rw [growColumn] at h
    cases hb : column.back? with
    | none => simp [hb] at h
    | some child =>
      by_cases ht : child.value = 1
      · have he : column = result := by simpa [hb, ht] using h
        subst result
        rfl
      · by_cases hz : child.value = 0 <;> simp [hb, ht, hz] at h
  | succ fuel ih =>
    rw [growColumn] at h
    cases hb : column.back? with
    | none => simp [hb] at h
    | some child =>
      by_cases ht : child.value = 1
      · have he : column = result := by simpa [hb, ht] using h
        subst result
        rfl
      · by_cases hz : child.value = 0
        · simp [hb, ht, hz] at h
        · cases hp : findParent (left.push column) ⟨left.size, column.size - 1⟩ with
          | error e => simp [hb, ht, hz, hp] at h
          | ok parentRef =>
            cases hr : cellAt (left.push column) parentRef with
            | error e => simp [hb, ht, hz, hp, hr] at h
            | ok parent =>
              let next : Cell := ⟨Row.B child.row parent.row,
                child.value - parent.value, some parentRef⟩
              have hRest : growColumn left fuel (column.push next) = .ok result := by
                simpa only [hb, ht, hz, if_false, hp, hr,
                  except_bind_ok] using h
              have hi' : i < (column.push next).size := by simp only [Array.size_push]; omega
              exact (ih hRest hi').trans (by simp [Array.getElem?_push, Nat.ne_of_lt hi])

theorem growColumn_size_le {left : Mountain} {fuel : Nat} {column result : Column}
    (h : growColumn left fuel column = .ok result) : column.size ≤ result.size := by
  by_cases hz : column.size = 0
  · omega
  · have hi : column.size - 1 < column.size := by omega
    have hCell := growColumn_preserves_cells h hi
    rw [Array.getElem?_eq_getElem hi] at hCell
    obtain ⟨hr, _⟩ := Array.getElem?_eq_some_iff.mp hCell
    omega

/-- Every old node of the current column keeps its actual numerical parent
through the entire successful completion of that column. -/
theorem growColumn_preserves_parent {left : Mountain} {fuel : Nat}
    {column result : Column} (h : growColumn left fuel column = .ok result)
    {i : Nat} (hi : i < column.size) :
    findParent (left.push result) ⟨left.size, i⟩ =
      findParent (left.push column) ⟨left.size, i⟩ :=
  findParent_last_column (growColumn_preserves_cells h hi)

#print axioms findParent_eq_of_left_columns
#print axioms findParent_push_cell
#print axioms buildFrom_preserves_parent
#print axioms growColumn_preserves_parent

end OmegaY.Canonical
