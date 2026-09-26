/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Canonical/Search.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Canonical/Search.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.Build

set_option backward.do.legacy false

/-!
# Correctness of canonical candidate search

`FirstSmaller` follows the actual executable Q steps and records every rejected
candidate.  The column-derived search allowance is sufficient for every such
finite first-smaller search.  This proves that this allowance does not discard
an existing answer; it does not yet prove that an answer exists for every node
of every legal-input mountain.
-/

namespace OmegaY.Canonical

@[simp] theorem except_bind_ok {α β : Type} (a : α) (f : α → Except BuildError β) :
    (Except.ok a >>= f) = f a := rfl

@[simp] theorem except_bind_error {α β : Type} (error : BuildError)
    (f : α → Except BuildError β) :
    (Except.error error >>= f) = Except.error error := rfl

@[simp] theorem except_pure {α : Type} (a : α) :
    (pure a : Except BuildError α) = Except.ok a := rfl

@[simp] theorem except_throw {α : Type} (error : BuildError) :
    (throw error : Except BuildError α) = Except.error error := rfl

/-- A direct operational specification of the first positive value smaller
than the fixed original threshold along consecutive Q steps. -/
inductive FirstSmaller (mountain : Mountain) (threshold : Nat) : Ref → Ref → Prop
  | hit {current found : Ref} {cell : Cell}
      (hNext : nextCandidate mountain current = .ok found)
      (hCell : cellAt mountain found = .ok cell)
      (hPositive : 0 < cell.value) (hSmall : cell.value < threshold) :
      FirstSmaller mountain threshold current found
  | skip {current next found : Ref} {cell : Cell}
      (hNext : nextCandidate mountain current = .ok next)
      (hCell : cellAt mountain next = .ok cell)
      (hReject : ¬ (0 < cell.value ∧ cell.value < threshold))
      (hRest : FirstSmaller mountain threshold next found) :
      FirstSmaller mountain threshold current found

theorem nextCandidate_column_lt {mountain : Mountain} {current found : Ref}
    (h : nextCandidate mountain current = .ok found) :
    found.column < current.column := by
  cases hc : cellAt mountain current with
  | error e => simp [nextCandidate, hc] at h
  | ok cell =>
      cases hl : cell.left with
      | none => simp [nextCandidate, hc, hl] at h
      | some left =>
          by_cases hLeft : left.column < current.column
          · have hNot : ¬ current.column ≤ left.column := by omega
            cases hp : cellAt mountain left with
            | error e => simp [nextCandidate, hc, hl, hNot, hp] at h
            | ok parent =>
                cases hcol : mountain[left.column]? with
                | none => simp [nextCandidate, hc, hl, hNot, hp, hcol] at h
                | some column =>
                    have he :
                        (⟨left.column, climb cell.row left.index
                          (column.toList.drop (left.index + 1))⟩ : Ref) = found := by
                      simpa [nextCandidate, hc, hl, hNot, hp, hcol] using h
                    rw [← he]
                    exact hLeft
          · have hLe : current.column ≤ left.column := by omega
            simp [nextCandidate, hc, hl, hLe] at h

theorem findParentAux_sound {mountain : Mountain} {threshold fuel : Nat}
    {current found : Ref}
    (h : findParentAux mountain threshold fuel current = .ok found) :
    FirstSmaller mountain threshold current found := by
  induction fuel generalizing current with
  | zero => simp [findParentAux] at h
  | succ fuel ih =>
      cases hNext : nextCandidate mountain current with
      | error e => simp [findParentAux, hNext] at h
      | ok next =>
          cases hCell : cellAt mountain next with
          | error e => simp [findParentAux, hNext, hCell] at h
          | ok cell =>
              by_cases hSmall : 0 < cell.value ∧ cell.value < threshold
              · have he : next = found := by
                  simpa [findParentAux, hNext, hCell, hSmall] using h
                subst found
                exact .hit hNext hCell hSmall.1 hSmall.2
              · apply FirstSmaller.skip hNext hCell hSmall
                apply ih
                simpa [findParentAux, hNext, hCell, hSmall] using h

/-- No arbitrary fuel parameter is assumed large enough: a candidate's own
column number suffices, since every successful Q step strictly lowers it. -/
theorem FirstSmaller.run {mountain : Mountain} {threshold : Nat}
    {current found : Ref} (trace : FirstSmaller mountain threshold current found) :
    ∀ fuel, current.column ≤ fuel →
      findParentAux mountain threshold fuel current = .ok found := by
  induction trace with
  | @hit current found cell hNext hCell hPositive hSmall =>
      intro fuel hFuel
      have hDecrease := nextCandidate_column_lt hNext
      cases fuel with
      | zero => omega
      | succ fuel => simp [findParentAux, hNext, hCell, hPositive, hSmall]
  | @skip current next found cell hNext hCell hReject hRest ih =>
      intro fuel hFuel
      have hDecrease := nextCandidate_column_lt hNext
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hRun := ih fuel (by omega)
          simpa [findParentAux, hNext, hCell, hReject] using hRun

theorem findParentAux_column_iff {mountain : Mountain} {threshold : Nat}
    {current found : Ref} :
    findParentAux mountain threshold current.column current = .ok found ↔
      FirstSmaller mountain threshold current found :=
  ⟨findParentAux_sound, fun h => h.run _ (Nat.le_refl _)⟩

theorem FirstSmaller.result {mountain : Mountain} {threshold : Nat}
    {current found : Ref} (trace : FirstSmaller mountain threshold current found) :
    ∃ cell, cellAt mountain found = .ok cell ∧
      0 < cell.value ∧ cell.value < threshold := by
  induction trace with
  | hit _ hCell hPositive hSmall => exact ⟨_, hCell, hPositive, hSmall⟩
  | skip _ _ _ _ ih => exact ih

theorem FirstSmaller.column_lt {mountain : Mountain} {threshold : Nat}
    {current found : Ref} (trace : FirstSmaller mountain threshold current found) :
    found.column < current.column := by
  induction trace with
  | hit hNext _ _ _ => exact nextCandidate_column_lt hNext
  | skip hNext _ _ _ ih => exact Nat.lt_trans ih (nextCandidate_column_lt hNext)

theorem FirstSmaller.unique {mountain : Mountain} {threshold : Nat}
    {current found other : Ref}
    (left : FirstSmaller mountain threshold current found)
    (right : FirstSmaller mountain threshold current other) : found = other := by
  have hl := left.run current.column (Nat.le_refl _)
  have hr := right.run current.column (Nat.le_refl _)
  exact Except.ok.inj (hl.symm.trans hr)

theorem findParent_iff {mountain : Mountain} {current found : Ref} {cell : Cell}
    (hCell : cellAt mountain current = .ok cell) :
    findParent mountain current = .ok found ↔
      FirstSmaller mountain cell.value current found := by
  simpa [findParent, hCell] using
    (findParentAux_column_iff (mountain := mountain) (threshold := cell.value)
      (current := current) (found := found))

theorem findParent_result {mountain : Mountain} {current found : Ref} {cell : Cell}
    (hCell : cellAt mountain current = .ok cell)
    (hFound : findParent mountain current = .ok found) :
    ∃ parent, cellAt mountain found = .ok parent ∧
      0 < parent.value ∧ parent.value < cell.value :=
  ((findParent_iff hCell).mp hFound).result

#print axioms findParentAux_column_iff
#print axioms FirstSmaller.unique
#print axioms findParent_result

end OmegaY.Canonical
