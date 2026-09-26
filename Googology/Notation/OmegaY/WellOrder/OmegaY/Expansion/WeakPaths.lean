/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/WeakPaths.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/WeakPaths.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.Build

set_option backward.do.legacy false

/-!
# Recognition of actual weak-edge paths

A weak edge is the actual operation `lower.above.left` with equal endpoint
heights. The executable check in `weakParent` also enforces leftwardness. This
file proves that the backwards marker search recognizes exactly finite paths
of these edges, using the source column itself as a sufficient allowance.
It does not assume an abstract marker oracle or a bound on mountain height.
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

theorem weakParent_column_lt {mountain : Mountain} {current parent : Ref}
    (h : weakParent mountain current = .ok (some parent)) :
    parent.column < current.column := by
  cases hcol : columnAt mountain current.column with
  | error e => simp [weakParent, hcol] at h
  | ok column =>
    cases hc : lookup mountain current with
    | error e => simp [weakParent, hcol, hc] at h
    | ok cell =>
      cases hu : column[current.index + 1]? with
      | none => simp [weakParent, hcol, hc, hu] at h
      | some upper =>
        cases hl : leftOf upper with
        | error e => simp [weakParent, hcol, hc, hu, hl] at h
        | ok left =>
          by_cases hlt : left.column < current.column
          · have hnot := Nat.not_le_of_lt hlt
            cases hp : lookup mountain left with
            | error e => simp [weakParent, hcol, hc, hu, hl, hnot, hp] at h
            | ok parentCell =>
              by_cases heq : parentCell.row = cell.row
              · have he : left = parent := by
                  simpa [weakParent, hcol, hc, hu, hl, hlt, hnot, hp, heq] using h
                exact he ▸ hlt
              · simp [weakParent, hcol, hc, hu, hl, hnot, hp, heq] at h
          · have hle := Nat.le_of_not_gt hlt
            simp [weakParent, hcol, hc, hu, hl, hle] at h

/-- A reflexive finite forward path of actual weak edges. Marker enumeration
uses only paths whose final column lies strictly to the right of the root. -/
inductive WeakPath (mountain : Mountain) (root : Ref) : Ref → Prop
  | root : WeakPath mountain root root
  | step {parent current : Ref}
      (previous : WeakPath mountain root parent)
      (edge : weakParent mountain current = .ok (some parent)) :
      WeakPath mountain root current

theorem WeakPath.column_le {mountain : Mountain} {root current : Ref}
    (path : WeakPath mountain root current) : root.column ≤ current.column := by
  induction path with
  | root => exact Nat.le_refl _
  | step _ edge ih => exact Nat.le_trans ih (Nat.le_of_lt (weakParent_column_lt edge))

theorem weakReaches_sound {mountain : Mountain} {root current : Ref} {fuel : Nat}
    (h : weakReaches mountain root fuel current = .ok true) :
    WeakPath mountain root current := by
  induction fuel generalizing current with
  | zero =>
    by_cases he : current = root
    · subst current; exact .root
    · simp [weakReaches, he] at h
  | succ fuel ih =>
    by_cases he : current = root
    · subst current; exact .root
    · by_cases hcol : current.column ≤ root.column
      · simp [weakReaches, he, hcol] at h
      · cases hp : weakParent mountain current with
        | error e => simp [weakReaches, he, hcol, hp] at h
        | ok parent =>
          cases parent with
          | none => simp [weakReaches, he, hcol, hp] at h
          | some parent =>
            exact .step (ih (by simpa [weakReaches, he, hcol, hp] using h)) hp

/-- No path to this root is lost to fuel exhaustion: the current column gives
a sufficient allowance, because all weak edges point strictly rightward. -/
theorem WeakPath.run {mountain : Mountain} {root current : Ref}
    (path : WeakPath mountain root current) :
    ∀ fuel, current.column ≤ fuel → weakReaches mountain root fuel current = .ok true := by
  induction path with
  | root =>
    intro fuel _
    cases fuel <;> simp [weakReaches]
  | @step parent current previous edge ih =>
    intro fuel hFuel
    have hlt := weakParent_column_lt edge
    have hroot := previous.column_le
    have he : current ≠ root := by intro h; subst current; omega
    have hcol : ¬ current.column ≤ root.column := by omega
    cases fuel with
    | zero => omega
    | succ fuel =>
      simpa [weakReaches, he, hcol, edge] using ih fuel (by omega)

theorem weakReaches_iff {mountain : Mountain} {root current : Ref} {fuel : Nat}
    (hFuel : current.column ≤ fuel) :
    weakReaches mountain root fuel current = .ok true ↔ WeakPath mountain root current :=
  ⟨weakReaches_sound, fun path => path.run fuel hFuel⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.weakParent_column_lt
#print axioms OmegaY.Expansion.weakReaches_iff
