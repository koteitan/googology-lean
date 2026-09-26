/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Canonical/Values.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Canonical/Values.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.Locality
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.Invariant

set_option backward.do.legacy false

/-! Successful canonical construction preserves the supplied bottom values.
These statements follow the actual array builder and impose no global success
assumption. They complement totality with fidelity to the input sequence. -/

namespace OmegaY.Canonical

def bottomValue (column : Column) : Option Nat := (column[1]?).map Cell.value
def bottomValues (mountain : Mountain) : List (Option Nat) :=
  mountain.toList.map bottomValue

theorem buildColumn_bottom {mountain : Mountain} {value : Nat} {column : Column}
    (h : buildColumn mountain value = .ok column) :
    column[1]? = some (initialBottom mountain.size value) := by
  by_cases hz : value = 0
  · simp [buildColumn, hz] at h
  · have hr : growColumn mountain (value - 1) (initialColumn mountain.size value) =
        .ok column := by simpa [buildColumn, hz] using h
    have he := growColumn_preserves_cells hr
      (show 1 < (initialColumn mountain.size value).size by simp [initialColumn])
    simpa [initialColumn, initialBottom] using he

theorem buildColumn_bottom_value {mountain : Mountain} {value : Nat} {column : Column}
    (h : buildColumn mountain value = .ok column) : bottomValue column = some value := by
  simp [bottomValue, buildColumn_bottom h, initialBottom]

@[simp] theorem bottomValues_empty : bottomValues #[] = [] := rfl

@[simp] theorem bottomValues_push (mountain : Mountain) (column : Column) :
    bottomValues (mountain.push column) = bottomValues mountain ++ [bottomValue column] := by
  simp [bottomValues]

theorem buildFrom_bottom_values {mountain result : Mountain} {values : List Nat}
    (h : buildFrom mountain values = .ok result) :
    bottomValues result = bottomValues mountain ++ values.map some := by
  induction values generalizing mountain with
  | nil =>
      have he : mountain = result := by simpa [buildFrom] using h
      subst result
      simp
  | cons value rest ih =>
      cases hb : buildColumn mountain value with
      | error e => simp [buildFrom, hb] at h
      | ok column =>
          have hr : buildFrom (mountain.push column) rest = .ok result := by
            simpa [buildFrom, hb] using h
          rw [ih hr, bottomValues_push, buildColumn_bottom_value hb]
          simp only [List.map_cons, List.append_assoc, List.singleton_append]

/-- Each returned bottom value is exactly the corresponding input, including
for arbitrary successful builds beyond the finite comparison fixtures. -/
theorem build_bottom_values {values : List Nat} {mountain : Mountain}
    (h : build values = .ok mountain) : bottomValues mountain = values.map some := by
  simpa using buildFrom_bottom_values (buildFrom_of_build h)

theorem build_bottom_at {values : List Nat} {mountain : Mountain} {index value : Nat}
    (h : build values = .ok mountain) (hv : values[index]? = some value) :
    ∃ column, mountain[index]? = some column ∧ bottomValue column = some value := by
  have he := congrArg (fun xs : List (Option Nat) => xs[index]?) (build_bottom_values h)
  simp only [bottomValues, List.getElem?_map, Array.getElem?_toList, hv,
    Option.map_some] at he
  cases hc : mountain[index]? with
  | none => simp [hc] at he
  | some column =>
      exact ⟨column, rfl, by simpa [hc] using he⟩

end OmegaY.Canonical

#print axioms OmegaY.Canonical.buildColumn_bottom
#print axioms OmegaY.Canonical.build_bottom_values
#print axioms OmegaY.Canonical.build_bottom_at
