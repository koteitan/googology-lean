/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Canonical/Prefix.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Canonical/Prefix.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.Search

set_option backward.do.legacy false

/-!
# front preservation of actual successful canonical builds

The statements below concern the executable `buildFrom` / `build`.  They do
not assume success for arbitrary legal inputs.  If a build succeeds, its input
can be split into the same successful front build followed by the suffix;
all existing columns, including values and stored references, are preserved.
-/

namespace OmegaY.Canonical

/-- Actual construction on a concatenation is sequential composition. -/
theorem buildFrom_append (mountain : Mountain) (front suffix : List Nat) :
    buildFrom mountain (front ++ suffix) =
      (buildFrom mountain front >>= fun middle => buildFrom middle suffix) := by
  induction front generalizing mountain with
  | nil => simp [buildFrom]
  | cons value rest ih =>
      cases hColumn : buildColumn mountain value with
      | error error => simp [buildFrom, hColumn]
      | ok column =>
          simpa [buildFrom, hColumn] using ih (mountain.push column)

theorem buildFrom_append_success_iff
    {mountain result : Mountain} {front suffix : List Nat} :
    buildFrom mountain (front ++ suffix) = .ok result ↔
      ∃ middle, buildFrom mountain front = .ok middle ∧
        buildFrom middle suffix = .ok result := by
  rw [buildFrom_append]
  cases hPrefix : buildFrom mountain front with
  | error error => simp
  | ok middle => simp

/-- Exactly one complete column is appended per successfully processed input. -/
theorem buildFrom_size {mountain result : Mountain} {values : List Nat}
    (h : buildFrom mountain values = .ok result) :
    result.size = mountain.size + values.length := by
  induction values generalizing mountain with
  | nil =>
      have he : mountain = result := by simpa [buildFrom] using h
      subst result
      simp
  | cons value rest ih =>
      cases hColumn : buildColumn mountain value with
      | error error => simp [buildFrom, hColumn] at h
      | ok column =>
          have hRest : buildFrom (mountain.push column) rest = .ok result := by
            simpa [buildFrom, hColumn] using h
          have hSize := ih hRest
          simp only [Array.size_push] at hSize
          simp only [List.length_cons]
          omega

/-- Successful construction preserves each old column as a complete value;
this includes every row, numeric label, and stored left reference. -/
theorem buildFrom_preserves_columns {mountain result : Mountain} {values : List Nat}
    (h : buildFrom mountain values = .ok result) {column : Nat}
    (hc : column < mountain.size) : result[column]? = mountain[column]? := by
  induction values generalizing mountain with
  | nil =>
      have he : mountain = result := by simpa [buildFrom] using h
      subst result
      rfl
  | cons value rest ih =>
      cases hColumn : buildColumn mountain value with
      | error error => simp [buildFrom, hColumn] at h
      | ok next =>
          have hRest : buildFrom (mountain.push next) rest = .ok result := by
            simpa [buildFrom, hColumn] using h
          have hIndex : column < (mountain.push next).size := by
            simpa only [Array.size_push] using (Nat.lt_succ_of_lt hc)
          have hOld : (mountain.push next)[column]? = mountain[column]? := by
            simp [Array.getElem?_push, Nat.ne_of_lt hc]
          exact (ih hRest hIndex).trans hOld

/-- Two successful builds with the same input front agree on all columns
through that front, even when their later inputs differ. -/
theorem buildFrom_common_prefix
    {mountain left right : Mountain} {front leftTail rightTail : List Nat}
    (hLeft : buildFrom mountain (front ++ leftTail) = .ok left)
    (hRight : buildFrom mountain (front ++ rightTail) = .ok right)
    {column : Nat} (hc : column < mountain.size + front.length) :
    left[column]? = right[column]? := by
  obtain ⟨middle, hPrefix, hLeftTail⟩ := buildFrom_append_success_iff.mp hLeft
  obtain ⟨other, hOther, hRightTail⟩ := buildFrom_append_success_iff.mp hRight
  have he : middle = other := Except.ok.inj (hPrefix.symm.trans hOther)
  subst other
  have hSize := buildFrom_size hPrefix
  have hIndex : column < middle.size := by omega
  exact (buildFrom_preserves_columns hLeftTail hIndex).trans
    (buildFrom_preserves_columns hRightTail hIndex).symm

/-- A successful validated build is the same successful unvalidated build;
validation never repairs or changes its input sequence. -/
theorem buildFrom_of_build {values : List Nat} {result : Mountain}
    (h : build values = .ok result) : buildFrom #[] values = .ok result := by
  cases values with
  | nil => simpa [build, buildFrom] using h
  | cons first rest =>
      cases first with
      | zero => simp [build] at h
      | succ first =>
          cases first with
          | zero =>
              cases hPositive : rest.all (fun n => 0 < n) with
              | false => simp [build, hPositive] at h
              | true => simpa [build, hPositive] using h
          | succ first => simp [build] at h

theorem build_size {values : List Nat} {result : Mountain}
    (h : build values = .ok result) : result.size = values.length := by
  simpa using buildFrom_size (buildFrom_of_build h)

theorem build_common_prefix
    {left right : Mountain} {front leftTail rightTail : List Nat}
    (hLeft : build (front ++ leftTail) = .ok left)
    (hRight : build (front ++ rightTail) = .ok right)
    {column : Nat} (hc : column < front.length) :
    left[column]? = right[column]? :=
  buildFrom_common_prefix (buildFrom_of_build hLeft) (buildFrom_of_build hRight)
    (by simpa using hc)

/-- In particular, changing the last entry cannot alter any earlier column
of two successful canonical builds. -/
theorem build_changed_last_preserves_prefix
    {left right : Mountain} {front : List Nat} {lastLeft lastRight column : Nat}
    (hLeft : build (front ++ [lastLeft]) = .ok left)
    (hRight : build (front ++ [lastRight]) = .ok right)
    (hc : column < front.length) : left[column]? = right[column]? :=
  build_common_prefix hLeft hRight hc

/-- Identical containing columns give identical complete cells at any fixed
reference, including identical row, value, and stored left reference. -/
theorem cellAt_eq_of_column_eq {left right : Mountain} {ref : Ref}
    (hColumn : left[ref.column]? = right[ref.column]?) :
    cellAt left ref = cellAt right ref := by
  unfold cellAt
  rw [hColumn]

/-- Direct executable root-restoration interface before a changed last entry. -/
theorem build_changed_last_preserves_ref
    {left right : Mountain} {front : List Nat} {lastLeft lastRight : Nat} {ref : Ref}
    (hLeft : build (front ++ [lastLeft]) = .ok left)
    (hRight : build (front ++ [lastRight]) = .ok right)
    (hc : ref.column < front.length) : cellAt left ref = cellAt right ref :=
  cellAt_eq_of_column_eq (build_changed_last_preserves_prefix hLeft hRight hc)

#print axioms buildFrom_append
#print axioms buildFrom_size
#print axioms buildFrom_preserves_columns
#print axioms build_changed_last_preserves_prefix
#print axioms build_changed_last_preserves_ref

end OmegaY.Canonical
