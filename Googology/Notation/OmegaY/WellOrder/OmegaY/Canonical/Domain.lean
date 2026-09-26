/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Canonical/Domain.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Canonical/Domain.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.Normal

set_option backward.do.legacy false

/-! The constructor succeeds exactly on the stated syntactic input domain.
The forward implication is validation alone; the reverse implication uses
the independent constructive totality theorem. -/

namespace OmegaY.Canonical

theorem build_success_legal {values : List Nat} {mountain : Mountain}
    (hBuild : build values = .ok mountain) : Legal values := by
  cases values with
  | nil => exact Or.inl rfl
  | cons first rest =>
    cases first with
    | zero => simp [build] at hBuild
    | succ first =>
      cases first with
      | zero =>
        cases hAll : rest.all (fun n => 0 < n) with
        | false => simp [build, hAll] at hBuild
        | true =>
          exact Or.inr ⟨rest, rfl,
            by simpa only [List.all_eq_true, decide_eq_true_eq] using hAll⟩
      | succ first => simp [build] at hBuild

theorem build_succeeds_iff_legal (values : List Nat) :
    (∃ mountain, build values = .ok mountain) ↔ Legal values := by
  constructor
  · rintro ⟨mountain, hBuild⟩
    exact build_success_legal hBuild
  · intro hLegal
    obtain ⟨mountain, hBuild, _⟩ := build_total hLegal
    exact ⟨mountain, hBuild⟩

theorem build_normal_of_success {values : List Nat} {mountain : Mountain}
    (hBuild : build values = .ok mountain) : (Geometry.Frame.ofMountain mountain).Normal :=
  build_normal_of_legal (build_success_legal hBuild) hBuild

theorem build_valid_of_success {values : List Nat} {mountain : Mountain}
    (hBuild : build values = .ok mountain) : MountainValid mountain := by
  obtain ⟨result, hResult, hValid, _⟩ := build_total (build_success_legal hBuild)
  have he : result = mountain := Except.ok.inj (hResult.symm.trans hBuild)
  exact he ▸ hValid

end OmegaY.Canonical

#print axioms OmegaY.Canonical.build_succeeds_iff_legal
#print axioms OmegaY.Canonical.build_normal_of_success
