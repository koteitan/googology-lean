/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Rows/Intervals.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Rows/Intervals.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Rows

set_option backward.do.legacy false

/-!
# Root interval cap and reset for arbitrary Cantor degrees

These are the coefficient facts used in the full weak-magma copy totality
proof. They do not suppose the copied graph is numerically canonical.
Every interval is `[root, bump root e)`, so it may cross any finite omega
power. A finite word of the actual bump exponents remains in the interval
until its first exponent at least `e`, where its starting offset disappears.
-/

namespace OmegaY.Row

theorem jump_le_of_same_interval {root a b : Row} {e : Nat}
    (hra : root ≤ a) (ha : a < bump root e)
    (hrb : root ≤ b) (hb : b < bump root e) : jump a b ≤ e := by
  have h₁ := jump_le_of_lt_bump hra ha
  have h₂ := jump_le_of_lt_bump hrb hb
  apply jump_le_iff.mpr
  intro i hi
  exact (jump_le_iff.mp h₁ i hi).symm.trans (jump_le_iff.mp h₂ i hi)

theorem bump_lt_cap {root a : Row} {e d : Nat}
    (hra : root ≤ a) (ha : a < bump root e) (hd : d < e) :
    bump a d < bump root e := by
  have hj := jump_le_of_lt_bump hra ha
  apply lt_iff.mpr
  refine ⟨e, ?_, ?_⟩
  · intro i hi
    rw [coeff_bump_high (Nat.lt_trans hd hi), coeff_bump_high hi]
    exact (jump_le_iff.mp hj i (by omega)).symm
  · rw [coeff_bump_high hd, coeff_bump_at, ← jump_le_iff.mp hj e (Nat.le_refl e)]
    omega

theorem bump_mem_interval {root a : Row} {e d : Nat}
    (hra : root ≤ a) (ha : a < bump root e) (hd : d < e) :
    root ≤ bump a d ∧ bump a d < bump root e :=
  ⟨hra.trans (le_of_lt (lt_bump a d)), bump_lt_cap hra ha hd⟩

/-- The first sufficiently high bump erases every possible interval offset. -/
theorem bump_reset {root a b : Row} {e d : Nat}
    (hra : root ≤ a) (ha : a < bump root e)
    (hrb : root ≤ b) (hb : b < bump root e) (hed : e ≤ d) :
    bump a d = bump b d :=
  bump_eq_of_jump_le ((jump_le_of_same_interval hra ha hrb hb).trans hed)

/-- Apply a finite list of the engine's bump exponents. -/
def run (a : Row) (exponents : List Nat) : Row := exponents.foldl bump a

@[simp] theorem run_nil (a : Row) : run a [] = a := rfl
@[simp] theorem run_cons (a : Row) (d : Nat) (ds : List Nat) :
    run a (d :: ds) = run (bump a d) ds := rfl

theorem run_append (a : Row) (ds es : List Nat) :
    run a (ds ++ es) = run (run a ds) es := by simp [run, List.foldl_append]

theorem run_monotone (ds : List Nat) : Monotone (fun a : Row => run a ds) := by
  induction ds with
  | nil => intro a b h; exact h
  | cons d ds ih =>
      intro a b h
      exact ih (bump_monotone d h)

theorem le_run (a : Row) (ds : List Nat) : a ≤ run a ds := by
  induction ds generalizing a with
  | nil => exact le_refl _
  | cons d ds ih =>
      exact (le_of_lt (lt_bump a d)).trans (ih (bump a d))

theorem run_mem_interval {root a : Row} {e : Nat} (ds : List Nat)
    (hra : root ≤ a) (ha : a < bump root e)
    (hsmall : ∀ d ∈ ds, d < e) :
    root ≤ run a ds ∧ run a ds < bump root e := by
  induction ds generalizing a with
  | nil => exact ⟨hra, ha⟩
  | cons d ds ih =>
      obtain ⟨h₁, h₂⟩ := bump_mem_interval hra ha (hsmall d (by simp))
      exact ih h₁ h₂ (fun k hk => hsmall k (by simp [hk]))

/-- After the first exponent reaching the root scale, the two paths agree
at every subsequent step, with no assumption on later exponents. -/
theorem run_reset_after {root a b : Row} {e d : Nat} (before after : List Nat)
    (hra : root ≤ a) (ha : a < bump root e)
    (hrb : root ≤ b) (hb : b < bump root e)
    (hsmall : ∀ k ∈ before, k < e) (hed : e ≤ d) :
    run a (before ++ d :: after) = run b (before ++ d :: after) := by
  obtain ⟨h₁, h₂⟩ := run_mem_interval before hra ha hsmall
  obtain ⟨h₃, h₄⟩ := run_mem_interval before hrb hb hsmall
  rw [run_append, run_append, run_cons, run_cons, bump_reset h₁ h₂ h₃ h₄ hed]

/-- Any finite path either stays below the common cap or has already reset.
This avoids choosing or assuming the existence of a first high exponent. -/
theorem run_same_or_below {root a b : Row} {e : Nat} (ds : List Nat)
    (hra : root ≤ a) (ha : a < bump root e)
    (hrb : root ≤ b) (hb : b < bump root e) :
    run a ds = run b ds ∨
      (run a ds < bump root e ∧ run b ds < bump root e) := by
  induction ds generalizing a b with
  | nil => exact Or.inr ⟨ha, hb⟩
  | cons d ds ih =>
      by_cases hd : d < e
      · obtain ⟨h₁, h₂⟩ := bump_mem_interval hra ha hd
        obtain ⟨h₃, h₄⟩ := bump_mem_interval hrb hb hd
        exact ih h₁ h₂ h₃ h₄
      · exact Or.inl (congrArg (fun x => run x ds)
          (bump_reset hra ha hrb hb (Nat.le_of_not_gt hd)))

/-- The lifted path cannot exceed the old path together with the root cap. -/
theorem run_le_max {root a b : Row} {e : Nat} (ds : List Nat)
    (hra : root ≤ a) (ha : a < bump root e)
    (hrb : root ≤ b) (hb : b < bump root e) :
    run b ds ≤ max (bump root e) (run a ds) := by
  rcases run_same_or_below ds hra ha hrb hb with he | hh
  · rw [he]
    exact le_max_right _ _
  · exact (le_of_lt hh.2).trans (le_max_left _ _)

end OmegaY.Row

#print axioms OmegaY.Row.bump_reset
#print axioms OmegaY.Row.run_reset_after
#print axioms OmegaY.Row.run_le_max
