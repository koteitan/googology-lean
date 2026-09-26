/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Rows/Lift.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Rows/Lift.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Rows.AddGap

set_option backward.do.legacy false

/-! # The exact interval lift t + gap(root,r): basic recovery and cap laws -/

namespace OmegaY.Row

def lift (root t r : Row) : Row := add t (gap root r)

@[simp] theorem lift_at_root (root t : Row) : lift root t root = t := by
  simp [lift]

theorem lift_identity {root r : Row} (hr : root ≤ r) : lift root root r = r :=
  add_gap hr

theorem lift_ge_target (root t r : Row) : t ≤ lift root t r := le_add _ _

theorem lift_ge_source {root t r : Row} (ht : root ≤ t) (hr : root ≤ r) :
    r ≤ lift root t r := by
  calc
    r = add root (gap root r) := (add_gap hr).symm
    _ ≤ lift root t r := add_monotone (gap root r) ht

theorem lift_high {root t r : Row} {e i : Nat}
    (hr : root ≤ r) (hrc : r < bump root e) (hi : e ≤ i) :
    coeff (lift root t r) i = coeff t i := by
  apply coeff_add_high_of_jump_le (e := e)
  · rw [jump_zero_gap hr]
    exact jump_le_of_lt_bump hr hrc
  · exact hi

theorem lt_cap_of_jump_le {root r : Row} {e : Nat} (h : jump root r ≤ e) :
    r < bump root e := by
  apply lt_iff.mpr
  refine ⟨e, ?_, ?_⟩
  · intro i hi
    rw [coeff_bump_high hi]
    exact (jump_le_iff.mp h i (by omega)).symm
  · rw [coeff_bump_at, ← jump_le_iff.mp h e (Nat.le_refl e)]
    omega

theorem lift_mem_interval {root t r : Row} {e : Nat}
    (ht : root ≤ t) (htc : t < bump root e)
    (hr : root ≤ r) (hrc : r < bump root e) :
    root ≤ lift root t r ∧ lift root t r < bump root e := by
  refine ⟨ht.trans (lift_ge_target root t r), ?_⟩
  have hj := jump_le_of_lt_bump ht htc
  apply lt_iff.mpr
  refine ⟨e, ?_, ?_⟩
  · intro i hi
    rw [lift_high hr hrc (by omega : e ≤ i), coeff_bump_high hi]
    exact (jump_le_iff.mp hj i (by omega)).symm
  · rw [lift_high hr hrc (Nat.le_refl e), coeff_bump_at,
      ← jump_le_iff.mp hj e (Nat.le_refl e)]
    omega

/-- The actual lift also resets on every jump reaching the root scale. -/
theorem bump_lift_reset {root t r : Row} {e d : Nat}
    (ht : root ≤ t) (htc : t < bump root e)
    (hr : root ≤ r) (hrc : r < bump root e) (hed : e ≤ d) :
    bump (lift root t r) d = bump r d := by
  obtain ⟨h₁, h₂⟩ := lift_mem_interval ht htc hr hrc
  exact bump_reset h₁ h₂ hr hrc hed

/-- Source nodes at or above the root cap are already fully reset. -/
theorem lift_eq_of_ge_cap {root t r : Row} {e : Nat}
    (ht : root ≤ t) (htc : t < bump root e) (hrc : bump root e ≤ r) :
    lift root t r = r := by
  have hr : root ≤ r := (le_of_lt (lt_bump root e)).trans hrc
  have hj : e < jump root r := by
    apply Nat.lt_of_not_ge
    intro h
    exact (not_lt_of_ge hrc) (lt_cap_of_jump_le h)
  have hrt := jump_le_of_lt_bump ht htc
  have he : add t (gap root r) = add root (gap root r) := by
    apply add_eq_of_jump_le
    rw [jump_comm t root, jump_zero_gap hr]
    omega
  exact he.trans (add_gap hr)

/-- The exact coefficient formula.  No interval condition on the target is
needed; the source must be on the right of the root. -/
theorem coeff_lift {root t r : Row} (hr : root ≤ r) (i : Nat) :
    coeff (lift root t r) i =
      if jump root r ≤ i then coeff t i
      else if jump root r = i + 1 then coeff t i + (coeff r i - coeff root i)
      else coeff r i := by
  rcases eq_or_lt_of_le hr with rfl | hr
  · simp [lift]
  have hne := ne_of_lt hr
  have hg := gap_ne_zero_of_lt hr
  have hj := jump_zero_gap_of_lt hr
  have hp : 0 < jump root r := Nat.pos_of_ne_zero (fun h => hne (jump_eq_zero.mp h))
  simp only [lift, coeff_add, hg, ↓reduceIte, hj, coeff_gap, hne]
  split_ifs <;> omega

theorem coeff_lift_high {root t r : Row} (hr : root ≤ r) {i : Nat}
    (hi : jump root r ≤ i) : coeff (lift root t r) i = coeff t i := by
  simp [coeff_lift hr, hi]

theorem coeff_lift_low {root t r : Row} (hr : root ≤ r) {i : Nat}
    (hi : i + 1 < jump root r) : coeff (lift root t r) i = coeff r i := by
  simp [coeff_lift hr, show ¬ jump root r ≤ i by omega,
    show jump root r ≠ i + 1 by omega]

theorem coeff_lift_at_or_above {root t r : Row} (hr : root ≤ r) {i : Nat}
    (hi : jump root r ≤ i + 1) :
    coeff (lift root t r) i = coeff t i + (coeff r i - coeff root i) := by
  by_cases h : jump root r ≤ i
  · rw [coeff_lift_high hr h, jump_le_iff.mp h i (Nat.le_refl i)]
    omega
  · have he : jump root r = i + 1 := by omega
    simp [coeff_lift hr, he]

theorem coeff_le_of_le_of_jump_le {a b : Row} {i : Nat}
    (hab : a ≤ b) (hi : jump a b ≤ i + 1) : coeff a i ≤ coeff b i := by
  by_cases h : jump a b ≤ i
  · exact le_of_eq (jump_le_iff.mp h i (Nat.le_refl i))
  · have he : jump a b = i + 1 := by omega
    have hneq : a ≠ b := by
      intro hzero
      simp [hzero] at he
    have hl := lexLt_iff_last.mp (lt_of_le_of_ne hab hneq)
    rw [he, Nat.add_sub_cancel] at hl
    exact Nat.le_of_lt hl

/-- The same highest unequal coefficient witnesses strict order after a lift. -/
theorem lift_order_witness {root t q r : Row} {i : Nat} (hq : root ≤ q)
    (hh : ∀ j, i < j → coeff q j = coeff r j) (hi : coeff q i < coeff r i) :
    (∀ j, i < j → coeff (lift root t q) j = coeff (lift root t r) j) ∧
      coeff (lift root t q) i < coeff (lift root t r) i := by
  have hqr : q < r := lt_iff.mpr ⟨i, hh, hi⟩
  have hr := hq.trans (le_of_lt hqr)
  have hjqr : jump q r = i + 1 := jump_eq_succ_of_last (Nat.ne_of_lt hi) hh
  have hj : jump root r = max (jump root q) (i + 1) := by
    simpa only [hjqr] using jump_max hq (le_of_lt hqr)
  constructor
  · intro j hij
    by_cases hd : i + 1 < jump root q
    · have he : jump root r = jump root q := by omega
      rw [coeff_lift hq, coeff_lift hr, he, hh j hij]
    · have hqj : jump root q ≤ j := by omega
      have hrj : jump root r ≤ j := by omega
      rw [coeff_lift_high hq hqj, coeff_lift_high hr hrj]
  · by_cases hd : i + 1 < jump root q
    · have hdr : i + 1 < jump root r := by omega
      rw [coeff_lift_low hq hd, coeff_lift_low hr hdr]
      exact hi
    · have hqd : jump root q ≤ i + 1 := by omega
      have hrd : jump root r ≤ i + 1 := by omega
      rw [coeff_lift_at_or_above hq hqd, coeff_lift_at_or_above hr hrd]
      have hroot := coeff_le_of_le_of_jump_le hq hqd
      omega

/-- Source order is preserved strictly, even without an upper bound on t. -/
theorem lift_strictMono {root t q r : Row} (hq : root ≤ q) (hqr : q < r) :
    lift root t q < lift root t r := by
  obtain ⟨i, hh, hi⟩ := lt_iff.mp hqr
  obtain ⟨hh', hi'⟩ := lift_order_witness (t := t) hq hh hi
  exact lt_iff.mpr ⟨i, hh', hi'⟩

theorem lift_monotone {root t q r : Row} (hq : root ≤ q) (hqr : q ≤ r) :
    lift root t q ≤ lift root t r := by
  rcases eq_or_lt_of_le hqr with rfl | hqr
  · exact le_refl _
  · exact le_of_lt (lift_strictMono hq hqr)

/-- Lifting preserves the highest differing exponent of any two source rows. -/
theorem jump_lift {root t q r : Row} (hq : root ≤ q) (hr : root ≤ r) :
    jump (lift root t q) (lift root t r) = jump q r := by
  rcases lt_trichotomy q r with hqr | hqr | hrq
  · obtain ⟨i, hh, hi⟩ := lt_iff.mp hqr
    obtain ⟨hh', hi'⟩ := lift_order_witness (t := t) hq hh hi
    rw [jump_eq_succ_of_last (Nat.ne_of_lt hi') hh',
      jump_eq_succ_of_last (Nat.ne_of_lt hi) hh]
  · subst r
    simp
  · obtain ⟨i, hh, hi⟩ := lt_iff.mp hrq
    obtain ⟨hh', hi'⟩ := lift_order_witness (t := t) hr hh hi
    rw [jump_comm (lift root t q), jump_comm q,
      jump_eq_succ_of_last (Nat.ne_of_lt hi') hh',
      jump_eq_succ_of_last (Nat.ne_of_lt hi) hh]

theorem differenceDegree_lift {root t q r : Row} (hq : root ≤ q) (hr : root ≤ r) :
    differenceDegree (lift root t q) (lift root t r) = differenceDegree q r := by
  simp only [differenceDegree, jump_lift hq hr]

/-- Every source bump transports by exactly the same exponent. -/
theorem lift_bump {root t r : Row} (hr : root ≤ r) (d : Nat) :
    lift root t (bump r d) = bump (lift root t r) d := by
  have hrb := hr.trans (le_of_lt (lt_bump r d))
  have hj : jump root (bump r d) = max (jump root r) (d + 1) := by
    simpa only [jump_bump] using jump_max hr (le_of_lt (lt_bump r d))
  apply ext
  intro i
  rcases Nat.lt_trichotomy i d with hi | hi | hi
  · have hil : i + 1 < jump root (bump r d) := by omega
    rw [coeff_lift_low hrb hil, coeff_bump_low hi, coeff_bump_low hi]
  · subst i
    by_cases hd : d + 1 < jump root r
    · have hdb : d + 1 < jump root (bump r d) := by omega
      rw [coeff_lift_low hrb hdb, coeff_bump_at, coeff_bump_at,
        coeff_lift_low hr hd]
    · have hrd : jump root r ≤ d + 1 := by omega
      have hbd : jump root (bump r d) ≤ d + 1 := by omega
      rw [coeff_lift_at_or_above hrb hbd, coeff_bump_at, coeff_bump_at,
        coeff_lift_at_or_above hr hrd]
      have hroot := coeff_le_of_le_of_jump_le hr hrd
      omega
  · rw [coeff_bump_high hi]
    by_cases hri : jump root r ≤ i
    · have hbi : jump root (bump r d) ≤ i := by omega
      rw [coeff_lift_high hrb hbi, coeff_lift_high hr hri]
    · have he : jump root (bump r d) = jump root r := by omega
      rw [coeff_lift hrb, coeff_lift hr, he, coeff_bump_high hi]

/-- The exact next-row formula transports with a common lift of both endpoints. -/
theorem lift_B {root t q r : Row} (hq : root ≤ q) (hr : root ≤ r) :
    lift root t (B q r) = B (lift root t q) (lift root t r) := by
  simp only [B, lift_bump hq, jump_lift hq hr]

/-- The operational finite bump path is exactly the pointwise interval lift. -/
theorem lift_run {root t r : Row} (hr : root ≤ r) (ds : List Nat) :
    lift root t (run r ds) = run (lift root t r) ds := by
  induction ds generalizing r with
  | nil => rfl
  | cons d ds ih =>
    change lift root t (run (bump r d) ds) = run (bump (lift root t r) d) ds
    rw [ih (hr.trans (le_of_lt (lt_bump r d))), lift_bump hr]

theorem run_eq_lift (root t : Row) (ds : List Nat) :
    run t ds = lift root t (run root ds) := by
  rw [lift_run (le_refl root), lift_at_root]

example : toList (lift (ofList [2]) (ofList [5]) (ofList [4])) = [7] := by decide
example : toList (lift (ofList [2]) (ofList [5]) (ofList [1, 1])) = [1, 1] := by decide

end OmegaY.Row

#print axioms OmegaY.Row.lift_mem_interval
#print axioms OmegaY.Row.lift_ge_source
#print axioms OmegaY.Row.bump_lift_reset
#print axioms OmegaY.Row.lift_eq_of_ge_cap
#print axioms OmegaY.Row.lift_strictMono
#print axioms OmegaY.Row.jump_lift
#print axioms OmegaY.Row.lift_bump
#print axioms OmegaY.Row.lift_B
#print axioms OmegaY.Row.run_eq_lift
