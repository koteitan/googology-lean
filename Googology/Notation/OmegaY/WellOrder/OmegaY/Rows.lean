/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Rows.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Rows.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.SplitIfs

set_option backward.do.legacy false

/-!
# Finite Cantor rows for the actual weak-magma omega-Y algorithm

The coefficient of exponent `i` is a natural number; only finitely many
coefficients are nonzero. The order compares at the largest differing exponent.
Thus trailing zeroes in the JavaScript ascending coefficient arrays carry no
data here. No ordinal row is replaced by an ordinary natural-number height.

`jump = differenceDegree + 1` avoids a negative index in the implementation.
`bump a d` is ordinal right addition of omega^d, not coefficientwise addition.
-/

namespace OmegaY

structure Row where
  coeffs : Nat →₀ Nat
  deriving DecidableEq

namespace Row

def coeff (a : Row) (i : Nat) : Nat := a.coeffs i

private def listCoeff (xs : List Nat) (i : Nat) : Nat :=
  if h : i < xs.length then xs[i] else 0

/-- Interpret the engine's ascending coefficient list, ignoring trailing zeros. -/
def ofList (xs : List Nat) : Row where
  coeffs := {
    support := (Finset.range xs.length).filter fun i => listCoeff xs i ≠ 0
    toFun := listCoeff xs
    mem_support_toFun := by
      intro i
      simp only [Finset.mem_filter, Finset.mem_range]
      by_cases h : i < xs.length
      · simp [h]
      · simp [h, listCoeff] }

@[simp] theorem coeff_ofList_at (xs : List Nat) (i : Nat) (h : i < xs.length) :
    coeff (ofList xs) i = xs[i] := by simp [coeff, ofList, listCoeff, h]

@[simp] theorem coeff_ofList_above (xs : List Nat) (i : Nat) (h : xs.length ≤ i) :
    coeff (ofList xs) i = 0 := by simp [coeff, ofList, listCoeff, Nat.not_lt.mpr h]

theorem coeff_ofList (xs : List Nat) (i : Nat) :
    coeff (ofList xs) i = xs[i]?.getD 0 := by
  by_cases h : i < xs.length
  · simp [coeff, ofList, listCoeff, h]
  · simp [coeff, ofList, listCoeff, h]

instance (n : Nat) : OfNat Row n := ⟨ofList [n]⟩
instance : NatCast Row := ⟨fun n => ofList [n]⟩
instance : Inhabited Row := ⟨0⟩

def toList (a : Row) : List Nat :=
  (List.range (a.coeffs.support.sup (fun i => i+1))).map (coeff a)

@[ext] theorem ext {a b : Row} (h : ∀ i, coeff a i = coeff b i) : a = b := by
  cases a with | mk a =>
    cases b with | mk b =>
      have he : a = b := Finsupp.ext h
      exact congrArg Row.mk he

@[simp] theorem ofList_append_zeros (xs : List Nat) (n : Nat) :
    ofList (xs ++ List.replicate n 0) = ofList xs := by
  apply ext
  intro i
  simp only [coeff_ofList]
  by_cases hi : i < xs.length
  · rw [List.getElem?_append_left hi]
  · rw [List.getElem?_append_right (Nat.le_of_not_gt hi), List.getElem?_replicate]
    simp only [List.getElem?_eq_none (Nat.le_of_not_gt hi), Option.getD_none]
    split <;> rfl

@[simp] theorem coeff_nat (n i : Nat) : coeff (n : Row) i = if i = 0 then n else 0 := by
  change coeff (ofList [n]) i = _
  cases i with
  | zero => rfl
  | succ i => exact coeff_ofList_above [n] (i+1) (Nat.succ_le_succ (Nat.zero_le i))

@[simp] theorem coeff_zero (i : Nat) : coeff (0 : Row) i = 0 := by
  change coeff (ofList [0]) i = 0
  cases i with
  | zero => rfl
  | succ i => exact coeff_ofList_above [0] (i+1) (Nat.succ_le_succ (Nat.zero_le i))

/-- The exact finite set of differing exponents. -/
def differences (a b : Row) : Finset Nat :=
  (a.coeffs.support ∪ b.coeffs.support).filter fun i => coeff a i ≠ coeff b i

@[simp] theorem mem_differences {a b : Row} {i : Nat} :
    i ∈ differences a b ↔ coeff a i ≠ coeff b i := by
  simp only [differences, Finset.mem_filter, Finset.mem_union, Finsupp.mem_support_iff]
  change ((coeff a i ≠ 0 ∨ coeff b i ≠ 0) ∧ coeff a i ≠ coeff b i) ↔ _
  omega

/-- Zero on equal rows; otherwise one plus the highest differing exponent. -/
def jump (a b : Row) : Nat := (differences a b).sup (fun i => i + 1)

/-- Same signed convention as the JavaScript `differenceDegree`. -/
def differenceDegree (a b : Row) : Int := (jump a b : Int) - 1

theorem jump_le_iff {a b : Row} {d : Nat} :
    jump a b ≤ d ↔ ∀ i, d ≤ i → coeff a i = coeff b i := by
  rw [jump, Finset.sup_le_iff]
  constructor
  · intro h i hi
    by_contra hn
    have := h i (mem_differences.mpr hn)
    omega
  · intro h i hi
    have hn := mem_differences.mp hi
    by_contra hb
    exact hn (h i (by omega))

theorem coeff_eq_of_jump_le {a b : Row} {d i : Nat}
    (h : jump a b ≤ d) (hi : d ≤ i) : coeff a i = coeff b i :=
  jump_le_iff.mp h i hi

@[simp] theorem jump_self (a : Row) : jump a a = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact jump_le_iff.mpr (fun _ _ => rfl)

@[simp] theorem jump_eq_zero {a b : Row} : jump a b = 0 ↔ a = b := by
  constructor
  · intro h
    apply ext
    intro i
    exact jump_le_iff.mp (Nat.le_of_eq h) i (Nat.zero_le _)
  · rintro rfl
    exact jump_self _

theorem jump_comm (a b : Row) : jump a b = jump b a := by
  apply Nat.le_antisymm
  · exact jump_le_iff.mpr (fun i hi => (jump_le_iff.mp (Nat.le_refl _) i hi).symm)
  · exact jump_le_iff.mpr (fun i hi => (jump_le_iff.mp (Nat.le_refl _) i hi).symm)

def LexLt (a b : Row) : Prop :=
  ∃ i, (∀ j, i < j → coeff a j = coeff b j) ∧ coeff a i < coeff b i

theorem jump_eq_succ_of_last {a b : Row} {i : Nat}
    (h : coeff a i ≠ coeff b i) (hh : ∀ j, i < j → coeff a j = coeff b j) :
    jump a b = i + 1 := by
  apply Nat.le_antisymm
  · exact jump_le_iff.mpr (fun j hj => hh j (by omega))
  · exact Finset.le_sup (mem_differences.mpr h)

theorem lexLt_iff_last {a b : Row} : LexLt a b ↔
    coeff a (jump a b - 1) < coeff b (jump a b - 1) := by
  constructor
  · rintro ⟨i, hh, hi⟩
    rw [jump_eq_succ_of_last (Nat.ne_of_lt hi) hh]
    simpa using hi
  · intro hi
    refine ⟨jump a b - 1, ?_, hi⟩
    intro j hj
    exact jump_le_iff.mp (Nat.le_refl _) j (by omega)

theorem lexLt_irrefl (a : Row) : ¬ LexLt a a := by
  rintro ⟨i, _, hi⟩
  exact Nat.lt_irrefl _ hi

theorem lexLt_trans {a b c : Row} (hab : LexLt a b) (hbc : LexLt b c) : LexLt a c := by
  rcases hab with ⟨i, hai, hi⟩
  rcases hbc with ⟨j, hbj, hj⟩
  rcases Nat.lt_trichotomy i j with hij | hij | hij
  · refine ⟨j, ?_, ?_⟩
    · intro k hk
      exact (hai k (by omega)).trans (hbj k hk)
    · rw [hai j hij]
      exact hj
  · subst j
    refine ⟨i, fun k hk => (hai k hk).trans (hbj k hk), Nat.lt_trans hi hj⟩
  · refine ⟨i, ?_, ?_⟩
    · intro k hk
      exact (hai k hk).trans (hbj k (by omega))
    · rw [← hbj i hij]
      exact hi

theorem last_ne_of_ne {a b : Row} (h : a ≠ b) :
    coeff a (jump a b - 1) ≠ coeff b (jump a b - 1) := by
  have hp : 0 < jump a b := Nat.pos_of_ne_zero (fun he => h (jump_eq_zero.mp he))
  intro he
  have hle : jump a b ≤ jump a b - 1 := by
    apply jump_le_iff.mpr
    intro i hi
    by_cases heq : i = jump a b - 1
    · simpa [heq] using he
    · exact jump_le_iff.mp (Nat.le_refl _) i (by omega)
  omega

theorem lexLt_total (a b : Row) : LexLt a b ∨ a = b ∨ LexLt b a := by
  by_cases he : a = b
  · exact Or.inr (Or.inl he)
  · rcases Nat.lt_or_gt_of_ne (last_ne_of_ne he) with hl | hr
    · exact Or.inl (lexLt_iff_last.mpr hl)
    · apply Or.inr; apply Or.inr; apply lexLt_iff_last.mpr
      simpa only [jump_comm b a] using hr

instance instLT : LT Row := ⟨LexLt⟩
instance instLE : LE Row := ⟨fun a b => a = b ∨ LexLt a b⟩

instance instDecidableLT : DecidableLT Row := fun a b =>
  decidable_of_iff (coeff a (jump a b - 1) < coeff b (jump a b - 1)) lexLt_iff_last.symm

instance instDecidableLE : DecidableLE Row := fun a b =>
  inferInstanceAs (Decidable (a = b ∨ a < b))

instance instLinearOrder : LinearOrder Row where
  le_refl a := Or.inl rfl
  le_trans a b c hab hbc := by
    rcases hab with rfl | hab
    · exact hbc
    rcases hbc with rfl | hbc
    · exact Or.inr hab
    exact Or.inr (lexLt_trans hab hbc)
  le_antisymm a b hab hba := by
    rcases hab with he | hab
    · exact he
    rcases hba with he | hba
    · exact he.symm
    exact False.elim (lexLt_irrefl a (lexLt_trans hab hba))
  lt_iff_le_not_ge a b := by
    constructor
    · intro hab
      refine ⟨Or.inr hab, ?_⟩
      rintro (he | hba)
      · subst b; exact lexLt_irrefl a hab
      · exact lexLt_irrefl a (lexLt_trans hab hba)
    · rintro ⟨he | hab, hn⟩
      · exact False.elim (hn (Or.inl he.symm))
      · exact hab
  le_total a b := by
    rcases lexLt_total a b with h | h | h
    · exact Or.inl (Or.inr h)
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inr h)
  toDecidableLE := instDecidableLE
  toDecidableLT := instDecidableLT
  toDecidableEq := inferInstance

theorem lt_iff {a b : Row} : a < b ↔
    ∃ i, (∀ j, i < j → coeff a j = coeff b j) ∧ coeff a i < coeff b i := Iff.rfl

theorem le_of_coeff_le {a b : Row} (h : ∀ i, coeff a i ≤ coeff b i) : a ≤ b := by
  apply le_of_not_gt
  rintro ⟨i, _, hi⟩
  exact Nat.not_lt_of_ge (h i) hi

theorem zero_le (a : Row) : (0 : Row) ≤ a :=
  le_of_coeff_le (by intro i; simp)

theorem zero_lt_one : (0 : Row) < 1 := by decide

theorem jump_triangle (a b c : Row) :
    jump a c ≤ max (jump a b) (jump b c) := by
  apply jump_le_iff.mpr
  intro i hi
  exact (jump_le_iff.mp (Nat.le_refl (jump a b)) i (by omega)).trans
    (jump_le_iff.mp (Nat.le_refl (jump b c)) i (by omega))

/-- High coefficient agreement is convex for Cantor comparison. -/
theorem jump_le_between {a b c : Row} {d : Nat}
    (hab : a ≤ b) (hbc : b ≤ c) (hac : jump a c ≤ d) :
    jump a b ≤ d ∧ jump b c ≤ d := by
  have habd : jump a b ≤ d := by
    by_contra hn
    have hne : a ≠ b := by
      intro he
      subst b
      simp only [jump_self] at hn
      omega
    obtain ⟨i, hh, hi⟩ := lt_iff.mp (lt_of_le_of_ne hab hne)
    have hj := jump_eq_succ_of_last (Nat.ne_of_lt hi) hh
    have hdi : d ≤ i := by omega
    have hcb : c < b := by
      apply lt_iff.mpr
      refine ⟨i, ?_, ?_⟩
      · intro j hij
        exact (jump_le_iff.mp hac j (by omega)).symm.trans (hh j hij)
      · rw [← jump_le_iff.mp hac i hdi]
        exact hi
    exact (not_lt_of_ge hbc) hcb
  refine ⟨habd, jump_le_iff.mpr ?_⟩
  intro i hi
  exact (jump_le_iff.mp habd i hi).symm.trans (jump_le_iff.mp hac i hi)

theorem jump_max {a b c : Row} (hab : a ≤ b) (hbc : b ≤ c) :
    jump a c = max (jump a b) (jump b c) := by
  apply Nat.le_antisymm (jump_triangle a b c)
  obtain ⟨h₁, h₂⟩ := jump_le_between hab hbc (Nat.le_refl (jump a c))
  exact max_le h₁ h₂

/-- Same coefficient operation as `bump` in omega-y/engine.js. -/
def bump (a : Row) (d : Nat) : Row where
  coeffs := {
    support := insert d (a.coeffs.support.filter (fun i => d < i))
    toFun := fun i => if i < d then 0 else if i = d then coeff a i + 1 else coeff a i
    mem_support_toFun := by
      intro i
      simp only [Finset.mem_insert, Finset.mem_filter, Finsupp.mem_support_iff]
      change (i = d ∨ (coeff a i ≠ 0 ∧ d < i)) ↔ _
      split_ifs <;> omega }

theorem coeff_bump (a : Row) (d i : Nat) :
    coeff (bump a d) i = if i < d then 0 else if i = d then coeff a i + 1 else coeff a i := rfl

@[simp] theorem coeff_bump_low {a : Row} {d i : Nat} (h : i < d) :
    coeff (bump a d) i = 0 := by simp [coeff_bump, h]

@[simp] theorem coeff_bump_at (a : Row) (d : Nat) :
    coeff (bump a d) d = coeff a d + 1 := by simp [coeff_bump]

@[simp] theorem coeff_bump_high {a : Row} {d i : Nat} (h : d < i) :
    coeff (bump a d) i = coeff a i := by
  have hn : ¬ i < d := by omega
  simp [coeff_bump, hn, ne_of_gt h]

theorem lt_bump (a : Row) (d : Nat) : a < bump a d := by
  apply lt_iff.mpr
  refine ⟨d, ?_, ?_⟩
  · intro i hi
    exact (coeff_bump_high hi).symm
  · rw [coeff_bump_at]
    omega

theorem bump_eq_of_jump_le {a b : Row} {d : Nat} (h : jump a b ≤ d) :
    bump a d = bump b d := by
  apply ext
  intro i
  by_cases hi : i < d
  · simp [hi]
  · have he := jump_le_iff.mp h i (by omega)
    simp only [coeff_bump, he]

theorem bump_strictMono_exponent (a : Row) : StrictMono (bump a) := by
  intro d e hde
  apply lt_iff.mpr
  refine ⟨e, ?_, ?_⟩
  · intro i hei
    rw [coeff_bump_high (Nat.lt_trans hde hei), coeff_bump_high hei]
  · rw [coeff_bump_high hde, coeff_bump_at]
    omega

theorem bump_mono_exponent (a : Row) : Monotone (bump a) :=
  (bump_strictMono_exponent a).monotone

@[simp] theorem jump_bump (a : Row) (d : Nat) : jump a (bump a d) = d + 1 := by
  apply jump_eq_succ_of_last
  · rw [coeff_bump_at]
    omega
  · intro i hi
    exact (coeff_bump_high hi).symm

@[simp] theorem differenceDegree_bump (a : Row) (d : Nat) :
    differenceDegree a (bump a d) = (d : Int) := by
  simp [differenceDegree]

theorem bump_monotone (d : Nat) : Monotone (fun a : Row => bump a d) := by
  intro a b hab
  rcases eq_or_lt_of_le hab with rfl | hab
  · exact le_refl _
  obtain ⟨i, hh, hi⟩ := lt_iff.mp hab
  by_cases hid : i < d
  · have hj : jump a b ≤ d := by
      rw [jump_eq_succ_of_last (Nat.ne_of_lt hi) hh]
      omega
    exact le_of_eq (bump_eq_of_jump_le hj)
  · apply le_of_lt
    apply lt_iff.mpr
    refine ⟨i, ?_, ?_⟩
    · intro j hij
      rw [coeff_bump_high (by omega : d < j), coeff_bump_high (by omega : d < j)]
      exact hh j hij
    · by_cases he : i = d
      · subst i
        simp only [coeff_bump_at]
        omega
      · rw [coeff_bump_high (by omega : d < i), coeff_bump_high (by omega : d < i)]
        exact hi

/-- At the leading unequal coefficient, one unit is the least possible rise. -/
theorem bump_last_le {a b : Row} (hab : a < b) :
    bump a (jump a b - 1) ≤ b := by
  obtain ⟨i, hh, hi⟩ := lt_iff.mp hab
  rw [jump_eq_succ_of_last (Nat.ne_of_lt hi) hh]
  simp only [Nat.add_sub_cancel]
  apply le_of_coeff_le
  intro j
  rcases Nat.lt_trichotomy j i with hj | hj | hj
  · rw [coeff_bump_low hj]
    exact Nat.zero_le _
  · subst j
    rw [coeff_bump_at]
    omega
  · rw [coeff_bump_high hj, hh j hj]

/-- The half-open bump interval keeps all coefficients at and above d fixed. -/
theorem jump_le_of_lt_bump {a b : Row} {d : Nat}
    (hab : a ≤ b) (hba : b < bump a d) : jump a b ≤ d := by
  by_contra hn
  have hne : a ≠ b := by
    intro he
    subst b
    simp only [jump_self] at hn
    omega
  have h₁ := bump_mono_exponent a (by omega : d ≤ jump a b - 1)
  have h₂ := bump_last_le (lt_of_le_of_ne hab hne)
  exact (not_le_of_gt hba) (h₁.trans h₂)

/-- The row of the next difference node. -/
def B (a b : Row) : Row := bump a (jump a b)

theorem lt_B (a b : Row) : a < B a b := lt_bump _ _

@[simp] theorem B_self (a : Row) : B a a = bump a 0 := by simp [B]

/-- The ordered three-point maximum identity used at the decrement seam. -/
theorem B_max {a b c : Row} (hba : b ≤ a) (hcb : c ≤ b) :
    B a c = max (B a b) (B b c) := by
  have hj : jump a c = max (jump a b) (jump b c) := by
    calc
      jump a c = jump c a := jump_comm _ _
      _ = max (jump c b) (jump b a) := jump_max hcb hba
      _ = max (jump a b) (jump b c) := by
        rw [jump_comm c b, jump_comm b a, max_comm]
  unfold B
  rw [hj]
  by_cases hd : jump a b ≤ jump b c
  · rw [max_eq_right hd]
    have he := bump_eq_of_jump_le hd
    rw [he]
    apply (max_eq_right ?_).symm
    rw [← he]
    exact bump_mono_exponent a hd
  · have he : jump b c ≤ jump a b := by omega
    rw [max_eq_left he]
    apply (max_eq_left ?_).symm
    exact (bump_monotone (jump b c) hba).trans (bump_mono_exponent a he)

/-- If b <= a lies strictly before B(b,c), its next comparison against b
cannot rise past that same bound. No order assumption on c is needed here. -/
theorem interval_bound {a b c : Row} (hba : b ≤ a) (ha : a < B b c) :
    B a b ≤ B b c := by
  have hj : jump a b ≤ jump b c := by
    rw [jump_comm a b]
    exact jump_le_of_lt_bump hba ha
  unfold B
  have he : bump a (jump b c) = bump b (jump b c) := bump_eq_of_jump_le hj
  exact (bump_mono_exponent a hj).trans (le_of_eq he)

theorem B_eq_of_between {a b c : Row} (hba : b ≤ a) (hcb : c ≤ b)
    (ha : a < B b c) : B a c = B b c := by
  rw [B_max hba hcb, max_eq_right (interval_bound hba ha)]

def compare (a b : Row) : Ordering :=
  if a < b then .lt else if b < a then .gt else .eq

@[simp] theorem compare_eq_lt {a b : Row} : compare a b = .lt ↔ a < b := by
  simp only [compare]
  split_ifs <;> simp_all

@[simp] theorem compare_eq_eq {a b : Row} : compare a b = .eq ↔ a = b := by
  by_cases h : a < b
  · simp [compare, h, ne_of_lt h]
  · by_cases h' : b < a
    · simp [compare, h, h', ne_of_gt h']
    · have he : a = b := le_antisymm (le_of_not_gt h') (le_of_not_gt h)
      simp [compare, he]

example : toList (bump (ofList [7, 2, 3]) 1) = [0, 3, 3] := by decide
example : toList (bump (ofList [7, 2, 3]) 3) = [0, 0, 0, 1] := by decide
example : differenceDegree (ofList [3]) (ofList [1]) = 0 := by decide
example : toList (B (ofList [3]) (ofList [1])) = [0, 1] := by decide
example : compare (ofList [0, 1]) (ofList [37]) = .gt := by decide

end Row
end OmegaY

#print axioms OmegaY.Row.lt_bump
#print axioms OmegaY.Row.jump_le_iff
#print axioms OmegaY.Row.B_max
#print axioms OmegaY.Row.interval_bound
