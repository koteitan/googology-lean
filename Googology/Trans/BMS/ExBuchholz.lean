import Googology.Notation.BMS
import Googology.Notation.ExBuchholz

/-!
# Bashicu matrices and extended Buchholz's ψ

What a translation between the two would buy is the **value**: which ordinal a
matrix names.  That is the ordinal analysis of BM4, and it is settled only for
few rows — one row is the primitive sequence system and lands below `ε₀`, two
rows land below the Bachmann–Howard ordinal, and three rows on are open.  So
the reachable target is one row.

This file has the map for that case.  `read` sends a one-row matrix, read as a
list of entries, to an extended Buchholz term: split the list at the entries
that are not above the current level, and send a block `a :: hi` to
`ψ_0(read (b+1) hi)`, which is `ω` to that power.  What is proved here is that the
reading is countable, that its subscripts are all `0`, and that a term of that
shape is below `ψ_0` of itself — which is what the standard-form condition
needs once the descending condition is in hand.

`unread` writes a term back as a list, and `read_unread` says the reading is
onto the terms whose subscripts are all `0`: every such term is the reading of
some one-row matrix.

`OT_of_desc` settles the standard-form side as far as the term goes: with the
subscripts all `0`, being a standard form is exactly the descending
condition.  What is left is on the matrix side — that a standard one-row
matrix reads as a descending term — and the commutation with expansion.  The
second is where the work is: `BM4.expand` is stated through
`Classical.choice`, so matching it against `fs` step for step is not a
rewriting exercise.  The two are entangled, because the descending condition
is the invariant the expansion has to preserve.
-/

namespace Googology.Trans.BMS

open Googology.Notation.ExBuchholz
open Googology.Notation.ExBuchholz.Term

/-- The primitive-sequence reading.  A one-row Bashicu matrix is a list of
entries; `read b s` reads `s` as an ordinal notation relative to the level
`b`, by splitting `s` at its entries that are not above `b`.  A block
`a :: hi`, with `hi` the entries above `b` that follow `a`, becomes
`ψ_0(read (b+1) hi)`, which is `ω` to that power. -/
def read (b : Nat) : List Nat → Term
  | [] => nil
  | _ :: rest =>
      cons nil (read (b + 1) (rest.takeWhile (fun a => decide (b < a))))
        (read b (rest.dropWhile (fun a => decide (b < a))))
  termination_by s => s.length
  decreasing_by
    all_goals simp only [List.length_cons]
    · exact Nat.lt_succ_of_le (List.takeWhile_sublist _).length_le
    · exact Nat.lt_succ_of_le (List.dropWhile_sublist _).length_le

@[simp] theorem read_nil (b : Nat) : read b [] = nil := by rw [read]

theorem read_cons (b : Nat) (a : Nat) (rest : List Nat) :
    read b (a :: rest)
      = cons nil (read (b + 1) (rest.takeWhile (fun x => decide (b < x))))
          (read b (rest.dropWhile (fun x => decide (b < x)))) := by
  rw [read]

/-- Everything the reading produces is countable: its subscripts are all
`0`. -/
theorem read_lt_tW (b : Nat) (s : List Nat) : read b s < tW := by
  cases s with
  | nil => rw [read_nil]; exact nil_lt_cons _ _ _
  | cons a rest =>
    rw [read_cons]
    exact cons_lt_cons_iff.mpr
      (Or.inl (psi_lt_psi_iff.mpr (Or.inl (nil_lt_cons _ _ _))))

/-- The reading of a nonempty list is a nonempty term. -/
theorem read_ne_nil (b : Nat) (a : Nat) (rest : List Nat) :
    read b (a :: rest) ≠ nil := by
  rw [read_cons]; exact fun h => Term.noConfusion h

/-- Every subscript in the term is `0`.  The reading of a one-row matrix has
this shape, because `ψ_0` is the only collapse it uses. -/
def AllNil : Term → Prop
  | nil => True
  | cons a b t => a = nil ∧ AllNil b ∧ AllNil t

theorem allNil_read : ∀ (b : Nat) (s : List Nat), AllNil (read b s) := by
  intro b s
  induction hn : s.length using Nat.strong_induction_on generalizing b s with
  | _ n ih =>
    cases s with
    | nil => rw [read_nil]; exact trivial
    | cons a rest =>
      rw [read_cons]
      refine ⟨rfl, ?_, ?_⟩
      · exact ih (rest.takeWhile (fun x => decide (b < x))).length
          (by subst hn; simp only [List.length_cons]
              exact Nat.lt_succ_of_le (List.takeWhile_sublist _).length_le) _ _ rfl
      · exact ih (rest.dropWhile (fun x => decide (b < x))).length
          (by subst hn; simp only [List.length_cons]
              exact Nat.lt_succ_of_le (List.dropWhile_sublist _).length_le) _ _ rfl

/-- A term whose subscripts are all `0` is below `ψ_0` of itself. -/
theorem lt_psi_self : ∀ X : Term, AllNil X → ∀ Y : Term, X < cons nil X Y := by
  intro X
  induction X with
  | nil => intro _ Y; exact nil_lt_cons _ _ _
  | cons a b t _ ihb _ =>
    intro h Y
    obtain ⟨ha, hb, _⟩ := h
    subst ha
    refine cons_lt_cons_iff.mpr (Or.inl (psi_lt_psi_iff.mpr (Or.inr ⟨rfl, ?_⟩)))
    exact ihb hb t

/-- The principal terms do not increase, everywhere in the term. -/
def DescAll : Term → Prop
  | nil => True
  | cons a b t => DescAll b ∧ DescAll t ∧ descHead a b t = true

/-- With the subscripts all `0` and the principal terms descending, the tail
of a term is below it. -/
theorem tail_lt_of_desc : ∀ t a b : Term, AllNil (cons a b t) →
    DescAll (cons a b t) → t < cons a b t := by
  intro t
  induction t with
  | nil => intro a b _ _; exact nil_lt_cons _ _ _
  | cons c d s _ _ ihs =>
    intro a b hA hD
    have hle : psi c d ≤ psi a b := by
      have := hD.2.2
      simp only [descHead, head?, decide_eq_true_eq] at this
      exact this
    rcases le_iff_lt_or_eq.mp hle with h | h
    · exact cons_lt_cons_iff.mpr (Or.inl h)
    · refine cons_lt_cons_iff.mpr (Or.inr ⟨h, ?_⟩)
      exact ihs c d hA.2.2 hD.2.1

/-- With the subscripts all `0` and the principal terms descending, `G` at
level `0` stays below the term. -/
theorem G_lt_of_desc : ∀ X : Term, AllNil X → DescAll X →
    ∀ y ∈ G nil X, y < X := by
  intro X
  induction X with
  | nil => intro _ _ y hy; rw [G_nil] at hy; exact absurd hy List.not_mem_nil
  | cons a b t _ ihb iht =>
    intro hA hD y hy
    obtain ⟨ha, hAb, hAt⟩ := hA
    subst ha
    rw [G_cons, if_pos (le_refl _), G_nil, List.nil_append] at hy
    rcases List.mem_append.mp hy with hy | hy
    · rcases List.mem_cons.mp hy with he | hy
      · rw [he]; exact lt_psi_self b hAb t
      · exact lt_trans (ihb hAb hD.1 y hy) (lt_psi_self b hAb t)
    · exact lt_trans (iht hAt hD.2.1 y hy) (tail_lt_of_desc t nil b ⟨rfl, hAb, hAt⟩ hD)

/-- **With the subscripts all `0`, being a standard form is exactly the
descending condition.** -/
theorem OT_of_desc : ∀ X : Term, AllNil X → DescAll X → OT X := by
  intro X
  induction X with
  | nil => intro _ _; exact rfl
  | cons a b t _ ihb iht =>
    intro hA hD
    obtain ⟨ha, hAb, hAt⟩ := hA
    subst ha
    have hGb : (G nil b).all (fun x => decide (x < b)) = true :=
      List.all_eq_true.mpr (fun x hx => decide_eq_true (G_lt_of_desc b hAb hD.1 x hx))
    have hb : isOT b = true := ihb hAb hD.1
    have ht : isOT t = true := iht hAt hD.2.1
    show isOT (cons nil b t) = true
    rw [isOT]
    simp only [hGb, hb, ht, hD.2.2, Bool.and_true, Bool.true_and]
    rfl

/-- The inverse reading: a term whose subscripts are all `0` is written back
as a one-row matrix, at level `b`. -/
def unread (b : Nat) : Term → List Nat
  | nil => []
  | cons _ X Y => b :: (unread (b + 1) X ++ unread b Y)

@[simp] theorem unread_nil (b : Nat) : unread b nil = [] := rfl

@[simp] theorem unread_cons (b : Nat) (a X Y : Term) :
    unread b (cons a X Y) = b :: (unread (b + 1) X ++ unread b Y) := rfl

/-- Nothing written at level `b` is below `b`. -/
theorem le_of_mem_unread : ∀ (X : Term) (b a : Nat), a ∈ unread b X → b ≤ a := by
  intro X
  induction X with
  | nil => intro b a h; exact absurd h (by simp)
  | cons _ P Q _ ihP ihQ =>
    intro b a h
    rcases List.mem_cons.mp h with he | h
    · exact Nat.le_of_eq he.symm
    rcases List.mem_append.mp h with h | h
    · exact Nat.le_of_succ_le (ihP (b + 1) a h)
    · exact ihQ b a h

theorem takeWhile_append_of_all {p : Nat → Bool} : ∀ (l₁ l₂ : List Nat),
    (∀ a ∈ l₁, p a = true) → (∀ a, l₂.head? = some a → p a = false) →
    (l₁ ++ l₂).takeWhile p = l₁ := by
  intro l₁
  induction l₁ with
  | nil =>
    intro l₂ _ h₂
    cases l₂ with
    | nil => rfl
    | cons c s => rw [List.nil_append, List.takeWhile_cons, if_neg (by rw [h₂ c rfl]; simp)]
  | cons a l₁ ih =>
    intro l₂ h₁ h₂
    rw [List.cons_append, List.takeWhile_cons, if_pos (h₁ a (List.mem_cons_self ..))]
    rw [ih l₂ (fun x hx => h₁ x (List.mem_cons_of_mem _ hx)) h₂]

theorem dropWhile_append_of_all {p : Nat → Bool} : ∀ (l₁ l₂ : List Nat),
    (∀ a ∈ l₁, p a = true) → (∀ a, l₂.head? = some a → p a = false) →
    (l₁ ++ l₂).dropWhile p = l₂ := by
  intro l₁
  induction l₁ with
  | nil =>
    intro l₂ _ h₂
    cases l₂ with
    | nil => rfl
    | cons c s => rw [List.nil_append, List.dropWhile_cons, if_neg (by rw [h₂ c rfl]; simp)]
  | cons a l₁ ih =>
    intro l₂ h₁ h₂
    rw [List.cons_append, List.dropWhile_cons, if_pos (h₁ a (List.mem_cons_self ..))]
    exact ih l₂ (fun x hx => h₁ x (List.mem_cons_of_mem _ hx)) h₂

/-- **The reading is onto the terms whose subscripts are all `0`**: writing a
term back and reading it again gives the term. -/
theorem read_unread : ∀ (X : Term), AllNil X → ∀ b : Nat, read b (unread b X) = X := by
  intro X
  induction X with
  | nil => intro _ b; rw [unread_nil, read_nil]
  | cons a P Q _ ihP ihQ =>
    intro h b
    obtain ⟨ha, hP, hQ⟩ := h
    subst ha
    have hhi : (unread (b + 1) P ++ unread b Q).takeWhile (fun x => decide (b < x))
        = unread (b + 1) P := by
      refine takeWhile_append_of_all _ _ (fun x hx => ?_) (fun x hx => ?_)
      · exact decide_eq_true (le_of_mem_unread P (b + 1) x hx)
      · cases Q with
        | nil => exact absurd hx (by simp)
        | cons c R S =>
          rw [unread_cons] at hx
          simp only [List.head?_cons, Option.some.injEq] at hx
          subst hx; simp
    have hlo : (unread (b + 1) P ++ unread b Q).dropWhile (fun x => decide (b < x))
        = unread b Q := by
      refine dropWhile_append_of_all _ _ (fun x hx => ?_) (fun x hx => ?_)
      · exact decide_eq_true (le_of_mem_unread P (b + 1) x hx)
      · cases Q with
        | nil => exact absurd hx (by simp)
        | cons c R S =>
          rw [unread_cons] at hx
          simp only [List.head?_cons, Option.some.injEq] at hx
          subst hx; simp
    rw [unread_cons, read_cons, hhi, hlo, ihP hP (b + 1), ihQ hQ b]

end Googology.Trans.BMS
