import Googology.Trans.BMS.Trio
import Googology.Trans.BMS.Tables
import Googology.Trans.BMS.Cofinal

/-!
# The trio map is order-preserving below `ε₀`

`Trio.lean` transcribes the map `ψ_0(Ω_α) ↦ M(α)` of
[koteitan/trio](https://github.com/koteitan/trio) (its
[algorithm page](https://github.com/koteitan/trio/blob/main/ebp2bms/algorithm/1/README-en.md))
for `α < ε₀`.  This file proves that the map keeps the order: for standard
`α < β < ε₀`,

  `omegaIndexMatrix α < omegaIndexMatrix β`

in the dictionary order on the matrices — the order `List.lt` on
`List (List Nat)`, a list of columns `[x, y, z]`, each column compared as a list
and a proper prefix counted as smaller.  That is the same order the library
uses on the entries of one-row matrices (`primLt`) and on the states of
`bmsL r`.  Since the order on the terms is total, the map also reflects the
order and is injective (`omegaIndexMatrix_lt_iff`, `omegaIndexMatrix_injective`).

The proof follows the three levels of the Cantor normal form.

* **Add units.**  Two sums `Σ ω^{β_i}` first differ at a summand, or one is a
  prefix of the other.  The units before the first difference are the same
  columns, and the state the map carries (`rp1`, `lastX`, `prevZero`, `i`) is
  the same after them.  A proper prefix gives a proper prefix.  At the first
  difference `β_k < β_k'`: if `β_k = 0` the other unit has the same anchor and a
  root `(r+1, i, 1)` against `(r+1, i, 0)`; the descending condition is what
  rules out the chain of `β = 0` units here (`prevZero`), because after a `1`
  only `1`s follow.
* **Multiply units.**  If both `β_k, β_k'` are positive the two bodies share
  the anchor and the root, and `β' < β''` for `1 + β' = β_k`, `1 + β'' = β_k'`
  (`peelOne_lt`).  The multiply units are a digit `(x₀+1, i, 1)` and a
  primitive-sequence embedding with `x ≥ x₀+2`, and whatever follows the last
  one starts with `(x₀+1, i, 0)`, below every digit.  So the comparison is the
  one of the sums `β', β''` (`mulUnits_lt`).
* **Exponents.**  Inside a multiply unit the embedding is `unread`, which keeps
  the order by `read_lt_read_iff` (`unread_lt`).

The terms need their subscripts all `0` (`AllNil`) and, for the larger term,
the top-level descending condition (`DescTop`); a standard form below `ε₀`
has both.  Without the descending condition the statement is false: `1 + 1`
and `1 + ω` would come out in the wrong order.
-/

namespace Googology.Trans.BMS

open Googology.Notation.ExBuchholz
open Googology.Notation.ExBuchholz.Term

namespace TrioMono

/-! ### The dictionary order on the matrices -/

/-- One column below another, by its first differing row. -/
theorem col_lt {x y z x' y' z' : Nat}
    (h : x < x' ∨ (x = x' ∧ (y < y' ∨ (y = y' ∧ z < z')))) :
    ([x, y, z] : List Nat) < [x', y', z'] := by
  rcases h with h | ⟨rfl, h | ⟨rfl, h⟩⟩
  · exact List.cons_lt_cons_iff.mpr (Or.inl h)
  · exact List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, List.cons_lt_cons_iff.mpr (Or.inl h)⟩)
  · exact List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, List.cons_lt_cons_iff.mpr
      (Or.inr ⟨rfl, List.cons_lt_cons_iff.mpr (Or.inl h)⟩)⟩)

/-- A common prefix does not change the comparison. -/
theorem append_lt_append_left : ∀ (p : List (List Nat)) {x y : List (List Nat)},
    x < y → p ++ x < p ++ y
  | [], _, _, h => h
  | _ :: p, _, _, h => List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, append_lt_append_left p h⟩)

/-- A list whose first column is below `c` is below any list starting with `c`. -/
theorem lt_cons_of_head {c : List Nat} {R : List (List Nat)} (S : List (List Nat))
    (h : ∀ d ∈ R.head?, d < c) : R < c :: S := by
  cases R with
  | nil => exact List.nil_lt_cons _ _
  | cons d R => exact List.cons_lt_cons_iff.mpr (Or.inl (h d rfl))

/-- A strictly increasing column map sends the dictionary order on `List Nat`
to the order on the column lists, whatever follows, as long as what follows
the shorter one starts below every image column. -/
theorem map_append_lt (f : Nat → List Nat) (hf : ∀ a b, a < b → f a < f b) :
    ∀ (l m : List Nat) (X Y : List (List Nat)), l < m →
      (∀ d ∈ X.head?, ∀ e, d < f e) → l.map f ++ X < m.map f ++ Y
  | [], [], _, _, h, _ => by cases h
  | [], b :: m, X, Y, _, hX => by
    rw [List.map_nil, List.nil_append, List.map_cons, List.cons_append]
    exact lt_cons_of_head _ (fun d hd => hX d hd b)
  | _ :: _, [], _, _, h, _ => by cases h
  | a :: l, b :: m, X, Y, h, hX => by
    rw [List.map_cons, List.map_cons, List.cons_append, List.cons_append]
    rcases List.cons_lt_cons_iff.mp h with h1 | ⟨rfl, h2⟩
    · exact List.cons_lt_cons_iff.mpr (Or.inl (hf a b h1))
    · exact List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, map_append_lt f hf l m X Y h2 hX⟩)

/-! ### Terms -/

theorem eq_nil_of_le_nil {b : Term} (h : b ≤ nil) : b = nil := by
  rcases le_iff_lt_or_eq.mp h with h | h
  · exact absurd h (not_lt_nil b)
  · exact h

theorem ne_nil_of_lt {b c : Term} (h : b < c) : c ≠ nil := by
  rintro rfl; exact not_lt_nil b h

/-- **`unread` keeps the order**, on the terms with every subscript `0`. -/
theorem unread_lt {g g' : Term} (hg : AllNil g) (hg' : AllNil g') (h : g < g') :
    unread 0 g < unread 0 g' := by
  rw [← read_lt_read_iff (col_unread g hg 0) (col_unread g' hg' 0), read_unread g hg,
    read_unread g' hg']
  exact h

/-- Two principal terms with subscript `0` compare as their arguments. -/
theorem arg_lt_of_psi_lt {b b' : Term} (h : psi nil b < psi nil b') : b < b' := by
  rcases psi_lt_psi_iff.mp h with h | ⟨_, h⟩
  · exact absurd h (lt_irrefl nil)
  · exact h

/-- A sum below another, both with subscripts `0`: the heads decide, or they
are equal and the tails decide. -/
theorem cons_lt_cases {b t b' t' : Term} (h : cons nil b t < cons nil b' t') :
    b < b' ∨ (b = b' ∧ t < t') := by
  rcases cons_lt_cons_iff.mp h with h | ⟨h, h'⟩
  · exact Or.inl (arg_lt_of_psi_lt h)
  · injection h with _ h
    exact Or.inr ⟨h, h'⟩

/-! ### `β ↦ β'` with `1 + β' = β` keeps the order -/

theorem allNil_dropLastT : ∀ x : Term, AllNil x → AllNil (dropLastT x)
  | nil, _ => trivial
  | cons a b t, h => by
    rw [dropLastT]
    split
    · exact trivial
    · exact ⟨h.1, h.2.1, allNil_dropLastT t h.2.2⟩

theorem allNil_peelOne (x : Term) (h : AllNil x) : AllNil (peelOne x) := by
  rw [peelOne]
  split
  · exact allNil_dropLastT x h
  · exact h

/-- Dropping the last summand makes a nonzero term smaller. -/
theorem dropLastT_lt : ∀ x : Term, x ≠ nil → dropLastT x < x
  | nil, h => absurd rfl h
  | cons a b t, _ => by
    rw [dropLastT]
    by_cases ht : t = nil
    · rw [if_pos (beq_iff_eq.mpr ht)]; exact nil_lt_cons _ _ _
    · rw [if_neg (fun h => ht (beq_iff_eq.mp h))]
      exact cons_lt_cons_iff.mpr (Or.inr ⟨rfl, dropLastT_lt t ht⟩)

/-- Below a finite term, with subscripts `0`, a term is finite. -/
theorem finite_of_lt : ∀ x y : Term, AllNil x → AllNil y → isFiniteT y = true → x < y →
    isFiniteT x = true
  | nil, _, _, _, _, _ => rfl
  | cons _ _ _, nil, _, _, _, h => absurd h (not_lt_nil _)
  | cons a c t, cons a' c' u, hx, hy, hf, h => by
    obtain ⟨rfl, _, hxt⟩ := hx
    obtain ⟨rfl, _, hyu⟩ := hy
    simp only [isFiniteT, Bool.and_eq_true, beq_iff_eq] at hf ⊢
    obtain ⟨rfl, hfu⟩ := hf
    rcases cons_lt_cases h with h | ⟨rfl, h⟩
    · exact absurd h (not_lt_nil c)
    · exact ⟨rfl, finite_of_lt t u hxt hyu hfu h⟩

/-- On the finite terms, dropping the last summand keeps the order. -/
theorem dropLastT_lt_dropLastT : ∀ x y : Term, AllNil x → AllNil y →
    isFiniteT x = true → isFiniteT y = true → x ≠ nil → x < y →
    dropLastT x < dropLastT y
  | nil, _, _, _, _, _, hne, _ => absurd rfl hne
  | cons _ _ _, nil, _, _, _, _, _, h => absurd h (not_lt_nil _)
  | cons a c t, cons a' c' u, hx, hy, hfx, hfy, _, h => by
    obtain ⟨rfl, _, hxt⟩ := hx
    obtain ⟨rfl, _, hyu⟩ := hy
    simp only [isFiniteT, Bool.and_eq_true, beq_iff_eq] at hfx hfy
    obtain ⟨rfl, hft⟩ := hfx
    obtain ⟨rfl, hfu⟩ := hfy
    have htu : t < u := by
      rcases cons_lt_cases h with h | ⟨_, h⟩
      · exact absurd h (lt_irrefl nil)
      · exact h
    have hu : u ≠ nil := ne_nil_of_lt htu
    rw [dropLastT, dropLastT, if_neg (fun h => hu (beq_iff_eq.mp h))]
    by_cases ht : t = nil
    · rw [if_pos (beq_iff_eq.mpr ht)]; exact nil_lt_cons _ _ _
    · rw [if_neg (fun h => ht (beq_iff_eq.mp h))]
      exact cons_lt_cons_iff.mpr
        (Or.inr ⟨rfl, dropLastT_lt_dropLastT t u hxt hyu hft hfu ht htu⟩)

/-- **`peelOne` keeps the order** on the nonzero terms with subscripts `0`:
`1 + β' = β < β'' + 1 = ...` gives `β' < β''`. -/
theorem peelOne_lt {b b' : Term} (hb : AllNil b) (hb' : AllNil b') (hne : b ≠ nil)
    (h : b < b') : peelOne b < peelOne b' := by
  unfold peelOne
  by_cases hf : isFiniteT b = true
  · rw [if_pos hf]
    by_cases hf' : isFiniteT b' = true
    · rw [if_pos hf']
      exact dropLastT_lt_dropLastT b b' hb hb' hf hf' hne h
    · rw [if_neg hf']
      exact lt_trans (dropLastT_lt b hne) h
  · rw [if_neg hf]
    by_cases hf' : isFiniteT b' = true
    · exact absurd (finite_of_lt b b' hb hb' hf' h) hf
    · rw [if_neg hf']; exact h

/-! ### Multiply units -/

/-- **The multiply units keep the order.**  Whatever follows the smaller one
only has to start below the digit `(x₀+1, y, 1)`. -/
theorem mulUnits_lt (x0 y : Nat) : ∀ s t : Term, AllNil s → AllNil t → s < t →
    ∀ R R' : List (List Nat), (∀ d ∈ R.head?, d < [x0 + 1, y, 1]) →
      mulUnits x0 y s ++ R < mulUnits x0 y t ++ R'
  | nil, nil, _, _, h, _, _, _ => absurd h (lt_irrefl nil)
  | nil, cons _ g u, _, _, _, R, R', hR => by
    rw [mulUnits, mulUnits, List.nil_append, List.cons_append, List.cons_append]
    exact lt_cons_of_head _ hR
  | cons _ _ _, nil, _, _, h, _, _, _ => absurd h (not_lt_nil _)
  | cons a g u, cons a' g' u', hs, ht, h, R, R', hR => by
    obtain ⟨rfl, hg, hu⟩ := hs
    obtain ⟨rfl, hg', hu'⟩ := ht
    rw [mulUnits, mulUnits, List.append_assoc, List.append_assoc]
    rcases cons_lt_cases h with h | ⟨rfl, h2⟩
    · -- the exponents differ: the embeddings decide
      rw [List.cons_append, List.cons_append]
      refine List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, ?_⟩)
      have hdig : ∀ e, ([x0 + 1, y, 1] : List Nat) < [x0 + 2 + e, 0, 0] :=
        fun e => col_lt (Or.inl (by omega))
      refine map_append_lt (fun e => [x0 + 2 + e, 0, 0])
        (fun a b hab => col_lt (Or.inl (by omega))) _ _ _ _ (unread_lt hg hg' h) ?_
      intro d hd e
      cases u with
      | nil =>
        rw [mulUnits, List.nil_append] at hd
        exact lt_trans (hR d hd) (hdig e)
      | cons _ _ _ =>
        rw [mulUnits, List.append_assoc, List.cons_append] at hd
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hd
        rw [← hd]; exact hdig e
    · -- the same exponent: the tails decide
      exact append_lt_append_left _ (mulUnits_lt x0 y u u' hu hu' h2 R R' hR)

/-! ### Add units -/

/-- The argument of the leading summand is `0`, if there is one. -/
def HeadArgNil : Term → Prop
  | nil => True
  | cons _ b _ => b = nil

/-- The top-level descending condition: every summand's argument is at most
the one before. -/
def DescTop : Term → Prop
  | nil => True
  | cons _ b t => headLe b t ∧ DescTop t

theorem descTop_of_OT : ∀ X : Term, OT X → AllNil X → DescTop X
  | nil, _, _ => trivial
  | cons a b t, hOT, hA => by
    obtain ⟨rfl, hAb, hAt⟩ := hA
    exact ⟨headLe_tail hOT ⟨rfl, hAb, hAt⟩, descTop_of_OT t (OT_tail hOT) hAt⟩

theorem headArgNil_of_headLe {t : Term} (h : headLe nil t) : HeadArgNil t := by
  cases t with
  | nil => trivial
  | cons _ b _ => exact eq_nil_of_le_nil h

/-- The add units of a nonzero term are a nonempty list. -/
theorem addUnits_cons (rp1 lastX : Nat) (pz : Bool) (i : Nat) (a b t : Term) :
    ∃ c r, addUnits rp1 lastX pz i (cons a b t) = c :: r := by
  rw [addUnits]
  split
  · split
    · exact ⟨_, _, rfl⟩
    · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, by rw [List.cons_append]⟩

/-- After a unit, the next unit starts with its anchor `(r+1, i-1, 0)`. -/
theorem addUnits_head_false (rp1 lastX i : Nat) (t : Term) :
    ∀ d ∈ (addUnits rp1 lastX false i t).head?, d = [rp1, i - 1, 0] := by
  intro d hd
  cases t with
  | nil => rw [addUnits] at hd; exact absurd hd (by simp)
  | cons a b u =>
    rw [addUnits] at hd
    split at hd
    · simp only [Bool.false_eq_true, if_false, List.head?_cons, Option.mem_def,
        Option.some.injEq] at hd
      exact hd.symm
    · simp only [List.cons_append, List.head?_cons, Option.mem_def, Option.some.injEq] at hd
      exact hd.symm

/-- **The add units keep the order.**  The state `(rp1, lastX, pz, i)` is
arbitrary; when the previous unit was a `β = 0` unit (`pz`), the larger term
must continue with `1`s, which the descending condition gives. -/
theorem addUnits_lt : ∀ α β : Term, AllNil α → AllNil β → DescTop β → α < β →
    ∀ (rp1 lastX : Nat) (pz : Bool) (i : Nat), (pz = true → HeadArgNil β) →
      addUnits rp1 lastX pz i α < addUnits rp1 lastX pz i β
  | nil, nil, _, _, _, h, _, _, _, _, _ => absurd h (lt_irrefl nil)
  | nil, cons a b t, _, _, _, _, rp1, lastX, pz, i, _ => by
    obtain ⟨c, r, hcr⟩ := addUnits_cons rp1 lastX pz i a b t
    rw [hcr, addUnits]
    exact List.nil_lt_cons _ _
  | cons _ _ _, nil, _, _, _, h, _, _, _, _, _ => absurd h (not_lt_nil _)
  | cons a b t, cons a' b' t', hα, hβ, hd, h, rp1, lastX, pz, i, hpz => by
    obtain ⟨rfl, hb, ht⟩ := hα
    obtain ⟨rfl, hb', ht'⟩ := hβ
    rcases cons_lt_cases h with h | ⟨rfl, h2⟩
    · -- the first difference is here, `b < b'`
      have hb'ne : b' ≠ nil := ne_nil_of_lt h
      have hpz' : pz = false := by
        cases pz with
        | false => rfl
        | true => exact absurd (hpz rfl) hb'ne
      subst hpz'
      rw [addUnits, addUnits, if_neg (fun h => hb'ne (beq_iff_eq.mp h))]
      by_cases hbn : b = nil
      · -- `β = 0` against a positive one: `(r+1, i, 0) < (r+1, i, 1)`
        subst hbn
        rw [if_pos (beq_self_eq_true nil), if_neg Bool.false_ne_true, List.cons_append, bodyU,
          List.cons_append]
        refine List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, List.cons_lt_cons_iff.mpr (Or.inl ?_)⟩)
        exact col_lt (Or.inr ⟨rfl, Or.inr ⟨rfl, by omega⟩⟩)
      · -- both positive: same anchor and root, then the multiply units
        rw [if_neg (fun h => hbn (beq_iff_eq.mp h)), List.cons_append, List.cons_append, bodyU,
          bodyU, List.cons_append, List.cons_append]
        refine List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, List.cons_lt_cons_iff.mpr
          (Or.inr ⟨rfl, ?_⟩)⟩)
        refine mulUnits_lt (rp1 + 1) i _ _ (allNil_peelOne b hb) (allNil_peelOne b' hb')
          (peelOne_lt hb hb' hbn h) _ _ ?_
        intro d hd
        rw [addUnits_head_false _ _ _ t d hd]
        exact col_lt (Or.inr ⟨by omega, Or.inr ⟨by omega, by omega⟩⟩)
    · -- the same summand: the tails decide
      obtain ⟨hle, hdt⟩ := hd
      rw [addUnits, addUnits]
      by_cases hbn : b = nil
      · subst hbn
        have hnext : HeadArgNil t' := headArgNil_of_headLe hle
        rw [if_pos (beq_self_eq_true nil), if_pos (beq_self_eq_true nil)]
        cases pz with
        | true =>
          rw [if_pos rfl, if_pos rfl]
          exact List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl,
            addUnits_lt t t' ht ht' hdt h2 _ _ _ _ (fun _ => hnext)⟩)
        | false =>
          rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
          exact List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, List.cons_lt_cons_iff.mpr
            (Or.inr ⟨rfl, addUnits_lt t t' ht ht' hdt h2 _ _ _ _ (fun _ => hnext)⟩)⟩)
      · rw [if_neg (fun h => hbn (beq_iff_eq.mp h)), if_neg (fun h => hbn (beq_iff_eq.mp h))]
        exact append_lt_append_left _
          (addUnits_lt t t' ht ht' hdt h2 _ _ _ _ (fun h => absurd h Bool.false_ne_true))

end TrioMono

open TrioMono

/-! ### The theorems -/

/-- **The trio map is monotone** on the terms with every subscript `0`, the
larger one descending at the top level. -/
theorem omegaIndexMatrix_lt {α β : Term} (hα : AllNil α) (hβ : AllNil β) (hd : DescTop β)
    (h : α < β) : omegaIndexMatrix α < omegaIndexMatrix β :=
  addUnits_lt α β hα hβ hd h 0 0 false 1 (fun h => absurd h Bool.false_ne_true)

/-- **The trio map is monotone below `ε₀`**: for standard forms `α < β < ε₀`
(the states of `exbE0`), `M(α) < M(β)` in the dictionary order on the
matrices. -/
theorem omegaIndexMatrix_strictMono (α β : exbE0.State) (h : α.1 < β.1) :
    omegaIndexMatrix α.1 < omegaIndexMatrix β.1 :=
  omegaIndexMatrix_lt (allNil_of_state α) (allNil_of_state β)
    (descTop_of_OT β.1 β.2.1 (allNil_of_state β)) h

/-- **And it reflects the order**: below `ε₀` one matrix is below another
exactly when its ordinal index is. -/
theorem omegaIndexMatrix_lt_iff (α β : exbE0.State) :
    omegaIndexMatrix α.1 < omegaIndexMatrix β.1 ↔ α.1 < β.1 := by
  refine ⟨fun h => ?_, omegaIndexMatrix_strictMono α β⟩
  rcases lt_trichotomy α.1 β.1 with h' | h' | h'
  · exact h'
  · rw [h'] at h; exact absurd h (_root_.lt_irrefl _)
  · exact absurd (omegaIndexMatrix_strictMono β α h') (_root_.lt_asymm h)

/-- **So it is injective** below `ε₀`. -/
theorem omegaIndexMatrix_injective {α β : exbE0.State}
    (h : omegaIndexMatrix α.1 = omegaIndexMatrix β.1) : α = β := by
  rcases lt_trichotomy α.1 β.1 with h' | h' | h'
  · have := omegaIndexMatrix_strictMono α β h'
    rw [h] at this; exact absurd this (_root_.lt_irrefl _)
  · exact Subtype.ext h'
  · have := omegaIndexMatrix_strictMono β α h'
    rw [h] at this; exact absurd this (_root_.lt_irrefl _)

/-- Below `ε₀` the general map `trioMatrix` is `omegaIndexMatrix`: its only
other clause needs a subscript that is not `0`. -/
theorem trioMatrix_eq_of_allNil : ∀ α : Term, AllNil α → trioMatrix α = omegaIndexMatrix α := by
  intro α
  induction α using trioMatrix.induct with
  | case1 X hX =>
    intro _
    rw [trioMatrix, if_pos hX, beq_iff_eq.mp hX]
  | case2 X hX _ =>
    intro h
    exact absurd (beq_iff_eq.mpr h.2.1.1) hX
  | case3 α h1 =>
    intro _
    rw [trioMatrix]
    exact h1

/-- **The same for `trioMatrix`**: for standard forms `α < β < ε₀`,
`trioMatrix α < trioMatrix β`. -/
theorem trioMatrix_strictMono (α β : exbE0.State) (h : α.1 < β.1) :
    trioMatrix α.1 < trioMatrix β.1 := by
  rw [trioMatrix_eq_of_allNil α.1 (allNil_of_state α),
    trioMatrix_eq_of_allNil β.1 (allNil_of_state β)]
  exact omegaIndexMatrix_strictMono α β h

end Googology.Trans.BMS
