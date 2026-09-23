import Googology.Trans.BMS.TrioMono
import Googology.Trans.BMS.TrioRules
import Googology.Notation.ExBuchholz.Cofinal

/-!
# The trio map below `ψ_0(Ω_2)`, without fuel, and its order

`TrioRules.lean` transcribes the rules of
[koteitan/trio](https://github.com/koteitan/trio) for `ε₀ ≤ α < Λ` as
`trioMatrixL`, a program with a fuel of `200` on every recursion.  This file
isolates what that program does on the standard forms whose subscripts are all
`0` or `1` (all of them lie below `ψ_0(Ω_2)`), writes it as a structural
recursion `trioE`, and proves that `trioE` keeps the order.

## What `trioMatrixL` does there

On such a term every `Ω` is written with `ψ_1`, and the builder never lays a
storey, never copies a base and never appends an upgrade mark (its regime is
empty and every level it meets is `1`).  What is left is the grammar of
`Trio.lean` with the primitive-sequence embedding replaced by the **tree** of
the term, `treeB`: a summand `ψ_ν(b)` is the column `(x, ν, 0)` followed by
the tree of `b` one step to the right.  A summand `ψ_0(b)` of `α` with `b`
free of `Ω` is the add unit of `Trio.lean`; a summand `ψ_0(b)` whose argument
contains `Ω` is read by the program as an `ε`-number atom `E`, so its add unit
is the root, one digit, and the tree of `E` itself (`peelE`).

That `trioE` is what the program computes is proved in `TrioTreeRules.lean`
for every such term of nesting depth at most `200`
(`TrioTreeRules.trioMatrixL_eq_trioE`); the depth bound is needed, see below.
The `#guard` at the end of this file compares the two on every standard term
of this kind with at most six `ψ`s outside the subscripts (a wider survey, all
40 883 such terms with at most nine, agreed as well; it was run outside this
file).

## Two facts about `trioMatrixL` that the checks show

* **The fuel is not enough.**  `ψ_0(Ω + T)` for the tower `T` of `205` and of
  `206` copies of `ψ_0` are two different standard terms between `ε₀` and
  `ε₁`, and `trioMatrixL` gives them the same matrix (`#guard` below).  So
  `trioMatrixL` is neither injective nor order-preserving on `ε₀ ≤ α < ε₁`,
  and no theorem of that form holds for it as it stands.  The same happens
  below `ε₀` (the tower of `210` against `211`).  On this fragment the program
  agrees with `trioE` exactly up to depth `200` (`TrioTreeRules.lean`).
* **Terms and the sheet disagree.**  `TrioRules.ofTerm` reads every `ψ_0(b)`
  with `Ω` in `b` as a fixed point of `x ↦ ω^x`.  That is right for
  `ψ_0(Ω) = ε₀` but not for `ψ_0(Ω + 1) = ε₀·ω`, which the program then lays
  out as it lays out the label `ε₀^{ε₀^ω}` rather than as the sheet's row for `ε₀·ω`
  (`#guard` below).  The map on terms is still order-preserving (the theorem
  of this file), but it is not the sheet's map above `ε₀`, and its image skips
  standard forms: the sheet's matrix of `ε₀·ω`,
  `(0,0,0)(1,1,1)(2,1,1)(3,0,0)(4,1,0)(2,1,1)`, a standard form (`bms -s` of
  [yaBMS](https://github.com/koteitan/yaBMS)), is `trioE α` for no `α` of the
  fragment: a digit with the tree of `ψ_0(Ω)` is followed by no other digit.

## The theorem

`trioE_lt_of_OT`: for standard forms `α < β`, countable (`< Ω`), with every
subscript `0` or `1`,

  `trioE α < trioE β`

in the dictionary order on the column lists, the order of `TrioMono.lean`;
so `trioE` also reflects the order and is injective (`trioE_lt_iff`,
`trioE_injective`).  Below `ε₀` it is `omegaIndexMatrix` (`trioE_allNil`).

The proof is `TrioMono.lean`'s, one level deeper.  The trees keep the order
(`treeB_lt`): two sums first differ at a summand, and `(x,0,0) < (x,1,0)`
where the subscripts differ.  An argument with `Ω` in it starts with `Ω`
(`argOK_of_OT`: otherwise `ψ_0(b)` would have to bound an argument
`G` collects that starts with `Ω`), so it sits above every argument without
`Ω`, and the one digit with the tree of `E` sits above every run of digits
the other kind of unit has (`peelE_lt`).
-/

namespace Googology.Trans.BMS.TrioTree

open Googology.Notation.ExBuchholz
open Googology.Notation.ExBuchholz.Term
open Googology.Trans.BMS.TrioMono

/-! ### The map -/

/-- The row-1 value of a subscript: `0` for `0`, `1` otherwise. -/
def subY : Term → Nat
  | nil => 0
  | cons _ _ _ => 1

/-- **The tree of a term** at `x`: a summand `ψ_ν(b)` is the column
`(x, ν, 0)`, then the tree of `b` at `x + 1`; the summands one after another. -/
def treeB (x : Nat) : Term → List (List Nat)
  | nil => []
  | cons a b t => ([x, subY a, 0] :: treeB (x + 1) b) ++ treeB x t

/-- The multiply units: a digit and the tree of the argument, per summand. -/
def mulUnitsE (x0 y : Nat) : Term → List (List Nat)
  | nil => []
  | cons _ g t => ([x0 + 1, y, 1] :: treeB (x0 + 2) g) ++ mulUnitsE x0 y t

/-- Every subscript is `0`, as a test. -/
def allNilB : Term → Bool
  | nil => true
  | cons a b t => (a == nil) && allNilB b && allNilB t

/-- `β'` with `1 + β' = β` for an argument free of `Ω`; for an argument with
`Ω` in it, the one summand `ψ_0(E)` with `E = ψ_0(b)` itself, which is how
the program reads it. -/
def peelE (b : Term) : Term := if allNilB b then peelOne b else psi nil (psi nil b)

/-- The body of an add unit: the root and the multiply units. -/
def bodyE (b : Term) (x0 y : Nat) : List (List Nat) := [x0, y, 1] :: mulUnitsE x0 y (peelE b)

/-- The add units, as `addUnits` of `Trio.lean` with `bodyE` for `bodyU`. -/
def addUnitsE (rp1 lastX : Nat) (prevZero : Bool) (i : Nat) : Term → List (List Nat)
  | nil => []
  | cons _ b t =>
      if b == nil then
        if prevZero then
          [lastX + 1, i, 0] :: addUnitsE rp1 (lastX + 1) true (i + 1) t
        else
          [rp1, i - 1, 0] :: [rp1 + 1, i, 0] :: addUnitsE rp1 (rp1 + 1) true (i + 1) t
      else
        ([rp1, i - 1, 0] :: bodyE b (rp1 + 1) i) ++ addUnitsE (rp1 + 2) (rp1 + 1) false (i + 1) t

/-- **The trio matrix of `ψ_0(Ω_α)`** for a countable `α` whose subscripts are
`0` or `1`: what `TrioRules.trioMatrixL` computes there, without fuel. -/
def trioE (α : Term) : List (List Nat) := addUnitsE 0 0 false 1 α

/-! ### Below `ε₀` it is `omegaIndexMatrix` -/

theorem allNilB_iff : ∀ b : Term, allNilB b = true ↔ AllNil b := by
  intro b
  induction b with
  | nil => simp [allNilB, AllNil]
  | cons a c t _ ihc iht =>
    simp only [allNilB, Bool.and_eq_true, beq_iff_eq, ihc, iht, AllNil, and_assoc]

theorem treeB_allNil : ∀ g : Term, AllNil g → ∀ x k : Nat,
    treeB (x + k) g = (unread k g).map (fun e => [x + e, 0, 0]) := by
  intro g
  induction g with
  | nil => intro _ _ _; rfl
  | cons a b t _ ihb iht =>
    intro h x k
    obtain ⟨rfl, hb, ht⟩ := h
    rw [treeB, unread_cons, List.map_cons, List.map_append, show x + k + 1 = x + (k + 1) by omega,
      ihb hb x (k + 1), iht ht x k]
    rfl

theorem treeB_eq_prSS (x : Nat) (g : Term) (h : AllNil g) : treeB x g = prSS x g := by
  rw [prSS, ← treeB_allNil g h x 0, Nat.add_zero]

theorem mulUnitsE_allNil (x0 y : Nat) : ∀ t : Term, AllNil t → mulUnitsE x0 y t = mulUnits x0 y t := by
  intro t
  induction t with
  | nil => intro _; rfl
  | cons a g u _ _ ihu =>
    intro h
    rw [mulUnitsE, mulUnits, treeB_eq_prSS _ g h.2.1, ihu h.2.2]

theorem bodyE_allNil (b : Term) (x0 y : Nat) (h : AllNil b) : bodyE b x0 y = bodyU b x0 y := by
  rw [bodyE, bodyU, peelE, if_pos ((allNilB_iff b).mpr h),
    mulUnitsE_allNil _ _ _ (allNil_peelOne b h)]

theorem addUnitsE_allNil : ∀ α : Term, AllNil α → ∀ (rp1 lastX : Nat) (pz : Bool) (i : Nat),
    addUnitsE rp1 lastX pz i α = addUnits rp1 lastX pz i α := by
  intro α
  induction α with
  | nil => intro _ _ _ _ _; rfl
  | cons a b t _ _ iht =>
    intro h rp1 lastX pz i
    rw [addUnitsE, addUnits]
    split
    · split
      · rw [iht h.2.2]
      · rw [iht h.2.2]
    · rw [bodyE_allNil b _ _ h.2.1, iht h.2.2]

/-- **Below `ε₀`, `trioE` is `omegaIndexMatrix` of `Trio.lean`.** -/
theorem trioE_allNil (α : Term) (h : AllNil α) : trioE α = omegaIndexMatrix α :=
  addUnitsE_allNil α h 0 0 false 1

/-! ### The fragment -/

/-- Every subscript is `0` or `1`. -/
def Sub01 : Term → Prop
  | nil => True
  | cons a b t => (a = nil ∨ a = t1) ∧ Sub01 b ∧ Sub01 t

/-- An argument of `ψ_0` in the fragment: free of `Ω`, or starting with `Ω`. -/
def ArgOK (b : Term) : Prop := AllNil b ∨ ∃ e u, b = cons t1 e u

/-- A countable term of the fragment: summands `ψ_0(b)`, each `b` in `Sub01`
and `ArgOK`. -/
def Frag : Term → Prop
  | nil => True
  | cons a b t => a = nil ∧ Sub01 b ∧ ArgOK b ∧ Frag t

theorem sub01_of_allNil : ∀ b : Term, AllNil b → Sub01 b := by
  intro b
  induction b with
  | nil => intro _; trivial
  | cons a c t _ ihc iht =>
    intro h
    exact ⟨Or.inl h.1, ihc h.2.1, iht h.2.2⟩

theorem sub01_psi_psi {b : Term} (h : Sub01 b) : Sub01 (psi nil (psi nil b)) :=
  ⟨Or.inl rfl, ⟨Or.inl rfl, h, trivial⟩, trivial⟩

/-- The subscripts of a sum of `ψ_0`s. -/
def TopNil : Term → Prop
  | nil => True
  | cons a _ t => a = nil ∧ TopNil t

theorem topNil_of_allNil : ∀ b : Term, AllNil b → TopNil b := by
  intro b
  induction b with
  | nil => intro _; trivial
  | cons a c t _ _ iht => intro h; exact ⟨h.1, iht h.2.2⟩

/-- An argument free of `Ω` is below an argument starting with `Ω`. -/
theorem allNil_lt_t1head {g e u : Term} (hg : AllNil g) : g < cons t1 e u := by
  cases g with
  | nil => exact nil_lt_cons _ _ _
  | cons a c t =>
    obtain ⟨rfl, _, _⟩ := hg
    exact cons_lt_cons_iff.mpr (Or.inl (psi_lt_psi_iff.mpr (Or.inl (nil_lt_cons _ _ _))))

theorem sub_eq_of_Sub01_lt {a c : Term} (ha : a = nil ∨ a = t1) (hc : c = nil ∨ c = t1)
    (h : a < c) : a = nil ∧ c = t1 := by
  rcases ha with rfl | rfl <;> rcases hc with rfl | rfl
  · exact absurd h (Term.lt_irrefl _)
  · exact ⟨rfl, rfl⟩
  · exact absurd h (not_lt_nil _)
  · exact absurd h (Term.lt_irrefl _)

/-! ### Trees keep the order -/

theorem treeB_head_lt (x : Nat) (t : Term) (R : List (List Nat))
    (hR : ∀ d ∈ R.head?, d < [x, 0, 0]) : ∀ d ∈ (treeB x t ++ R).head?, d < [x + 1, 0, 0] := by
  intro d hd
  cases t with
  | nil =>
    rw [treeB, List.nil_append] at hd
    exact _root_.lt_trans (hR d hd) (col_lt (Or.inl (by omega)))
  | cons a b u =>
    rw [treeB, List.append_assoc, List.cons_append] at hd
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hd
    rw [← hd]
    exact col_lt (Or.inl (by omega))

/-- **The tree keeps the order**, whatever follows the smaller one, as long as
that starts below `(x, 0, 0)`. -/
theorem treeB_lt : ∀ s t : Term, Sub01 s → Sub01 t → s < t →
    ∀ (x : Nat) (R R' : List (List Nat)), (∀ d ∈ R.head?, d < [x, 0, 0]) →
      treeB x s ++ R < treeB x t ++ R' := by
  intro s
  induction s with
  | nil =>
    intro t _ _ h x R R' hR
    cases t with
    | nil => exact absurd h (Term.lt_irrefl _)
    | cons c d v =>
      show R < treeB x (cons c d v) ++ R'
      rw [treeB, List.append_assoc, List.cons_append]
      refine lt_cons_of_head _ (fun e he => _root_.lt_of_lt_of_le (hR e he) ?_)
      cases c with
      | nil => exact _root_.le_refl _
      | cons _ _ _ => exact le_of_lt (col_lt (Or.inr ⟨rfl, Or.inl (by simp [subY])⟩))
  | cons a b u _ ihb ihu =>
    intro t hs ht h x R R' hR
    cases t with
    | nil => exact absurd h (not_lt_nil _)
    | cons c d v =>
      obtain ⟨ha, hb, hu⟩ := hs
      obtain ⟨hc, hd, hv⟩ := ht
      rw [treeB, treeB, List.append_assoc, List.append_assoc, List.cons_append, List.cons_append]
      rcases cons_lt_cons_iff.mp h with h1 | ⟨h1, h2⟩
      · rcases psi_lt_psi_iff.mp h1 with h3 | ⟨rfl, h3⟩
        · obtain ⟨rfl, rfl⟩ := sub_eq_of_Sub01_lt ha hc h3
          exact List.cons_lt_cons_iff.mpr (Or.inl (col_lt (Or.inr ⟨rfl, Or.inl (by simp [subY])⟩)))
        · refine List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, ?_⟩)
          exact ihb d hb hd h3 (x + 1) _ _ (treeB_head_lt x u R hR)
      · injection h1 with e1 e2
        subst e1 e2
        refine append_lt_append_left (([x, subY a, 0] :: treeB (x + 1) b)) ?_
        exact ihu v hu hv h2 x R R' hR

/-! ### Multiply units keep the order -/

theorem mulUnitsE_lt (x0 y : Nat) : ∀ s t : Term, TopNil s → TopNil t → Sub01 s → Sub01 t →
    s < t → ∀ R R' : List (List Nat), (∀ d ∈ R.head?, d < [x0 + 1, y, 1]) →
      mulUnitsE x0 y s ++ R < mulUnitsE x0 y t ++ R' := by
  intro s
  induction s with
  | nil =>
    intro t _ _ _ _ h R R' hR
    cases t with
    | nil => exact absurd h (Term.lt_irrefl _)
    | cons _ g u =>
      rw [mulUnitsE, mulUnitsE, List.nil_append, List.cons_append, List.cons_append]
      exact lt_cons_of_head _ hR
  | cons a g u _ _ ihu =>
    intro t hs ht ss st h R R' hR
    cases t with
    | nil => exact absurd h (not_lt_nil _)
    | cons a' g' u' =>
      obtain ⟨rfl, hu⟩ := hs
      obtain ⟨rfl, hu'⟩ := ht
      rw [mulUnitsE, mulUnitsE, List.append_assoc, List.append_assoc]
      rcases cons_lt_cases h with h | ⟨rfl, h2⟩
      · rw [List.cons_append, List.cons_append]
        refine List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, ?_⟩)
        refine treeB_lt g g' ss.2.1 st.2.1 h (x0 + 2) _ _ (fun d hd => ?_)
        cases u with
        | nil =>
          rw [mulUnitsE, List.nil_append] at hd
          exact _root_.lt_trans (hR d hd) (col_lt (Or.inl (by omega)))
        | cons _ _ _ =>
          rw [mulUnitsE, List.append_assoc, List.cons_append] at hd
          simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hd
          rw [← hd]; exact col_lt (Or.inl (by omega))
      · exact append_lt_append_left _ (ihu u' hu hu' ss.2.2 st.2.2 h2 R R' hR)

/-! ### `peelE` keeps the order -/

theorem topNil_peelE (b : Term) : TopNil (peelE b) := by
  unfold peelE
  split
  · rename_i h
    exact topNil_of_allNil _ (allNil_peelOne b ((allNilB_iff b).mp h))
  · exact ⟨rfl, trivial⟩

theorem sub01_peelE (b : Term) (hs : Sub01 b) : Sub01 (peelE b) := by
  unfold peelE
  split
  · rename_i h
    exact sub01_of_allNil _ (allNil_peelOne b ((allNilB_iff b).mp h))
  · exact sub01_psi_psi hs

theorem peelE_of_allNil {b : Term} (h : AllNil b) : peelE b = peelOne b := by
  rw [peelE, if_pos ((allNilB_iff b).mpr h)]

theorem peelE_of_not {b : Term} (h : ¬ AllNil b) : peelE b = psi nil (psi nil b) := by
  rw [peelE, if_neg (fun h' => h ((allNilB_iff b).mp h'))]

theorem not_allNil_t1 {e u : Term} : ¬ AllNil (cons t1 e u) := by
  intro h; exact Term.noConfusion h.1

/-- **`peelE` keeps the order** on the arguments of the fragment. -/
theorem peelE_lt {b b' : Term} (hb : ArgOK b) (hb' : ArgOK b') (hne : b ≠ nil) (h : b < b') :
    peelE b < peelE b' := by
  rcases hb with hb | ⟨e, u, rfl⟩ <;> rcases hb' with hb' | ⟨e', u', rfl⟩
  · rw [peelE_of_allNil hb, peelE_of_allNil hb']
    exact peelOne_lt hb hb' hne h
  · rw [peelE_of_allNil hb, peelE_of_not not_allNil_t1]
    have hp := allNil_peelOne b hb
    cases hq : peelOne b with
    | nil => exact nil_lt_cons _ _ _
    | cons a g v =>
      rw [hq] at hp
      obtain ⟨rfl, hg, _⟩ := hp
      refine cons_lt_cons_iff.mpr (Or.inl (psi_lt_psi_iff.mpr (Or.inr ⟨rfl, ?_⟩)))
      cases g with
      | nil => exact nil_lt_cons _ _ _
      | cons a2 h2 w =>
        obtain ⟨rfl, hh, _⟩ := hg
        exact cons_lt_cons_iff.mpr (Or.inl (psi_lt_psi_iff.mpr (Or.inr ⟨rfl,
          allNil_lt_t1head hh⟩)))
  · exact absurd (allNil_lt_t1head hb') (Term.lt_asymm h)
  · rw [peelE_of_not not_allNil_t1, peelE_of_not not_allNil_t1]
    exact cons_lt_cons_iff.mpr (Or.inl (psi_lt_psi_iff.mpr (Or.inr ⟨rfl,
      cons_lt_cons_iff.mpr (Or.inl (psi_lt_psi_iff.mpr (Or.inr ⟨rfl, h⟩)))⟩)))

/-! ### Add units keep the order -/

/-- The add units of a nonzero term are a nonempty list. -/
theorem addUnitsE_cons (rp1 lastX : Nat) (pz : Bool) (i : Nat) (a b t : Term) :
    ∃ c r, addUnitsE rp1 lastX pz i (cons a b t) = c :: r := by
  rw [addUnitsE]
  split
  · split
    · exact ⟨_, _, rfl⟩
    · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, by rw [List.cons_append]⟩

theorem addUnitsE_head_false (rp1 lastX i : Nat) (t : Term) :
    ∀ d ∈ (addUnitsE rp1 lastX false i t).head?, d = [rp1, i - 1, 0] := by
  intro d hd
  cases t with
  | nil => rw [addUnitsE] at hd; exact absurd hd (by simp)
  | cons a b u =>
    rw [addUnitsE] at hd
    split at hd
    · simp only [Bool.false_eq_true, if_false, List.head?_cons, Option.mem_def,
        Option.some.injEq] at hd
      exact hd.symm
    · simp only [List.cons_append, List.head?_cons, Option.mem_def, Option.some.injEq] at hd
      exact hd.symm

/-- **The add units keep the order**, as `addUnits_lt` of `TrioMono.lean`. -/
theorem addUnitsE_lt : ∀ α β : Term, Frag α → Frag β → DescTop β → α < β →
    ∀ (rp1 lastX : Nat) (pz : Bool) (i : Nat), (pz = true → HeadArgNil β) →
      addUnitsE rp1 lastX pz i α < addUnitsE rp1 lastX pz i β
  | nil, nil, _, _, _, h, _, _, _, _, _ => absurd h (Term.lt_irrefl _)
  | nil, cons a b t, _, _, _, _, rp1, lastX, pz, i, _ => by
    obtain ⟨c, r, hcr⟩ := addUnitsE_cons rp1 lastX pz i a b t
    rw [hcr, addUnitsE]
    exact List.nil_lt_cons _ _
  | cons _ _ _, nil, _, _, _, h, _, _, _, _, _ => absurd h (not_lt_nil _)
  | cons a b t, cons a' b' t', hα, hβ, hd, h, rp1, lastX, pz, i, hpz => by
    obtain ⟨rfl, _, hbA, ht⟩ := hα
    obtain ⟨rfl, _, hbA', ht'⟩ := hβ
    rcases cons_lt_cases h with h | ⟨rfl, h2⟩
    · have hb'ne : b' ≠ nil := ne_nil_of_lt h
      have hpz' : pz = false := by
        cases pz with
        | false => rfl
        | true => exact absurd (hpz rfl) hb'ne
      subst hpz'
      rw [addUnitsE, addUnitsE, if_neg (fun h => hb'ne (beq_iff_eq.mp h))]
      by_cases hbn : b = nil
      · subst hbn
        rw [if_pos (beq_self_eq_true nil), if_neg Bool.false_ne_true, List.cons_append, bodyE,
          List.cons_append]
        refine List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, List.cons_lt_cons_iff.mpr (Or.inl ?_)⟩)
        exact col_lt (Or.inr ⟨rfl, Or.inr ⟨rfl, by omega⟩⟩)
      · rw [if_neg (fun h => hbn (beq_iff_eq.mp h)), List.cons_append, List.cons_append, bodyE,
          bodyE, List.cons_append, List.cons_append]
        refine List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, List.cons_lt_cons_iff.mpr
          (Or.inr ⟨rfl, ?_⟩)⟩)
        refine mulUnitsE_lt (rp1 + 1) i _ _ (topNil_peelE b) (topNil_peelE b')
          (sub01_peelE b ‹_›) (sub01_peelE b' ‹_›) (peelE_lt hbA hbA' hbn h) _ _ ?_
        intro d hd
        rw [addUnitsE_head_false _ _ _ t d hd]
        exact col_lt (Or.inr ⟨by omega, Or.inr ⟨by omega, by omega⟩⟩)
    · obtain ⟨hle, hdt⟩ := hd
      rw [addUnitsE, addUnitsE]
      by_cases hbn : b = nil
      · subst hbn
        have hnext : HeadArgNil t' := headArgNil_of_headLe hle
        rw [if_pos (beq_self_eq_true nil), if_pos (beq_self_eq_true nil)]
        cases pz with
        | true =>
          rw [if_pos rfl, if_pos rfl]
          exact List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl,
            addUnitsE_lt t t' ht ht' hdt h2 _ _ _ _ (fun _ => hnext)⟩)
        | false =>
          rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
          exact List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, List.cons_lt_cons_iff.mpr
            (Or.inr ⟨rfl, addUnitsE_lt t t' ht ht' hdt h2 _ _ _ _ (fun _ => hnext)⟩)⟩)
      · rw [if_neg (fun h => hbn (beq_iff_eq.mp h)), if_neg (fun h => hbn (beq_iff_eq.mp h))]
        exact append_lt_append_left _
          (addUnitsE_lt t t' ht ht' hdt h2 _ _ _ _ (fun h => absurd h Bool.false_ne_true))

/-- **`trioE` keeps the order** on the fragment, the larger term descending at
the top level. -/
theorem trioE_lt {α β : Term} (hα : Frag α) (hβ : Frag β) (hd : DescTop β) (h : α < β) :
    trioE α < trioE β :=
  addUnitsE_lt α β hα hβ hd h 0 0 false 1 (fun h => absurd h Bool.false_ne_true)

/-! ### Standard forms are in the fragment -/

theorem eq_nil_of_le_nil' {c : Term} (h : c ≤ nil) : c = nil := by
  rcases le_iff_lt_or_eq.mp h with h | h
  · exact absurd h (not_lt_nil c)
  · exact h

/-- After a leading `ψ_0`, a standard sum has only `ψ_0`s. -/
theorem topNil_of_OT : ∀ t : Term, OT t → ∀ d u, t = cons nil d u → TopNil t := by
  intro t
  induction t with
  | nil => intro _ _ _ h; exact Term.noConfusion h
  | cons a b u _ _ ihu =>
    intro hOT d v he
    injection he with ha _ _
    subst ha
    refine ⟨rfl, ?_⟩
    cases u with
    | nil => trivial
    | cons c e w =>
      have hle := OT_tail_head_le hOT
      have hc : c = nil := by
        rcases le_iff_lt_or_eq.mp hle with h | h
        · rcases psi_lt_psi_iff.mp h with h' | ⟨h', _⟩
          · exact absurd h' (not_lt_nil c)
          · exact h'
        · injection h
      subst hc
      exact ihu (OT_tail hOT) e w rfl

theorem topNil_of_lt_tW {α : Term} (hOT : OT α) (hc : α < tW) : TopNil α := by
  cases α with
  | nil => trivial
  | cons a b t =>
    have ha := sub_eq_nil_of_lt_tW hc
    subst ha
    exact topNil_of_OT _ hOT b t rfl

/-- A sum of `ψ_0`s with `Ω` somewhere collects, for `ψ_0`, an argument
starting with `Ω`. -/
theorem exists_G_t1 : ∀ s : Term, OT s → TopNil s → Sub01 s → ¬ AllNil s →
    ∃ x ∈ G nil s, ∃ e u, x = cons t1 e u := by
  intro s
  induction s with
  | nil => intro _ _ _ h; exact absurd trivial h
  | cons a d u _ ihd ihu =>
    intro hOT hT hS hA
    obtain ⟨rfl, hTu⟩ := hT
    by_cases hAu : AllNil u
    · have hAd : ¬ AllNil d := fun h => hA ⟨rfl, h, hAu⟩
      cases d with
      | nil => exact absurd trivial hAd
      | cons c e w =>
        rcases hS.2.1.1 with rfl | rfl
        · obtain ⟨x, hx, hxe⟩ := ihd (OT_snd hOT) (topNil_of_OT _ (OT_snd hOT) e w rfl)
            hS.2.1 hAd
          exact ⟨x, G_mem_cons_argG (le_refl nil) hx, hxe⟩
        · exact ⟨_, G_mem_cons_arg (le_refl nil), e, w, rfl⟩
    · obtain ⟨x, hx, hxe⟩ := ihu (OT_tail hOT) hTu hS.2.2 hAu
      exact ⟨x, G_mem_cons_tail hx, hxe⟩

/-- **An argument of `ψ_0` with `Ω` in it starts with `Ω`.** -/
theorem argOK_of_OT {b t : Term} (hOT : OT (cons nil b t)) (hS : Sub01 b) : ArgOK b := by
  by_cases hA : AllNil b
  · exact Or.inl hA
  · right
    cases b with
    | nil => exact absurd trivial hA
    | cons c e w =>
      rcases hS.1 with rfl | rfl
      · exfalso
        have hOTb : OT (cons nil e w) := OT_snd hOT
        obtain ⟨x, hx, ⟨e', u', rfl⟩⟩ :=
          exists_G_t1 _ hOTb (topNil_of_OT _ hOTb e w rfl) hS hA
        have hall : (G nil (cons nil e w)).all (fun x => decide (x < cons nil e w)) = true := by
          simp only [OT, isOT, Bool.and_eq_true] at hOT
          exact hOT.1.1.2
        have hlt := of_decide_eq_true (List.all_eq_true.mp hall _ hx)
        exact absurd (cons_lt_cons_iff.mpr (Or.inl (psi_lt_psi_iff.mpr
          (Or.inl (nil_lt_cons nil nil nil))))) (Term.lt_asymm hlt)
      · exact ⟨e, w, rfl⟩

theorem frag_of_OT : ∀ α : Term, OT α → TopNil α → Sub01 α → Frag α := by
  intro α
  induction α with
  | nil => intro _ _ _; trivial
  | cons a b t _ _ iht =>
    intro hOT hT hS
    obtain ⟨rfl, hTt⟩ := hT
    exact ⟨rfl, hS.2.1, argOK_of_OT hOT hS.2.1, iht (OT_tail hOT) hTt hS.2.2⟩

theorem descTop_of_OT' : ∀ X : Term, OT X → TopNil X → DescTop X := by
  intro X
  induction X with
  | nil => intro _ _; trivial
  | cons a b t _ _ iht =>
    intro hOT hT
    obtain ⟨rfl, hTt⟩ := hT
    refine ⟨?_, iht (OT_tail hOT) hTt⟩
    cases t with
    | nil => trivial
    | cons c d u =>
      obtain ⟨rfl, _⟩ := hTt
      exact psi_le_psi_nil (OT_tail_head_le hOT)

/-! ### The theorems -/

/-- **`trioE` keeps the order on the standard forms of the fragment**: for
standard `α < β`, both countable and with every subscript `0` or `1`,
`trioE α < trioE β`. -/
theorem trioE_lt_of_OT {α β : Term} (hα : OT α) (hβ : OT β) (hαc : α < tW) (hβc : β < tW)
    (sα : Sub01 α) (sβ : Sub01 β) (h : α < β) : trioE α < trioE β :=
  trioE_lt (frag_of_OT α hα (topNil_of_lt_tW hα hαc) sα)
    (frag_of_OT β hβ (topNil_of_lt_tW hβ hβc) sβ)
    (descTop_of_OT' β hβ (topNil_of_lt_tW hβ hβc)) h

/-- **And reflects it.** -/
theorem trioE_lt_iff {α β : Term} (hα : OT α) (hβ : OT β) (hαc : α < tW) (hβc : β < tW)
    (sα : Sub01 α) (sβ : Sub01 β) : trioE α < trioE β ↔ α < β := by
  refine ⟨fun h => ?_, trioE_lt_of_OT hα hβ hαc hβc sα sβ⟩
  rcases Term.lt_trichotomy α β with h' | h' | h'
  · exact h'
  · rw [h'] at h; exact absurd h (_root_.lt_irrefl _)
  · exact absurd (trioE_lt_of_OT hβ hα hβc hαc sβ sα h') (_root_.lt_asymm h)

/-- **So it is injective** on the fragment. -/
theorem trioE_injective {α β : Term} (hα : OT α) (hβ : OT β) (hαc : α < tW) (hβc : β < tW)
    (sα : Sub01 α) (sβ : Sub01 β) (h : trioE α = trioE β) : α = β := by
  rcases Term.lt_trichotomy α β with h' | h' | h'
  · have := trioE_lt_of_OT hα hβ hαc hβc sα sβ h'
    rw [h] at this; exact absurd this (_root_.lt_irrefl _)
  · exact h'
  · have := trioE_lt_of_OT hβ hα hβc hαc sβ sα h'
    rw [h] at this; exact absurd this (_root_.lt_irrefl _)

/-- The fragment lies below `ψ_0(Ω_2)`. -/
theorem lt_bho_of_frag {α : Term} (hT : TopNil α) (hS : Sub01 α) :
    α < psi nil (psi (cons nil nil t1) nil) := by
  cases α with
  | nil => exact nil_lt_cons _ _ _
  | cons a b t =>
    obtain ⟨rfl, _⟩ := hT
    refine cons_lt_psi_iff.mpr (psi_lt_psi_iff.mpr (Or.inr ⟨rfl, ?_⟩))
    cases b with
    | nil => exact nil_lt_cons _ _ _
    | cons c d u =>
      refine cons_lt_psi_iff.mpr (psi_lt_psi_iff.mpr (Or.inl ?_))
      rcases hS.2.1.1 with rfl | rfl
      · exact nil_lt_cons _ _ _
      · exact cons_lt_cons_iff.mpr (Or.inr ⟨rfl, nil_lt_cons _ _ _⟩)

/-! ### Calibration against `TrioRules.trioMatrixL`

These are computations, not theorems (`trioMatrixL` does not reduce in the
kernel).  `smallFrag n` lists every standard term with at most `n` `ψ`s
outside the subscripts, every subscript `0` or `1`, and countable. -/

/-- The terms with `n` `ψ`s outside the subscripts, subscripts `0` or `1`,
tabulated by `n`. -/
def genTab : Nat → Array (List Term)
  | 0 => #[[nil]]
  | n + 1 =>
    let T := genTab n
    T.push ((List.range (n + 1)).flatMap fun k =>
      (T.getD k []).flatMap fun b =>
        (T.getD (n - k) []).flatMap fun t => [cons nil b t, cons t1 b t])

/-- The standard countable ones among them, up to `n`. -/
def smallFrag (n : Nat) : List Term :=
  ((List.range (n + 1)).flatMap fun k => (genTab n).getD k []).filter
    fun a => isOT a && decide (a < tW)

#guard (smallFrag 6).length = 610
#guard (smallFrag 6).all fun a => trioE a == TrioRules.trioMatrixL a

/-- `ψ_0` applied `n` times to `0`. -/
def towerP : Nat → Term
  | 0 => nil
  | n + 1 => psi nil (towerP n)

-- The fuel runs out: `ψ_0(Ω + T₂₀₅)` and `ψ_0(Ω + T₂₀₆)` are distinct standard
-- terms between `ε₀` and `ε₁` with the same `trioMatrixL`; `trioE` separates them.
#guard isOT (psi nil (cons t1 nil (towerP 205))) && isOT (psi nil (cons t1 nil (towerP 206)))
#guard decide (psi nil (cons t1 nil (towerP 205)) < psi nil (cons t1 nil (towerP 206)))
#guard TrioRules.trioMatrixL (psi nil (cons t1 nil (towerP 205)))
  = TrioRules.trioMatrixL (psi nil (cons t1 nil (towerP 206)))
#guard trioE (psi nil (cons t1 nil (towerP 205))) != trioE (psi nil (cons t1 nil (towerP 206)))
-- The same below `ε₀`.
#guard TrioRules.trioMatrixL (towerP 210) = TrioRules.trioMatrixL (towerP 211)

-- `ψ_0(Ω + 1) = ε₀·ω`: the map on terms lays it out as the program lays out
-- the label `psi(W)^psi(W)^w`, `ε₀^{ε₀^ω}`, not as the sheet's row for `ε₀·ω`.
#guard TrioRules.trioMatrixL (psi nil (cons t1 nil t1))
  = [[0,0,0],[1,1,1],[2,1,1],[3,0,0],[4,1,0],[4,0,0]]
#guard TrioRules.trioRuleMatrixOf "psi(W)^psi(W)^w"
  = some [[0,0,0],[1,1,1],[2,1,1],[3,0,0],[4,1,0],[4,0,0]]
#guard TrioRules.trioRuleMatrixOf "psi(W)*w" = some [[0,0,0],[1,1,1],[2,1,1],[3,0,0],[4,1,0],[2,1,1]]

end Googology.Trans.BMS.TrioTree
