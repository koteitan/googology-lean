import Googology.Trans.BMS.Equiv
import Googology.Trans.BMS.RankVal

/-!
# Cells of the translation tables: primitive sequences

This file fills three cells of the tables in the README.

**Order-preserving.**  The order on the states of `prim` is the dictionary
order on the entries (`List.lt`).  `cmp_read` says the reading turns it into
the order on terms: for two matrices at the same level, comparing the terms
gives the same answer as comparing the lists.  With `val_lt_val` this becomes
`primEval_lt_iff`: one matrix is below another exactly when its ordinal is
smaller.

**Preserves the rank.**  `primHomE0`, the forward half of `primEquivE0`, keeps
the bracket numbers and halts exactly where the source halts.  So
`StepHom.rank_map` applies: `rank_primHomE0`.

**Injective.**  `primHomPair` writes a row of zeros under a matrix.  Taking
the first row back gives the matrix, so the map is one to one:
`primHomPair_injective`.
-/

namespace Googology.Trans.BMS

open Googology.Notation.ExBuchholz
open Googology.Notation.ExBuchholz.Term

/-! ### The dictionary order on lists -/

/-- The dictionary comparison of two lists of naturals.  A proper prefix is
smaller. -/
def lcmp : List Nat → List Nat → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: l, c :: m => (compare a c).then (lcmp l m)

/-- `lcmp` says `.lt` exactly when the lists are in the order `List.lt`. -/
theorem lcmp_eq_lt_iff : ∀ l m : List Nat, lcmp l m = .lt ↔ l < m := by
  intro l
  induction l with
  | nil =>
    intro m
    cases m with
    | nil => simp [lcmp]
    | cons c m => simp [lcmp]
  | cons a l ih =>
    intro m
    cases m with
    | nil => simp [lcmp]
    | cons c m =>
      rw [List.cons_lt_cons_iff, ← ih m]
      show (compare a c).then (lcmp l m) = .lt ↔ _
      rcases Nat.lt_trichotomy a c with h | h | h
      · rw [Nat.compare_eq_lt.mpr h]
        exact ⟨fun _ => Or.inl h, fun _ => rfl⟩
      · rw [Nat.compare_eq_eq.mpr h]
        exact ⟨fun h' => Or.inr ⟨h, h'⟩, fun h' => h'.elim (fun h'' => absurd h'' (by omega))
          (fun h'' => h''.2)⟩
      · rw [Nat.compare_eq_gt.mpr h]
        refine ⟨fun h' => Ordering.noConfusion h', fun h' => ?_⟩
        rcases h' with h' | h'
        · omega
        · omega

theorem then_assoc (x y z : Ordering) : (x.then y).then z = x.then (y.then z) := by
  cases x <;> rfl

/-- Comparing `h₁ ++ lo₁` with `h₂ ++ lo₂`, where every entry of `h₁, h₂` is
above `b` and `lo₁, lo₂` start at or below `b`, compares `h₁` with `h₂` first
and `lo₁` with `lo₂` after. -/
theorem lcmp_append (b : Nat) : ∀ (h₁ h₂ lo₁ lo₂ : List Nat),
    (∀ x ∈ h₁, b < x) → (∀ x ∈ h₂, b < x) →
    (∀ x ∈ lo₁.head?, x ≤ b) → (∀ x ∈ lo₂.head?, x ≤ b) →
    lcmp (h₁ ++ lo₁) (h₂ ++ lo₂) = (lcmp h₁ h₂).then (lcmp lo₁ lo₂) := by
  intro h₁
  induction h₁ with
  | nil =>
    intro h₂ lo₁ lo₂ _ hh₂ hl₁ _
    cases h₂ with
    | nil => rfl
    | cons y h₂ =>
      cases lo₁ with
      | nil => rfl
      | cons z lo₁ =>
        have hz : z ≤ b := hl₁ z rfl
        have hy : b < y := hh₂ y (List.mem_cons_self)
        show (compare z y).then _ = Ordering.lt.then _
        rw [Nat.compare_eq_lt.mpr (by omega)]
        rfl
  | cons x h₁ ih =>
    intro h₂ lo₁ lo₂ hh₁ hh₂ hl₁ hl₂
    cases h₂ with
    | nil =>
      cases lo₂ with
      | nil => rfl
      | cons z lo₂ =>
        have hz : z ≤ b := hl₂ z rfl
        have hx : b < x := hh₁ x (List.mem_cons_self)
        show (compare x z).then _ = Ordering.gt.then _
        rw [Nat.compare_eq_gt.mpr (by omega)]
        rfl
    | cons y h₂ =>
      show (compare x y).then (lcmp (h₁ ++ lo₁) (h₂ ++ lo₂))
        = ((compare x y).then (lcmp h₁ h₂)).then (lcmp lo₁ lo₂)
      rw [then_assoc, ih h₂ lo₁ lo₂ (fun x hx => hh₁ x (List.mem_cons_of_mem _ hx))
        (fun x hx => hh₂ x (List.mem_cons_of_mem _ hx)) hl₁ hl₂]

theorem head_le_of_col {b : Nat} : ∀ {l : List Nat}, Col b l → ∀ x ∈ l.head?, x ≤ b
  | [], _, x, hx => by simp at hx
  | a :: _, h, x, hx => by
    have hx' : a = x := by simpa using hx
    rw [← hx', h.1]

theorem lt_of_mem_takeWhile {b x : Nat} {s : List Nat}
    (h : x ∈ s.takeWhile (fun a => decide (b < a))) : b < x := by
  have := List.mem_takeWhile_imp h
  simpa using this

/-- **The reading turns the dictionary order on matrices into the order on
terms.**  For two matrices at the same level, the terms compare exactly as the
lists do. -/
theorem cmp_read : ∀ (n : Nat) (l m : List Nat) (b : Nat), l.length + m.length = n →
    Col b l → Col b m → Term.cmp (read b l) (read b m) = lcmp l m := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro l m b hn hl hm
    cases l with
    | nil =>
      cases m with
      | nil => rw [read_nil]; rfl
      | cons c m => rw [read_nil, read_cons]; rfl
    | cons a l =>
      cases m with
      | nil => rw [read_nil, read_cons]; rfl
      | cons c m =>
        obtain ⟨ha, hcl⟩ := hl
        obtain ⟨hc, hcm⟩ := hm
        subst hc; subst ha
        rw [read_cons, read_cons]
        show (Term.cmp nil nil).then ((Term.cmp _ _).then (Term.cmp _ _)) = (compare a a).then (lcmp l m)
        rw [cmp_self, Nat.compare_eq_eq.mpr rfl]
        show (Term.cmp _ _).then (Term.cmp _ _) = lcmp l m
        have hl1 := (List.takeWhile_sublist (fun x => decide (a < x)) (l := l)).length_le
        have hl2 := (List.dropWhile_sublist (fun x => decide (a < x)) (l := l)).length_le
        have hm1 := (List.takeWhile_sublist (fun x => decide (a < x)) (l := m)).length_le
        have hm2 := (List.dropWhile_sublist (fun x => decide (a < x)) (l := m)).length_le
        simp only [List.length_cons] at hn
        have hcol1 := col_takeWhile l a a (Nat.le_refl _) hcl
        have hcol2 := col_takeWhile m a a (Nat.le_refl _) hcm
        have hlo1 := col_dropWhile l a a hcl
        have hlo2 := col_dropWhile m a a hcm
        rw [ih _ (by omega) _ _ (a + 1) rfl hcol1 hcol2,
          ih _ (by omega) _ _ a rfl hlo1 hlo2]
        conv_rhs => rw [← List.takeWhile_append_dropWhile (p := fun x => decide (a < x)) (l := l),
          ← List.takeWhile_append_dropWhile (p := fun x => decide (a < x)) (l := m)]
        rw [lcmp_append a _ _ _ _ (fun x hx => lt_of_mem_takeWhile hx)
          (fun x hx => lt_of_mem_takeWhile hx) (head_le_of_col hlo1) (head_le_of_col hlo2)]

/-- **Two matrices compare as their terms do.** -/
theorem read_lt_read_iff {l m : List Nat} {b : Nat} (hl : Col b l) (hm : Col b m) :
    read b l < read b m ↔ l < m := by
  rw [lt_def, cmp_read _ l m b rfl hl hm, lcmp_eq_lt_iff]

/-! ### Order-preserving -/

/-- The order on the states of the primitive sequence system: the dictionary
order on the entries. -/
def primLt (a b : PrimState) : Prop := a.1 < b.1

theorem primEval_val (l : PrimState) : primEval.val l = val (read 0 l.1) := rfl

/-- **Primitive sequences → ordinals is order-preserving.**  One matrix is
below another in the dictionary order exactly when its ordinal is smaller. -/
theorem primEval_lt_iff (a b : PrimState) :
    primLt a b ↔ primEval.val a < primEval.val b := by
  rw [primEval_val, primEval_val]
  unfold primLt
  rw [← read_lt_read_iff a.2.1 b.2.1]
  refine ⟨val_lt_val a.2.2 b.2.2, fun h => ?_⟩
  rcases lt_trichotomy (read 0 a.1) (read 0 b.1) with h' | h' | h'
  · exact h'
  · rw [h'] at h; exact absurd h (lt_irrefl _)
  · exact absurd (val_lt_val b.2.2 a.2.2 h') (not_lt.mpr h.le)

/-! ### Preserves the rank -/

instance instIsWellFoundedE0 : IsWellFounded exbE0.State exbE0.Rel :=
  ⟨primEquivE0.wf_iff.mp prim_wf⟩

/-- **Primitive sequences → extended Buchholz's ψ preserves the rank.**  The
map is `primHomE0`, the forward half of `primEquivE0`. -/
theorem rank_primHomE0 (l : PrimState) :
    IsWellFounded.rank exbE0.Rel (primHomE0.map l) = IsWellFounded.rank prim.Rel l :=
  primHomE0.rank_map (fun k => ⟨k, rfl⟩)
    (fun s => ⟨fun h => by
      show read 0 s.1 = nil
      rw [show s.1 = [] from h, read_nil],
      fun h => read_eq_nil s.1 0 h⟩) l

/-- The same, for the map as it sits in `primEquivE0`. -/
theorem rank_primEquivE0 (l : PrimState) :
    IsWellFounded.rank exbE0.Rel (primEquivE0.toFun.map l) = IsWellFounded.rank prim.Rel l :=
  rank_primHomE0 l

/-- On the standard forms below `ψ_0(Ω)` the rank is the value of the term. -/
theorem rank_e0_eq_val (X : exbE0.State) : IsWellFounded.rank exbE0.Rel X = val X.1 := by
  have h := rank_primHomE0 (toUnread X)
  have hX : primHomE0.map (toUnread X) = X := primEquivE0.right_inv X
  rw [hX, rank_prim_eq_val] at h
  rw [h]
  show val (read 0 (unread 0 X.1)) = val X.1
  rw [read_unread X.1 (allNil_of_state X) 0]

/-! ### Injective -/

/-- **Primitive sequences → pair sequences is injective.** -/
theorem primHomPair_injective : Function.Injective primHomPair.map := by
  intro l m h
  have h1 : withZero l.1 = withZero m.1 := congrArg Subtype.val h
  have h2 := congrArg (List.map Prod.fst) h1
  simp only [withZero, List.map_map] at h2
  have e : (Prod.fst ∘ fun a : Nat => (a, 0)) = id := rfl
  rw [e, List.map_id, List.map_id] at h2
  exact Subtype.ext h2

end Googology.Trans.BMS
