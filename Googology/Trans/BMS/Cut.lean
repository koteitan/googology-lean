import Googology.Trans.BMS.Commute

/-!
# Where expansion cuts

`BMS/Commute.lean` defines `expandL` by the block structure of a matrix,
because that is the shape the reading follows.  The definition of BMS states
expansion differently: find the last entry below the last one, drop the last
column, and repeat what lies between them `N + 1` times.

`cut` is that split, `cut_spec` says it is the right one, and `expandL_cut`
says `expandL` is exactly `good ++ bad ⌢ ⋯ ⌢ bad`.  `expandL_split` states the
two together.  So the block recursion and the textbook rule are the same rule,
and `read_expandL` is about the rule people mean.

The split is stated by concatenation — `l = g ++ bad ++ [x]`, `bad` beginning
below `x` and continuing at or above it — rather than by indices, because that
is what makes the induction follow `cut`'s own recursion.
-/

namespace Googology.Trans.BMS

open Googology.Notation.ExBuchholz
open Googology.Notation.ExBuchholz.Term

/-- Where expansion cuts a matrix: the good part and the bad part.  The last
entry is not in either. -/
def cut : Nat → List Nat → List Nat × List Nat
  | _, [] => ([], [])
  | b, _ :: rest =>
      if rest.dropWhile (fun x => decide (b < x)) = [] then
        (if rest.takeWhile (fun x => decide (b < x)) = [] then ([], [])
         else if lastOf (rest.takeWhile (fun x => decide (b < x))) = some (b + 1) then
           ([], b :: (rest.takeWhile (fun x => decide (b < x))).dropLast)
         else (b :: (cut (b + 1) (rest.takeWhile (fun x => decide (b < x)))).1,
               (cut (b + 1) (rest.takeWhile (fun x => decide (b < x)))).2))
      else (b :: (rest.takeWhile (fun x => decide (b < x))
              ++ (cut b (rest.dropWhile (fun x => decide (b < x)))).1),
            (cut b (rest.dropWhile (fun x => decide (b < x)))).2)
  termination_by _ s => s.length
  decreasing_by
    all_goals simp only [List.length_cons]
    all_goals first
      | exact Nat.lt_succ_of_le (List.takeWhile_sublist _).length_le
      | exact Nat.lt_succ_of_le (List.dropWhile_sublist _).length_le

@[simp] theorem cut_nil (b : Nat) : cut b [] = ([], []) := by simp [cut]

theorem cut_cons (b a : Nat) (rest : List Nat) :
    cut b (a :: rest) =
      if rest.dropWhile (fun x => decide (b < x)) = [] then
        (if rest.takeWhile (fun x => decide (b < x)) = [] then ([], [])
         else if lastOf (rest.takeWhile (fun x => decide (b < x))) = some (b + 1) then
           ([], b :: (rest.takeWhile (fun x => decide (b < x))).dropLast)
         else (b :: (cut (b + 1) (rest.takeWhile (fun x => decide (b < x)))).1,
               (cut (b + 1) (rest.takeWhile (fun x => decide (b < x)))).2))
      else (b :: (rest.takeWhile (fun x => decide (b < x))
              ++ (cut b (rest.dropWhile (fun x => decide (b < x)))).1),
            (cut b (rest.dropWhile (fun x => decide (b < x)))).2) := by
  conv_lhs => rw [cut]

theorem flatten_replicate_nil (k : Nat) :
    (List.replicate k ([] : List Nat)).flatten = [] := by
  induction k with
  | zero => rfl
  | succ m ih => rw [List.replicate_succ, List.flatten_cons, List.nil_append, ih]

/-- **Expansion is the cut, with the bad part repeated.** -/
theorem expandL_cut (N : Nat) : ∀ (l : List Nat) (b : Nat),
    expandL N b l = (cut b l).1 ++ (List.replicate (N + 1) (cut b l).2).flatten := by
  intro l
  induction hn : l.length using Nat.strong_induction_on generalizing l with
  | _ n ih =>
    cases l with
    | nil => intro b; rw [expandL_nil, cut_nil, flatten_replicate_nil]; rfl
    | cons a rest =>
      intro b
      have hhilen : (rest.takeWhile (fun x => decide (b < x))).length < n := by
        subst hn; simp only [List.length_cons]
        exact Nat.lt_succ_of_le (List.takeWhile_sublist _).length_le
      have hlolen : (rest.dropWhile (fun x => decide (b < x))).length < n := by
        subst hn; simp only [List.length_cons]
        exact Nat.lt_succ_of_le (List.dropWhile_sublist _).length_le
      rw [expandL_cons, cut_cons]
      split
      · split
        · rw [flatten_replicate_nil]; rfl
        · split
          · rw [List.nil_append]
          · rw [ih _ hhilen _ rfl (b + 1), List.cons_append]
      · rw [ih _ hlolen _ rfl b, List.cons_append, List.append_assoc]

/-- **The cut is where the textbook says it is.**  Writing `l = g ++ bad ++ [x]`
with `x` the last entry, the bad part starts at the last entry below `x`, and
it is empty exactly when no entry is below `x` — that is, when `x` is the
level itself. -/
theorem cut_spec : ∀ (l : List Nat) (b : Nat), Col b l → l ≠ [] →
    ∃ x, lastOf l = some x ∧
      l = (cut b l).1 ++ (cut b l).2 ++ [x] ∧
      (∀ y, (cut b l).2.head? = some y → y < x) ∧
      (∀ y ∈ (cut b l).2.tail, x ≤ y) ∧
      ((cut b l).2 = [] ↔ x = b) := by
  intro l
  induction hn : l.length using Nat.strong_induction_on generalizing l with
  | _ n ih =>
    cases l with
    | nil => intro _ _ h; exact absurd rfl h
    | cons a rest =>
      intro b hc _
      obtain ⟨ha, hch⟩ := hc
      subst ha
      have hcolhi : Col (a + 1) (rest.takeWhile (fun x => decide (a < x))) :=
        col_takeWhile rest a a (Nat.le_refl _) hch
      have hcollo : Col a (rest.dropWhile (fun x => decide (a < x))) :=
        col_dropWhile rest a a hch
      have hhilen : (rest.takeWhile (fun x => decide (a < x))).length < n := by
        subst hn; simp only [List.length_cons]
        exact Nat.lt_succ_of_le (List.takeWhile_sublist _).length_le
      have hlolen : (rest.dropWhile (fun x => decide (a < x))).length < n := by
        subst hn; simp only [List.length_cons]
        exact Nat.lt_succ_of_le (List.dropWhile_sublist _).length_le
      have hsplit : rest.takeWhile (fun x => decide (a < x))
          ++ rest.dropWhile (fun x => decide (a < x)) = rest :=
        List.takeWhile_append_dropWhile
      rw [cut_cons]
      by_cases hlo : rest.dropWhile (fun x => decide (a < x)) = []
      · rw [if_pos hlo]
        have hrest : rest = rest.takeWhile (fun x => decide (a < x)) := by
          have h0 := hsplit
          rw [hlo, List.append_nil] at h0
          exact h0.symm
        by_cases hhi : rest.takeWhile (fun x => decide (a < x)) = []
        · rw [if_pos hhi]
          have hr : rest = [] := by rw [hrest, hhi]
          subst hr
          exact ⟨a, rfl, rfl, by simp, by simp, by simp⟩
        · rw [if_neg hhi]
          have hrne : rest ≠ [] := fun he => hhi (by rw [he, List.takeWhile_nil])
          have hlastl : lastOf (a :: rest)
              = lastOf (rest.takeWhile (fun x => decide (a < x))) :=
            (lastOf_cons a rest hrne).trans (congrArg lastOf hrest)
          by_cases hl1 : lastOf (rest.takeWhile (fun x => decide (a < x))) = some (a + 1)
          · rw [if_pos hl1]
            refine ⟨a + 1, hlastl.trans hl1, ?_, ?_, ?_, ?_⟩
            · rw [List.nil_append, List.cons_append]
              exact congrArg (a :: ·) (hrest.trans (eq_concat_of_lastOf _ _ hl1))
            · intro y hy
              simp only [List.head?_cons, Option.some.injEq] at hy
              omega
            · intro y hy
              exact col_ge _ _ (col_dropLast _ _ hcolhi) y hy
            · exact ⟨fun h => absurd h (by simp), fun h => absurd h (by omega)⟩
          · rw [if_neg hl1]
            obtain ⟨x, hx1, hx2, hx3, hx4, hx5⟩ := ih _ hhilen _ rfl (a + 1) hcolhi hhi
            have hxne : x ≠ a + 1 := fun he => hl1 (by rw [hx1, he])
            have hxge : a + 1 ≤ x := col_ge _ _ hcolhi x (mem_of_lastOf _ _ hx1)
            refine ⟨x, hlastl.trans hx1, ?_, hx3, hx4, ?_⟩
            · rw [List.cons_append, List.cons_append]
              exact congrArg (a :: ·) (hrest.trans hx2)
            · exact ⟨fun h => absurd (hx5.mp h) hxne, fun h => absurd h (by omega)⟩
      · rw [if_neg hlo]
        obtain ⟨x, hx1, hx2, hx3, hx4, hx5⟩ := ih _ hlolen _ rfl a hcollo hlo
        have hrne : rest ≠ [] := by
          intro he; rw [he] at hlo; simp [List.dropWhile] at hlo
        refine ⟨x, ?_, ?_, hx3, hx4, hx5⟩
        · exact (lastOf_cons a rest hrne).trans
            ((congrArg lastOf hsplit.symm).trans ((lastOf_append _ _ hlo).trans hx1))
        · rw [List.cons_append, List.cons_append]
          refine congrArg (a :: ·) (hsplit.symm.trans ?_)
          exact (congrArg (rest.takeWhile (fun x => decide (a < x)) ++ ·) hx2).trans
            (by simp [List.append_assoc])

/-- **Expansion, in the form the definition of BMS states it.**  Write
`l = g ++ bad ++ [x]` with `x` the last entry and `bad` beginning at the last
entry below `x`.  Expansion drops `x` and writes `N + 1` copies of `bad`. -/
theorem expandL_split (N : Nat) (l : List Nat) (b : Nat) (h : Col b l) (hne : l ≠ []) :
    ∃ g bad x, l = g ++ bad ++ [x] ∧ lastOf l = some x ∧
      (∀ y, bad.head? = some y → y < x) ∧ (∀ y ∈ bad.tail, x ≤ y) ∧
      (bad = [] ↔ x = b) ∧
      expandL N b l = g ++ (List.replicate (N + 1) bad).flatten := by
  obtain ⟨x, h1, h2, h3, h4, h5⟩ := cut_spec l b h hne
  exact ⟨(cut b l).1, (cut b l).2, x, h2, h1, h3, h4, h5, expandL_cut N l b⟩

/-- When no entry is below the last one, expansion drops the last column. -/
theorem expandL_eq_dropLast (N : Nat) (l : List Nat) (b : Nat) (h : Col b l)
    (hne : l ≠ []) (hlast : lastOf l = some b) : expandL N b l = l.dropLast := by
  obtain ⟨x, h1, h2, _, _, h5⟩ := cut_spec l b h hne
  have hx : x = b := by rw [hlast] at h1; exact (Option.some.inj h1).symm
  have hbad : (cut b l).2 = [] := h5.mpr hx
  rw [expandL_cut N l b, hbad, flatten_replicate_nil, List.append_nil]
  conv_rhs => rw [h2, hbad]
  rw [List.append_nil, List.dropLast_concat]


end Googology.Trans.BMS
