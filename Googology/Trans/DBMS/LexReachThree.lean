import Googology.Trans.DBMS.BlocksLex

/-!
# `LexReach r` holds at every number of rows

`BlocksLex.lean` reduces the characterization "a list of blocks is standard
iff its contents do not increase in the dictionary order" to `LexReach r`: a
content reaches every content of `CReach r` below it.  This file proves it, at
every number of rows, so in particular `LexReach 2`.

The argument does not look at the entries.

* `rt_expandRL_succ`: **`M[N + 1]` reaches `M[N]`.**  If `M` has a bad root,
  `M[N + 1] = M[N] ++ X` (`expandRL_succ_append`), and a list reaches each of
  its prefixes by `[0]` steps (`rt_prefix`).  Without a bad root every `M[N]`
  is `M` without its last column.
* `rt_total_of_rt`: so **what one matrix reaches is totally ordered by
  reaching.**  By induction on the rank of `M`: a matrix reached from `M` is
  `M` or reached from some `M[N]`; two of them, reached from `M[N₁]` and
  `M[N₂]` with `N₁ ≤ N₂`, are both reached from `M[N₂]`, of smaller rank.
* `reachTotal`: every content is reached from a generator `cgen r n`, and a
  larger generator reaches a smaller one by `[0]`, so any two contents are
  reached from one generator; reaching is total on `CReach r`.
* `lexReach`, `lexCof`: then `LexReach r` and `LexCof r` by
  `lexReach_iff_total`, `lexReach_iff_lexCof`.

At three rows: `lexReach_two`, `lexCof_two`, and the characterization of the
standard forms in the dictionary order, `dstdL_three_iff_dlex`, and
`rt_iff_le_three` (a content reaches another iff the other is `≤` in the
dictionary order).
-/

namespace Googology.Trans.DBMS

open BM4
open Googology.Notation.DBMS
open Googology.Trans.BMS
open Ordinal Order

/-- **`M[N + 1]` reaches `M[N]`**: the next member of the fundamental sequence
extends the previous one, and a list reaches its prefixes. -/
theorem rt_expandRL_succ {r : Nat} {M : List (List Nat)} (hv : Valid r M) (N : Nat) :
    Relation.ReflTransGen (CStep r) (expandRL (r + 1) (N + 1) M) (expandRL (r + 1) N M) := by
  cases hb : badRootR (r + 1) M with
  | none =>
    have e : ∀ K, expandRL (r + 1) K M = M.dropLast := by
      intro K; rw [expandRL, hb]
    rw [e, e]
  | some p =>
    obtain ⟨X, _, he⟩ := expandRL_succ_append (r + 1) N M hb
    have hv' : Valid r (expandRL (r + 1) N M ++ X) := by
      rw [← he]; exact valid_expandRL hv _
    rw [he]
    exact rt_prefix _ X hv'

/-- The fundamental sequence goes up in the reaching order. -/
theorem rt_expandRL_of_le {r : Nat} {M : List (List Nat)} (hv : Valid r M) {N₁ N₂ : Nat}
    (h : N₁ ≤ N₂) :
    Relation.ReflTransGen (CStep r) (expandRL (r + 1) N₂ M) (expandRL (r + 1) N₁ M) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | step _ ih => exact (rt_expandRL_succ hv _).trans ih

/-- What the empty list reaches is the empty list. -/
theorem eq_nil_of_rt_nil {r : Nat} {B : List (List Nat)}
    (h : Relation.ReflTransGen (CStep r) [] B) : B = [] := by
  induction h with
  | refl => rfl
  | tail _ hs ih =>
    obtain ⟨N, rfl⟩ := hs
    rw [ih, expandRL_nil]

theorem rt_total_of_rt_aux (r : Nat) (o : Ordinal.{0}) : ∀ M : List (List Nat), Valid r M →
    rkL r M = o → ∀ B C, Relation.ReflTransGen (CStep r) M B →
      Relation.ReflTransGen (CStep r) M C →
      Relation.ReflTransGen (CStep r) B C ∨ Relation.ReflTransGen (CStep r) C B := by
  induction o using WellFoundedLT.induction with
  | _ o ih =>
  intro M hv ho B C hB hC
  by_cases hM : M = []
  · subst hM
    rw [eq_nil_of_rt_nil hB, eq_nil_of_rt_nil hC]
    exact Or.inl Relation.ReflTransGen.refl
  rcases Relation.ReflTransGen.cases_head hB with hBe | ⟨B', ⟨N₁, rfl⟩, hB'⟩
  · subst hBe; exact Or.inl hC
  rcases Relation.ReflTransGen.cases_head hC with hCe | ⟨C', ⟨N₂, rfl⟩, hC'⟩
  · subst hCe; exact Or.inr hB
  -- both are reached from `M[max N₁ N₂]`
  set K := max N₁ N₂ with hK
  have hB2 : Relation.ReflTransGen (CStep r) (expandRL (r + 1) K M) B :=
    (rt_expandRL_of_le hv (le_max_left N₁ N₂)).trans hB'
  have hC2 : Relation.ReflTransGen (CStep r) (expandRL (r + 1) K M) C :=
    (rt_expandRL_of_le hv (le_max_right N₁ N₂)).trans hC'
  have hlt : rkL r (expandRL (r + 1) K M) < o := by rw [← ho]; exact rkL_lt hv hM K
  exact ih _ hlt _ (valid_expandRL hv K) rfl B C hB2 hC2

/-- **What one matrix reaches is totally ordered by reaching.** -/
theorem rt_total_of_rt {r : Nat} {M B C : List (List Nat)} (hv : Valid r M)
    (hB : Relation.ReflTransGen (CStep r) M B) (hC : Relation.ReflTransGen (CStep r) M C) :
    Relation.ReflTransGen (CStep r) B C ∨ Relation.ReflTransGen (CStep r) C B :=
  rt_total_of_rt_aux r _ M hv rfl B C hB hC

/-- A larger generator reaches a smaller one. -/
theorem rt_cgen_of_le (r : Nat) {m n : Nat} (h : m ≤ n) :
    Relation.ReflTransGen (CStep r) (cgen r n) (cgen r m) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @step n _ ih =>
    have hs : CStep r (cgen r (n + 1)) (cgen r n) :=
      ⟨0, by rw [expandRL_zero (r + 1) _ (valid_cgen r (n + 1)), cgen_dropLast]⟩
    exact Relation.ReflTransGen.head hs ih

/-- **Reaching is total on the content system**, at every number of rows. -/
theorem reachTotal (r : Nat) : ReachTotal r := by
  intro M M' hM hM'
  obtain ⟨m, hm⟩ := hM.exists_rt
  obtain ⟨m', hm'⟩ := hM'.exists_rt
  exact rt_total_of_rt (valid_cgen r (max m m'))
    ((rt_cgen_of_le r (le_max_left m m')).trans hm)
    ((rt_cgen_of_le r (le_max_right m m')).trans hm')

/-- **`LexReach r` at every number of rows**: a content reaches every content
of the content system below it in the dictionary order. -/
theorem lexReach (r : Nat) : LexReach r :=
  (lexReach_iff_total r).mpr (reachTotal r)

/-- **The fundamental sequences are cofinal** in the dictionary order on the
content system, at every number of rows. -/
theorem lexCof (r : Nat) : LexCof r :=
  (lexReach_iff_lexCof r).mp (lexReach r)

/-- **A content reaches another iff the other is at most it in the dictionary
order**, at every number of rows. -/
theorem rt_iff_le_all {r : Nat} {M M' : List (List Nat)} (hM : CReach r M) (hM' : CReach r M') :
    Relation.ReflTransGen (CStep r) M M' ↔ M' ≤ M :=
  rt_iff_le (lexReach r) hM hM'

/-- **Standard iff the contents do not increase in the dictionary order**, at
every number of rows. -/
theorem dstdL_iff_dlex (r : Nat) (l : List (List Nat)) :
    DStdL r l ↔ ∃ Ms, DLex r Ms ∧ l = blocksR r Ms :=
  dstdL_iff_dlex_of_lexReach (lexReach r) l

/-! ### Three rows -/

/-- **`LexReach 2`.** -/
theorem lexReach_two : LexReach 2 := lexReach 2

/-- **`ReachTotal 2`.** -/
theorem reachTotal_two : ReachTotal 2 := reachTotal 2

/-- **`LexCof 2`**: for contents `X < M` of `C₃`, some `M[N]` is `≥ X`. -/
theorem lexCof_two : LexCof 2 := lexCof 2

/-- **Three rows: reaching is the dictionary order on `C₃`.** -/
theorem rt_iff_le_three {M M' : List (List Nat)} (hM : CReach 2 M) (hM' : CReach 2 M') :
    Relation.ReflTransGen (CStep 2) M M' ↔ M' ≤ M :=
  rt_iff_le_three_of_lexReach lexReach_two hM hM'

/-- **Three rows: a list of columns is a standard form of three-row DBMS iff it
is a list of blocks whose contents lie in `C₃` and do not increase in the
dictionary order.** -/
theorem dstdL_three_iff_dlex (l : List (List Nat)) :
    DStdL 2 l ↔
      ∃ Ms, (∀ M ∈ Ms, CReach 2 M) ∧ Ms.Pairwise (fun a b => b ≤ a) ∧ l = blocksR 2 Ms :=
  dstdL_three_iff_dlex_of_lexReach lexReach_two l

end Googology.Trans.DBMS

#print axioms Googology.Trans.DBMS.lexReach_two
#print axioms Googology.Trans.DBMS.dstdL_three_iff_dlex
