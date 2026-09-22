import Googology.Trans.BMS.Bms
import Googology.Trans.BMS.Cofinal

/-!
# Which one-row matrices are standard

`Trans/BMS/Bms.lean` reads a standard array off as a matrix whose term is a
standard form.  This file goes the other way: every such matrix is the entries
of a standard array, so `std_entries_iff` settles what the states of `prim`
are.

The proof is the usual descent.  The generators `(0)(1)⋯(n)` read as towers,
and `exists_lt_twr` says the towers reach past any term below `ψ_0(Ω)`.  So
pick a generator above the matrix and walk down: `exists_le_fs` says one
expansion of the generator still sits above, `fs_lt` says it sits strictly
below the generator, and `OTLt_wf` says that cannot go on forever.  The walk
ends where the two terms are equal, and `unread_read` makes that an equality
of matrices.

`exists_bms_of_lt_e0` reads the conclusion on the ordinal side: every standard
form below `ψ_0(Ω)` is named by a one-row matrix.
-/

namespace Googology.Trans.BMS

open BM4 Pat
open Googology.Notation.ExBuchholz
open Googology.Notation.ExBuchholz.Term

/-- The towers are cofinal below `ψ_0(Ω)`. -/
theorem exists_lt_twr : ∀ X : Term, AllNil X → ∃ m, X < twr m := by
  intro X
  induction hn : size X using Nat.strong_induction_on generalizing X with
  | _ n ih =>
    cases X with
    | nil => exact fun _ => ⟨1, by rw [twr, twr]; exact nil_lt_cons _ _ _⟩
    | cons a b t =>
      intro h
      obtain ⟨ha, hAb, _⟩ := h
      subst ha
      obtain ⟨m, hm⟩ := ih (size b) (by subst hn; simp only [size_cons]; omega) b rfl hAb
      exact ⟨m + 1, by
        rw [twr]
        exact cons_lt_psi_iff.mpr (psi_lt_psi_iff.mpr (Or.inr ⟨rfl, hm⟩))⟩

theorem read_range_eq_twr (k : Nat) : read 0 (List.range (k + 1)) = twr (k + 1) := by
  rw [List.range_eq_range', read_range']

/-- A matrix is reachable when it is the entries of a standard array. -/
def Reach (l : List Nat) : Prop := ∃ A : Arr 1, Std 1 A ∧ entries A = l

theorem reach_range (n : Nat) : Reach (List.range (n + 1)) :=
  ⟨stair 1 n, Std.init n, entries_stair n⟩

theorem reach_expandL {l : List Nat} (hc : Col 0 l) (h : Reach l) (N : Nat) :
    Reach (expandL N 0 l) := by
  obtain ⟨A, hStd, hA⟩ := h
  refine ⟨expand A N, Std.step N hStd, ?_⟩
  rw [entries_expand' A N (by rw [hA]; exact hc), hA]

/-- The reading is one to one on matrices. -/
theorem read_inj {l m : List Nat} (hl : Col 0 l) (hm : Col 0 m) (h : read 0 l = read 0 m) :
    l = m := by
  rw [← unread_read l 0 hl, ← unread_read m 0 hm, h]

/-- **Everything at or below a reachable matrix is reachable.** -/
theorem reach_of_le (X : Term) : ∀ g : List Nat, Col 0 g → OT (read 0 g) → read 0 g = X →
    Reach g → ∀ l : List Nat, Col 0 l → OT (read 0 l) → read 0 l ≤ X → Reach l := by
  refine WellFounded.induction (C := fun X => ∀ g : List Nat, Col 0 g → OT (read 0 g) →
    read 0 g = X → Reach g → ∀ l : List Nat, Col 0 l → OT (read 0 l) → read 0 l ≤ X → Reach l)
    OTLt_wf X ?_
  intro X ih g hcg hOTg hgX hR l hcl hOTl hle
  subst hgX
  rcases le_iff_lt_or_eq.mp hle with h | h
  · obtain ⟨n, hn⟩ := exists_le_fs _ _ hOTg hOTl (allNil_read 0 g) (allNil_read 0 l) h
    have hgne : read 0 g ≠ nil := by
      intro he; rw [he] at h; exact not_lt_nil _ h
    have hstep : read 0 (expandL n 0 g) = fs (read 0 g) (idx (read 0 g) (n + 1)) :=
      read_expandL n g 0 hcg
    have hOTe : OT (read 0 (expandL n 0 g)) := (prim_step_ok ⟨g, hcg, hOTg⟩ n).2
    have hlt : OTLt (read 0 (expandL n 0 g)) (read 0 g) := by
      refine ⟨hOTe, hOTg, ?_⟩
      rw [hstep]
      exact fs_lt (idx_lt_dom hOTg (read_lt_tW 0 g) hgne (n + 1))
    exact ih _ hlt (expandL n 0 g) (col_expandL n g 0 hcg) hOTe rfl
      (reach_expandL hcg hR n) l hcl hOTl (by rw [hstep]; exact hn)
  · rw [read_inj hcl hcg h]; exact hR

/-- **Every standard one-row matrix is the entries of a standard array.**  With
`std_entries` this settles the states of `prim`: they are exactly the entries
of the standard one-row Bashicu matrices. -/
theorem exists_std_of_col {l : List Nat} (hc : Col 0 l) (hOT : OT (read 0 l)) :
    ∃ A : Arr 1, Std 1 A ∧ entries A = l := by
  obtain ⟨m, hm⟩ := exists_lt_twr (read 0 l) (allNil_read 0 l)
  cases m with
  | zero => exact absurd hm (by rw [twr]; exact not_lt_nil _)
  | succ k =>
    exact reach_of_le _ (List.range (k + 1)) (col_range k) (OT_read_range k)
      (read_range_eq_twr k) (reach_range k) l hc hOT
      (le_of_lt hm)

/-- **The standard one-row Bashicu matrices are exactly the matrices whose
term is a standard form.**  Both directions: `std_entries` reads a standard
array off as one, and `exists_std_of_col` builds a standard array from one. -/
theorem std_entries_iff (l : List Nat) :
    (∃ A : Arr 1, Std 1 A ∧ entries A = l) ↔ (Col 0 l ∧ OT (read 0 l)) := by
  constructor
  · rintro ⟨A, hStd, rfl⟩
    exact std_entries A hStd
  · rintro ⟨hc, hOT⟩
    exact exists_std_of_col hc hOT

/-- **Every standard form below `ψ_0(Ω)` is named by a one-row Bashicu
matrix.**  So `bmsOrdEval` lands on exactly the ordinals those forms name. -/
theorem exists_bms_of_lt_e0 {X : Term} (hOT : OT X) (hlt : X < te0) :
    ∃ A : (Googology.Notation.BMS.bms 1).State, read 0 (entries A.1) = X := by
  obtain ⟨l, hc, hl⟩ := exists_read hOT hlt
  obtain ⟨A, hStd, hA⟩ := exists_std_of_col hc (by rw [hl]; exact hOT)
  exact ⟨⟨A, hStd⟩, by rw [hA]; exact hl⟩


end Googology.Trans.BMS
