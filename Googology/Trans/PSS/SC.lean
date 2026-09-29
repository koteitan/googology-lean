import Googology.Trans.PSS.SC.Defs
import Googology.Trans.PSS.SC.Step
import Googology.Trans.PSS.Rank

/-!
# Theorem SC: a criterion for standard pair sequences

`proof/COMB.md` §8b in this directory proves on paper that a pair sequence `M`
is standard and starts at `(0,0)` (`Bijectivity.CTPS M`) exactly when it
satisfies five conditions on its forest of row-0 parents (`SC/Basic.lean`,
namespace `Googology.Trans.PSS.Forest`):

* **(R0)** `M₀ = (0,0)`, and every root has `y = 0`;
* **(I0)** `x_{j+1} ≤ x_j + 1`;
* **(A)** `y_c ≤ y_{p(c)} + 1` for every non-root `c` with parent `p(c)`;
* **(Sib)** siblings (the roots count as siblings) have non-increasing terms;
* **(G\*)** `T(u) <ₚ T(v(u))` for every descending node `u`: a non-root with
  `y_u ≤ y_{p(u)}`, where `v(u)` is its nearest proper ancestor with
  `y ≤ y_u`.

Terms `T(u)` are the blocks of the columns, normalized to `x = 0`, compared by
the lexicographic order `<ₚ` with a proper prefix smaller.

## Contents

* `R0`, `I0`, `CondA`, `Sib`, `Gstar`, and `SC` their conjunction
  (`SC/Defs.lean`).  All are decidable, and `SC` is checked on small examples
  at the end.
* `ctps_iff_SC : CTPS M ↔ SC M`, from the two directions
  `sc_of_ctps` (COMB §8b Part 1) and `ctps_of_sc` (Part 2).
* Part 1 is proved.  `r0_of_ctps` and `i0_of_ctps` (`SC/Invariants.lean`);
  `condA_of_ctps`, `sib_of_ctps` and `gstar_of_ctps` by induction on
  `PSS.STPS` (`SC/Step.lean`): one expansion step `M ↦ M[n]` keeps (A), Sib
  and G\*.  The columns before the last column `j₁` of `M` are handled in
  `SC/Pert.lean` (`M[n]` lowers the column `j₁`), the columns from `j₁` on by
  induction on `n`, since they are a shifted copy of `M[n-1]` from `j₀` on.
  The tree facts (ancestors, parents, terms, the order `<ₚ`) are in
  `SC/Tree.lean`; the terms in `oper M n` in `SC/Oper.lean`.

## Placeholder (`sorry`)

* `ctps_of_sc` (COMB §8b Part 2).
-/

namespace Googology.Trans.PSS

open Forest

open Bijectivity (CTPS ltPS lePS)

/-! ## Part 1: CTPS ⇒ SC -/

/-- In a sequence whose first column has `x = 0`, a column with `x > 0` has a
parent. -/
theorem par_ne_none_of_pos {M : PS} (h0 : xAt M 0 = 0) {i : ℕ} (hi : 0 < xAt M i) :
    par M i ≠ none := by
  have hi0 : 0 < i := by
    rcases Nat.eq_zero_or_pos i with rfl | h
    · omega
    · exact h
  unfold par
  rw [ne_eq, List.getLast?_eq_none_iff, ← ne_eq, ← List.length_pos_iff, List.length_filter_pos_iff]
  exact ⟨0, List.mem_range.mpr hi0, by simp [h0, hi]⟩

/-- **(R0) for standard sequences.** -/
theorem r0_of_ctps {M : PS} (h : CTPS M) : R0 M := by
  have hne := ctps_ne_nil h
  have hhd := h.2
  have hinv := (good_of_ctps h).2
  obtain ⟨q, M', rfl⟩ := List.exists_cons_of_ne_nil hne
  simp only [List.headD_cons] at hhd
  subst hhd
  refine ⟨rfl, fun i hi hroot => ?_⟩
  have hx : xAt ((0, 0) :: M') i = 0 := by
    by_contra hx
    exact par_ne_none_of_pos (M := (0, 0) :: M') rfl (Nat.pos_of_ne_zero hx) hroot
  rw [xAt_of_lt hi] at hx
  rw [yAt_of_lt hi]
  exact hinv _ (List.getElem_mem hi) hx

/-- **(I0) for standard sequences** (COMB Lemma 1). -/
theorem i0_of_ctps {M : PS} (h : CTPS M) : I0 M := I0_of_stps h.1

/-- **(A) for standard sequences** (COMB Lemma 1, (I2)). -/
theorem condA_of_ctps {M : PS} (h : CTPS M) : CondA M := condA_of_stps h.1

/-- **(Sib) for standard sequences** (COMB Lemma 7). -/
theorem sib_of_ctps {M : PS} (h : CTPS M) : Sib M := sib_of_stps h.1

/-- **(G\*) for standard sequences** (COMB Lemma 8). -/
theorem gstar_of_ctps {M : PS} (h : CTPS M) : Gstar M := gstar_of_stps h.1

/-- **Theorem SC, Part 1: a standard sequence satisfies SC.** -/
theorem sc_of_ctps {M : PS} (h : CTPS M) : SC M :=
  ⟨r0_of_ctps h, i0_of_ctps h, condA_of_ctps h, sib_of_ctps h, gstar_of_ctps h⟩

/-! ## Part 2: SC ⇒ CTPS -/

/-- **Theorem SC, Part 2: a sequence satisfying SC is standard** (COMB §8b
Part 2: the least standard sequence above `M`, and Lemma 9).  Placeholder. -/
theorem ctps_of_sc {M : PS} (h : SC M) : CTPS M := by
  sorry

/-- **Theorem SC.**  A pair sequence is standard and starts at `(0,0)` exactly
when it satisfies R0, I0, (A), Sib and G\*. -/
theorem ctps_iff_SC (M : PS) : CTPS M ↔ SC M := ⟨sc_of_ctps, ctps_of_sc⟩

/-! ## Small examples -/

/-- `(0,0)(1,0)(2,1)` is not SC: the column `(1,0)` is descending, and its term
`(0,0)(1,1)` is above the term `(0,0)(1,0)(2,1)` of the root. -/
example : ¬ SC [(0, 0), (1, 0), (2, 1)] := by decide
example : ¬ Gstar [(0, 0), (1, 0), (2, 1)] := by decide
example : R0 [(0, 0), (1, 0), (2, 1)] ∧ I0 [(0, 0), (1, 0), (2, 1)] ∧
    CondA [(0, 0), (1, 0), (2, 1)] ∧ Sib [(0, 0), (1, 0), (2, 1)] := by decide

example : SC [(0, 0), (1, 1)] := by decide
example : SC [(0, 0), (0, 0)] := by decide
example : SC [(0, 0), (1, 1), (1, 1)] := by decide
example : SC [(0, 0), (1, 1), (2, 0)] := by decide
example : SC [(0, 0), (1, 1), (2, 2), (3, 1)] := by decide

/-- Sib fails: the later sibling `(1,1)` is above `(1,0)`. -/
example : ¬ Sib [(0, 0), (1, 0), (1, 1)] := by decide
/-- R0 fails: a root with `y = 1`. -/
example : ¬ R0 [(0, 0), (0, 1)] := by decide
/-- I0 fails. -/
example : ¬ I0 [(0, 0), (2, 0)] := by decide
/-- (A) fails. -/
example : ¬ CondA [(0, 0), (1, 2)] := by decide

example : par [(0, 0), (1, 1), (2, 0), (1, 1)] 3 = some 0 := by decide
example : children [(0, 0), (1, 1), (2, 0), (1, 1)] 0 = [1, 3] := by decide
example : term [(0, 0), (1, 1), (2, 0), (1, 1)] 1 = [(0, 1), (1, 0)] := by decide
example : vOf [(0, 0), (1, 1), (2, 2), (3, 1)] 3 = some 1 := by decide
example : forest [(0, 0), (1, 1), (2, 0), (1, 1), (0, 0)] =
    [.node 0 [.node 1 [.node 0 []], .node 1 []], .node 0 []] := by rfl
example : (treeAt [(0, 0), (1, 1), (2, 0), (1, 1)] 0).cols = term [(0, 0), (1, 1), (2, 0), (1, 1)] 0 := by
  decide

end Googology.Trans.PSS
