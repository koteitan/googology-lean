import Googology.Trans.PSS.SC.Basic
import Googology.Trans.PSS.SC.Oper
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

* `R0`, `I0`, `CondA`, `Sib`, `Gstar`, and `SC` their conjunction.  All are
  decidable, and `SC` is checked on small examples at the end.
* `ctps_iff_SC : CTPS M ↔ SC M`, from the two directions
  `sc_of_ctps` (COMB §8b Part 1) and `ctps_of_sc` (Part 2).
* `r0_of_ctps` is proved; the other parts of the two directions are named
  placeholders (see the list below).

The facts about terms in `oper M n` that Part 1 uses are in `SC/Oper.lean`
(`term_oper_copy`, `term_oper_anc`).

## Placeholders (`sorry`)

* `i0_of_ctps`, `condA_of_ctps` (COMB Lemma 1), `sib_of_ctps` (Lemma 7),
  `gstar_of_ctps` (Lemma 8);
* `ctps_of_sc` (COMB §8b Part 2).
-/

namespace Googology.Trans.PSS

open Forest

open Bijectivity (CTPS ltPS lePS)

/-! ## The five conditions -/

/-- **(R0)** `M₀ = (0,0)`, and every root has `y = 0`. -/
def R0 (M : PS) : Prop :=
  M.head? = some (0, 0) ∧ ∀ i < M.length, par M i = none → yAt M i = 0

/-- **(I0)** `x_{j+1} ≤ x_j + 1`. -/
def I0 (M : PS) : Prop :=
  ∀ j, j + 1 < M.length → xAt M (j + 1) ≤ xAt M j + 1

/-- **(A)** `y_c ≤ y_{p(c)} + 1` for every non-root `c`. -/
def CondA (M : PS) : Prop :=
  ∀ c < M.length, ∀ p < M.length, par M c = some p → yAt M c ≤ yAt M p + 1

/-- **(Sib)** Siblings have non-increasing terms: if `c < c'` have the same
parent, or are both roots, then `T(c') ≤ₚ T(c)`. -/
def Sib (M : PS) : Prop :=
  ∀ c < M.length, ∀ c' < M.length, c < c' → par M c = par M c' → lePS (term M c') (term M c)

/-- `u` is **descending**: it has a parent `p` with `y_u ≤ y_p`. -/
def Descending (M : PS) (u : ℕ) : Prop := ∃ p < M.length, par M u = some p ∧ yAt M u ≤ yAt M p

instance (M : PS) (u : ℕ) : Decidable (Descending M u) := by unfold Descending; infer_instance

/-- `v(u)`: the nearest proper row-0 ancestor of `u` with `y ≤ y_u`. -/
def vOf (M : PS) (u : ℕ) : Option ℕ := (ancs M u).find? (fun a => decide (yAt M a ≤ yAt M u))

/-- **(G\*)** `T(u) <ₚ T(v(u))` for every descending node `u`. -/
def Gstar (M : PS) : Prop :=
  ∀ u < M.length, Descending M u → ∀ v < M.length, vOf M u = some v → ltPS (term M u) (term M v)

/-- **Theorem SC's criterion**: R0, I0, (A), Sib and G\*. -/
def SC (M : PS) : Prop := R0 M ∧ I0 M ∧ CondA M ∧ Sib M ∧ Gstar M

instance (M : PS) : Decidable (R0 M) := by unfold R0; infer_instance
instance (M : PS) : Decidable (I0 M) := by
  unfold I0
  exact decidable_of_iff (∀ j < M.length - 1, xAt M (j + 1) ≤ xAt M j + 1)
    ⟨fun h j hj => h j (by omega), fun h j hj => h j (by omega)⟩
instance (M : PS) : Decidable (CondA M) := by unfold CondA; infer_instance
instance (M : PS) : Decidable (Sib M) := by unfold Sib; infer_instance
instance (M : PS) : Decidable (Gstar M) := by unfold Gstar; infer_instance
instance (M : PS) : Decidable (SC M) := by unfold SC; infer_instance

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

/-- **(I0) for standard sequences** (COMB Lemma 1).  Placeholder. -/
theorem i0_of_ctps {M : PS} (h : CTPS M) : I0 M := by
  sorry

/-- **(A) for standard sequences** (COMB Lemma 1, (I2)).  Placeholder. -/
theorem condA_of_ctps {M : PS} (h : CTPS M) : CondA M := by
  sorry

/-- **(Sib) for standard sequences** (COMB Lemma 7).  Placeholder. -/
theorem sib_of_ctps {M : PS} (h : CTPS M) : Sib M := by
  sorry

/-- **(G\*) for standard sequences** (COMB Lemma 8).  Placeholder. -/
theorem gstar_of_ctps {M : PS} (h : CTPS M) : Gstar M := by
  sorry

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
