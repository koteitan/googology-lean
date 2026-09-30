import Googology.Trans.BMS.PoR.PSS.SC.Tree

/-!
# The five conditions of Theorem SC

`proof/COMB.md` §8b states Theorem SC with five conditions on the forest of
row-0 parents of a pair sequence (`SC/Basic.lean`):

* **(R0)** `M₀ = (0,0)`, and every root has `y = 0`;
* **(I0)** `x_{j+1} ≤ x_j + 1`;
* **(A)** `y_c ≤ y_{p(c)} + 1` for every non-root `c` with parent `p(c)`;
* **(Sib)** siblings (the roots count as siblings) have non-increasing terms;
* **(G\*)** `T(u) <ₚ T(v(u))` for every descending node `u`: a non-root with
  `y_u ≤ y_{p(u)}`, where `v(u)` is its nearest proper ancestor with
  `y ≤ y_u`.

All are decidable.  `vOf_eq_some_iff` and `descending_iff` restate `v(u)` and
"descending" with the ancestor relation `Anc` of `SC/Tree.lean`.
-/

namespace Googology.Trans.PSS

open Forest

open Bijectivity (ltPS lePS)

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

/-! ## `v(u)` and "descending" through ancestors -/

/-- **`v(u)` is the largest ancestor of `u` with `y ≤ y_u`.** -/
theorem vOf_eq_some_iff {M : PS} {u v : ℕ} :
    vOf M u = some v ↔
      Anc M v u ∧ yAt M v ≤ yAt M u ∧ ∀ a, Anc M a u → v < a → yAt M u < yAt M a := by
  unfold vOf
  rw [find?_eq_some_of_pairwise ancs_pairwise]
  simp only [mem_ancs, decide_eq_true_eq, decide_eq_false_iff_not, not_le]

theorem descending_iff {M : PS} {u : ℕ} :
    Descending M u ↔ ∃ p, par M u = some p ∧ yAt M u ≤ yAt M p := by
  unfold Descending
  constructor
  · rintro ⟨p, _, hp, hy⟩
    exact ⟨p, hp, hy⟩
  · rintro ⟨p, hp, hy⟩
    have h1 := (anc_of_par hp).lt_length
    have h2 := par_lt hp
    exact ⟨p, by omega, hp, hy⟩

/-- `v(u)` only sees the columns up to `u`. -/
theorem vOf_congr {M M' : PS} {u : ℕ} (hx : ∀ j ≤ u, xAt M j = xAt M' j)
    (hy : ∀ j ≤ u, yAt M j = yAt M' j) : vOf M u = vOf M' u := by
  apply Option.ext
  intro v
  rw [vOf_eq_some_iff, vOf_eq_some_iff]
  have hanc : ∀ a, Anc M a u ↔ Anc M' a u := fun a => Anc_congr hx
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hv := h1.1
    refine ⟨(hanc v).mp h1, by rw [← hy v hv.le, ← hy u le_rfl]; exact h2, fun a ha hva => ?_⟩
    have := h3 a ((hanc a).mpr ha) hva
    rwa [hy u le_rfl, hy a ha.1.le] at this
  · rintro ⟨h1, h2, h3⟩
    have hv := h1.1
    refine ⟨(hanc v).mpr h1, by rw [hy v hv.le, hy u le_rfl]; exact h2, fun a ha hva => ?_⟩
    have := h3 a ((hanc a).mp ha) hva
    rwa [← hy u le_rfl, ← hy a ha.1.le] at this

/-- "Descending" only sees the columns up to `u`. -/
theorem descending_congr {M M' : PS} {u : ℕ} (hx : ∀ j ≤ u, xAt M j = xAt M' j)
    (hy : ∀ j ≤ u, yAt M j = yAt M' j) : Descending M u ↔ Descending M' u := by
  rw [descending_iff, descending_iff, par_congr hx]
  constructor
  · rintro ⟨p, hp, h⟩
    have := par_lt hp
    exact ⟨p, hp, by rw [← hy u le_rfl, ← hy p (by omega)]; exact h⟩
  · rintro ⟨p, hp, h⟩
    have := par_lt hp
    exact ⟨p, hp, by rw [hy u le_rfl, hy p (by omega)]; exact h⟩

end Googology.Trans.PSS
