import Googology.Trans.BMS.PoR.PSS.SC.Oper
import Googology.Trans.BMS.ExBuchholz.PSS.Expand

/-!
# Invariants of standard pair sequences

(I0) of `proof/COMB.md` Lemma 1: every standard pair sequence has
`x_{j+1} ≤ x_j + 1`.  The proof is by induction on `PSS.STPS`: a diagonal
sequence has steps of `1`, dropping the last column keeps the steps, and in
the copying case of `oper` the steps inside a copy are those of `M`, while the
step from one copy to the next is `x_{j₀} + d₀ ≤ x_{j₁-1} + 1`.

* `oper_cases`: `oper M n` is `M`, `M.dropLast`, or the copying case.
* `ExpCase.x_lt`: the columns after `j₀` up to the last one are higher than
  `j₀` (the parent `j₀` is a row-0 ancestor of the last column in both rows).
* `xAt_oper_copy`: the entries of the `k`-th copy.
* `par_append_left`: parents are local.
* `I0_of_stps`.
-/

namespace Googology.Trans.PSS.Forest

open _root_.PSS (oper entry Lng idx1 hasParent parent parents nextR STPS diagSeq)
open Googology.Trans.BMS (AncL)

/-- The first entries in the list of first entries. -/
theorem xAt_eq_map (M : PS) (j : ℕ) : xAt M j = (M.map Prod.fst)[j]! := by
  rw [xAt_eq_entry, entry_zero']

theorem xAt_append_left {l₁ l₂ : PS} {j : ℕ} (h : j < l₁.length) :
    xAt (l₁ ++ l₂) j = xAt l₁ j := by
  rw [xAt_of_lt (by simp; omega), xAt_of_lt h, List.getElem_append_left h]

/-- **Parents are local**: the parent of a column only depends on the columns
up to it. -/
theorem par_append_left {l₁ l₂ : PS} {c : ℕ} (h : c < l₁.length) :
    par (l₁ ++ l₂) c = par l₁ c := by
  unfold par
  congr 1
  apply List.filter_congr
  intro j hj
  rw [List.mem_range] at hj
  rw [xAt_append_left h, xAt_append_left (by omega)]

/-- **The parent `j₀` is below every later column up to the last one.** -/
theorem ExpCase.x_lt {M : PS} {j0 d0 : ℕ} (h : ExpCase M j0 d0) :
    ∀ j, j0 < j → j ≤ Lng M - 1 → xAt M j0 < xAt M j := by
  have hhas := h.has
  have hj := h.j0_eq
  unfold hasParent at hhas
  unfold parent at hj
  set ps := parents M (idx1 M (Lng M - 1)) (Lng M - 1) with hps
  have hlen : ps.length = 1 := by simpa using hhas
  obtain ⟨a, ha⟩ : ∃ a, ps = [a] := List.length_eq_one_iff.mp hlen
  rw [ha] at hj
  simp only [List.headD_cons] at hj
  subst hj
  have hmem : a ∈ ps := by rw [ha]; exact List.mem_singleton_self a
  rw [hps, parents, List.mem_filter] at hmem
  have hanc : AncL (M.map Prod.fst) a (Lng M - 1) := by
    have hn := hmem.2
    unfold nextR at hn
    split at hn
    · exact Relation.TransGen.single ((nextrel0_iff M a _).mp hn).2
    · exact ((nextrel1_iff M a _).mp hn).2.2.1
  intro j h1 h2
  rw [xAt_eq_map, xAt_eq_map]
  exact AncL_gt hanc j h1 h2

/-- **The three cases of `oper`.** -/
theorem oper_cases (M : PS) (n : ℕ) :
    oper M n = M ∨ oper M n = M.dropLast ∨ ∃ j0 d0, ExpCase M j0 d0 := by
  by_cases h1 : Lng M - 1 = 0
  · left; simp [oper, h1]
  have h2 : ¬ Lng M ≤ 1 := by omega
  by_cases hz : entry M 0 (Lng M - 1) = 0 ∧ entry M 1 (Lng M - 1) = 0
  · right; left
    simp [oper, h1, hz, _root_.PSS.Pred, h2]
  by_cases hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true
  · right; right
    exact ⟨_, _, ⟨by omega, hz, hp, rfl, rfl⟩⟩
  · right; left
    have hz' : (entry M 0 (Lng M - 1) = 0 && entry M 1 (Lng M - 1) = 0) = false := by
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
      by_contra hc
      push Not at hc
      exact hz ⟨by simpa using hc.1, by simpa using hc.2⟩
    simp only [Bool.not_eq_true] at hp
    simp [oper, h1, hz', hp, _root_.PSS.Pred, h2]

theorem length_oper_copies {M : PS} {j0 d0 : ℕ} (h : ExpCase M j0 d0) (n : ℕ) :
    (oper M n).length = j0 + n * (Lng M - 1 - j0) := by
  have hj0 : j0 ≤ M.length := by have := h.j0_lt; simp [Lng] at this; omega
  rw [oper_eq_copies h, List.length_append, length_copies, List.length_take]
  omega

theorem xAt_oper_left {M : PS} {j0 d0 : ℕ} (h : ExpCase M j0 d0) (n : ℕ) {i : ℕ} (hi : i < j0) :
    xAt (oper M n) i = xAt M i := by
  have hj0 : j0 ≤ M.length := by have := h.j0_lt; simp [Lng] at this; omega
  rw [oper_eq_copies h, xAt_of_lt (by simp; omega), xAt_of_lt (by omega),
    List.getElem_append_left (by simp; omega)]
  simp

theorem xAt_oper_copy {M : PS} {j0 d0 : ℕ} (h : ExpCase M j0 d0) {k n : ℕ} (hk : k < n)
    {r : ℕ} (hr : r < Lng M - 1 - j0) :
    xAt (oper M n) (j0 + k * (Lng M - 1 - j0) + r) = xAt M (j0 + r) + k * d0 := by
  have hg := getElem?_oper_copy h hk hr
  rw [xAt_eq_entry M]
  unfold xAt
  rw [List.getD_eq_getElem?_getD, hg]
  rfl

/-! ## (I0) -/

theorem I0_diagSeq (u v : ℕ) :
    ∀ j, j + 1 < (diagSeq u v).length → xAt (diagSeq u v) (j + 1) ≤ xAt (diagSeq u v) j + 1 := by
  intro j hj
  rw [xAt_of_lt hj, xAt_of_lt (by omega)]
  simp [diagSeq]
  omega

theorem I0_dropLast {M : PS}
    (hM : ∀ j, j + 1 < M.length → xAt M (j + 1) ≤ xAt M j + 1) :
    ∀ j, j + 1 < M.dropLast.length → xAt M.dropLast (j + 1) ≤ xAt M.dropLast j + 1 := by
  intro j hj
  have hj' : j + 1 < M.length := by simp at hj; omega
  rw [xAt_of_lt hj, xAt_of_lt (by omega), List.getElem_dropLast, List.getElem_dropLast,
    ← xAt_of_lt hj', ← xAt_of_lt (by omega)]
  exact hM j hj'

theorem I0_oper {M : PS} (hM : ∀ j, j + 1 < M.length → xAt M (j + 1) ≤ xAt M j + 1) (n : ℕ) :
    ∀ j, j + 1 < (oper M n).length → xAt (oper M n) (j + 1) ≤ xAt (oper M n) j + 1 := by
  rcases oper_cases M n with h | h | ⟨j0, d0, h⟩
  · rw [h]; exact hM
  · rw [h]; exact I0_dropLast hM
  intro j hj
  have hj0 := h.j0_lt
  have hML : Lng M = M.length := rfl
  obtain ⟨L, hL⟩ : ∃ L, Lng M - 1 - j0 = L := ⟨_, rfl⟩
  have hLpos : 0 < L := by omega
  have hcopy : ∀ {k : ℕ}, k < n → ∀ {r : ℕ}, r < L →
      xAt (oper M n) (j0 + k * L + r) = xAt M (j0 + r) + k * d0 := by
    intro k hk r hr
    have e := xAt_oper_copy h hk (r := r) (by omega)
    rwa [hL] at e
  rw [length_oper_copies h, hL] at hj
  by_cases hjl : j + 1 < j0
  · rw [xAt_oper_left h n hjl, xAt_oper_left h n (by omega)]
    exact hM j (by omega)
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp at hj; omega
    · exact hn
  by_cases hje : j + 1 = j0
  · have e0 := hcopy hn (k := 0) (r := 0) hLpos
    simp only [zero_mul, add_zero] at e0
    rw [hje, e0, xAt_oper_left h n (by omega)]
    have := hM j (by omega)
    rwa [hje] at this
  -- `j ≥ j₀`: write `j = j₀ + k·L + r`
  obtain ⟨k, r, hr, hjkr⟩ : ∃ k r, r < L ∧ j = j0 + k * L + r :=
    ⟨(j - j0) / L, (j - j0) % L, Nat.mod_lt _ hLpos, by
      have := Nat.div_add_mod (j - j0) L
      rw [Nat.mul_comm] at this; omega⟩
  have hkn : k < n := by
    by_contra hkn
    push Not at hkn
    have : n * L ≤ k * L := Nat.mul_le_mul_right L hkn
    omega
  rw [hjkr, hcopy hkn hr]
  by_cases hr1 : r + 1 < L
  · rw [show j0 + k * L + r + 1 = j0 + k * L + (r + 1) by omega, hcopy hkn hr1]
    have := hM (j0 + r) (by omega)
    rw [show j0 + r + 1 = j0 + (r + 1) by omega] at this
    omega
  · have hk1 : k + 1 < n := by
      by_contra hk1
      push Not at hk1
      have : n * L ≤ (k + 1) * L := Nat.mul_le_mul_right L hk1
      rw [Nat.add_mul] at this
      omega
    have e := hcopy hk1 (r := 0) hLpos
    rw [show j0 + k * L + r + 1 = j0 + (k + 1) * L + 0 by rw [Nat.add_mul]; omega, e]
    simp only [add_zero]
    -- the step from one copy to the next: `x_{j₀} + d₀ ≤ x_{j₁-1} + 1`
    have hjunc : xAt M j0 + d0 ≤ xAt M (j0 + r) + 1 := by
      rw [← h.d0_eq]
      split
      · have hxl := h.x_lt (Lng M - 1) (by omega) le_rfl
        have hstep := hM (Lng M - 2) (by simp [Lng] at hj0 ⊢; omega)
        rw [show Lng M - 2 + 1 = Lng M - 1 by omega] at hstep
        rw [show j0 + r = Lng M - 2 by omega]
        rw [← xAt_eq_entry, ← xAt_eq_entry]
        simp only [Lng] at hxl hstep ⊢
        omega
      · simp only [add_zero]
        rcases Nat.eq_zero_or_pos r with hr0 | hr0
        · rw [hr0]; simp
        · have := h.x_lt (j0 + r) (by omega) (by omega)
          omega
    rw [Nat.add_mul, one_mul]
    omega

/-- **(I0) for standard sequences** (COMB Lemma 1). -/
theorem I0_of_stps {M : PS} (h : STPS M) :
    ∀ j, j + 1 < M.length → xAt M (j + 1) ≤ xAt M j + 1 := by
  induction h with
  | diag u v _ => exact I0_diagSeq u v
  | oper _ n _ ih => exact I0_oper ih n

end Googology.Trans.PSS.Forest
