import Googology.Trans.BMS.PoR.PSS.SC.Basic

/-!
# Terms in `oper M n`

`proof/COMB.md` §8b (Lemmas 7 and 8) uses two facts about the terms of the
fundamental sequence `M[n] = oper M n`, in the case where `oper` copies the bad
part.  Write `j₁ = Lng M - 1` for the last column, `j₀` for its parent (in row
`i₁`), `L = j₁ - j₀` for the length of the bad part and `d₀` for the
increment of the first row.  Then

```
M[n] = M↾j₀ ++ B₀ ++ ⋯ ++ B_{n-1},   B_k = ((x_j + k·d₀, y_j))_{j₀ ≤ j < j₁}
```

* `term_oper_copy`: the column `j₀ + k·L + r` of `M[n]` (the column `j₀ + r`
  in the `k`-th copy) has the same term as the column `j₀ + r` of `M[n-k]`.
  The reason is that the tail of `M[n]` from that column is the tail of
  `M[n-k]` from `j₀ + r`, shifted up by `k·d₀` (`drop_oper_copy`).
* `term_oper_anc`: a column `a < j₀` that is a row-0 ancestor of `j₁` in `M`
  gets the whole tail of `M[n]` as its term.

`oper_eq_copies` states the shape of `oper M n` in this case (`ExpCase`).
-/

namespace Googology.Trans.PSS.Forest

open _root_.PSS (oper entry Lng idx1 hasParent parent parents nextR)

/-! ## The copies of the bad part -/

/-- The `k`-th copy `B_k` of the bad part `[j₀, j₁)`, shifted up by `k·d₀`. -/
def copyB (M : PS) (j0 j1 d0 k : ℕ) : PS :=
  (List.range' j0 (j1 - j0)).map (fun j => (entry M 0 j + k * d0, entry M 1 j))

/-- `B₀ ++ ⋯ ++ B_{n-1}`. -/
def copies (M : PS) (j0 j1 d0 n : ℕ) : PS :=
  (List.range n).flatMap (fun k => copyB M j0 j1 d0 k)

theorem length_copyB (M : PS) (j0 j1 d0 k : ℕ) : (copyB M j0 j1 d0 k).length = j1 - j0 := by
  simp [copyB]

theorem length_copies (M : PS) (j0 j1 d0 n : ℕ) :
    (copies M j0 j1 d0 n).length = n * (j1 - j0) := by
  induction n with
  | zero => simp [copies]
  | succ n ih =>
    rw [copies, List.range_succ, List.flatMap_append, List.length_append, ← copies, ih]
    simp [length_copyB, Nat.succ_mul]

theorem copyB_add (M : PS) (j0 j1 d0 k i : ℕ) :
    copyB M j0 j1 d0 (k + i) = shUp (k * d0) (copyB M j0 j1 d0 i) := by
  simp only [copyB, shUp, List.map_map]
  apply List.map_congr_left
  intro j _
  simp [Nat.add_mul]; omega

theorem copies_add (M : PS) (j0 j1 d0 k m : ℕ) :
    copies M j0 j1 d0 (k + m) = copies M j0 j1 d0 k ++ shUp (k * d0) (copies M j0 j1 d0 m) := by
  rw [copies, List.range_add, List.flatMap_append, ← copies]
  congr 1
  rw [List.flatMap_map, copies, shUp, List.map_flatMap]
  congr 1
  funext i
  rw [copyB_add]; rfl

theorem drop_shUp (c r : ℕ) (l : PS) : (shUp c l).drop r = shUp c (l.drop r) := by
  simp [shUp]

theorem drop_len_add (l₁ l₂ : PS) (i : ℕ) : (l₁ ++ l₂).drop (l₁.length + i) = l₂.drop i := by
  rw [List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append,
    Nat.add_sub_cancel_left]

/-- Dropping `k` whole copies and `r` more columns. -/
theorem drop_copies (M : PS) (j0 j1 d0 : ℕ) {k n : ℕ} (hk : k ≤ n) (r : ℕ) :
    (copies M j0 j1 d0 n).drop (k * (j1 - j0) + r)
      = shUp (k * d0) ((copies M j0 j1 d0 (n - k)).drop r) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [copies_add, ← length_copies M j0 j1 d0 k, drop_len_add, Nat.add_sub_cancel_left, drop_shUp]

/-- **The tail from a column of the `k`-th copy.**  For `k ≤ n`, the tail of
`G ++ B₀ ++ ⋯ ++ B_{n-1}` from `j₀ + k·L + r` is the tail of
`G ++ B₀ ++ ⋯ ++ B_{n-k-1}` from `j₀ + r`, shifted up by `k·d₀`. -/
theorem drop_take_copies (M : PS) {j0 j1 d0 k n : ℕ} (hj0 : j0 ≤ M.length) (hk : k ≤ n)
    (r : ℕ) :
    (M.take j0 ++ copies M j0 j1 d0 n).drop (j0 + k * (j1 - j0) + r)
      = shUp (k * d0) ((M.take j0 ++ copies M j0 j1 d0 (n - k)).drop (j0 + r)) := by
  have hlen : (M.take j0).length = j0 := by simp; omega
  rw [show j0 + k * (j1 - j0) + r = (M.take j0).length + (k * (j1 - j0) + r) by omega,
    show j0 + r = (M.take j0).length + r by omega, drop_len_add, drop_len_add,
    drop_copies M j0 j1 d0 hk r]

/-! ## The expansion case of `oper` -/

/-- The case of `oper` that copies the bad part: `M` has at least two
columns, the last column is not `(0,0)`, it has a parent `j₀` in row `i₁`, and
`d₀` is the increment of the first row. -/
structure ExpCase (M : PS) (j0 d0 : ℕ) : Prop where
  one_lt : 1 < Lng M
  not_zero : ¬ (entry M 0 (Lng M - 1) = 0 ∧ entry M 1 (Lng M - 1) = 0)
  has : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true
  j0_eq : parent M (idx1 M (Lng M - 1)) (Lng M - 1) = j0
  d0_eq : (if 0 < idx1 M (Lng M - 1) then entry M 0 (Lng M - 1) - entry M 0 j0 else 0) = d0

theorem idx1_le_one (M : PS) (j : ℕ) : idx1 M j ≤ 1 := by
  unfold idx1; split <;> omega

theorem nextR_lt {M : PS} {i a b : ℕ} (h : nextR M i a b = true) : a < b := by
  unfold nextR at h
  split at h
  · simp only [_root_.PSS.nextrel0, Bool.and_eq_true, decide_eq_true_eq] at h; exact h.1.1.2
  · simp only [_root_.PSS.nextrel1, Bool.and_eq_true, decide_eq_true_eq] at h; exact h.1.1.1.2

/-- The parent `j₀` lies before the last column. -/
theorem ExpCase.j0_lt {M : PS} {j0 d0 : ℕ} (h : ExpCase M j0 d0) : j0 < Lng M - 1 := by
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
  exact nextR_lt hmem.2

/-- **The shape of `oper M n` in the expansion case.** -/
theorem oper_eq_copies {M : PS} {j0 d0 : ℕ} (h : ExpCase M j0 d0) (n : ℕ) :
    oper M n = M.take j0 ++ copies M j0 (Lng M - 1) d0 n := by
  have h1 : Lng M - 1 ≠ 0 := by have := h.one_lt; omega
  have hz : (entry M 0 (Lng M - 1) = 0 && entry M 1 (Lng M - 1) = 0) = false := by
    have := h.not_zero
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
    by_contra hc
    push Not at hc
    exact this ⟨by simpa using hc.1, by simpa using hc.2⟩
  have hd1 : ¬ 1 < idx1 M (Lng M - 1) := by have := idx1_le_one M (Lng M - 1); omega
  unfold oper
  simp only [h1, ↓reduceIte, hz, Bool.false_eq_true, h.has, Bool.not_true, h.j0_eq, h.d0_eq,
    hd1, mul_zero, add_zero]
  rfl

/-! ## Terms in `oper M n` -/

/-- **A column of the `k`-th copy has the term of the corresponding column of
`M[n-k]`.**  For `k ≤ n`, the column `j₀ + k·L + r` of `M[n]` and the column
`j₀ + r` of `M[n-k]` have the same term (COMB §8b, Lemma 7 item 3′ and
Lemma 8). -/
theorem term_oper_copy {M : PS} {j0 d0 : ℕ} (h : ExpCase M j0 d0) {k n : ℕ} (hk : k ≤ n)
    (r : ℕ) :
    term (oper M n) (j0 + k * (Lng M - 1 - j0) + r) = term (oper M (n - k)) (j0 + r) := by
  have hj0 : j0 ≤ M.length := by have := h.j0_lt; simp [Lng] at this; omega
  unfold term
  rw [oper_eq_copies h, oper_eq_copies h, drop_take_copies M hj0 hk r, termOf_shUp]

/-- The first copy `B₀` is the bad part itself: for `1 ≤ m` and `r < L`, the
column `j₀ + r` of `M[m]` is the column `j₀ + r` of `M`. -/
theorem getElem?_oper_first {M : PS} {j0 d0 : ℕ} (h : ExpCase M j0 d0) {m : ℕ} (hm : 1 ≤ m)
    {r : ℕ} (hr : r < Lng M - 1 - j0) :
    (oper M m)[j0 + r]? = some (entry M 0 (j0 + r), entry M 1 (j0 + r)) := by
  have hj0 : j0 ≤ M.length := by have := h.j0_lt; simp [Lng] at this; omega
  have hlen : (M.take j0).length = j0 := by simp; omega
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [oper_eq_copies h, List.getElem?_append_right (by omega), hlen,
    show j0 + r - j0 = r by omega, show m' + 1 = 1 + m' by omega, copies_add,
    List.getElem?_append_left (by rw [length_copies]; omega)]
  simp [copies, copyB, hr]

/-- A column of the `k`-th copy, for `r < L`, is the copy of the column
`j₀ + r` of `M`: its entries are those of `M` with `x` raised by `k·d₀`. -/
theorem getElem?_oper_copy {M : PS} {j0 d0 : ℕ} (h : ExpCase M j0 d0) {k n : ℕ} (hk : k < n)
    {r : ℕ} (hr : r < Lng M - 1 - j0) :
    (oper M n)[j0 + k * (Lng M - 1 - j0) + r]?
      = some (entry M 0 (j0 + r) + k * d0, entry M 1 (j0 + r)) := by
  have hj0 : j0 ≤ M.length := by have := h.j0_lt; simp [Lng] at this; omega
  have key := congrArg List.head? (drop_take_copies M hj0 hk.le r (j1 := Lng M - 1) (d0 := d0))
  rw [← oper_eq_copies h, ← oper_eq_copies h, List.head?_drop, shUp, List.head?_map,
    List.head?_drop] at key
  rw [key, getElem?_oper_first h (by omega) hr]
  rfl

/-- **An ancestor of the last column gets the tail of `M[n]`.**  If `a < j₀`
and every column of `M` after `a`, up to the last one, is higher than `a`
(that is, `a` is a row-0 ancestor of the last column), then the term of `a`
in `M[n]` is the tail of `M[n]` from `a`, normalized. -/
theorem term_oper_anc {M : PS} {j0 d0 : ℕ} (h : ExpCase M j0 d0) {a : ℕ} (ha : a < j0)
    (hanc : ∀ j, a < j → j ≤ Lng M - 1 → xAt M a < xAt M j) (n : ℕ) :
    term (oper M n) a = sh (xAt M a) ((oper M n).drop a) := by
  have hj0 : j0 < M.length := by have := h.j0_lt; simp [Lng] at this; omega
  have haM : a < M.length := by omega
  have hat : a < (M.take j0).length := by simp; omega
  rw [term, oper_eq_copies h, List.drop_append_of_le_length hat.le,
    List.drop_eq_getElem_cons hat, List.cons_append, termOf_cons_of_forall]
  · congr 1; simp [xAt_of_lt haM]
  intro q hq
  rw [List.mem_append] at hq
  rcases hq with hq | hq
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hq
    simp only [List.length_drop, List.length_take] at hi
    simp only [List.getElem_drop, List.getElem_take]
    have := hanc (a + 1 + i) (by omega) (by simp [Lng]; omega)
    rwa [xAt_of_lt haM, xAt_of_lt (by omega)] at this
  · simp only [copies, copyB, List.mem_flatMap, List.mem_map, List.mem_range'_1] at hq
    obtain ⟨k, _, j, ⟨hj1, hj2⟩, rfl⟩ := hq
    have := hanc j (by omega) (by omega)
    rw [xAt_of_lt haM, xAt_eq_entry] at this
    simp only [List.getElem_take]; omega

end Googology.Trans.PSS.Forest
