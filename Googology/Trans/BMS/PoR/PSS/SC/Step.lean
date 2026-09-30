import Googology.Trans.BMS.PoR.PSS.SC.Pert
import Bijectivity.«07-oper-pred»

/-!
# One expansion step keeps (A), Sib and G\*

`proof/COMB.md` §8b, Lemmas 7 and 8 (and (I2) of Lemma 1): if `M` satisfies
(A), Sib or G\*, so does every `M[n] = oper M n`, `n ≥ 1`.

We treat the copying case `ExpCase M j₀ d₀` of `oper`.  Write `j₁ = Lng M - 1`
and `L = j₁ - j₀`.  Then `M[1] = M↾j₁`, and for `n ≥ 1`

```
M[n+1] = M↾j₁ ++ (M[n] from j₀ on, with x raised by d₀)      (getElem?_shift)
```

So the column `j₁ + t` of `M[n+1]` is the column `j₀ + t` of `M[n]`, raised by
`d₀`; it has the same term (`term_shift`).  The proof is by induction on `n`:

* the columns before `j₁`: `M[n+1]` lowers the last column of `M`
  (`ExpCase.pert`, `SC/Pert.lean`);
* the columns from `j₁` on: their parents are those of `M[n]` moved by
  `fIdx` (`par_shift`: an index `a < j₀` stays, an index `a ≥ j₀` moves to
  `a + L`), except the column `j₁` itself when `i₁ = 1`, whose parent is the
  parent of `j₁` in `M`.  The columns `[j₀, j₁)` of `M[n+1]` are ancestors of a
  column `j₁ + t` only when `i₁ = 1`, and then they have `y ≥ y_{j₀}`
  (`anc_mid`, `ExpCase.one`).

The main results are `ExpCase.condA_succ`, `ExpCase.sib_succ`,
`ExpCase.gstar_succ`, and `condA_oper`, `sib_oper`, `gstar_oper` for all three
cases of `oper`.
-/

namespace Googology.Trans.PSS.Forest

open _root_.PSS (oper entry Lng idx1 hasParent parent parents nextR Pred)
open Googology.Trans.BMS (AncL ParL1)
open Bijectivity (ltPS lePS)

variable {M : PS} {j0 d0 : ℕ}

/-! ## The parent `j₀` -/

theorem yAt_eq_getElem! (M : PS) (j : ℕ) : yAt M j = (M[j]!).2 := by
  rw [yAt_eq_entry, entry_one]

theorem ExpCase.nextR_true (h : ExpCase M j0 d0) :
    nextR M (idx1 M (Lng M - 1)) j0 (Lng M - 1) = true := by
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
  exact hmem.2

theorem ExpCase.anc (h : ExpCase M j0 d0) : Anc M j0 (Lng M - 1) := ⟨h.j0_lt, h.x_lt⟩

theorem idx1_cases (M : PS) : idx1 M (Lng M - 1) = 0 ∨ idx1 M (Lng M - 1) = 1 := by
  have := idx1_le_one M (Lng M - 1)
  omega

theorem ExpCase.d0_zero (h : ExpCase M j0 d0) (hi : idx1 M (Lng M - 1) = 0) : d0 = 0 := by
  have := h.d0_eq
  rw [hi] at this
  simpa using this.symm

/-- **The case `i₁ = 1`**: `j₀` is the nearest ancestor of `j₁` with a smaller
`y`, and `d₀ = x_{j₁} - x_{j₀}`. -/
theorem ExpCase.one (h : ExpCase M j0 d0) (hi : idx1 M (Lng M - 1) = 1) :
    xAt M j0 + d0 = xAt M (Lng M - 1) ∧ yAt M j0 < yAt M (Lng M - 1) ∧
      ∀ a, j0 < a → Anc M a (Lng M - 1) → yAt M (Lng M - 1) ≤ yAt M a := by
  have hanc := h.anc
  have hx := hanc.2 (Lng M - 1) hanc.1 le_rfl
  have hd := h.d0_eq
  rw [hi] at hd
  simp only [zero_lt_one, ↓reduceIte] at hd
  rw [← xAt_eq_entry, ← xAt_eq_entry] at hd
  have hn := h.nextR_true
  rw [hi] at hn
  simp only [nextR, one_ne_zero, ↓reduceIte] at hn
  obtain ⟨_, _, _, hy, hmin⟩ := (nextrel1_iff M j0 (Lng M - 1)).mp hn
  refine ⟨by omega, by rw [yAt_eq_getElem!, yAt_eq_getElem!]; exact hy, fun a ha hMa => ?_⟩
  rw [yAt_eq_getElem!, yAt_eq_getElem!]
  apply hmin a ha hMa.1
  rcases desc_of_gt (l := M.map Prod.fst) (p := a) (Lng M - 1) hMa.1.le
    (fun y h1 h2 => by rw [← xAt_eq_map, ← xAt_eq_map]; exact hMa.2 y h1 h2) with he | hA
  · have := hMa.1
    omega
  · exact hA

/-- The first column of the copy `B₁` is below the last column of `M`. -/
theorem ExpCase.plt (h : ExpCase M j0 d0) :
    PLt (xAt M j0 + d0, yAt M j0) (xAt M (Lng M - 1), yAt M (Lng M - 1)) := by
  have hx := h.anc.2 (Lng M - 1) h.anc.1 le_rfl
  unfold PLt
  simp only
  rcases idx1_cases M with hi | hi
  · rw [h.d0_zero hi]
    omega
  · have := h.one hi
    omega

/-! ## The shape of `M[n]` -/

theorem ExpCase.j1_lt_length (h : ExpCase M j0 d0) : Lng M - 1 < M.length := by
  have := h.one_lt
  simp only [Lng] at this ⊢
  omega

theorem ExpCase.L_pos (h : ExpCase M j0 d0) : 0 < Lng M - 1 - j0 := by
  have := h.j0_lt
  omega

theorem ExpCase.length_succ (h : ExpCase M j0 d0) (n : ℕ) :
    (oper M (n + 1)).length = (oper M n).length + (Lng M - 1 - j0) := by
  rw [length_oper_copies h, length_oper_copies h, Nat.add_mul, one_mul, Nat.add_assoc]

theorem ExpCase.j1_le_length (h : ExpCase M j0 d0) {n : ℕ} (hn : 1 ≤ n) :
    Lng M - 1 ≤ (oper M n).length := by
  have := h.j0_lt
  have : Lng M - 1 - j0 ≤ n * (Lng M - 1 - j0) := Nat.le_mul_of_pos_left _ hn
  rw [length_oper_copies h]
  omega

theorem ExpCase.length_one (h : ExpCase M j0 d0) : (oper M 1).length = Lng M - 1 := by
  have := h.j0_lt
  rw [length_oper_copies h]
  omega

theorem ExpCase.oper_succ (h : ExpCase M j0 d0) (n : ℕ) :
    oper M (n + 1) = oper M n ++ copyB M j0 (Lng M - 1) d0 n := by
  rw [oper_eq_copies h, oper_eq_copies h, copies_add, List.append_assoc]
  congr 2
  rw [show copies M j0 (Lng M - 1) d0 1 = copyB M j0 (Lng M - 1) d0 0 by simp [copies],
    ← copyB_add, Nat.add_zero]

theorem ExpCase.copyB_ne_nil (h : ExpCase M j0 d0) (n : ℕ) : copyB M j0 (Lng M - 1) d0 n ≠ [] := by
  rw [← List.length_pos_iff, length_copyB]
  exact h.L_pos

theorem ExpCase.take_oper (h : ExpCase M j0 d0) {m : ℕ} (hm : 1 ≤ m) :
    (oper M m).take (Lng M - 1) = M.take (Lng M - 1) := by
  rw [(Bijectivity.oper_take_pred h.one_lt m hm).2]
  have := h.one_lt
  simp only [Pred, show ¬ Lng M ≤ 1 by omega, ↓reduceIte, List.dropLast_eq_take]

theorem ExpCase.xAt_lt (h : ExpCase M j0 d0) {m : ℕ} (hm : 1 ≤ m) {j : ℕ} (hj : j < Lng M - 1) :
    xAt (oper M m) j = xAt M j := by
  rw [← xAt_take (M := oper M m) hj, h.take_oper hm, xAt_take hj]

theorem ExpCase.yAt_lt (h : ExpCase M j0 d0) {m : ℕ} (hm : 1 ≤ m) {j : ℕ} (hj : j < Lng M - 1) :
    yAt (oper M m) j = yAt M j := by
  rw [← yAt_take (M := oper M m) hj, h.take_oper hm, yAt_take hj]

/-- **The copy of `M[n]` inside `M[n+1]`.** -/
theorem ExpCase.getElem?_shift (h : ExpCase M j0 d0) (n t : ℕ) :
    (oper M (n + 1))[Lng M - 1 + t]? = ((oper M n)[j0 + t]?).map (fun q => (q.1 + d0, q.2)) := by
  have hj0 : j0 ≤ M.length := by have := h.j0_lt; simp [Lng] at this; omega
  have key := congrArg List.head?
    (drop_take_copies M hj0 (j1 := Lng M - 1) (d0 := d0) (k := 1) (n := n + 1) (by omega) t)
  rw [← oper_eq_copies h (n + 1), Nat.add_sub_cancel, ← oper_eq_copies h n, List.head?_drop,
    shUp, List.head?_map, List.head?_drop] at key
  simp only [one_mul] at key
  rwa [show j0 + (Lng M - 1 - j0) + t = Lng M - 1 + t by have := h.j0_lt; omega] at key

theorem ExpCase.xAt_shift (h : ExpCase M j0 d0) (n t : ℕ) (ht : j0 + t < (oper M n).length) :
    xAt (oper M (n + 1)) (Lng M - 1 + t) = xAt (oper M n) (j0 + t) + d0 := by
  unfold xAt
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, h.getElem?_shift,
    List.getElem?_eq_getElem ht]
  rfl

theorem ExpCase.yAt_shift (h : ExpCase M j0 d0) (n t : ℕ) :
    yAt (oper M (n + 1)) (Lng M - 1 + t) = yAt (oper M n) (j0 + t) := by
  unfold yAt
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, h.getElem?_shift]
  cases (oper M n)[j0 + t]? <;> rfl

theorem ExpCase.term_shift (h : ExpCase M j0 d0) (n t : ℕ) :
    term (oper M (n + 1)) (Lng M - 1 + t) = term (oper M n) (j0 + t) := by
  have := term_oper_copy h (k := 1) (n := n + 1) (by omega) t
  rwa [one_mul, show j0 + (Lng M - 1 - j0) + t = Lng M - 1 + t by have := h.j0_lt; omega,
    Nat.add_sub_cancel] at this

theorem ExpCase.xAt_j1 (h : ExpCase M j0 d0) {n : ℕ} (hn : 1 ≤ n) :
    xAt (oper M (n + 1)) (Lng M - 1) = xAt M j0 + d0 := by
  have hl := h.j1_le_length hn
  have := h.xAt_shift n 0 (by have := h.j0_lt; omega)
  simp only [Nat.add_zero] at this
  rw [this, h.xAt_lt hn h.j0_lt]

theorem ExpCase.yAt_j1 (h : ExpCase M j0 d0) {n : ℕ} (hn : 1 ≤ n) :
    yAt (oper M (n + 1)) (Lng M - 1) = yAt M j0 := by
  have := h.yAt_shift n 0
  simp only [Nat.add_zero] at this
  rw [this, h.yAt_lt hn h.j0_lt]

/-- A column from `j₀` on is the column `j₀ + r` of the `k`-th copy. -/
theorem ExpCase.decomp (h : ExpCase M j0 d0) {m j : ℕ} (hj0 : j0 ≤ j)
    (hj : j < (oper M m).length) :
    ∃ k r, k < m ∧ r < Lng M - 1 - j0 ∧ j = j0 + k * (Lng M - 1 - j0) + r := by
  have hL := h.L_pos
  rw [length_oper_copies h] at hj
  refine ⟨(j - j0) / (Lng M - 1 - j0), (j - j0) % (Lng M - 1 - j0), ?_, Nat.mod_lt _ hL, ?_⟩
  · by_contra hk
    push Not at hk
    have h1 := Nat.mul_le_mul_right (Lng M - 1 - j0) hk
    have h2 := Nat.div_mul_le_self (j - j0) (Lng M - 1 - j0)
    omega
  · have := Nat.div_add_mod (j - j0) (Lng M - 1 - j0)
    rw [Nat.mul_comm] at this
    omega

/-- Every column of `M[m]` from `j₀` on is at least as high as `j₀`. -/
theorem ExpCase.x_ge (h : ExpCase M j0 d0) (m : ℕ) {j : ℕ} (hj0 : j0 ≤ j)
    (hj : j < (oper M m).length) : xAt M j0 ≤ xAt (oper M m) j := by
  obtain ⟨k, r, hk, hr, rfl⟩ := h.decomp hj0 hj
  rw [xAt_oper_copy h hk hr]
  rcases Nat.eq_zero_or_pos r with hr0 | hr0
  · rw [hr0, Nat.add_zero]
    omega
  · have := h.x_lt (j0 + r) (by omega) (by omega)
    omega

/-- When `i₁ = 1`, every column of `M[m]` after `j₀` is higher than `j₀`. -/
theorem ExpCase.x_gt (h : ExpCase M j0 d0) (hi : idx1 M (Lng M - 1) = 1) (m : ℕ) {j : ℕ}
    (hj0 : j0 < j) (hj : j < (oper M m).length) : xAt M j0 < xAt (oper M m) j := by
  obtain ⟨k, r, hk, hr, rfl⟩ := h.decomp hj0.le hj
  rw [xAt_oper_copy h hk hr]
  rcases Nat.eq_zero_or_pos r with hr0 | hr0
  · rw [hr0, Nat.add_zero]
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with hk0 | hk0
      · rw [hk0, hr0] at hj0
        simp at hj0
      · exact hk0
    have hd := h.one hi
    have hx := h.anc.2 (Lng M - 1) h.anc.1 le_rfl
    have : d0 ≤ k * d0 := Nat.le_mul_of_pos_left d0 hk1
    omega
  · have := h.x_lt (j0 + r) (by omega) (by omega)
    omega

/-! ## Ancestors in `M[n+1]` -/

/-- Ancestors inside the copy of `M[n]`. -/
theorem ExpCase.anc_shift (h : ExpCase M j0 d0) (n a t : ℕ) :
    Anc (oper M (n + 1)) (Lng M - 1 + a) (Lng M - 1 + t) ↔ Anc (oper M n) (j0 + a) (j0 + t) := by
  have hlen := h.length_succ n
  have hj := h.j0_lt
  constructor
  · intro hA
    have hb := hA.lt_length
    have hat := hA.1
    refine ⟨by omega, fun j h1 h2 => ?_⟩
    have := hA.2 (Lng M - 1 + (j - j0)) (by omega) (by omega)
    rw [h.xAt_shift n a (by omega), h.xAt_shift n (j - j0) (by omega),
      show j0 + (j - j0) = j by omega] at this
    omega
  · intro hA
    have hb := hA.lt_length
    have hat := hA.1
    refine ⟨by omega, fun j h1 h2 => ?_⟩
    obtain ⟨j', rfl⟩ : ∃ j', j = Lng M - 1 + j' := ⟨j - (Lng M - 1), by omega⟩
    have := hA.2 (j0 + j') (by omega) (by omega)
    rw [h.xAt_shift n a (by omega), h.xAt_shift n j' (by omega)]
    omega

/-- Ancestors before `j₀` of a column from `j₀` on: the ancestors of `j₀` in `M`. -/
theorem ExpCase.anc_low (h : ExpCase M j0 d0) {m : ℕ} (hm : 1 ≤ m) {a b : ℕ} (ha : a < j0)
    (hb : j0 ≤ b) (hbm : b < (oper M m).length) : Anc (oper M m) a b ↔ Anc M a j0 := by
  have hj := h.j0_lt
  have hx : ∀ j ≤ j0, xAt (oper M m) j = xAt M j := fun j hj' => h.xAt_lt hm (by omega)
  constructor
  · intro hA
    exact (Anc_congr hx).mp (hA.of_le ha hb)
  · intro hA
    refine ⟨by omega, fun j h1 h2 => ?_⟩
    rw [hx a ha.le]
    rcases Nat.lt_or_ge j0 j with hj' | hj'
    · exact lt_of_lt_of_le (hA.2 j0 ha le_rfl) (h.x_ge m hj'.le (by omega))
    · rw [hx j hj']
      exact hA.2 j h1 hj'

/-- An ancestor in `[j₀, j₁)` of a column from `j₁` on occurs only when `i₁ = 1`,
and then it is an ancestor of `j₁` in `M`. -/
theorem ExpCase.anc_mid (h : ExpCase M j0 d0) {n : ℕ} (hn : 1 ≤ n) {a t : ℕ} (ha0 : j0 ≤ a)
    (ha1 : a < Lng M - 1) (hA : Anc (oper M (n + 1)) a (Lng M - 1 + t)) :
    idx1 M (Lng M - 1) = 1 ∧ Anc M a (Lng M - 1) := by
  have hA' := hA.of_le ha1 (by omega)
  have hx1 := hA'.2 (Lng M - 1) ha1 le_rfl
  rw [h.xAt_lt (by omega) ha1, h.xAt_j1 hn] at hx1
  have hxa : xAt M j0 ≤ xAt M a := by
    rcases Nat.eq_or_lt_of_le ha0 with rfl | ha0'
    · exact le_rfl
    · exact (h.x_lt a ha0' ha1.le).le
  rcases idx1_cases M with hi | hi
  · rw [h.d0_zero hi] at hx1
    omega
  · refine ⟨hi, (Anc_congr ?_).mp hA'⟩
    intro j hj
    rcases Nat.lt_or_ge j (Lng M - 1) with hj' | hj'
    · exact h.xAt_lt (by omega) hj'
    · rw [show j = Lng M - 1 by omega, h.xAt_j1 hn, (h.one hi).1]

/-- When `i₁ = 1`, `j₀` is an ancestor of every later column of `M[m]`. -/
theorem ExpCase.anc_j0 (h : ExpCase M j0 d0) (hi : idx1 M (Lng M - 1) = 1) {m t : ℕ}
    (hm : 1 ≤ m) (ht : 0 < t) (htm : j0 + t < (oper M m).length) :
    Anc (oper M m) j0 (j0 + t) :=
  ⟨by omega, fun j h1 h2 => by
    rw [h.xAt_lt hm h.j0_lt]
    exact h.x_gt hi m h1 (by omega)⟩

/-- When `i₁ = 1`, the columns up to `j₁` of `M[n+1]` have the first entries of `M`. -/
theorem ExpCase.x_agree_j1 (h : ExpCase M j0 d0) {n : ℕ} (hn : 1 ≤ n)
    (hi : idx1 M (Lng M - 1) = 1) : ∀ j ≤ Lng M - 1, xAt (oper M (n + 1)) j = xAt M j := by
  intro j hj
  rcases Nat.lt_or_ge j (Lng M - 1) with hj' | hj'
  · exact h.xAt_lt (by omega) hj'
  · rw [show j = Lng M - 1 by omega, h.xAt_j1 hn, (h.one hi).1]

/-! ## Moving indices from `M[n]` to `M[n+1]` -/

/-- An index `a < j₀` stays, an index `a ≥ j₀` moves by `L`. -/
def fIdx (j0 L a : ℕ) : ℕ := if a < j0 then a else a + L

theorem fIdx_lt {j0 L a : ℕ} (h : a < j0) : fIdx j0 L a = a := by simp [fIdx, h]

theorem fIdx_ge {j0 L a : ℕ} (h : j0 ≤ a) : fIdx j0 L a = a + L := by
  simp [fIdx, show ¬ a < j0 by omega]

theorem fIdx_le {j0 L a b : ℕ} (h : a ≤ b) : fIdx j0 L a ≤ fIdx j0 L b := by
  unfold fIdx
  split <;> split <;> omega

theorem fIdx_lt_fIdx {j0 L a b : ℕ} (h : a < b) : fIdx j0 L a < fIdx j0 L b := by
  unfold fIdx
  split <;> split <;> omega

theorem fIdx_injective {j0 L : ℕ} : Function.Injective (fIdx j0 L) := by
  intro a b hab
  rcases Nat.lt_trichotomy a b with h | h | h
  · have := fIdx_lt_fIdx (j0 := j0) (L := L) h
    omega
  · exact h
  · have := fIdx_lt_fIdx (j0 := j0) (L := L) h
    omega

theorem ExpCase.anc_f (h : ExpCase M j0 d0) {n t : ℕ} (hn : 1 ≤ n)
    (ht : j0 + t < (oper M n).length) (a : ℕ) :
    Anc (oper M n) a (j0 + t) ↔
      Anc (oper M (n + 1)) (fIdx j0 (Lng M - 1 - j0) a) (Lng M - 1 + t) := by
  have hj := h.j0_lt
  have hlen := h.length_succ n
  by_cases ha : a < j0
  · rw [fIdx_lt ha, h.anc_low hn ha (by omega) ht,
      h.anc_low (by omega) ha (by omega) (by omega)]
  · rw [fIdx_ge (by omega), show a + (Lng M - 1 - j0) = Lng M - 1 + (a - j0) by omega,
      h.anc_shift n (a - j0) t, show j0 + (a - j0) = a by omega]

theorem ExpCase.y_f (h : ExpCase M j0 d0) {n : ℕ} (hn : 1 ≤ n) {a : ℕ}
    (_ha : a < (oper M n).length) :
    yAt (oper M (n + 1)) (fIdx j0 (Lng M - 1 - j0) a) = yAt (oper M n) a := by
  have hj := h.j0_lt
  by_cases ha0 : a < j0
  · rw [fIdx_lt ha0, h.yAt_lt (by omega) (by omega), h.yAt_lt hn (by omega)]
  · rw [fIdx_ge (by omega), show a + (Lng M - 1 - j0) = Lng M - 1 + (a - j0) by omega,
      h.yAt_shift, show j0 + (a - j0) = a by omega]

/-- **Parents from `j₁` on**: the parent of `j₁ + t` in `M[n+1]` is the parent of
`j₀ + t` in `M[n]`, moved by `fIdx`, unless `i₁ = 1` and `t = 0`. -/
theorem ExpCase.par_shift (h : ExpCase M j0 d0) {n t : ℕ} (hn : 1 ≤ n)
    (hc : idx1 M (Lng M - 1) = 0 ∨ 0 < t) (ht : j0 + t < (oper M n).length) :
    par (oper M (n + 1)) (Lng M - 1 + t) =
      (par (oper M n) (j0 + t)).map (fIdx j0 (Lng M - 1 - j0)) := by
  have hj := h.j0_lt
  have hmid : ∀ a, j0 ≤ a → a < Lng M - 1 → Anc (oper M (n + 1)) a (Lng M - 1 + t) →
      ∃ q, par (oper M n) (j0 + t) = some q ∧ j0 ≤ q := by
    intro a h0 h1 hA
    obtain ⟨hi, -⟩ := h.anc_mid hn h0 h1 hA
    have ht0 : 0 < t := by
      rcases hc with hc | hc
      · rw [hi] at hc
        cases hc
      · exact hc
    have hA0 := h.anc_j0 hi hn ht0 ht
    obtain ⟨q, hq⟩ := par_isSome_of_anc hA0
    exact ⟨q, hq, le_par_of_anc hq hA0⟩
  have hback : ∀ a, Lng M - 1 ≤ a →
      fIdx j0 (Lng M - 1 - j0) (a - (Lng M - 1 - j0)) = a := by
    intro a ha
    rw [fIdx_ge (by omega)]
    omega
  cases hp : par (oper M n) (j0 + t) with
  | none =>
    simp only [Option.map_none]
    rw [par_eq_none_iff]
    intro a hA
    have hnone := par_eq_none_iff.mp hp
    rcases Nat.lt_or_ge a j0 with ha | ha
    · exact hnone a ((h.anc_f hn ht a).mpr (by rwa [fIdx_lt ha]))
    rcases Nat.lt_or_ge a (Lng M - 1) with ha1 | ha1
    · obtain ⟨q, hq, -⟩ := hmid a ha ha1 hA
      rw [hp] at hq
      cases hq
    · exact hnone _ ((h.anc_f hn ht _).mpr (by rwa [hback a ha1]))
  | some p =>
    simp only [Option.map_some]
    rw [par_eq_some_iff]
    obtain ⟨hpA, hmax⟩ := par_eq_some_iff.mp hp
    refine ⟨(h.anc_f hn ht p).mp hpA, fun a hA => ?_⟩
    rcases Nat.lt_or_ge a j0 with ha | ha
    · have := hmax a ((h.anc_f hn ht a).mpr (by rwa [fIdx_lt ha]))
      rw [← fIdx_lt (L := Lng M - 1 - j0) ha]
      exact fIdx_le this
    rcases Nat.lt_or_ge a (Lng M - 1) with ha1 | ha1
    · obtain ⟨q, hq, hq0⟩ := hmid a ha ha1 hA
      rw [hp] at hq
      cases hq
      rw [fIdx_ge hq0]
      omega
    · have := hmax _ ((h.anc_f hn ht _).mpr (by rwa [hback a ha1]))
      rw [← hback a ha1]
      exact fIdx_le this

theorem ExpCase.par_j1 (h : ExpCase M j0 d0) {n : ℕ} (hn : 1 ≤ n)
    (hi : idx1 M (Lng M - 1) = 1) : par (oper M (n + 1)) (Lng M - 1) = par M (Lng M - 1) :=
  par_congr (h.x_agree_j1 hn hi)

/-! ## `M[n+1]` lowers the last column of `M` -/

theorem ExpCase.pert (h : ExpCase M j0 d0) {n : ℕ} (hn : 1 ≤ n) :
    Pert M (oper M (n + 1)) (Lng M - 1) where
  len := by have := h.one_lt; simp [Lng] at this ⊢; omega
  take := h.take_oper (by omega)
  last := fun _ => by rw [h.xAt_j1 hn, h.yAt_j1 hn]; exact h.plt

theorem ExpCase.pert_one (h : ExpCase M j0 d0) : Pert M (oper M 1) (Lng M - 1) where
  len := by have := h.one_lt; simp [Lng] at this ⊢; omega
  take := h.take_oper le_rfl
  last := fun hl => by rw [h.length_one] at hl; omega

/-! ## Terms -/

/-- The term of the last column is a single column. -/
theorem term_last {M : PS} (hM : M ≠ []) : term M (M.length - 1) = [(0, yAt M (M.length - 1))] := by
  have hl := List.length_pos_iff.mpr hM
  rw [term_eq_of_end (e := M.length) (by omega) le_rfl (fun j h1 h2 => by omega)
    (fun h => by omega), List.take_length, List.drop_eq_getElem_cons (by omega),
    List.drop_eq_nil_of_le (by omega)]
  simp [sh, xAt_of_lt (show M.length - 1 < M.length by omega),
    yAt_of_lt (show M.length - 1 < M.length by omega)]

/-- A column below which every later column is higher: its term is the tail. -/
theorem term_eq_drop {M : PS} {u : ℕ} (hu : u < M.length)
    (h : ∀ j, u < j → j < M.length → xAt M u < xAt M j) :
    term M u = sh (xAt M u) (M.drop u) := by
  rw [term_eq_of_end hu le_rfl h (fun h => by omega), List.take_length]

/-! ## (A) -/

theorem ExpCase.condA_succ (h : ExpCase M j0 d0) {n : ℕ} (hn : 1 ≤ n) (hA : CondA M)
    (hN : CondA (oper M n)) : CondA (oper M (n + 1)) := by
  intro c hc p _ hpar
  have hP := h.pert hn
  have hj := h.j0_lt
  have hlen := h.length_succ n
  by_cases hcj : c < Lng M - 1
  · exact condA_pert hP hA c hcj p hpar
  obtain ⟨t, rfl⟩ : ∃ t, c = Lng M - 1 + t := ⟨c - (Lng M - 1), by omega⟩
  have ht : j0 + t < (oper M n).length := by omega
  by_cases hcase : idx1 M (Lng M - 1) = 0 ∨ 0 < t
  · rw [h.par_shift hn hcase ht] at hpar
    obtain ⟨q, hq, hqp⟩ := Option.map_eq_some_iff.mp hpar
    subst hqp
    have hqt := par_lt hq
    have := hN (j0 + t) ht q (by omega) hq
    rw [h.yAt_shift, h.y_f hn (by omega)]
    exact this
  · have hi : idx1 M (Lng M - 1) = 1 := by
      rcases idx1_cases M with hi | hi
      · exact absurd (Or.inl hi) hcase
      · exact hi
    have ht0 : t = 0 := by
      by_contra ht0
      exact hcase (Or.inr (by omega))
    subst ht0
    simp only [Nat.add_zero] at hpar ⊢
    rw [h.par_j1 hn hi] at hpar
    have hpj := par_lt hpar
    have hj1 := h.j1_lt_length
    have h1 := hA (Lng M - 1) hj1 p (by omega) hpar
    have h2 := (h.one hi).2.1
    rw [h.yAt_j1 hn, h.yAt_lt (by omega) hpj]
    omega

/-! ## Sib -/

theorem ExpCase.sib_succ (h : ExpCase M j0 d0) {n : ℕ} (hn : 1 ≤ n) (hS : Sib M)
    (hN : Sib (oper M n)) : Sib (oper M (n + 1)) := by
  intro c hc c' hc' hcc' hpar
  have hP := h.pert hn
  have hj := h.j0_lt
  have hlen := h.length_succ n
  have hj1n := h.j1_le_length hn
  have hL := h.L_pos
  by_cases hc'j : c' < Lng M - 1
  · exact sib_pert hP hS c c' hcc' hc'j hpar
  obtain ⟨t', rfl⟩ : ∃ t', c' = Lng M - 1 + t' := ⟨c' - (Lng M - 1), by omega⟩
  have ht' : j0 + t' < (oper M n).length := by omega
  rw [h.term_shift]
  by_cases hcj : Lng M - 1 ≤ c
  · -- both from `j₁` on
    obtain ⟨t, rfl⟩ : ∃ t, c = Lng M - 1 + t := ⟨c - (Lng M - 1), by omega⟩
    have ht : j0 + t < (oper M n).length := by omega
    rw [h.term_shift]
    by_cases hcase : idx1 M (Lng M - 1) = 0 ∨ 0 < t
    · rw [h.par_shift hn hcase ht, h.par_shift hn (Or.inr (by omega)) ht'] at hpar
      exact hN (j0 + t) ht (j0 + t') ht' (by omega) (Option.map_injective fIdx_injective hpar)
    · exfalso
      have hi : idx1 M (Lng M - 1) = 1 := by
        rcases idx1_cases M with hi | hi
        · exact absurd (Or.inl hi) hcase
        · exact hi
      have ht0 : t = 0 := by
        by_contra ht0
        exact hcase (Or.inr (by omega))
      subst ht0
      rw [h.par_shift hn (Or.inr (by omega)) ht'] at hpar
      have hA0 := h.anc_j0 hi hn (show 0 < t' by omega) ht'
      obtain ⟨q, hq⟩ := par_isSome_of_anc hA0
      have hq0 := le_par_of_anc hq hA0
      rw [hq, Option.map_some, Nat.add_zero] at hpar
      have := par_lt hpar
      rw [fIdx_ge hq0] at this
      omega
  · -- `c` before `j₁`, `c'` from `j₁` on
    push Not at hcj
    rw [hP.par_eq hcj] at hpar
    rcases idx1_cases M with hi | hi
    · -- `i₁ = 0`: the copies of `j₀` are siblings of `j₀`
      rw [h.par_shift hn (Or.inl hi) ht'] at hpar
      have hpN : par (oper M n) c = par M c := par_congr (fun j hj' => h.xAt_lt hn (by omega))
      have hq : par (oper M n) (j0 + t') = par M c := by
        cases hq : par (oper M n) (j0 + t') with
        | none =>
          rw [hq] at hpar
          simpa using hpar.symm
        | some q =>
          rw [hq, Option.map_some] at hpar
          have hqc := par_lt hpar
          by_cases hq0 : q < j0
          · rw [fIdx_lt hq0] at hpar
            exact hpar.symm
          · rw [fIdx_ge (by omega)] at hqc
            omega
      have hcj0 : c ≤ j0 := by
        by_contra hcj0
        have hanc : Anc M j0 c := h.anc.of_le (by omega) (by omega)
        obtain ⟨p, hp⟩ := par_isSome_of_anc hanc
        have hp0 := le_par_of_anc hp hanc
        rw [hq, hp, Option.map_some, Option.some.injEq, fIdx_ge hp0] at hpar
        omega
      have hS' : lePS (term (oper M n) (j0 + t')) (term (oper M n) c) := by
        rcases Nat.lt_or_ge c (j0 + t') with hlt | hge
        · exact hN c (by omega) (j0 + t') ht' hlt (by rw [hpN, hq])
        · rw [show c = j0 + t' by omega]
          exact Or.inl rfl
      have hterm : term (oper M (n + 1)) c = term (oper M n) c := by
        rw [h.oper_succ n]
        rcases Nat.lt_or_ge c (j0 + t') with hlt | hge
        · have hna : ¬ Anc (oper M n) c (j0 + t') := by
            intro ha
            obtain ⟨p, hp⟩ := par_isSome_of_anc ha
            have h1 := le_par_of_anc hp ha
            rw [hq, ← hpN] at hp
            have := par_lt hp
            omega
          obtain ⟨e, he1, he2, he3, -⟩ := Pert.exists_end hlt hna
          exact term_append_eq he1 (by omega) (fun _ => by
            rwa [xAt_append_left (j := e) (by omega), xAt_append_left (j := c) (by omega)])
        · have hc0 : c = j0 := by omega
          rw [hc0]
          refine term_append_eq (e := Lng M - 1) hj hj1n (fun _ => ?_)
          rw [← h.oper_succ n, h.xAt_j1 hn, h.d0_zero hi, h.xAt_lt (by omega) hj]
          omega
      rw [hterm]
      exact hS'
    · -- `i₁ = 1`: only `j₁` itself can be a sibling of an earlier column
      by_cases ht0 : t' = 0
      · subst ht0
        simp only [Nat.add_zero] at hpar ⊢
        rw [h.par_j1 hn hi] at hpar
        have hj1 := h.j1_lt_length
        have hS' := hS c (by omega) (Lng M - 1) hj1 hcj hpar
        have hna : ¬ Anc M c (Lng M - 1) := by
          intro ha
          obtain ⟨p, hp⟩ := par_isSome_of_anc ha
          have h1 := le_par_of_anc hp ha
          rw [← hpar] at hp
          have := par_lt hp
          omega
        rw [hP.term_of_not_anc hcj hna]
        have hM : M ≠ [] := by
          intro h'
          simp [h'] at hj1
        have hl : term M (Lng M - 1) = [(0, yAt M (Lng M - 1))] := term_last hM
        rw [hl] at hS'
        obtain ⟨r, hr⟩ := term_head (M := oper M n) (u := j0) (by omega)
        obtain ⟨r', hr'⟩ := term_head (M := M) (u := c) (by omega)
        rw [hr'] at hS'
        have hy := le_of_lePS_single hS'
        rw [hr, hr']
        right
        apply ltPS_head
        rw [h.yAt_lt hn hj]
        have := (h.one hi).2.1
        omega
      · exfalso
        rw [h.par_shift hn (Or.inr (by omega)) ht'] at hpar
        have hA0 := h.anc_j0 hi hn (show 0 < t' by omega) ht'
        obtain ⟨q, hq⟩ := par_isSome_of_anc hA0
        have hq0 := le_par_of_anc hq hA0
        rw [hq, Option.map_some, fIdx_ge hq0] at hpar
        have := par_lt hpar
        omega

/-! ## G\* -/

theorem ExpCase.gstar_succ (h : ExpCase M j0 d0) {n : ℕ} (hn : 1 ≤ n) (hG : Gstar M)
    (hN : Gstar (oper M n)) : Gstar (oper M (n + 1)) := by
  intro u hu hdesc v _ hvOf
  have hP := h.pert hn
  have hj := h.j0_lt
  have hlen := h.length_succ n
  have hj1n := h.j1_le_length hn
  have hL := h.L_pos
  by_cases huj : u < Lng M - 1
  · exact gstar_pert hP hG u huj hdesc v hvOf
  obtain ⟨t, rfl⟩ : ∃ t, u = Lng M - 1 + t := ⟨u - (Lng M - 1), by omega⟩
  have ht : j0 + t < (oper M n).length := by omega
  rw [h.term_shift]
  by_cases hcase : idx1 M (Lng M - 1) = 0 ∨ 0 < t
  · rw [descending_iff, h.par_shift hn hcase ht] at hdesc
    obtain ⟨p, hp, hy⟩ := hdesc
    obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp hp
    have hqt := par_lt hq
    have hdescN : Descending (oper M n) (j0 + t) :=
      descending_iff.mpr ⟨q, hq, by rwa [h.yAt_shift, h.y_f hn (by omega)] at hy⟩
    obtain ⟨hvA, hvy, hvmax⟩ := vOf_eq_some_iff.mp hvOf
    -- `v(u)` is not in `[j₀, j₁)`
    have hvmid : ¬ (j0 ≤ v ∧ v < Lng M - 1) := by
      rintro ⟨h0, h1⟩
      obtain ⟨hi, hMa⟩ := h.anc_mid hn h0 h1 hvA
      have ht0 : 0 < t := by
        rcases hcase with hc | hc
        · rw [hi] at hc
          cases hc
        · exact hc
      have hj1A : Anc (oper M (n + 1)) (Lng M - 1) (Lng M - 1 + t) := by
        have := (h.anc_shift n 0 t).mpr (by simpa using h.anc_j0 hi hn ht0 ht)
        simpa using this
      have hlt := hvmax (Lng M - 1) hj1A h1
      rw [h.yAt_j1 hn] at hlt
      have hyv : yAt M j0 ≤ yAt M v := by
        rcases Nat.eq_or_lt_of_le h0 with h0' | h0'
        · rw [h0']
        · have := (h.one hi).2.2 v h0' hMa
          have := (h.one hi).2.1
          omega
      rw [h.yAt_lt (by omega) h1] at hvy
      omega
    have hvlen := hvA.1
    obtain ⟨v', hv'N, hfv⟩ : ∃ v', v' < (oper M n).length ∧ fIdx j0 (Lng M - 1 - j0) v' = v := by
      by_cases hv0 : v < j0
      · exact ⟨v, by omega, fIdx_lt hv0⟩
      · refine ⟨v - (Lng M - 1 - j0), by omega, ?_⟩
        rw [fIdx_ge (by omega)]
        omega
    subst hfv
    have hvOfN : vOf (oper M n) (j0 + t) = some v' := by
      rw [vOf_eq_some_iff]
      refine ⟨(h.anc_f hn ht v').mpr hvA, ?_, fun a ha hva => ?_⟩
      · rw [← h.y_f hn hv'N, ← h.yAt_shift]
        exact hvy
      · have := hvmax _ ((h.anc_f hn ht a).mp ha) (fIdx_lt_fIdx hva)
        rwa [h.yAt_shift, h.y_f hn (by have := ha.1; omega)] at this
    have hlt := hN (j0 + t) ht hdescN v' hv'N hvOfN
    apply ltPS_of_ltPS_of_lePS hlt
    by_cases hv0 : v' < j0
    · rw [fIdx_lt hv0, h.oper_succ n]
      exact lePS_of_prefix (term_prefix _ hv'N)
    · rw [fIdx_ge (by omega), show v' + (Lng M - 1 - j0) = Lng M - 1 + (v' - j0) by omega,
        h.term_shift, show j0 + (v' - j0) = v' by omega]
      exact Or.inl rfl
  · -- `i₁ = 1` and `u = j₁`: then `v(u) = j₀`
    have hi : idx1 M (Lng M - 1) = 1 := by
      rcases idx1_cases M with hi | hi
      · exact absurd (Or.inl hi) hcase
      · exact hi
    have ht0 : t = 0 := by
      by_contra ht0
      exact hcase (Or.inr (by omega))
    subst ht0
    simp only [Nat.add_zero] at hvOf ⊢
    have hxa := h.x_agree_j1 hn hi
    have hvj0 : vOf (oper M (n + 1)) (Lng M - 1) = some j0 := by
      rw [vOf_eq_some_iff]
      refine ⟨(Anc_congr hxa).mpr h.anc, by rw [h.yAt_j1 hn, h.yAt_lt (by omega) hj],
        fun a ha hja => ?_⟩
      have hMa := (Anc_congr hxa).mp ha
      rw [h.yAt_j1 hn, h.yAt_lt (by omega) ha.1]
      have := (h.one hi).2.2 a hja hMa
      have := (h.one hi).2.1
      omega
    rw [hvj0, Option.some.injEq] at hvOf
    subst hvOf
    have hN0 : j0 < (oper M n).length := by omega
    rw [term_eq_drop hN0 (fun j h1 h2 => by rw [h.xAt_lt hn hj]; exact h.x_gt hi n h1 h2),
      term_eq_drop (by omega)
        (fun j h1 h2 => by rw [h.xAt_lt (by omega) hj]; exact h.x_gt hi (n + 1) h1 h2),
      h.oper_succ n, List.drop_append_of_le_length hN0.le, sh_append, xAt_append_left hN0]
    apply ltPS_append_right
    rw [← List.length_pos_iff, length_sh, length_copyB]
    exact hL

/-! ## All `n ≥ 1` -/

theorem ExpCase.condA_oper (h : ExpCase M j0 d0) (hA : CondA M) :
    ∀ n, 1 ≤ n → CondA (oper M n)
  | 0, hn => absurd hn (by omega)
  | 1, _ => condA_of_pert h.pert_one h.length_one hA
  | n + 2, _ => h.condA_succ (by omega) hA (ExpCase.condA_oper h hA (n + 1) (by omega))

theorem ExpCase.sib_oper (h : ExpCase M j0 d0) (hS : Sib M) :
    ∀ n, 1 ≤ n → Sib (oper M n)
  | 0, hn => absurd hn (by omega)
  | 1, _ => sib_of_pert h.pert_one h.length_one hS
  | n + 2, _ => h.sib_succ (by omega) hS (ExpCase.sib_oper h hS (n + 1) (by omega))

theorem ExpCase.gstar_oper (h : ExpCase M j0 d0) (hG : Gstar M) :
    ∀ n, 1 ≤ n → Gstar (oper M n)
  | 0, hn => absurd hn (by omega)
  | 1, _ => gstar_of_pert h.pert_one h.length_one hG
  | n + 2, _ => h.gstar_succ (by omega) hG (ExpCase.gstar_oper h hG (n + 1) (by omega))

theorem condA_oper {M : PS} (hA : CondA M) (n : ℕ) (hn : 1 ≤ n) : CondA (oper M n) := by
  rcases oper_cases M n with h | h | ⟨j0, d0, h⟩
  · rw [h]; exact hA
  · rw [h]; exact condA_dropLast hA
  · exact h.condA_oper hA n hn

theorem sib_oper {M : PS} (hS : Sib M) (n : ℕ) (hn : 1 ≤ n) : Sib (oper M n) := by
  rcases oper_cases M n with h | h | ⟨j0, d0, h⟩
  · rw [h]; exact hS
  · rw [h]; exact sib_dropLast hS
  · exact h.sib_oper hS n hn

theorem gstar_oper {M : PS} (hG : Gstar M) (n : ℕ) (hn : 1 ≤ n) : Gstar (oper M n) := by
  rcases oper_cases M n with h | h | ⟨j0, d0, h⟩
  · rw [h]; exact hG
  · rw [h]; exact gstar_dropLast hG
  · exact h.gstar_oper hG n hn

/-! ## Diagonal sequences -/

open _root_.PSS (diagSeq STPS)

theorem xAt_diagSeq {u v j : ℕ} (hj : j < (diagSeq u v).length) : xAt (diagSeq u v) j = u + j := by
  rw [xAt_of_lt hj]
  simp [diagSeq]

theorem yAt_diagSeq {u v j : ℕ} (hj : j < (diagSeq u v).length) : yAt (diagSeq u v) j = u + j := by
  rw [yAt_of_lt hj]
  simp [diagSeq]

theorem par_diagSeq {u v j : ℕ} (hj : j < (diagSeq u v).length) (hj0 : 0 < j) :
    par (diagSeq u v) j = some (j - 1) :=
  par_eq_some_iff.mpr ⟨⟨by omega, fun i h1 h2 => by
    rw [xAt_diagSeq (by omega), xAt_diagSeq (by omega)]
    omega⟩, fun a ha => by have := ha.1; omega⟩

theorem par_diagSeq_zero (u v : ℕ) : par (diagSeq u v) 0 = none :=
  par_eq_none_iff.mpr (fun a ha => by have := ha.1; omega)

theorem condA_diagSeq (u v : ℕ) : CondA (diagSeq u v) := by
  intro c hc p _ hp
  rcases Nat.eq_zero_or_pos c with rfl | hc0
  · rw [par_diagSeq_zero] at hp
    cases hp
  · rw [par_diagSeq hc hc0, Option.some.injEq] at hp
    subst hp
    rw [yAt_diagSeq hc, yAt_diagSeq (by omega)]
    omega

theorem sib_diagSeq (u v : ℕ) : Sib (diagSeq u v) := by
  intro c hc c' hc' hcc' hpar
  exfalso
  rw [par_diagSeq hc' (by omega)] at hpar
  rcases Nat.eq_zero_or_pos c with rfl | hc0
  · rw [par_diagSeq_zero] at hpar
    cases hpar
  · rw [par_diagSeq hc hc0, Option.some.injEq] at hpar
    omega

theorem gstar_diagSeq (u v : ℕ) : Gstar (diagSeq u v) := by
  intro w hw hdesc
  exfalso
  obtain ⟨p, hp, hy⟩ := descending_iff.mp hdesc
  rcases Nat.eq_zero_or_pos w with rfl | hw0
  · rw [par_diagSeq_zero] at hp
    cases hp
  · rw [par_diagSeq hw hw0, Option.some.injEq] at hp
    subst hp
    rw [yAt_diagSeq hw, yAt_diagSeq (by omega)] at hy
    omega

/-! ## Standard sequences -/

/-- **(A) for standard sequences** (COMB Lemma 1, (I2)). -/
theorem condA_of_stps {M : PS} (h : STPS M) : CondA M := by
  induction h with
  | diag u v _ => exact condA_diagSeq u v
  | oper _ n hn ih => exact condA_oper ih n hn

/-- **Sib for standard sequences** (COMB Lemma 7). -/
theorem sib_of_stps {M : PS} (h : STPS M) : Sib M := by
  induction h with
  | diag u v _ => exact sib_diagSeq u v
  | oper _ n hn ih => exact sib_oper ih n hn

/-- **G\* for standard sequences** (COMB Lemma 8). -/
theorem gstar_of_stps {M : PS} (h : STPS M) : Gstar M := by
  induction h with
  | diag u v _ => exact gstar_diagSeq u v
  | oper _ n hn ih => exact gstar_oper ih n hn

end Googology.Trans.PSS.Forest
