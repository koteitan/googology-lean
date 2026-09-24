import Googology.Trans.DBMS.ThreeRowUpper

/-!
# The nested raise `t3n`

`ThreeRowUpper.lean` reduces the upper bound `rkL 2 (cgen 2 4) ≤ rkL 2 (bgen3 2)`
to `T3RankDesc`, through the map `t3` that raises column `1` from `(1,1,0)` to
`(1,1,1)`.  `ThreeRowUpperRefute.lean` shows that `t3 C` need not be a standard
form: the matrices reached from `(cgen 2 4)[v]` contain **inner** lifted blocks
`(a-1,0,0)(a,1,0)(a+1,2,1)`, copies of the block `(0,0,0)(1,1,0)(2,2,1)` at the
start, and `t3` raises only the first one.

This file raises all of them.  A column `i` is **raisable** (`Rz C i`) when it is
`(a,1,0)` and the next column is `(a+1,2,1)`; `t3n C` sets the row-`2` entry of
every raisable column to `1`.  At the start this is `t3`:

    t3n ((0,0,0)(1,1,0)(2,2,1)(3,3,1)⋯(v+2,v+2,1)) = trioGen (v + 2)   (t3n_lift_trioGen)

and the counterexample of `ThreeRowUpperRefute.lean` goes to a standard form:
`t3n (C₀[1]) = (0,0,0)(1,1,1)(2,2,1)(3,0,0)(4,1,1)(5,2,1)`.

**The reduction** (`rkL_cgen_two_four_eq_of_t3n`): if `t3n` lowers the rank with
every expansion on the reached matrices (`T3nRankDesc`), then
`rkL 2 (cgen 2 4) = rkL 2 (bgen3 2)`.  The proof is the one of
`rkL_cgen_two_four_eq_of` with `t3n` in place of `t3`.

Numerically (breadth-first from `lift 3 (trioGen v)`, `v ≤ 3`, depth `≤ 10`, at
most `14` columns, `6639` matrices, `N ≤ 2`): every `t3n C` is a standard form of
the trio fragment, `t3n (C[N]) < t3n C` in the dictionary order, and `t3n (C[N])`
is reached from `t3n C` by expansions.  On `28741` matrices (depth `12`, at most
`16` columns) raisability agrees with "`(a,1,0)` that has a row-`2` child".
-/

namespace Googology.Trans.DBMS

open Ordinal Order
open Googology.Trans.BMS
open Googology.Trans.BMS.TrioCofinal (trioGen TrioStdL)

/-! ### Parents depend only on the rows up to their own

(The same statements as in `ThreeRowUpperComm.lean`, repeated so that this file
depends only on `ThreeRowUpper.lean`.) -/

theorem ParR_congr_rows' (l l' : List (List Nat)) : ∀ k : Nat,
    (∀ i k' : Nat, k' ≤ k → (l[i]!)[k']! = (l'[i]!)[k']!) → ∀ j i, ParR l k j i ↔ ParR l' k j i := by
  intro k
  induction k with
  | zero =>
    intro h j i
    have h0 : ∀ i : Nat, (l[i]!)[0]! = (l'[i]!)[0]! := fun i => h i 0 le_rfl
    simp only [ParR, h0]
  | succ m ih =>
    intro h j i
    have e : ParR l m = ParR l' m := by
      funext a b; exact propext (ih (fun i k' hk => h i k' (by omega)) a b)
    have h1 : ∀ i : Nat, (l[i]!)[m + 1]! = (l'[i]!)[m + 1]! := fun i => h i (m + 1) le_rfl
    simp only [ParR, e, h1]

theorem parAtR_congr' {l l' : List (List Nat)} {k : Nat} (h : ∀ j i, ParR l k j i ↔ ParR l' k j i)
    (i : Nat) : parAtR l k i = parAtR l' k i := by
  apply Option.ext
  intro j
  rw [parAtR_eq_some, parAtR_eq_some]
  exact h j i

theorem get_one_of' {C : List (List Nat)} (h : C[1]? = some [1, 1, 0]) : C[1]! = [1, 1, 0] := by
  rw [getElem!_def, h]

/-! ### Raisable columns and the nested raise -/

/-- **Column `i` is raisable**: it is `(a,1,0)` and column `i + 1` is `(a+1,2,1)`. -/
def Rz (C : List (List Nat)) (i : Nat) : Prop :=
  i + 1 < C.length ∧ (C[i]!)[1]! = 1 ∧ (C[i]!)[2]! = 0 ∧
    (C[i + 1]!)[0]! = (C[i]!)[0]! + 1 ∧ (C[i + 1]!)[1]! = 2 ∧ (C[i + 1]!)[2]! = 1

instance (C : List (List Nat)) (i : Nat) : Decidable (Rz C i) := by
  unfold Rz; infer_instance

/-- **The nested raise**: every raisable column `(a,1,0)` becomes `(a,1,1)`. -/
def t3n (C : List (List Nat)) : List (List Nat) :=
  (List.range C.length).map (fun i => if Rz C i then [(C[i]!)[0]!, 1, 1] else C[i]!)

@[simp] theorem t3n_length (C : List (List Nat)) : (t3n C).length = C.length := by
  simp [t3n]

theorem t3n_get {C : List (List Nat)} {i : Nat} (hi : i < C.length) :
    (t3n C)[i]! = if Rz C i then [(C[i]!)[0]!, 1, 1] else C[i]! := by
  rw [t3n, getElem!_map_range _ _ hi]

theorem t3n_get_of_ge {C : List (List Nat)} {i : Nat} (hi : C.length ≤ i) :
    (t3n C)[i]! = [] := getElem!_neg _ i (by rw [t3n_length]; omega)

theorem Rz_lt {C : List (List Nat)} {i : Nat} (h : Rz C i) : i + 1 < C.length := h.1

/-- Rows `0` and `1` are not changed. -/
theorem t3n_entry_low (C : List (List Nat)) (i k : Nat) (hk : k ≤ 1) :
    ((t3n C)[i]!)[k]! = (C[i]!)[k]! := by
  by_cases hi : i < C.length
  · rw [t3n_get hi]
    split
    · rename_i h
      match k, hk with
      | 0, _ => rfl
      | 1, _ => exact h.2.1.symm
    · rfl
  · rw [t3n_get_of_ge (by omega), getElem!_neg C i hi]; rfl

/-- Row `2`: `1` at the raisable columns. -/
theorem t3n_entry_two (C : List (List Nat)) (i : Nat) :
    ((t3n C)[i]!)[2]! = if Rz C i then 1 else (C[i]!)[2]! := by
  by_cases hi : i < C.length
  · rw [t3n_get hi]
    split <;> rfl
  · rw [t3n_get_of_ge (by omega), getElem!_neg C i hi,
      if_neg (fun h => by have := h.1; omega)]
    rfl

theorem t3n_entry_two_ge (C : List (List Nat)) (i : Nat) :
    (C[i]!)[2]! ≤ ((t3n C)[i]!)[2]! := by
  rw [t3n_entry_two]
  split
  · rename_i h; rw [h.2.2.1]; omega
  · exact le_rfl

theorem t3n_get_of_not {C : List (List Nat)} {i : Nat} (h : ¬ Rz C i) : (t3n C)[i]! = C[i]! := by
  by_cases hi : i < C.length
  · rw [t3n_get hi, if_neg h]
  · rw [t3n_get_of_ge (by omega), getElem!_neg C i hi]; rfl

theorem valid_t3n {C : List (List Nat)} (hv : Valid 2 C) : Valid 2 (t3n C) := by
  intro v hv'
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv'
  have hi' : i < C.length := List.mem_range.mp hi
  split
  · rfl
  · exact hv _ (getElem!_mem C i hi')

theorem t3n_ne_nil {C : List (List Nat)} (h : C ≠ []) : t3n C ≠ [] := by
  intro e
  have := congrArg List.length e
  rw [t3n_length, List.length_nil] at this
  exact h (List.eq_nil_of_length_eq_zero this)

/-- Parents in rows `0` and `1` are not changed. -/
theorem ParR_t3n_low (C : List (List Nat)) (k : Nat) (hk : k ≤ 1) (j i : Nat) :
    ParR (t3n C) k j i ↔ ParR C k j i :=
  ParR_congr_rows' _ _ k (fun i k' hk' => t3n_entry_low C i k' (by omega)) j i

theorem ParR_t3n_low_eq (C : List (List Nat)) (k : Nat) (hk : k ≤ 1) :
    ParR (t3n C) k = ParR C k := by
  funext j i; exact propext (ParR_t3n_low C k hk j i)

theorem AncR_t3n_low (C : List (List Nat)) (k : Nat) (hk : k ≤ 1) (j i : Nat) :
    AncR (t3n C) k j i ↔ AncR C k j i := by
  rw [AncR, AncR, ParR_t3n_low_eq C k hk]

/-! ### When only column `1` is raisable, `t3n` is `t3` -/

theorem t3n_eq_set_one {C : List (List Nat)} (h1 : Rz C 1) (h1c : C[1]? = some [1, 1, 0])
    (hother : ∀ i, i ≠ 1 → ¬ Rz C i) : t3n C = C.set 1 [1, 1, 1] := by
  have hl : 1 < C.length := by have := h1.1; omega
  apply List.ext_getElem (by simp)
  intro i h1' h2'
  rw [List.getElem_set, ← getElem!_pos (t3n C) i h1']
  have hi : i < C.length := by simpa using h1'
  rw [t3n_get hi]
  by_cases hi1 : i = 1
  · subst hi1
    rw [if_pos h1, if_pos rfl, get_one_of' h1c]
    rfl
  · rw [if_neg (hother i hi1), if_neg (Ne.symm hi1), getElem!_pos C i hi]

theorem lift_trioGen_get (v : Nat) {i : Nat} (hi : i < v + 2) :
    (lift 3 (trioGen (v + 1)))[i + 1]! = [i + 1, i + 1, min i 1] := by
  rw [lift_get_succ 3 _ (by simp [trioGen]; omega), trioGen,
    getElem!_map_range _ _ (by omega)]
  rfl

/-- **At the start `t3n` is `t3`**, and gives a trio generator:
`t3n ((0,0,0)(1,1,0)(2,2,1)⋯(v+2,v+2,1)) = (0,0,0)(1,1,1)(2,2,1)⋯(v+2,v+2,1)`. -/
theorem t3n_lift_trioGen (v : Nat) : t3n (lift 3 (trioGen (v + 1))) = trioGen (v + 2) := by
  have hlen : (lift 3 (trioGen (v + 1))).length = v + 3 := by simp [trioGen]
  have h1c : (lift 3 (trioGen (v + 1)))[1]? = some [1, 1, 0] := by
    rw [lift_trioGen_succ]; rfl
  have hR1 : Rz (lift 3 (trioGen (v + 1))) 1 := by
    refine ⟨by omega, ?_⟩
    rw [lift_trioGen_get v (i := 0) (by omega), lift_trioGen_get v (i := 1) (by omega)]
    decide
  have hother : ∀ i, i ≠ 1 → ¬ Rz (lift 3 (trioGen (v + 1))) i := by
    intro i hi h
    have hr := h.2.1
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [lift_get0] at hr
      simp [zcol] at hr
    · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      have := h.1
      rw [lift_trioGen_get v (i := i') (by omega)] at hr
      simp at hr
      omega
  rw [t3n_eq_set_one hR1 h1c hother, ← t3_lift_trioGen v, t3,
    if_pos ⟨h1c, [2, 2, 1], by rw [lift_trioGen_succ]; simp, by decide⟩]

/-! ### The reduction -/

/-- `t3n` lowers the rank with every expansion, on the matrices reached from
`(cgen 2 4)[v]`. -/
def T3nRankDesc : Prop :=
  ∀ C, SReach C → C ≠ [] → ∀ N, rkL 2 (t3n (expandRL 3 N C)) < rkL 2 (t3n C)

theorem rkL_le_rkL_t3n_aux (h : T3nRankDesc) :
    ∀ M : AllLState 2, SReach M.1 → rkL 2 M.1 ≤ rkL 2 (t3n M.1) := by
  intro M
  induction M using WellFounded.induction (bmsAllL_wf 2) with
  | _ M ih =>
    intro hS
    by_cases hne : M.1 = []
    · rw [hne, rkL_nil]; exact zero_le
    · rw [rkL_step M.2 hne]
      refine Ordinal.iSup_le (fun N => succ_le_of_lt ?_)
      exact lt_of_le_of_lt (ih ((bmsAllL 2).step M N) (rel_of_ne M hne N) (hS.step N))
        (h _ hS hne N)

/-- **Under `T3nRankDesc`, `t3n` never lowers the rank** on the reached matrices. -/
theorem rkL_le_rkL_t3n (h : T3nRankDesc) {C : List (List Nat)} (hC : SReach C) :
    rkL 2 C ≤ rkL 2 (t3n C) :=
  rkL_le_rkL_t3n_aux h ⟨C, hC.valid⟩ hC

/-- **The upper bound at `n = 2`, under `T3nRankDesc`.** -/
theorem rkL_cgen_two_four_le_of_t3n (h : T3nRankDesc) : rkL 2 (cgen 2 4) ≤ rkL 2 (bgen3 2) := by
  rw [rkL_step (valid_cgen 2 4) (by simp [cgen])]
  refine Ordinal.iSup_le (fun N => succ_le_of_lt ?_)
  have h1 := rkL_le_rkL_t3n h (SReach.gen N)
  rw [expandRL_cgen_two_four, t3n_lift_trioGen] at h1
  rw [expandRL_cgen_two_four]
  exact lt_of_le_of_lt h1 (rkL_trioGen_lt_bgen3_two N)

/-- **Under `T3nRankDesc` the two ranks are equal**: the DBMS content
`(0,0,0)(1,1,0)(2,2,1)(3,3,2)` and the BMS matrix `(0,0,0)(1,1,1)(2,2,2)`. -/
theorem rkL_cgen_two_four_eq_of_t3n (h : T3nRankDesc) : rkL 2 (cgen 2 4) = rkL 2 (bgen3 2) :=
  le_antisymm (rkL_cgen_two_four_le_of_t3n h) (rkL_bgen3_le_cgen 2)

end Googology.Trans.DBMS

#print axioms Googology.Trans.DBMS.t3n_lift_trioGen
#print axioms Googology.Trans.DBMS.rkL_cgen_two_four_eq_of_t3n
