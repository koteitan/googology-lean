import Googology.Trans.DBMS.ThreeRowLower
import Googology.Trans.DBMS.LexReachThree

/-!
# Three-row DBMS against three-row BMS at `n = 2`: the upper bound, reduced

`ThreeRowLower.lean` proves `rkL 2 (bgen3 n) ≤ rkL 2 (cgen 2 (n + 2))` for
every `n`.  This file works on the other half at `n = 2`,

    rkL 2 (cgen 2 4) ≤ rkL 2 (bgen3 2),

that is `(0,0,0)(1,1,0)(2,2,1)(3,3,2)` against `(0,0,0)(1,1,1)(2,2,2)`.
It proves everything except one rank statement, stated as the open
proposition `T3RankDesc`.  (The stronger `T3Std` would give it, but `T3Std`
is false: see below.)

**The map.**  `t3 C` raises the row-`2` entry of column `1` from `0` to `1`
when column `1` is `(1,1,0)` and some row-`2` entry of `C` is positive
(`T3Cond`), and leaves `C` alone otherwise.  On the matrices reached from
`(cgen 2 4)[v] = lift 3 (trioGen (v + 1))` (`SReach`) this condition is,
numerically, the same as "column `1` has a row-`2` child".  At the start
(`t3_lift_trioGen`)

    t3 ((0,0,0)(1,1,0)(2,2,1)⋯(v+2,v+2,1)) = (0,0,0)(1,1,1)(2,2,1)⋯(v+2,v+2,1)
                                        = trioGen (v + 2) = (bgen3 2)[v + 1].

**What is proved.**

* `t3_expand_lt`: `t3 (C[N]) < t3 C` in the dictionary order, for every rooted
  three-row `C ≠ []` (so for every member of `SReach`).  The two lists agree
  in front of the last column of `C`, raising column `1` keeps the order when
  both are raised, and `C[N]` has a positive row-`2` entry only if `C` has one
  before its last column (`expandRL_row2_from`).
* `rkL_lt_of_trio`: on the trio fragment `TrioStdL` the rank is strictly
  monotone in the dictionary order.  This is `trio_cofinal` (ported from
  koteitan/trio) plus induction on the rank.
* `rkL_le_rkL_t3`: if `T3RankDesc` holds (`rkL 2 (t3 (C[N])) < rkL 2 (t3 C)`
  on `SReach`), then `rkL 2 C ≤ rkL 2 (t3 C)` on `SReach`.
* `rkL_cgen_two_four_le_of`, `rkL_cgen_two_four_eq_of`: under `T3RankDesc`,
  `rkL 2 (cgen 2 4) ≤ rkL 2 (bgen3 2)`, and with `rkL_bgen3_le_cgen` the two
  ranks are equal.
* `t3RankDesc_of_t3Std`: `T3Std` (every `t3 C` with `C ∈ SReach` lies in the
  trio fragment) implies `T3RankDesc`, by `t3_expand_lt` and `rkL_lt_of_trio`.

**What is not proved.**  `T3RankDesc`.  `T3Std` would give it, but **`T3Std`
is false** (`ThreeRowUpperRefute.lean`, `not_t3Std`): `C₀ = (0,0,0)(1,1,0)(2,2,1)(3,1,0)`
is in `SReach`, and `t3 (C₀[1]) = (0,0,0)(1,1,1)(2,2,1)(3,0,0)(4,1,0)(5,2,1)` is
not in the trio fragment.  Its rank is still below `rkL 2 (t3 C₀)`
(`t3RankDesc_C₀`), because its expansions are those of the standard
`(0,0,0)(1,1,1)(2,2,1)(3,0,0)(4,1,1)`.  The inner blocks such as
`(3,0,0)(4,1,0)(5,2,1)` are lifted content blocks again, and `t3` does not raise
them.  So the rank comparison in `T3RankDesc` has to hold for non-standard
matrices, where the dictionary order says nothing about the rank.

Numerically (scripts outside the library, breadth-first from `lift 3 (trioGen v)`,
`v ≤ 3`, depth `≤ 10`, `N ≤ 2`, at most 14 columns, 6639 states): `t3 C` has an
explicit expansion path from a trio generator for all but 44 states, and
`t3 (C[N]) < t3 C` in the dictionary order always (as `t3_expand_lt` proves).
-/

namespace Googology.Trans.DBMS

open Ordinal Order
open Googology.Trans.BMS
open Googology.Trans.BMS.TrioCofinal (trioGen TrioStdL trio_cofinal expandRL_stair2)

/-! ### The map `t3` -/

/-- Column `1` is `(1,1,0)` and some row-`2` entry is positive. -/
def T3Cond (C : List (List Nat)) : Prop := C[1]? = some [1, 1, 0] ∧ ∃ v ∈ C, 0 < v[2]!

instance (C : List (List Nat)) : Decidable (T3Cond C) := by
  unfold T3Cond; infer_instance

/-- **Raise column `1` from `(1,1,0)` to `(1,1,1)`** when `T3Cond` holds. -/
def t3 (C : List (List Nat)) : List (List Nat) := if T3Cond C then C.set 1 [1, 1, 1] else C

/-- The matrices reached from the expansions `(cgen 2 4)[v] = lift 3 (trioGen (v + 1))`
of the content generator `(0,0,0)(1,1,0)(2,2,1)(3,3,2)`. -/
inductive SReach : List (List Nat) → Prop
  | gen (v : Nat) : SReach (expandRL 3 v (cgen 2 4))
  | step {C : List (List Nat)} (N : Nat) : SReach C → SReach (expandRL 3 N C)

theorem SReach.valid {C : List (List Nat)} (h : SReach C) : Valid 2 C := by
  induction h with
  | gen v => exact valid_expandRL (valid_cgen 2 4) v
  | step N _ ih => exact valid_expandRL ih N

theorem SReach.rooted {C : List (List Nat)} (h : SReach C) : Rooted C := by
  induction h with
  | gen v => exact rooted_expandRL 3 v (rooted_cgen 2 4)
  | step N _ ih => exact rooted_expandRL 3 N ih

/-! ### The start -/

theorem map_range_succ_front {α : Type} (f : Nat → α) (n : Nat) :
    (List.range (n + 1)).map f = f 0 :: (List.range n).map (fun i => f (i + 1)) := by
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]; rfl

theorem lift_trioGen_succ (v : Nat) : lift 3 (trioGen (v + 1)) =
    [0, 0, 0] :: [1, 1, 0] :: [2, 2, 1] :: (List.range v).map (fun i => [i + 3, i + 3, 1]) := by
  rw [lift, trioGen, List.map_map, map_range_succ_front, map_range_succ_front]
  simp only [Function.comp, List.cons.injEq]
  refine ⟨rfl, rfl, rfl, List.map_congr_left (fun i _ => ?_)⟩
  simp only [up01]
  show [i + 1 + 1 + 1, i + 1 + 1 + 1, min (i + 1 + 1) 1] = _
  simp

theorem trioGen_succ_succ (v : Nat) : trioGen (v + 2) =
    [0, 0, 0] :: [1, 1, 1] :: [2, 2, 1] :: (List.range v).map (fun i => [i + 3, i + 3, 1]) := by
  rw [trioGen, map_range_succ_front, map_range_succ_front, map_range_succ_front]
  refine congrArg (List.cons _) (congrArg (List.cons _) (congrArg (List.cons _)
    (List.map_congr_left (fun i _ => ?_))))
  simp

/-- **`t3` takes the start to a trio generator**:
`t3 ((0,0,0)(1,1,0)(2,2,1)⋯(v+2,v+2,1)) = (0,0,0)(1,1,1)(2,2,1)⋯(v+2,v+2,1)`. -/
theorem t3_lift_trioGen (v : Nat) : t3 (lift 3 (trioGen (v + 1))) = trioGen (v + 2) := by
  rw [lift_trioGen_succ, trioGen_succ_succ, t3, if_pos ⟨rfl, [2, 2, 1], by simp, by decide⟩]
  rfl

/-! ### Lists in the dictionary order -/

theorem lt_set_of_lt : ∀ (l : List (List Nat)) (i : Nat) (a b : List Nat), l[i]? = some a →
    a < b → l < l.set i b
  | [], i, a, b, h, _ => by simp at h
  | x :: l, 0, a, b, h, hab => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    exact List.cons_lt_cons_iff.mpr (Or.inl hab)
  | x :: l, i + 1, a, b, h, hab =>
    List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, lt_set_of_lt l i a b (by simpa using h) hab⟩)

theorem set_lt_set : ∀ (x y : List (List Nat)) (i : Nat) (a b : List Nat), x[i]? = some a →
    y[i]? = some a → x < y → x.set i b < y.set i b
  | [], _, _, _, _, h, _, _ => by simp at h
  | _ :: _, [], _, _, _, _, h, _ => by simp at h
  | u :: x, w :: y, 0, a, b, hx, hy, hlt => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hx hy
    subst hx hy
    rcases List.cons_lt_cons_iff.mp hlt with h | ⟨_, h⟩
    · exact absurd h (lt_irrefl _)
    · exact List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, h⟩)
  | u :: x, w :: y, i + 1, a, b, hx, hy, hlt => by
    simp only [List.set_cons_succ]
    rcases List.cons_lt_cons_iff.mp hlt with h | ⟨he, h⟩
    · exact List.cons_lt_cons_iff.mpr (Or.inl h)
    · exact List.cons_lt_cons_iff.mpr
        (Or.inr ⟨he, set_lt_set x y i a b (by simpa using hx) (by simpa using hy) h⟩)

theorem le_t3 (C : List (List Nat)) : C ≤ t3 C := by
  rw [t3]
  split
  · rename_i h
    exact le_of_lt (lt_set_of_lt C 1 _ _ h.1 (by decide))
  · exact le_rfl

/-! ### What an expansion keeps -/

theorem expandRL_eq_dropLast_append (N : Nat) {l : List (List Nat)} (hv : Valid 2 l) :
    ∃ Z, expandRL 3 N l = l.dropLast ++ Z := by
  cases N with
  | zero => exact ⟨[], by rw [expandRL_zero 3 l hv, List.append_nil]⟩
  | succ N =>
    cases hb : badRootR 3 l with
    | none => exact ⟨[], by simp [expandRL, hb]⟩
    | some p =>
      obtain ⟨Z, _, hZ⟩ := expandRL_succ_eq_dropLast_append 3 N l hv hb
      exact ⟨Z, hZ⟩

/-- **Every row-`2` entry of an expansion is `0` or a row-`2` entry of a column
before the last.** -/
theorem expandRL_row2_from (N : Nat) (l : List (List Nat)) (i : Nat) :
    ((expandRL 3 N l)[i]!)[2]! = 0 ∨
      ∃ j, j + 1 < l.length ∧ ((expandRL 3 N l)[i]!)[2]! = (l[j]!)[2]! := by
  cases hb : badRootR 3 l with
  | none =>
    rw [expandRL, hb]
    dsimp only
    rw [getElem!_dropLast']
    split
    · rename_i h
      exact Or.inr ⟨i, by omega, rfl⟩
    · exact Or.inl rfl
  | some p =>
    have hp : p + 1 < l.length := badRootR_lt hb
    have hs : 0 < l.length - 1 - p := by omega
    have hm : m0L 3 l < 3 := m0L_lt (by norm_num) l
    rw [expandRL, hb]
    dsimp only
    by_cases hip : i < p
    · rw [getElem!_append_left _ _ (by simpa using hip), getElem!_map_range _ _ hip]
      exact Or.inr ⟨i, by omega, rfl⟩
    · obtain ⟨t, rfl⟩ : ∃ t, i = p + t := ⟨i - p, by omega⟩
      have hlenG : ((List.range p).map (fun i => l[i]!)).length = p := by simp
      have key : ∀ (G C : List (List Nat)), G.length = p → (G ++ C)[p + t]! = C[t]! := by
        intro G C h; rw [← h]; exact getElem!_append_right G C t
      rw [key _ _ hlenG]
      by_cases ht : t < (N + 1) * (l.length - 1 - p)
      · rw [getElem!_map_range _ _ ht, getElem!_map_range_nat, if_pos (by norm_num)]
        have hj : p + t % (l.length - 1 - p) + 1 < l.length := by
          have := Nat.mod_lt t hs; omega
        refine Or.inr ⟨_, hj, ?_⟩
        rw [if_neg (by simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]; intro h; omega)]
      · rw [getElem!_neg _ t (by simpa using ht)]
        exact Or.inl rfl

/-- If an expansion has a positive row-`2` entry, a column before the last has
one. -/
theorem exists_row2_pos_of_expandRL {N : Nat} {l : List (List Nat)} {v : List Nat}
    (hv : v ∈ expandRL 3 N l) (h : 0 < v[2]!) :
    ∃ j, j + 1 < l.length ∧ 0 < (l[j]!)[2]! := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hv
  rw [← getElem!_pos (expandRL 3 N l) i hi] at h
  rcases expandRL_row2_from N l i with h0 | ⟨j, hj, he⟩
  · omega
  · exact ⟨j, hj, by omega⟩

/-! ### `t3` goes down with every expansion -/

/-- **`t3 (C[N]) < t3 C`** in the dictionary order, for rooted three-row `C ≠ []`. -/
theorem t3_expand_lt {C : List (List Nat)} (hv : Valid 2 C) (hR : Rooted C) (hne : C ≠ [])
    (N : Nat) : t3 (expandRL 3 N C) < t3 C := by
  have hlt : expandRL 3 N C < C := expandRL_lt_self 3 N hv hne
  by_cases hD : T3Cond (expandRL 3 N C)
  · obtain ⟨v, hvm, hv2⟩ := hD.2
    obtain ⟨j, hj, hj2⟩ := exists_row2_pos_of_expandRL hvm hv2
    have hj0 : j ≠ 0 := by
      rintro rfl
      have := hR.1 2
      omega
    obtain ⟨Z, hZ⟩ := expandRL_eq_dropLast_append N hv
    have hC1 : (expandRL 3 N C)[1]? = C[1]? := by
      rw [hZ, List.getElem?_append_left (by simp; omega), List.getElem?_dropLast,
        if_pos (by omega)]
    have hCc : T3Cond C :=
      ⟨hC1 ▸ hD.1, C[j]!, getElem!_mem C j (by omega), hj2⟩
    rw [t3, if_pos hD, t3, if_pos hCc]
    exact set_lt_set _ _ 1 _ _ hD.1 hCc.1 hlt
  · rw [t3, if_neg hD]
    exact lt_of_lt_of_le hlt (le_t3 C)

/-! ### The rank on the trio fragment -/

theorem valid_trioStdL {a : List (List Nat)} (h : TrioStdL a) : Valid 2 a := by
  induction h with
  | gen v =>
    intro c hc
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc
    rfl
  | step n _ ih => exact valid_expandRL ih n

theorem rkL_lt_of_trio_aux (o : Ordinal.{0}) : ∀ a, TrioStdL a → rkL 2 a = o →
    ∀ b, TrioStdL b → b < a → rkL 2 b < rkL 2 a := by
  induction o using WellFoundedLT.induction with
  | _ o ih =>
  intro a ha ho b hb hlt
  have hne : a ≠ [] := by
    rintro rfl
    exact List.not_lt_nil _ hlt
  obtain ⟨k, hk⟩ := trio_cofinal ha hb hlt
  have hstep := rkL_lt (valid_trioStdL ha) hne k
  rcases hk with rfl | hk
  · exact hstep
  · exact lt_trans (ih _ (ho ▸ hstep) _ (TrioStdL.step k ha) rfl b hb hk) hstep

/-- **On the trio fragment the rank is strictly monotone in the dictionary
order.** -/
theorem rkL_lt_of_trio {a b : List (List Nat)} (ha : TrioStdL a) (hb : TrioStdL b)
    (h : b < a) : rkL 2 b < rkL 2 a :=
  rkL_lt_of_trio_aux _ a ha rfl b hb h

/-! ### The reduction -/

/-- Every `t3 C` with `C ∈ SReach` is in the trio fragment.  **False**:
see `not_t3Std` in `ThreeRowUpperRefute.lean`. -/
def T3Std : Prop := ∀ C, SReach C → TrioStdL (t3 C)

/-- **Open.**  `t3` lowers the rank with every expansion, on `SReach`. -/
def T3RankDesc : Prop :=
  ∀ C, SReach C → C ≠ [] → ∀ N, rkL 2 (t3 (expandRL 3 N C)) < rkL 2 (t3 C)

theorem t3RankDesc_of_t3Std (h : T3Std) : T3RankDesc := fun C hC hne N =>
  rkL_lt_of_trio (h C hC) (h _ (hC.step N)) (t3_expand_lt hC.valid hC.rooted hne N)

theorem rkL_le_rkL_t3_aux (h : T3RankDesc) :
    ∀ M : AllLState 2, SReach M.1 → rkL 2 M.1 ≤ rkL 2 (t3 M.1) := by
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

/-- **Under `T3RankDesc`, `t3` never lowers the rank** on `SReach`. -/
theorem rkL_le_rkL_t3 (h : T3RankDesc) {C : List (List Nat)} (hC : SReach C) :
    rkL 2 C ≤ rkL 2 (t3 C) :=
  rkL_le_rkL_t3_aux h ⟨C, hC.valid⟩ hC

theorem bgen3_two : bgen3 2 = [[0, 0, 0], [1, 1, 1], [2, 2, 2]] := rfl

/-- `(bgen3 2)[N + 1] = trioGen (N + 2)`, below `bgen3 2`. -/
theorem rkL_trioGen_lt_bgen3_two (N : Nat) : rkL 2 (trioGen (N + 2)) < rkL 2 (bgen3 2) := by
  have he := expandRL_stair2 (N + 1)
  rw [show N + 1 + 1 = N + 2 from rfl] at he
  rw [← he, bgen3_two]
  exact rkL_lt (by rw [← bgen3_two]; exact valid_bgen3 2) (by simp) (N + 1)

/-- **The upper bound at `n = 2`, under `T3RankDesc`.** -/
theorem rkL_cgen_two_four_le_of (h : T3RankDesc) : rkL 2 (cgen 2 4) ≤ rkL 2 (bgen3 2) := by
  rw [rkL_step (valid_cgen 2 4) (by simp [cgen])]
  refine Ordinal.iSup_le (fun N => succ_le_of_lt ?_)
  have h1 := rkL_le_rkL_t3 h (SReach.gen N)
  rw [expandRL_cgen_two_four, t3_lift_trioGen] at h1
  rw [expandRL_cgen_two_four]
  exact lt_of_le_of_lt h1 (rkL_trioGen_lt_bgen3_two N)

/-- **Under `T3RankDesc` the two ranks are equal**: the DBMS content
`(0,0,0)(1,1,0)(2,2,1)(3,3,2)` and the BMS matrix `(0,0,0)(1,1,1)(2,2,2)`. -/
theorem rkL_cgen_two_four_eq_of (h : T3RankDesc) : rkL 2 (cgen 2 4) = rkL 2 (bgen3 2) :=
  le_antisymm (rkL_cgen_two_four_le_of h) (rkL_bgen3_le_cgen 2)

theorem rkL_cgen_two_four_eq_of_t3Std (h : T3Std) : rkL 2 (cgen 2 4) = rkL 2 (bgen3 2) :=
  rkL_cgen_two_four_eq_of (t3RankDesc_of_t3Std h)

end Googology.Trans.DBMS

#print axioms Googology.Trans.DBMS.t3_expand_lt
#print axioms Googology.Trans.DBMS.rkL_lt_of_trio
#print axioms Googology.Trans.DBMS.t3_lift_trioGen
#print axioms Googology.Trans.DBMS.rkL_cgen_two_four_eq_of
#print axioms Googology.Trans.DBMS.rkL_cgen_two_four_eq_of_t3Std
