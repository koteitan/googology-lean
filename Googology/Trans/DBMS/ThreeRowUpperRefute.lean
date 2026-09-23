import Googology.Trans.DBMS.ThreeRowUpper

/-!
# `T3Std` is false

`ThreeRowUpper.lean` reduces `rkL 2 (cgen 2 4) ≤ rkL 2 (bgen3 2)` to
`T3RankDesc`, and shows that `T3Std` (every `t3 C` with `C ∈ SReach` is in
the trio fragment) would give it.  This file shows that **`T3Std` does not
hold** (`not_t3Std`), so the route through standard forms has to go through
`T3RankDesc` directly.

The counterexample:

    C₀ = (0,0,0)(1,1,0)(2,2,1)(3,1,0)                    ∈ SReach
    C₁ = C₀[1] = (0,0,0)(1,1,0)(2,2,1)(3,0,0)(4,1,0)(5,2,1)
    t3 C₁      = (0,0,0)(1,1,1)(2,2,1)(3,0,0)(4,1,0)(5,2,1)

`C₀` is reached from `(cgen 2 4)[1] = (0,0,0)(1,1,0)(2,2,1)(3,3,1)` by
`[1][0][1][1][0][1][0]` (`sReach_C₁`).  `t3 C₁` is not a standard form of the
trio fragment (`not_trioStdL_t3_C₁`): the standard form

    a = (0,0,0)(1,1,1)(2,2,1)(3,0,0)(4,1,1)              (trioStdL_a)

is above it, but every `a[k] = (0,0,0)(1,1,1)(2,2,1)(3,0,0)(4,1,0)(5,2,0)⋯(k+3,k,0)`
is below it, which `trio_cofinal` forbids.  (`a` is reached from `trioGen 3`
by fourteen expansions, the same path as `C₀` with column `1` raised.)

The rank itself behaves: `(t3 C₁)[k] = a[k + 1]` (`expandRL_t3_C₁`), so
`rkL 2 (t3 C₁) ≤ rkL 2 a < rkL 2 (t3 C₀)` (`t3RankDesc_C₀`), which is the
instance of `T3RankDesc` at `C₀`, `N = 1`.  `t3 C₁` is a non-standard matrix
with the rank of the standard `a`.
-/

namespace Googology.Trans.DBMS

open Ordinal Order
open Googology.Trans.BMS
open Googology.Trans.BMS.TrioCofinal (trioGen TrioStdL trio_cofinal)

theorem trio_step_eq {l l' : List (List Nat)} (N : Nat) (h : TrioStdL l)
    (e : expandRL 3 N l = l') : TrioStdL l' := e ▸ TrioStdL.step N h

theorem sReach_step_eq {l l' : List (List Nat)} (N : Nat) (h : SReach l)
    (e : expandRL 3 N l = l') : SReach l' := e ▸ SReach.step N h

/-- `C₀ = (0,0,0)(1,1,0)(2,2,1)(3,1,0)`. -/
def C₀ : List (List Nat) := [[0, 0, 0], [1, 1, 0], [2, 2, 1], [3, 1, 0]]

/-- `C₁ = C₀[1]`. -/
def C₁ : List (List Nat) := [[0, 0, 0], [1, 1, 0], [2, 2, 1], [3, 0, 0], [4, 1, 0], [5, 2, 1]]

/-- The standard form just above `t3 C₁`. -/
def aTop : List (List Nat) := [[0, 0, 0], [1, 1, 1], [2, 2, 1], [3, 0, 0], [4, 1, 1]]

/-- `t3 C₁`. -/
def T₁ : List (List Nat) := [[0, 0, 0], [1, 1, 1], [2, 2, 1], [3, 0, 0], [4, 1, 0], [5, 2, 1]]

theorem expandRL_C₀ : expandRL 3 1 C₀ = C₁ := by decide

theorem sReach_C₀ : SReach C₀ := by
  refine sReach_step_eq 0 ?_ (by decide : expandRL 3 0
    [[0, 0, 0], [1, 1, 0], [2, 2, 1], [3, 1, 0], [4, 2, 1]] = C₀)
  refine sReach_step_eq 1 ?_ (by decide : expandRL 3 1
    [[0, 0, 0], [1, 1, 0], [2, 2, 1], [3, 2, 0]] = [[0, 0, 0], [1, 1, 0], [2, 2, 1], [3, 1, 0], [4, 2, 1]])
  refine sReach_step_eq 0 ?_ (by decide : expandRL 3 0
    [[0, 0, 0], [1, 1, 0], [2, 2, 1], [3, 2, 0], [4, 3, 1]] = [[0, 0, 0], [1, 1, 0], [2, 2, 1], [3, 2, 0]])
  refine sReach_step_eq 1 ?_ (by decide : expandRL 3 1
    [[0, 0, 0], [1, 1, 0], [2, 2, 1], [3, 2, 1]] = [[0, 0, 0], [1, 1, 0], [2, 2, 1], [3, 2, 0], [4, 3, 1]])
  refine sReach_step_eq 1 ?_ (by decide : expandRL 3 1
    [[0, 0, 0], [1, 1, 0], [2, 2, 1], [3, 3, 0]] = [[0, 0, 0], [1, 1, 0], [2, 2, 1], [3, 2, 1]])
  refine sReach_step_eq 0 ?_ (by decide : expandRL 3 0
    [[0, 0, 0], [1, 1, 0], [2, 2, 1], [3, 3, 0], [4, 4, 1]] = [[0, 0, 0], [1, 1, 0], [2, 2, 1], [3, 3, 0]])
  exact sReach_step_eq 1 (SReach.gen 1) (by decide : expandRL 3 1 (expandRL 3 1 (cgen 2 4)) =
    [[0, 0, 0], [1, 1, 0], [2, 2, 1], [3, 3, 0], [4, 4, 1]])

/-- **`C₁ = C₀[1]` is reached from the content generator `(0,0,0)(1,1,0)(2,2,1)(3,3,2)`.** -/
theorem sReach_C₁ : SReach C₁ := expandRL_C₀ ▸ SReach.step 1 sReach_C₀

theorem t3_C₁ : t3 C₁ = T₁ := by decide

theorem t3_C₀ : t3 C₀ = [[0, 0, 0], [1, 1, 1], [2, 2, 1], [3, 1, 0]] := by decide

/-- **`a = (0,0,0)(1,1,1)(2,2,1)(3,0,0)(4,1,1)` is a standard form of the trio
fragment**, fourteen expansions below `trioGen 3`. -/
theorem trioStdL_a : TrioStdL aTop := by
  have h3 : TrioStdL [[0, 0, 0], [1, 1, 1], [2, 2, 1], [3, 1, 0]] := by
    refine trio_step_eq 0 ?_ (by decide : expandRL 3 0
      [[0, 0, 0], [1, 1, 1], [2, 2, 1], [3, 1, 0], [4, 2, 1]] = [[0, 0, 0], [1, 1, 1], [2, 2, 1], [3, 1, 0]])
    refine trio_step_eq 0 ?_ (by decide : expandRL 3 0
      [[0, 0, 0], [1, 1, 1], [2, 2, 1], [3, 1, 0], [4, 2, 1], [5, 3, 1]]
        = [[0, 0, 0], [1, 1, 1], [2, 2, 1], [3, 1, 0], [4, 2, 1]])
    refine trio_step_eq 1 ?_ (by decide : expandRL 3 1
      [[0, 0, 0], [1, 1, 1], [2, 2, 1], [3, 1, 1]]
        = [[0, 0, 0], [1, 1, 1], [2, 2, 1], [3, 1, 0], [4, 2, 1], [5, 3, 1]])
    refine trio_step_eq 0 ?_ (by decide : expandRL 3 0
      [[0, 0, 0], [1, 1, 1], [2, 2, 1], [3, 1, 1], [4, 2, 1]] = [[0, 0, 0], [1, 1, 1], [2, 2, 1], [3, 1, 1]])
    refine trio_step_eq 1 ?_ (by decide : expandRL 3 1
      [[0, 0, 0], [1, 1, 1], [2, 2, 1], [3, 2, 0]] = [[0, 0, 0], [1, 1, 1], [2, 2, 1], [3, 1, 1], [4, 2, 1]])
    refine trio_step_eq 0 ?_ (by decide : expandRL 3 0
      [[0, 0, 0], [1, 1, 1], [2, 2, 1], [3, 2, 0], [4, 3, 1]] = [[0, 0, 0], [1, 1, 1], [2, 2, 1], [3, 2, 0]])
    refine trio_step_eq 0 ?_ (by decide : expandRL 3 0
      [[0, 0, 0], [1, 1, 1], [2, 2, 1], [3, 2, 0], [4, 3, 1], [5, 4, 1]]
        = [[0, 0, 0], [1, 1, 1], [2, 2, 1], [3, 2, 0], [4, 3, 1]])
    refine trio_step_eq 1 ?_ (by decide : expandRL 3 1
      [[0, 0, 0], [1, 1, 1], [2, 2, 1], [3, 2, 1]]
        = [[0, 0, 0], [1, 1, 1], [2, 2, 1], [3, 2, 0], [4, 3, 1], [5, 4, 1]])
    refine trio_step_eq 1 ?_ (by decide : expandRL 3 1
      [[0, 0, 0], [1, 1, 1], [2, 2, 1], [3, 3, 0]] = [[0, 0, 0], [1, 1, 1], [2, 2, 1], [3, 2, 1]])
    refine trio_step_eq 0 ?_ (by decide : expandRL 3 0
      [[0, 0, 0], [1, 1, 1], [2, 2, 1], [3, 3, 0], [4, 4, 1]] = [[0, 0, 0], [1, 1, 1], [2, 2, 1], [3, 3, 0]])
    refine trio_step_eq 0 ?_ (by decide : expandRL 3 0
      [[0, 0, 0], [1, 1, 1], [2, 2, 1], [3, 3, 0], [4, 4, 1], [5, 5, 1]]
        = [[0, 0, 0], [1, 1, 1], [2, 2, 1], [3, 3, 0], [4, 4, 1]])
    exact trio_step_eq 1 (TrioStdL.gen 3) (by decide : expandRL 3 1 (trioGen 3)
      = [[0, 0, 0], [1, 1, 1], [2, 2, 1], [3, 3, 0], [4, 4, 1], [5, 5, 1]])
  refine trio_step_eq 0 ?_ (by decide : expandRL 3 0
    [[0, 0, 0], [1, 1, 1], [2, 2, 1], [3, 0, 0], [4, 1, 1], [5, 2, 1]] = aTop)
  exact trio_step_eq 1 h3 (by decide : expandRL 3 1 [[0, 0, 0], [1, 1, 1], [2, 2, 1], [3, 1, 0]]
    = [[0, 0, 0], [1, 1, 1], [2, 2, 1], [3, 0, 0], [4, 1, 1], [5, 2, 1]])

theorem valid_aTop : Valid 2 aTop := by unfold Valid; decide

theorem badRootR_aTop : badRootR 3 aTop = some 3 := by decide

theorem expandRL_aTop_two : expandRL 3 2 aTop =
    [[0, 0, 0], [1, 1, 1], [2, 2, 1], [3, 0, 0], [4, 1, 0], [5, 2, 0]] := by decide

/-- `a[k + 2]` extends `a[2]`. -/
theorem expandRL_aTop_ext (k : Nat) : ∃ Z, expandRL 3 (k + 2) aTop = expandRL 3 2 aTop ++ Z := by
  induction k with
  | zero => exact ⟨[], by rw [List.append_nil]⟩
  | succ k ih =>
    obtain ⟨Z, hZ⟩ := ih
    obtain ⟨X, _, hX⟩ := expandRL_succ_append 3 (k + 2) aTop badRootR_aTop
    exact ⟨Z ++ X, by rw [show k + 1 + 2 = (k + 2) + 1 from rfl, hX, hZ, List.append_assoc]⟩

/-- **Every `a[k]` is below `t3 C₁`.** -/
theorem expandRL_aTop_lt (k : Nat) : expandRL 3 k aTop < T₁ := by
  match k with
  | 0 => decide
  | 1 => decide
  | k + 2 =>
    obtain ⟨Z, hZ⟩ := expandRL_aTop_ext k
    rw [hZ, expandRL_aTop_two, T₁]
    exact List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl,
      List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl,
      List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, List.cons_lt_cons_iff.mpr
        (Or.inl (by decide))⟩)⟩)⟩)⟩)⟩)

theorem T₁_lt_aTop : T₁ < aTop := by decide

/-- **`t3 C₁` is not in the trio fragment.** -/
theorem not_trioStdL_t3_C₁ : ¬ TrioStdL (t3 C₁) := by
  rw [t3_C₁]
  intro h
  obtain ⟨k, hk⟩ := trio_cofinal trioStdL_a h T₁_lt_aTop
  have hlt := expandRL_aTop_lt k
  rcases hk with he | hk
  · rw [← he] at hlt; exact lt_irrefl _ hlt
  · exact lt_asymm hk hlt

/-- **`T3Std` is false.** -/
theorem not_t3Std : ¬ T3Std := fun h => not_trioStdL_t3_C₁ (h C₁ sReach_C₁)

/-! ### The rank at the counterexample -/

theorem badRootR_T₁ : badRootR 3 T₁ = some 4 := by decide

theorem m0L_T₁ : m0L 3 T₁ = 2 := by decide

theorem m0L_aTop : m0L 3 aTop = 2 := by decide

/-- **`(t3 C₁)[k] = a[k + 1]`.** -/
theorem expandRL_t3_C₁ (k : Nat) : expandRL 3 k T₁ = expandRL 3 (k + 1) aTop := by
  rw [expandRL, badRootR_T₁, expandRL, badRootR_aTop]
  dsimp only
  rw [m0L_T₁, m0L_aTop, show T₁.length - 1 - 4 = 1 from rfl, show aTop.length - 1 - 3 = 1 from rfl,
    Nat.mul_one, Nat.mul_one, map_range_succ_front (n := k + 1)]
  simp only [Nat.mod_one, Nat.div_one, Nat.add_zero, beq_self_eq_true, Bool.true_or, Bool.and_true]
  rw [show (List.range 4).map (fun i => T₁[i]!) = [[0, 0, 0], [1, 1, 1], [2, 2, 1], [3, 0, 0]] from rfl,
    show (List.range 3).map (fun i => aTop[i]!) = [[0, 0, 0], [1, 1, 1], [2, 2, 1]] from rfl]
  simp only [List.cons_append, List.nil_append, List.cons.injEq, true_and]
  refine ⟨by decide, List.map_congr_left (fun t _ => ?_)⟩
  rw [show (List.range 3 : List Nat) = [0, 1, 2] from rfl]
  simp only [List.map_cons, List.map_nil]
  show [_, _, _] = [_, _, _]
  simp only [List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_⟩ <;> simp [T₁, aTop] <;> omega

theorem valid_T₁ : Valid 2 T₁ := by unfold Valid; decide

theorem rkL_T₁_le : rkL 2 T₁ ≤ rkL 2 aTop := by
  rw [rkL_step valid_T₁ (by decide)]
  refine Ordinal.iSup_le (fun k => succ_le_of_lt ?_)
  rw [expandRL_t3_C₁]
  exact rkL_lt valid_aTop (by decide) (k + 1)

/-- **`T3RankDesc` holds at the counterexample**: `rkL 2 (t3 (C₀[1])) < rkL 2 (t3 C₀)`,
although `t3 (C₀[1])` is not standard. -/
theorem t3RankDesc_C₀ : rkL 2 (t3 (expandRL 3 1 C₀)) < rkL 2 (t3 C₀) := by
  rw [expandRL_C₀, t3_C₁, t3_C₀]
  have e : expandRL 3 0 (expandRL 3 1 [[0, 0, 0], [1, 1, 1], [2, 2, 1], [3, 1, 0]]) = aTop := by
    decide
  have hv : Valid 2 [[0, 0, 0], [1, 1, 1], [2, 2, 1], [3, 1, 0]] := by unfold Valid; decide
  calc rkL 2 T₁ ≤ rkL 2 aTop := rkL_T₁_le
    _ = rkL 2 (expandRL 3 0 (expandRL 3 1 [[0, 0, 0], [1, 1, 1], [2, 2, 1], [3, 1, 0]])) := by rw [e]
    _ < rkL 2 (expandRL 3 1 [[0, 0, 0], [1, 1, 1], [2, 2, 1], [3, 1, 0]]) :=
        rkL_lt (valid_expandRL hv 1) (by decide) 0
    _ < rkL 2 [[0, 0, 0], [1, 1, 1], [2, 2, 1], [3, 1, 0]] := rkL_lt hv (by decide) 1

end Googology.Trans.DBMS

#print axioms Googology.Trans.DBMS.not_t3Std
#print axioms Googology.Trans.DBMS.sReach_C₁
#print axioms Googology.Trans.DBMS.t3RankDesc_C₀
