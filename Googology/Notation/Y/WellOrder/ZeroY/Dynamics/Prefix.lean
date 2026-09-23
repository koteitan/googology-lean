/-
Adapted from Phyrion, 1Y-Well-Ordering-Lean, formalization/ZeroY/Dynamics/Prefix.lean,
revision 6533b2975f3cafb3582dc8f8127e9ea7144d7e69 (Apache-2.0).
Changes: none besides this header (the file refers to no BMS-layer name).
Taken from koteitan, 1y-wo-por, `ZeroY/Dynamics/Prefix.lean` (https://github.com/koteitan/1y-wo-por,
revision db86f2d13c2e18a8e2c2fae5e083d00fc4d48a78, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.Y.WellOrder.`.
-/
import Googology.Notation.Y.WellOrder.ZeroY.Dynamics.Definitions
import Googology.Notation.Y.WellOrder.ZeroY.Expansion.Conjugacy

/-!
# 有限展开闭包对任意前缀封闭

使用实际算法的参数零删尾等式，不调用良序性来证明前缀可达。
-/

namespace ZeroY

theorem expr_take_take (s : Expr) (first second : Nat) :
    (s.take first).take second = s.take (min second first) := by
  apply Expr.ext
  exact List.take_take ..

theorem expr_take_of_length_le (s : Expr) (count : Nat) (hCount : s.values.length ≤ count) :
    s.take count = s := by
  apply Expr.ext
  exact List.take_of_length_le hCount

theorem yPath_take (s : Expr) (count : Nat) : YExpansionPath s (s.take count) := by
  generalize hLength : s.values.length = length
  induction length using Nat.strongRecOn generalizing s with
  | ind length ih =>
      by_cases hCount : length ≤ count
      · rw [expr_take_of_length_le s count (by omega)]
        exact .refl _
      · have hLengthPos : 0 < length := by omega
        have hMiddleLength : (s.take (s.values.length - 1)).values.length = length - 1 := by
          simp only [Expr.take, List.length_take, hLength, Nat.min_eq_left (Nat.sub_le ..)]
        have hPrior : YExpansionPath s (s.take (s.values.length - 1)) := by
          rw [← expandY_zero]
          exact .single s 0
        have hNext := ih (length - 1) (by omega) (s.take (s.values.length - 1)) hMiddleLength
        rw [expr_take_take, Nat.min_eq_left (by omega : count ≤ s.values.length - 1)] at hNext
        exact hPrior.trans hNext

theorem yGenerated_take {s : Expr} (hGenerated : YGenerated s) (count : Nat) :
    YGenerated (s.take count) := yGenerated_of_path hGenerated (yPath_take s count)

end ZeroY
