/-
Adapted from Phyrion, 1Y-Well-Ordering-Lean, formalization/ZeroY/Expansion/Prefix.lean,
revision 6533b2975f3cafb3582dc8f8127e9ea7144d7e69 (Apache-2.0).
Changes: imports and namespaces of the BMS layer renamed to Por.BMS. In `encode_expandY_of_no_site`, the unfolding of `expandRaw` is replaced by the Por.BMS lemma `expandRaw_of_maximalParentRow_none`.
Taken from koteitan, 1y-wo-por, `ZeroY/Expansion/Prefix.lean` (https://github.com/koteitan/1y-wo-por,
revision db86f2d13c2e18a8e2c2fae5e083d00fc4d48a78, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.Y.WellOrder.`.
-/
import Googology.Notation.Y.WellOrder.ZeroY.Expansion.Context
import Googology.Notation.Y.WellOrder.ZeroY.PaddedExt
import Googology.Notation.Y.WellOrder.ZeroY.OrderEmbedding
import Googology.Notation.Y.WellOrder.ZeroY.Structural.Prefix

/-!
# 前缀交换及退化展开

编码与截取任意前缀交换。删除末项的退化展开因此直接交换，不需要
假定源表达式是标准式，也不需要展开保持定理。
-/

namespace ZeroY

open Por.BMS

def Expr.take (s : Expr) (count : Nat) : Expr :=
  ⟨s.values.take count, legal_take s.legal count⟩

def matrixPrefix (array : ValidArray) (count : Nat) : ValidArray where
  raw := trimZeroRows (array.raw.take count)
  rectangular_eq := by
    apply rectangular_trimZeroRows
    apply rectangular_iff_exists_uniformHeight.mpr
    refine ⟨trimHeight array.raw, ?_⟩
    intro column hColumn
    exact validArray_uniform_trimHeight array column (List.mem_of_mem_take hColumn)
  trimmed_eq := trimZeroRows_idempotent _

theorem encode_take (s : Expr) (count : Nat) :
    encode (s.take count) = matrixPrefix (encode s) count := by
  apply validArray_eq_of_padded_entries
  · rw [encode_length]
    simp only [Expr.take, matrixPrefix, length_trimZeroRows, List.length_take, encode_length]
  · intro column hColumn row
    have hBounds : column < s.values.length ∧ column < count := by
      rw [encode_length] at hColumn
      change column < (s.values.take count).length at hColumn
      simp only [List.length_take] at hColumn
      omega
    change matrixEntry (encode (s.take count)).raw column row =
      matrixEntry (trimZeroRows ((encode s).raw.take count)) column row
    rw [matrixEntry_trimZeroRows, matrixEntry_take hBounds.2]
    apply encode_entry_eq_of_prefix
    · simpa only [encode_length] using hColumn
    · exact hBounds.1
    · intro earlier hEarlier
      exact congrArg (fun value : Option Nat => value.getD 0)
        (List.getElem?_take_of_lt (by omega : earlier < count))

theorem expandY_eq_take_of_no_site (s : Expr) (count : Nat)
    (hNone : expansionSite s.values = none) :
    expandY s count = s.take (s.values.length - 1) := by
  apply Expr.ext
  simp only [expandY_values, expandYRaw, hNone, Expr.take]

theorem encode_expandY_of_no_site (s : Expr) (count : Nat)
    (hNone : expansionSite s.values = none) :
    encode (expandY s count) = (encode s).expand count := by
  rw [expandY_eq_take_of_no_site s count hNone, encode_take]
  have hMaximal := (expansionSite_none_iff s).mp hNone
  apply ValidArray.ext
  change trimZeroRows ((encode s).raw.take (s.values.length - 1)) =
    trimZeroRows (expandRaw (encode s).raw count)
  rw [← encode_length s, expandRaw_of_maximalParentRow_none hMaximal]

end ZeroY
