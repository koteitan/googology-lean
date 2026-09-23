/-
Adapted from Phyrion, 1Y-Well-Ordering-Lean, formalization/ZeroY/Encode.lean,
revision 6533b2975f3cafb3582dc8f8127e9ea7144d7e69 (Apache-2.0).
Changes: imports and namespaces of the BMS layer renamed to Por.BMS.
Taken from koteitan, 1y-wo-por, `ZeroY/Encode.lean` (https://github.com/koteitan/1y-wo-por,
revision db86f2d13c2e18a8e2c2fae5e083d00fc4d48a78, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.Y.WellOrder.`.
-/
import Googology.Notation.Y.WellOrder.ZeroY.Mountain
import Googology.Notation.Y.WellOrder.Por.BMS

/-!
# 与上游规范矩阵载体相接的编码

先用山脉算法生成列，再删除共同尾零行。这只固定矩阵表示，不以可逆性或
标准生成性作为定义前提。编码和解码的全称往返定理仍须另证。
-/

namespace ZeroY

theorem encodeRaw_rectangular (values : Sequence) :
    Por.BMS.rectangular (encodeRaw values) = true := by
  apply Por.BMS.rectangular_iff_exists_uniformHeight.mpr
  refine ⟨(mountainRows (maxValue values) ⟨values, linearParent⟩).length, ?_⟩
  intro column hColumn
  rcases List.mem_map.mp hColumn with ⟨index, _, rfl⟩
  simp

/-- 合法 0-Y 表达式到规范矩阵的总编码。 -/
def encode (s : Expr) : Por.BMS.ValidArray where
  raw := Por.BMS.trimZeroRows (encodeRaw s.values)
  rectangular_eq := Por.BMS.rectangular_trimZeroRows (encodeRaw_rectangular s.values)
  trimmed_eq := Por.BMS.trimZeroRows_idempotent _

@[simp]
theorem encode_raw (s : Expr) :
    (encode s).raw = Por.BMS.trimZeroRows (encodeRaw s.values) := rfl

theorem encode_length (s : Expr) : (encode s).raw.length = s.values.length := by
  simp [encode, encodeRaw_length]

/-- 全 1 输入产生零行矩阵，每一个列位置都保留。 -/
theorem encodeRaw_nil_columns_of_all_ones (values : Sequence)
    (hOnes : values.all (fun value => value == 1) = true) :
    encodeRaw values = List.replicate values.length [] := by
  have hRows : mountainRows (maxValue values) ⟨values, linearParent⟩ = [] := by
    cases maxValue values <;> simp [mountainRows, hOnes]
  simp [encodeRaw, hRows, List.map_const']

theorem encodeRaw_replicate_one (count : Nat) :
    encodeRaw (List.replicate count 1) = List.replicate count [] := by
  simpa using encodeRaw_nil_columns_of_all_ones (List.replicate count 1) (by simp)

end ZeroY
