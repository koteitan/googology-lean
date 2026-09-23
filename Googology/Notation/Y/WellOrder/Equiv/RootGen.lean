/-
From koteitan, 1y-expand-equiv, `Equiv/RootGen.lean`
(https://github.com/koteitan/1y-expand-equiv, revision c9a5368a09ceb62ec671a6c3447a4719d035dfc0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.Y.WellOrder.`; the transcription `Equiv/Yukito.lean` is replaced by
`Googology.Notation.Y.Yukito` (opened below).
This file is part of googology-lean and is licensed under its MIT license.
-/
import Googology.Notation.Y.WellOrder.Equiv.RowSucc

open Googology.Notation.Y

/-!
# 一般の行への還元

行を 1 つ固定して記号を決める。frame を `F`、その上の値を `U` とすると、
その行の森は `G = restrictedParent F U`、次の行の値は
`v q = U q - U (G q)`（親が無ければ 0）である。Lean では `select F U` が
ちょうどこの行にあたる。

`root` を `G` の根、`p` を `G p = root` なる列、`j` を `root` より右で最初に
「次の行で生きている」列とする。目標は `v p ≤ v j` である。

本ファイルは、これが次の 2 つだけに帰着することを示す。

* (a) `root` は `j` の `F` 祖先である
* (1) `U p ≤ U j`

残りは (a) と (1) から出る。すなわち

* (b) `G j = some t` なら `root ≤ t`  … (a) と (1) から
* (2) `U t ≤ U root`                 … (a) と (b) と祖先鎖の線形性から
* `v p ≤ v j`                        … (1) と (2) から（`difference_le_of_value_le`）
-/

namespace Yukito

open OneY OneY.Numeric

variable {F : ParentForest} {U : Nat → Nat}

/-- 祖先鎖は線形。同じ列の 2 つの `F` 祖先は比較可能で、左の方が右の祖先になる。 -/
theorem anc_of_common (j root t : Nat)
    (hr : ZeroY.Forest.Ancestor F.parent j root)
    (ht : ZeroY.Forest.Ancestor F.parent j t)
    (hlt : root < t) : ZeroY.Forest.Ancestor F.parent t root :=
  ZeroY.Forest.ancestor_of_common_target F.parent_left hr ht hlt

/-- (b)。`root` が `j` の `F` 祖先で値も小さければ、`root` は親候補なので
実際の親は `root` 以上の位置にある。 -/
theorem parent_ge_root (root j t : Nat)
    (ha : ZeroY.Forest.Ancestor F.parent j root)
    (hpos : 0 < U root) (hlt : U root < U j)
    (ht : restrictedParent F U j = some t) : root ≤ t := by
  obtain ⟨_, _, _, hmax⟩ := (restrictedParent_some_iff F U j t).mp ht
  exact hmax root ha hpos hlt

/-- (2)。`root` と `t` の間の列がすべて `G` の根なら、`t` の値は `U root` 以下。

`t = root` なら等号。`root < t` なら `t` は `G` の根であり、
`root` は `t` の `F` 祖先（`anc_of_common`）なので、根の条件から
`U t ≤ U root` が出る。 -/
theorem parent_value_le_root (root j t : Nat)
    (ha : ZeroY.Forest.Ancestor F.parent j root)
    (hpos : 0 < U root)
    (hdead : ∀ q, root < q → q < j → restrictedParent F U q = none)
    (ht : restrictedParent F U j = some t)
    (hge : root ≤ t) : U t ≤ U root := by
  rcases Nat.eq_or_lt_of_le hge with heq | hgt
  · subst heq; exact Nat.le_refl _
  · obtain ⟨hanc, _, _, _⟩ := (restrictedParent_some_iff F U j t).mp ht
    have htj : t < j := ZeroY.Forest.ancestor_lt F.parent_left hanc
    have hroot_t : ZeroY.Forest.Ancestor F.parent t root := anc_of_common j root t ha hanc hgt
    have hnone := hdead t hgt htj
    have := (restrictedParent_none_iff F U t).mp hnone root
      (ParentForest.ancestor_of_zeroY hroot_t) hpos
    exact this

/-- 還元の総まとめ。(a) と (1) から `v p ≤ v j` が出る。 -/
theorem diff_le_of_a_and_one (root p j : Nat)
    (hp : restrictedParent F U p = some root)
    (ha : ZeroY.Forest.Ancestor F.parent j root)
    (hpos : 0 < U root)
    (hdead : ∀ q, root < q → q < j → restrictedParent F U q = none)
    (hjlive : ∃ t, restrictedParent F U j = some t)
    (hone : U p ≤ U j) :
    (select F U).difference p ≤ (select F U).difference j := by
  obtain ⟨t, ht⟩ := hjlive
  -- U root < U p は親の条件から
  obtain ⟨_, _, hlt, _⟩ := (restrictedParent_some_iff F U p root).mp hp
  -- (b)
  have hge : root ≤ t := parent_ge_root root j t ha hpos (by omega) ht
  -- (2)
  have hUt : U t ≤ U root := parent_value_le_root root j t ha hpos hdead ht hge
  -- 最終算術
  exact difference_le_of_value_le (select F U) hp ht hUt hone

/-! ## `j` が `p` の `F` 祖先である場合

この場合、(a) と (1) はどちらも `restrictedParent` の最大性と
祖先鎖の線形性だけで出る。 -/

/-- (1) の祖先の場合。`root = G p` は `0 < U` かつ `U < U p` を満たす
`F` 祖先のうち最大のものだから、`root` より右の `F` 祖先 `j` は
その条件を満たさない。`U j > 0` なので `U p ≤ U j` となる。 -/
theorem one_of_ancestor (root p j : Nat)
    (hp : restrictedParent F U p = some root)
    (hj : ZeroY.Forest.Ancestor F.parent p j)
    (hjr : root < j) (hUj : 0 < U j) : U p ≤ U j := by
  obtain ⟨_, _, _, hmax⟩ := (restrictedParent_some_iff F U p root).mp hp
  rcases Nat.lt_or_ge (U j) (U p) with hlt | hge
  · have := hmax j hj hUj hlt
    omega
  · exact hge

end Yukito
