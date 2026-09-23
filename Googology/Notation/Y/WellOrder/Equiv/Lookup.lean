/-
From koteitan, 1y-expand-equiv, `Equiv/Lookup.lean`
(https://github.com/koteitan/1y-expand-equiv, revision c9a5368a09ceb62ec671a6c3447a4719d035dfc0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.Y.WellOrder.`; the transcription `Equiv/Yukito.lean` is replaced by
`Googology.Notation.Y.Yukito` (opened below).
This file is part of googology-lean and is licensed under its MIT license.
-/
import Googology.Notation.Y.WellOrder.Equiv.Rep
import Googology.Notation.Y.WellOrder.Equiv.SibSucc

open Googology.Notation.Y

/-!
# 疎配列を列番号で引く

`Rep` があるとき、生きた列は必ず配列の中にあり、`firstAtLeast` はその添字を指す
（`rep_lookup`）。

JS の親探索にはもう 1 つ、Lean 側に対応するもののない条件がある。

```js
if (j<0 || j<lastLayer.length-1 && lastLayer[j].position+1!=lastLayer[j+1].position) break;
```

「`j` のすぐ右に隙間があれば打ち切る」というもので、本ファイルの `breakHere` である。
これは**右隣の列も生きていれば発動しない**（`not_breakHere`）。理由は単純で、
右隣の列が生きていれば配列でも隣り合うからである。

親探索が見る列は鎖の要素であり、鎖の要素 `q` は必ず「ある列の親」なので、
`leftmost_child_all` から `q + 1` も生きている。したがって鎖の上では隙間 break は
発動しない。発動しうるのは鎖の根に降りたときだけで、そこでは JS も Lean も親を返さない
（`Search.lean`）。
-/

namespace Yukito

open OneY OneY.Numeric

/-- 生きた列は疎配列の中にあり、`firstAtLeast` はその添字を指す。 -/
theorem rep_lookup (row : Rowj) (r n : Nat) (U : Nat → Nat) (h : Rep row r n U)
    (c : Nat) (hrc : r ≤ c) (hcn : c < n) (hlive : 0 < U c) :
    ∃ j, ∃ hj : j < row.size, (row[j]'hj).pos + r = c ∧ firstAtLeast row (c - r) = j := by
  obtain ⟨x, hx, hcx⟩ := h.cover c hrc hcn hlive
  obtain ⟨j, hj, hjx⟩ := getElem_of_mem row hx
  have hcj : (row[j]'hj).pos + r = c := by rw [hjx]; exact hcx
  exact ⟨j, hj, hcj,
    firstAtLeast_eq_of_mem row h.posMono (c - r) j hj (by omega)⟩

/-- 生きている 2 列が隣り合っていれば、配列でも隣り合う。 -/
theorem rep_succ_index (row : Rowj) (r n : Nat) (U : Nat → Nat) (h : Rep row r n U)
    (c j : Nat) (hj : j < row.size) (hcj : (row[j]'hj).pos + r = c)
    (_hrc : r ≤ c) (hcn : c + 1 < n) (hlive : 0 < U (c + 1)) :
    ∃ hj1 : j + 1 < row.size, (row[j+1]'hj1).pos + r = c + 1 := by
  obtain ⟨m, hm, hcm, _⟩ := rep_lookup row r n U h (c + 1) (by omega) hcn hlive
  have hjm : j < m := by
    rcases Nat.lt_trichotomy m j with hlt | heq | hgt
    · have := h.posMono m j hm hj hlt
      omega
    · subst heq; omega
    · exact hgt
  have hj1 : j + 1 < row.size := by omega
  refine ⟨hj1, ?_⟩
  rcases Nat.eq_or_lt_of_le hjm with heq | hgt
  · subst heq
    exact hcm
  · exfalso
    have h1 := h.posMono j (j + 1) hj hj1 (by omega)
    have h2 := h.posMono (j + 1) m hj1 hm (by omega)
    omega

/-- **隙間 break は、右隣の列も生きていれば発動しない。** -/
theorem not_breakHere (row : Rowj) (r n : Nat) (U : Nat → Nat) (h : Rep row r n U)
    (c j : Nat) (hj : j < row.size) (hcj : (row[j]'hj).pos + r = c)
    (hrc : r ≤ c) (hcn : c + 1 < n) (hlive : 0 < U (c + 1)) :
    breakHere row j = false := by
  obtain ⟨hj1, hcj1⟩ := rep_succ_index row r n U h c j hj hcj hrc hcn hlive
  show (if h : j < row.size then
          if h2 : j + 1 < row.size then decide ((row[j]'h).pos + 1 ≠ (row[j+1]'h2).pos)
          else false
        else true) = false
  rw [dif_pos hj, dif_pos hj1, decide_eq_false_iff_not]
  omega

/-- 鎖の要素の右隣は、その行で生きている。鎖の要素はどれも「ある列の親」なので、
`leftmost_child_rows`（最左の子は右隣）が使える。したがって鎖の上では
隙間 break は発動しない。 -/
theorem chain_succ_live (T : Tower) (k q x : Nat)
    (h : (rows T.base k).forest.parent x = some q) :
    0 < (rows T.base (k + 1)).value (q + 1) :=
  (rows_parent_iff_next_live T.base k (q + 1)).mp
    ⟨q, leftmost_child_rows T k q x h⟩

/-- 目標列が死んでいて右隣が生きていれば、`firstAtLeast` は右隣を指す。
山の段で唯一のずれが起きるのがこの形である。 -/
theorem rep_lookup_dead (row : Rowj) (r n : Nat) (U : Nat → Nat) (h : Rep row r n U)
    (c : Nat) (hrc : r ≤ c + 1) (hcn : c + 1 < n) (hdead : U c = 0)
    (hlive : 0 < U (c + 1)) :
    ∃ j, ∃ hj : j < row.size,
      (row[j]'hj).pos + r = c + 1 ∧ firstAtLeast row (c - r) = j := by
  obtain ⟨j, hj, hcj, _⟩ := rep_lookup row r n U h (c + 1) hrc hcn hlive
  refine ⟨j, hj, hcj, firstAtLeast_eq row (c - r) j hj (by omega) ?_⟩
  intro i hi hij
  have h1 := h.posMono i j hi hj hij
  rcases Nat.lt_or_ge c r with _ | hrc'
  · omega
  · have h2 : (row[i]'hi).pos + r ≠ c := by
      intro he
      have hlv := h.live _ (mem_of_getElem row i hi)
      have hv := h.val _ (mem_of_getElem row i hi)
      rw [he, hdead] at hv
      omega
    omega

/-- 位置引きの成功。生きた列は必ず引ける。 -/
theorem lookupPos_some (row : Rowj) (r n : Nat) (U : Nat → Nat) (h : Rep row r n U)
    (c : Nat) (hrc : r ≤ c) (hcn : c < n) (hlive : 0 < U c) :
    ∃ m, ∃ hm : m < row.size,
      lookupPos row (c - r) = some m ∧ (row[m]'hm).pos + r = c := by
  obtain ⟨m, hm, hcm, hfa⟩ := rep_lookup row r n U h c hrc hcn hlive
  refine ⟨m, hm, ?_, hcm⟩
  simp only [lookupPos, hfa, dif_pos hm,
    if_pos (show (row[m]'hm).pos = c - r by omega)]

/-- 位置引きの失敗。死んだ列は引けない。 -/
theorem lookupPos_none (row : Rowj) (r n : Nat) (U : Nat → Nat) (h : Rep row r n U)
    (c : Nat) (hrc : r ≤ c) (hdead : U c = 0) : lookupPos row (c - r) = none := by
  simp only [lookupPos]
  split
  · rename_i hm
    have hne : (row[firstAtLeast row (c - r)]'hm).pos ≠ c - r := by
      intro he
      have h1 := h.val _ (mem_of_getElem row _ hm)
      have h2 := h.live _ (mem_of_getElem row _ hm)
      rw [show (row[firstAtLeast row (c - r)]'hm).pos + r = c by omega, hdead] at h1
      omega
    rw [if_neg hne]
  · rfl

end Yukito
