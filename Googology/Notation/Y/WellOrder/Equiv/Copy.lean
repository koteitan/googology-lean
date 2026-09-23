/-
From koteitan, 1y-expand-equiv, `Equiv/Copy.lean`
(https://github.com/koteitan/1y-expand-equiv, revision c9a5368a09ceb62ec671a6c3447a4719d035dfc0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.Y.WellOrder.`; the transcription `Equiv/Yukito.lean` is replaced by
`Googology.Notation.Y.Yukito` (opened below).
This file is part of googology-lean and is licensed under its MIT license.
-/
import Googology.Notation.Y.WellOrder.Equiv.NoBad

open Googology.Notation.Y

/-!
# コピーの座標

JS の Mt.Fuji シェルは、継ぎ目の列 `j` を `j + len * i` へ写す。Phyrion 側の
`CopyCoordinates` は同じ写像を `encode` / `parentCopy` と呼ぶ。ここでは両者の
算術が一致することを示す。

- 値の周期的なコピー（JS の `yamaVal`）は `OrdinaryCopy` の `source0` である。
- 親の桁上げ（JS の `shift`）は `parentCopy` である。
-/

namespace Yukito

open OneY OneY.Numeric

/-- **周期的なコピーは `source0` の形をしている。** -/
theorem yamaVal_eq (base : Rowj) (y x c : Nat) (hyx : y < x) :
    yamaVal base y x c = valAtIdx base (if c < y then c else y + (c - y) % (x - y)) := by
  unfold yamaVal
  rcases Nat.lt_or_ge c x with hcx | hcx
  · rw [if_pos hcx]
    rcases Nat.lt_or_ge c y with hcy | hcy
    · rw [if_pos hcy]
    · rw [if_neg (Nat.not_lt.mpr hcy)]
      have h1 : (c - y) % (x - y) = c - y := Nat.mod_eq_of_lt (by omega)
      have h2 : y + (c - y) = c := by omega
      rw [h1, h2]
  · rw [if_neg (Nat.not_lt.mpr hcx), if_neg (by omega)]
    have hmod : (c - x) % (x - y) = (c - y) % (x - y) := by
      have he : c - y = (c - x) + (x - y) := by omega
      rw [he, Nat.add_mod_right]
    rw [hmod]

/-- **JS の桁上げは `parentCopy` である。** -/
theorem js_shift_eq_parentCopy (C : CopyCoordinates.Context) (b col : Nat) :
    col + (if C.y ≤ col then b * C.length else 0) = C.parentCopy b col := by
  unfold CopyCoordinates.Context.parentCopy
  rcases Nat.lt_or_ge col C.y with h | h
  · rw [if_neg (Nat.not_le.mpr h), if_pos h, Nat.add_zero]
  · rw [if_pos h, if_neg (Nat.not_lt.mpr h)]

/-! ## 段への積み足し

`pushAt res k c` は段 `k` の末尾にセルを積む。段が無ければ作る。ループでは `k` は
0 から順に増えるので、つねに `k ≤ res.length` である。 -/

theorem rowAt_getElem? (L : List Rowj) (r : Nat) : rowAt L r = (L[r]?).getD #[] := rfl

theorem rowAt_set_self (L : List Rowj) (y : Rowj) (k : Nat) (h : k < L.length) :
    rowAt (L.set k y) k = y := by
  rw [rowAt_getElem?, List.getElem?_set_self h]
  rfl

theorem rowAt_set_of_ne (L : List Rowj) (y : Rowj) (k m : Nat) (h : m ≠ k) :
    rowAt (L.set k y) m = rowAt L m := by
  rw [rowAt_getElem?, rowAt_getElem?, List.getElem?_set_ne (Ne.symm h)]

theorem rowAt_append_lt (L : List Rowj) (x : Rowj) (m : Nat) (h : m < L.length) :
    rowAt (L ++ [x]) m = rowAt L m := by
  rw [rowAt_getElem?, rowAt_getElem?, List.getElem?_append_left h]

theorem rowAt_append_self (L : List Rowj) (x : Rowj) : rowAt (L ++ [x]) L.length = x := by
  rw [rowAt_getElem?, List.getElem?_append_right (Nat.le_refl _)]
  simp

theorem rowAt_append_gt (L : List Rowj) (x : Rowj) (m : Nat) (h : L.length < m) :
    rowAt (L ++ [x]) m = #[] := by
  rw [rowAt_of_ge]
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

/-- 積み足したあとの段の数。 -/
theorem pushAt_length (res : List Rowj) (k : Nat) (c : Cell) (hk : k ≤ res.length) :
    (pushAt res k c).length = max res.length (k + 1) := by
  unfold pushAt
  rcases Nat.lt_or_ge k res.length with h | h
  · rw [if_pos h, List.length_set]
    omega
  · have he : k = res.length := by omega
    subst he
    rw [if_neg (Nat.lt_irrefl _)]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

/-- **積み足したあとの各段。** 段 `k` には末尾にセルが増え、他の段は変わらない。 -/
theorem rowAt_pushAt (res : List Rowj) (k m : Nat) (c : Cell) (hk : k ≤ res.length) :
    rowAt (pushAt res k c) m = if m = k then (rowAt res k).push c else rowAt res m := by
  unfold pushAt
  rcases Nat.lt_or_ge k res.length with h | h
  · rw [if_pos h]
    rcases Decidable.em (m = k) with hm | hm
    · subst hm
      rw [if_pos rfl, rowAt_set_self _ _ _ h]
      rfl
    · rw [if_neg hm, rowAt_set_of_ne _ _ _ _ hm]
  · have he : k = res.length := by omega
    subst he
    rw [if_neg (Nat.lt_irrefl _)]
    rcases Decidable.em (m = res.length) with hm | hm
    · subst hm
      rw [if_pos rfl, rowAt_append_self, rowAt_of_ge res _ (Nat.le_refl _)]
      rfl
    · rw [if_neg hm]
      rcases Nat.lt_or_ge m res.length with h2 | h2
      · exact rowAt_append_lt _ _ _ h2
      · rw [rowAt_append_gt _ _ _ (by omega), rowAt_of_ge _ _ (by omega)]

/-! ## 段のループ

`fujiRows` は段 `k = 0 … kmax−1` に 1 個ずつセルを積む。段 `k` に積むとき、
それより上の段はまだ触られていないので、`fujiCell` に渡る「今の段」は
ループに入る前の段 `k` そのものである。 -/

/-- `fujiRows` が段 `k` に積むセル。 -/
def fujiCellAt (M : List Rowj) (P : FujiParams) (nd : Nat → Nat) (i j : Nat)
    (isRep isAsc : Bool) (res : List Rowj) (k : Nat) : Cell :=
  let sysx := fujiSourceAt P i k isRep isAsc
  let sx := sourceIdx M sysx.1 j sysx.2
  let ir := if isRep then 1 else 0
  fujiCell M P (rowAt res k) sysx.1 sx k i j (i - ir) (nd (j + P.len * i))

theorem fujiRows_length (M : List Rowj) (P : FujiParams) (nd : Nat → Nat) (i j : Nat)
    (isRep isAsc : Bool) : ∀ (kmax : Nat) (res : List Rowj),
      (fujiRows M P nd i j isRep isAsc kmax res).length = max res.length kmax := by
  intro kmax
  induction kmax with
  | zero => intro res; simp only [fujiRows, Nat.max_def]; split <;> omega
  | succ kmax ih =>
      intro res
      have hlen := ih res
      have hk : kmax ≤ (fujiRows M P nd i j isRep isAsc kmax res).length := by
        rw [hlen]
        simp only [Nat.max_def]
        split <;> omega
      show (pushAt (fujiRows M P nd i j isRep isAsc kmax res) kmax _).length = _
      rw [pushAt_length _ _ _ hk, hlen]
      simp only [Nat.max_def]
      split <;> split <;> (first | omega | (split <;> omega))

/-- **段のループの結果。** 段 `m < kmax` にはセルが 1 個増え、他は変わらない。 -/
theorem rowAt_fujiRows (M : List Rowj) (P : FujiParams) (nd : Nat → Nat) (i j : Nat)
    (isRep isAsc : Bool) : ∀ (kmax : Nat) (res : List Rowj) (m : Nat),
      rowAt (fujiRows M P nd i j isRep isAsc kmax res) m
        = if m < kmax then (rowAt res m).push (fujiCellAt M P nd i j isRep isAsc res m)
          else rowAt res m := by
  intro kmax
  induction kmax with
  | zero => intro res m; rw [if_neg (by omega)]; rfl
  | succ kmax ih =>
      intro res m
      have hlen := fujiRows_length M P nd i j isRep isAsc kmax res
      have hk : kmax ≤ (fujiRows M P nd i j isRep isAsc kmax res).length := by
        rw [hlen]
        simp only [Nat.max_def]
        split <;> omega
      have hcur : rowAt (fujiRows M P nd i j isRep isAsc kmax res) kmax = rowAt res kmax := by
        rw [ih res kmax, if_neg (by omega)]
      show rowAt (pushAt (fujiRows M P nd i j isRep isAsc kmax res) kmax
        (fujiCell M P (rowAt (fujiRows M P nd i j isRep isAsc kmax res) kmax)
          (fujiSourceAt P i kmax isRep isAsc).1
          (sourceIdx M (fujiSourceAt P i kmax isRep isAsc).1 j
            (fujiSourceAt P i kmax isRep isAsc).2)
          kmax i j (i - (if isRep then 1 else 0)) (nd (j + P.len * i)))) m = _
      rw [rowAt_pushAt _ _ _ _ hk]
      rcases Decidable.em (m = kmax) with hm | hm
      · rw [if_pos hm, hcur, if_pos (show m < kmax + 1 by omega), hm]
        rfl
      · rw [if_neg hm, ih res m]
        rcases Nat.lt_or_ge m kmax with h | h
        · rw [if_pos h, if_pos (show m < kmax + 1 by omega)]
        · rw [if_neg (show ¬ m < kmax by omega), if_neg (show ¬ m < kmax + 1 by omega)]

/-! ## 継ぎ目と繰り返しのループ -/

/-- 継ぎ目の列 `j` が「置き換え」の列か。 -/
def isRepAt (P : FujiParams) (j : Nat) : Bool := decide (j = P.badRootSeam)

/-- 継ぎ目の列 `j` が上りかどうか。 -/
def isAscAt (M : List Rowj) (P : FujiParams) (j ascFuel : Nat) : Bool :=
  isAscending M P.badRootHeight P.badRootSeam j ascFuel

/-- 置き換えの継ぎ目が上りなら、`isRepAt` から `isAscAt` が出る。 -/
theorem hra_of_seamAsc (M : List Rowj) (P : FujiParams) (fuel j : Nat)
    (h : isAscAt M P P.badRootSeam fuel = true) :
    isRepAt P j = true → isAscAt M P j fuel = true := by
  intro hr
  have hj : j = P.badRootSeam := of_decide_eq_true hr
  rw [hj]
  exact h

/-- 継ぎ目の列 `j` で積む段の数。 -/
def kmaxAt (M : List Rowj) (P : FujiParams) (i j afterCutHeight ascFuel : Nat) : Nat :=
  let isAsc := isAscAt M P j ascFuel
  let seamH := seamHeightOf M j afterCutHeight
  let d := P.cutHeight - P.badRootHeight
  if isAsc then seamH + d * i else seamH

theorem fujiSeams_succ (M : List Rowj) (P : FujiParams) (nd : Nat → Nat)
    (i ach af t : Nat) (res : List Rowj) :
    fujiSeams M P nd i ach af (t + 1) res
      = fujiRows M P nd i (P.badRootSeam + t) (isRepAt P (P.badRootSeam + t))
          (isAscAt M P (P.badRootSeam + t) af)
          (kmaxAt M P i (P.badRootSeam + t) ach af) (fujiSeams M P nd i ach af t res) := rfl

theorem fujiIters_succ (M : List Rowj) (P : FujiParams) (nd : Nat → Nat)
    (ach af i : Nat) (res : List Rowj) :
    fujiIters M P nd ach af (i + 1) res
      = fujiSeams M P nd (i + 1) ach af P.len (fujiIters M P nd ach af i res) := rfl

/-! ## 段は後ろに伸びるだけ

`pushAt` は末尾に積むので、既にある添字のセルは変わらない。したがって
`fujiCell` が見る「今の段」は、最終形と既存の添字の上で一致する。 -/

/-- `b` は `a` の後ろにセルを足したもの。 -/
def RowExt (a b : Rowj) : Prop := a.size ≤ b.size ∧ ∀ i, i < a.size → b[i]? = a[i]?

theorem RowExt.rfl' (a : Rowj) : RowExt a a := ⟨Nat.le_refl _, fun _ _ => rfl⟩

theorem RowExt.trans {a b c : Rowj} (h1 : RowExt a b) (h2 : RowExt b c) : RowExt a c := by
  refine ⟨Nat.le_trans h1.1 h2.1, fun i hi => ?_⟩
  exact (h2.2 i (Nat.lt_of_lt_of_le hi h1.1)).trans (h1.2 i hi)

theorem RowExt.push (a : Rowj) (c : Cell) : RowExt a (a.push c) :=
  ⟨by rw [Array.size_push]; omega,
   fun i hi => by rw [Array.getElem?_push, if_neg (by omega)]⟩

theorem rowExt_fujiRows (M : List Rowj) (P : FujiParams) (nd : Nat → Nat) (i j : Nat)
    (isRep isAsc : Bool) (kmax : Nat) (res : List Rowj) (m : Nat) :
    RowExt (rowAt res m) (rowAt (fujiRows M P nd i j isRep isAsc kmax res) m) := by
  rw [rowAt_fujiRows]
  split
  · exact RowExt.push _ _
  · exact RowExt.rfl' _

theorem rowExt_fujiSeams (M : List Rowj) (P : FujiParams) (nd : Nat → Nat) (i ach af : Nat) :
    ∀ (t : Nat) (res : List Rowj) (m : Nat),
      RowExt (rowAt res m) (rowAt (fujiSeams M P nd i ach af t res) m) := by
  intro t
  induction t with
  | zero => intro res m; exact RowExt.rfl' _
  | succ t ih =>
      intro res m
      rw [fujiSeams_succ]
      exact RowExt.trans (ih res m) (rowExt_fujiRows _ _ _ _ _ _ _ _ _ _)

theorem rowExt_fujiIters (M : List Rowj) (P : FujiParams) (nd : Nat → Nat) (ach af : Nat) :
    ∀ (n : Nat) (res : List Rowj) (m : Nat),
      RowExt (rowAt res m) (rowAt (fujiIters M P nd ach af n res) m) := by
  intro n
  induction n with
  | zero => intro res m; exact RowExt.rfl' _
  | succ n ih =>
      intro res m
      rw [fujiIters_succ]
      exact RowExt.trans (ih res m) (rowExt_fujiSeams _ _ _ _ _ _ _ _ _)

/-! ## 積むセルの列と親の列 -/

/-- **親の列は「元の親の列 + 桁上げ」。** `parentPos` はそれを段 `k` の position に
直したものである。 -/
theorem parentPos_eq (M : List Rowj) (P : FujiParams) (sy sx k shifts q : Nat)
    (hsy : sy ≤ k) (hq : parentPos M P sy sx k shifts = some q) :
    ∃ hx : sx < (rowAt M sy).size, ∃ sp, ((rowAt M sy)[sx]'hx).par = some sp ∧
      ∃ hp : sp < (rowAt M sy).size,
        q + k = ((rowAt M sy)[sp]'hp).pos + sy
          + (if P.badRootSeam ≤ ((rowAt M sy)[sp]'hp).pos + sy then shifts * P.len else 0) := by
  unfold parentPos at hq
  dsimp only at hq
  split at hq
  · next hx =>
      cases hpar : ((rowAt M sy)[sx]'hx).par with
      | none => rw [hpar] at hq; exact absurd hq (by simp)
      | some sp =>
          rw [hpar] at hq
          dsimp only at hq
          split at hq
          · next hp =>
              split at hq
              · next hs =>
                  split at hq
                  · next hcond =>
                      refine ⟨hx, sp, hpar, hp, ?_⟩
                      rw [if_pos hs]
                      have he := Option.some.inj hq
                      omega
                  · exact absurd hq (by simp)
              · next hs =>
                  split at hq
                  · next hcond =>
                      refine ⟨hx, sp, hpar, hp, ?_⟩
                      rw [if_neg hs]
                      have he := Option.some.inj hq
                      omega
                  · exact absurd hq (by simp)
          · exact absurd hq (by simp)
  · exact absurd hq (by simp)

/-! ## 子を切る

`cutChild res cutH` は段 `0 … cutH` の最後のセルを落とし、最上段が空なら段ごと落とす。 -/

/-- 段 `i` の最後のセルを落とす 1 歩。 -/
def popStep (r : List Rowj) (i : Nat) : List Rowj :=
  if i < r.length then r.set i ((r.getD i #[]).pop) else r

theorem rowAt_take_lt (L : List Rowj) (k m : Nat) (h : m < k) :
    rowAt (L.take k) m = rowAt L m := by
  rw [rowAt_getElem?, rowAt_getElem?, List.getElem?_take_of_lt h]

theorem popFold_length : ∀ (n : Nat) (res : List Rowj),
    ((List.range n).foldl popStep res).length = res.length := by
  intro n
  induction n with
  | zero => intro res; rfl
  | succ n ih =>
      intro res
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, popStep]
      split
      · rw [List.length_set, ih]
      · exact ih res

/-- **段 `m ≤ cutH` は最後のセルが 1 つ減る。** -/
theorem rowAt_popFold : ∀ (n : Nat) (res : List Rowj) (m : Nat),
    rowAt ((List.range n).foldl popStep res) m
      = if m < n then (rowAt res m).pop else rowAt res m := by
  intro n
  induction n with
  | zero => intro res m; rw [if_neg (show ¬ m < 0 by omega)]; rfl
  | succ n ih =>
      intro res m
      have hlen := popFold_length n res
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, popStep]
      split
      · next hn =>
          rcases Decidable.em (m = n) with hm | hm
          · have hA : ((List.range n).foldl popStep res).getD n #[] = rowAt res n := by
              rw [show ((List.range n).foldl popStep res).getD n #[]
                    = rowAt ((List.range n).foldl popStep res) n from rfl,
                ih res n, if_neg (show ¬ n < n by omega)]
            rw [hm, rowAt_set_self _ _ _ hn, if_pos (show n < n + 1 by omega), hA]
          · rw [rowAt_set_of_ne _ _ _ _ hm, ih res m]
            rcases Nat.lt_or_ge m n with h | h
            · rw [if_pos h, if_pos (show m < n + 1 by omega)]
            · rw [if_neg (show ¬ m < n by omega), if_neg (show ¬ m < n + 1 by omega)]
      · next hn =>
          rw [ih res m]
          rcases Nat.lt_or_ge m n with h | h
          · rw [if_pos h, if_pos (show m < n + 1 by omega)]
          · rcases Decidable.em (m = n) with hm | hm
            · have hres : rowAt res m = #[] := rowAt_of_ge res m (by omega)
              rw [if_neg (show ¬ m < n by omega), if_pos (show m < n + 1 by omega), hres]
              rfl
            · rw [if_neg (show ¬ m < n by omega), if_neg (show ¬ m < n + 1 by omega)]

theorem cutChild_eq (res : List Rowj) (cutH : Nat) :
    cutChild res cutH
      = (if 0 < ((List.range (cutH + 1)).foldl popStep res).length ∧
            (rowAt ((List.range (cutH + 1)).foldl popStep res)
              (((List.range (cutH + 1)).foldl popStep res).length - 1)).size = 0
          then ((List.range (cutH + 1)).foldl popStep res).take
            (((List.range (cutH + 1)).foldl popStep res).length - 1)
          else (List.range (cutH + 1)).foldl popStep res) := rfl

theorem cutChild_length_le (res : List Rowj) (cutH : Nat) :
    (cutChild res cutH).length ≤ res.length := by
  have hlen := popFold_length (cutH + 1) res
  rw [cutChild_eq]
  split
  · rw [List.length_take]
    simp only [Nat.min_def]
    split <;> omega
  · omega

/-- **子を切ったあとの段。** 残っている段については、`cutH` 以下なら最後のセルが
1 つ減り、それより上は変わらない。 -/
theorem rowAt_cutChild (res : List Rowj) (cutH m : Nat) (h : m < (cutChild res cutH).length) :
    rowAt (cutChild res cutH) m
      = if m < cutH + 1 then (rowAt res m).pop else rowAt res m := by
  rw [cutChild_eq] at h
  rw [← rowAt_popFold (cutH + 1) res m, cutChild_eq]
  rcases Decidable.em (0 < ((List.range (cutH + 1)).foldl popStep res).length ∧
      (rowAt ((List.range (cutH + 1)).foldl popStep res)
        (((List.range (cutH + 1)).foldl popStep res).length - 1)).size = 0) with hc | hc
  · rw [if_pos hc] at h ⊢
    rw [List.length_take] at h
    refine rowAt_take_lt _ _ _ ?_
    simp only [Nat.min_def] at h
    split at h <;> omega
  · rw [if_neg hc]

/-! ## 伸びても引ける

`fujiCell` は `lookupPos` で親の添字を引く。段は後ろに伸びるだけなので、その添字は
最終形でも同じ添字である。 -/

theorem RowExt.getElem {a b : Rowj} (h : RowExt a b) (i : Nat) (hi : i < a.size) :
    ∃ hb : i < b.size, (b[i]'hb) = (a[i]'hi) := by
  have hb : i < b.size := Nat.lt_of_lt_of_le hi h.1
  refine ⟨hb, ?_⟩
  have h2 := h.2 i hi
  rw [Array.getElem?_eq_getElem hb, Array.getElem?_eq_getElem hi] at h2
  exact Option.some.inj h2

theorem lookupPos_some_iff (row : Rowj) (q i : Nat) (hl : lookupPos row q = some i) :
    ∃ hi : i < row.size, (row[i]'hi).pos = q := by
  unfold lookupPos at hl
  dsimp only at hl
  split at hl
  · next hm =>
      split at hl
      · next hpos =>
          have heq : firstAtLeast row q = i := Option.some.inj hl
          subst heq
          exact ⟨hm, hpos⟩
      · exact absurd hl (by simp)
  · exact absurd hl (by simp)

theorem lookupPos_of_pos (row : Rowj) (hmono : PosMono row) (q i : Nat) (hi : i < row.size)
    (hpos : (row[i]'hi).pos = q) : lookupPos row q = some i := by
  have hfa : firstAtLeast row q = i := firstAtLeast_eq_of_mem row hmono q i hi hpos
  simp only [lookupPos, hfa, dif_pos hi, if_pos hpos]

/-! ## 位置の単調性と列の上限

積むセルの列は `(i, j)` の辞書式順で真に増える。段への積み足しは末尾なので、
各段の位置はつねに真に増加のままである。 -/

/-- どの段も位置が真に増加している。 -/
def RowsMono (res : List Rowj) : Prop := ∀ m, PosMono (rowAt res m)

/-- どのセルの列も `b` より小さい。 -/
def ColLt (res : List Rowj) (b : Nat) : Prop :=
  ∀ (m t : Nat) (c : Cell), (rowAt res m)[t]? = some c → c.pos + m < b

theorem ColLt.mono {res : List Rowj} {b b' : Nat} (h : ColLt res b) (hb : b ≤ b') :
    ColLt res b' := fun m t c hc => Nat.lt_of_lt_of_le (h m t c hc) hb

theorem posMono_push (row : Rowj) (hmono : PosMono row) (c : Cell)
    (h : ∀ (t : Nat) (d : Cell), row[t]? = some d → d.pos < c.pos) : PosMono (row.push c) := by
  intro p q hp hq hpq
  rw [Array.size_push] at hp hq
  rcases Nat.lt_or_ge q row.size with hqs | hqs
  · have hps : p < row.size := by omega
    rw [Array.getElem_push_lt hps, Array.getElem_push_lt hqs]
    exact hmono p q hps hqs hpq
  · have hqe : q = row.size := by omega
    have hps : p < row.size := by omega
    subst hqe
    rw [Array.getElem_push_lt hps, Array.getElem_push_eq]
    exact h p (row[p]'hps) (Array.getElem?_eq_getElem hps)

theorem fujiCellAt_col (M : List Rowj) (P : FujiParams) (nd : Nat → Nat) (i j : Nat)
    (isRep isAsc : Bool) (res : List Rowj) (k : Nat) (h : k ≤ j + P.len * i) :
    (fujiCellAt M P nd i j isRep isAsc res k).pos + k = j + P.len * i := by
  show (j + P.len * i - k) + k = j + P.len * i
  omega

theorem fujiRows_invariant (M : List Rowj) (P : FujiParams) (nd : Nat → Nat) (i j : Nat)
    (isRep isAsc : Bool) (kmax : Nat) (res : List Rowj) (b : Nat)
    (hk : kmax ≤ j + P.len * i + 1) (hb : ColLt res b) (hbc : b ≤ j + P.len * i)
    (hmono : RowsMono res) :
    RowsMono (fujiRows M P nd i j isRep isAsc kmax res) ∧
      ColLt (fujiRows M P nd i j isRep isAsc kmax res) (j + P.len * i + 1) := by
  constructor
  · intro m
    rw [rowAt_fujiRows]
    split
    · next hm =>
        refine posMono_push _ (hmono m) _ ?_
        intro t d hd
        have h1 := hb m t d hd
        have h2 := fujiCellAt_col M P nd i j isRep isAsc res m (by omega)
        omega
    · exact hmono m
  · intro m t c hc
    rw [rowAt_fujiRows] at hc
    split at hc
    · next hm =>
        rw [Array.getElem?_push] at hc
        split at hc
        · have he := Option.some.inj hc
          have h2 := fujiCellAt_col M P nd i j isRep isAsc res m (by omega)
          rw [he] at h2
          omega
        · have := hb m t c hc
          omega
    · have := hb m t c hc
      omega

theorem fujiSeams_invariant (M : List Rowj) (P : FujiParams) (nd : Nat → Nat) (i ach af : Nat)
    (hkm : ∀ i' j', kmaxAt M P i' j' ach af ≤ j' + P.len * i' + 1) :
    ∀ (t : Nat) (res : List Rowj) (b : Nat),
      ColLt res b → b ≤ P.badRootSeam + P.len * i → RowsMono res →
      RowsMono (fujiSeams M P nd i ach af t res) ∧
        ColLt (fujiSeams M P nd i ach af t res) (P.badRootSeam + t + P.len * i) := by
  intro t
  induction t with
  | zero =>
      intro res b hb hbc hmono
      exact ⟨hmono, hb.mono (by omega)⟩
  | succ t ih =>
      intro res b hb hbc hmono
      obtain ⟨hm1, hb1⟩ := ih res b hb hbc hmono
      rw [fujiSeams_succ]
      have h := fujiRows_invariant M P nd i (P.badRootSeam + t)
        (isRepAt P (P.badRootSeam + t)) (isAscAt M P (P.badRootSeam + t) af)
        (kmaxAt M P i (P.badRootSeam + t) ach af)
        (fujiSeams M P nd i ach af t res) (P.badRootSeam + t + P.len * i)
        (hkm i (P.badRootSeam + t)) hb1 (by omega) hm1
      exact ⟨h.1, h.2.mono (by omega)⟩

theorem fujiIters_invariant (M : List Rowj) (P : FujiParams) (nd : Nat → Nat) (ach af : Nat)
    (hkm : ∀ i' j', kmaxAt M P i' j' ach af ≤ j' + P.len * i' + 1) :
    ∀ (n : Nat) (res : List Rowj) (b : Nat),
      ColLt res b → b ≤ P.badRootSeam + P.len → RowsMono res →
      RowsMono (fujiIters M P nd ach af n res) ∧
        ColLt (fujiIters M P nd ach af n res) (P.badRootSeam + P.len + P.len * n) := by
  intro n
  induction n with
  | zero =>
      intro res b hb hbc hmono
      exact ⟨hmono, hb.mono (by omega)⟩
  | succ n ih =>
      intro res b hb hbc hmono
      obtain ⟨hm1, hb1⟩ := ih res b hb hbc hmono
      rw [fujiIters_succ]
      have hle : P.badRootSeam + P.len + P.len * n ≤ P.badRootSeam + P.len * (n + 1) := by
        rw [Nat.mul_succ]
        omega
      have h := fujiSeams_invariant M P nd (n + 1) ach af hkm P.len
        (fujiIters M P nd ach af n res) (P.badRootSeam + P.len + P.len * n) hb1 hle hm1
      refine ⟨h.1, h.2.mono ?_⟩
      rw [Nat.mul_succ]
      omega

/-! ## どの列がどの段に載るか

段 `m` に載る列は、元からあったものと、`m < kmax(i,j)` となる `(i,j)` の
`j + len * i` である。ここでは載ることだけを示す。 -/

/-- 段 `m` に列 `c` のセルがある。 -/
def HasCol (res : List Rowj) (m c : Nat) : Prop :=
  ∃ (t : Nat) (d : Cell), (rowAt res m)[t]? = some d ∧ d.pos + m = c

theorem lt_size_of_getElem? {a : Rowj} {t : Nat} {d : Cell} (h : a[t]? = some d) :
    t < a.size := by
  rcases Nat.lt_or_ge t a.size with h1 | h1
  · exact h1
  · rw [Array.getElem?_eq_none h1] at h
    exact absurd h (by simp)

theorem HasCol.ext {res res' : List Rowj} {m c : Nat}
    (h : RowExt (rowAt res m) (rowAt res' m)) (hc : HasCol res m c) : HasCol res' m c := by
  obtain ⟨t, d, ht, hd⟩ := hc
  exact ⟨t, d, (h.2 t (lt_size_of_getElem? ht)).trans ht, hd⟩

theorem hasCol_fujiRows_new (M : List Rowj) (P : FujiParams) (nd : Nat → Nat) (i j : Nat)
    (isRep isAsc : Bool) (kmax : Nat) (res : List Rowj) (m : Nat) (hm : m < kmax)
    (hk : m ≤ j + P.len * i) :
    HasCol (fujiRows M P nd i j isRep isAsc kmax res) m (j + P.len * i) := by
  refine ⟨(rowAt res m).size, fujiCellAt M P nd i j isRep isAsc res m, ?_, ?_⟩
  · rw [rowAt_fujiRows, if_pos hm, Array.getElem?_push_size]
  · exact fujiCellAt_col M P nd i j isRep isAsc res m hk

theorem hasCol_fujiSeams (M : List Rowj) (P : FujiParams) (nd : Nat → Nat) (i ach af : Nat)
    (hkm : ∀ i' j', kmaxAt M P i' j' ach af ≤ j' + P.len * i' + 1) :
    ∀ (t : Nat) (res : List Rowj) (m j : Nat), P.badRootSeam ≤ j → j < P.badRootSeam + t →
      m < kmaxAt M P i j ach af →
      HasCol (fujiSeams M P nd i ach af t res) m (j + P.len * i) := by
  intro t
  induction t with
  | zero => intro res m j hj1 hj2 _; omega
  | succ t ih =>
      intro res m j hj1 hj2 hm
      rw [fujiSeams_succ]
      rcases Nat.lt_or_ge j (P.badRootSeam + t) with hlt | hge
      · exact HasCol.ext (rowExt_fujiRows _ _ _ _ _ _ _ _ _ _)
          (ih res m j hj1 hlt hm)
      · have hje : j = P.badRootSeam + t := by omega
        subst hje
        exact hasCol_fujiRows_new M P nd i (P.badRootSeam + t)
          (isRepAt P (P.badRootSeam + t)) (isAscAt M P (P.badRootSeam + t) af)
          (kmaxAt M P i (P.badRootSeam + t) ach af) _ m hm
          (by have := hkm i (P.badRootSeam + t); omega)

theorem hasCol_fujiIters (M : List Rowj) (P : FujiParams) (nd : Nat → Nat) (ach af : Nat)
    (hkm : ∀ i' j', kmaxAt M P i' j' ach af ≤ j' + P.len * i' + 1) :
    ∀ (n : Nat) (res : List Rowj) (m i j : Nat), 0 < i → i ≤ n →
      P.badRootSeam ≤ j → j < P.badRootSeam + P.len →
      m < kmaxAt M P i j ach af →
      HasCol (fujiIters M P nd ach af n res) m (j + P.len * i) := by
  intro n
  induction n with
  | zero => intro res m i j h1 h2 _ _ _; omega
  | succ n ih =>
      intro res m i j h1 h2 hj1 hj2 hm
      rw [fujiIters_succ]
      rcases Nat.lt_or_ge i (n + 1) with hlt | hge
      · exact HasCol.ext (rowExt_fujiSeams _ _ _ _ _ _ _ _ _)
          (ih res m i j h1 (by omega) hj1 hj2 hm)
      · have hie : i = n + 1 := by omega
        subst hie
        exact hasCol_fujiSeams M P nd (n + 1) ach af hkm P.len _ m j hj1 hj2 hm

/-- 元からあった列は残る。 -/
theorem hasCol_fujiIters_old (M : List Rowj) (P : FujiParams) (nd : Nat → Nat) (ach af : Nat)
    (n : Nat) (res : List Rowj) (m c : Nat) (h : HasCol res m c) :
    HasCol (fujiIters M P nd ach af n res) m c :=
  HasCol.ext (rowExt_fujiIters _ _ _ _ _ _ _ _) h

/-! ## 余分な列は載らない

逆向き。最終形のセルは、元からあったものか、`(i,j)` のどれかで積んだものである。 -/

theorem cell_fujiRows (M : List Rowj) (P : FujiParams) (nd : Nat → Nat) (i j : Nat)
    (isRep isAsc : Bool) (kmax : Nat) (res : List Rowj) (m t : Nat) (d : Cell)
    (h : (rowAt (fujiRows M P nd i j isRep isAsc kmax res) m)[t]? = some d) :
    (rowAt res m)[t]? = some d ∨ (m < kmax ∧ d = fujiCellAt M P nd i j isRep isAsc res m) := by
  rw [rowAt_fujiRows] at h
  split at h
  · next hm =>
      rw [Array.getElem?_push] at h
      split at h
      · exact Or.inr ⟨hm, (Option.some.inj h).symm⟩
      · exact Or.inl h
  · exact Or.inl h

theorem cell_fujiSeams (M : List Rowj) (P : FujiParams) (nd : Nat → Nat) (i ach af : Nat)
    (hkm : ∀ i' j', kmaxAt M P i' j' ach af ≤ j' + P.len * i' + 1) :
    ∀ (t : Nat) (res : List Rowj) (m u : Nat) (d : Cell),
      (rowAt (fujiSeams M P nd i ach af t res) m)[u]? = some d →
        (rowAt res m)[u]? = some d ∨
          ∃ j, P.badRootSeam ≤ j ∧ j < P.badRootSeam + t ∧ m < kmaxAt M P i j ach af ∧
            d.pos + m = j + P.len * i := by
  intro t
  induction t with
  | zero => intro res m u d h; exact Or.inl h
  | succ t ih =>
      intro res m u d h
      rw [fujiSeams_succ] at h
      rcases cell_fujiRows M P nd i (P.badRootSeam + t) (isRepAt P (P.badRootSeam + t))
        (isAscAt M P (P.badRootSeam + t) af)
        (kmaxAt M P i (P.badRootSeam + t) ach af) _ m u d h with h1 | ⟨hm, hd⟩
      · rcases ih res m u d h1 with h2 | ⟨j, hj1, hj2, hj3, hj4⟩
        · exact Or.inl h2
        · exact Or.inr ⟨j, hj1, by omega, hj3, hj4⟩
      · refine Or.inr ⟨P.badRootSeam + t, by omega, by omega, hm, ?_⟩
        rw [hd]
        exact fujiCellAt_col M P nd i (P.badRootSeam + t) _ _ _ m
          (by have := hkm i (P.badRootSeam + t); omega)

theorem cell_fujiIters (M : List Rowj) (P : FujiParams) (nd : Nat → Nat) (ach af : Nat)
    (hkm : ∀ i' j', kmaxAt M P i' j' ach af ≤ j' + P.len * i' + 1) :
    ∀ (n : Nat) (res : List Rowj) (m u : Nat) (d : Cell),
      (rowAt (fujiIters M P nd ach af n res) m)[u]? = some d →
        (rowAt res m)[u]? = some d ∨
          ∃ i j, 0 < i ∧ i ≤ n ∧ P.badRootSeam ≤ j ∧ j < P.badRootSeam + P.len ∧
            m < kmaxAt M P i j ach af ∧ d.pos + m = j + P.len * i := by
  intro n
  induction n with
  | zero => intro res m u d h; exact Or.inl h
  | succ n ih =>
      intro res m u d h
      rw [fujiIters_succ] at h
      rcases cell_fujiSeams M P nd (n + 1) ach af hkm P.len _ m u d h with h1 | ⟨j, hj⟩
      · rcases ih res m u d h1 with h2 | ⟨i, j, hi⟩
        · exact Or.inl h2
        · exact Or.inr ⟨i, j, hi.1, by omega, hi.2.2.1, hi.2.2.2.1, hi.2.2.2.2.1,
            hi.2.2.2.2.2⟩
      · exact Or.inr ⟨n + 1, j, by omega, Nat.le_refl _, hj.1, hj.2.1, hj.2.2.1, hj.2.2.2⟩

/-! ## 積むセルの中身 -/

theorem fujiCell_par (M : List Rowj) (P : FujiParams) (cur : Rowj)
    (sy sx k i j shifts topVal : Nat) :
    (fujiCell M P cur sy sx k i j shifts topVal).par
      = (match parentPos M P sy sx k shifts with
         | none => none
         | some q => lookupPos cur q) := rfl

theorem fujiCell_val (M : List Rowj) (P : FujiParams) (cur : Rowj)
    (sy sx k i j shifts topVal : Nat) :
    (fujiCell M P cur sy sx k i j shifts topVal).val
      = (if ((fujiCell M P cur sy sx k i j shifts topVal).par).isNone then topVal else 0) := rfl

/-- **積むセルの親の列。** 親の列は「元の親の列 + 桁上げ」である。 -/
theorem fujiCell_par_col (M : List Rowj) (P : FujiParams) (cur : Rowj)
    (sy sx k i j shifts topVal : Nat) (hsy : sy ≤ k) (p : Nat)
    (hp : (fujiCell M P cur sy sx k i j shifts topVal).par = some p) :
    ∃ (hp' : p < cur.size) (hx : sx < (rowAt M sy).size) (sp : Nat),
      ((rowAt M sy)[sx]'hx).par = some sp ∧ ∃ hsp : sp < (rowAt M sy).size,
        (cur[p]'hp').pos + k = ((rowAt M sy)[sp]'hsp).pos + sy
          + (if P.badRootSeam ≤ ((rowAt M sy)[sp]'hsp).pos + sy then shifts * P.len else 0) := by
  rw [fujiCell_par] at hp
  cases hq : parentPos M P sy sx k shifts with
  | none => rw [hq] at hp; exact absurd hp (by simp)
  | some q =>
      rw [hq] at hp
      dsimp only at hp
      obtain ⟨hp', hpos⟩ := lookupPos_some_iff cur q p hp
      obtain ⟨hx, sp, hpar, hsp, hcol⟩ := parentPos_eq M P sy sx k shifts q hsy hq
      exact ⟨hp', hx, sp, hpar, hsp, by rw [hpos]; exact hcol⟩

/-! ## 枝の選び方についての初等的な事実 -/

/-- **積む段の数の上限。** 継ぎ目の高さが `j + 1` 以下で、切りの落差 `d` が
コピー 1 つぶんの長さ以下なら、`kmax ≤ j + len*i + 1` である。 -/
theorem kmaxAt_le (M : List Rowj) (P : FujiParams) (i j ach af : Nat)
    (hs : seamHeightOf M j ach ≤ j + 1)
    (hd : P.cutHeight - P.badRootHeight ≤ P.len) :
    kmaxAt M P i j ach af ≤ j + P.len * i + 1 := by
  have hmul : (P.cutHeight - P.badRootHeight) * i ≤ P.len * i := Nat.mul_le_mul_right i hd
  unfold kmaxAt
  dsimp only
  split
  · omega
  · omega

/-! ## 覆えば密

位置が真に増加していて、列が `0 … W−1` をちょうど覆うなら、その疎配列は密である。 -/

theorem dense_of_cover (row : Rowj) (W : Nat) (hmono : PosMono row)
    (hb : ∀ (t : Nat) (d : Cell), row[t]? = some d → d.pos < W)
    (hc : ∀ c, c < W → ∃ (t : Nat) (d : Cell), row[t]? = some d ∧ d.pos = c) :
    row.size = W ∧ ∀ (t : Nat) (ht : t < row.size), (row[t]'ht).pos = t := by
  have key : ∀ c, c ≤ W →
      c ≤ row.size ∧ ∀ (t : Nat) (ht : t < row.size), t < c → (row[t]'ht).pos = t := by
    intro c
    induction c with
    | zero => intro _; exact ⟨Nat.zero_le _, fun t ht h => absurd h (by omega)⟩
    | succ c ih =>
        intro hcW
        obtain ⟨hcs, hpos⟩ := ih (by omega)
        obtain ⟨t, d, hd, hdc⟩ := hc c (by omega)
        have hts : t < row.size := lt_size_of_getElem? hd
        have hdt : (row[t]'hts) = d := by
          rw [Array.getElem?_eq_getElem hts] at hd
          exact Option.some.inj hd
        have htc : t = c := by
          rcases Nat.lt_trichotomy t c with h | h | h
          · exfalso
            have h1 := hpos t hts h
            rw [hdt, hdc] at h1
            omega
          · exact h
          · exfalso
            have hcs' : c < row.size := by omega
            have h1 := hmono c t hcs' hts h
            have h2 := posMono_add row hmono c 0 c (by omega) hcs' (by omega)
            rw [hdt, hdc] at h1
            omega
        subst htc
        refine ⟨by omega, fun u hu hut => ?_⟩
        rcases Nat.lt_or_ge u t with h | h
        · exact hpos u hu h
        · have hue : u = t := by omega
          subst hue
          rw [hdt, hdc]
  obtain ⟨hW, hall⟩ := key W (Nat.le_refl _)
  have hsz : row.size ≤ W := by
    rcases Nat.lt_or_ge W row.size with h | h
    · exfalso
      have hposW := posMono_add row hmono W 0 W (by omega) h (by omega)
      have hbW := hb W (row[W]'h) (Array.getElem?_eq_getElem h)
      omega
    · exact h
  exact ⟨by omega, fun t ht => hall t ht (by omega)⟩

/-! ## 継ぎ目の高さの上限 -/

/-- 継ぎ目の高さが正なら、積む段の数も正。 -/
theorem kmaxAt_pos (M : List Rowj) (P : FujiParams) (i j ach af : Nat)
    (hs : 0 < seamHeightOf M j ach) : 0 < kmaxAt M P i j ach af := by
  unfold kmaxAt
  dsimp only
  split
  · omega
  · omega

/-! ## 行 0 の列は隙間なく並ぶ

行 0 は元の `0 … afterCutLength−1` に加えて、繰り返しごとに `len` 列ずつ増える。
`badRootSeam + len = afterCutLength` なので、全体で `0 … afterCutLength + len*n − 1`
をちょうど覆う。 -/

theorem hasCol0_fujiIters (M : List Rowj) (P : FujiParams) (nd : Nat → Nat) (ach af : Nat)
    (hkm : ∀ i' j', kmaxAt M P i' j' ach af ≤ j' + P.len * i' + 1)
    (hkpos : ∀ i r, r < P.len → 0 < kmaxAt M P i (P.badRootSeam + r) ach af)
    (hlenpos : 0 < P.len) (hlen : P.badRootSeam + P.len = P.afterCutLength)
    (n : Nat) (res : List Rowj)
    (hd0 : ∀ c, c < P.afterCutLength → HasCol res 0 c) :
    ∀ c, c < P.afterCutLength + P.len * n → HasCol (fujiIters M P nd ach af n res) 0 c := by
  intro c hc
  rcases Nat.lt_or_ge c P.afterCutLength with h | h
  · exact hasCol_fujiIters_old M P nd ach af n res 0 c (hd0 c h)
  · obtain ⟨e, hev⟩ : ∃ e, c - P.afterCutLength = e := ⟨_, rfl⟩
    have helt : e < P.len * n := by omega
    obtain ⟨q, hqv⟩ : ∃ q, e / P.len = q := ⟨_, rfl⟩
    obtain ⟨r, hrv⟩ : ∃ r, e % P.len = r := ⟨_, rfl⟩
    have hdm : P.len * q + r = e := by
      rw [← hqv, ← hrv]
      exact Nat.div_add_mod e P.len
    have hmod : r < P.len := by
      rw [← hrv]
      exact Nat.mod_lt e hlenpos
    have hq : q < n := by
      rcases Nat.lt_or_ge q n with hx | hx
      · exact hx
      · exfalso
        have h2 : P.len * n ≤ P.len * q := Nat.mul_le_mul_left P.len hx
        omega
    have hmul : P.len * (q + 1) = P.len * q + P.len := Nat.mul_succ _ _
    have hcol : (P.badRootSeam + r) + P.len * (q + 1) = c := by omega
    have hh := hasCol_fujiIters M P nd ach af hkm n res 0 (q + 1) (P.badRootSeam + r)
      (by omega) (by omega) (by omega) (by omega) (hkpos (q + 1) r hmod)
    rw [hcol] at hh
    exact hh

/-- **行 0 は密。** 大きさは `afterCutLength + len * n`、位置は添字そのもの。 -/
theorem row0_dense_fujiIters (M : List Rowj) (P : FujiParams) (nd : Nat → Nat) (ach af : Nat)
    (hkm : ∀ i' j', kmaxAt M P i' j' ach af ≤ j' + P.len * i' + 1)
    (hkpos : ∀ i r, r < P.len → 0 < kmaxAt M P i (P.badRootSeam + r) ach af)
    (hlenpos : 0 < P.len) (hlen : P.badRootSeam + P.len = P.afterCutLength)
    (n : Nat) (res : List Rowj) (hmono : RowsMono res)
    (hb : ColLt res P.afterCutLength)
    (hd0 : ∀ c, c < P.afterCutLength → HasCol res 0 c) :
    (rowAt (fujiIters M P nd ach af n res) 0).size = P.afterCutLength + P.len * n ∧
      ∀ (t : Nat) (ht : t < (rowAt (fujiIters M P nd ach af n res) 0).size),
        ((rowAt (fujiIters M P nd ach af n res) 0)[t]'ht).pos = t := by
  obtain ⟨hm', hb'⟩ := fujiIters_invariant M P nd ach af hkm n res P.afterCutLength hb
    (by omega) hmono
  refine dense_of_cover _ _ (hm' 0) ?_ ?_
  · intro t d hd
    have h1 := hb' 0 t d hd
    omega
  · intro c hc
    obtain ⟨t, d, hd, hdc⟩ :=
      hasCol0_fujiIters M P nd ach af hkm hkpos hlenpos hlen n res hd0 c hc
    exact ⟨t, d, hd, by omega⟩

/-- **JS の出力の形。** 行 0 の大きさが `W` なら、出力は列 `0 … W−1` の値を
並べたものである。Phyrion の `reconstructedValues` と同じ形になる。 -/
theorem expandOut_eq_range (Mf : List Rowj) (W : Nat) (hsize : (rowAt Mf 0).size = W) :
    expandOut Mf = (List.range W).map (fun c => valAtIdx (rowAt Mf 0) c) := by
  refine List.ext_getElem ?_ ?_
  · simp only [expandOut, List.length_map, Array.length_toList, List.length_range, hsize]
  · intro t h1 h2
    have hts : t < (rowAt Mf 0).size := by
      simp only [expandOut, List.length_map, Array.length_toList] at h1
      exact h1
    simp only [expandOut, List.getElem_map, Array.getElem_toList, List.getElem_range]
    show ((rowAt Mf 0)[t]'hts).val = valAtIdx (rowAt Mf 0) t
    unfold valAtIdx
    rw [dif_pos hts]

/-- 継ぎ目が切ったあとの列数より小さければ、`badRootSeam + len = afterCutLength`。 -/
theorem badRootSeam_add_len (P : FujiParams) (h : P.badRootSeam ≤ P.afterCutLength) :
    P.badRootSeam + P.len = P.afterCutLength := by
  show P.badRootSeam + (P.afterCutLength - P.badRootSeam) = P.afterCutLength
  omega

/-! ## `expand` の `some` の枝の展開

`expandJS` の本体で使う値を名前付きにして、枝を書き下せるようにする。 -/

/-- 切る段。 -/
def expCutH (M : List Rowj) : Nat := (topRowOfLast M (rowAt M 0).size M.length).getD 0

/-- bad root の列。 -/
def expSeam (M : List Rowj) (mfuel : Nat) : Nat := (getBadRoot M mfuel mfuel).getD 0

/-- 対角から作る山。 -/
def expDg (M : List Rowj) (mfuel : Nat) : List Rowj :=
  calcMountainFrom (parseDiag (calcDiagonal M)) mfuel

/-- 山崎噴火の枝か。 -/
def expYama (M : List Rowj) (mfuel : Nat) : Prop := lastVal (rowAt (expDg M mfuel) 0) = 1

instance (M : List Rowj) (mfuel : Nat) : Decidable (expYama M mfuel) :=
  inferInstanceAs (Decidable (_ = _))

/-- 新しい対角の値。 -/
def expNd (nrep mfuel efuel : Nat) (M : List Rowj) : Nat → Nat :=
  if expYama M mfuel then
    yamaVal (rowAt (expDg M mfuel) 0).pop (expSeam M mfuel) ((rowAt M 0).size - 1)
  else valAtIdx (rowAt (expandJS nrep mfuel efuel (expDg M mfuel)) 0)

/-- 子を切ったあとの山。 -/
def expRes (M : List Rowj) : List Rowj := cutChild M (expCutH M)

/-- Mt.Fuji シェルのパラメータ。 -/
def expP (M : List Rowj) (mfuel : Nat) : FujiParams :=
  ⟨expSeam M mfuel,
   if expYama M mfuel then expCutH M - 1
     else (topRowWithCol M (expSeam M mfuel) M.length).getD 0,
   if expYama M mfuel then expCutH M - 1 else expCutH M,
   (rowAt (expRes M) 0).size,
   expYama M mfuel⟩

/-- Mt.Fuji シェルを回した結果（値の埋め前）。 -/
def fujiRaw (M : List Rowj) (mfuel : Nat) (nd : Nat → Nat) (nrep : Nat) : List Rowj :=
  fujiIters M (expP M mfuel) nd (expRes M).length mfuel nrep (expRes M)

/-- 値の埋めに渡す疎な山。 -/
def fujiRs (M : List Rowj) (mfuel : Nat) (nd : Nat → Nat) (nrep : Nat) : List Rowj :=
  dropEmptyTop (fujiRaw M mfuel nd nrep)

/-- **`expand` の `some` の枝。** -/
theorem expandJS_some (nrep mfuel efuel : Nat) (M : List Rowj)
    (h : (if hlt : (rowAt M 0).size - 1 < (rowAt M 0).size
          then (((rowAt M 0)[(rowAt M 0).size - 1]'hlt).par).isSome else false) = true) :
    expandJS nrep mfuel (efuel + 1) M
      = fillValues (dropEmptyTop (fujiIters M (expP M mfuel) (expNd nrep mfuel efuel M)
          (expRes M).length mfuel nrep (expRes M))) := by
  simp only [expandJS, h, Bool.not_true, Bool.false_eq_true, if_false]
  rfl

/-! ## 位置で読むことと列で読むこと

`fillRow` は 1 つ上の段を「position で」引く（`readValAt`）。列で引く `readVal` と
段のずれのぶんだけ違う。 -/

theorem readValAt_eq_readVal (row : Rowj) (r c : Nat) (h : r ≤ c) :
    readValAt row (c - r) = readVal row r c := by
  rcases Nat.lt_or_ge (firstAtLeast row (c - r)) row.size with hm | hm
  · obtain ⟨m, hmv⟩ : ∃ m, firstAtLeast row (c - r) = m := ⟨_, rfl⟩
    rw [hmv] at hm
    rcases Decidable.em ((row[m]'hm).pos = c - r) with hp | hp
    · have hlk : lookupPos row (c - r) = some m := by
        simp only [lookupPos, hmv, dif_pos hm, if_pos hp]
      have hrv : readVal row r c = (row[m]'hm).val := by
        simp only [readVal, hmv, dif_pos hm,
          if_pos (show (row[m]'hm).pos + r = c by omega)]
      rw [hrv]
      simp only [readValAt, hlk, dif_pos hm]
    · have hlk : lookupPos row (c - r) = none := by
        simp only [lookupPos, hmv, dif_pos hm, if_neg hp]
      have hrv : readVal row r c = 0 := by
        simp only [readVal, hmv, dif_pos hm,
          if_neg (show ¬ (row[m]'hm).pos + r = c by omega)]
      rw [hrv]
      simp only [readValAt, hlk]
  · have hlk : lookupPos row (c - r) = none := by
      simp only [lookupPos, dif_neg (Nat.not_lt.mpr hm)]
    have hrv : readVal row r c = 0 := by
      simp only [readVal, dif_neg (Nat.not_lt.mpr hm)]
    rw [hrv]
    simp only [readValAt, hlk]

/-- 添字で読んだ値は、その添字のセルの列で読んだ値。 -/
theorem readVal_of_index (row : Rowj) (hmono : PosMono row) (r c i : Nat) (hi : i < row.size)
    (hc : (row[i]'hi).pos + r = c) : readVal row r c = valAtIdx row i := by
  have hfa : firstAtLeast row (c - r) = i :=
    firstAtLeast_eq_of_mem row hmono (c - r) i hi (by omega)
  simp only [readVal, hfa, dif_pos hi, if_pos hc, valAtIdx]

/-! ## 値の埋めを列で書く -/

theorem fillValues_pos_get (Rs : List Rowj) (r t : Nat)
    (ht : t < (rowAt (fillValues Rs) r).size) (ht' : t < (rowAt Rs r).size) :
    ((rowAt (fillValues Rs) r)[t]'ht).pos = ((rowAt Rs r)[t]'ht').pos := by
  have h := fillValues_pos? Rs r t
  rw [Array.getElem?_eq_getElem ht, Array.getElem?_eq_getElem ht'] at h
  simpa using h

theorem posMono_fillValues (Rs : List Rowj) (r : Nat) (h : PosMono (rowAt Rs r)) :
    PosMono (rowAt (fillValues Rs) r) := by
  intro p q hp hq hpq
  have hsz := fillValues_size Rs r
  rw [fillValues_pos_get Rs r p hp (by omega), fillValues_pos_get Rs r q hq (by omega)]
  exact h p q (by omega) (by omega) hpq

/-- **値の埋めを列で書いたもの。** 値 0 のセルの列 `c` について
`V r c = V r（同じ段の親の列）+ V (r+1) c` である。 -/
theorem colVal_step (Rs : List Rowj)
    (hpar : ∀ (r i : Nat) (h : i < (rowAt Rs r).size) (p : Nat),
      ((rowAt Rs r)[i]'h).par = some p → p < i)
    (r : Nat) (hr : r + 1 < Rs.length) (i : Nat) (hi : i < (rowAt Rs r).size)
    (hmono : PosMono (rowAt Rs r)) (c : Nat) (hc : ((rowAt Rs r)[i]'hi).pos + r = c)
    (hrc : r + 1 ≤ c) (hval : ((rowAt Rs r)[i]'hi).val = 0) :
    readVal (rowAt (fillValues Rs) r) r c
      = (match ((rowAt Rs r)[i]'hi).par with
         | none => 0
         | some p => valAtIdx (rowAt (fillValues Rs) r) p)
        + readVal (rowAt (fillValues Rs) (r + 1)) (r + 1) c := by
  have hsz := fillValues_size Rs r
  have hiF : i < (rowAt (fillValues Rs) r).size := by omega
  have hposF : ((rowAt (fillValues Rs) r)[i]'hiF).pos + r = c := by
    rw [fillValues_pos_get Rs r i hiF hi]
    exact hc
  rw [readVal_of_index _ (posMono_fillValues Rs r hmono) r c i hiF hposF]
  rw [fillValues_val Rs hpar r hr i hi, if_neg (by omega)]
  have hpm : ((rowAt Rs r)[i]'hi).pos - 1 = c - (r + 1) := by omega
  rw [hpm, readValAt_eq_readVal _ (r + 1) c hrc]
  rfl

/-- **差分の関係を列だけで書いたもの。** `value_of_diff_prefix` の `hstep` の形。 -/
theorem colVal_step_col (Rs : List Rowj)
    (hpar : ∀ (r i : Nat) (h : i < (rowAt Rs r).size) (p : Nat),
      ((rowAt Rs r)[i]'h).par = some p → p < i)
    (r : Nat) (hr : r + 1 < Rs.length) (i : Nat) (hi : i < (rowAt Rs r).size)
    (hmono : PosMono (rowAt Rs r)) (c : Nat) (hc : ((rowAt Rs r)[i]'hi).pos + r = c)
    (hrc : r + 1 ≤ c) (hval : ((rowAt Rs r)[i]'hi).val = 0)
    (p : Nat) (hpi : ((rowAt Rs r)[i]'hi).par = some p) (hp : p < (rowAt Rs r).size)
    (cp : Nat) (hcp : ((rowAt Rs r)[p]'hp).pos + r = cp) :
    readVal (rowAt (fillValues Rs) r) r c
      = readVal (rowAt (fillValues Rs) r) r cp
        + readVal (rowAt (fillValues Rs) (r + 1)) (r + 1) c := by
  rw [colVal_step Rs hpar r hr i hi hmono c hc hrc hval, hpi]
  dsimp only
  have hszF := fillValues_size Rs r
  have hpF : p < (rowAt (fillValues Rs) r).size := by omega
  have hposF : ((rowAt (fillValues Rs) r)[p]'hpF).pos + r = cp := by
    rw [fillValues_pos_get Rs r p hpF hp]
    exact hcp
  rw [readVal_of_index _ (posMono_fillValues Rs r hmono) r cp p hpF hposF]

/-- **値が入っているセルは埋めで変わらない。** `value_of_diff_prefix` の `htop` に使う。 -/
theorem colVal_top (Rs : List Rowj)
    (hpar : ∀ (r i : Nat) (h : i < (rowAt Rs r).size) (p : Nat),
      ((rowAt Rs r)[i]'h).par = some p → p < i)
    (r : Nat) (hr : r + 1 < Rs.length) (i : Nat) (hi : i < (rowAt Rs r).size)
    (hmono : PosMono (rowAt Rs r)) (c : Nat) (hc : ((rowAt Rs r)[i]'hi).pos + r = c)
    (hval : ((rowAt Rs r)[i]'hi).val ≠ 0) :
    readVal (rowAt (fillValues Rs) r) r c = ((rowAt Rs r)[i]'hi).val := by
  have hsz := fillValues_size Rs r
  have hiF : i < (rowAt (fillValues Rs) r).size := by omega
  have hposF : ((rowAt (fillValues Rs) r)[i]'hiF).pos + r = c := by
    rw [fillValues_pos_get Rs r i hiF hi]
    exact hc
  rw [readVal_of_index _ (posMono_fillValues Rs r hmono) r c i hiF hposF]
  rw [fillValues_val Rs hpar r hr i hi, if_pos hval]

/-- 段に列が無ければ読んだ値は 0。`value_of_diff_prefix` の `hzero` に使う。 -/
theorem readVal_of_no_col (row : Rowj) (r c : Nat)
    (h : ∀ (t : Nat) (d : Cell), row[t]? = some d → d.pos + r ≠ c) : readVal row r c = 0 := by
  rcases Nat.lt_or_ge (firstAtLeast row (c - r)) row.size with hm | hm
  · obtain ⟨m, hmv⟩ : ∃ m, firstAtLeast row (c - r) = m := ⟨_, rfl⟩
    rw [hmv] at hm
    have hne : ¬ ((row[m]'hm).pos + r = c) :=
      h m (row[m]'hm) (Array.getElem?_eq_getElem hm)
    simp only [readVal, hmv, dif_pos hm, if_neg hne]
  · simp only [readVal, dif_neg (Nat.not_lt.mpr hm)]

/-! ## 山崎噴火の枝の新しい対角

JS は `(rowAt dg 0).pop`（対角の最後の列を落としたもの）に周期的なコピーを掛ける。
`source0 c` はつねに `x` より小さいので、落とした列は使われない。 -/

theorem source0_lt (y x c : Nat) (hyx : y < x) :
    (if c < y then c else y + (c - y) % (x - y)) < x := by
  split
  · omega
  · have := Nat.mod_lt (c - y) (show 0 < x - y by omega)
    omega

theorem valAtIdx_pop (base : Rowj) (s : Nat) (hs : s < base.size - 1) :
    valAtIdx base.pop s = valAtIdx base s := by
  have h1 : s < base.pop.size := by rw [Array.size_pop]; omega
  have h2 : s < base.size := by omega
  unfold valAtIdx
  rw [dif_pos h1, dif_pos h2, Array.getElem_pop]

/-- **最後の列を落としても周期的なコピーは変わらない。** -/
theorem yamaVal_pop (base : Rowj) (y x c : Nat) (hyx : y < x) (hx : x < base.size) :
    yamaVal base.pop y x c
      = valAtIdx base (if c < y then c else y + (c - y) % (x - y)) := by
  rw [yamaVal_eq base.pop y x c hyx]
  exact valAtIdx_pop base _ (by have := source0_lt y x c hyx; omega)

/-- `OrdinaryCopy` の言葉での言い換え。 -/
theorem yamaVal_pop_source0 (base : Rowj) (C : OrdinaryCopy.Context) (c : Nat)
    (hx : C.coordinates.x < base.size) :
    yamaVal base.pop C.coordinates.y C.coordinates.x c = valAtIdx base (C.source0 c) := by
  rw [yamaVal_pop base _ _ c C.coordinates.root_lt_last hx]
  unfold OrdinaryCopy.Context.source0 CopyCoordinates.Context.length
  rfl

/-! ## 新しい対角の値の 2 つの枝 -/

/-- `OrdinaryCopy` の言葉での言い換え。 -/
theorem expNd_yama_source0 (nrep mfuel efuel : Nat) (M : List Rowj) (h : expYama M mfuel)
    (C : OrdinaryCopy.Context) (hy : C.coordinates.y = expSeam M mfuel)
    (hxx : C.coordinates.x = (rowAt M 0).size - 1)
    (hx : (rowAt M 0).size - 1 < (rowAt (expDg M mfuel) 0).size) (c : Nat) :
    expNd nrep mfuel efuel M c = valAtIdx (rowAt (expDg M mfuel) 0) (C.source0 c) := by
  unfold expNd
  rw [if_pos h, ← hy, ← hxx]
  exact yamaVal_pop_source0 _ C c (by omega)

/-- **そうでない枝。** 新しい対角は、対角の山を展開した行 0 の値である。 -/
theorem expNd_not_yama (nrep mfuel efuel : Nat) (M : List Rowj) (h : ¬ expYama M mfuel)
    (c : Nat) :
    expNd nrep mfuel efuel M c
      = valAtIdx (rowAt (expandJS nrep mfuel efuel (expDg M mfuel)) 0) c := by
  unfold expNd
  rw [if_neg h]

/-! ## 山崎噴火の枝での枝の選び方

`yamakazi` かつ落差 `d = 0` のとき、`fujiSource` は極めて単純になる。
元の段はつねに行き先の段そのもので、「行の最後から取る」のは
置き換えの継ぎ目かつ `badRootHeight` より下の段のときだけである。 -/

theorem fujiSource_yama (P : FujiParams) (hy : P.yamakazi = true)
    (hd : P.cutHeight = P.badRootHeight) (i k : Nat) (isRep : Bool) :
    fujiSource P i k isRep = (k, isRep && decide (k < P.badRootHeight)) := by
  have hdz : P.cutHeight - P.badRootHeight = 0 := by omega
  unfold fujiSource
  dsimp only
  rw [hdz, hy]
  simp only [Nat.zero_mul, Nat.add_zero, Bool.not_true, Bool.false_and]
  rcases Nat.lt_or_ge k P.badRootHeight with h1 | h1
  · rw [if_pos h1]
    simp [h1]
  · rw [if_neg (Nat.not_lt.mpr h1)]
    rcases Nat.eq_or_lt_of_le h1 with h2 | h2
    · rw [if_pos (by omega)]
      simp [h2]
    · rw [if_neg (by omega), if_neg (by simp [show ¬ (k ≤ P.badRootHeight) by omega])]
      simp [show ¬ (k < P.badRootHeight) by omega]

/-- 落差が 0 なら、積む段の数は継ぎ目の高さそのもの（上りの判定によらない）。 -/
theorem kmaxAt_yama (M : List Rowj) (P : FujiParams) (i j ach af : Nat)
    (hd : P.cutHeight = P.badRootHeight) :
    kmaxAt M P i j ach af = seamHeightOf M j ach := by
  have hdz : P.cutHeight - P.badRootHeight = 0 := by omega
  unfold kmaxAt
  dsimp only
  rw [hdz, Nat.zero_mul, Nat.add_zero]
  split <;> rfl

/-! ## 元のセルの添字

`sourceIdx` は、`useLast` なら行の最後のセル、そうでなければ列 `j` のセルを指す。 -/

theorem sourceIdx_true (M : List Rowj) (sy j : Nat) :
    sourceIdx M sy j true = (rowAt M sy).size - 1 := rfl

/-- **列 `j` が段 `r` で生きていれば、`sourceIdx` はその列のセルを指す。** -/
theorem sourceIdx_col (S : Setting) (M : List Rowj) (hM : MtRep S M) (r j : Nat)
    (hr : r < M.length) (hrj : r ≤ j) (hj : j < S.n)
    (hlive : 0 < (rows S.tower.base r).value j) :
    ∃ h : sourceIdx M r j false < (rowAt M r).size,
      ((rowAt M r)[sourceIdx M r j false]'h).pos + r = j := by
  have hrep := rep_top S M hM r hr
  obtain ⟨m, hm, _, hcm⟩ := lookupPos_some (rowAt M r) r S.n _ hrep j hrj hj hlive
  have hs : sourceIdx M r j false = m := by
    show firstAtLeast (rowAt M r) (j - r) = m
    exact firstAtLeast_eq_of_mem (rowAt M r) hrep.posMono (j - r) m hm (by omega)
  rw [hs]
  exact ⟨hm, hcm⟩

/-- **列 `n−1` が段 `r` で生きていれば、行の最後のセルはその列である。** -/
theorem sourceIdx_last_col (S : Setting) (M : List Rowj) (hM : MtRep S M) (r j : Nat)
    (hr : r < M.length) (hn : 1 < S.n)
    (hlive : 0 < (rows S.tower.base r).value (S.n - 1)) :
    ∃ h : sourceIdx M r j true < (rowAt M r).size,
      ((rowAt M r)[sourceIdx M r j true]'h).pos + r = S.n - 1 := by
  have hrep := rep_top S M hM r hr
  have hrn : r ≤ S.n - 1 := by
    rcases Nat.lt_or_ge (S.n - 1) r with hx | hx
    · rw [rows_value_zero_of_lt S.tower.base r (S.n - 1) hx] at hlive
      omega
    · exact hx
  obtain ⟨m, hm, _, _⟩ :=
    lookupPos_some (rowAt M r) r S.n _ hrep (S.n - 1) hrn (by omega) hlive
  have hne : 0 < (rowAt M r).size := by omega
  have heq : lastCol (rowAt M r) r = S.n - 1 := (lastCol_eq_iff S M hM r hr hn).mpr hlive
  refine ⟨by simp only [sourceIdx_true]; omega, ?_⟩
  simp only [lastCol, dif_pos hne] at heq
  exact heq

/-! ## 元のセルの親を密表現で読む -/

theorem parRep_some (S : Setting) (M : List Rowj) (hM : MtRep S M) (r : Nat) (hr : r < M.length)
    (sx : Nat) (hsx : sx < (rowAt M r).size) (sp : Nat)
    (hpar : ((rowAt M r)[sx]'hsx).par = some sp) :
    ∃ hsp : sp < (rowAt M r).size,
      (rows S.tower.base r).forest.parent (((rowAt M r)[sx]'hsx).pos + r)
        = some (((rowAt M r)[sp]'hsp).pos + r) := by
  have hP : ParRep (rowAt M r) r (rows S.tower.base r).forest := by
    rw [rowAt_eq M r hr]
    exact (hM.rowRep r hr).2
  have h := hP _ (mem_of_getElem _ sx hsx)
  rw [hpar] at h
  exact h

theorem parRep_none (S : Setting) (M : List Rowj) (hM : MtRep S M) (r : Nat) (hr : r < M.length)
    (sx : Nat) (hsx : sx < (rowAt M r).size)
    (hpar : ((rowAt M r)[sx]'hsx).par = none) :
    (rows S.tower.base r).forest.parent (((rowAt M r)[sx]'hsx).pos + r) = none := by
  have hP : ParRep (rowAt M r) r (rows S.tower.base r).forest := by
    rw [rowAt_eq M r hr]
    exact (hM.rowRep r hr).2
  have h := hP _ (mem_of_getElem _ sx hsx)
  rw [hpar] at h
  exact h

/-- **積むセルの親の列は `parentCopy`（元の親の列）である。** -/
theorem fujiCell_par_parentCopy (S : Setting) (M : List Rowj) (hM : MtRep S M)
    (P : FujiParams) (cur : Rowj) (sy sx k i j shifts topVal : Nat)
    (hsy : sy ≤ k) (hry : sy < M.length) (C : CopyCoordinates.Context)
    (hy : C.y = P.badRootSeam) (hL : C.length = P.len) (p : Nat)
    (hp : (fujiCell M P cur sy sx k i j shifts topVal).par = some p) :
    ∃ (hp' : p < cur.size) (hsx : sx < (rowAt M sy).size) (q : Nat),
      (rows S.tower.base sy).forest.parent (((rowAt M sy)[sx]'hsx).pos + sy) = some q ∧
        (cur[p]'hp').pos + k = C.parentCopy shifts q := by
  obtain ⟨hp', hsx, sp, hspar, hsp, hcol⟩ :=
    fujiCell_par_col M P cur sy sx k i j shifts topVal hsy p hp
  obtain ⟨hsp', hF⟩ := parRep_some S M hM sy hry sx hsx sp hspar
  refine ⟨hp', hsx, ((rowAt M sy)[sp]'hsp').pos + sy, hF, ?_⟩
  rw [← js_shift_eq_parentCopy C shifts _, hy, hL]
  exact hcol

/-! ## 山崎噴火の枝で積むセル -/

/-- 山崎噴火の枝での枝の選択。上りでない列は置き換えの継ぎ目ではないので、
第 2 成分はどちらの枝でも同じになる。 -/
theorem fujiSourceAt_yama (P : FujiParams) (hy : P.yamakazi = true)
    (hd : P.cutHeight = P.badRootHeight) (i k : Nat) (isRep isAsc : Bool)
    (hra : isRep = true → isAsc = true) :
    fujiSourceAt P i k isRep isAsc = (k, isRep && decide (k < P.badRootHeight)) := by
  unfold fujiSourceAt
  cases hA : isAsc with
  | true => simpa using fujiSource_yama P hy hd i k isRep
  | false =>
      have hR : isRep = false := by
        cases hRp : isRep with
        | true => rw [hA] at hra; exact absurd (hra hRp) (by simp)
        | false => rfl
      simp [hR]

theorem fujiCellAt_yama (M : List Rowj) (P : FujiParams) (nd : Nat → Nat) (i j : Nat)
    (isRep isAsc : Bool) (res : List Rowj) (k : Nat) (hy : P.yamakazi = true)
    (hd : P.cutHeight = P.badRootHeight) (hra : isRep = true → isAsc = true) :
    fujiCellAt M P nd i j isRep isAsc res k
      = fujiCell M P (rowAt res k) k
          (sourceIdx M k j (isRep && decide (k < P.badRootHeight))) k i j
          (i - (if isRep then 1 else 0)) (nd (j + P.len * i)) := by
  unfold fujiCellAt
  dsimp only
  rw [fujiSourceAt_yama P hy hd i k isRep isAsc hra]

/-- 山崎噴火の枝での元の列。置き換えの継ぎ目で `badRootHeight` より下なら最後の列、
そうでなければ継ぎ目の列そのもの。 -/
def srcColYama (S : Setting) (P : FujiParams) (j k : Nat) (isRep : Bool) : Nat :=
  if isRep && decide (k < P.badRootHeight) then S.n - 1 else j

theorem sourceIdx_yama_col (S : Setting) (M : List Rowj) (hM : MtRep S M)
    (P : FujiParams) (j k : Nat) (isRep : Bool) (hk : k < M.length) (hn : 1 < S.n)
    (hkj : k ≤ j) (hj : j < S.n)
    (hlive : 0 < (rows S.tower.base k).value j)
    (hbh : P.badRootHeight ≤ height S.tower.base (S.n - 1)) :
    ∃ h : sourceIdx M k j (isRep && decide (k < P.badRootHeight)) < (rowAt M k).size,
      ((rowAt M k)[sourceIdx M k j (isRep && decide (k < P.badRootHeight))]'h).pos + k
        = srcColYama S P j k isRep := by
  unfold srcColYama
  cases hb : isRep && decide (k < P.badRootHeight) with
  | true =>
      rw [if_pos rfl]
      have hkb : k < P.badRootHeight := by
        have h2 : isRep = true ∧ (k < P.badRootHeight) := by simpa using hb
        exact h2.2
      exact sourceIdx_last_col S M hM k j hk hn
        ((live_iff_le_height S.tower.base (S.tower.hpos (S.n - 1)) k).mpr (by omega))
  | false =>
      rw [if_neg (by simp)]
      exact sourceIdx_col S M hM k j hk hkj hj hlive

/-- **山崎噴火の枝で積むセルの親の列。** -/
theorem fujiCellAt_par_yama (S : Setting) (M : List Rowj) (hM : MtRep S M)
    (P : FujiParams) (nd : Nat → Nat) (i j : Nat) (isRep isAsc : Bool) (res : List Rowj) (k : Nat)
    (hy : P.yamakazi = true) (hd : P.cutHeight = P.badRootHeight)
    (hk : k < M.length) (hn : 1 < S.n) (hkj : k ≤ j) (hj : j < S.n)
    (hlive : 0 < (rows S.tower.base k).value j)
    (hbh : P.badRootHeight ≤ height S.tower.base (S.n - 1))
    (hra : isRep = true → isAsc = true)
    (C : CopyCoordinates.Context) (hcy : C.y = P.badRootSeam) (hcL : C.length = P.len)
    (p : Nat) (hp : (fujiCellAt M P nd i j isRep isAsc res k).par = some p) :
    ∃ (hp' : p < (rowAt res k).size) (q : Nat),
      (rows S.tower.base k).forest.parent (srcColYama S P j k isRep) = some q ∧
        ((rowAt res k)[p]'hp').pos + k
          = C.parentCopy (i - (if isRep then 1 else 0)) q := by
  rw [fujiCellAt_yama M P nd i j isRep isAsc res k hy hd hra] at hp
  obtain ⟨hp', hsx, q, hq, hcol⟩ :=
    fujiCell_par_parentCopy S M hM P (rowAt res k) k
      (sourceIdx M k j (isRep && decide (k < P.badRootHeight))) k i j
      (i - (if isRep then 1 else 0)) (nd (j + P.len * i)) (Nat.le_refl _) hk C hcy hcL p hp
  obtain ⟨hsx', hcolsrc⟩ :=
    sourceIdx_yama_col S M hM P j k isRep hk hn hkj hj hlive hbh
  rw [hcolsrc] at hq
  exact ⟨hp', q, hq, hcol⟩

/-- **根 `y` の親は `y` より左にあるので、桁上げは効かない。** 原文が
`level ≤ r` の場合に `parentCopy` を掛けないのと、JS が掛けるのとが一致する理由。 -/
theorem parentCopy_of_parent_y (C : CopyCoordinates.Context) (F : ParentForest) (q : Nat)
    (h : F.parent C.y = some q) (b : Nat) : C.parentCopy b q = q := by
  have hlt := F.parent_left h
  unfold CopyCoordinates.Context.parentCopy
  rw [if_pos hlt]

/-! ## 子を切ったあとの段のセル -/

theorem size_rowAt_cutChild (M : List Rowj) (cutH m : Nat)
    (h : m < (cutChild M cutH).length) :
    (rowAt (cutChild M cutH) m).size
      = if m < cutH + 1 then (rowAt M m).size - 1 else (rowAt M m).size := by
  rw [rowAt_cutChild M cutH m h]
  split
  · rw [Array.size_pop]
  · rfl

/-- 残ったセルは元のセルそのもの。 -/
theorem rowAt_cutChild_getElem? (M : List Rowj) (cutH m t : Nat)
    (h : m < (cutChild M cutH).length) (ht : t < (rowAt (cutChild M cutH) m).size) :
    (rowAt (cutChild M cutH) m)[t]? = (rowAt M m)[t]? := by
  have hrow := rowAt_cutChild M cutH m h
  rcases Nat.lt_or_ge m (cutH + 1) with hm | hm
  · rw [if_pos hm] at hrow
    rw [hrow] at ht ⊢
    have hts : t < (rowAt M m).size := by
      rw [Array.size_pop] at ht
      omega
    rw [Array.getElem?_eq_getElem ht, Array.getElem?_eq_getElem hts, Array.getElem_pop]
  · rw [if_neg (by omega)] at hrow
    rw [hrow]

/-! ## 継ぎ目の列と原文の座標

JS の継ぎ目 `j`（`y ≤ j < x`）は列 `j + L*i` に写る。原文の `source` / `block` は
`j > y` なら `(j, i)`、`j = y` なら `(x, i−1)` を返す。`j = y` が
「retained seam」（`source = x`）にあたる。 -/

theorem coord_source_block (C : CopyCoordinates.Context) (j i : Nat)
    (hj1 : C.y < j) (hj2 : j < C.x) :
    C.source (j + C.length * i) = j ∧ C.block (j + C.length * i) = i := by
  have hL := C.root_add_length
  have hLp := C.length_pos
  have he : j + C.length * i - C.y - 1 = (j - C.y - 1) + C.length * i := by omega
  have hlt : j - C.y - 1 < C.length := by omega
  constructor
  · unfold CopyCoordinates.Context.source
    rw [he, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
    omega
  · unfold CopyCoordinates.Context.block
    rw [he, Nat.add_mul_div_left _ _ hLp, Nat.div_eq_of_lt hlt]
    omega

theorem coord_source_block_seam (C : CopyCoordinates.Context) (i : Nat) (hi : 0 < i) :
    C.source (C.y + C.length * i) = C.x ∧ C.block (C.y + C.length * i) = i - 1 := by
  have hL := C.root_add_length
  have hLp := C.length_pos
  have he : C.y + C.length * i - C.y - 1 = (C.length - 1) + C.length * (i - 1) := by
    obtain ⟨m, hm⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
    subst hm
    have hms : C.length * (m + 1) = C.length * m + C.length := Nat.mul_succ _ _
    simp only [Nat.add_sub_cancel]
    omega
  have hlt : C.length - 1 < C.length := by omega
  constructor
  · unfold CopyCoordinates.Context.source
    rw [he, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
    omega
  · unfold CopyCoordinates.Context.block
    rw [he, Nat.add_mul_div_left _ _ hLp, Nat.div_eq_of_lt hlt]
    omega

/-! ## 親の添字は自分より前

積むセルの親は「今の段」を `lookupPos` で引いた添字なので、必ずその時点の
大きさより小さい。積む場所はちょうどその大きさなので、親は自分より前になる。 -/

/-- どの段でも、親の添字は自分より前。 -/
def ParLt (res : List Rowj) : Prop :=
  ∀ (r t : Nat) (d : Cell), (rowAt res r)[t]? = some d → ∀ p, d.par = some p → p < t

theorem ParLt.dep {Rs : List Rowj} (h : ParLt Rs) :
    ∀ (r i : Nat) (hi : i < (rowAt Rs r).size) (p : Nat),
      ((rowAt Rs r)[i]'hi).par = some p → p < i :=
  fun r i hi p hp => h r i _ (Array.getElem?_eq_getElem hi) p hp

theorem fujiCell_par_lt (M : List Rowj) (P : FujiParams) (cur : Rowj)
    (sy sx k i j shifts topVal p : Nat)
    (hp : (fujiCell M P cur sy sx k i j shifts topVal).par = some p) : p < cur.size := by
  rw [fujiCell_par] at hp
  cases hq : parentPos M P sy sx k shifts with
  | none => rw [hq] at hp; exact absurd hp (by simp)
  | some q =>
      rw [hq] at hp
      dsimp only at hp
      obtain ⟨h1, _⟩ := lookupPos_some_iff cur q p hp
      exact h1

theorem fujiCellAt_par_lt (M : List Rowj) (P : FujiParams) (nd : Nat → Nat) (i j : Nat)
    (isRep isAsc : Bool) (res : List Rowj) (k p : Nat)
    (hp : (fujiCellAt M P nd i j isRep isAsc res k).par = some p) : p < (rowAt res k).size :=
  fujiCell_par_lt M P (rowAt res k) _ _ k i j _ _ p hp

theorem parLt_fujiRows (M : List Rowj) (P : FujiParams) (nd : Nat → Nat) (i j : Nat)
    (isRep isAsc : Bool) (kmax : Nat) (res : List Rowj) (h : ParLt res) :
    ParLt (fujiRows M P nd i j isRep isAsc kmax res) := by
  intro r t d hd p hp
  rw [rowAt_fujiRows] at hd
  split at hd
  · rw [Array.getElem?_push] at hd
    split at hd
    · next hte =>
        have he := Option.some.inj hd
        rw [← he] at hp
        have h2 := fujiCellAt_par_lt M P nd i j isRep isAsc res r p hp
        omega
    · exact h r t d hd p hp
  · exact h r t d hd p hp

theorem parLt_fujiSeams (M : List Rowj) (P : FujiParams) (nd : Nat → Nat) (i ach af : Nat) :
    ∀ (t : Nat) (res : List Rowj), ParLt res → ParLt (fujiSeams M P nd i ach af t res) := by
  intro t
  induction t with
  | zero => intro res h; exact h
  | succ t ih =>
      intro res h
      rw [fujiSeams_succ]
      exact parLt_fujiRows _ _ _ _ _ _ _ _ _ (ih res h)

theorem parLt_fujiIters (M : List Rowj) (P : FujiParams) (nd : Nat → Nat) (ach af : Nat) :
    ∀ (n : Nat) (res : List Rowj), ParLt res → ParLt (fujiIters M P nd ach af n res) := by
  intro n
  induction n with
  | zero => intro res h; exact h
  | succ n ih =>
      intro res h
      rw [fujiIters_succ]
      exact parLt_fujiSeams _ _ _ _ _ _ _ _ (ih res h)

/-- 元の山では、親の添字は自分より前（`par_index_lt`）。 -/
theorem parLt_of_mtRep (S : Setting) (M : List Rowj) (hM : MtRep S M) : ParLt M := by
  intro r t d hd p hp
  have hts : t < (rowAt M r).size := lt_size_of_getElem? hd
  have hdt : (rowAt M r)[t]'hts = d := by
    rw [Array.getElem?_eq_getElem hts] at hd
    exact Option.some.inj hd
  rcases Nat.lt_or_ge r M.length with hr | hr
  · have := par_index_lt S M hM r hr t p hts (by rw [hdt]; exact hp)
    exact this.2
  · exfalso
    rw [rowAt_of_ge M r hr] at hts
    simp at hts

/-- 子を切っても親の添字は自分より前のまま。 -/
theorem parLt_cutChild (M : List Rowj) (cutH : Nat) (h : ParLt M) :
    ParLt (cutChild M cutH) := by
  intro r t d hd p hp
  have hts : t < (rowAt (cutChild M cutH) r).size := lt_size_of_getElem? hd
  rcases Nat.lt_or_ge r (cutChild M cutH).length with hr | hr
  · rw [rowAt_cutChild_getElem? M cutH r t hr hts] at hd
    exact h r t d hd p hp
  · exfalso
    rw [rowAt_of_ge _ r hr] at hts
    simp at hts

/-! ## 子を切ったあとの段の性質 -/

theorem posMono_pop (row : Rowj) (h : PosMono row) : PosMono row.pop := by
  intro p q hp hq hpq
  have hp' : p < row.size := by
    rw [Array.size_pop] at hp
    omega
  have hq' : q < row.size := by
    rw [Array.size_pop] at hq
    omega
  rw [Array.getElem_pop, Array.getElem_pop]
  exact h p q hp' hq' hpq

theorem rowsMono_cutChild (M : List Rowj) (cutH : Nat) (h : RowsMono M) :
    RowsMono (cutChild M cutH) := by
  intro m
  rcases Nat.lt_or_ge m (cutChild M cutH).length with hm | hm
  · rw [rowAt_cutChild M cutH m hm]
    split
    · exact posMono_pop _ (h m)
    · exact h m
  · rw [rowAt_of_ge _ m hm]
    intro p q hp _ _
    simp at hp

theorem rowsMono_of_mtRep (S : Setting) (M : List Rowj) (hM : MtRep S M) : RowsMono M := by
  intro m
  rcases Nat.lt_or_ge m M.length with hm | hm
  · exact (rep_top S M hM m hm).posMono
  · rw [rowAt_of_ge M m hm]
    intro p q hp _ _
    simp at hp

theorem size_rowAt_cutChild_zero (S : Setting) (M : List Rowj) (hM : MtRep S M) (cutH : Nat)
    (h0 : 0 < (cutChild M cutH).length) :
    (rowAt (cutChild M cutH) 0).size = S.n - 1 := by
  rw [size_rowAt_cutChild M cutH 0 h0, if_pos (by omega), hM.size0]

/-- **子を切ると列 `n−1` が消える。** 残るセルの列はすべて `n−1` より小さい。 -/
theorem colLt_cutChild (S : Setting) (M : List Rowj) (hM : MtRep S M) (cutH : Nat)
    (hn : 1 < S.n) (hcut : height S.tower.base (S.n - 1) ≤ cutH) :
    ColLt (cutChild M cutH) (S.n - 1) := by
  intro m t d hd
  have hts : t < (rowAt (cutChild M cutH) m).size := lt_size_of_getElem? hd
  rcases Nat.lt_or_ge m (cutChild M cutH).length with hm | hm
  · rw [rowAt_cutChild_getElem? M cutH m t hm hts] at hd
    have htM : t < (rowAt M m).size := lt_size_of_getElem? hd
    have hdt : (rowAt M m)[t]'htM = d := by
      rw [Array.getElem?_eq_getElem htM] at hd
      exact Option.some.inj hd
    have hmM : m < M.length := by
      rcases Nat.lt_or_ge m M.length with h1 | h1
      · exact h1
      · exfalso
        rw [rowAt_of_ge M m h1] at htM
        simp at htM
    have hrep := rep_top S M hM m hmM
    have hb := hrep.bound d (by rw [← hdt]; exact mem_of_getElem _ t htM)
    rcases Decidable.em (d.pos + m = S.n - 1) with heq | hne
    · exfalso
      have hlive : 0 < (rows S.tower.base m).value (S.n - 1) := by
        have h1 := hrep.val d (by rw [← hdt]; exact mem_of_getElem _ t htM)
        have h2 := hrep.live d (by rw [← hdt]; exact mem_of_getElem _ t htM)
        rw [heq] at h1
        omega
      have hmh : m ≤ height S.tower.base (S.n - 1) :=
        (live_iff_le_height S.tower.base (S.tower.hpos (S.n - 1)) m).mp hlive
      have hsz := size_rowAt_cutChild M cutH m hm
      rw [if_pos (by omega)] at hsz
      have hlast : lastCol (rowAt M m) m = S.n - 1 := (lastCol_eq_iff S M hM m hmM hn).mpr hlive
      have hne0 : 0 < (rowAt M m).size := by omega
      simp only [lastCol, dif_pos hne0] at hlast
      have hlt : t < (rowAt M m).size - 1 := by omega
      have := hrep.posMono t ((rowAt M m).size - 1) htM (by omega) (by omega)
      rw [hdt] at this
      omega
    · omega
  · exfalso
    rw [rowAt_of_ge _ m hm] at hts
    simp at hts

/-- 子を切っても段の数は 1 つしか減らない。 -/
theorem cutChild_length_ge (M : List Rowj) (cutH : Nat) :
    M.length - 1 ≤ (cutChild M cutH).length := by
  have hlen := popFold_length (cutH + 1) M
  rw [cutChild_eq]
  split
  · rw [List.length_take]
    simp only [Nat.min_def]
    split <;> omega
  · omega

/-- **子を切ったあとの行 0 は `0 … n−2` を覆う。** -/
theorem hasCol_cutChild_zero (S : Setting) (M : List Rowj) (hM : MtRep S M) (cutH : Nat)
    (h0 : 0 < (cutChild M cutH).length) (hM0 : 0 < M.length) (c : Nat) (hc : c < S.n - 1) :
    HasCol (cutChild M cutH) 0 c := by
  have hsz := size_rowAt_cutChild_zero S M hM cutH h0
  have hcs : c < (rowAt (cutChild M cutH) 0).size := by omega
  have hcM : c < (rowAt M 0).size := by rw [hM.size0]; omega
  refine ⟨c, (rowAt (cutChild M cutH) 0)[c]'hcs, Array.getElem?_eq_getElem hcs, ?_⟩
  have hget := rowAt_cutChild_getElem? M cutH 0 c h0 hcs
  rw [Array.getElem?_eq_getElem hcs, Array.getElem?_eq_getElem hcM] at hget
  rw [Option.some.inj hget]
  have := pos_eq_index (rowAt M 0) S.n _ (rep_top S M hM 0 hM0) hM.size0 c hcM
  omega

/-! ## 継ぎ目の高さの上限（仮定なし）

`hasCol M r j` が真なら、段 `r` に列 `j` のセルがあるので `r ≤ j` である
（position は非負）。したがって継ぎ目の高さはつねに `j + 1` 以下。 -/

theorem hasCol_le (M : List Rowj) (r j : Nat) (h : hasCol M r j = true) : r ≤ j := by
  unfold hasCol at h
  cases hlk : lookupPos (rowAt M r) (j - r) with
  | none => rw [hlk] at h; exact absurd h (by simp)
  | some m =>
      rw [hlk] at h
      dsimp only at h
      split at h
      · next hm =>
          have := (beq_iff_eq).mp h
          omega
      · exact absurd h (by simp)

/-- **継ぎ目の高さはつねに `j + 1` 以下。** -/
theorem seamHeightOf_le_col (M : List Rowj) (j : Nat) :
    ∀ hi : Nat, seamHeightOf M j hi ≤ j + 1 := by
  intro hi
  induction hi with
  | zero => exact Nat.zero_le _
  | succ h ih =>
      rw [seamHeightOf]
      split
      · next hc => have := hasCol_le M h j hc; omega
      · exact ih

/-- **積む段の数の上限（継ぎ目の高さの仮定なし）。** 残る仮定は `d ≤ len` だけ。 -/
theorem kmaxAt_le' (M : List Rowj) (P : FujiParams) (i j ach af : Nat)
    (hd : P.cutHeight - P.badRootHeight ≤ P.len) :
    kmaxAt M P i j ach af ≤ j + P.len * i + 1 :=
  kmaxAt_le M P i j ach af (seamHeightOf_le_col M j ach) hd

/-- 山崎噴火の枝では仮定なしで成り立つ。 -/
theorem kmaxAt_le_yama' (M : List Rowj) (P : FujiParams) (i j ach af : Nat)
    (hd : P.cutHeight = P.badRootHeight) :
    kmaxAt M P i j ach af ≤ j + P.len * i + 1 :=
  kmaxAt_le' M P i j ach af (by omega)

/-! ## 積む段の数は正 -/

theorem seamHeightOf_pos_of_hasCol (M : List Rowj) (j r : Nat) :
    ∀ hi, r < hi → hasCol M r j = true → 0 < seamHeightOf M j hi := by
  intro hi
  induction hi with
  | zero => intro h; omega
  | succ h ih =>
      intro hr hc
      rw [seamHeightOf]
      split
      · omega
      · next hnc =>
          have hrh : r < h := by
            rcases Nat.lt_or_ge r h with h1 | h1
            · exact h1
            · exfalso
              have : r = h := by omega
              rw [this] at hc
              exact hnc hc
          exact ih hrh hc

/-- 行 0 にはすべての列がある。 -/
theorem hasCol_zero (S : Setting) (M : List Rowj) (hM : MtRep S M) (h0 : 0 < M.length)
    (j : Nat) (hj : j < S.n) : hasCol M 0 j = true := by
  refine (hasCol_iff S M hM 0 j h0 hj).mpr ?_
  exact S.tower.hpos j

/-- **積む段の数は正。** -/
theorem kmaxAt_pos' (S : Setting) (M : List Rowj) (hM : MtRep S M) (h0 : 0 < M.length)
    (P : FujiParams) (i j ach af : Nat) (hj : j < S.n) (hach : 0 < ach) :
    0 < kmaxAt M P i j ach af :=
  kmaxAt_pos M P i j ach af
    (seamHeightOf_pos_of_hasCol M j 0 ach hach (hasCol_zero S M hM h0 j hj))

/-! ## 末尾の空段を落とす

`dropEmptyTop` は末尾の空段だけを落とすので、残った段は元のままである。 -/

theorem take_len_cons (a : Rowj) (t : List Rowj) :
    ((a :: t).take t.length).length = t.length := by
  simp only [List.length_take, List.length_cons, Nat.min_def]
  split <;> omega

theorem dropEmptyTop_length_le (n : Nat) : ∀ (L : List Rowj), L.length ≤ n →
    (dropEmptyTop L).length ≤ L.length := by
  induction n with
  | zero =>
      intro L hL
      rcases L with _ | ⟨a, t⟩
      · rw [dropEmptyTop_nil]
        exact Nat.le_refl _
      · exact absurd hL (by simp)
  | succ n ih =>
      intro L hL
      rcases L with _ | ⟨a, t⟩
      · rw [dropEmptyTop_nil]
        exact Nat.le_refl _
      · rcases Decidable.em (((a :: t).getD t.length #[]).size = 0) with hc | hc
        · have hd : dropEmptyTop (a :: t) = dropEmptyTop ((a :: t).take t.length) := by
            rw [dropEmptyTop, if_pos hc]
          have hlen := take_len_cons a t
          have h1 := ih ((a :: t).take t.length) (by simp only [List.length_cons] at hL; omega)
          rw [hd]
          simp only [List.length_cons]
          omega
        · have hd : dropEmptyTop (a :: t) = a :: t := by
            rw [dropEmptyTop, if_neg hc]
          rw [hd]
          exact Nat.le_refl _

theorem rowAt_dropEmptyTop (n : Nat) : ∀ (L : List Rowj) (m : Nat), L.length ≤ n →
    m < (dropEmptyTop L).length → rowAt (dropEmptyTop L) m = rowAt L m := by
  induction n with
  | zero =>
      intro L m hL _
      rcases L with _ | ⟨a, t⟩
      · rw [dropEmptyTop_nil]
      · exact absurd hL (by simp)
  | succ n ih =>
      intro L m hL hm
      rcases L with _ | ⟨a, t⟩
      · rw [dropEmptyTop_nil]
      · rcases Decidable.em (((a :: t).getD t.length #[]).size = 0) with hc | hc
        · have hd : dropEmptyTop (a :: t) = dropEmptyTop ((a :: t).take t.length) := by
            rw [dropEmptyTop, if_pos hc]
          have hlen := take_len_cons a t
          have hle := dropEmptyTop_length_le n ((a :: t).take t.length)
            (by simp only [List.length_cons] at hL; omega)
          rw [hd] at hm ⊢
          have hmt : m < t.length := by omega
          rw [ih ((a :: t).take t.length) m (by simp only [List.length_cons] at hL; omega) hm,
            rowAt_take_lt _ _ _ hmt]
        · have hd : dropEmptyTop (a :: t) = a :: t := by
            rw [dropEmptyTop, if_neg hc]
          rw [hd]

/-- **空でない段は残る。** -/
theorem lt_dropEmptyTop_length (n : Nat) : ∀ (L : List Rowj) (m : Nat), L.length ≤ n →
    m < L.length → 0 < (rowAt L m).size → m < (dropEmptyTop L).length := by
  induction n with
  | zero =>
      intro L m hL hm _
      rcases L with _ | ⟨a, t⟩
      · simp at hm
      · exact absurd hL (by simp)
  | succ n ih =>
      intro L m hL hm hs
      rcases L with _ | ⟨a, t⟩
      · simp at hm
      · rcases Decidable.em (((a :: t).getD t.length #[]).size = 0) with hc | hc
        · have hd : dropEmptyTop (a :: t) = dropEmptyTop ((a :: t).take t.length) := by
            rw [dropEmptyTop, if_pos hc]
          have hlen := take_len_cons a t
          have hz : (rowAt (a :: t) t.length).size = 0 := hc
          have hmt : m < t.length := by
            rcases Nat.lt_or_ge m t.length with h | h
            · exact h
            · exfalso
              have hme : m = t.length := by simp only [List.length_cons] at hm; omega
              rw [hme] at hs
              omega
          rw [hd]
          refine ih ((a :: t).take t.length) m
            (by simp only [List.length_cons] at hL; omega) (by omega) ?_
          rw [rowAt_take_lt _ _ _ hmt]
          exact hs
        · have hd : dropEmptyTop (a :: t) = a :: t := by
            rw [dropEmptyTop, if_neg hc]
          rw [hd]
          exact hm

/-- 空段落としのあとにあるセルは元にもある。 -/
theorem getElem?_dropEmptyTop (L : List Rowj) (m t : Nat) (d : Cell)
    (h : (rowAt (dropEmptyTop L) m)[t]? = some d) : (rowAt L m)[t]? = some d := by
  have hts : t < (rowAt (dropEmptyTop L) m).size := lt_size_of_getElem? h
  have hm : m < (dropEmptyTop L).length := by
    rcases Nat.lt_or_ge m (dropEmptyTop L).length with h1 | h1
    · exact h1
    · exfalso
      rw [rowAt_of_ge _ m h1] at hts
      simp at hts
  rwa [rowAt_dropEmptyTop L.length L m (Nat.le_refl _) hm] at h

/-- 元にある列は空段落としのあとにもある。 -/
theorem hasCol_dropEmptyTop (L : List Rowj) (m c : Nat) (h : HasCol L m c) :
    HasCol (dropEmptyTop L) m c := by
  obtain ⟨t, d, hd, hdc⟩ := h
  have hts : t < (rowAt L m).size := lt_size_of_getElem? hd
  have hmL : m < L.length := by
    rcases Nat.lt_or_ge m L.length with h1 | h1
    · exact h1
    · exfalso
      rw [rowAt_of_ge L m h1] at hts
      simp at hts
  have hm : m < (dropEmptyTop L).length :=
    lt_dropEmptyTop_length L.length L m (Nat.le_refl _) hmL (by omega)
  refine ⟨t, d, ?_, hdc⟩
  rw [rowAt_dropEmptyTop L.length L m (Nat.le_refl _) hm]
  exact hd

theorem rowsMono_dropEmptyTop (L : List Rowj) (h : RowsMono L) : RowsMono (dropEmptyTop L) := by
  intro m
  rcases Nat.lt_or_ge m (dropEmptyTop L).length with h1 | h1
  · rw [rowAt_dropEmptyTop L.length L m (Nat.le_refl _) h1]
    exact h m
  · rw [rowAt_of_ge _ m h1]
    intro p q hp _ _
    simp at hp

theorem parLt_dropEmptyTop (L : List Rowj) (h : ParLt L) : ParLt (dropEmptyTop L) :=
  fun r t d hd p hp => h r t d (getElem?_dropEmptyTop L r t d hd) p hp

/-- **子を切ったあとも、列 `n−1` より左の生きた列は残る。** -/
theorem hasCol_cutChild (S : Setting) (M : List Rowj) (hM : MtRep S M)
    (hn : 1 < S.n) (cutH : Nat) (hcut : cutH = height S.tower.base (S.n - 1))
    (m c : Nat) (hc : c < S.n - 1) (hlive : m ≤ height S.tower.base c)
    (hm : m < (cutChild M cutH).length) :
    HasCol (cutChild M cutH) m c := by
  have hmM : m < M.length := by
    have := cutChild_length_le M cutH
    omega
  have hhs := height_le_self' S.tower.base S.tower.hpos c
  have hrep := rep_top S M hM m hmM
  have hlivec : 0 < (rows S.tower.base m).value c :=
    (live_iff_le_height S.tower.base (S.tower.hpos c) m).mpr hlive
  obtain ⟨x1, hx1, hcx1⟩ := hrep.cover c (by omega) (by omega) hlivec
  obtain ⟨t, ht, het⟩ := getElem_of_mem _ hx1
  rcases Nat.lt_or_ge m (cutH + 1) with hmc | hmc
  · have hlast : 0 < (rows S.tower.base m).value (S.n - 1) :=
      (live_iff_le_height S.tower.base (S.tower.hpos (S.n - 1)) m).mpr (by omega)
    have hne : 0 < (rowAt M m).size := by omega
    have hlt1 : (rowAt M m).size - 1 < (rowAt M m).size := by omega
    have hlc : ((rowAt M m)[(rowAt M m).size - 1]'hlt1).pos + m = S.n - 1 := by
      have h := (lastCol_eq_iff S M hM m hmM hn).mpr hlast
      simp only [lastCol, dif_pos hne] at h
      exact h
    have htlt : t < (rowAt M m).size - 1 := by
      rcases Nat.lt_or_ge t ((rowAt M m).size - 1) with h | h
      · exact h
      · exfalso
        have hte : t = (rowAt M m).size - 1 := by omega
        have hxx : x1 = (rowAt M m)[(rowAt M m).size - 1]'hlt1 := by
          rw [← het]
          exact getElem_congr_idx (rowAt M m) t ((rowAt M m).size - 1) ht hlt1 hte
        rw [hxx] at hcx1
        omega
    have hrow := rowAt_cutChild M cutH m hm
    rw [if_pos hmc] at hrow
    refine ⟨t, x1, ?_, hcx1⟩
    rw [hrow]
    have htp : t < (rowAt M m).pop.size := by rw [Array.size_pop]; omega
    rw [Array.getElem?_eq_getElem htp, Array.getElem_pop, het]
  · have hrow := rowAt_cutChild M cutH m hm
    rw [if_neg (by omega)] at hrow
    refine ⟨t, x1, ?_, hcx1⟩
    rw [hrow, Array.getElem?_eq_getElem ht, het]

/-! ## 列の分解と辞書式順

コピーの列 `j + L*i`（`y ≤ j < x`、`L = x − y`）は `(i, j)` の辞書式順で
真に増える。逆に `x` 以上の列はこの形に一意に分解できる。 -/

theorem col_decomp (y x L n c : Nat) (hL : L = x - y) (hLp : 0 < L) (hyx : y < x)
    (hc1 : x ≤ c) (hc2 : c < x + L * n) :
    ∃ i j, 0 < i ∧ i ≤ n ∧ y ≤ j ∧ j < x ∧ c = j + L * i := by
  obtain ⟨e, hev⟩ : ∃ e, c - x = e := ⟨_, rfl⟩
  have helt : e < L * n := by omega
  obtain ⟨q, hqv⟩ : ∃ q, e / L = q := ⟨_, rfl⟩
  obtain ⟨r, hrv⟩ : ∃ r, e % L = r := ⟨_, rfl⟩
  have hdm : L * q + r = e := by
    rw [← hqv, ← hrv]
    exact Nat.div_add_mod e L
  have hmod : r < L := by
    rw [← hrv]
    exact Nat.mod_lt e hLp
  have hq : q < n := by
    rcases Nat.lt_or_ge q n with hx | hx
    · exact hx
    · exfalso
      have h2 : L * n ≤ L * q := Nat.mul_le_mul_left L hx
      omega
  have hmul : L * (q + 1) = L * q + L := Nat.mul_succ _ _
  exact ⟨q + 1, y + r, by omega, by omega, by omega, by omega, by omega⟩

theorem col_lt_lex (y x L : Nat) (hL : L = x - y) (hyx : y < x)
    (j1 i1 j2 i2 : Nat) (h1 : y ≤ j1) (_h1' : j1 < x) (_h2 : y ≤ j2) (h2' : j2 < x)
    (hlt : j1 + L * i1 < j2 + L * i2) : i1 < i2 ∨ (i1 = i2 ∧ j1 < j2) := by
  rcases Nat.lt_or_ge i1 i2 with h | h
  · exact Or.inl h
  · rcases Nat.eq_or_lt_of_le h with he | hgt
    · subst he
      exact Or.inr ⟨rfl, by omega⟩
    · exfalso
      have hmul : L * (i2 + 1) ≤ L * i1 := Nat.mul_le_mul_left L hgt
      have hexp : L * (i2 + 1) = L * i2 + L := Nat.mul_succ _ _
      omega

/-! ## 山では高さは列番号以下

どの `RowMountain` でも `height c ≤ c` である。親は真に左へ動き、親は自分の段まで
生きているので、段を 1 つ上がるごとに列が 1 つ以上左へ寄るからである。 -/

theorem rowMountain_height_le (M : RootGeometry.RowMountain) : ∀ c, M.height c ≤ c := by
  intro c
  induction c using Nat.strongRecOn with
  | ind c ih =>
      rcases Nat.eq_zero_or_pos (M.height c) with h | h
      · omega
      · obtain ⟨p, hp⟩ := M.parent_exists (M.height c - 1) c (by omega)
        have hpc : p < c := (M.row _).parent_left hp
        have hend : M.height c - 1 ≤ M.height p := M.parent_endpoint hp
        have := ih p hpc
        omega

/-! ## 積むセルの値 -/

theorem fujiCell_val_of_par_none (M : List Rowj) (P : FujiParams) (cur : Rowj)
    (sy sx k i j shifts topVal : Nat)
    (h : (fujiCell M P cur sy sx k i j shifts topVal).par = none) :
    (fujiCell M P cur sy sx k i j shifts topVal).val = topVal := by
  rw [fujiCell_val, h]
  rfl

theorem fujiCell_val_of_par_some (M : List Rowj) (P : FujiParams) (cur : Rowj)
    (sy sx k i j shifts topVal p : Nat)
    (h : (fujiCell M P cur sy sx k i j shifts topVal).par = some p) :
    (fujiCell M P cur sy sx k i j shifts topVal).val = 0 := by
  rw [fujiCell_val, h]
  rfl

theorem fujiCellAt_val_of_par_none (M : List Rowj) (P : FujiParams) (nd : Nat → Nat)
    (i j : Nat) (isRep isAsc : Bool) (res : List Rowj) (k : Nat)
    (h : (fujiCellAt M P nd i j isRep isAsc res k).par = none) :
    (fujiCellAt M P nd i j isRep isAsc res k).val = nd (j + P.len * i) :=
  fujiCell_val_of_par_none M P (rowAt res k) _ _ k i j _ _ h

theorem fujiCellAt_val_of_par_some (M : List Rowj) (P : FujiParams) (nd : Nat → Nat)
    (i j : Nat) (isRep isAsc : Bool) (res : List Rowj) (k p : Nat)
    (h : (fujiCellAt M P nd i j isRep isAsc res k).par = some p) :
    (fujiCellAt M P nd i j isRep isAsc res k).val = 0 :=
  fujiCell_val_of_par_some M P (rowAt res k) _ _ k i j _ _ p h

/-! ## 密表現に親があれば疎配列にも親がある -/

theorem parRep_some_of_forest (S : Setting) (M : List Rowj) (hM : MtRep S M) (r : Nat)
    (hr : r < M.length) (sx : Nat) (hsx : sx < (rowAt M r).size) (q : Nat)
    (hF : (rows S.tower.base r).forest.parent (((rowAt M r)[sx]'hsx).pos + r) = some q) :
    ∃ sp, ((rowAt M r)[sx]'hsx).par = some sp := by
  cases hp : ((rowAt M r)[sx]'hsx).par with
  | none =>
      exfalso
      have h := parRep_none S M hM r hr sx hsx hp
      rw [h] at hF
      exact absurd hF (by simp)
  | some sp => exact ⟨sp, rfl⟩

/-- **親の位置は負にならない。** 密表現に親があり、その新しい列が段より右なら、
JS の `parentPos` はその位置を返す。 -/
theorem parentPos_some (S : Setting) (M : List Rowj) (hM : MtRep S M) (P : FujiParams)
    (sy sx k shifts q : Nat) (hr : sy < M.length) (hsx : sx < (rowAt M sy).size)
    (hsy : sy ≤ k)
    (hF : (rows S.tower.base sy).forest.parent (((rowAt M sy)[sx]'hsx).pos + sy) = some q)
    (hge : k ≤ q + (if P.badRootSeam ≤ q then shifts * P.len else 0)) :
    parentPos M P sy sx k shifts
      = some (q + (if P.badRootSeam ≤ q then shifts * P.len else 0) - k) := by
  obtain ⟨sp, hsp⟩ := parRep_some_of_forest S M hM sy hr sx hsx q hF
  obtain ⟨hsp', hFsp⟩ := parRep_some S M hM sy hr sx hsx sp hsp
  rw [hF] at hFsp
  have hq : ((rowAt M sy)[sp]'hsp').pos + sy = q := (Option.some.inj hFsp).symm
  obtain ⟨pp, hpp⟩ : ∃ pp, ((rowAt M sy)[sp]'hsp').pos = pp := ⟨_, rfl⟩
  rw [hpp] at hq
  unfold parentPos
  try dsimp only
  rw [dif_pos hsx, hsp]
  try dsimp only
  rw [dif_pos hsp', hpp]
  try dsimp only
  rcases Decidable.em (P.badRootSeam ≤ q) with hc | hc
  · rw [if_pos (show P.badRootSeam ≤ pp + sy by omega), if_pos hc] at *
    rw [if_pos (show k - sy ≤ pp + shifts * P.len by omega)]
    congr 1
    omega
  · rw [if_neg (show ¬ P.badRootSeam ≤ pp + sy by omega), if_neg hc] at *
    rw [if_pos (show k - sy ≤ pp + 0 by omega)]
    congr 1
    omega

/-- **親の位置が今の段にあれば、積むセルは親を持つ。** -/
theorem fujiCell_par_isSome (M : List Rowj) (P : FujiParams) (cur : Rowj)
    (sy sx k i j shifts topVal z : Nat) (hmono : PosMono cur)
    (hpp : parentPos M P sy sx k shifts = some z)
    (u : Nat) (hu : u < cur.size) (hpos : (cur[u]'hu).pos = z) :
    (fujiCell M P cur sy sx k i j shifts topVal).par = some u := by
  rw [fujiCell_par, hpp]
  dsimp only
  exact lookupPos_of_pos cur hmono z u hu hpos

theorem fujiCellAt_par_isSome (M : List Rowj) (P : FujiParams) (nd : Nat → Nat)
    (i j : Nat) (isRep isAsc : Bool) (res : List Rowj) (k z : Nat)
    (hmono : PosMono (rowAt res k))
    (hpp : parentPos M P (fujiSourceAt P i k isRep isAsc).1
      (sourceIdx M (fujiSourceAt P i k isRep isAsc).1 j (fujiSourceAt P i k isRep isAsc).2) k
      (i - (if isRep then 1 else 0)) = some z)
    (u : Nat) (hu : u < (rowAt res k).size) (hpos : ((rowAt res k)[u]'hu).pos = z) :
    (fujiCellAt M P nd i j isRep isAsc res k).par = some u :=
  fujiCell_par_isSome M P (rowAt res k) _ _ k i j _ _ z hmono hpp u hu hpos

/-- 同じ配列なら同じセル。 -/
theorem getElem_congr_arr (a b : Rowj) (h : a = b) (t : Nat) (ha : t < a.size)
    (hb : t < b.size) : a[t]'ha = b[t]'hb := by
  subst h
  rfl

/-- `HasCol` から添字と位置を取り出す。 -/
theorem hasCol_pos (res : List Rowj) (k c : Nat) (h : HasCol res k c) :
    ∃ (u : Nat) (hu : u < (rowAt res k).size), ((rowAt res k)[u]'hu).pos + k = c := by
  obtain ⟨t, d, hd, hdc⟩ := h
  have ht : t < (rowAt res k).size := lt_size_of_getElem? hd
  refine ⟨t, ht, ?_⟩
  have hdt : (rowAt res k)[t]'ht = d := by
    rw [Array.getElem?_eq_getElem ht] at hd
    exact Option.some.inj hd
  rw [hdt]
  exact hdc

/-- 子を切ったあとに残るセルは、元の山で生きていて、列は `n−1` より小さい。 -/
theorem cutChild_cell_live (S : Setting) (M : List Rowj) (hM : MtRep S M) (hn : 1 < S.n)
    (cutH : Nat) (hcut : cutH = height S.tower.base (S.n - 1))
    (m t : Nat) (d : Cell) (hd : (rowAt (cutChild M cutH) m)[t]? = some d) :
    m ≤ height S.tower.base (d.pos + m) ∧ d.pos + m < S.n - 1 := by
  have hts : t < (rowAt (cutChild M cutH) m).size := lt_size_of_getElem? hd
  have hm : m < (cutChild M cutH).length := by
    rcases Nat.lt_or_ge m (cutChild M cutH).length with h1 | h1
    · exact h1
    · exfalso
      rw [rowAt_of_ge _ m h1] at hts
      simp at hts
  have hbound := colLt_cutChild S M hM cutH hn (by omega) m t d hd
  rw [rowAt_cutChild_getElem? M cutH m t hm hts] at hd
  have htM : t < (rowAt M m).size := lt_size_of_getElem? hd
  have hdt : (rowAt M m)[t]'htM = d := by
    rw [Array.getElem?_eq_getElem htM] at hd
    exact Option.some.inj hd
  have hmM : m < M.length := by
    rcases Nat.lt_or_ge m M.length with h1 | h1
    · exact h1
    · exfalso
      rw [rowAt_of_ge M m h1] at htM
      simp at htM
  have hrep := rep_top S M hM m hmM
  have hmem : d ∈ (rowAt M m).toList := by
    rw [← hdt]
    exact mem_of_getElem _ t htM
  have hv := hrep.val d hmem
  have hl := hrep.live d hmem
  refine ⟨?_, hbound⟩
  refine (live_iff_le_height S.tower.base (S.tower.hpos (d.pos + m)) m).mp ?_
  omega

/-- 最上段は埋めで変わらないので、その段の値はセルの値そのもの。 -/
theorem colVal_top_last (Rs : List Rowj) (r : Nat) (hr : r = Rs.length - 1) (i : Nat)
    (hi : i < (rowAt Rs r).size) (hmono : PosMono (rowAt Rs r)) (c : Nat)
    (hc : ((rowAt Rs r)[i]'hi).pos + r = c) :
    readVal (rowAt (fillValues Rs) r) r c = ((rowAt Rs r)[i]'hi).val := by
  have htop : rowAt (fillValues Rs) r = rowAt Rs r := by
    rw [hr]
    exact fillValues_top Rs
  rw [htop, readVal_of_index _ hmono r c i hi hc]
  unfold valAtIdx
  rw [dif_pos hi]

/-- 空段落としのあとにセルがあれば、その段は元のまま。 -/
theorem rowAt_dropEmptyTop_of_cell (L : List Rowj) (m t : Nat) (d : Cell)
    (hd : (rowAt (dropEmptyTop L) m)[t]? = some d) :
    rowAt (dropEmptyTop L) m = rowAt L m := by
  have hts : t < (rowAt (dropEmptyTop L) m).size := lt_size_of_getElem? hd
  have hm : m < (dropEmptyTop L).length := by
    rcases Nat.lt_or_ge m (dropEmptyTop L).length with h1 | h1
    · exact h1
    · exfalso
      rw [rowAt_of_ge _ m h1] at hts
      simp at hts
  exact rowAt_dropEmptyTop L.length L m (Nat.le_refl _) hm

/-- 子を切ったあとに残るセルの値は、元の山の値。 -/
theorem cutChild_cell_val (S : Setting) (M : List Rowj) (hM : MtRep S M) (cutH : Nat)
    (m t : Nat) (d : Cell) (hd : (rowAt (cutChild M cutH) m)[t]? = some d) :
    d.val = (rows S.tower.base m).value (d.pos + m) ∧ 0 < d.val := by
  have hts : t < (rowAt (cutChild M cutH) m).size := lt_size_of_getElem? hd
  have hm : m < (cutChild M cutH).length := by
    rcases Nat.lt_or_ge m (cutChild M cutH).length with h1 | h1
    · exact h1
    · exfalso
      rw [rowAt_of_ge _ m h1] at hts
      simp at hts
  rw [rowAt_cutChild_getElem? M cutH m t hm hts] at hd
  have htM : t < (rowAt M m).size := lt_size_of_getElem? hd
  have hdt : (rowAt M m)[t]'htM = d := by
    rw [Array.getElem?_eq_getElem htM] at hd
    exact Option.some.inj hd
  have hmM : m < M.length := by
    have h2 : (cutChild M cutH).length ≤ M.length := cutChild_length_le M cutH
    omega
  have hrep := rep_top S M hM m hmM
  have hmem : d ∈ (rowAt M m).toList := by
    rw [← hdt]
    exact mem_of_getElem _ t htM
  exact ⟨hrep.val d hmem, hrep.live d hmem⟩

/-! ## 積んだセルの正体

`cell_fujiIters` は列しか返さない。積んだセルが `fujiCellAt` そのものであること、
およびその時点の状態が何かも返す強い版を作る。 -/

theorem cell_fujiSeams' (M : List Rowj) (P : FujiParams) (nd : Nat → Nat) (i ach af : Nat) :
    ∀ (t : Nat) (res : List Rowj) (m u : Nat) (d : Cell),
      (rowAt (fujiSeams M P nd i ach af t res) m)[u]? = some d →
        (rowAt res m)[u]? = some d ∨
          ∃ t', t' < t ∧ m < kmaxAt M P i (P.badRootSeam + t') ach af ∧
            d = fujiCellAt M P nd i (P.badRootSeam + t') (isRepAt P (P.badRootSeam + t'))
              (isAscAt M P (P.badRootSeam + t') af)
              (fujiSeams M P nd i ach af t' res) m := by
  intro t
  induction t with
  | zero => intro res m u d h; exact Or.inl h
  | succ t ih =>
      intro res m u d h
      rw [fujiSeams_succ] at h
      rcases cell_fujiRows M P nd i (P.badRootSeam + t) (isRepAt P (P.badRootSeam + t))
        (isAscAt M P (P.badRootSeam + t) af)
        (kmaxAt M P i (P.badRootSeam + t) ach af) _ m u d h with h1 | ⟨hm, hd⟩
      · rcases ih res m u d h1 with h2 | ⟨t', ht', hk', hd'⟩
        · exact Or.inl h2
        · exact Or.inr ⟨t', by omega, hk', hd'⟩
      · exact Or.inr ⟨t, by omega, hm, hd⟩

theorem cell_fujiIters' (M : List Rowj) (P : FujiParams) (nd : Nat → Nat) (ach af : Nat) :
    ∀ (n : Nat) (res : List Rowj) (m u : Nat) (d : Cell),
      (rowAt (fujiIters M P nd ach af n res) m)[u]? = some d →
        (rowAt res m)[u]? = some d ∨
          ∃ i' t', i' < n ∧ t' < P.len ∧
            m < kmaxAt M P (i' + 1) (P.badRootSeam + t') ach af ∧
            d = fujiCellAt M P nd (i' + 1) (P.badRootSeam + t')
              (isRepAt P (P.badRootSeam + t')) (isAscAt M P (P.badRootSeam + t') af)
              (fujiSeams M P nd (i' + 1) ach af t' (fujiIters M P nd ach af i' res)) m := by
  intro n
  induction n with
  | zero => intro res m u d h; exact Or.inl h
  | succ n ih =>
      intro res m u d h
      rw [fujiIters_succ] at h
      rcases cell_fujiSeams' M P nd (n + 1) ach af P.len _ m u d h with h1 | ⟨t', ht', hk', hd'⟩
      · rcases ih res m u d h1 with h2 | ⟨i2, t2, hi2, ht2, hk2, hd2⟩
        · exact Or.inl h2
        · exact Or.inr ⟨i2, t2, by omega, ht2, hk2, hd2⟩
      · exact Or.inr ⟨n, t', by omega, ht', hk', hd'⟩

/-! ## 途中の状態から最終形への伸び -/

theorem rowExt_fujiSeams_mono (M : List Rowj) (P : FujiParams) (nd : Nat → Nat)
    (i ach af : Nat) (res : List Rowj) (m : Nat) :
    ∀ t2 t1, t1 ≤ t2 → RowExt (rowAt (fujiSeams M P nd i ach af t1 res) m)
      (rowAt (fujiSeams M P nd i ach af t2 res) m) := by
  intro t2
  induction t2 with
  | zero =>
      intro t1 h
      have : t1 = 0 := by omega
      subst this
      exact RowExt.rfl' _
  | succ t ih =>
      intro t1 h
      rcases Nat.lt_or_ge t1 (t + 1) with h1 | h1
      · rw [fujiSeams_succ]
        exact RowExt.trans (ih t1 (by omega)) (rowExt_fujiRows _ _ _ _ _ _ _ _ _ _)
      · have : t1 = t + 1 := by omega
        subst this
        exact RowExt.rfl' _

theorem rowExt_fujiIters_mono (M : List Rowj) (P : FujiParams) (nd : Nat → Nat)
    (ach af : Nat) (res : List Rowj) (m : Nat) :
    ∀ n2 n1, n1 ≤ n2 → RowExt (rowAt (fujiIters M P nd ach af n1 res) m)
      (rowAt (fujiIters M P nd ach af n2 res) m) := by
  intro n2
  induction n2 with
  | zero =>
      intro n1 h
      have : n1 = 0 := by omega
      subst this
      exact RowExt.rfl' _
  | succ n ih =>
      intro n1 h
      rcases Nat.lt_or_ge n1 (n + 1) with h1 | h1
      · rw [fujiIters_succ]
        exact RowExt.trans (ih n1 (by omega)) (rowExt_fujiSeams _ _ _ _ _ _ _ _ _)
      · have : n1 = n + 1 := by omega
        subst this
        exact RowExt.rfl' _

/-- 途中の状態から最終形へ。 -/
theorem rowExt_state_to_final (M : List Rowj) (P : FujiParams) (nd : Nat → Nat)
    (ach af : Nat) (res : List Rowj) (m i' t' nrep : Nat)
    (hi : i' < nrep) (ht : t' ≤ P.len) :
    RowExt (rowAt (fujiSeams M P nd (i' + 1) ach af t' (fujiIters M P nd ach af i' res)) m)
      (rowAt (fujiIters M P nd ach af nrep res) m) := by
  have h1 : RowExt (rowAt (fujiSeams M P nd (i' + 1) ach af t'
      (fujiIters M P nd ach af i' res)) m)
      (rowAt (fujiSeams M P nd (i' + 1) ach af P.len
        (fujiIters M P nd ach af i' res)) m) :=
    rowExt_fujiSeams_mono M P nd (i' + 1) ach af _ m P.len t' ht
  have h2 : RowExt (rowAt (fujiIters M P nd ach af (i' + 1) res) m)
      (rowAt (fujiIters M P nd ach af nrep res) m) :=
    rowExt_fujiIters_mono M P nd ach af res m nrep (i' + 1) (by omega)
  rw [fujiIters_succ] at h2
  exact RowExt.trans h1 h2

/-! ## 山崎噴火でない枝の枝の選び方

`yamakazi = false` のとき、「行の最後から取るか」はつねに `isRep` に等しい。
元の段の選び方だけが 4 通りに分かれる。 -/

/-- 元の段の選び方（`yamakazi = false` のとき）。 -/
def fujiSrcRow (P : FujiParams) (i k : Nat) (isRep : Bool) : Nat :=
  let d := P.cutHeight - P.badRootHeight
  let ir := if isRep then 1 else 0
  if k < P.badRootHeight then k
  else if k ≤ P.badRootHeight + d * (i - ir) then P.badRootHeight
  else if isRep && decide (k ≤ P.badRootHeight + d * i) then k - d * (i - 1)
  else k - d * i

/-- 上りかどうかまで込めた元の段。上りでなければその段そのもの。 -/
def fujiSrcRowAt (P : FujiParams) (i k : Nat) (isRep isAsc : Bool) : Nat :=
  if isAsc then fujiSrcRow P i k isRep else k

theorem fujiSource_notyama (P : FujiParams) (hyk : P.yamakazi = false) (i k : Nat)
    (isRep : Bool) : fujiSource P i k isRep = (fujiSrcRow P i k isRep, isRep) := by
  unfold fujiSource fujiSrcRow
  dsimp only
  rw [hyk]
  simp only [Bool.not_false, Bool.true_and]
  repeat' split
  all_goals rfl

theorem fujiSrcRow_le (P : FujiParams) (i k : Nat) (isRep : Bool) :
    fujiSrcRow P i k isRep ≤ k := by
  unfold fujiSrcRow
  dsimp only
  repeat' split
  all_goals omega

theorem fujiSrcRowAt_le (P : FujiParams) (i k : Nat) (isRep isAsc : Bool) :
    fujiSrcRowAt P i k isRep isAsc ≤ k := by
  unfold fujiSrcRowAt
  cases isAsc with
  | true => simpa using fujiSrcRow_le P i k isRep
  | false => simp

theorem fujiSourceAt_notyama (P : FujiParams) (hyk : P.yamakazi = false) (i k : Nat)
    (isRep isAsc : Bool) :
    fujiSourceAt P i k isRep isAsc = (fujiSrcRowAt P i k isRep isAsc, isRep) := by
  unfold fujiSourceAt fujiSrcRowAt
  cases isAsc with
  | true => simpa using fujiSource_notyama P hyk i k isRep
  | false => simp

end Yukito
