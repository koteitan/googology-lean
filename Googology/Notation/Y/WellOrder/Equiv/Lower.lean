/-
From koteitan, 1y-expand-equiv, `Equiv/Lower.lean`
(https://github.com/koteitan/1y-expand-equiv, revision c9a5368a09ceb62ec671a6c3447a4719d035dfc0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.Y.WellOrder.`; the transcription `Equiv/Yukito.lean` is replaced by
`Googology.Notation.Y.Yukito` (opened below).
This file is part of googology-lean and is licensed under its MIT license.
-/
import Googology.Notation.Y.WellOrder.Equiv.Spec
import Googology.Notation.Y.WellOrder.OneY.ExpansionRebuildPrefix

open Googology.Notation.Y

/-!
# `k < K` の枝のコピー先の山

原文の `badAtLowerContext`（= `activeLowerContext`）は `LowerCopy.Context` である。
こちらの `Setting` から同じものを組み立てる。

JS 側との対応は
```
badRootHeight = floor = height y
cutHeight     = height x
d             = rise = height x − height y
isAscending   = InCone
```
である。
-/

namespace Yukito

open OneY OneY.Numeric OneY.RootGeometry

/-! ## この枝の `FujiParams`

`expYama` が偽のとき、JS のパラメータは次のようになる。

```
badRootSeam   = expSeam M mfuel     （= y）
badRootHeight = height y            （列 y を含む最上段）
cutHeight     = height (n−1)        （= expCutH M）
yamakazi      = false
```
-/

theorem expP_yamakazi_lower (M : List Rowj) (mfuel : Nat) (h : ¬ expYama M mfuel) :
    (expP M mfuel).yamakazi = false := by
  show decide (expYama M mfuel) = false
  exact decide_eq_false h

theorem expP_cutHeight_lower (S : Setting) (M : List Rowj) (hM : MtRep S M) (hn : 1 < S.n)
    (mfuel : Nat) (h : ¬ expYama M mfuel) :
    (expP M mfuel).cutHeight = height S.tower.base (S.n - 1) := by
  show (if expYama M mfuel then expCutH M - 1 else expCutH M) = _
  rw [if_neg h]
  exact expCutH_eq S M hM hn

theorem expP_badRootHeight_lower (S : Setting) (M : List Rowj) (hM : MtRep S M)
    (mfuel : Nat) (h : ¬ expYama M mfuel) (hseam : expSeam M mfuel < S.n) :
    (expP M mfuel).badRootHeight = height S.tower.base (expSeam M mfuel) := by
  show (if expYama M mfuel then expCutH M - 1
        else (topRowWithCol M (expSeam M mfuel) M.length).getD 0) = _
  rw [if_neg h, topRowWithCol_eq S M hM _ hseam M.length (Nat.le_refl _)
    (hM.tall _ hseam)]
  rfl

/-- `k < K` の枝で使う `LowerCopy.Context`。 -/
def lowerContext (S : Setting) (y x : Nat) (hyx : y < x)
    (hroot : (mountainOf' S).rootAt (height S.tower.base y) x = y)
    (hhigher : height S.tower.base y < height S.tower.base x) : LowerCopy.Context where
  mountain := mountainOf' S
  coordinates := ⟨y, x, hyx⟩
  last_root := hroot
  last_higher := hhigher

variable {S : Setting} {y x : Nat}

/-- **`InCone` は「段 `height y` で生きていて、その段の根が `y`」。** -/
theorem lowerContext_inCone (hyx : y < x) (hroot) (hhigher) (c : Nat) :
    (lowerContext S y x hyx hroot hhigher).InCone c
      ↔ (height S.tower.base y ≤ height S.tower.base c ∧
          (rows S.tower.base (height S.tower.base y)).forest.root c = y) := Iff.rfl

/-- **JS の `isAscending` は `InCone`。** -/
theorem isAscending_iff_inCone (M : List Rowj) (hM : MtRep S M) (hyx : y < x)
    (hroot) (hhigher) (j fuel : Nat)
    (hbh : height S.tower.base y < M.length) (hj : j < S.n)
    (hfuel : (rowAt M (height S.tower.base y)).size ≤ fuel) :
    isAscending M (height S.tower.base y) y j fuel = true
      ↔ (lowerContext S y x hyx hroot hhigher).InCone j := by
  rw [isAscending_iff_root S M hM (height S.tower.base y) y j fuel hbh hj hfuel
    (parent_none_at_top S.tower.base S.tower.hpos y)]
  exact (lowerContext_inCone hyx hroot hhigher j).symm

theorem lowerContext_height_orig (hyx : y < x) (hroot) (hhigher) (c : Nat) (hc : c ≤ x) :
    (lowerContext S y x hyx hroot hhigher).height c = height S.tower.base c :=
  (lowerContext S y x hyx hroot hhigher).height_original hc

/-- **継ぎ目の列（`j = y`）の高さ。** -/
theorem lowerContext_height_seam (hyx : y < x) (hroot) (hhigher) (i : Nat) :
    (lowerContext S y x hyx hroot hhigher).height (y + (x - y) * i)
      = height S.tower.base y
        + i * (height S.tower.base x - height S.tower.base y) := by
  have hc : y + (x - y) * i = (lowerContext S y x hyx hroot hhigher).coordinates.y
      + i * (lowerContext S y x hyx hroot hhigher).coordinates.length := by
    show y + (x - y) * i = y + i * (x - y)
    rw [Nat.mul_comm]
  rw [hc]
  exact (lowerContext S y x hyx hroot hhigher).height_root_copy i

/-- **それ以外の継ぎ目の列の高さ。** `InCone` なら `rise * i` だけ持ち上がる。 -/
theorem lowerContext_height_other (hyx : y < x) (hroot) (hhigher) (j i : Nat)
    (hj1 : y < j) (hj2 : j ≤ x) :
    (lowerContext S y x hyx hroot hhigher).height (j + (x - y) * i)
      = if (lowerContext S y x hyx hroot hhigher).InCone j then
          height S.tower.base j + i * (height S.tower.base x - height S.tower.base y)
        else height S.tower.base j := by
  have hc : j + (x - y) * i
      = (lowerContext S y x hyx hroot hhigher).coordinates.encode j i := by
    show j + (x - y) * i = j + i * (x - y)
    rw [Nat.mul_comm]
  rw [hc]
  exact (lowerContext S y x hyx hroot hhigher).height_encode hj1 hj2 i

/-- 継ぎ目自身は `InCone`。 -/
theorem inCone_seam (hyx : y < x) (hroot) (hhigher) :
    (lowerContext S y x hyx hroot hhigher).InCone y := by
  refine ⟨Nat.le_refl _, ?_⟩
  exact ParentForest.root_of_parent_none _
    (parent_none_at_top S.tower.base S.tower.hpos y)

/-- **JS の `kmax` は原文の高さ + 1。** -/
theorem kmaxAt_eq_height_lower (M : List Rowj) (hM : MtRep S M) (P : FujiParams)
    (hyx : y < x) (hroot) (hhigher)
    (hbh : P.badRootHeight = height S.tower.base y)
    (hsm : P.badRootSeam = y) (hcut : P.cutHeight = height S.tower.base x)
    (ach af i j : Nat) (hj1 : y ≤ j) (hj2 : j < x) (hjn : j < S.n)
    (hsh : seamHeightOf M j ach = height S.tower.base j + 1)
    (hbhlen : height S.tower.base y < M.length)
    (hfuel : (rowAt M (height S.tower.base y)).size ≤ af) :
    kmaxAt M P i j ach af
      = (lowerContext S y x hyx hroot hhigher).height (j + (x - y) * i) + 1 := by
  have hasc := isAscending_iff_inCone M hM hyx hroot hhigher j af hbhlen hjn hfuel
  unfold kmaxAt isAscAt
  dsimp only
  rw [hbh, hsm, hcut, hsh]
  rcases Decidable.em (j = y) with hje | hjne
  · subst hje
    rw [lowerContext_height_seam hyx hroot hhigher i,
      if_pos (hasc.mpr (inCone_seam hyx hroot hhigher))]
    rw [Nat.mul_comm]
    omega
  · rw [lowerContext_height_other hyx hroot hhigher j i (by omega) (by omega)]
    rcases Decidable.em ((lowerContext S y x hyx hroot hhigher).InCone j) with hc | hc
    · rw [if_pos (hasc.mpr hc), if_pos hc, Nat.mul_comm]
      omega
    · rw [if_neg (fun h => hc (hasc.mp h)), if_neg hc]

/-! ## 上りでない列

`isAscending` が偽の列では、`script.js` は Bb 枝しか使わない（`sy = k`）。原文の
`¬InCone s` の枝も `((M.row r).parent s).map (parentCopy b)` で段は `r` そのもの
なので、そのまま対応する。親のセルが積んであることは原文側の
`height_parentCopy_ge`（`M.height p ≤ height (parentCopy b p)`）と
`parent_endpoint`（`r ≤ M.height p`）から出る。 -/

/-! ## 原文の親をコピーの座標で開く

`c = s + b*L`（`y < s ≤ x`、`0 < b`）は `x` より右なので、原文の `parent` は
新しい列の枝に入る。 -/

theorem lowerContext_row (hyx : y < x) (hroot) (hhigher) (r : Nat) :
    (lowerContext S y x hyx hroot hhigher).mountain.row r
      = (rows S.tower.base r).forest := rfl

theorem lowerContext_parent_new (hyx : y < x) (hroot) (hhigher) (r s b : Nat)
    (hs1 : y < s) (hs2 : s ≤ x) (hb : 0 < b) :
    (lowerContext S y x hyx hroot hhigher).parent r (s + b * (x - y))
      = if (lowerContext S y x hyx hroot hhigher).InCone s
            ∧ (lowerContext S y x hyx hroot hhigher).floor ≤ r then
          (if r < (lowerContext S y x hyx hroot hhigher).floor
                + b * (lowerContext S y x hyx hroot hhigher).rise then
            ((lowerContext S y x hyx hroot hhigher).mountain.row
              (lowerContext S y x hyx hroot hhigher).floor).parent s
           else
            ((lowerContext S y x hyx hroot hhigher).mountain.row
              (r - b * (lowerContext S y x hyx hroot hhigher).rise)).parent s).map
            (fun p => p + b * (lowerContext S y x hyx hroot hhigher).coordinates.length)
        else (((lowerContext S y x hyx hroot hhigher).mountain.row r).parent s).map
          ((lowerContext S y x hyx hroot hhigher).coordinates.parentCopy b) := by
  have henc : s + b * (x - y)
      = (lowerContext S y x hyx hroot hhigher).coordinates.encode s b := rfl
  have hgt : (lowerContext S y x hyx hroot hhigher).coordinates.x
      < (lowerContext S y x hyx hroot hhigher).coordinates.encode s b := by
    obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    exact (lowerContext S y x hyx hroot hhigher).encode_succ_gt_last hs1 b'
  have hsrc : (lowerContext S y x hyx hroot hhigher).coordinates.source
      ((lowerContext S y x hyx hroot hhigher).coordinates.encode s b) = s :=
    (lowerContext S y x hyx hroot hhigher).coordinates.source_encode hs1 hs2 b
  have hblk : (lowerContext S y x hyx hroot hhigher).coordinates.block
      ((lowerContext S y x hyx hroot hhigher).coordinates.encode s b) = b :=
    (lowerContext S y x hyx hroot hhigher).coordinates.block_encode hs1 hs2 b
  rw [henc]
  show (if (lowerContext S y x hyx hroot hhigher).coordinates.encode s b
      ≤ (lowerContext S y x hyx hroot hhigher).coordinates.x then _ else _) = _
  rw [if_neg (Nat.not_le_of_gt hgt)]
  dsimp only
  rw [hsrc, hblk]
  split
  · split <;> rfl
  · rfl

/-! ## 元の段の一致

原文は上りの列について `r < floor + b*rise` なら段 `floor`、そうでなければ
`r − b*rise` を使う。これは `floor` で下から押さえた `max floor (r − b*rise)` に
等しい。JS の `fujiSrcRow` も、段が `floor + rise*i` 以下であればこれに一致する。 -/

theorem clamp_srcRow (f b R r : Nat) :
    (if r < f + b * R then f else r - b * R) = max f (r - b * R) := by
  simp only [Nat.max_def]
  split <;> split <;> omega

theorem fujiSrcRow_notrep (P : FujiParams) (i k : Nat) :
    fujiSrcRow P i k false
      = if k < P.badRootHeight then k
        else if k ≤ P.badRootHeight + (P.cutHeight - P.badRootHeight) * i then P.badRootHeight
        else k - (P.cutHeight - P.badRootHeight) * i := by
  simp [fujiSrcRow]

theorem fujiSrcRow_rep (P : FujiParams) (i k : Nat) :
    fujiSrcRow P i k true
      = if k < P.badRootHeight then k
        else if k ≤ P.badRootHeight + (P.cutHeight - P.badRootHeight) * (i - 1) then
          P.badRootHeight
        else if k ≤ P.badRootHeight + (P.cutHeight - P.badRootHeight) * i then
          k - (P.cutHeight - P.badRootHeight) * (i - 1)
        else k - (P.cutHeight - P.badRootHeight) * i := by
  simp [fujiSrcRow]

/-- **JS の元の段は原文の元の段に一致する。** 段が `floor + rise*i` 以下であれば、
上りの列では `max floor (k − b*rise)`、そうでなければ `k` そのものである。 -/
theorem fujiSrcRowAt_eq (P : FujiParams)
    (hbh : P.badRootHeight = height S.tower.base y)
    (hcut : P.cutHeight = height S.tower.base x)
    (i k : Nat) (isRep isAsc : Bool)
    (hk : isRep = true → k ≤ height S.tower.base y
      + (height S.tower.base x - height S.tower.base y) * i) :
    fujiSrcRowAt P i k isRep isAsc
      = if isAsc = true ∧ height S.tower.base y ≤ k then
          max (height S.tower.base y)
            (k - (i - (if isRep then 1 else 0))
              * (height S.tower.base x - height S.tower.base y))
        else k := by
  unfold fujiSrcRowAt
  have hc1 : (height S.tower.base x - height S.tower.base y) * i
      = i * (height S.tower.base x - height S.tower.base y) := Nat.mul_comm _ _
  have hc2 : (height S.tower.base x - height S.tower.base y) * (i - 1)
      = (i - 1) * (height S.tower.base x - height S.tower.base y) := Nat.mul_comm _ _
  cases isAsc with
  | false => simp
  | true =>
      cases isRep with
      | false =>
          rw [if_pos rfl, fujiSrcRow_notrep, hbh, hcut]
          simp only [Bool.false_eq_true, if_false, Nat.sub_zero, true_and,
            Nat.max_def]
          repeat' split
          all_goals omega
      | true =>
          have hk' := hk rfl
          rw [if_pos rfl, fujiSrcRow_rep, hbh, hcut]
          simp only [if_true, true_and, Nat.max_def]
          repeat' split
          all_goals omega

/-! ## 原文の親から元の段・元の列・その親を取り出す -/

theorem lowerContext_y_eq (hyx : y < x) (hroot) (hhigher) :
    (lowerContext S y x hyx hroot hhigher).coordinates.y = y := rfl

theorem lowerContext_length_eq (hyx : y < x) (hroot) (hhigher) :
    (lowerContext S y x hyx hroot hhigher).coordinates.length = x - y := rfl

/-- 継ぎ目でない列（`y < j < x`）。 -/
theorem lowerContext_parent_other (hyx : y < x) (hroot) (hhigher) (k i j : Nat)
    (hi : 0 < i) (hjy : y < j) (hjx : j < x) :
    (lowerContext S y x hyx hroot hhigher).parent k (j + (x - y) * i)
      = ((rows S.tower.base
          (if (lowerContext S y x hyx hroot hhigher).InCone j ∧ height S.tower.base y ≤ k then
            max (height S.tower.base y)
              (k - i * (height S.tower.base x - height S.tower.base y))
           else k)).forest.parent j).map
          (fun q => q + (if y ≤ q then i * (x - y) else 0)) := by
  have hcol : j + (x - y) * i = j + i * (x - y) := by rw [Nat.mul_comm]
  rw [hcol, lowerContext_parent_new hyx hroot hhigher k j i hjy (by omega) hi]
  have hfl : (lowerContext S y x hyx hroot hhigher).floor = height S.tower.base y := rfl
  have hri : (lowerContext S y x hyx hroot hhigher).rise
      = height S.tower.base x - height S.tower.base y := rfl
  rcases Decidable.em ((lowerContext S y x hyx hroot hhigher).InCone j
      ∧ height S.tower.base y ≤ k) with hcase | hcase
  · rw [if_pos hcase]
    rw [if_pos (show (lowerContext S y x hyx hroot hhigher).InCone j
      ∧ (lowerContext S y x hyx hroot hhigher).floor ≤ k from ⟨hcase.1, hcase.2⟩)]
    rw [hfl, hri]
    have hif : (if k < height S.tower.base y
              + i * (height S.tower.base x - height S.tower.base y) then
            ((lowerContext S y x hyx hroot hhigher).mountain.row
              (height S.tower.base y)).parent j
          else
            ((lowerContext S y x hyx hroot hhigher).mountain.row
              (k - i * (height S.tower.base x - height S.tower.base y))).parent j)
        = ((lowerContext S y x hyx hroot hhigher).mountain.row
            (max (height S.tower.base y)
              (k - i * (height S.tower.base x - height S.tower.base y)))).parent j := by
      rw [← clamp_srcRow (height S.tower.base y) i
        (height S.tower.base x - height S.tower.base y) k]
      split <;> rfl
    rw [hif, lowerContext_row]
    cases hq : (rows S.tower.base (max (height S.tower.base y)
        (k - i * (height S.tower.base x - height S.tower.base y)))).forest.parent j with
    | none => rfl
    | some q =>
        have hcone : (lowerContext S y x hyx hroot hhigher).InCone q :=
          (lowerContext S y x hyx hroot hhigher).high_parent_inCone hcase.1
            (show (lowerContext S y x hyx hroot hhigher).floor
              ≤ max (height S.tower.base y)
                  (k - i * (height S.tower.base x - height S.tower.base y)) by
              rw [hfl]; exact Nat.le_max_left _ _) hq
        have hyq : y ≤ q := (lowerContext S y x hyx hroot hhigher).root_le_of_inCone hcone
        show Option.map _ (some q) = Option.map _ (some q)
        rw [Option.map_some, Option.map_some, if_pos hyq]
        rfl
  · rw [if_neg hcase]
    rw [if_neg (fun h => hcase ⟨h.1, h.2⟩), lowerContext_row]
    cases hq : (rows S.tower.base k).forest.parent j with
    | none => rfl
    | some q =>
        show Option.map _ (some q) = Option.map _ (some q)
        rw [Option.map_some, Option.map_some, parentCopy_eq,
          lowerContext_y_eq, lowerContext_length_eq]

/-- 継ぎ目の列（`j = y`）。この列の元の列は `x` で、繰り返し `i` のコピーは
`x` の block `i−1` にあたる。 -/
theorem lowerContext_parent_seam (hyx : y < x) (hroot) (hhigher) (k i : Nat)
    (hi : 0 < i) :
    (lowerContext S y x hyx hroot hhigher).parent k (y + (x - y) * i)
      = ((rows S.tower.base
          (if height S.tower.base y ≤ k then
            max (height S.tower.base y)
              (k - (i - 1) * (height S.tower.base x - height S.tower.base y))
           else k)).forest.parent x).map
          (fun q => q + (if y ≤ q then (i - 1) * (x - y) else 0)) := by
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
  have hcol : y + (x - y) * (m + 1) = x + m * (x - y) := by
    have h1 : (x - y) * (m + 1) = (x - y) * m + (x - y) := Nat.mul_succ _ _
    have h2 : (x - y) * m = m * (x - y) := Nat.mul_comm _ _
    omega
  have hm1 : m + 1 - 1 = m := by omega
  rw [hcol, hm1]
  have hfl : (lowerContext S y x hyx hroot hhigher).floor = height S.tower.base y := rfl
  have hri : (lowerContext S y x hyx hroot hhigher).rise
      = height S.tower.base x - height S.tower.base y := rfl
  have hcone : (lowerContext S y x hyx hroot hhigher).InCone x :=
    (lowerContext S y x hyx hroot hhigher).last_inCone
  cases m with
  | zero =>
      have hx0 : x + 0 * (x - y) = x := by omega
      rw [hx0, (lowerContext S y x hyx hroot hhigher).parent_original
        (show x ≤ (lowerContext S y x hyx hroot hhigher).coordinates.x from Nat.le_refl _)]
      have hrowk : (if height S.tower.base y ≤ k then
            max (height S.tower.base y)
              (k - 0 * (height S.tower.base x - height S.tower.base y))
           else k) = k := by
        split
        · simp only [Nat.max_def]
          split <;> omega
        · rfl
      rw [hrowk, lowerContext_row]
      cases hq : (rows S.tower.base k).forest.parent x with
      | none => rfl
      | some q => simp
  | succ m' =>
      rw [lowerContext_parent_new hyx hroot hhigher k x (m' + 1) hyx (Nat.le_refl _)
        (by omega)]
      rcases Nat.lt_or_ge k (height S.tower.base y) with hk | hk
      · rw [if_neg (show ¬ (height S.tower.base y ≤ k) by omega)]
        rw [if_neg (show ¬ ((lowerContext S y x hyx hroot hhigher).InCone x
          ∧ (lowerContext S y x hyx hroot hhigher).floor ≤ k) by
          rintro ⟨-, h2⟩; rw [hfl] at h2; omega), lowerContext_row]
        cases hq : (rows S.tower.base k).forest.parent x with
        | none => rfl
        | some q =>
            show Option.map _ (some q) = Option.map _ (some q)
            rw [Option.map_some, Option.map_some, parentCopy_eq,
              lowerContext_y_eq, lowerContext_length_eq]
      · rw [if_pos hk]
        rw [if_pos (show (lowerContext S y x hyx hroot hhigher).InCone x
          ∧ (lowerContext S y x hyx hroot hhigher).floor ≤ k from ⟨hcone, by rw [hfl]; exact hk⟩),
          hfl, hri]
        have hif : (if k < height S.tower.base y
                  + (m' + 1) * (height S.tower.base x - height S.tower.base y) then
                ((lowerContext S y x hyx hroot hhigher).mountain.row
                  (height S.tower.base y)).parent x
              else
                ((lowerContext S y x hyx hroot hhigher).mountain.row
                  (k - (m' + 1)
                    * (height S.tower.base x - height S.tower.base y))).parent x)
            = ((lowerContext S y x hyx hroot hhigher).mountain.row
                (max (height S.tower.base y)
                  (k - (m' + 1)
                    * (height S.tower.base x - height S.tower.base y)))).parent x := by
          rw [← clamp_srcRow (height S.tower.base y) (m' + 1)
            (height S.tower.base x - height S.tower.base y) k]
          split <;> rfl
        rw [hif, lowerContext_row]
        cases hq : (rows S.tower.base (max (height S.tower.base y)
            (k - (m' + 1) * (height S.tower.base x - height S.tower.base y)))).forest.parent x with
        | none => rfl
        | some q =>
            have hconeq : (lowerContext S y x hyx hroot hhigher).InCone q :=
              (lowerContext S y x hyx hroot hhigher).high_parent_inCone hcone
                (show (lowerContext S y x hyx hroot hhigher).floor
                  ≤ max (height S.tower.base y)
                      (k - (m' + 1)
                        * (height S.tower.base x - height S.tower.base y)) by
                  rw [hfl]; exact Nat.le_max_left _ _) hq
            have hyq : y ≤ q := (lowerContext S y x hyx hroot hhigher).root_le_of_inCone hconeq
            show Option.map _ (some q) = Option.map _ (some q)
            rw [Option.map_some, Option.map_some, if_pos hyq]
            rfl

/-- **原文の親は、JS が使う元の段・元の列の親の写しである。** -/
theorem lowerContext_parent_src (hyx : y < x) (hroot) (hhigher) (P : FujiParams)
    (hbh : P.badRootHeight = height S.tower.base y)
    (hcut : P.cutHeight = height S.tower.base x)
    (hsm : P.badRootSeam = y)
    (k i j : Nat) (hi : 0 < i) (hjy : y ≤ j) (hjx : j < x) (isAsc : Bool)
    (hasc : isAsc = true ↔ (lowerContext S y x hyx hroot hhigher).InCone j)
    (hk : j = y → k ≤ height S.tower.base y
      + (height S.tower.base x - height S.tower.base y) * i) :
    (lowerContext S y x hyx hroot hhigher).parent k (j + (x - y) * i)
      = ((rows S.tower.base (fujiSrcRowAt P i k (isRepAt P j) isAsc)).forest.parent
          (if j = y then x else j)).map
          (fun q => q + (if y ≤ q then (i - (if j = y then 1 else 0)) * (x - y) else 0)) := by
  rw [fujiSrcRowAt_eq P hbh hcut i k (isRepAt P j) isAsc
    (fun hr => hk (by rw [← hsm]; exact of_decide_eq_true hr))]
  rcases Decidable.em (j = y) with hje | hjne
  · subst hje
    have hrep : isRepAt P j = true := by
      show decide (j = P.badRootSeam) = true
      rw [hsm]
      simp
    have hasct : isAsc = true := hasc.mpr (inCone_seam hyx hroot hhigher)
    rw [hrep, hasct, if_pos rfl, if_pos rfl]
    simp only [true_and]
    exact lowerContext_parent_seam hyx hroot hhigher k i hi
  · have hrep : isRepAt P j = false := by
      show decide (j = P.badRootSeam) = false
      rw [hsm]
      simp [hjne]
    rw [hrep]
    simp only [if_neg hjne, Bool.false_eq_true, if_false, Nat.sub_zero]
    have h := lowerContext_parent_other hyx hroot hhigher k i j hi (by omega) hjx
    rcases Decidable.em ((lowerContext S y x hyx hroot hhigher).InCone j
        ∧ height S.tower.base y ≤ k) with hc | hc
    · rw [if_pos (show isAsc = true ∧ height S.tower.base y ≤ k from ⟨hasc.mpr hc.1, hc.2⟩)]
      rw [if_pos hc] at h
      exact h
    · rw [if_neg (fun hcon => hc ⟨hasc.mp hcon.1, hcon.2⟩)]
      rw [if_neg hc] at h
      exact h

/-- **JS の元のセルの列。** 置き換えの継ぎ目では行の最後（= `n−1`）、
そうでなければ列 `j` そのもの。 -/
theorem sourceIdx_lower_col (S : Setting) (M : List Rowj) (hM : MtRep S M)
    (P : FujiParams) (sy j : Nat) (hsy : sy < M.length) (hn : 1 < S.n) (hj : j < S.n)
    (hlive : isRepAt P j = false → 0 < (rows S.tower.base sy).value j)
    (hlast : isRepAt P j = true → 0 < (rows S.tower.base sy).value (S.n - 1)) :
    ∃ h : sourceIdx M sy j (isRepAt P j) < (rowAt M sy).size,
      ((rowAt M sy)[sourceIdx M sy j (isRepAt P j)]'h).pos + sy
        = if j = P.badRootSeam then S.n - 1 else j := by
  cases hb : isRepAt P j with
  | true =>
      rw [if_pos (of_decide_eq_true hb)]
      exact sourceIdx_last_col S M hM sy j hsy hn (hlast hb)
  | false =>
      rw [if_neg (of_decide_eq_false hb)]
      have hlv := hlive hb
      have hsyj : sy ≤ j := by
        rcases Nat.lt_or_ge j sy with hxx | hxx
        · rw [rows_value_zero_of_lt S.tower.base sy j hxx] at hlv
          omega
        · exact hxx
      exact sourceIdx_col S M hM sy j hsy hsyj hj hlv

/-- **JS が積むセルの親。** 元の段の元の列の親を、`parentCopy` で写した列にある。 -/
theorem fujiCellAt_par_lower (S : Setting) (M : List Rowj) (hM : MtRep S M)
    (P : FujiParams) (hyk : P.yamakazi = false) (nd : Nat → Nat)
    (i j : Nat) (isAsc : Bool) (res : List Rowj) (k : Nat)
    (hry : fujiSrcRowAt P i k (isRepAt P j) isAsc < M.length)
    (hn : 1 < S.n) (hjn : j < S.n)
    (hlive : isRepAt P j = false →
      0 < (rows S.tower.base (fujiSrcRowAt P i k (isRepAt P j) isAsc)).value j)
    (hlast : isRepAt P j = true →
      0 < (rows S.tower.base (fujiSrcRowAt P i k (isRepAt P j) isAsc)).value (S.n - 1))
    (C : CopyCoordinates.Context) (hy : C.y = P.badRootSeam) (hL : C.length = P.len)
    (p : Nat) (hp : (fujiCellAt M P nd i j (isRepAt P j) isAsc res k).par = some p) :
    ∃ hp' : p < (rowAt res k).size, ∃ q,
      (rows S.tower.base (fujiSrcRowAt P i k (isRepAt P j) isAsc)).forest.parent
        (if j = P.badRootSeam then S.n - 1 else j) = some q ∧
      ((rowAt res k)[p]'hp').pos + k
        = C.parentCopy (i - (if isRepAt P j then 1 else 0)) q := by
  have hsy : fujiSrcRowAt P i k (isRepAt P j) isAsc ≤ k :=
    fujiSrcRowAt_le P i k (isRepAt P j) isAsc
  have hp' : (fujiCell M P (rowAt res k) (fujiSrcRowAt P i k (isRepAt P j) isAsc)
      (sourceIdx M (fujiSrcRowAt P i k (isRepAt P j) isAsc) j (isRepAt P j)) k i j
      (i - (if isRepAt P j then 1 else 0)) (nd (j + P.len * i))).par = some p := by
    have hun : fujiCellAt M P nd i j (isRepAt P j) isAsc res k
        = fujiCell M P (rowAt res k) (fujiSourceAt P i k (isRepAt P j) isAsc).1
          (sourceIdx M (fujiSourceAt P i k (isRepAt P j) isAsc).1 j
            (fujiSourceAt P i k (isRepAt P j) isAsc).2) k i j
          (i - (if isRepAt P j then 1 else 0)) (nd (j + P.len * i)) := rfl
    rw [hun, fujiSourceAt_notyama P hyk] at hp
    exact hp
  obtain ⟨hpp, hsx, q, hq, hcol⟩ :=
    fujiCell_par_parentCopy S M hM P (rowAt res k) (fujiSrcRowAt P i k (isRepAt P j) isAsc)
      (sourceIdx M (fujiSrcRowAt P i k (isRepAt P j) isAsc) j (isRepAt P j)) k i j
      (i - (if isRepAt P j then 1 else 0)) (nd (j + P.len * i)) hsy hry C hy hL p hp'
  obtain ⟨hsx', hcolsrc⟩ :=
    sourceIdx_lower_col S M hM P (fujiSrcRowAt P i k (isRepAt P j) isAsc) j hry hn
      hjn hlive hlast
  refine ⟨hpp, q, ?_, hcol⟩
  rw [← hcolsrc]
  exact hq

/-- `isRepAt` と `j = y` は同じ判定。 -/
theorem isRepAt_eq_lower (P : FujiParams) (hsm : P.badRootSeam = y) (j : Nat) :
    (if isRepAt P j then 1 else 0) = (if j = y then 1 else 0) := by
  show (if (decide (j = P.badRootSeam)) = true then 1 else 0) = _
  rw [hsm]
  simp

/-- **原文に親があれば JS も親を見つける。** -/
theorem fujiCellAt_par_some_of_parent_lower (S : Setting) (M : List Rowj) (hM : MtRep S M)
    (P : FujiParams) (hyk : P.yamakazi = false)
    (hbh : P.badRootHeight = height S.tower.base y)
    (hcut : P.cutHeight = height S.tower.base x)
    (hsm : P.badRootSeam = y) (hlen : P.len = x - y) (hx : x = S.n - 1)
    (hyx : y < x) (hroot) (hhigher)
    (nd : Nat → Nat) (st : List Rowj) (i j k pc : Nat) (isAsc : Bool)
    (hasc : isAsc = true ↔ (lowerContext S y x hyx hroot hhigher).InCone j)
    (hi : 0 < i) (hjy : y ≤ j) (hjx : j < x)
    (hk : j = y → k ≤ height S.tower.base y
      + (height S.tower.base x - height S.tower.base y) * i)
    (hry : fujiSrcRowAt P i k (isRepAt P j) isAsc < M.length)
    (hn : 1 < S.n)
    (hlive : isRepAt P j = false →
      0 < (rows S.tower.base (fujiSrcRowAt P i k (isRepAt P j) isAsc)).value j)
    (hlast : isRepAt P j = true →
      0 < (rows S.tower.base (fujiSrcRowAt P i k (isRepAt P j) isAsc)).value (S.n - 1))
    (hmono : PosMono (rowAt st k)) (hcov : HasCol st k pc)
    (hpc : (lowerContext S y x hyx hroot hhigher).parent k (j + (x - y) * i) = some pc) :
    ∃ u, (fujiCellAt M P nd i j (isRepAt P j) isAsc st k).par = some u := by
  have hpcM : ((lowerContext S y x hyx hroot hhigher).toRowMountain.row k).parent
      (j + (x - y) * i) = some pc := hpc
  have hkpc : k ≤ pc := by
    have h1 : k ≤ ((lowerContext S y x hyx hroot hhigher).toRowMountain).height pc :=
      ((lowerContext S y x hyx hroot hhigher).toRowMountain).parent_endpoint hpcM
    have h2 := rowMountain_height_le ((lowerContext S y x hyx hroot hhigher).toRowMountain) pc
    omega
  rw [lowerContext_parent_src hyx hroot hhigher P hbh hcut hsm k i j hi hjy hjx isAsc hasc hk]
    at hpc
  obtain ⟨q, hq, hpceq0⟩ := Option.map_eq_some_iff.mp hpc
  have hpceq : q + (if y ≤ q then (i - (if j = y then 1 else 0)) * (x - y) else 0) = pc :=
    hpceq0
  obtain ⟨hsx, hcolsrc⟩ :=
    sourceIdx_lower_col S M hM P (fujiSrcRowAt P i k (isRepAt P j) isAsc) j hry hn
      (by omega) hlive hlast
  have hsrceq : (if j = P.badRootSeam then S.n - 1 else j) = (if j = y then x else j) := by
    rw [hsm, hx]
  have hF : (rows S.tower.base (fujiSrcRowAt P i k (isRepAt P j) isAsc)).forest.parent
      (((rowAt M (fujiSrcRowAt P i k (isRepAt P j) isAsc))[sourceIdx M
        (fujiSrcRowAt P i k (isRepAt P j) isAsc) j (isRepAt P j)]'hsx).pos
        + fujiSrcRowAt P i k (isRepAt P j) isAsc) = some q := by
    rw [hcolsrc, hsrceq]
    exact hq
  have hir := isRepAt_eq_lower P hsm j
  have hge : k ≤ q + (if P.badRootSeam ≤ q then
      (i - (if isRepAt P j then 1 else 0)) * P.len else 0) := by
    rw [hsm, hir, hlen]
    omega
  have hpp := parentPos_some S M hM P (fujiSrcRowAt P i k (isRepAt P j) isAsc) _ k
    (i - (if isRepAt P j then 1 else 0)) q hry hsx
    (fujiSrcRowAt_le P i k (isRepAt P j) isAsc) hF hge
  rw [← hir] at hpceq
  rw [hsm, hlen, hpceq] at hpp
  obtain ⟨u, hu, hupos⟩ := hasCol_pos st k pc hcov
  refine ⟨u, ?_⟩
  refine fujiCellAt_par_isSome M P nd i j (isRepAt P j) isAsc st k (pc - k) hmono ?_ u hu
    (by omega)
  rw [fujiSourceAt_notyama P hyk i k (isRepAt P j) isAsc]
  exact hpp

/-- **JS の親のセルの列は原文の親である。** -/
theorem fujiCellAt_parCol_lower (S : Setting) (M : List Rowj) (hM : MtRep S M)
    (P : FujiParams) (hyk : P.yamakazi = false)
    (hbh : P.badRootHeight = height S.tower.base y)
    (hcut : P.cutHeight = height S.tower.base x)
    (hsm : P.badRootSeam = y) (hlen : P.len = x - y) (hx : x = S.n - 1)
    (hyx : y < x) (hroot) (hhigher)
    (nd : Nat → Nat) (res : List Rowj) (i j k p : Nat) (isAsc : Bool)
    (hasc : isAsc = true ↔ (lowerContext S y x hyx hroot hhigher).InCone j)
    (hi : 0 < i) (hjy : y ≤ j) (hjx : j < x)
    (hk : j = y → k ≤ height S.tower.base y
      + (height S.tower.base x - height S.tower.base y) * i)
    (hry : fujiSrcRowAt P i k (isRepAt P j) isAsc < M.length)
    (hn : 1 < S.n)
    (hlive : isRepAt P j = false →
      0 < (rows S.tower.base (fujiSrcRowAt P i k (isRepAt P j) isAsc)).value j)
    (hlast : isRepAt P j = true →
      0 < (rows S.tower.base (fujiSrcRowAt P i k (isRepAt P j) isAsc)).value (S.n - 1))
    (hp : (fujiCellAt M P nd i j (isRepAt P j) isAsc res k).par = some p) :
    ∃ hp' : p < (rowAt res k).size,
      (lowerContext S y x hyx hroot hhigher).parent k (j + (x - y) * i)
        = some (((rowAt res k)[p]'hp').pos + k) := by
  obtain ⟨hpp, q, hq, hcol⟩ :=
    fujiCellAt_par_lower S M hM P hyk nd i j isAsc res k hry hn (by omega) hlive hlast
      (lowerContext S y x hyx hroot hhigher).coordinates (by rw [hsm]; rfl)
      (by rw [hlen]; rfl) p hp
  refine ⟨hpp, ?_⟩
  rw [lowerContext_parent_src hyx hroot hhigher P hbh hcut hsm k i j hi hjy hjx isAsc hasc hk]
  have hsrceq : (if j = P.badRootSeam then S.n - 1 else j) = (if j = y then x else j) := by
    rw [hsm, hx]
  rw [hsrceq] at hq
  rw [hq, hcol, parentCopy_eq, lowerContext_y_eq, lowerContext_length_eq,
    isRepAt_eq_lower P hsm j]
  rfl

/-- **JS が親を見つけなければ原文でも根。** -/
theorem fujiCellAt_parNone_lower (S : Setting) (M : List Rowj) (hM : MtRep S M)
    (P : FujiParams) (hyk : P.yamakazi = false)
    (hbh : P.badRootHeight = height S.tower.base y)
    (hcut : P.cutHeight = height S.tower.base x)
    (hsm : P.badRootSeam = y) (hlen : P.len = x - y) (hx : x = S.n - 1)
    (hyx : y < x) (hroot) (hhigher)
    (nd : Nat → Nat) (st : List Rowj) (i j k : Nat) (isAsc : Bool)
    (hasc : isAsc = true ↔ (lowerContext S y x hyx hroot hhigher).InCone j)
    (hi : 0 < i) (hjy : y ≤ j) (hjx : j < x)
    (hk : j = y → k ≤ height S.tower.base y
      + (height S.tower.base x - height S.tower.base y) * i)
    (hry : fujiSrcRowAt P i k (isRepAt P j) isAsc < M.length)
    (hn : 1 < S.n)
    (hlive : isRepAt P j = false →
      0 < (rows S.tower.base (fujiSrcRowAt P i k (isRepAt P j) isAsc)).value j)
    (hlast : isRepAt P j = true →
      0 < (rows S.tower.base (fujiSrcRowAt P i k (isRepAt P j) isAsc)).value (S.n - 1))
    (hmono : PosMono (rowAt st k))
    (hcov : ∀ pc, pc < j + (x - y) * i →
      k ≤ (lowerContext S y x hyx hroot hhigher).height pc → HasCol st k pc)
    (hnone : (fujiCellAt M P nd i j (isRepAt P j) isAsc st k).par = none) :
    (lowerContext S y x hyx hroot hhigher).parent k (j + (x - y) * i) = none := by
  cases hp : (lowerContext S y x hyx hroot hhigher).parent k (j + (x - y) * i) with
  | none => rfl
  | some pc =>
      exfalso
      have hpcM : ((lowerContext S y x hyx hroot hhigher).toRowMountain.row k).parent
          (j + (x - y) * i) = some pc := hp
      have hlt : pc < j + (x - y) * i :=
        ((lowerContext S y x hyx hroot hhigher).toRowMountain.row k).parent_left hpcM
      have hge : k ≤ (lowerContext S y x hyx hroot hhigher).height pc :=
        ((lowerContext S y x hyx hroot hhigher).toRowMountain).parent_endpoint hpcM
      obtain ⟨u, hu⟩ :=
        fujiCellAt_par_some_of_parent_lower S M hM P hyk hbh hcut hsm hlen hx hyx hroot hhigher
          nd st i j k pc isAsc hasc hi hjy hjx hk hry hn hlive hlast hmono
          (hcov pc hlt hge) hp
      rw [hu] at hnone
      exact absurd hnone (by simp)

/-! ## 積む段の数

この枝では `kmax` は原文の高さ + 1 である（`kmaxAt_eq_height_lower`）。
`expRes` を使う形にしておく。 -/

/-- **`kmax` は原文の高さ + 1（`expRes` の形）。** -/
theorem kmaxAt_lower (S : Setting) (M : List Rowj) (hM : MtRep S M) (mfuel : Nat)
    (hn : 1 < S.n) (hM2 : 2 ≤ M.length) (P : FujiParams)
    (hbh : P.badRootHeight = height S.tower.base y)
    (hsm : P.badRootSeam = y) (hcut : P.cutHeight = height S.tower.base x)
    (hx : x = S.n - 1) (hyx : y < x) (hroot) (hhigher)
    (hfuel : (rowAt M (height S.tower.base y)).size ≤ mfuel)
    (i j : Nat) (hj1 : y ≤ j) (hj2 : j < x) :
    kmaxAt M P i j (expRes M).length mfuel
      = (lowerContext S y x hyx hroot hhigher).height (j + (x - y) * i) + 1 := by
  have hjn : j < S.n := by omega
  have hbhlen : height S.tower.base y < M.length := hM.tall y (by omega)
  exact kmaxAt_eq_height_lower M hM P hyx hroot hhigher hbh hsm hcut
    (expRes M).length mfuel i j hj1 hj2 hjn
    (seamHeightOf_expRes S M hM hn hM2 j (by omega)) hbhlen hfuel

/-! ## 落差は幅を超えない

段 `r ∈ [floor, height x]` について `rootAt r x` は真に増える。`rootAt floor x = y`
で `rootAt (height x) x = x` なので、段の数だけ列が進む。 -/

theorem rootAt_ge_of_gap (S : Setting) (x : Nat) (y : Nat)
    (hroot : (mountainOf' S).rootAt (height S.tower.base y) x = y) :
    ∀ d, height S.tower.base y + d ≤ height S.tower.base x →
      y + d ≤ (mountainOf' S).rootAt (height S.tower.base y + d) x := by
  intro d
  induction d with
  | zero =>
      intro _
      have h0 : height S.tower.base y + 0 = height S.tower.base y := by omega
      rw [h0, hroot]
      omega
  | succ d ih =>
      intro hd
      have h1 := ih (by omega)
      have h2 : (mountainOf' S).rootAt (height S.tower.base y + d) x
          < (mountainOf' S).rootAt (height S.tower.base y + (d + 1)) x :=
        (mountainOf' S).rootAt_strict_mono (by omega) (show height S.tower.base y + (d + 1)
          ≤ (mountainOf' S).height x from hd)
      omega

/-- **落差は幅を超えない。** -/
theorem rise_le_length (S : Setting) (y x : Nat)
    (hroot : (mountainOf' S).rootAt (height S.tower.base y) x = y)
    (hhigher : height S.tower.base y < height S.tower.base x) :
    height S.tower.base x - height S.tower.base y ≤ x - y := by
  have hd : height S.tower.base y + (height S.tower.base x - height S.tower.base y)
      = height S.tower.base x := by omega
  have h := rootAt_ge_of_gap S x y hroot
    (height S.tower.base x - height S.tower.base y) (by omega)
  rw [hd] at h
  have htop : (mountainOf' S).rootAt (height S.tower.base x) x = x :=
    (mountainOf' S).top_root x
  rw [htop] at h
  omega

/-- **積む段の数の一様な上界。** -/
theorem kmaxAt_le_lower' (S : Setting) (M : List Rowj) (P : FujiParams)
    (y x : Nat)
    (hbh : P.badRootHeight = height S.tower.base y)
    (hcut : P.cutHeight = height S.tower.base x) (hlen : P.len = x - y)
    (hroot : (mountainOf' S).rootAt (height S.tower.base y) x = y)
    (hhigher : height S.tower.base y < height S.tower.base x)
    (i j ach af : Nat) :
    kmaxAt M P i j ach af ≤ j + P.len * i + 1 := by
  refine kmaxAt_le' M P i j ach af ?_
  rw [hbh, hcut, hlen]
  exact rise_le_length S y x hroot hhigher

/-! ## この枝で作る疎な山の形 -/

/-- コピー 1 つぶんの長さ。 -/
theorem expP_len_lower (S : Setting) (M : List Rowj) (hM : MtRep S M) (mfuel : Nat)
    (h0 : 0 < (expRes M).length) (y x : Nat)
    (hsm : (expP M mfuel).badRootSeam = y) (hx : x = S.n - 1) :
    (expP M mfuel).len = x - y := by
  show (expP M mfuel).afterCutLength - (expP M mfuel).badRootSeam = x - y
  rw [expP_afterCutLength S M hM mfuel h0, hsm, hx]

/-! ## 上りの判定と元の段の上界 -/

/-- **JS の上り判定は原文の `InCone`。** -/
theorem hasc_lower (S : Setting) (M : List Rowj) (hM : MtRep S M) (mfuel : Nat)
    (P : FujiParams) (y x : Nat)
    (hbh : P.badRootHeight = height S.tower.base y) (hsm : P.badRootSeam = y)
    (hyx : y < x)
    (hroot : (mountainOf' S).rootAt (height S.tower.base y) x = y)
    (hhigher : height S.tower.base y < height S.tower.base x)
    (hfuel : (rowAt M (height S.tower.base y)).size ≤ mfuel)
    (hyn : y < S.n) (j : Nat) (hjn : j < S.n) :
    isAscAt M P j mfuel = true ↔ (lowerContext S y x hyx hroot hhigher).InCone j := by
  have hbhlen : height S.tower.base y < M.length := hM.tall y hyn
  show isAscending M P.badRootHeight P.badRootSeam j mfuel = true ↔ _
  rw [hbh, hsm]
  exact isAscending_iff_inCone M hM hyx hroot hhigher j mfuel hbhlen hjn hfuel

/-- **継ぎ目でない列では、元の段はその列の高さ以下。** -/
theorem srcRow_le_other (S : Setting) (P : FujiParams) (y x : Nat)
    (hbh : P.badRootHeight = height S.tower.base y)
    (hcut : P.cutHeight = height S.tower.base x)
    (hyx : y < x)
    (hroot : (mountainOf' S).rootAt (height S.tower.base y) x = y)
    (hhigher : height S.tower.base y < height S.tower.base x)
    (i k j : Nat) (_hi : 0 < i) (hjy : y < j) (hjx : j ≤ x) (isRep isAsc : Bool)
    (hrep : isRep = false)
    (hasc : isAsc = true ↔ (lowerContext S y x hyx hroot hhigher).InCone j)
    (hk : k ≤ (lowerContext S y x hyx hroot hhigher).height (j + (x - y) * i)) :
    fujiSrcRowAt P i k isRep isAsc ≤ height S.tower.base j := by
  rw [lowerContext_height_other hyx hroot hhigher j i hjy hjx] at hk
  rw [fujiSrcRowAt_eq P hbh hcut i k isRep isAsc (by rw [hrep]; intro hc; cases hc)]
  rcases Decidable.em ((lowerContext S y x hyx hroot hhigher).InCone j) with hc | hc
  · rw [if_pos hc] at hk
    have hfl : height S.tower.base y ≤ height S.tower.base j := hc.1
    rcases Decidable.em (isAsc = true ∧ height S.tower.base y ≤ k) with hcc | hcc
    · rw [if_pos hcc, hrep]
      simp only [Bool.false_eq_true, if_false, Nat.sub_zero, Nat.max_def]
      split <;> omega
    · rw [if_neg hcc]
      rcases Decidable.em (height S.tower.base y ≤ k) with h1 | h1
      · exact absurd ⟨hasc.mpr hc, h1⟩ hcc
      · omega
  · rw [if_neg hc] at hk
    have hnot : isAsc = false := by
      cases hA : isAsc with
      | true => exact absurd (hasc.mp hA) hc
      | false => rfl
    rw [if_neg (by rw [hnot]; rintro ⟨h1, -⟩; cases h1)]
    exact hk

/-- **継ぎ目の列では、元の段は `x` の高さ以下。** -/
theorem srcRow_le_seam (S : Setting) (P : FujiParams) (y x : Nat)
    (hbh : P.badRootHeight = height S.tower.base y)
    (hcut : P.cutHeight = height S.tower.base x)
    (_hyx : y < x)
    (hhigher : height S.tower.base y < height S.tower.base x)
    (i k : Nat) (hi : 0 < i) (isRep isAsc : Bool) (hasct : isAsc = true)
    (hk : k ≤ height S.tower.base y
      + (height S.tower.base x - height S.tower.base y) * i) :
    fujiSrcRowAt P i k isRep isAsc ≤ height S.tower.base x := by
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
  have hsucc : (m + 1) * (height S.tower.base x - height S.tower.base y)
      = m * (height S.tower.base x - height S.tower.base y)
        + (height S.tower.base x - height S.tower.base y) := Nat.succ_mul _ _
  have hm1 : (m + 1) - 1 = m := by omega
  have hcomm : (height S.tower.base x - height S.tower.base y) * (m + 1)
      = (m + 1) * (height S.tower.base x - height S.tower.base y) := Nat.mul_comm _ _
  have hcomm2 : (height S.tower.base x - height S.tower.base y) * m
      = m * (height S.tower.base x - height S.tower.base y) := Nat.mul_comm _ _
  rw [fujiSrcRowAt_eq P hbh hcut (m + 1) k isRep isAsc (fun _ => hk)]
  rcases Decidable.em (isAsc = true ∧ height S.tower.base y ≤ k) with hc | hc
  · rw [if_pos hc]
    cases isRep with
    | false =>
        simp only [Bool.false_eq_true, if_false, Nat.sub_zero, Nat.max_def]
        split <;> omega
    | true =>
        simp only [if_true, hm1, Nat.max_def]
        split <;> omega
  · rw [if_neg hc]
    have hlt : k < height S.tower.base y := by
      rcases Nat.lt_or_ge k (height S.tower.base y) with h1 | h1
      · exact h1
      · exact absurd ⟨hasct, h1⟩ hc
    omega

/-! ## 積んだセルの補助条件

`m < kmaxAt` から、段と列についての条件がまとめて出る。 -/

theorem push_side_lower (S : Setting) (M : List Rowj) (hM : MtRep S M) (mfuel : Nat)
    (hn : 1 < S.n) (hM2 : 2 ≤ M.length) (y x : Nat)
    (hbh : (expP M mfuel).badRootHeight = height S.tower.base y)
    (hsm : (expP M mfuel).badRootSeam = y)
    (hcut : (expP M mfuel).cutHeight = height S.tower.base x)
    (hx : x = S.n - 1) (hyx : y < x)
    (hroot : (mountainOf' S).rootAt (height S.tower.base y) x = y)
    (hhigher : height S.tower.base y < height S.tower.base x)
    (hfuel : (rowAt M (height S.tower.base y)).size ≤ mfuel)
    (i' t' m : Nat) (ht' : t' < (expP M mfuel).len)
    (hk' : m < kmaxAt M (expP M mfuel) (i' + 1) (y + t') (expRes M).length mfuel) :
    y + t' < x ∧
      m ≤ (lowerContext S y x hyx hroot hhigher).height ((y + t') + (x - y) * (i' + 1)) ∧
      fujiSrcRowAt (expP M mfuel) (i' + 1) m (isRepAt (expP M mfuel) (y + t'))
          (isAscAt M (expP M mfuel) (y + t') mfuel) < M.length ∧
      (isRepAt (expP M mfuel) (y + t') = false →
        0 < (rows S.tower.base (fujiSrcRowAt (expP M mfuel) (i' + 1) m
          (isRepAt (expP M mfuel) (y + t'))
          (isAscAt M (expP M mfuel) (y + t') mfuel))).value (y + t')) ∧
      (isRepAt (expP M mfuel) (y + t') = true →
        0 < (rows S.tower.base (fujiSrcRowAt (expP M mfuel) (i' + 1) m
          (isRepAt (expP M mfuel) (y + t'))
          (isAscAt M (expP M mfuel) (y + t') mfuel))).value (S.n - 1)) ∧
      ((y + t') = y → m ≤ height S.tower.base y
        + (height S.tower.base x - height S.tower.base y) * (i' + 1)) := by
  have h0 : 0 < (expRes M).length := expRes_length_pos M hM2
  have hlen : (expP M mfuel).len = x - y := expP_len_lower S M hM mfuel h0 y x hsm hx
  have hjx : y + t' < x := by omega
  have hjn : y + t' < S.n := by omega
  have hasc := hasc_lower S M hM mfuel (expP M mfuel) y x hbh hsm hyx hroot hhigher hfuel
    (by omega) (y + t') hjn
  have hm : m ≤ (lowerContext S y x hyx hroot hhigher).height ((y + t') + (x - y) * (i' + 1)) := by
    have := kmaxAt_lower S M hM mfuel hn hM2 (expP M mfuel) hbh hsm hcut hx hyx hroot hhigher
      hfuel (i' + 1) (y + t') (by omega) hjx
    omega
  -- 継ぎ目の列のときの段の上界
  have hseamk : (y + t') = y → m ≤ height S.tower.base y
      + (height S.tower.base x - height S.tower.base y) * (i' + 1) := by
    intro he
    have hcomm : (i' + 1) * (height S.tower.base x - height S.tower.base y)
        = (height S.tower.base x - height S.tower.base y) * (i' + 1) := Nat.mul_comm _ _
    rw [he, lowerContext_height_seam hyx hroot hhigher (i' + 1)] at hm
    omega
  -- 元の段の上界
  have hsyj : isRepAt (expP M mfuel) (y + t') = false →
      fujiSrcRowAt (expP M mfuel) (i' + 1) m (isRepAt (expP M mfuel) (y + t'))
        (isAscAt M (expP M mfuel) (y + t') mfuel) ≤ height S.tower.base (y + t') := by
    intro hrep
    have hne : y + t' ≠ y := by
      intro he
      have : isRepAt (expP M mfuel) (y + t') = true := by
        show decide (y + t' = (expP M mfuel).badRootSeam) = true
        rw [hsm, he]
        simp
      rw [this] at hrep
      cases hrep
    exact srcRow_le_other S (expP M mfuel) y x hbh hcut hyx hroot hhigher (i' + 1) m (y + t')
      (by omega) (by omega) (by omega) _ _ hrep hasc hm
  have hsyx : isRepAt (expP M mfuel) (y + t') = true →
      fujiSrcRowAt (expP M mfuel) (i' + 1) m (isRepAt (expP M mfuel) (y + t'))
        (isAscAt M (expP M mfuel) (y + t') mfuel) ≤ height S.tower.base x := by
    intro hrep
    have he : y + t' = y := by
      have := of_decide_eq_true hrep
      omega
    have hasct : isAscAt M (expP M mfuel) (y + t') mfuel = true := by
      rw [he] at hasc ⊢
      exact hasc.mpr (inCone_seam hyx hroot hhigher)
    exact srcRow_le_seam S (expP M mfuel) y x hbh hcut hyx hhigher (i' + 1) m (by omega) _ _
      hasct (hseamk he)
  have htallj : height S.tower.base (y + t') < M.length := hM.tall (y + t') hjn
  have htallx : height S.tower.base x < M.length := hM.tall x (by omega)
  refine ⟨hjx, hm, ?_, ?_, ?_, hseamk⟩
  · rcases Decidable.em (isRepAt (expP M mfuel) (y + t') = true) with hrep | hrep
    · have := hsyx hrep
      omega
    · have hf : isRepAt (expP M mfuel) (y + t') = false := by
        cases h : isRepAt (expP M mfuel) (y + t') with
        | true => exact absurd h hrep
        | false => rfl
      have := hsyj hf
      omega
  · intro hrep
    exact (live_iff_le_height S.tower.base (S.tower.hpos (y + t')) _).mpr (hsyj hrep)
  · intro hrep
    have hxn : x = S.n - 1 := hx
    rw [← hxn]
    exact (live_iff_le_height S.tower.base (S.tower.hpos x) _).mpr (hsyx hrep)

/-! ## 積む時点での被覆と単調性 -/

/-! ## この枝の `FujiSpec` -/

/-- **`k < K` の枝の `FujiSpec`。** -/
theorem lowerSpec (S : Setting) (M : List Rowj) (hM : MtRep S M) (mfuel : Nat)
    (hn : 1 < S.n) (hM2 : 2 ≤ M.length) (y x : Nat)
    (hbh : (expP M mfuel).badRootHeight = height S.tower.base y)
    (hsm : (expP M mfuel).badRootSeam = y)
    (hcut : (expP M mfuel).cutHeight = height S.tower.base x)
    (hx : x = S.n - 1) (hyx : y < x)
    (hroot : (mountainOf' S).rootAt (height S.tower.base y) x = y)
    (hhigher : height S.tower.base y < height S.tower.base x)
    (hfuel : (rowAt M (height S.tower.base y)).size ≤ mfuel)
    (hyk : (expP M mfuel).yamakazi = false) :
    FujiSpec S M mfuel (lowerContext S y x hyx hroot hhigher).toRowMountain y x where
  hM := hM
  hn := hn
  hM2 := hM2
  hx := hx
  hyx := hyx
  hsm := hsm
  hkm := fun i j => kmaxAt_le_lower' S M (expP M mfuel) y x hbh hcut
    (expP_len_lower S M hM mfuel (expRes_length_pos M hM2) y x hsm hx) hroot hhigher i j _ _
  heightOrig := fun c hc => lowerContext_height_orig hyx hroot hhigher c (by omega)
  parentOrig := fun r c hc => by
    show (lowerContext S y x hyx hroot hhigher).parent r c = _
    rw [(lowerContext S y x hyx hroot hhigher).parent_original
      (show c ≤ (lowerContext S y x hyx hroot hhigher).coordinates.x by show c ≤ x; omega),
      lowerContext_row]
  kmaxHeight := fun i j _ hjy hjx => by
    have := kmaxAt_lower S M hM mfuel hn hM2 (expP M mfuel) hbh hsm hcut hx hyx hroot hhigher
      hfuel i j hjy hjx
    rw [expP_len_lower S M hM mfuel (expRes_length_pos M hM2) y x hsm hx]
    exact this
  parNoneCell := fun nd st i' t' m ht' hk' hmono hcov hnone => by
    have hlen := expP_len_lower S M hM mfuel (expRes_length_pos M hM2) y x hsm hx
    obtain ⟨hjx, _, hmM, hlive, hlast, hseamk⟩ :=
      push_side_lower S M hM mfuel hn hM2 y x hbh hsm hcut hx hyx hroot hhigher hfuel
        i' t' m ht' hk'
    rw [hlen]
    exact fujiCellAt_parNone_lower S M hM (expP M mfuel) hyk hbh hcut hsm hlen hx hyx hroot
      hhigher nd st (i' + 1) (y + t') m _
      (hasc_lower S M hM mfuel (expP M mfuel) y x hbh hsm hyx hroot hhigher hfuel (by omega)
        (y + t') (by omega))
      (by omega) (by omega) hjx hseamk hmM hn hlive hlast hmono
      (fun pc hlt hge => hcov pc (by rw [hlen]; exact hlt) hge) hnone
  parColCell := fun nd st i' t' m p ht' hk' hsome => by
    have hlen := expP_len_lower S M hM mfuel (expRes_length_pos M hM2) y x hsm hx
    obtain ⟨hjx, _, hmM, hlive, hlast, hseamk⟩ :=
      push_side_lower S M hM mfuel hn hM2 y x hbh hsm hcut hx hyx hroot hhigher hfuel
        i' t' m ht' hk'
    rw [hlen]
    exact fujiCellAt_parCol_lower S M hM (expP M mfuel) hyk hbh hcut hsm hlen hx hyx hroot
      hhigher nd st (i' + 1) (y + t') m p _
      (hasc_lower S M hM mfuel (expP M mfuel) y x hbh hsm hyx hroot hhigher hfuel (by omega)
        (y + t') (by omega))
      (by omega) (by omega) hjx hseamk hmM hn hlive hlast hsome

/-! ## 原文の `badAtLowerContext` との同定 -/

/-- **bad root の層より下では、`hroot` と `hhigher` が原文から出る。** -/
theorem lower_root_higher (s : List Nat) (hs : ZeroY.Legal s) (K d x y k : Nat)
    (hbad : BadAt (rootedSequence s hs) K d x y) (hk : k < K) :
    (mountainOf' (iterSet (linearSetting s hs.1) k)).rootAt
        (height (iterSet (linearSetting s hs.1) k).tower.base y) x = y ∧
      height (iterSet (linearSetting s hs.1) k).tower.base y
        < height (iterSet (linearSetting s hs.1) k).tower.base x := by
  have hb : (iterSet (linearSetting s hs.1) k).tower.base
      = (layers (rootedSequence s hs) k).row := iterSet_base s hs k
  obtain ⟨h1, h2⟩ := active_parent_lower_root (rootedSequence s hs) hbad.1 hk
  refine ⟨?_, ?_⟩
  · show (rows (iterSet (linearSetting s hs.1) k).tower.base
      (height (iterSet (linearSetting s hs.1) k).tower.base y)).forest.root x = y
    rw [hb]
    exact h2
  · rw [hb]
    exact h1

/-- **こちらで組んだ `LowerCopy.Context` は原文の `badAtLowerContext`。** -/
theorem lowerContext_eq (s : List Nat) (hs : ZeroY.Legal s) (K d x y k : Nat)
    (hbad : BadAt (rootedSequence s hs) K d x y) (hk : k < K) (hyx : y < x)
    (hroot : (mountainOf' (iterSet (linearSetting s hs.1) k)).rootAt
      (height (iterSet (linearSetting s hs.1) k).tower.base y) x = y)
    (hhigher : height (iterSet (linearSetting s hs.1) k).tower.base y
      < height (iterSet (linearSetting s hs.1) k).tower.base x) :
    lowerContext (iterSet (linearSetting s hs.1) k) y x hyx hroot hhigher
      = badAtLowerContext (rootedSequence s hs) hbad hk := by
  have hb : (iterSet (linearSetting s hs.1) k).tower.base
      = (layers (rootedSequence s hs) k).row := iterSet_base s hs k
  unfold lowerContext badAtLowerContext activeLowerContext
  congr 1
  unfold mountainOf'
  congr 1

/-! ## 上の層の畳み込み

`k+1` 段目以上を畳んだ値は、列 `x` より左では層 `k+1` の値そのものである。
原文の `assemble_family_prefix`（前置きが一致すれば畳み込みも一致する）と
`assemble_originalGraphs`（元の塔の畳み込みはその層の値）から出る。 -/

theorem assemble_above_layer (s : List Nat) (hs : ZeroY.Legal s) {K d x y : Nat}
    (hbad : BadAt (rootedSequence s hs) K d x y) (k : Nat) {c : Nat} (hc : c < x)
    (hk : k + 1 ≤ sequenceBound s) :
    TowerReconstruction.assemble
        ((List.range' (k + 1) (sequenceBound s - (k + 1))).map
          (expandedMountain (rootedSequence s hs) hbad)) (fun _ => 1) c
      = (layers (rootedSequence s hs) (k + 1)).row.value c := by
  have h := TowerReconstruction.assemble_family_prefix
    (expandedMountain (rootedSequence s hs) hbad)
    (fun j => mountain (layers (rootedSequence s hs) j).row
      (layers (rootedSequence s hs) j).positive)
    (fun _ => 1) (fun _ => 1) x
    (fun j _ hc' => expandedMountain_height_original _ hbad j hc')
    (fun j r _ hc' => expandedMountain_parent_original _ hbad j r hc')
    (fun _ _ => rfl) (k + 1) (sequenceBound s - (k + 1)) c hc
  have hone : (layers (rootedSequence s hs)
      ((k + 1) + (sequenceBound s - (k + 1)))).row.value = (fun _ => 1) := by
    funext c'
    exact sequence_layers_all_one s hs (by omega) c'
  have h2 := TowerReconstruction.assemble_originalGraphs (rootedSequence s hs) (k + 1)
    (sequenceBound s - (k + 1))
  rw [hone] at h2
  rw [h]
  exact congrFun h2 c

/-! ## 層の再帰

`k < K` の枝では、新しい対角は対角の山を展開した行 0 の値である。上の層の
畳み込みと突き合わせると、層が 1 つ降りる。 -/

/-- `expandOut` の要素は行 0 の値そのもの。 -/
theorem valAtIdx_of_expandOut (M' : List Rowj) (W : Nat) (f : Nat → Nat)
    (h : expandOut M' = (List.range W).map f) (c : Nat) (hc : c < W) :
    valAtIdx (rowAt M' 0) c = f c := by
  have hlen : (rowAt M' 0).size = W := by
    have hl := congrArg List.length h
    simpa [expandOut] using hl
  have hc' : c < (rowAt M' 0).size := by omega
  have h2 : (expandOut M')[c]? = ((List.range W).map f)[c]? := by rw [h]
  rw [show expandOut M' = (rowAt M' 0).toList.map (fun d => d.val) from rfl] at h2
  simp only [List.getElem?_map, List.getElem?_range, Array.getElem?_toList,
    Array.getElem?_eq_getElem hc', hc, Option.map_some] at h2
  unfold valAtIdx
  rw [dif_pos hc']
  exact Option.some.inj h2

/-- **層が 1 つ降りる。** 対角の展開が `k+1` 段目以上の畳み込みなら、
この層の展開は `k` 段目以上の畳み込みである。 -/
theorem expandOut_step_lower (s : List Nat) (hs : ZeroY.Legal s) {K d x y : Nat}
    (hbad : BadAt (rootedSequence s hs) K d x y) (hK : K < sequenceBound s)
    (hxs : s.length - 1 = x) (hyx : y < x) (k : Nat) (hk : k < K)
    (M : List Rowj) (mfuel efuel nrep : Nat)
    (hM : MtRep (iterSet (linearSetting s hs.1) k) M) (hM2 : 2 ≤ M.length)
    (hbh : (expP M mfuel).badRootHeight
      = height (iterSet (linearSetting s hs.1) k).tower.base y)
    (hsm : (expP M mfuel).badRootSeam = y)
    (hcut : (expP M mfuel).cutHeight
      = height (iterSet (linearSetting s hs.1) k).tower.base x)
    (hfuel : (rowAt M (height (iterSet (linearSetting s hs.1) k).tower.base y)).size ≤ mfuel)
    (hyk : ¬ expYama M mfuel)
    (hhas : (if hlt : (rowAt M 0).size - 1 < (rowAt M 0).size
          then (((rowAt M 0)[(rowAt M 0).size - 1]'hlt).par).isSome else false) = true)
    (hIH : expandOut (expandJS nrep mfuel efuel (expDg M mfuel))
      = (List.range (x + (x - y) * nrep)).map
          (TowerReconstruction.assemble
            ((List.range' (k + 1) (sequenceBound s - (k + 1))).map
              (expandedMountain (rootedSequence s hs) hbad)) (fun _ => 1))) :
    expandOut (expandJS nrep mfuel (efuel + 1) M)
      = (List.range (x + (x - y) * nrep)).map
          (TowerReconstruction.assemble
            ((List.range' k (sequenceBound s - k)).map
              (expandedMountain (rootedSequence s hs) hbad)) (fun _ => 1)) := by
  have hnn : (iterSet (linearSetting s hs.1) k).n = s.length := iterSet_n s hs.1 k
  have hb : (iterSet (linearSetting s hs.1) k).tower.base
      = (layers (rootedSequence s hs) k).row := iterSet_base s hs k
  have hx : x = (iterSet (linearSetting s hs.1) k).n - 1 := by omega
  have hn : 1 < (iterSet (linearSetting s hs.1) k).n := by omega
  obtain ⟨hroot, hhigher⟩ := lower_root_higher s hs K d x y k hbad hk
  have h0 : 0 < (expRes M).length := expRes_length_pos M hM2
  have hlenP : (expP M mfuel).len = x - y :=
    expP_len_lower (iterSet (linearSetting s hs.1) k) M hM mfuel h0 y x hsm hx
  have hyk' : (expP M mfuel).yamakazi = false :=
    expP_yamakazi_lower M mfuel hyk
  -- 上の層の畳み込み
  have hup : ∀ c, c < x + (x - y) * nrep →
      expNd nrep mfuel efuel M c
        = TowerReconstruction.assemble
            ((List.range' (k + 1) (sequenceBound s - (k + 1))).map
              (expandedMountain (rootedSequence s hs) hbad)) (fun _ => 1) c := by
    intro c hc
    rw [expNd_not_yama nrep mfuel efuel M hyk]
    exact valAtIdx_of_expandOut _ _ _ hIH c hc
  have hnd : ∀ c, c < (iterSet (linearSetting s hs.1) k).n - 1 →
      expNd nrep mfuel efuel M c
        = topValue (iterSet (linearSetting s hs.1) k).tower.base c := by
    intro c hc
    rw [hup c (by omega), assemble_above_layer s hs hbad k (by omega) (by omega), hb]
    rfl
  have hndpos : ∀ c, c < x + (expP M mfuel).len * nrep → 0 < expNd nrep mfuel efuel M c := by
    intro c hc
    rw [hlenP] at hc
    rw [hup c hc]
    exact TowerReconstruction.assemble_positive _ _ (fun _ => by decide) c
  -- JS の出力
  have hjs := (lowerSpec (iterSet (linearSetting s hs.1) k) M hM mfuel hn hM2 y x
    hbh hsm hcut hx hyx hroot hhigher hfuel hyk').outJS nrep efuel hnd hndpos hhas
  rw [hlenP] at hjs
  rw [hjs]
  -- 原文側を 1 段ほどく
  have hsplit : sequenceBound s - k = (sequenceBound s - (k + 1)) + 1 := by omega
  have hG : expandedMountain (rootedSequence s hs) hbad k
      = (lowerContext (iterSet (linearSetting s hs.1) k) y x hyx hroot hhigher).toRowMountain := by
    rw [lowerContext_eq s hs K d x y k hbad hk hyx hroot hhigher]
    show _ = (badAtLowerContext (rootedSequence s hs) hbad hk).toRowMountain
    simp only [expandedMountain, dif_pos hk]
  refine List.map_congr_left ?_
  intro c hc
  have hc' : c < x + (x - y) * nrep := by
    rw [List.mem_range] at hc
    exact hc
  rw [hsplit]
  show _ = TowerReconstruction.assemble
    ((List.range' k ((sequenceBound s - (k + 1)) + 1)).map
      (expandedMountain (rootedSequence s hs) hbad)) (fun _ => 1) c
  rw [List.range'_succ]
  show _ = Reconstruction.value (expandedMountain (rootedSequence s hs) hbad k)
    (TowerReconstruction.assemble
      ((List.range' (k + 1) (sequenceBound s - (k + 1))).map
        (expandedMountain (rootedSequence s hs) hbad)) (fun _ => 1)) 0 c
  rw [hG]
  exact Reconstruction.value_prefix_congr _ _ _ _ (x + (x - y) * nrep)
    (fun _ _ => rfl) (fun _ _ _ => rfl) hup c hc' 0

/-- **層 `K`（山崎噴火の枝）が再帰の底。** -/
theorem expandOut_base_yama (s : List Nat) (hs : ZeroY.Legal s) {K d x y : Nat}
    (hbad : BadAt (rootedSequence s hs) K d x y) (hK : K < sequenceBound s)
    (hxs : s.length - 1 = x) (hyx : y < x)
    (M : List Rowj) (f efuel nrep : Nat)
    (hM : MtRep (iterSet (linearSetting s hs.1) K) M) (hM2 : 2 ≤ M.length)
    (hyama : expYama M (f + 1)) (hsm : expSeam M (f + 1) = y)
    (hy : y < (iterSet (linearSetting s hs.1) K).n - 1)
    (hpar : ((mountainOf' (iterSet (linearSetting s hs.1) K)).row
        (height (iterSet (linearSetting s hs.1) K).tower.base
          ((iterSet (linearSetting s hs.1) K).n - 1) - 1)).parent
        ((iterSet (linearSetting s hs.1) K).n - 1) = some y)
    (hh : 0 < height (iterSet (linearSetting s hs.1) K).tower.base
      ((iterSet (linearSetting s hs.1) K).n - 1))
    (hfuel : (rowAt M (height (iterSet (linearSetting s hs.1) K).tower.base
      ((iterSet (linearSetting s hs.1) K).n - 1) - 1)).size ≤ f + 1)
    (hhas : (if hlt : (rowAt M 0).size - 1 < (rowAt M 0).size
          then (((rowAt M 0)[(rowAt M 0).size - 1]'hlt).par).isSome else false) = true) :
    expandOut (expandJS nrep (f + 1) (efuel + 1) M)
      = (List.range (x + (x - y) * nrep)).map
          (TowerReconstruction.assemble
            ((List.range' K (sequenceBound s - K)).map
              (expandedMountain (rootedSequence s hs) hbad)) (fun _ => 1)) := by
  have hnn : (iterSet (linearSetting s hs.1) K).n = s.length := iterSet_n s hs.1 K
  have hn : 1 < (iterSet (linearSetting s hs.1) K).n := by omega
  have h0 : 0 < (expRes M).length := expRes_length_pos M hM2
  have hseamP : (expP M (f + 1)).badRootSeam = y := hsm
  have hlenP : (expP M (f + 1)).len = (iterSet (linearSetting s hs.1) K).n - 1 - y :=
    expP_len_yama (iterSet (linearSetting s hs.1) K) M hM (f + 1) h0 y hseamP
  have hlen' : (expP M (f + 1)).len = x - y := by rw [hlenP]; omega
  -- 新しい対角は上の層の畳み込み
  have hnda : ∀ c, expNd nrep (f + 1) efuel M c
      = TowerReconstruction.assemble
          ((List.range' (K + 1) (sequenceBound s - (K + 1))).map
            (expandedMountain (rootedSequence s hs) hbad)) (fun _ => 1) c :=
    fun c => expNd_eq_assemble s hs hbad hK M hM f hn hyama hsm hxs nrep efuel c
  have hnd : ∀ c, c < (iterSet (linearSetting s hs.1) K).n - 1 →
      expNd nrep (f + 1) efuel M c
        = topValue (iterSet (linearSetting s hs.1) K).tower.base c := by
    intro c hc
    have hb : (iterSet (linearSetting s hs.1) K).tower.base
        = (layers (rootedSequence s hs) K).row := iterSet_base s hs K
    rw [hnda c, assemble_above_layer s hs hbad K (by omega) (by omega), hb]
    rfl
  have hndpos : ∀ c, 0 < expNd nrep (f + 1) efuel M c := by
    intro c
    rw [hnda c]
    exact TowerReconstruction.assemble_positive _ _ (fun _ => by decide) c
  have hjs := (yamaSpec (iterSet (linearSetting s hs.1) K) M hM (f + 1) hn hM2 hyama
    y hy hpar hh hseamP (isAscAt_seam_yama (iterSet (linearSetting s hs.1) K) M hM (f + 1) hn
      hyama y hy hpar hseamP hfuel)).outJS nrep efuel hnd (fun c _ => hndpos c) hhas
  have hwid : (iterSet (linearSetting s hs.1) K).n - 1 + (expP M (f + 1)).len * nrep
      = x + (x - y) * nrep := by rw [hlen']; omega
  rw [hwid] at hjs
  rw [hjs]
  have hsplit : sequenceBound s - K = (sequenceBound s - (K + 1)) + 1 := by omega
  have hG : expandedMountain (rootedSequence s hs) hbad K
      = ((yamaContext (iterSet (linearSetting s hs.1) K) y hy hpar hh)).toRowMountain := by
    rw [yamaContext_eq s hs K d x y hbad hxs hy hpar hh]
    show _ = (badAtTerminalContext (rootedSequence s hs) hbad).toRowMountain
    simp only [expandedMountain, Nat.lt_irrefl, ↓reduceDIte, ↓reduceIte]
    rfl
  refine List.map_congr_left ?_
  intro c hc
  rw [hsplit]
  show _ = TowerReconstruction.assemble
    ((List.range' K ((sequenceBound s - (K + 1)) + 1)).map
      (expandedMountain (rootedSequence s hs) hbad)) (fun _ => 1) c
  rw [List.range'_succ]
  show _ = Reconstruction.value (expandedMountain (rootedSequence s hs) hbad K)
    (TowerReconstruction.assemble
      ((List.range' (K + 1) (sequenceBound s - (K + 1))).map
        (expandedMountain (rootedSequence s hs) hbad)) (fun _ => 1)) 0 c
  rw [hG]
  congr 1
  funext c'
  exact hnda c'

/-! ## 再帰に必要な補助 -/

/-- 各段のセルの数は列の上限以下。 -/
theorem rowAt_size_le (S : Setting) (M : List Rowj) (hM : MtRep S M) (r : Nat) :
    (rowAt M r).size ≤ S.n := by
  rcases Nat.lt_or_ge r M.length with hr | hr
  · have hrep := rep_top S M hM r hr
    rcases Nat.eq_zero_or_pos (rowAt M r).size with hz | hpos
    · omega
    · have hlast : (rowAt M r).size - 1 < (rowAt M r).size := by omega
      have hge := posMono_add (rowAt M r) hrep.posMono ((rowAt M r).size - 1) 0
        ((rowAt M r).size - 1) (by omega) hlast (by omega)
      have hb := hrep.bound _ (mem_of_getElem _ ((rowAt M r).size - 1) hlast)
      omega
  · rw [rowAt_of_ge M r hr]
    simp

/-- 抽出しても値の上限は変わらない。 -/
theorem iterSet_bnd (S : Setting) (k : Nat) : (iterSet S k).bnd = S.bnd := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih

/-- **行 0 の最後のセルが親を持つこと。** -/
theorem hhas_of_parent (S : Setting) (M : List Rowj) (hM : MtRep S M) (hn : 1 < S.n)
    (hM0 : 0 < M.length)
    (hp : S.tower.base.forest.parent (S.n - 1) ≠ none) :
    (if hlt : (rowAt M 0).size - 1 < (rowAt M 0).size
      then (((rowAt M 0)[(rowAt M 0).size - 1]'hlt).par).isSome else false) = true := by
  have hsz := hM.size0
  have hlt : (rowAt M 0).size - 1 < (rowAt M 0).size := by omega
  rw [dif_pos hlt]
  have hpos : ((rowAt M 0)[(rowAt M 0).size - 1]'hlt).pos = (rowAt M 0).size - 1 :=
    pos_eq_index (rowAt M 0) S.n _ (rep_top S M hM 0 hM0) hsz _ hlt
  cases hq : ((rowAt M 0)[(rowAt M 0).size - 1]'hlt).par with
  | some _ => rfl
  | none =>
      exfalso
      have hF := parRep_none S M hM 0 hM0 _ hlt hq
      rw [hpos, hsz] at hF
      refine hp ?_
      have hF' : (rows S.tower.base 0).forest.parent (S.n - 1) = none := by simpa using hF
      exact hF'

/-- **層 `k ≤ K` では最後の列の値は 1 より大きい。** -/
theorem value_gt_one_layer (s : List Nat) (hs : ZeroY.Legal s) {K d x y : Nat}
    (hbad : BadAt (rootedSequence s hs) K d x y) (_hxs : s.length - 1 = x) (k : Nat)
    (hk : k ≤ K) :
    1 < (iterSet (linearSetting s hs.1) k).tower.base.value x := by
  have hb : (iterSet (linearSetting s hs.1) k).tower.base
      = (layers (rootedSequence s hs) k).row := iterSet_base s hs k
  have h1 := badAt_value_gt_one hbad
  have h2 := layers_value_antitone (rootedSequence s hs) hk x
  rw [hb]
  omega

/-- **層 `k < K` は山崎噴火の枝ではない。** -/
theorem not_expYama_layer (s : List Nat) (hs : ZeroY.Legal s) {K d x y : Nat}
    (hbad : BadAt (rootedSequence s hs) K d x y) (hxs : s.length - 1 = x) (k : Nat)
    (hk : k < K) (M : List Rowj) (f : Nat)
    (hM : MtRep (iterSet (linearSetting s hs.1) k) M)
    (hn : 1 < (iterSet (linearSetting s hs.1) k).n) :
    ¬ expYama M (f + 1) := by
  have hnn : (iterSet (linearSetting s hs.1) k).n = s.length := iterSet_n s hs.1 k
  have hb : (iterSet (linearSetting s hs.1) k).tower.base
      = (layers (rootedSequence s hs) k).row := iterSet_base s hs k
  intro hy
  have hlv : lastVal (rowAt (expDg M (f + 1)) 0)
      = topValue (iterSet (linearSetting s hs.1) k).tower.base
        ((iterSet (linearSetting s hs.1) k).n - 1) :=
    lastVal_expDg (iterSet (linearSetting s hs.1) k) M hM f hn
  have hone : topValue (layers (rootedSequence s hs) k).row x = 1 := by
    have : lastVal (rowAt (expDg M (f + 1)) 0) = 1 := hy
    rw [hlv, hb] at this
    rw [show x = (iterSet (linearSetting s hs.1) k).n - 1 from by omega]
    exact this
  obtain ⟨r, p, hp⟩ := badAt_of_top_one (layers (rootedSequence s hs) k)
    (by have := value_gt_one_layer s hs hbad hxs k (by omega); rw [hb] at this; exact this) hone
  have hp' : BadAt (rootedSequence s hs) k r x p := hp
  have := badAt_unique hbad hp'
  omega

/-- **層 `k ≤ K` の JS の bad root は `y`。** -/
theorem expSeam_layer (s : List Nat) (hs : ZeroY.Legal s) {K d x y : Nat}
    (hbad : BadAt (rootedSequence s hs) K d x y) (hxs : s.length - 1 = x) (hK : K < sequenceBound s)
    (k : Nat) (hk : k ≤ K) (M : List Rowj) (m : Nat)
    (hM : MtRep (iterSet (linearSetting s hs.1) k) M) (hm : sequenceBound s ≤ m)
    (hn : 1 < (iterSet (linearSetting s hs.1) k).n) :
    expSeam M (m + 1) = y := by
  have hnn : (iterSet (linearSetting s hs.1) k).n = s.length := iterSet_n s hs.1 k
  have hbnd : (iterSet (linearSetting s hs.1) k).bnd = (linearSetting s hs.1).bnd :=
    iterSet_bnd _ k
  have hgt := value_gt_one_layer s hs hbad hxs k hk
  have hx : (iterSet (linearSetting s hs.1) k).n - 1 = x := by omega
  show (getBadRoot M (m + 1) (m + 1)).getD 0 = y
  rw [getBadRoot_eq m (m + 1) (iterSet (linearSetting s hs.1) k) M hM
      (by rw [hbnd]; exact hm) hn (by rw [hx]; exact hgt),
    hx, badRootOf_of_badAt s hs x hbad (m + 1) k (by omega) hk]
  rfl

/-- 層 `k ≤ K` では山の段は 2 つ以上ある。 -/
theorem two_rows_layer (s : List Nat) (hs : ZeroY.Legal s) {K d x y : Nat}
    (hbad : BadAt (rootedSequence s hs) K d x y) (hxs : s.length - 1 = x) (k : Nat)
    (hk : k ≤ K) (M : List Rowj)
    (hM : MtRep (iterSet (linearSetting s hs.1) k) M)
    (hn : 1 < (iterSet (linearSetting s hs.1) k).n) : 2 ≤ M.length := by
  have hnn : (iterSet (linearSetting s hs.1) k).n = s.length := iterSet_n s hs.1 k
  have hb : (iterSet (linearSetting s hs.1) k).tower.base
      = (layers (rootedSequence s hs) k).row := iterSet_base s hs k
  have hgt := value_gt_one_layer s hs hbad hxs k hk
  have hpar : (iterSet (linearSetting s hs.1) k).tower.base.forest.parent x ≠ none := by
    intro hc
    have h1 : (layers (rootedSequence s hs) k).row.forest.parent x = none := by
      rw [← hb]; exact hc
    have := (layers (rootedSequence s hs) k).rootsOne x h1
    rw [hb] at hgt
    omega
  have hh : 0 < height (iterSet (linearSetting s hs.1) k).tower.base x := by
    refine (parent_exists_iff_lt_height (iterSet (linearSetting s hs.1) k).tower.base
      ((iterSet (linearSetting s hs.1) k).tower.hpos x) 0).mp ?_
    cases hq : (iterSet (linearSetting s hs.1) k).tower.base.forest.parent x with
    | none => exact absurd hq hpar
    | some p => exact ⟨p, hq⟩
  have := hM.tall x (by omega)
  omega

/-- 層 `k ≤ K` では行 0 の最後のセルは親を持つ。 -/
theorem hhas_layer (s : List Nat) (hs : ZeroY.Legal s) {K d x y : Nat}
    (hbad : BadAt (rootedSequence s hs) K d x y) (hxs : s.length - 1 = x) (k : Nat)
    (hk : k ≤ K) (M : List Rowj)
    (hM : MtRep (iterSet (linearSetting s hs.1) k) M)
    (hn : 1 < (iterSet (linearSetting s hs.1) k).n) (hM0 : 0 < M.length) :
    (if hlt : (rowAt M 0).size - 1 < (rowAt M 0).size
      then (((rowAt M 0)[(rowAt M 0).size - 1]'hlt).par).isSome else false) = true := by
  have hnn : (iterSet (linearSetting s hs.1) k).n = s.length := iterSet_n s hs.1 k
  have hb : (iterSet (linearSetting s hs.1) k).tower.base
      = (layers (rootedSequence s hs) k).row := iterSet_base s hs k
  have hgt := value_gt_one_layer s hs hbad hxs k hk
  refine hhas_of_parent (iterSet (linearSetting s hs.1) k) M hM hn hM0 ?_
  intro hc
  have h1 : (layers (rootedSequence s hs) k).row.forest.parent x = none := by
    rw [← hb, show x = (iterSet (linearSetting s hs.1) k).n - 1 from by omega]
    exact hc
  have := (layers (rootedSequence s hs) k).rootsOne x h1
  rw [hb] at hgt
  omega

/-! ## **層の再帰** -/

/-- **層 `K − j` から下は、`K − j` 段目以上の畳み込みに一致する。** -/
theorem expandOut_layers (s : List Nat) (hs : ZeroY.Legal s) {K d x y : Nat}
    (hbad : BadAt (rootedSequence s hs) K d x y) (hK : K < sequenceBound s)
    (hxs : s.length - 1 = x) (hyx : y < x) (nrep m : Nat) (hm : sequenceBound s ≤ m)
    (hml : s.length ≤ m) :
    ∀ j, j ≤ K → ∀ (M : List Rowj) (efuel : Nat), j < efuel →
      MtRep (iterSet (linearSetting s hs.1) (K - j)) M →
      expandOut (expandJS nrep (m + 1) efuel M)
        = (List.range (x + (x - y) * nrep)).map
            (TowerReconstruction.assemble
              ((List.range' (K - j) (sequenceBound s - (K - j))).map
                (expandedMountain (rootedSequence s hs) hbad)) (fun _ => 1)) := by
  intro j
  induction j with
  | zero =>
      intro _ M efuel hef hM
      obtain ⟨e, rfl⟩ : ∃ e, efuel = e + 1 := ⟨efuel - 1, by omega⟩
      have hKK : K - 0 = K := by omega
      rw [hKK] at hM ⊢
      have hnn : (iterSet (linearSetting s hs.1) K).n = s.length := iterSet_n s hs.1 K
      have hn : 1 < (iterSet (linearSetting s hs.1) K).n := by omega
      have hb : (iterSet (linearSetting s hs.1) K).tower.base
          = (layers (rootedSequence s hs) K).row := iterSet_base s hs K
      obtain ⟨hh1, ht1⟩ := badAt_height_and_top hbad
      have hx : (iterSet (linearSetting s hs.1) K).n - 1 = x := by omega
      have hhgt : height (iterSet (linearSetting s hs.1) K).tower.base
          ((iterSet (linearSetting s hs.1) K).n - 1) = d + 1 := by rw [hb, hx]; exact hh1
      have hyama : expYama M (m + 1) := by
        show lastVal (rowAt (expDg M (m + 1)) 0) = 1
        rw [lastVal_expDg (iterSet (linearSetting s hs.1) K) M hM m hn, hb, hx]
        exact ht1
      have hpar : ((mountainOf' (iterSet (linearSetting s hs.1) K)).row
          (height (iterSet (linearSetting s hs.1) K).tower.base
            ((iterSet (linearSetting s hs.1) K).n - 1) - 1)).parent
          ((iterSet (linearSetting s hs.1) K).n - 1) = some y := by
        show (rows (iterSet (linearSetting s hs.1) K).tower.base _).forest.parent _ = some y
        rw [hb, hx, hh1, show d + 1 - 1 = d from by omega]
        exact hbad.1
      have hM2 := two_rows_layer s hs hbad hxs K (Nat.le_refl _) M hM hn
      refine expandOut_base_yama s hs hbad hK hxs hyx M m e nrep hM hM2 hyama
        (expSeam_layer s hs hbad hxs hK K (Nat.le_refl _) M m hM hm hn)
        (by omega) hpar (by omega) ?_
        (hhas_layer s hs hbad hxs K (Nat.le_refl _) M hM hn (by omega))
      have := rowAt_size_le (iterSet (linearSetting s hs.1) K) M hM
        (height (iterSet (linearSetting s hs.1) K).tower.base
          ((iterSet (linearSetting s hs.1) K).n - 1) - 1)
      omega
  | succ j ih =>
      intro hj M efuel hef hM
      obtain ⟨e, rfl⟩ : ∃ e, efuel = e + 1 := ⟨efuel - 1, by omega⟩
      have hk : K - (j + 1) < K := by omega
      have hnext : K - (j + 1) + 1 = K - j := by omega
      have hnn : (iterSet (linearSetting s hs.1) (K - (j + 1))).n = s.length :=
        iterSet_n s hs.1 (K - (j + 1))
      have hn : 1 < (iterSet (linearSetting s hs.1) (K - (j + 1))).n := by omega
      have hbnd : (iterSet (linearSetting s hs.1) (K - (j + 1))).bnd
          = (linearSetting s hs.1).bnd := iterSet_bnd _ _
      have hM2 := two_rows_layer s hs hbad hxs (K - (j + 1)) (by omega) M hM hn
      have hsm : expSeam M (m + 1) = y :=
        expSeam_layer s hs hbad hxs hK (K - (j + 1)) (by omega) M m hM hm hn
      have hseamP : (expP M (m + 1)).badRootSeam = y := hsm
      have hyk : ¬ expYama M (m + 1) :=
        not_expYama_layer s hs hbad hxs (K - (j + 1)) hk M m hM hn
      have hbh : (expP M (m + 1)).badRootHeight
          = height (iterSet (linearSetting s hs.1) (K - (j + 1))).tower.base y := by
        rw [expP_badRootHeight_lower (iterSet (linearSetting s hs.1) (K - (j + 1))) M hM
          (m + 1) hyk (by rw [hsm]; omega), hsm]
      have hcut : (expP M (m + 1)).cutHeight
          = height (iterSet (linearSetting s hs.1) (K - (j + 1))).tower.base x := by
        rw [expP_cutHeight_lower (iterSet (linearSetting s hs.1) (K - (j + 1))) M hM hn
          (m + 1) hyk, show x = (iterSet (linearSetting s hs.1) (K - (j + 1))).n - 1
            from by omega]
      have hfuel : (rowAt M (height (iterSet (linearSetting s hs.1) (K - (j + 1))).tower.base y)).size
          ≤ m + 1 := by
        have := rowAt_size_le (iterSet (linearSetting s hs.1) (K - (j + 1))) M hM
          (height (iterSet (linearSetting s hs.1) (K - (j + 1))).tower.base y)
        omega
      have hdg : MtRep (iterSet (linearSetting s hs.1) (K - j)) (expDg M (m + 1)) := by
        rw [← hnext]
        exact mtRep_extract (iterSet (linearSetting s hs.1) (K - (j + 1))) M hM m
          (by rw [hbnd]; exact hm)
      have hIH := ih (by omega) (expDg M (m + 1)) e (by omega) hdg
      rw [← hnext] at hIH
      exact expandOut_step_lower s hs hbad hK hxs hyx (K - (j + 1)) hk M (m + 1) e nrep
        hM hM2 hbh hseamP hcut hfuel hyk
        (hhas_layer s hs hbad hxs (K - (j + 1)) (by omega) M hM hn (by omega)) hIH

/-! ## **全体の一致** -/

/-- **bad root があるときの一致。** -/
theorem expand_eq_bad_root (s : List Nat) (hs : ZeroY.Legal s) (N m efuel : Nat)
    (hm : sequenceBound s ≤ m) (hml : s.length ≤ m) (hef : sequenceBound s ≤ efuel)
    {z : RootAddress} (hz : findBadRoot s hs (s.length - 1) = some z) :
    expandOut (expandJS N (m + 1) efuel (calcMountain s (m + 1))) = expandValues s hs N := by
  obtain ⟨hK, hbad⟩ := findBadRoot_sound s hs (s.length - 1) hz
  have hyx : z.column < s.length - 1 :=
    (rows (layers (rootedSequence s hs) z.layer).row z.row).forest.parent_left hbad.1
  have hM : MtRep (iterSet (linearSetting s hs.1) 0) (calcMountain s (m + 1)) :=
    mtRep_calcMountain s hs.1 m hm
  have hzz : z.layer - z.layer = 0 := by omega
  have h := expandOut_layers s hs hbad hK rfl hyx N m hm hml z.layer (Nat.le_refl _)
    (calcMountain s (m + 1)) efuel (by omega) (by rw [hzz]; exact hM)
  rw [hzz] at h
  rw [h, expandValues_of_badRoot s hs N hz]
  show _ = (List.range (s.length - 1 + N * (s.length - 1 - z.column))).map
    (TowerReconstruction.assemble
      ((List.range (sequenceBound s)).map (expandedMountain (rootedSequence s hs) hbad))
      (fun _ => 1))
  rw [show sequenceBound s - 0 = sequenceBound s from by omega, ← List.range_eq_range',
    Nat.mul_comm (s.length - 1 - z.column) N]

/-- **JS の `expand` と原文の `expandValues` は同じ関数である。** -/
theorem expand_eq (s : List Nat) (hs : ZeroY.Legal s) (N m efuel : Nat)
    (hm : sequenceBound s ≤ m) (hml : s.length ≤ m) (hef : sequenceBound s ≤ efuel)
    (hn : 0 < s.length) :
    expandOut (expandJS N (m + 1) efuel (calcMountain s (m + 1))) = expandValues s hs N := by
  have hb : 0 < sequenceBound s := by
    unfold sequenceBound
    omega
  obtain ⟨e, rfl⟩ : ∃ e, efuel = e + 1 := ⟨efuel - 1, by omega⟩
  cases hz : findBadRoot s hs (s.length - 1) with
  | none =>
      exact expand_eq_no_bad s hs m hm hn ((findBadRoot_none_iff s hs (s.length - 1)).mp hz)
        N (m + 1) e N
  | some z => exact expand_eq_bad_root s hs N m (e + 1) hm hml hef hz

end Yukito
