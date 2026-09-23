/-
From koteitan, 1y-expand-equiv, `Equiv/BadRoot.lean`
(https://github.com/koteitan/1y-expand-equiv, revision c9a5368a09ceb62ec671a6c3447a4719d035dfc0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.Y.WellOrder.`; the transcription `Equiv/Yukito.lean` is replaced by
`Googology.Notation.Y.Yukito` (opened below).
This file is part of googology-lean and is licensed under its MIT license.
-/
import Googology.Notation.Y.WellOrder.Equiv.DiagBridge
import Googology.Notation.Y.WellOrder.OneY.Expansion
import Googology.Notation.Y.WellOrder.OneY.RootSearch

open Googology.Notation.Y

/-!
# bad root と `expand` の分岐

Phyrion の `expandValues` は最後の列の bad root で分岐する。

```
match findBadRoot s hs (s.length − 1) with
| none   => s.take (s.length − 1)
| some z => reconstructedValues … (x + N*(x − z.column))
```

JS の `expand` は「行 0 の最後のセルが親を持たない」で分岐し、持たなければ最後の列を
落とす。この 2 つの分岐条件が同じであることを示す。
-/

namespace Yukito

open OneY OneY.Numeric

/-- **`expand` の分岐条件が一致する。** JS の「行 0 の最後のセルに親が無い」と、
Phyrion の「`findBadRoot` が `none`」は同値である。 -/
theorem last_parent_none_iff (s : List Nat) (hs : ZeroY.Legal s) (fuel : Nat)
    (_hf : sequenceBound s ≤ fuel) (hn : 0 < s.length) :
    readPar (rowAt (calcMountain s (fuel + 1)) 0) 0 (s.length - 1) = none
      ↔ findBadRoot s hs (s.length - 1) = none := by
  have h0 : (0 : Nat) < (calcMountain s (fuel + 1)).length :=
    calcMountainFrom_length_pos _ fuel
  rw [findBadRoot_none_iff, rowAt_eq _ 0 h0,
    calcMountain_parent s hs.1 fuel 0 (s.length - 1) h0 (by omega)]
  exact Iff.rfl

/-! ## 行の最後のセル

`Rep` があれば、行の最後のセルはその行で最大の生きた列である。JS の `getBadRoot` は
これを使って「列 `n−1` を含む最上段」を探す。 -/

theorem lastCol_max (row : Rowj) (r : Nat) (hmono : PosMono row) (hne : 0 < row.size)
    (i : Nat) (hi : i < row.size) : (row[i]'hi).pos + r ≤ lastCol row r := by
  simp only [lastCol, dif_pos hne]
  rcases Nat.lt_or_ge i (row.size - 1) with hx | hx
  · have := hmono i (row.size - 1) hi (by omega) hx
    omega
  · have he : i = row.size - 1 := by omega
    subst he
    omega

theorem lastCol_live (row : Rowj) (r n : Nat) (V : Nat → Nat) (h : Rep row r n V)
    (hne : 0 < row.size) : 0 < V (lastCol row r) := by
  simp only [lastCol, dif_pos hne]
  have h1 := h.val _ (mem_of_getElem row _ (show row.size - 1 < row.size by omega))
  have h2 := h.live _ (mem_of_getElem row _ (show row.size - 1 < row.size by omega))
  omega

theorem lastCol_lt (row : Rowj) (r n : Nat) (V : Nat → Nat) (h : Rep row r n V)
    (hne : 0 < row.size) : lastCol row r < n := by
  simp only [lastCol, dif_pos hne]
  exact h.bound _ (mem_of_getElem row _ (show row.size - 1 < row.size by omega))

/-- **最後のセルが列 `n−1` であることと、その列がその行で生きていることは同値。** -/
theorem lastCol_eq_iff (S : Setting) (M : List Rowj) (hM : MtRep S M) (i : Nat)
    (hi : i < M.length) (hn : 1 < S.n) :
    lastCol (rowAt M i) i = S.n - 1 ↔ 0 < (rows S.tower.base i).value (S.n - 1) := by
  have hrep := rep_top S M hM i hi
  constructor
  · intro he
    have hne : 0 < (rowAt M i).size := by
      rcases Nat.eq_zero_or_pos (rowAt M i).size with hz | hz
      · exfalso
        simp only [lastCol, dif_neg (by omega : ¬ (0 < (rowAt M i).size))] at he
        omega
      · exact hz
    have := lastCol_live (rowAt M i) i S.n _ hrep hne
    rw [he] at this
    exact this
  · intro hlive
    have hik : i ≤ S.n - 1 := by
      rcases Nat.lt_or_ge (S.n - 1) i with hx | hx
      · rw [rows_value_zero_of_lt S.tower.base i (S.n - 1) hx] at hlive; omega
      · exact hx
    obtain ⟨x, hx, hcx⟩ := hrep.cover (S.n - 1) hik (by omega) hlive
    obtain ⟨j, hj, hjx⟩ := getElem_of_mem _ hx
    have hne : 0 < (rowAt M i).size := by omega
    have h1 : S.n - 1 ≤ lastCol (rowAt M i) i := by
      have := lastCol_max (rowAt M i) i hrep.posMono hne j hj
      rw [hjx] at this
      omega
    have h2 := lastCol_lt (rowAt M i) i S.n _ hrep hne
    omega

/-- **列 `n−1` を含む最上段。** `topRowOfLast` は `height (n−1)` を返す。 -/
theorem topRowOfLast_eq (S : Setting) (M : List Rowj) (hM : MtRep S M) (hn : 1 < S.n) :
    ∀ L, L ≤ M.length → height S.tower.base (S.n - 1) < L →
      topRowOfLast M S.n L = some (height S.tower.base (S.n - 1)) := by
  intro L
  induction L with
  | zero => intro _ h; omega
  | succ j ih =>
    intro hjM hij
    rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hij) with heq | hlt
    · rw [heq]
      have hj : j < M.length := by omega
      have hlive : 0 < (rows S.tower.base j).value (S.n - 1) :=
        (live_iff_le_height S.tower.base (S.tower.hpos (S.n - 1)) j).mpr (by omega)
      rw [topRowOfLast, if_pos ((lastCol_eq_iff S M hM j hj hn).mpr hlive)]
    · have hstep : topRowOfLast M S.n (j + 1) = topRowOfLast M S.n j := by
        rw [topRowOfLast]
        rcases Nat.lt_or_ge j M.length with hjlen | hjlen
        · have hdead : ¬ (0 < (rows S.tower.base j).value (S.n - 1)) := by
            intro hcon
            exact absurd ((live_iff_le_height S.tower.base
              (S.tower.hpos (S.n - 1)) j).mp hcon) (by omega)
          rw [if_neg (fun hcon =>
            hdead ((lastCol_eq_iff S M hM j hjlen hn).mp hcon))]
        · rw [rowAt_of_ge M j hjlen]
          rw [if_neg (by simp [lastCol]; omega)]
      rw [hstep]
      exact ih (by omega) hlt

/-! ## 見つけた段での取り出し -/

/-- 見つけた段の 1 つ下で、最後のセルの親を列番号で読むと、密表現の親になる。 -/
theorem badRoot_found (S : Setting) (M : List Rowj) (hM : MtRep S M) (hn : 1 < S.n)
    (hH : 0 < height S.tower.base (S.n - 1)) :
    (let prev := rowAt M (height S.tower.base (S.n - 1) - 1)
     if hp : 0 < prev.size then
       match (prev[prev.size - 1]'(by omega)).par with
       | none => none
       | some p => if hq : p < prev.size then some ((prev[p]'hq).pos
           + (height S.tower.base (S.n - 1) - 1)) else none
     else none)
      = (rows S.tower.base (height S.tower.base (S.n - 1) - 1)).forest.parent
          (S.n - 1) := by
  have hHl : height S.tower.base (S.n - 1) - 1 < M.length := by
    have := hM.tall (S.n - 1) (by omega)
    omega
  have hrep := rep_top S M hM _ hHl
  have hpar : ParRep (rowAt M (height S.tower.base (S.n - 1) - 1))
      (height S.tower.base (S.n - 1) - 1)
      (rows S.tower.base (height S.tower.base (S.n - 1) - 1)).forest := by
    rw [rowAt_eq M _ hHl]
    exact (hM.rowRep _ hHl).2
  have hlive : 0 < (rows S.tower.base
      (height S.tower.base (S.n - 1) - 1)).value (S.n - 1) :=
    (live_iff_le_height S.tower.base (S.tower.hpos (S.n - 1)) _).mpr (by omega)
  have hlast : lastCol (rowAt M (height S.tower.base (S.n - 1) - 1))
      (height S.tower.base (S.n - 1) - 1) = S.n - 1 :=
    (lastCol_eq_iff S M hM _ hHl hn).mpr hlive
  have hrc : height S.tower.base (S.n - 1) - 1 ≤ S.n - 1 := by
    rcases Nat.lt_or_ge (S.n - 1) (height S.tower.base (S.n - 1) - 1) with hx | hx
    · rw [rows_value_zero_of_lt S.tower.base _ (S.n - 1) hx] at hlive; omega
    · exact hx
  have hne : 0 < (rowAt M (height S.tower.base (S.n - 1) - 1)).size := by
    obtain ⟨x, hx, _⟩ := hrep.cover (S.n - 1) hrc (by omega) hlive
    obtain ⟨j, hj, _⟩ := getElem_of_mem _ hx
    omega
  simp only [dif_pos hne]
  have hcol : ((rowAt M (height S.tower.base (S.n - 1) - 1))[
      (rowAt M (height S.tower.base (S.n - 1) - 1)).size - 1]'(by omega)).pos
      + (height S.tower.base (S.n - 1) - 1) = S.n - 1 := by
    simpa only [lastCol, dif_pos hne] using hlast
  have hP := hpar _ (mem_of_getElem _ _ (show
    (rowAt M (height S.tower.base (S.n - 1) - 1)).size - 1
      < (rowAt M (height S.tower.base (S.n - 1) - 1)).size by omega))
  rw [hcol] at hP
  cases hpp : ((rowAt M (height S.tower.base (S.n - 1) - 1))[
      (rowAt M (height S.tower.base (S.n - 1) - 1)).size - 1]'(by omega)).par with
  | none =>
      rw [hpp] at hP
      exact hP.symm
  | some p =>
      rw [hpp] at hP
      obtain ⟨hq, hFc⟩ := hP
      dsimp only
      rw [dif_pos hq]
      exact hFc.symm

/-- 行 0 の最後のセルの値は、列 `n−1` の値。 -/
theorem lastVal_eq (S : Setting) (M : List Rowj) (hM : MtRep S M) (hn : 1 < S.n) :
    lastVal (rowAt M 0) = S.tower.base.value (S.n - 1) := by
  have h0 : (0 : Nat) < M.length := by
    have := hM.tall (S.n - 1) (by omega); omega
  have hrep := rep_top S M hM 0 h0
  have hlive : 0 < (rows S.tower.base 0).value (S.n - 1) := S.tower.hpos (S.n - 1)
  have hlast : lastCol (rowAt M 0) 0 = S.n - 1 :=
    (lastCol_eq_iff S M hM 0 h0 hn).mpr hlive
  have hne : 0 < (rowAt M 0).size := by
    obtain ⟨x, hx, _⟩ := hrep.cover (S.n - 1) (Nat.zero_le _) (by omega) hlive
    obtain ⟨j, hj, _⟩ := getElem_of_mem _ hx
    omega
  have hv := hrep.val _ (mem_of_getElem (rowAt M 0) _
    (show (rowAt M 0).size - 1 < (rowAt M 0).size by omega))
  simp only [lastVal, dif_pos hne]
  simp only [lastCol, dif_pos hne] at hlast
  rw [hv, hlast]
  rfl

/-! ## `getBadRoot` の密表現版 -/

/-- 密表現側の bad root 探索。抽出を繰り返し、頂の値が 1 になった層で
「頂の 1 つ下の段での親」を返す。 -/
def badRootOf (S : Setting) (c : Nat) : Nat → Option Nat
  | 0 => none
  | fuel + 1 =>
    if topValue S.tower.base c = 1 then
      (rows S.tower.base (height S.tower.base c - 1)).forest.parent c
    else badRootOf (extractSet S) c fuel

/-- **JS の `getBadRoot` は密表現側の探索に一致する。** -/
theorem getBadRoot_eq (m : Nat) :
    ∀ fuel (S : Setting) (M : List Rowj), MtRep S M → S.bnd ≤ m → 1 < S.n →
      1 < S.tower.base.value (S.n - 1) →
      getBadRoot M (m + 1) fuel = badRootOf S (S.n - 1) fuel := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ _; rfl
  | succ fuel ih =>
    intro S M hM hm hn hgt
    have hd := mtRep_extract S M hM m hm
    have hlv : lastVal (rowAt (calcMountainFrom (parseDiag (calcDiagonal M)) (m + 1)) 0)
        = topValue S.tower.base (S.n - 1) :=
      lastVal_eq (extractSet S) _ hd hn
    rw [getBadRoot, badRootOf, hlv]
    by_cases hc : topValue S.tower.base (S.n - 1) = 1
    · rw [if_pos hc, if_pos hc]
      -- 頂の段は 0 でない
      have hH : 0 < height S.tower.base (S.n - 1) := by
        rcases Nat.eq_zero_or_pos (height S.tower.base (S.n - 1)) with hz | hz
        · exfalso
          have : topValue S.tower.base (S.n - 1)
              = (rows S.tower.base 0).value (S.n - 1) := by
            show (rows S.tower.base (height S.tower.base (S.n - 1))).value (S.n - 1) = _
            rw [hz]
          rw [this] at hc
          show False
          have : (rows S.tower.base 0).value (S.n - 1) = S.tower.base.value (S.n - 1) := rfl
          omega
        · exact hz
      rw [hM.size0, topRowOfLast_eq S M hM hn M.length (Nat.le_refl _)
        (hM.tall (S.n - 1) (by omega))]
      exact badRoot_found S M hM hn hH
    · rw [if_neg hc, if_neg hc]
      refine ih (extractSet S) _ hd hm hn ?_
      have := topValue_pos S.tower.base (S.tower.hpos (S.n - 1))
      show 1 < topValue S.tower.base (S.n - 1)
      omega

/-! ## 密表現側の探索と `findBadRoot`

`badRootOf` の再帰は Phyrion の `layers`（抽出の繰り返し）にあたる。停止条件は
`badAt_height_and_top`（bad root の層では `topValue = 1`）と対応し、`badAt_unique`
（bad root は唯一）が「それより手前の層では止まらない」ことを与える。 -/

/-- 設定を `k` 回抽出したもの。 -/
def iterSet (S : Setting) : Nat → Setting
  | 0 => S
  | k + 1 => extractSet (iterSet S k)

theorem rawExtract_congr {b1 b2 : Row} (h : b1 = b2) (h1 : ∀ c, 0 < b1.value c)
    (h2 : ∀ c, 0 < b2.value c) : rawExtract b1 h1 = rawExtract b2 h2 := by
  subst h
  rfl

/-- `k` 回抽出した設定の底は、Phyrion の `layers` の `k` 段目である。 -/
theorem iterSet_base (s : List Nat) (hs : ZeroY.Legal s) (k : Nat) :
    (iterSet (linearSetting s hs.1) k).tower.base
      = (layers (rootedSequence s hs) k).row := by
  induction k with
  | zero => rfl
  | succ k ih =>
      show rawExtract (iterSet (linearSetting s hs.1) k).tower.base _
        = rawExtract (layers (rootedSequence s hs) k).row _
      exact rawExtract_congr ih _ _

/-- bad root の層まで降りると、`badRootOf` はその親を返す。 -/
theorem badRootOf_of_badAt (s : List Nat) (hs : ZeroY.Legal s) (c : Nat)
    {K r p : Nat} (h : BadAt (rootedSequence s hs) K r c p) :
    ∀ fuel k, K < k + fuel → k ≤ K →
      badRootOf (iterSet (linearSetting s hs.1) k) c fuel = some p := by
  intro fuel
  induction fuel with
  | zero => intro k h1 h2; omega
  | succ fuel ih =>
    intro k h1 h2
    rw [badRootOf]
    rcases Nat.eq_or_lt_of_le h2 with heq | hlt
    · -- ちょうど bad root の層
      subst heq
      obtain ⟨hh, ht⟩ := badAt_height_and_top h
      have hb : (iterSet (linearSetting s hs.1) k).tower.base
          = (layers (rootedSequence s hs) k).row := iterSet_base s hs k
      rw [hb, ht, if_pos rfl, hh]
      show (rows (layers (rootedSequence s hs) k).row (r + 1 - 1)).forest.parent c = some p
      rw [show r + 1 - 1 = r from by omega]
      exact h.1
    · -- まだ手前の層
      have hb : (iterSet (linearSetting s hs.1) k).tower.base
          = (layers (rootedSequence s hs) k).row := iterSet_base s hs k
      have hgt : 1 < (layers (rootedSequence s hs) k).row.value c := by
        have h1' := badAt_value_gt_one h
        have h2' := layers_value_antitone (rootedSequence s hs) h2 c
        omega
      have hne : topValue (layers (rootedSequence s hs) k).row c ≠ 1 := by
        intro hcon
        obtain ⟨r', p', hb'⟩ := badAt_of_top_one (layers (rootedSequence s hs) k) hgt hcon
        have hb'' : BadAt (rootedSequence s hs) k r' c p' := hb'
        obtain ⟨hkk, _, _⟩ := badAt_unique hb'' h
        omega
      rw [hb, if_neg hne]
      show badRootOf (iterSet (linearSetting s hs.1) (k + 1)) c fuel = some p
      exact ih (k + 1) (by omega) (by omega)

end Yukito
