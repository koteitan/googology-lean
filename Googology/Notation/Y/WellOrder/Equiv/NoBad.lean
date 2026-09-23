/-
From koteitan, 1y-expand-equiv, `Equiv/NoBad.lean`
(https://github.com/koteitan/1y-expand-equiv, revision c9a5368a09ceb62ec671a6c3447a4719d035dfc0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.Y.WellOrder.`; the transcription `Equiv/Yukito.lean` is replaced by
`Googology.Notation.Y.Yukito` (opened below).
This file is part of googology-lean and is licensed under its MIT license.
-/
import Googology.Notation.Y.WellOrder.Equiv.Fill
import Googology.Notation.Y.WellOrder.Equiv.BadRoot

open Googology.Notation.Y

/-!
# bad root が無いときの一致

Phyrion の `expandValues` は `findBadRoot s hs (s.length−1) = none` のとき
`s.take (s.length−1)` を返す。JS の `expand` は「行 0 の最後のセルが親を持たない」
とき最後のセルを削る。本ファイルはこの分岐で両者の出力が一致することを示す。
-/

namespace Yukito

open OneY OneY.Numeric OneY.RootGeometry

/-! ## 疎配列の位置が添字と一致すること

行 0 は列 `0 … n−1` を全部持つので、疎配列の添字がそのまま列番号になる。 -/

theorem posMono_add (row : Rowj) (hmono : PosMono row) :
    ∀ (d i j : Nat) (hi : i < row.size) (hj : j < row.size), j = i + d →
      (row[i]'hi).pos + d ≤ (row[j]'hj).pos := by
  intro d
  induction d with
  | zero =>
      intro i j hi hj he
      have he' : j = i := by omega
      subst he'
      omega
  | succ d ih =>
      intro i j hi hj he
      have hj' : i + d < row.size := by omega
      have h1 := ih i (i + d) hi hj' rfl
      have h2 := hmono (i + d) j hj' hj (by omega)
      omega

/-- **行 0 の疎配列は密である。** 位置は添字そのもの。 -/
theorem pos_eq_index (row : Rowj) (n : Nat) (V : Nat → Nat) (h : Rep row 0 n V)
    (hsize : row.size = n) (i : Nat) (hi : i < row.size) : (row[i]'hi).pos = i := by
  have hmono := h.posMono
  have hlast : row.size - 1 < row.size := by omega
  have hge := posMono_add row hmono i 0 i (by omega) hi (by omega)
  have hle := posMono_add row hmono (row.size - 1 - i) i (row.size - 1) hi hlast (by omega)
  have hb0 := h.bound _ (mem_of_getElem row 0 (by omega))
  have hb := h.bound _ (mem_of_getElem row (row.size - 1) hlast)
  omega

/-! ## 行 0 の親は添字そのもの -/

/-- **行 0 では、列で引いた親は疎配列の親そのもの。** -/
theorem readPar_row0 (S : Setting) (M : List Rowj) (hM : MtRep S M) (h0 : 0 < M.length)
    (c : Nat) (hc : c < (rowAt M 0).size) :
    readPar (rowAt M 0) 0 c = ((rowAt M 0)[c]'hc).par := by
  have hrep : Rep (rowAt M 0) 0 S.n (rows S.tower.base 0).value := rep_top S M hM 0 h0
  have hpos := pos_eq_index (rowAt M 0) S.n _ hrep hM.size0
  have hfa : firstAtLeast (rowAt M 0) (c - 0) = c :=
    firstAtLeast_eq_of_mem _ hrep.posMono (c - 0) c hc (hpos c hc)
  show (if h : firstAtLeast (rowAt M 0) (c - 0) < (rowAt M 0).size then
          if ((rowAt M 0)[firstAtLeast (rowAt M 0) (c - 0)]'h).pos + 0 = c then
            readIdx (rowAt M 0) 0 (((rowAt M 0)[firstAtLeast (rowAt M 0) (c - 0)]'h).par)
          else none
        else none) = _
  rw [hfa, dif_pos hc, if_pos (by simp [hpos c hc])]
  cases hq : ((rowAt M 0)[c]'hc).par with
  | none => rfl
  | some q =>
      obtain ⟨hqs, _⟩ := par_index_lt S M hM 0 h0 c q hc hq
      show (if h : q < (rowAt M 0).size then some (((rowAt M 0)[q]'h).pos + 0) else none)
        = some q
      rw [dif_pos hqs, hpos q hqs, Nat.add_zero]

/-! ## 値の埋めは値が入っている行を変えない -/

theorem fillG_id (up acc : Rowj) (c : Cell) (h : c.val ≠ 0) : fillG up acc c = c := by
  unfold fillG
  rw [if_pos h]

theorem fillRow_id (row up : Rowj) (h : ∀ x ∈ row.toList, x.val ≠ 0) :
    fillRow row up = row := by
  refine Array.ext (fillRow_size row up) ?_
  intro i hi hi'
  have hg := fillRow_get row up i hi'
  rw [Array.getElem?_eq_getElem hi] at hg
  rw [Option.some.inj hg, fillG_id _ _ _ (h _ (mem_of_getElem row i hi'))]

/-- 行 0 に値が入っていれば、値の埋めは行 0 を変えない。 -/
theorem fillValues_row0 (Rs : List Rowj) (h : ∀ x ∈ (rowAt Rs 0).toList, x.val ≠ 0) :
    rowAt (fillValues Rs) 0 = rowAt Rs 0 := by
  rcases Rs with _ | ⟨x, rest⟩
  · rfl
  · rcases rest with _ | ⟨a, t⟩
    · rfl
    · rw [fillValues_cons, rowAt_cons_zero]
      exact fillRow_id x _ h

/-! ## 末尾の空の段を落としても行 0 は変わらない -/

theorem dropEmptyTop_nil : dropEmptyTop ([] : List Rowj) = [] := by
  rw [dropEmptyTop]

theorem dropEmptyTop_row0 (n : Nat) : ∀ (L : List Rowj), L.length ≤ n →
    rowAt (dropEmptyTop L) 0 = rowAt L 0 := by
  induction n with
  | zero =>
      intro L hL
      rcases L with _ | ⟨a, t⟩
      · rw [dropEmptyTop_nil]
      · exact absurd hL (by simp)
  | succ n ih =>
      intro L hL
      rcases L with _ | ⟨a, t⟩
      · rw [dropEmptyTop_nil]
      · rw [dropEmptyTop]
        split
        · next hemp =>
            rcases Nat.eq_zero_or_pos t.length with h0 | h0
            · have ht : t = [] := by
                cases t with
                | nil => rfl
                | cons b u => simp at h0
              subst ht
              have hsz : a.size = 0 := hemp
              have ha : a = #[] :=
                Array.ext (by simp [hsz]) (fun i hi _ => absurd hi (by omega))
              simp only [List.length_nil, List.take_zero]
              rw [dropEmptyTop_nil, rowAt_cons_zero, ha]
              rw [rowAt_of_ge [] 0 (by simp)]
            · have hcons : (a :: t).take t.length = a :: t.take (t.length - 1) := by
                obtain ⟨m, hm⟩ : ∃ m, t.length = m + 1 := ⟨t.length - 1, by omega⟩
                rw [hm]
                simp only [List.take_succ_cons]
                congr 1
              have h1 : (t.take (t.length - 1)).length = min (t.length - 1) t.length :=
                List.length_take
              have h2 : min (t.length - 1) t.length ≤ t.length - 1 := Nat.min_le_left _ _
              have hlen : (a :: t.take (t.length - 1)).length ≤ n := by
                simp only [List.length_cons] at hL ⊢
                omega
              rw [hcons, ih (a :: t.take (t.length - 1)) hlen, rowAt_cons_zero,
                rowAt_cons_zero]
        · rfl

/-! ## 行 0 の値の列 -/

theorem row0Vals (s : List Nat) : (assignParents none (row0 s)).toList.map (·.val) = s := by
  refine List.ext_getElem ?_ ?_
  · simp only [List.length_map, Array.length_toList, assignParents_size, row0_size]
  · intro i h1 h2
    simp only [List.getElem_map, Array.getElem_toList]
    rw [assignParents_val none (row0 s) i (by simpa using h1) (by rw [row0_size]; omega),
      row0_val, ofSequence_value_lt s i h2]

/-! ## 分岐の一致 -/

/-- JS の分岐条件。行 0 の最後のセルが親を持つか。 -/
theorem expandJS_no_par (nrep mfuel efuel : Nat) (M : List Rowj)
    (h : ∀ hlt : (rowAt M 0).size - 1 < (rowAt M 0).size,
      (((rowAt M 0)[(rowAt M 0).size - 1]'hlt).par).isSome = false) :
    expandJS nrep mfuel (efuel + 1) M
      = fillValues (dropEmptyTop (M.set 0 (rowAt M 0).pop)) := by
  have hb : (if hlt : (rowAt M 0).size - 1 < (rowAt M 0).size
      then (((rowAt M 0)[(rowAt M 0).size - 1]'hlt).par).isSome else false) = false := by
    split
    · next hlt => exact h hlt
    · rfl
  simp only [expandJS, hb, Bool.not_false, if_true]

/-- 添字が等しければ同じセル。 -/
theorem getElem_congr_idx (row : Rowj) (i j : Nat) (hi : i < row.size) (hj : j < row.size)
    (h : i = j) : (row[i]'hi) = (row[j]'hj) := by
  subst h
  rfl

theorem rowAt_set_zero (L : List Rowj) (y : Rowj) (h : 0 < L.length) :
    rowAt (L.set 0 y) 0 = y := by
  have h' : 0 < (L.set 0 y).length := by rw [List.length_set]; exact h
  rw [rowAt_eq _ 0 h', List.getElem_set_self]

/-- **bad root が無いときの一致。** JS の `expand` と Phyrion の `expandValues` は
どちらも最後の列を削った列を返す。 -/
theorem expand_eq_no_bad (s : List Nat) (hs : ZeroY.Legal s) (mf : Nat)
    (hf : sequenceBound s ≤ mf) (hn : 0 < s.length)
    (hp : (ofSequence s).forest.parent (s.length - 1) = none)
    (nrep mfuel efuel N : Nat) :
    expandOut (expandJS nrep mfuel (efuel + 1) (calcMountain s (mf + 1)))
      = expandValues s hs N := by
  have hM : MtRep (linearSetting s hs.1) (calcMountain s (mf + 1)) :=
    mtRep_calcMountain s hs.1 mf hf
  have h0 : 0 < (calcMountain s (mf + 1)).length := calcMountainFrom_length_pos _ mf
  have hR : rowAt (calcMountain s (mf + 1)) 0 = assignParents none (row0 s) :=
    rowAt_calcMountain_zero s mf
  have hsize : (rowAt (calcMountain s (mf + 1)) 0).size = s.length :=
    size_rowAt_calcMountain_zero s mf
  have hlt' : s.length - 1 < (rowAt (calcMountain s (mf + 1)) 0).size := by omega
  -- JS の分岐条件
  have hparnone : ((rowAt (calcMountain s (mf + 1)) 0)[s.length - 1]'hlt').par = none := by
    rw [← readPar_row0 (linearSetting s hs.1) _ hM h0 (s.length - 1) hlt']
    exact (last_parent_none_iff s hs mf hf hn).mpr
      ((findBadRoot_none_iff s hs (s.length - 1)).mpr hp)
  rw [expandJS_no_par nrep mfuel efuel _ (fun hlt2 => by
    rw [getElem_congr_idx _ _ (s.length - 1) hlt2 hlt' (by omega), hparnone]
    rfl)]
  -- 行 0 は「最後のセルを削った行 0」
  have hset : rowAt ((calcMountain s (mf + 1)).set 0 (rowAt (calcMountain s (mf + 1)) 0).pop) 0
      = (rowAt (calcMountain s (mf + 1)) 0).pop := rowAt_set_zero _ _ h0
  have hdrop := dropEmptyTop_row0
    ((calcMountain s (mf + 1)).set 0 (rowAt (calcMountain s (mf + 1)) 0).pop).length
    ((calcMountain s (mf + 1)).set 0 (rowAt (calcMountain s (mf + 1)) 0).pop) (Nat.le_refl _)
  have hlive : ∀ x ∈ (rowAt (calcMountain s (mf + 1)) 0).pop.toList, x.val ≠ 0 := by
    intro x hx
    have hx' : x ∈ (rowAt (calcMountain s (mf + 1)) 0).toList := by
      rw [Array.toList_pop] at hx
      exact List.dropLast_subset _ hx
    have := (rep_top (linearSetting s hs.1) _ hM 0 h0).live x hx'
    omega
  show ((rowAt (fillValues (dropEmptyTop
    ((calcMountain s (mf + 1)).set 0 (rowAt (calcMountain s (mf + 1)) 0).pop))) 0).toList.map
      (·.val)) = _
  rw [fillValues_row0 _ (by rw [hdrop, hset]; exact hlive), hdrop, hset,
    expandValues_of_no_parent s hs N hp, hR, Array.toList_pop, List.map_dropLast, row0Vals,
    List.dropLast_eq_take]

end Yukito
