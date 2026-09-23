/-
From koteitan, 1y-expand-equiv, `Equiv/Fill.lean`
(https://github.com/koteitan/1y-expand-equiv, revision c9a5368a09ceb62ec671a6c3447a4719d035dfc0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.Y.WellOrder.`; the transcription `Equiv/Yukito.lean` is replaced by
`Googology.Notation.Y.Yukito` (opened below).
This file is part of googology-lean and is licensed under its MIT license.
-/
import Googology.Notation.Y.WellOrder.Equiv.Fuji

open Googology.Notation.Y

/-!
# 値の埋めの構造

`fillRow` は各セルについて 1 つずつ積む折り畳みである。積む値は「それまでに積んだ
配列」を見て決まるが、既に積んだ要素は変わらないので、最終形の前半部分と一致する。
本ファイルはその形を取り出す。
-/

namespace Yukito

/-! ## 1 つずつ積む折り畳み -/

/-- 直前までの結果を見ながら 1 つずつ積む折り畳み。 -/
def pushFold {α β : Type} (g : Array β → α → β) : Array β → List α → Array β
  | acc, [] => acc
  | acc, x :: t => pushFold g (acc.push (g acc x)) t

theorem pushFold_eq {α β : Type} (g : Array β → α → β) :
    ∀ (l : List α) (acc : Array β),
      pushFold g acc l = l.foldl (fun a x => a.push (g a x)) acc := by
  intro l
  induction l with
  | nil => intro acc; rfl
  | cons x t ih => intro acc; simp only [pushFold, List.foldl_cons, ih]

theorem pushFold_append {α β : Type} (g : Array β → α → β) :
    ∀ (l₁ l₂ : List α) (acc : Array β),
      pushFold g acc (l₁ ++ l₂) = pushFold g (pushFold g acc l₁) l₂ := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ acc; rfl
  | cons x t ih => intro l₂ acc; simp only [List.cons_append, pushFold, ih]

/-- 大きさは積んだ個数だけ増える。 -/
theorem pushFold_size {α β : Type} (g : Array β → α → β) :
    ∀ (l : List α) (acc : Array β), (pushFold g acc l).size = acc.size + l.length := by
  intro l
  induction l with
  | nil => intro acc; simp [pushFold]
  | cons x t ih =>
      intro acc
      simp only [pushFold, ih, Array.size_push, List.length_cons]
      omega

/-- 既に積んだ要素は後から変わらない。 -/
theorem pushFold_prefix {α β : Type} (g : Array β → α → β) :
    ∀ (l : List α) (acc : Array β) (j : Nat), j < acc.size →
      (pushFold g acc l)[j]? = acc[j]? := by
  intro l
  induction l with
  | nil => intro acc j _; rfl
  | cons x t ih =>
      intro acc j hj
      have hj' : j < (acc.push (g acc x)).size := by rw [Array.size_push]; omega
      rw [pushFold, ih (acc.push (g acc x)) j hj', Array.getElem?_push]
      rw [if_neg (by omega)]

/-- **積んだ `i` 番目は、`i` 個目までを積んだ時点の配列から決まる。** -/
theorem pushFold_get {α β : Type} (g : Array β → α → β) :
    ∀ (l : List α) (acc : Array β) (i : Nat),
      (pushFold g acc l)[acc.size + i]? = (l[i]?).map (g (pushFold g acc (l.take i))) := by
  intro l
  induction l with
  | nil =>
      intro acc i
      rw [pushFold, Array.getElem?_eq_none (by omega)]
      simp
  | cons x t ih =>
      intro acc i
      match i with
      | 0 =>
          have hlt : acc.size < (acc.push (g acc x)).size := by rw [Array.size_push]; omega
          rw [Nat.add_zero, pushFold, pushFold_prefix g t (acc.push (g acc x)) acc.size hlt,
            Array.getElem?_push, if_pos rfl]
          simp only [List.take_zero, pushFold, List.getElem?_cons_zero, Option.map_some]
      | j + 1 =>
          have hsz : (acc.push (g acc x)).size = acc.size + 1 := by rw [Array.size_push]
          have : acc.size + (j + 1) = (acc.push (g acc x)).size + j := by omega
          rw [pushFold, this, ih (acc.push (g acc x)) j]
          simp only [List.getElem?_cons_succ, List.take_succ_cons, pushFold]

theorem pushFold_get_nil {α β : Type} (g : Array β → α → β) (l : List α) (i : Nat) :
    (pushFold g #[] l)[i]? = (l[i]?).map (g (pushFold g #[] (l.take i))) := by
  have h := pushFold_get g l #[] i
  simpa using h

/-! ## `fillRow` -/

/-- `fillRow` が 1 セルについて積む値。 -/
def fillG (up : Rowj) (acc : Rowj) (c : Cell) : Cell :=
  if c.val ≠ 0 then c
  else { c with val := (match c.par with
                        | none => 0
                        | some p => valAtIdx acc p) + readValAt up (c.pos - 1) }

theorem fillRow_eq (row up : Rowj) : fillRow row up = pushFold (fillG up) #[] row.toList := by
  rw [pushFold_eq, Array.foldl_toList]
  rfl

/-- `fillG` の値の決まり方。 -/
theorem fillG_val (up acc : Rowj) (c : Cell) :
    (fillG up acc c).val
      = if c.val ≠ 0 then c.val
        else (match c.par with
              | none => 0
              | some p => valAtIdx acc p) + readValAt up (c.pos - 1) := by
  unfold fillG
  split
  · rfl
  · rfl

theorem fillRow_size (row up : Rowj) : (fillRow row up).size = row.size := by
  rw [fillRow_eq, pushFold_size]
  simp

theorem valAtIdx_eq (row : Rowj) (i : Nat) :
    valAtIdx row i = match row[i]? with | none => 0 | some c => c.val := by
  unfold valAtIdx
  split
  · next h => rw [Array.getElem?_eq_getElem h]
  · next h => rw [Array.getElem?_eq_none (Nat.le_of_not_lt h)]

/-- `fillRow` の `i` 番目のセルは、`i` 個目までを埋めた配列から決まる。 -/
theorem fillRow_get (row up : Rowj) (i : Nat) (hi : i < row.size) :
    (fillRow row up)[i]?
      = some (fillG up (pushFold (fillG up) #[] (row.toList.take i)) (row[i]'hi)) := by
  rw [fillRow_eq, pushFold_get_nil]
  have hlen : i < row.toList.length := by simpa using hi
  rw [List.getElem?_eq_getElem hlen]
  simp

/-- 参照する親が自分より前にあるとき、`fillRow` の値は最終形の中で閉じている。 -/
theorem fillRow_prefix_val (row up : Rowj) (i p : Nat) (hi : i ≤ row.size) (hp : p < i) :
    valAtIdx (pushFold (fillG up) #[] (row.toList.take i)) p = valAtIdx (fillRow row up) p := by
  have hsz : (pushFold (fillG up) #[] (row.toList.take i)).size = i := by
    rw [pushFold_size]
    simp only [Array.size_empty, List.length_take, Array.length_toList, Nat.zero_add]
    omega
  have key : pushFold (fillG up) #[] row.toList
      = pushFold (fillG up) (pushFold (fillG up) #[] (row.toList.take i)) (row.toList.drop i) := by
    rw [← pushFold_append, List.take_append_drop]
  rw [valAtIdx_eq, valAtIdx_eq, fillRow_eq, key,
    pushFold_prefix (fillG up) (row.toList.drop i)
      (pushFold (fillG up) #[] (row.toList.take i)) p (by omega)]

/-- **`fillRow` の値の決まり方。** 値が 0 でないセルはそのまま、0 のセルは
「同じ行の親の値 + 上の行の 1 つ左の列の値」になる。 -/
theorem fillRow_val (row up : Rowj)
    (hpar : ∀ (i : Nat) (h : i < row.size) (p : Nat), (row[i]'h).par = some p → p < i)
    (i : Nat) (hi : i < row.size) :
    valAtIdx (fillRow row up) i
      = if (row[i]'hi).val ≠ 0 then (row[i]'hi).val
        else (match (row[i]'hi).par with
              | none => 0
              | some p => valAtIdx (fillRow row up) p) + readValAt up ((row[i]'hi).pos - 1) := by
  rw [valAtIdx_eq, fillRow_get row up i hi]
  dsimp only
  rw [fillG_val]
  split
  · rfl
  · cases hcp : (row[i]'hi).par with
    | none => rfl
    | some p =>
        dsimp only
        rw [fillRow_prefix_val row up i p (Nat.le_of_lt hi) (hpar i hi p hcp)]

theorem fillRow_get? (row up : Rowj) (i : Nat) :
    (fillRow row up)[i]?
      = (row[i]?).map (fillG up (pushFold (fillG up) #[] (row.toList.take i))) := by
  rw [fillRow_eq, pushFold_get_nil]
  simp

theorem fillG_pos (up acc : Rowj) (c : Cell) : (fillG up acc c).pos = c.pos := by
  unfold fillG
  split
  · rfl
  · rfl

theorem fillRow_pos? (row up : Rowj) (i : Nat) :
    ((fillRow row up)[i]?).map (·.pos) = ((row[i]?)).map (·.pos) := by
  rw [fillRow_get?]
  cases h : row[i]? with
  | none => rfl
  | some c => simp [fillG_pos]

/-! ## 行の並び -/

theorem rowAt_cons_zero (x : Rowj) (L : List Rowj) : rowAt (x :: L) 0 = x := rfl

theorem rowAt_cons_succ (x : Rowj) (L : List Rowj) (k : Nat) :
    rowAt (x :: L) (k + 1) = rowAt L k := rfl

theorem headD_eq_rowAt (L : List Rowj) : L.headD #[] = rowAt L 0 := by
  cases L <;> rfl

/-! ## `fillValues` -/

theorem fillValues_cons (r a : Rowj) (t : List Rowj) :
    fillValues (r :: a :: t)
      = fillRow r (rowAt (fillValues (a :: t)) 0) :: fillValues (a :: t) := by
  rw [show fillValues (r :: a :: t)
        = fillRow r ((fillValues (a :: t)).headD #[]) :: fillValues (a :: t) from rfl,
    headD_eq_rowAt]

/-- 段の大きさは変わらない。 -/
theorem fillValues_size (Rs : List Rowj) (r : Nat) :
    (rowAt (fillValues Rs) r).size = (rowAt Rs r).size := by
  induction Rs generalizing r with
  | nil => rfl
  | cons x rest ih =>
      rcases rest with _ | ⟨a, t⟩
      · rfl
      · rw [fillValues_cons]
        cases r with
        | zero => rw [rowAt_cons_zero, rowAt_cons_zero, fillRow_size]
        | succ k => rw [rowAt_cons_succ, rowAt_cons_succ]; exact ih k

/-- `pos` は変わらない。 -/
theorem fillValues_pos? (Rs : List Rowj) (r i : Nat) :
    ((rowAt (fillValues Rs) r)[i]?).map (·.pos) = ((rowAt Rs r)[i]?).map (·.pos) := by
  induction Rs generalizing r with
  | nil => rfl
  | cons x rest ih =>
      rcases rest with _ | ⟨a, t⟩
      · rfl
      · rw [fillValues_cons]
        cases r with
        | zero => rw [rowAt_cons_zero, rowAt_cons_zero, fillRow_pos?]
        | succ k => rw [rowAt_cons_succ, rowAt_cons_succ]; exact ih k

/-- 最上段はそのまま。 -/
theorem fillValues_top (Rs : List Rowj) :
    rowAt (fillValues Rs) (Rs.length - 1) = rowAt Rs (Rs.length - 1) := by
  induction Rs with
  | nil => rfl
  | cons x rest ih =>
      rcases rest with _ | ⟨a, t⟩
      · rfl
      · have hlen : (x :: a :: t).length - 1 = ((a :: t).length - 1) + 1 := by
          simp only [List.length_cons]
          omega
        rw [hlen, fillValues_cons, rowAt_cons_succ, rowAt_cons_succ, ih]

/-- **`fillValues` の値の決まり方。** 最上段より下の段では、値 0 のセルは
「同じ段の親の値 + 1 つ上の段の 1 つ左の列の値」になる。 -/
theorem fillValues_val : ∀ (Rs : List Rowj),
    (∀ (r i : Nat) (h : i < (rowAt Rs r).size) (p : Nat),
      ((rowAt Rs r)[i]'h).par = some p → p < i) →
    ∀ (r : Nat), r + 1 < Rs.length → ∀ (i : Nat) (hi : i < (rowAt Rs r).size),
      valAtIdx (rowAt (fillValues Rs) r) i
        = if ((rowAt Rs r)[i]'hi).val ≠ 0 then ((rowAt Rs r)[i]'hi).val
          else (match ((rowAt Rs r)[i]'hi).par with
                | none => 0
                | some p => valAtIdx (rowAt (fillValues Rs) r) p)
               + readValAt (rowAt (fillValues Rs) (r + 1)) (((rowAt Rs r)[i]'hi).pos - 1) := by
  intro Rs
  induction Rs with
  | nil => intro _ r hr; exact absurd hr (by simp)
  | cons x rest ih =>
      rcases rest with _ | ⟨a, t⟩
      · intro _ r hr; exact absurd hr (by simp)
      · intro hpar r hr i hi
        cases r with
        | zero =>
            rw [fillValues_cons, rowAt_cons_zero, rowAt_cons_succ]
            exact fillRow_val x (rowAt (fillValues (a :: t)) 0)
              (fun i h p hp => hpar 0 i h p hp) i hi
        | succ k =>
            exact ih (fun r i h p hp => hpar (r + 1) i h p hp) k
              (by simp only [List.length_cons] at hr ⊢; omega) i hi

end Yukito
