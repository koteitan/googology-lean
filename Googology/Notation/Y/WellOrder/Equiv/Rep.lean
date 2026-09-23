/-
From koteitan, 1y-expand-equiv, `Equiv/Rep.lean`
(https://github.com/koteitan/1y-expand-equiv, revision c9a5368a09ceb62ec671a6c3447a4719d035dfc0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.Y.WellOrder.`; the transcription `Equiv/Yukito.lean` is replaced by
`Googology.Notation.Y.Yukito` (opened below).
This file is part of googology-lean and is licensed under its MIT license.
-/
import Googology.Notation.Y.WellOrder.Equiv.Sparse
import Googology.Notation.Y.WellOrder.Equiv.RowSucc

open Googology.Notation.Y

/-!
# 疎配列が密表現を表していること

JS の行と Phyrion 版の行の対応を、次の 4 条件で書く。

```
mono   position は狭義単調増加
val    セルの値は密表現の値
live   セルの値は正
cover  生きている列はすべてセルとして現れる
```

これがあれば、疎配列を列番号で引いた値は密表現の値にそのまま一致する。列 `r` 未満については、JS 側は `position ≥ 0` なのでセルが無く 0、
密表現側も 0 である（`rows_value_zero_of_lt`）。

`assignParents` は `par` しか書き換えないので、この 4 条件を保つ。
-/

namespace Yukito

open OneY OneY.Numeric

/-! ## 表現述語 -/

/-- 配列の要素はリストの要素。 -/
theorem mem_of_getElem (row : Rowj) (i : Nat) (hi : i < row.size) :
    (row[i]'hi) ∈ row.toList := Array.getElem_mem_toList hi

/-- リストの要素は配列のどこかの要素。 -/
theorem getElem_of_mem (row : Rowj) {x : Cell} (h : x ∈ row.toList) :
    ∃ i, ∃ hi : i < row.size, (row[i]'hi) = x := by
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp h
  refine ⟨i, by rw [← Array.length_toList]; exact hi, ?_⟩
  rw [← he, Array.getElem_toList]

/-- 疎配列 `row` が、行のずれ `r`・列の上限 `n` のもとで密な値 `V` を表している。

上限が要るのは、`ofSequence` が列 `n` 以降を値 1 で埋めるからである。埋めた列は
値 1 なので親を持てず（親には真に小さい正の値が要る）、他の列の親にもならない。
行 1 以降では死んでいるので、上限が効くのは行 0 だけである。 -/
structure Rep (row : Rowj) (r n : Nat) (V : Nat → Nat) : Prop where
  pairwise : List.Pairwise (fun a b => a.pos < b.pos) row.toList
  val : ∀ x ∈ row.toList, x.val = V (x.pos + r)
  live : ∀ x ∈ row.toList, 0 < x.val
  bound : ∀ x ∈ row.toList, x.pos + r < n
  cover : ∀ c, r ≤ c → c < n → 0 < V c → ∃ x ∈ row.toList, x.pos + r = c

/-- 添字の形で読んだ単調性。 -/
theorem Rep.posMono {row : Rowj} {r n : Nat} {V : Nat → Nat} (h : Rep row r n V) :
    PosMono row := by
  intro i j hi hj hij
  have h2 := List.pairwise_iff_getElem.mp h.pairwise i j
    (by rw [Array.length_toList]; exact hi) (by rw [Array.length_toList]; exact hj) hij
  rwa [Array.getElem_toList, Array.getElem_toList] at h2

/-- 疎配列を列番号で引く。JS の `while (row[j].position < c - r) j++` と、
その後の「ちょうどか」の判定にあたる。 -/
def readVal (row : Rowj) (r c : Nat) : Nat :=
  let j := firstAtLeast row (c - r)
  if h : j < row.size then
    if (row[j]'h).pos + r = c then (row[j]'h).val else 0
  else 0

/-- 疎配列の添字を列番号に読み替える。 -/
def readIdx (row : Rowj) (r : Nat) : Option Nat → Option Nat
  | none => none
  | some j => if h : j < row.size then some ((row[j]'h).pos + r) else none

/-- 疎配列の親を列番号で引く。 -/
def readPar (row : Rowj) (r c : Nat) : Option Nat :=
  let j := firstAtLeast row (c - r)
  if h : j < row.size then
    if (row[j]'h).pos + r = c then readIdx row r ((row[j]'h).par) else none
  else none

/-! ## `assignParents` は表現を保つ

`par` しか書き換えないので、`pos` と `val` はそのままである。 -/

theorem assignParents_size (prev : Option Rowj) (row : Rowj) :
    (assignParents prev row).size = row.size := Array.size_mapIdx

theorem assignParents_pos (prev : Option Rowj) (row : Rowj) (i : Nat)
    (hi : i < (assignParents prev row).size) (hi' : i < row.size) :
    ((assignParents prev row)[i]'hi).pos = (row[i]'hi').pos := by
  simp only [assignParents, Array.getElem_mapIdx]
  split
  · rfl
  · cases prev <;> rfl

theorem assignParents_val (prev : Option Rowj) (row : Rowj) (i : Nat)
    (hi : i < (assignParents prev row).size) (hi' : i < row.size) :
    ((assignParents prev row)[i]'hi).val = (row[i]'hi').val := by
  simp only [assignParents, Array.getElem_mapIdx]
  split
  · rfl
  · cases prev <;> rfl

/-- 強制親のセルが無いこと。素の数から作った行は常にこれを満たす。 -/
def NoForced (row : Rowj) : Prop := ∀ x ∈ row.toList, x.forced = false

theorem noForced_row0 (s : List Nat) : NoForced (row0 s) := by
  intro x hx
  obtain ⟨i, hi, hix⟩ := getElem_of_mem _ hx
  rw [← hix]
  simp only [row0, Array.getElem_mapIdx]

theorem rep_assignParents (prev : Option Rowj) (row : Rowj) (r n : Nat) (V : Nat → Nat)
    (h : Rep row r n V) : Rep (assignParents prev row) r n V := by
  have hsize := assignParents_size prev row
  have key : ∀ x ∈ (assignParents prev row).toList,
      ∃ i, ∃ hi : i < row.size, (row[i]'hi).pos = x.pos ∧ (row[i]'hi).val = x.val := by
    intro x hx
    obtain ⟨i, hi, hix⟩ := getElem_of_mem _ hx
    exact ⟨i, by omega,
      by rw [← hix]; exact (assignParents_pos prev row i hi (by omega)).symm,
      by rw [← hix]; exact (assignParents_val prev row i hi (by omega)).symm⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    rw [Array.length_toList] at hi hj
    rw [Array.getElem_toList, Array.getElem_toList,
      assignParents_pos prev row i hi (by omega),
      assignParents_pos prev row j hj (by omega)]
    exact h.posMono i j (by omega) (by omega) hij
  · intro x hx
    obtain ⟨i, hi, hp, hv⟩ := key x hx
    rw [← hv, ← hp]
    exact h.val _ (mem_of_getElem row i hi)
  · intro x hx
    obtain ⟨i, hi, _, hv⟩ := key x hx
    rw [← hv]
    exact h.live _ (mem_of_getElem row i hi)
  · intro x hx
    obtain ⟨i, hi, hp, _⟩ := key x hx
    rw [← hp]
    exact h.bound _ (mem_of_getElem row i hi)
  · intro c hrc hcn hv
    obtain ⟨x, hx, hcx⟩ := h.cover c hrc hcn hv
    obtain ⟨i, hi, hix⟩ := getElem_of_mem row hx
    refine ⟨(assignParents prev row)[i]'(by omega), mem_of_getElem _ i (by omega), ?_⟩
    rw [assignParents_pos prev row i (by omega) hi, hix]
    exact hcx

/-! ## 行 0 -/

theorem row0_size (s : List Nat) : (row0 s).size = s.length := by
  simp only [row0, Array.size_mapIdx, List.size_toArray]

theorem row0_pos (s : List Nat) (i : Nat) (hi : i < (row0 s).size) :
    ((row0 s)[i]'hi).pos = i := by
  simp only [row0, Array.getElem_mapIdx]

/-- 入力列の中の列の値は列の要素そのもの。 -/
theorem ofSequence_value_lt (s : List Nat) (i : Nat) (h : i < s.length) :
    (ofSequence s).value i = s[i]'h := by
  show s[i]?.getD 1 = _
  rw [List.getElem?_eq_getElem h]
  rfl

theorem row0_val (s : List Nat) (i : Nat) (hi : i < (row0 s).size) :
    ((row0 s)[i]'hi).val = (ofSequence s).value i := by
  have h : i < s.length := by rw [← row0_size s]; exact hi
  rw [ofSequence_value_lt s i h]
  simp only [row0, Array.getElem_mapIdx, List.getElem_toArray]

theorem assignParents_none_par (row : Rowj) (i : Nat)
    (hi : i < (assignParents none row).size) (hi' : i < row.size)
    (hf : (row[i]'hi').forced = false) :
    ((assignParents none row)[i]'hi).par = searchBase row i ((row[i]'hi').pos) := by
  simp only [assignParents, Array.getElem_mapIdx, hf]
  rfl

/-- 行 0 は入力列そのものを表す。 -/
theorem rep_row0 (s : List Nat) (hs : ∀ x ∈ s, 0 < x) :
    Rep (row0 s) 0 s.length (ofSequence s).value := by
  have hsize := row0_size s
  have hget : ∀ i, ∀ hi : i < (row0 s).size,
      (row0 s)[i]'hi = { pos := i, val := s[i]'(by omega), par := none } := by
    intro i hi
    simp only [row0, Array.getElem_mapIdx, List.getElem_toArray]
  have hval : ∀ i, ∀ h : i < s.length, (ofSequence s).value i = s[i]'h := by
    intro i h
    show s[i]?.getD 1 = _
    rw [List.getElem?_eq_getElem h]
    rfl
  have key : ∀ x ∈ (row0 s).toList, ∃ i, ∃ hi : i < s.length,
      x = { pos := i, val := s[i]'hi, par := none } := by
    intro x hx
    obtain ⟨i, hi, hix⟩ := getElem_of_mem _ hx
    exact ⟨i, by omega, by rw [← hix, hget i hi]⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    rw [Array.length_toList] at hi hj
    rw [Array.getElem_toList, Array.getElem_toList, hget i hi, hget j hj]
    exact hij
  · intro x hx
    obtain ⟨i, hi, hix⟩ := key x hx
    subst hix
    show s[i]'hi = (ofSequence s).value (i + 0)
    rw [Nat.add_zero, hval i hi]
  · intro x hx
    obtain ⟨i, hi, hix⟩ := key x hx
    subst hix
    exact hs _ (List.getElem_mem _)
  · intro x hx
    obtain ⟨i, hi, hix⟩ := key x hx
    subst hix
    show i + 0 < s.length
    omega
  · intro c _ hcn _
    refine ⟨(row0 s)[c]'(by omega), mem_of_getElem _ c (by omega), ?_⟩
    rw [hget c (by omega)]
    show c + 0 = c
    omega

/-! ## 階差行

JS の `nextRow` は「親を持つセルだけを残し、`position` を 1 減らし、値を親との差に
する」。これが密表現の `Row.difference` にあたる。

`position` を 1 減らすところは自然数の切り捨て引き算なので、`position = 0` のセルが
残ると単調性が壊れる。壊れないのは、親を持つセルの `position` が 1 以上だからである
（親は左にあるので `position` が真に小さい列が存在する）。この事実には `par` が森に
対応していること（`ParRep`）が要る。 -/

/-- `nextRow` が 1 セルに対して行う操作。 -/
def stepCell (row : Rowj) (c : Cell) : Option Cell :=
  match c.par with
  | none => none
  | some p =>
    if hp : p < row.size then
      some { pos := c.pos - 1, val := c.val - (row[p]'hp).val, par := none }
    else none

theorem nextRow_toList_aux (row : Rowj) :
    ∀ (l : List Cell) (acc : Rowj),
      (l.foldl (fun acc c =>
        match c.par with
        | none => acc
        | some p => if hp : p < row.size then
            acc.push { pos := c.pos - 1, val := c.val - row[p].val, par := none }
          else acc) acc).toList = acc.toList ++ l.filterMap (stepCell row) := by
  intro l
  induction l with
  | nil => intro acc; simp
  | cons x t ih =>
      intro acc
      cases hp : x.par with
      | none => simp [stepCell, hp, ih]
      | some p => by_cases hlt : p < row.size <;> simp [stepCell, hp, hlt, ih]

theorem nextRow_toList (row : Rowj) :
    (nextRow row).toList = row.toList.filterMap (stepCell row) := by
  have h := nextRow_toList_aux row row.toList #[]
  rw [Array.foldl_toList] at h
  simp only [List.nil_append] at h
  exact h

theorem stepCell_some {row : Rowj} {x y : Cell} (h : stepCell row x = some y) :
    ∃ p, ∃ hp : p < row.size, x.par = some p ∧
      y = { pos := x.pos - 1, val := x.val - (row[p]'hp).val, par := none } := by
  unfold stepCell at h
  cases hp : x.par with
  | none => rw [hp] at h; dsimp only at h; cases h
  | some p =>
      rw [hp] at h
      dsimp only at h
      by_cases hlt : p < row.size
      · rw [dif_pos hlt] at h
        exact ⟨p, hlt, rfl, (Option.some.inj h).symm⟩
      · rw [dif_neg hlt] at h
        cases h

/-- `par` が森 `F` に対応している。添字ではなく列番号で読んだ形。 -/
def ParRep (row : Rowj) (r : Nat) (F : ParentForest) : Prop :=
  ∀ x ∈ row.toList,
    match x.par with
    | none => F.parent (x.pos + r) = none
    | some p => ∃ hp : p < row.size, F.parent (x.pos + r) = some ((row[p]'hp).pos + r)

/-- 残るセルの `position` は 1 以上。親は左にあるからである。 -/
theorem pos_pos_of_step {row : Rowj} {r : Nat} {F : ParentForest} (hpar : ParRep row r F)
    {x y : Cell} (hx : x ∈ row.toList) (h : stepCell row x = some y) : 0 < x.pos := by
  obtain ⟨p, hp, hxp, _⟩ := stepCell_some h
  have hP := hpar x hx
  rw [hxp] at hP
  obtain ⟨hp', hF⟩ := hP
  have hlt := F.parent_left hF
  omega

/-- 残るセル 1 つぶんの事実。 -/
theorem step_facts (row : Rowj) (r n : Nat) (a : Row)
    (hrep : Rep row r n a.value) (hpar : ParRep row r a.forest)
    {x y : Cell} (hx : x ∈ row.toList) (h : stepCell row x = some y) :
    y.pos + (r + 1) = x.pos + r ∧
      y.val = a.difference (y.pos + (r + 1)) ∧ 0 < y.val := by
  obtain ⟨p, hp, hxp, hy⟩ := stepCell_some h
  have hpos := pos_pos_of_step hpar hx h
  have hcol : y.pos + (r + 1) = x.pos + r := by
    subst hy
    show x.pos - 1 + (r + 1) = x.pos + r
    omega
  have hP := hpar x hx
  rw [hxp] at hP
  obtain ⟨hp', hF⟩ := hP
  have hxv := hrep.val x hx
  have hpv := hrep.val _ (mem_of_getElem row p hp')
  have hdiff : a.difference (x.pos + r) =
      a.value (x.pos + r) - a.value ((row[p]'hp').pos + r) := by
    simp only [Row.difference, hF]
  have hyv : y.val = x.val - (row[p]'hp').val := by rw [hy]
  refine ⟨hcol, ?_, ?_⟩
  · rw [hcol, hdiff, hyv, ← hxv, ← hpv]
  · rw [hyv]
    have hd : 0 < a.difference (x.pos + r) := (a.difference_pos_iff _).mpr ⟨_, hF⟩
    rw [hdiff] at hd
    omega

/-- **親の読み替えの正しさ。** `Rep` と `ParRep` があれば、疎配列の親を列番号で
引いた結果は密表現の親に一致する。 -/
theorem rep_read_par (row : Rowj) (r n : Nat) (a : Row) (h : Rep row r n a.value)
    (hpr : ParRep row r a.forest) (hzero : ∀ q, q < r → a.value q = 0)
    (c : Nat) (hcn : c < n) : readPar row r c = a.forest.parent c := by
  show (if hj : firstAtLeast row (c - r) < row.size then
          if (row[firstAtLeast row (c - r)]'hj).pos + r = c then
            readIdx row r ((row[firstAtLeast row (c - r)]'hj).par)
          else none
        else none) = a.forest.parent c
  rcases Nat.eq_zero_or_pos (a.value c) with hv | hv
  · have hnone : a.forest.parent c = none := by
      cases hq : a.forest.parent c with
      | none => rfl
      | some q => have := (a.parent_values hq).2; omega
    rw [hnone]
    split
    · rename_i hj
      split
      · rename_i he
        exfalso
        have h1 := h.val _ (mem_of_getElem row _ hj)
        have h2 := h.live _ (mem_of_getElem row _ hj)
        rw [he] at h1
        omega
      · rfl
    · rfl
  · have hrc : r ≤ c := by
      rcases Nat.lt_or_ge c r with hcr | hrc
      · rw [hzero c hcr] at hv; omega
      · exact hrc
    obtain ⟨x, hx, hcx⟩ := h.cover c hrc hcn hv
    obtain ⟨i, hi, hix⟩ := getElem_of_mem row hx
    have hci : (row[i]'hi).pos + r = c := by rw [hix]; exact hcx
    have hfa : firstAtLeast row (c - r) = i :=
      firstAtLeast_eq_of_mem row h.posMono (c - r) i hi (by omega)
    simp only [hfa, dif_pos hi, if_pos hci]
    have hP := hpr _ (mem_of_getElem row i hi)
    rw [hci] at hP
    cases hpp : (row[i]'hi).par with
    | none =>
        rw [hpp] at hP
        simp only [readIdx]
        exact hP.symm
    | some p =>
        rw [hpp] at hP
        obtain ⟨hp', hFc⟩ := hP
        simp only [readIdx, dif_pos hp']
        exact hFc.symm

theorem noForced_nextRow (row : Rowj) : NoForced (nextRow row) := by
  intro x hx
  rw [nextRow_toList] at hx
  obtain ⟨y, _, hy⟩ := List.mem_filterMap.mp hx
  obtain ⟨p, hp, _, hyx⟩ := stepCell_some hy
  rw [hyx]

/-- **階差行も表現になっている。** -/
theorem rep_nextRow (row : Rowj) (r n : Nat) (a : Row)
    (hrep : Rep row r n a.value) (hpar : ParRep row r a.forest) :
    Rep (nextRow row) (r + 1) n a.difference := by
  have hmem : ∀ y ∈ (nextRow row).toList, ∃ x ∈ row.toList, stepCell row x = some y := by
    intro y hy
    rw [nextRow_toList] at hy
    exact List.mem_filterMap.mp hy
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [nextRow_toList]
    apply List.pairwise_filterMap.mpr
    refine List.Pairwise.imp_of_mem ?_ hrep.pairwise
    intro u v hu hv huv y hy y' hy'
    obtain ⟨_, _, _, hyu⟩ := stepCell_some hy
    obtain ⟨_, _, _, hyv⟩ := stepCell_some hy'
    have h1 := pos_pos_of_step hpar hu hy
    subst hyu
    subst hyv
    show u.pos - 1 < v.pos - 1
    omega
  · intro y hy
    obtain ⟨x, hx, hs⟩ := hmem y hy
    exact (step_facts row r n a hrep hpar hx hs).2.1
  · intro y hy
    obtain ⟨x, hx, hs⟩ := hmem y hy
    exact (step_facts row r n a hrep hpar hx hs).2.2
  · intro y hy
    obtain ⟨x, hx, hs⟩ := hmem y hy
    have hc := (step_facts row r n a hrep hpar hx hs).1
    rw [hc]
    exact hrep.bound x hx
  · intro c hrc hcn hv
    obtain ⟨q, hq⟩ := (a.difference_pos_iff c).mp hv
    have hva : 0 < a.value c := by
      have := a.difference_le c
      omega
    obtain ⟨x, hx, hcx⟩ := hrep.cover c (by omega) hcn hva
    have hP := hpar x hx
    have hxp : ∃ p, x.par = some p := by
      cases hpx : x.par with
      | none =>
          exfalso
          rw [hpx] at hP
          rw [hcx, hq] at hP
          cases hP
      | some p => exact ⟨p, rfl⟩
    obtain ⟨p, hpx⟩ := hxp
    rw [hpx] at hP
    obtain ⟨hp', _⟩ := hP
    refine ⟨{ pos := x.pos - 1, val := x.val - (row[p]'hp').val, par := none }, ?_, ?_⟩
    · rw [nextRow_toList]
      refine List.mem_filterMap.mpr ⟨x, hx, ?_⟩
      simp only [stepCell, hpx]
      rw [dif_pos hp']
    · have hs : stepCell row x =
          some { pos := x.pos - 1, val := x.val - (row[p]'hp').val, par := none } := by
        simp only [stepCell, hpx]
        rw [dif_pos hp']
      have hf := (step_facts row r n a hrep hpar hx hs).1
      show x.pos - 1 + (r + 1) = c
      have hf' : x.pos - 1 + (r + 1) = x.pos + r := hf
      omega

end Yukito
