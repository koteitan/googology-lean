/-
From koteitan, 1y-expand-equiv, `Equiv/Lift.lean`
(https://github.com/koteitan/1y-expand-equiv, revision c9a5368a09ceb62ec671a6c3447a4719d035dfc0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.Y.WellOrder.`; the transcription `Equiv/Yukito.lean` is replaced by
`Googology.Notation.Y.Yukito` (opened below).
This file is part of googology-lean and is licensed under its MIT license.
-/
import Googology.Notation.Y.WellOrder.Equiv.Search
import Googology.Notation.Y.WellOrder.Equiv.Row0

open Googology.Notation.Y

/-!
# 山全体への持ち上げ

1 行ぶんの対応（`rep_row0` / `rep_assignParents` / `rep_nextRow` /
`parRep_assignParents`）を `calcMountain` の全行に回す。

行 0 だけは JS が `searchBase`（左へ走る）を使う。これは `Row0.lean` の `scanLeft`
そのもので、`restrictedParent_linear` により線形森の `restrictedParent` に一致する。
-/

namespace Yukito

open OneY OneY.Numeric

/-! ## 行 0 -/

/-- JS の左スキャン `searchBase` は `scanLeft` そのもの。位置が添字に一致し、
値が `U` を表している行ならどれでも成り立つ。 -/
theorem searchBase_eq_scanLeft' (row : Rowj) (U : Nat → Nat) (i : Nat)
    (hi : i < row.size)
    (hval : ∀ j, ∀ hj : j < row.size, (row[j]'hj).val = U j) :
    ∀ j, j ≤ i → searchBase row i j = scanLeft U (U i) j := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
      intro hji
      have hj : j < row.size := by omega
      rw [searchBase, dif_pos hj, dif_pos hi, scanLeft, hval j hj, hval i hi]
      by_cases hc : U j < U i
      · rw [if_pos hc, if_pos hc]
      · rw [if_neg hc, if_neg hc]
        exact ih (by omega)

/-- 行 0 についての形。 -/
theorem searchBase_eq_scanLeft (s : List Nat) (i : Nat) (hi : i < (row0 s).size) :
    ∀ j, j ≤ i → searchBase (row0 s) i j
      = scanLeft (ofSequence s).value ((ofSequence s).value i) j :=
  searchBase_eq_scanLeft' (row0 s) (ofSequence s).value i hi (fun j hj => row0_val s j hj)

/-- 行 0 の親も `restrictedParent` に一致する。 -/
theorem parRep_row0 (s : List Nat) (hs : ∀ x ∈ s, 0 < x) :
    ParRep (assignParents none (row0 s)) 0 (rows (ofSequence s) 0).forest := by
  intro y hy
  obtain ⟨i, hi, hiy⟩ := getElem_of_mem _ hy
  have hsz : (assignParents none (row0 s)).size = (row0 s).size :=
    assignParents_size none (row0 s)
  have hi' : i < (row0 s).size := by omega
  have hpos : ((assignParents none (row0 s))[i]'hi).pos = i := by
    rw [assignParents_pos none (row0 s) i hi hi', row0_pos s i hi']
  have hp : ((assignParents none (row0 s))[i]'hi).par
      = restrictedParent linearForest (ofSequence s).value i := by
    rw [assignParents_none_par (row0 s) i hi hi' (noForced_row0 s _ (mem_of_getElem _ i hi')),
      row0_pos s i hi',
      searchBase_eq_scanLeft s i hi' i (Nat.le_refl _),
      restrictedParent_linear (ofSequence s).value (ofSequence_positive s hs) i]
  rw [← hiy, hp, hpos]
  cases hrp : restrictedParent linearForest (ofSequence s).value i with
  | none =>
      show (rows (ofSequence s) 0).forest.parent (i + 0) = none
      rw [Nat.add_zero]
      exact hrp
  | some p =>
      have hpi : p < i := restrictedParent_left _ _ hrp
      refine ⟨by omega, ?_⟩
      show (rows (ofSequence s) 0).forest.parent (i + 0)
        = some (((assignParents none (row0 s))[p]'(by omega)).pos + 0)
      rw [Nat.add_zero, Nat.add_zero,
        assignParents_pos none (row0 s) p (by omega) (by omega),
        row0_pos s p (by omega)]
      exact hrp

/-! ## 全行 -/

/-- 反復部の全行が対応していること。 -/
theorem mountainGo_rep (S : Setting) :
    ∀ f cur k, Rep cur k S.n (rows S.tower.base k).value →
      ParRep cur k (rows S.tower.base k).forest →
      ∀ r, ∀ hr : r < (mountainGo cur f).length,
        Rep ((mountainGo cur f)[r]'hr) (k + r) S.n
            (rows S.tower.base (k + r)).value ∧
          ParRep ((mountainGo cur f)[r]'hr) (k + r)
            (rows S.tower.base (k + r)).forest := by
  intro f
  induction f with
  | zero =>
      intro cur k hrep hpar r hr
      simp only [mountainGo] at hr ⊢
      have hr0 : r = 0 := by simp at hr; omega
      subst hr0
      exact ⟨hrep, hpar⟩
  | succ f ih =>
      intro cur k hrep hpar r hr
      by_cases hall : cur.all (fun c => c.par.isNone) = true
      · simp only [mountainGo, if_pos hall] at hr ⊢
        have hr0 : r = 0 := by simp at hr; omega
        subst hr0
        exact ⟨hrep, hpar⟩
      · simp only [mountainGo, if_neg hall] at hr ⊢
        cases r with
        | zero => exact ⟨hrep, hpar⟩
        | succ r =>
            have hnr : Rep (nextRow cur) (k + 1) S.n
                (rows S.tower.base (k + 1)).value :=
              rep_nextRow cur k S.n (rows S.tower.base k) hrep hpar
            have hnrep : Rep (assignParents (some cur) (nextRow cur)) (k + 1) S.n
                (rows S.tower.base (k + 1)).value :=
              rep_assignParents (some cur) (nextRow cur) (k + 1) S.n _ hnr
            have hnpar := parRep_assignParents S k cur (nextRow cur) hrep hpar hnr
              (noForced_nextRow cur)
            have hr' : r < (mountainGo (assignParents (some cur) (nextRow cur)) f).length := by
              simp at hr; omega
            have h := ih (assignParents (some cur) (nextRow cur)) (k + 1) hnrep hnpar r hr'
            rw [show k + (r + 1) = (k + 1) + r from by omega]
            exact h

/-- 入力列から作る設定。 -/
def linearSetting (s : List Nat) (hs : ∀ x ∈ s, 0 < x) : Setting where
  tower := linearTower s hs
  n := s.length
  htail := fun c h => ofSequence_value_ge s c h
  bnd := sequenceBound s
  hbnd := sequence_value_le_bound s

/-- **山の全行が対応している。** -/
theorem calcMountain_rep (s : List Nat) (hs : ∀ x ∈ s, 0 < x) (fuel r : Nat)
    (hr : r < (calcMountain s (fuel + 1)).length) :
    Rep ((calcMountain s (fuel + 1))[r]'hr) r s.length (rows (ofSequence s) r).value ∧
      ParRep ((calcMountain s (fuel + 1))[r]'hr) r (rows (ofSequence s) r).forest := by
  have h := mountainGo_rep (linearSetting s hs) fuel (assignParents none (row0 s)) 0
    (rep_assignParents none (row0 s) 0 s.length _ (rep_row0 s hs))
    (parRep_row0 s hs) r hr
  rw [Nat.zero_add] at h
  exact h

/-- **一般の行から作る山も全行が対応している。** 抽出を繰り返すときはこれを使う。 -/
theorem calcMountainFrom_rep (S : Setting) (start : Rowj) (fuel r : Nat)
    (hrep : Rep (assignParents none start) 0 S.n S.tower.base.value)
    (hpar : ParRep (assignParents none start) 0 S.tower.base.forest)
    (hr : r < (calcMountainFrom start (fuel + 1)).length) :
    Rep ((calcMountainFrom start (fuel + 1))[r]'hr) r S.n (rows S.tower.base r).value ∧
      ParRep ((calcMountainFrom start (fuel + 1))[r]'hr) r
        (rows S.tower.base r).forest := by
  have h := mountainGo_rep S fuel (assignParents none start) 0 hrep hpar r hr
  rw [Nat.zero_add] at h
  exact h

/-- **山の親が一致する。** JS の行 `r` の列 `c` の親は、Phyrion 版の行 `r` の
森での親である。 -/
theorem calcMountain_parent (s : List Nat) (hs : ∀ x ∈ s, 0 < x) (fuel r c : Nat)
    (hr : r < (calcMountain s (fuel + 1)).length) (hc : c < s.length) :
    readPar ((calcMountain s (fuel + 1))[r]'hr) r c
      = (rows (ofSequence s) r).forest.parent c :=
  rep_read_par _ r s.length (rows (ofSequence s) r)
    (calcMountain_rep s hs fuel r hr).1 (calcMountain_rep s hs fuel r hr).2
    (fun q hq => rows_value_zero_of_lt (ofSequence s) r q hq) c hc

/-- 反復部の先頭はその行そのもの。 -/
theorem rowAt_mountainGo_zero (cur : Rowj) (f : Nat) : rowAt (mountainGo cur f) 0 = cur := by
  cases f with
  | zero => rfl
  | succ f =>
      simp only [mountainGo]
      split
      · rfl
      · rfl

theorem mountainGo_length_pos (cur : Rowj) (f : Nat) : 0 < (mountainGo cur f).length := by
  cases f with
  | zero => simp [mountainGo]
  | succ f =>
      simp only [mountainGo]
      split <;> simp

theorem calcMountainFrom_length_pos (base : Rowj) (fuel : Nat) :
    0 < (calcMountainFrom base (fuel + 1)).length :=
  mountainGo_length_pos _ fuel

/-- 山の行 0 は入力列から作った行。 -/
theorem rowAt_calcMountainFrom_zero (base : Rowj) (fuel : Nat) :
    rowAt (calcMountainFrom base (fuel + 1)) 0 = assignParents none base :=
  rowAt_mountainGo_zero _ fuel

theorem rowAt_calcMountain_zero (s : List Nat) (fuel : Nat) :
    rowAt (calcMountain s (fuel + 1)) 0 = assignParents none (row0 s) :=
  rowAt_mountainGo_zero _ fuel

/-- 山の行 0 の大きさは入力列の長さ。 -/
theorem size_rowAt_calcMountain_zero (s : List Nat) (fuel : Nat) :
    (rowAt (calcMountain s (fuel + 1)) 0).size = s.length := by
  rw [rowAt_calcMountain_zero, assignParents_size, row0_size]

/-! ## 段の数

`mountainGo` は「その行の全セルが親を持たない」ところで止まる。密表現では
「次の行が空」にあたるので、生きた列がある限り段は伸びる。 -/

/-- 生きた列がある限り、反復部は段を作る。 -/
theorem mountainGo_length (S : Setting) :
    ∀ f cur k, Rep cur k S.n (rows S.tower.base k).value →
      ParRep cur k (rows S.tower.base k).forest →
      ∀ r, r ≤ f → (∃ c, c < S.n ∧ 0 < (rows S.tower.base (k + r)).value c) →
        r < (mountainGo cur f).length := by
  intro f
  induction f with
  | zero =>
      intro cur k _ _ r hr _
      simp only [mountainGo, List.length_cons, List.length_nil]
      omega
  | succ f ih =>
      intro cur k hrep hpar r hr hex
      cases r with
      | zero =>
          simp only [mountainGo]
          split <;> simp
      | succ r =>
          obtain ⟨c, hcn, hcv⟩ := hex
          -- 列 `c` は行 `k+1` でも生きている
          have hlive1 : 0 < (rows S.tower.base (k + 1)).value c := by
            have := rows_value_antitone S.tower.base
              (show k + 1 ≤ k + (r + 1) by omega) c
            omega
          have hlive0 : 0 < (rows S.tower.base k).value c := by
            have := rows_value_le S.tower.base k c
            omega
          -- したがって `cur` のどれかのセルは親を持つ
          have hall : cur.all (fun x => x.par.isNone) = false := by
            obtain ⟨j, hj, hcj, _⟩ :=
              rep_lookup cur k S.n _ hrep c
                (by rcases Nat.lt_or_ge c k with hx | hx
                    · rw [rows_value_zero_of_lt S.tower.base k c hx] at hlive0; omega
                    · exact hx) hcn hlive0
            have hP := hpar _ (mem_of_getElem cur j hj)
            rw [hcj] at hP
            rw [Array.all_eq_false]
            refine ⟨j, hj, ?_⟩
            cases hpp : (cur[j]'hj).par with
            | none =>
                rw [hpp] at hP
                obtain ⟨t, ht⟩ :=
                  (rows_parent_iff_next_live S.tower.base k c).mpr hlive1
                rw [hP] at ht
                cases ht
            | some p => simp
          have hnall : ¬ (cur.all (fun x => x.par.isNone) = true) := by
            rw [hall]
            exact fun h => Bool.noConfusion h
          simp only [mountainGo, if_neg hnall, List.length_cons]
          have hnr : Rep (nextRow cur) (k + 1) S.n
              (rows S.tower.base (k + 1)).value :=
            rep_nextRow cur k S.n (rows S.tower.base k) hrep hpar
          have hnrep : Rep (assignParents (some cur) (nextRow cur)) (k + 1) S.n
              (rows S.tower.base (k + 1)).value :=
            rep_assignParents (some cur) (nextRow cur) (k + 1) S.n _ hnr
          have hnpar := parRep_assignParents S k cur (nextRow cur) hrep hpar hnr
            (noForced_nextRow cur)
          have := ih (assignParents (some cur) (nextRow cur)) (k + 1) hnrep hnpar r
            (by omega) ⟨c, hcn, by rw [show k + 1 + r = k + (r + 1) from by omega]; exact hcv⟩
          omega

/-- **山は十分な段を持つ。** 入力列の中の列については、その頂の段が山にある。 -/
theorem height_lt_length (s : List Nat) (hs : ∀ x ∈ s, 0 < x) (fuel : Nat)
    (hf : sequenceBound s ≤ fuel) (i : Nat) (hi : i < s.length) :
    height (ofSequence s) i < (calcMountain s (fuel + 1)).length := by
  have hb : height (ofSequence s) i < sequenceBound s := by
    have h1 := height_lt (ofSequence s) (ofSequence_positive s hs i)
    have h2 := sequence_value_le_bound s i
    omega
  have hlive : 0 < (rows (ofSequence s) (0 + height (ofSequence s) i)).value i := by
    rw [Nat.zero_add]
    exact height_live (ofSequence s) (ofSequence_positive s hs i)
  exact mountainGo_length (linearSetting s hs) fuel (assignParents none (row0 s)) 0
    (rep_assignParents none (row0 s) 0 s.length _ (rep_row0 s hs))
    (parRep_row0 s hs) (height (ofSequence s) i) (by omega) ⟨i, hi, hlive⟩

end Yukito
