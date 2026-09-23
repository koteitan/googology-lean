/-
From koteitan, 1y-expand-equiv, `Equiv/Search.lean`
(https://github.com/koteitan/1y-expand-equiv, revision c9a5368a09ceb62ec671a6c3447a4719d035dfc0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.Y.WellOrder.`; the transcription `Equiv/Yukito.lean` is replaced by
`Googology.Notation.Y.Yukito` (opened below).
This file is part of googology-lean and is licensed under its MIT license.
Port change: in `parRep_assignParents` one argument proof starts with `dsimp only`, which beta-reduces its goal.
-/
import Googology.Notation.Y.WellOrder.Equiv.Lookup
import Googology.Notation.Y.WellOrder.Equiv.Diagonal
import Googology.Notation.Y.WellOrder.Equiv.Mountain

open Googology.Notation.Y

/-!
# 親探索が `restrictedParent` に一致すること

JS の `searchUpper` は、1 つ下の行の親チェーンを辿り、各要素の列を今の行で引いて
値を比べ、最初に小さいものを親にする。Lean 側の `chainFind`（`Diagonal.lean`）は
同じ形をしており、`chainFind_eq_restrictedParent'` で `restrictedParent` に一致する。

食い違いうるのは 2 か所だけで、どちらも押さえてある。

```
firstAtLeast のずれ  鎖の要素が今の行で死んでいるときだけ起きる（= 鎖の根）
                     そこで指す列の値は c の値以上（root_step_le）
隙間 break           鎖の要素の右隣は生きているので鎖の上では発動しない
                     （chain_succ_live と not_breakHere）
```

したがって歩行は 1 歩ずつ重なる。根に降りたときは JS も Lean も親を返さない。
-/

namespace Yukito

open OneY OneY.Numeric

/-- 位置の大小から添字の大小が出る。 -/
theorem index_lt_of_pos_lt (row : Rowj) (h : PosMono row) (i j : Nat)
    (hi : i < row.size) (hj : j < row.size)
    (hlt : (row[i]'hi).pos < (row[j]'hj).pos) : i < j := by
  rcases Nat.lt_trichotomy i j with h1 | h1 | h1
  · exact h1
  · subst h1; omega
  · have := h j i hj hi h1; omega

/-- 鎖の線形性。`x` の親 `q` より右にある `c` の祖先は、`x` 以上である。 -/
theorem anc_ge_of_gt_parent {F : ParentForest} {c x q y : Nat}
    (hxc : ZeroY.Forest.Ancestor F.parent c x ∨ x = c)
    (hq : F.parent x = some q)
    (hy : ZeroY.Forest.Ancestor F.parent c y) (hqy : q < y) : x ≤ y := by
  rcases Nat.lt_or_ge y x with hlt | hge
  · exfalso
    have hyx : ZeroY.Forest.Ancestor F.parent x y := by
      rcases hxc with hxa | hxe
      · exact anc_of_common c y x hy hxa hlt
      · rw [hxe]; exact hy
    have := ancestor_le_of_parent hq (ParentForest.ancestor_of_zeroY hyx)
    omega
  · exact hge

/-- 探索が見る述語。「その列が生きていて、値が `c` の値より小さい」。 -/
def searchPred (U : Nat → Nat) (c : Nat) : Nat → Bool :=
  fun q => decide (0 < U q) && decide (U q < U c)

/-- **親探索は `chainFind` に 1 歩ずつ重なる。**

`x` は今いる鎖の位置、`p` はその `prev` での添字。`hacc` は「`x` 以上の生きた祖先は
すべて値が `c` の値以上」で、これまでの比較が失敗してきたことを表す。 -/
theorem searchUpper_eq (S : Setting) (k : Nat)
    (prev row : Rowj) (i c : Nat)
    (hprev : Rep prev k S.n (rows S.tower.base k).value)
    (hpar : ParRep prev k (rows S.tower.base k).forest)
    (hrow : Rep row (k + 1) S.n (rows S.tower.base (k + 1)).value)
    (hi : i < row.size) (hci : (row[i]'hi).pos + (k + 1) = c) :
    ∀ fuel x p, ∀ hp : p < prev.size, (prev[p]'hp).pos + k = x →
      (ZeroY.Forest.Ancestor (rows S.tower.base k).forest.parent c x ∨ x = c) →
      (∀ y, ZeroY.Forest.Ancestor (rows S.tower.base k).forest.parent c y → x ≤ y →
        0 < (rows S.tower.base (k + 1)).value y →
        (rows S.tower.base (k + 1)).value c ≤ (rows S.tower.base (k + 1)).value y) →
      p < fuel →
      readIdx row (k + 1) (searchUpper prev row i fuel (some p))
        = chainFind (rows S.tower.base k).forest
            (searchPred (rows S.tower.base (k + 1)).value c) fuel x := by
  intro fuel
  induction fuel with
  | zero => intro x p hp _ _ _ hf; omega
  | succ fuel ih =>
    intro x p hp hpx hxc hacc hf
    rw [searchUpper, dif_pos hp]
    have hP := hpar _ (mem_of_getElem prev p hp)
    cases hpp : (prev[p]'hp).par with
    | none =>
        rw [hpp] at hP
        rw [hpx] at hP
        simp only [readIdx]
        rw [chainFind, hP]
    | some p' =>
        rw [hpp] at hP
        obtain ⟨hp', hFx⟩ := hP
        rw [hpx] at hFx
        dsimp only
        rw [dif_pos hp']
        -- q は鎖の次の要素
        obtain ⟨q, hq⟩ : ∃ q, (prev[p']'hp').pos + k = q := ⟨_, rfl⟩
        rw [hq] at hFx
        -- q は行 k で生きているので k ≤ q
        have hqV : 0 < (rows S.tower.base k).value q :=
          ((rows S.tower.base k).parent_values hFx).1
        have hqk : k ≤ q := by
          rcases Nat.lt_or_ge q k with hlt | hge
          · rw [rows_value_zero_of_lt S.tower.base k q hlt] at hqV; omega
          · exact hge
        have htarget : (prev[p']'hp').pos - 1 = q - (k + 1) := by omega
        -- q は c の祖先
        have hqc : ZeroY.Forest.Ancestor (rows S.tower.base k).forest.parent c q := by
          rcases hxc with ha | he
          · exact Relation.TransGen.tail ha hFx
          · rw [← he]; exact Relation.TransGen.single hFx
        -- 添字は減る
        have hidx : p' < p :=
          index_lt_of_pos_lt prev hprev.posMono p' p hp' hp
            (by have := (rows S.tower.base k).forest.parent_left hFx; omega)
        rw [chainFind, hFx]
        dsimp only
        rcases Nat.eq_zero_or_pos ((rows S.tower.base (k + 1)).value q) with hdead | hlive
        · -- 鎖の根に降りた場合。どちらも親を返さない。
          have hnp : (rows S.tower.base k).forest.parent q = none := by
            rcases hqp : (rows S.tower.base k).forest.parent q with _ | t
            · rfl
            · exact absurd ((rows_parent_iff_next_live S.tower.base k q).mp ⟨t, hqp⟩)
                (by omega)
          have hpred : searchPred (rows S.tower.base (k + 1)).value c q = false := by
            simp only [searchPred, Bool.and_eq_false_iff, decide_eq_false_iff_not]
            exact Or.inl (by omega)
          have hfalse : ¬ (searchPred (rows S.tower.base (k + 1)).value c q = true) := by
            rw [hpred]
            exact fun hcon => Bool.noConfusion hcon
          rw [if_neg hfalse, chainFind_none_of_no_parent hnp fuel]
          -- JS 側
          have hsucc : 0 < (rows S.tower.base (k + 1)).value (q + 1) :=
            chain_succ_live S.tower k q x hFx
          have hsn : q + 1 < S.n := by
            rcases Nat.lt_or_ge (q + 1) S.n with h | h
            · exact h
            · rw [setting_value_zero_of_ge S (k + 1) (q + 1) (by omega) h] at hsucc; omega
          obtain ⟨j, hj, hcj, hfa⟩ := rep_lookup_dead row (k + 1) S.n
            (rows S.tower.base (k + 1)).value hrow q (by omega) hsn (by omega) hsucc
          rw [htarget, hfa]
          by_cases hb : breakHere row j = true
          · rw [if_pos hb]; rfl
          · rw [if_neg hb, dif_pos hj, dif_pos hi]
            have hreach : ∀ y,
                ZeroY.Forest.Ancestor (rows S.tower.base k).forest.parent c y →
                (∃ t, (rows S.tower.base k).forest.parent y = some t) →
                (rows S.tower.base (k + 1)).value c ≤
                  (rows S.tower.base (k + 1)).value y := by
              intro y hy hyt
              have hlive' := (rows_parent_iff_next_live S.tower.base k y).mp hyt
              refine hacc y hy (anc_ge_of_gt_parent hxc hFx hy ?_) hlive'
              rcases Nat.lt_or_ge q y with h | h
              · exact h
              · exfalso
                rcases Nat.eq_or_lt_of_le h with he | he
                · rw [he] at hlive'; omega
                · obtain ⟨t, ht⟩ := ancestor_parent_exists'
                    (ParentForest.ancestor_of_zeroY (anc_of_common c y q hy hqc he))
                  rw [hnp] at ht
                  cases ht
            have hle := (root_step_le S.tower k c q hqc hreach).2
            have hvj : (row[j]'hj).val = (rows S.tower.base (k + 1)).value (q + 1) := by
              rw [hrow.val _ (mem_of_getElem row j hj), hcj]
            have hvi : (row[i]'hi).val = (rows S.tower.base (k + 1)).value c := by
              rw [hrow.val _ (mem_of_getElem row i hi), hci]
            rw [if_neg (by omega)]
            cases fuel with
            | zero => omega
            | succ f =>
                rw [searchUpper, dif_pos hp']
                have hP' := hpar _ (mem_of_getElem prev p' hp')
                rw [hq] at hP'
                cases hpp' : (prev[p']'hp').par with
                | none => simp only [readIdx]
                | some t =>
                    exfalso
                    rw [hpp'] at hP'
                    obtain ⟨ht, hFq⟩ := hP'
                    rw [hnp] at hFq
                    cases hFq
        · -- 鎖の要素が生きている場合。ちょうど引けて隙間 break も出ない。
          have hqn : q < S.n := by
            rcases Nat.lt_or_ge q S.n with h | h
            · exact h
            · rw [setting_value_zero_of_ge S (k + 1) q (by omega) h] at hlive; omega
          have hqk1 : k + 1 ≤ q := by
            rcases Nat.lt_or_ge q (k + 1) with h | h
            · rw [rows_value_zero_of_lt S.tower.base (k + 1) q h] at hlive; omega
            · exact h
          obtain ⟨j, hj, hcj, hfa⟩ := rep_lookup row (k + 1) S.n
            (rows S.tower.base (k + 1)).value hrow q (by omega) hqn hlive
          have hsucc : 0 < (rows S.tower.base (k + 1)).value (q + 1) :=
            chain_succ_live S.tower k q x hFx
          have hsn : q + 1 < S.n := by
            rcases Nat.lt_or_ge (q + 1) S.n with h | h
            · exact h
            · rw [setting_value_zero_of_ge S (k + 1) (q + 1) (by omega) h] at hsucc; omega
          have hnb := not_breakHere row (k + 1) S.n
            (rows S.tower.base (k + 1)).value hrow q j hj hcj (by omega) hsn hsucc
          rw [htarget, hfa, if_neg (by rw [hnb]; simp), dif_pos hj, dif_pos hi]
          have hvj : (row[j]'hj).val = (rows S.tower.base (k + 1)).value q := by
            rw [hrow.val _ (mem_of_getElem row j hj), hcj]
          have hvi : (row[i]'hi).val = (rows S.tower.base (k + 1)).value c := by
            rw [hrow.val _ (mem_of_getElem row i hi), hci]
          have hpred : searchPred (rows S.tower.base (k + 1)).value c q
              = decide ((rows S.tower.base (k + 1)).value q <
                        (rows S.tower.base (k + 1)).value c) := by
            simp only [searchPred, decide_eq_true hlive, Bool.true_and]
          rw [hpred]
          by_cases hcmp : (rows S.tower.base (k + 1)).value q <
              (rows S.tower.base (k + 1)).value c
          · rw [if_pos (by omega), if_pos (decide_eq_true hcmp)]
            simp only [readIdx, dif_pos hj, hcj]
          · rw [if_neg (by omega), if_neg (by simp [hcmp])]
            refine ih q p' hp' hq (Or.inl hqc) ?_ (by omega)
            intro y hy hqy hly
            rcases Nat.eq_or_lt_of_le hqy with he | hgt
            · rw [← he]; omega
            · exact hacc y hy (anc_ge_of_gt_parent hxc hFx hy hgt) hly

/-! ## `assignParents` への接続 -/

/-- 探索が返す添字は配列の中にある。 -/
theorem searchUpper_lt (prev row : Rowj) (i : Nat) :
    ∀ fuel op j, searchUpper prev row i fuel op = some j → j < row.size := by
  intro fuel
  induction fuel with
  | zero => intro op j h; cases h
  | succ fuel ih =>
    intro op j h
    cases op with
    | none => cases h
    | some p =>
      rw [searchUpper] at h
      by_cases hp : p < prev.size
      · rw [dif_pos hp] at h
        cases hpp : (prev[p]'hp).par with
        | none => rw [hpp] at h; cases h
        | some p' =>
          rw [hpp] at h
          dsimp only at h
          by_cases hp' : p' < prev.size
          · rw [dif_pos hp'] at h
            by_cases hb : breakHere row (firstAtLeast row ((prev[p']'hp').pos - 1)) = true
            · rw [if_pos hb] at h; cases h
            · rw [if_neg hb] at h
              by_cases hj : firstAtLeast row ((prev[p']'hp').pos - 1) < row.size
              · rw [dif_pos hj] at h
                by_cases hi2 : i < row.size
                · rw [dif_pos hi2] at h
                  by_cases hv : (row[firstAtLeast row ((prev[p']'hp').pos - 1)]'hj).val
                      < (row[i]'hi2).val
                  · rw [if_pos hv] at h
                    injection h with he
                    subst he
                    exact hj
                  · rw [if_neg hv] at h
                    exact ih _ _ h
                · rw [dif_neg hi2] at h; cases h
              · rw [dif_neg hj] at h; cases h
          · rw [dif_neg hp'] at h; cases h
      · rw [dif_neg hp] at h; cases h

theorem assignParents_some_par (pv row : Rowj) (i : Nat)
    (hi : i < (assignParents (some pv) row).size) (hi' : i < row.size)
    (hf : (row[i]'hi').forced = false) :
    ((assignParents (some pv) row)[i]'hi).par =
      searchUpper pv row i (pv.size + 1)
        (some (firstAtLeast pv ((row[i]'hi').pos + 1))) := by
  simp only [assignParents, Array.getElem_mapIdx, hf]
  rfl

/-- 親を持つ列は入力列の中にある。 -/
theorem col_lt_of_parent (S : Setting) (k a b : Nat)
    (hab : (rows S.tower.base k).forest.parent a = some b) : a < S.n := by
  obtain ⟨hbv, hlt⟩ := (rows S.tower.base k).parent_values hab
  rcases Nat.lt_or_ge a S.n with h | h
  · exact h
  · exfalso
    cases k with
    | zero =>
        have he : (rows S.tower.base 0).value a = 1 := S.htail a h
        omega
    | succ k =>
        have he : (rows S.tower.base (k + 1)).value a = 0 :=
          setting_value_zero_of_ge S (k + 1) a (by omega) h
        omega

/-- 疎配列での添字は鎖に沿って真に減る。`chainFind` の燃料はこれで足りる。 -/
theorem idx_measure (S : Setting) (k : Nat) (prev : Rowj)
    (hprev : Rep prev k S.n (rows S.tower.base k).value) :
    ∀ a b, (rows S.tower.base k).forest.parent a = some b →
      firstAtLeast prev (b - k) < firstAtLeast prev (a - k) := by
  intro a b hab
  obtain ⟨hbv, hlt⟩ := (rows S.tower.base k).parent_values hab
  have hav : 0 < (rows S.tower.base k).value a := by omega
  have hba : b < a := (rows S.tower.base k).forest.parent_left hab
  have han : a < S.n := col_lt_of_parent S k a b hab
  have hbk : k ≤ b := by
    rcases Nat.lt_or_ge b k with h | h
    · rw [rows_value_zero_of_lt S.tower.base k b h] at hbv; omega
    · exact h
  obtain ⟨jb, hjb, hcb, hfb⟩ :=
    rep_lookup prev k S.n _ hprev b hbk (by omega) hbv
  obtain ⟨ja, hja, hca, hfa⟩ :=
    rep_lookup prev k S.n _ hprev a (by omega) han hav
  rw [hfb, hfa]
  exact index_lt_of_pos_lt prev hprev.posMono jb ja hjb hja (by omega)

/-- **`assignParents` が計算する親は `restrictedParent` に一致する。**
これで疎配列と密表現の橋渡しが 1 行ぶん閉じる。 -/
theorem parRep_assignParents (S : Setting) (k : Nat)
    (prev row : Rowj)
    (hprev : Rep prev k S.n (rows S.tower.base k).value)
    (hpar : ParRep prev k (rows S.tower.base k).forest)
    (hrow : Rep row (k + 1) S.n (rows S.tower.base (k + 1)).value)
    (hnf : NoForced row) :
    ParRep (assignParents (some prev) row) (k + 1)
      (rows S.tower.base (k + 1)).forest := by
  intro y hy
  obtain ⟨i, hi, hiy⟩ := getElem_of_mem _ hy
  have hsz : (assignParents (some prev) row).size = row.size :=
    assignParents_size (some prev) row
  have hi' : i < row.size := by omega
  have hpos : ((assignParents (some prev) row)[i]'hi).pos = (row[i]'hi').pos :=
    assignParents_pos (some prev) row i hi hi'
  -- 列 c
  have hcv : 0 < (rows S.tower.base (k + 1)).value ((row[i]'hi').pos + (k + 1)) := by
    have h1 := hrow.live _ (mem_of_getElem row i hi')
    have h2 := hrow.val _ (mem_of_getElem row i hi')
    omega
  have hcn : (row[i]'hi').pos + (k + 1) < S.n := hrow.bound _ (mem_of_getElem row i hi')
  have hck : k + 1 ≤ (row[i]'hi').pos + (k + 1) := by omega
  -- c は行 k でも生きている
  have hcv0 : 0 < (rows S.tower.base k).value ((row[i]'hi').pos + (k + 1)) := by
    have := rows_value_le S.tower.base k ((row[i]'hi').pos + (k + 1))
    omega
  obtain ⟨p0, hp0, hcp0, hfa0⟩ :=
    rep_lookup prev k S.n _ hprev ((row[i]'hi').pos + (k + 1)) (by omega) hcn hcv0
  -- 探索の出発点
  have hstart : (row[i]'hi').pos + 1 = ((row[i]'hi').pos + (k + 1)) - k := by omega
  -- 歩行の一致
  have hstep := searchUpper_eq S k prev row i ((row[i]'hi').pos + (k + 1))
    hprev hpar hrow hi' rfl (prev.size + 1) ((row[i]'hi').pos + (k + 1)) p0 hp0 hcp0
    (Or.inr rfl)
    (fun z hz hle _ => absurd (ZeroY.Forest.ancestor_lt
      (rows S.tower.base k).forest.parent_left hz) (by omega))
    (by omega)
  -- 燃料が足りている
  have hbig := chainFind_ge (F := (rows S.tower.base k).forest)
    (pred := searchPred (rows S.tower.base (k + 1)).value
      ((row[i]'hi').pos + (k + 1)))
    (fun z => firstAtLeast prev (z - k)) (idx_measure S k prev hprev)
    ((row[i]'hi').pos + (k + 1)) (prev.size + 1)
    (by dsimp only; rw [hfa0]; omega) ((row[i]'hi').pos + (k + 1))
  have hres : chainFind (rows S.tower.base k).forest
      (searchPred (rows S.tower.base (k + 1)).value ((row[i]'hi').pos + (k + 1)))
      (prev.size + 1) ((row[i]'hi').pos + (k + 1))
      = (rows S.tower.base (k + 1)).forest.parent ((row[i]'hi').pos + (k + 1)) := by
    rw [← hbig]
    exact chainFind_eq_restrictedParent' _ _ _ _ (by omega)
  -- 場合分け
  rw [← hiy, assignParents_some_par prev row i hi hi' (hnf _ (mem_of_getElem row i hi')),
    hstart, hfa0, hpos]
  cases hsu : searchUpper prev row i (prev.size + 1) (some p0) with
  | none =>
      rw [hsu] at hstep
      simp only [readIdx] at hstep
      exact (hstep.trans hres).symm
  | some j =>
      have hj : j < row.size := searchUpper_lt prev row i _ _ j hsu
      rw [hsu] at hstep
      simp only [readIdx, dif_pos hj] at hstep
      refine ⟨by omega, ?_⟩
      rw [assignParents_pos (some prev) row j (by omega) hj]
      exact (hstep.trans hres).symm

end Yukito
