/-
From koteitan, 1y-expand-equiv, `Equiv/DiagBridge.lean`
(https://github.com/koteitan/1y-expand-equiv, revision c9a5368a09ceb62ec671a6c3447a4719d035dfc0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.Y.WellOrder.`; the transcription `Equiv/Yukito.lean` is replaced by
`Googology.Notation.Y.Yukito` (opened below).
This file is part of googology-lean and is licensed under its MIT license.
-/
import Googology.Notation.Y.WellOrder.Equiv.Lift
import Googology.Notation.Y.WellOrder.Equiv.Extract
import Googology.Notation.Y.WellOrder.Equiv.TopFrame

open Googology.Notation.Y

/-!
# 抽出段の疎配列との橋渡し

`calcDiagonal` の書き起こし（`Yukito.lean`）が、密表現側の `rawExtract` に一致する
ことを示す。山の段で作った `Rep` / `ParRep` / `firstAtLeast` をそのまま使う。

まず頂の探索から。JS は段を上から下へ走らせて、列 `i` を含む最上段を探す。密表現側
でそれにあたるのが Phyrion の `height` である。
-/

namespace Yukito

open OneY OneY.Numeric

/-- 設定の底を抽出した行。 -/
def extractOf (S : Setting) : Row := rawExtract S.tower.base S.tower.hpos

/-- 設定の底から作る Phyrion 側の山。 -/
def mountainOf' (S : Setting) : RootGeometry.RowMountain :=
  mountain S.tower.base S.tower.hpos

/-- JS の山が設定に対応していること。 -/
structure MtRep (S : Setting) (M : List Rowj) : Prop where
  /-- 各行が `Rep` と `ParRep` を満たす。 -/
  rowRep : ∀ r, ∀ hr : r < M.length,
    Rep (M[r]'hr) r S.n (rows S.tower.base r).value ∧
      ParRep (M[r]'hr) r (rows S.tower.base r).forest
  /-- 行 0 の大きさは列の上限。 -/
  size0 : (rowAt M 0).size = S.n
  /-- 段が足りている。 -/
  tall : ∀ i, i < S.n → height S.tower.base i < M.length

/-- 列 `i` が行 `r` にあることと、`r ≤ height i` は同値。 -/
theorem col_live_iff (S : Setting) (i : Nat) (_hi : i < S.n)
    (r : Nat) : 0 < (rows S.tower.base r).value i ↔ r ≤ height S.tower.base i :=
  live_iff_le_height S.tower.base (S.tower.hpos i) r

/-- 範囲内なら `rowAt` はその行。 -/
theorem rowAt_eq (M : List Rowj) (j : Nat) (hj : j < M.length) : rowAt M j = M[j]'hj :=
  (List.getElem_eq_getD #[]).symm

/-- 範囲外なら `rowAt` は空行。 -/
theorem rowAt_of_ge (M : List Rowj) (j : Nat) (hj : M.length ≤ j) : rowAt M j = #[] := by
  simp [rowAt, List.getD, List.getElem?_eq_none hj]

/-- **頂の探索。** 段が足りていれば、`topAt` は `height i` の段とその添字を返す。 -/
theorem topAt_eq (S : Setting) (M : List Rowj)
    (hM : MtRep S M) (i : Nat) (hi : i < S.n) :
    ∀ L, L ≤ M.length → height S.tower.base i < L →
      ∃ k, ∃ hk : k < (rowAt M (height S.tower.base i)).size,
        ((rowAt M (height S.tower.base i))[k]'hk).pos + height S.tower.base i = i ∧
          topAt M i L = some (height S.tower.base i, k) := by
  intro L
  induction L with
  | zero => intro _ h; omega
  | succ j ih =>
    intro hjM hij
    rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hij) with heq | hlt
    · rw [heq]
      have hj : j < M.length := by omega
      have hrowj : rowAt M j = M[j]'hj := rowAt_eq M j hj
      obtain ⟨hrep, _⟩ := hM.rowRep j hj
      have hlive : 0 < (rows S.tower.base j).value i :=
        (col_live_iff S i hi j).mpr (by omega)
      have hji : j ≤ i := by
        rcases Nat.lt_or_ge i j with h | h
        · rw [rows_value_zero_of_lt S.tower.base j i h] at hlive; omega
        · exact h
      rw [hrowj]
      obtain ⟨k, hk, hck, hfa⟩ :=
        rep_lookup (M[j]'hj) j S.n _ hrep i hji hi hlive
      refine ⟨k, hk, hck, ?_⟩
      rw [topAt, hrowj]
      simp only [hfa, dif_pos hk, if_pos hck]
    · have hstep : topAt M i (j + 1) = topAt M i j := by
        rw [topAt]
        rcases Nat.lt_or_ge j M.length with hjlen | hjlen
        · have hrowj : rowAt M j = M[j]'hjlen := rowAt_eq M j hjlen
          obtain ⟨hrep, _⟩ := hM.rowRep j hjlen
          have hdead : (rows S.tower.base j).value i = 0 := by
            rcases Nat.eq_zero_or_pos ((rows S.tower.base j).value i) with h | h
            · exact h
            · exact absurd ((col_live_iff S i hi j).mp h) (by omega)
          rw [hrowj]
          split
          · rename_i hk
            have hne :
                ((M[j]'hjlen)[firstAtLeast (M[j]'hjlen) (i - j)]'hk).pos + j ≠ i := by
              intro he
              have h1 := hrep.val _ (mem_of_getElem _ _ hk)
              have h2 := hrep.live _ (mem_of_getElem _ _ hk)
              rw [he, hdead] at h1
              omega
            rw [if_neg hne]
          · rfl
        · rw [rowAt_of_ge M j hjlen]
          simp
      rw [hstep]
      exact ih (by omega) hlt

/-- 頂の段の `Rep`。 -/
theorem rep_top (S : Setting) (M : List Rowj) (hM : MtRep S M)
    (H : Nat) (hH : H < M.length) :
    Rep (rowAt M H) H S.n (rows S.tower.base H).value := by
  rw [rowAt_eq M H hH]
  exact (hM.rowRep H hH).1

/-! ## 脚 1 歩の対応

`Extract.lean` の `legStep` は密表現での脚 1 歩である。JS の `legStepJS` と
1 対 1 に対応する。状態の読み替えは「（段, 添字）→（段, 列）」である。 -/

/-- 疎配列の状態（段, 添字）を列座標に読み替える。 -/
def readState (M : List Rowj) (st : Nat × Nat) : Option (Nat × Nat) :=
  if hi : st.2 < (rowAt M st.1).size then
    some (st.1, ((rowAt M st.1)[st.2]'hi).pos + st.1)
  else none

/-- 状態の読み替えを `Option` へ持ち上げたもの。 -/
def readOpt (M : List Rowj) : Option (Nat × Nat) → Option (Nat × Nat)
  | none => none
  | some st => readState M st

/-- **脚 1 歩が一致する。** -/
theorem legStepJS_eq (S : Setting) (M : List Rowj)
    (hM : MtRep S M) (h idx : Nat) (hh : h < M.length)
    (hidx : idx < (rowAt M h).size) (hn : ((rowAt M h)[idx]'hidx).pos + h < S.n) :
    readOpt M (legStepJS M h idx)
      = legStep (mountainOf' S) h (((rowAt M h)[idx]'hidx).pos + h) := by
  have hrep := rep_top S M hM h hh
  have hpar : ParRep (rowAt M h) h (rows S.tower.base h).forest := by
    rw [rowAt_eq M h hh]; exact (hM.rowRep h hh).2
  have hP := hpar _ (mem_of_getElem _ idx hidx)
  cases h with
  | zero =>
    show (readOpt M (if hi : idx < (rowAt M 0).size then
            match ((rowAt M 0)[idx]'hi).par with
            | none => none
            | some p => some ((0 : Nat), p)
          else none)) = _
    rw [dif_pos hidx]
    cases hpp : ((rowAt M 0)[idx]'hidx).par with
    | none =>
        rw [hpp] at hP
        show (none : Option (Nat × Nat)) = _
        show _ = (match (rows S.tower.base 0).forest.parent
          (((rowAt M 0)[idx]'hidx).pos + 0) with
          | none => none
          | some q => if 0 ≤ (mountainOf' S).height q then some (0, q)
                      else some (0 - 1, q))
        rw [hP]
    | some p =>
        rw [hpp] at hP
        obtain ⟨hp, hFc⟩ := hP
        show (readOpt M (some ((0 : Nat), p))) = _
        show (readState M (0, p)) = _
        show (if hi : p < (rowAt M 0).size then
                some ((0 : Nat), ((rowAt M 0)[p]'hi).pos + 0) else none) = _
        rw [dif_pos hp]
        show _ = (match (rows S.tower.base 0).forest.parent
          (((rowAt M 0)[idx]'hidx).pos + 0) with
          | none => none
          | some q => if 0 ≤ (mountainOf' S).height q then some (0, q)
                      else some (0 - 1, q))
        rw [hFc]
        simp
  | succ h' =>
    have hh' : h' < M.length := by omega
    have hrep' := rep_top S M hM h' hh'
    have hpar' : ParRep (rowAt M h') h' (rows S.tower.base h').forest := by
      rw [rowAt_eq M h' hh']; exact (hM.rowRep h' hh').2
    have hlive : 0 < (rows S.tower.base (h' + 1)).value
        (((rowAt M (h' + 1))[idx]'hidx).pos + (h' + 1)) := by
      have h1 := hrep.val _ (mem_of_getElem _ idx hidx)
      have h2 := hrep.live _ (mem_of_getElem _ idx hidx)
      omega
    have hlive' : 0 < (rows S.tower.base h').value
        (((rowAt M (h' + 1))[idx]'hidx).pos + (h' + 1)) := by
      have := rows_value_le S.tower.base h'
        (((rowAt M (h' + 1))[idx]'hidx).pos + (h' + 1))
      omega
    obtain ⟨l0, hl0, hlk0, hcl0⟩ :=
      lookupPos_some (rowAt M h') h' S.n _ hrep'
        (((rowAt M (h' + 1))[idx]'hidx).pos + (h' + 1)) (by omega) hn hlive'
    have htarget : ((rowAt M (h' + 1))[idx]'hidx).pos + 1
        = (((rowAt M (h' + 1))[idx]'hidx).pos + (h' + 1)) - h' := by omega
    show (readOpt M (legStepJS M (h' + 1) idx)) = _
    rw [legStepJS]
    simp only [dif_pos hidx, htarget, hlk0]
    have hP' := hpar' _ (mem_of_getElem _ l0 hl0)
    rw [hcl0] at hP'
    show _ = (match (rows S.tower.base h').forest.parent
        (((rowAt M (h' + 1))[idx]'hidx).pos + (h' + 1)) with
      | none => none
      | some q => if h' + 1 ≤ (mountainOf' S).height q then some (h' + 1, q)
                  else some (h' + 1 - 1, q))
    rw [dif_pos hl0]
    cases hpp : ((rowAt M h')[l0]'hl0).par with
    | none =>
        rw [hpp] at hP'
        rw [hP']
        rfl
    | some l =>
        rw [hpp] at hP'
        obtain ⟨hl, hFc⟩ := hP'
        dsimp only
        rw [hFc, dif_pos hl]
        dsimp only
        have hqlt : ((rowAt M h')[l]'hl).pos + h'
            < ((rowAt M (h' + 1))[idx]'hidx).pos + (h' + 1) :=
          (rows S.tower.base h').forest.parent_left hFc
        have hqlive' : 0 < (rows S.tower.base h').value
            (((rowAt M h')[l]'hl).pos + h') := by
          have h1 := hrep'.val _ (mem_of_getElem _ l hl)
          have h2 := hrep'.live _ (mem_of_getElem _ l hl)
          omega
        have hqn : ((rowAt M h')[l]'hl).pos + h' < S.n := by omega
        by_cases hz : ((rowAt M h')[l]'hl).pos = 0
        · rw [if_pos hz]
          have hhq : height S.tower.base (((rowAt M h')[l]'hl).pos + h') ≤ h' := by
            have := height_le_self' S.tower.base S.tower.hpos (((rowAt M h')[l]'hl).pos + h')
            omega
          rw [if_neg (show ¬ (h' + 1 ≤ (mountainOf' S).height
            (((rowAt M h')[l]'hl).pos + h')) by
              show ¬ (h' + 1 ≤ height S.tower.base _); omega)]
          show readState M (h', l) = _
          simp only [readState, dif_pos hl, Nat.add_sub_cancel]
        · rw [if_neg hz]
          have hteq : ((rowAt M h')[l]'hl).pos - 1
              = (((rowAt M h')[l]'hl).pos + h') - (h' + 1) := by omega
          rw [hteq]
          by_cases hql : 0 < (rows S.tower.base (h' + 1)).value
              (((rowAt M h')[l]'hl).pos + h')
          · obtain ⟨m, hm, hlkm, hcm⟩ :=
              lookupPos_some (rowAt M (h' + 1)) (h' + 1) S.n _ hrep
                (((rowAt M h')[l]'hl).pos + h') (by omega) hqn hql
            rw [hlkm]
            rw [if_pos (show h' + 1 ≤ (mountainOf' S).height
              (((rowAt M h')[l]'hl).pos + h') from
                (live_iff_le_height S.tower.base
                  (S.tower.hpos _) (h' + 1)).mp hql)]
            show readState M (h' + 1, m) = _
            simp only [readState, dif_pos hm, hcm]
          · rw [lookupPos_none (rowAt M (h' + 1)) (h' + 1) S.n _ hrep
              (((rowAt M h')[l]'hl).pos + h') (by omega) (by omega)]
            rw [if_neg (show ¬ (h' + 1 ≤ (mountainOf' S).height
              (((rowAt M h')[l]'hl).pos + h')) from fun hcon =>
                hql ((live_iff_le_height S.tower.base
                  (S.tower.hpos _) (h' + 1)).mpr hcon))]
            show readState M (h', l) = _
            simp only [readState, dif_pos hl, Nat.add_sub_cancel]

/-! ## 脚歩行の対応 -/

/-- **脚歩行が一致する。** 1 歩の対応を歩行全体に回したもの。 -/
theorem legWalkJS_eq (S : Setting) (M : List Rowj)
    (hM : MtRep S M) :
    ∀ fuel h idx, ∀ _hh : h < M.length, ∀ hidx : idx < (rowAt M h).size,
      ((rowAt M h)[idx]'hidx).pos + h < S.n →
      legWalkJS M fuel h idx
        = jsWalk (mountainOf' S) fuel h (((rowAt M h)[idx]'hidx).pos + h) := by
  intro fuel
  induction fuel with
  | zero => intro h idx _ _ _; rfl
  | succ fuel ih =>
    intro h idx hh hidx hn
    have hstep := legStepJS_eq S M hM h idx hh hidx hn
    rw [legWalkJS, jsWalk]
    cases hst : legStepJS M h idx with
    | none =>
        rw [hst, readOpt] at hstep
        rw [← hstep]
    | some st =>
        obtain ⟨h', idx'⟩ := st
        rw [hst, readOpt] at hstep
        dsimp only
        by_cases hi : idx' < (rowAt M h').size
        · rw [readState] at hstep
          dsimp only at hstep
          rw [dif_pos hi] at hstep
          have hh'h : h' ≤ h := legStep_row_le _ hstep.symm
          have hh' : h' < M.length := by omega
          have hlt := legStep_col_lt _ hstep.symm
          have hpar' : ParRep (rowAt M h') h' (rows S.tower.base h').forest := by
            rw [rowAt_eq M h' hh']; exact (hM.rowRep h' hh').2
          have hP := hpar' _ (mem_of_getElem _ idx' hi)
          rw [← hstep]
          dsimp only
          rw [dif_pos hi]
          cases hpp : ((rowAt M h')[idx']'hi).par with
          | none =>
              rw [hpp] at hP
              have hPn : ((mountainOf' S).row h').parent
                  (((rowAt M h')[idx']'hi).pos + h') = none := hP
              rw [if_pos hPn]
          | some p =>
              rw [hpp] at hP
              obtain ⟨hp, hFc⟩ := hP
              rw [if_neg (show ¬ (((mountainOf' S).row h').parent
                  (((rowAt M h')[idx']'hi).pos + h') = none) from by
                    show ¬ ((rows S.tower.base h').forest.parent
                      (((rowAt M h')[idx']'hi).pos + h') = none)
                    rw [hFc]
                    intro hcon
                    cases hcon)]
              exact ih h' idx' hh' hi (by omega)
        · rw [readState, dif_neg hi] at hstep
          rw [← hstep]
          dsimp only
          rw [dif_neg hi]

/-- **対角の 1 要素が一致する。** JS が積む値は `topValue`、歩行の結果は
Phyrion の `Pseudo.parent` である。 -/
theorem diagEntry_eq (S : Setting) (M : List Rowj)
    (hM : MtRep S M) (i : Nat) (hi : i < S.n)
    (hlen : height S.tower.base i < M.length) :
    diagEntry M i
      = some (topValue S.tower.base i, Pseudo.parent (mountainOf' S) i) := by
  obtain ⟨k, hk, hck, htop⟩ := topAt_eq S M hM i hi M.length (Nat.le_refl _) hlen
  have hrep := rep_top S M hM (height S.tower.base i) hlen
  have hval : ((rowAt M (height S.tower.base i))[k]'hk).val
      = topValue S.tower.base i := by
    have h := hrep.val _ (mem_of_getElem _ k hk)
    rw [hck] at h
    exact h
  have hwalk : legWalkJS M (i + 1) (height S.tower.base i) k
      = jsWalk (mountainOf' S) (i + 1) (height S.tower.base i) i := by
    have h := legWalkJS_eq S M hM (i + 1) (height S.tower.base i) k hlen hk
      (by rw [hck]; exact hi)
    rw [hck] at h
    exact h
  have hps : jsWalk (mountainOf' S) (i + 1) (height S.tower.base i) i
      = Pseudo.parent (mountainOf' S) i :=
    jsWalk_eq_pseudo (mountainOf' S) i (i + 1) (by omega)
  rw [diagEntry, htop]
  simp only [dif_pos hk, hval, hwalk, hps]

/-! ## 対角のリスト -/

theorem filterMap_range_eq_map {α : Type} (n : Nat) (f : Nat → Option α) (g : Nat → α)
    (h : ∀ i, i < n → f i = some (g i)) :
    (List.range n).filterMap f = (List.range n).map g := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.range_succ, List.filterMap_append, List.map_append,
        ih (fun i hi => h i (by omega))]
      simp [h n (by omega)]

/-- **対角のリストが一致する。** JS の `diagonal` と `diagonalTree` は、
Phyrion の `topValue` と `Pseudo.parent` の並びである。 -/
theorem diagList_eq (S : Setting) (M : List Rowj) (hM : MtRep S M) :
    diagList M
      = (List.range S.n).map
          (fun i => (topValue S.tower.base i, Pseudo.parent (mountainOf' S) i)) := by
  rw [diagList, hM.size0]
  exact filterMap_range_eq_map _ _ _ (fun i hi =>
    diagEntry_eq S M hM i hi (hM.tall i hi))

/-! ## 2 つの探索

`treeScan` は `diagonalTree`（擬親森）を辿る探索で、`Diagonal.lean` の `chainFind`
と同じ形をしている。`pwScan` は線形森を辿る探索で、`Row0.lean` の `scanLeft` と
同じ形である。 -/

theorem getD_map_range {α : Type} (n i : Nat) (g : Nat → α) (dflt : α) (hi : i < n) :
    ((List.range n).map g).getD i dflt = g i := by
  simp only [List.getD, List.getElem?_map, List.getElem?_range hi, Option.map_some,
    Option.getD_some]

theorem getD_map_range_ge {α : Type} (n i : Nat) (g : Nat → α) (dflt : α) (hi : n ≤ i) :
    ((List.range n).map g).getD i dflt = dflt := by
  have h : (List.range n)[i]? = none :=
    List.getElem?_eq_none (by simp only [List.length_range]; omega)
  simp only [List.getD, List.getElem?_map, h, Option.map_none, Option.getD_none]

/-- 対角の値の並び。 -/
theorem diagVals (S : Setting) (M : List Rowj) (hM : MtRep S M) :
    (diagList (M)).map Prod.fst
      = (List.range S.n).map (topValue S.tower.base) := by
  rw [diagList_eq S M hM, List.map_map]
  rfl

/-- 対角の歩行結果の並び。 -/
theorem diagTree (S : Setting) (M : List Rowj) (hM : MtRep S M) :
    (diagList (M)).map Prod.snd
      = (List.range S.n).map (Pseudo.parent (mountainOf' S)) := by
  rw [diagList_eq S M hM, List.map_map]
  rfl

/-- 入力列の外の列は頂が段 0 なので擬親を持たない。 -/
theorem pseudo_parent_of_ge (S : Setting) (p : Nat)
    (hp : S.n ≤ p) : Pseudo.parent (mountainOf' S) p = none := by
  refine (Pseudo.parent_none_iff (mountainOf' S) p).mpr ?_
  show height S.tower.base p = 0
  rcases Nat.eq_zero_or_pos (height S.tower.base p) with h | h
  · exact h
  · exfalso
    have hlive := height_live S.tower.base (S.tower.hpos p)
    rw [setting_value_zero_of_ge S (height S.tower.base p) p h hp] at hlive
    omega

/-- **`treeScan` は `chainFind` である。** -/
theorem treeScan_eq (S : Setting) (target : Nat) :
    ∀ fuel p,
      treeScan ((List.range S.n).map (topValue S.tower.base))
        ((List.range S.n).map (Pseudo.parent (mountainOf' S))) target fuel p
        = chainFind (Pseudo.forest (mountainOf' S))
            (fun q => decide (topValue S.tower.base q < target)) fuel p := by
  intro fuel
  induction fuel with
  | zero => intro p; rfl
  | succ fuel ih =>
    intro p
    rw [treeScan, chainFind]
    have hkey : ((List.range S.n).map (Pseudo.parent (mountainOf' S))).getD p none
        = (Pseudo.forest (mountainOf' S)).parent p := by
      rcases Nat.lt_or_ge p S.n with h | h
      · rw [getD_map_range S.n p _ none h]
        rfl
      · rw [getD_map_range_ge S.n p _ none h]
        exact (pseudo_parent_of_ge S p h).symm
    rw [hkey]
    cases hq : (Pseudo.forest (mountainOf' S)).parent p with
    | none => rfl
    | some q =>
        dsimp only
        have hqp : q < p := (Pseudo.forest (mountainOf' S)).parent_left hq
        have hpn : p < S.n := by
          rcases Nat.lt_or_ge p S.n with h | h
          · exact h
          · exfalso
            have h2 : Pseudo.parent (mountainOf' S) p = some q := hq
            rw [pseudo_parent_of_ge S p h] at h2
            cases h2
        rw [getD_map_range S.n q _ 0 (by omega)]
        by_cases hc : topValue S.tower.base q < target
        · rw [if_pos hc, if_pos (decide_eq_true hc)]
        · rw [if_neg hc, if_neg (by simp [hc])]
          exact ih q

/-- **`pwScan` は `scanLeft` である。** -/
theorem pwScan_eq (S : Setting) (target : Nat) :
    ∀ j, j ≤ S.n →
      pwScan ((List.range S.n).map (topValue S.tower.base)) target j
        = scanLeft (topValue S.tower.base) target j := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
      intro hj
      rw [pwScan, scanLeft, getD_map_range S.n j _ 0 (by omega)]
      by_cases hc : topValue S.tower.base j < target
      · rw [if_pos hc, if_pos hc]
      · rw [if_neg hc, if_neg hc]
        exact ih (by omega)

/-! ## `calcDiagonal` 全体 -/

/-- **`calcDiagonal` の出力が一致する。** 各要素の値は `topValue`、明示する親は
擬親森の `restrictedParent`（= `rawExtract` の親）で、線形森の `restrictedParent`
（= 読み直しの既定の親）と食い違うときだけ `"v"` が付く。 -/
theorem calcDiagonal_eq (S : Setting) (M : List Rowj) (hM : MtRep S M) :
    calcDiagonal (M)
      = (List.range S.n).map (fun i =>
          if restrictedParent (Pseudo.forest (mountainOf' S))
                (topValue S.tower.base) i
              = restrictedParent linearForest (topValue S.tower.base) i then
            { val := topValue S.tower.base i, forced := false, par := none }
          else
            { val := topValue S.tower.base i, forced := true,
              par := restrictedParent (Pseudo.forest (mountainOf' S))
                (topValue S.tower.base) i }) := by
  have hpos : ∀ p, 0 < topValue S.tower.base p :=
    fun p => topValue_pos S.tower.base (S.tower.hpos p)
  have hd := diagVals S M hM
  have ht := diagTree S M hM
  show (List.range ((diagList (M)).map Prod.fst).length).map _ = _
  rw [hd]
  simp only [List.length_map, List.length_range]
  refine List.map_congr_left ?_
  intro i hi
  have hin : i < S.n := List.mem_range.mp hi
  have htarget : ((List.range S.n).map (topValue S.tower.base)).getD i 0
      = topValue S.tower.base i := getD_map_range S.n i _ 0 hin
  simp only [ht, htarget]
  rw [treeScan_eq S (topValue S.tower.base i) (i + 1) i,
    chainFind_eq_restrictedParent (Pseudo.forest (mountainOf' S))
      (topValue S.tower.base) hpos (i + 1) i (by omega),
    pwScan_eq S (topValue S.tower.base i) i (by omega),
    restrictedParent_linear (topValue S.tower.base) hpos i]

/-! ## 読み直し

JS は対角を文字列にして `calcMountain` に渡す。`parseSequenceElement` にあたるのが
`parseDiag` で、`"v"` 付きは `forced` を立てて親を固定し、素の数は行 0 の規則に
任せる。素の数になるのは擬親森と線形森の `restrictedParent` が一致するときだけ
なので、どちらの枝でも親は擬親森の `restrictedParent` になる。 -/

theorem parseDiag_size (l : List DiagItem) : (parseDiag l).size = l.length := by
  simp only [parseDiag, Array.size_mapIdx, List.size_toArray]

theorem parseDiag_pos (l : List DiagItem) (i : Nat) (hi : i < (parseDiag l).size) :
    ((parseDiag l)[i]'hi).pos = i := by
  simp only [parseDiag, Array.getElem_mapIdx]

theorem parseDiag_val (l : List DiagItem) (i : Nat) (hi : i < (parseDiag l).size)
    (hi' : i < l.length) : ((parseDiag l)[i]'hi).val = (l[i]'hi').val := by
  simp only [parseDiag, Array.getElem_mapIdx, List.getElem_toArray]

theorem parseDiag_forced (l : List DiagItem) (i : Nat) (hi : i < (parseDiag l).size)
    (hi' : i < l.length) : ((parseDiag l)[i]'hi).forced = (l[i]'hi').forced := by
  simp only [parseDiag, Array.getElem_mapIdx, List.getElem_toArray]

theorem parseDiag_par (l : List DiagItem) (i : Nat) (hi : i < (parseDiag l).size)
    (hi' : i < l.length) : ((parseDiag l)[i]'hi).par
      = if (l[i]'hi').forced then clampPar i (l[i]'hi').par else none := by
  simp only [parseDiag, Array.getElem_mapIdx, List.getElem_toArray]

/-- 親が左にあるなら丸めは効かない。 -/
theorem clampPar_of_lt (i : Nat) (p : Option Nat) (h : ∀ q, p = some q → q < i) :
    clampPar i p = p := by
  cases i with
  | zero =>
      cases hp : p with
      | none => rfl
      | some q => exact absurd (h q hp) (by omega)
  | succ i' =>
      cases hp : p with
      | none => rfl
      | some q =>
          have := h q hp
          simp only [clampPar, Nat.min_eq_right (show q ≤ i' by omega)]

theorem forced_keeps (prev : Option Rowj) (row : Rowj) (i : Nat)
    (hi : i < (assignParents prev row).size) (hi' : i < row.size)
    (hf : (row[i]'hi').forced = true) :
    ((assignParents prev row)[i]'hi).par = (row[i]'hi').par := by
  simp only [assignParents, Array.getElem_mapIdx, hf, if_pos]

/-- `calcDiagonal_eq` が与える 1 要素。 -/
def diagItem (S : Setting) (i : Nat) : DiagItem :=
  if restrictedParent (Pseudo.forest (mountainOf' S)) (topValue S.tower.base) i
      = restrictedParent linearForest (topValue S.tower.base) i then
    { val := topValue S.tower.base i, forced := false, par := none }
  else
    { val := topValue S.tower.base i, forced := true,
      par := restrictedParent (Pseudo.forest (mountainOf' S))
        (topValue S.tower.base) i }

theorem calcDiagonal_eq' (S : Setting) (M : List Rowj) (hM : MtRep S M) :
    calcDiagonal (M) = (List.range S.n).map (diagItem S) :=
  calcDiagonal_eq S M hM

theorem diagItem_val (S : Setting) (i : Nat) :
    (diagItem S i).val = topValue S.tower.base i := by
  unfold diagItem
  split <;> rfl

/-- `"v"` の有無によらず、読み直しで復元される親は擬親森の `restrictedParent`。 -/
theorem diagItem_par (S : Setting) (i : Nat) :
    (if (diagItem S i).forced then clampPar i (diagItem S i).par
     else scanLeft (topValue S.tower.base) (topValue S.tower.base i) i)
      = restrictedParent (Pseudo.forest (mountainOf' S)) (topValue S.tower.base) i := by
  have hpos : ∀ p, 0 < topValue S.tower.base p :=
    fun p => topValue_pos S.tower.base (S.tower.hpos p)
  unfold diagItem
  split
  · rename_i heq
    rw [← restrictedParent_linear (topValue S.tower.base) hpos i, ← heq]
    simp
  · rename_i hne
    rw [if_pos rfl]
    exact clampPar_of_lt i _ (fun q hq => restrictedParent_left _ _ hq)

theorem getElem_map_range {α : Type} (n i : Nat) (g : Nat → α)
    (h : i < ((List.range n).map g).length) : ((List.range n).map g)[i]'h = g i := by
  have hi : i < (List.range n).length := by simpa using h
  rw [List.getElem_map]
  simp only [List.getElem_range]

/-- 読み直した行は抽出後の値を表す。 -/
theorem rep_parseDiag (S : Setting) (M : List Rowj) (hM : MtRep S M) :
    Rep (parseDiag (calcDiagonal (M))) 0 S.n
      (extractOf S).value := by
  rw [calcDiagonal_eq' S M hM]
  have hlen : ((List.range S.n).map (diagItem S)).length = S.n := by simp
  have hsz : (parseDiag ((List.range S.n).map (diagItem S))).size = S.n := by
    rw [parseDiag_size, hlen]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    rw [Array.length_toList] at hi hj
    rw [Array.getElem_toList, Array.getElem_toList,
      parseDiag_pos _ i hi, parseDiag_pos _ j hj]
    exact hij
  · intro x hx
    obtain ⟨i, hi, hix⟩ := getElem_of_mem _ hx
    rw [← hix, parseDiag_pos _ i hi,
      parseDiag_val _ i hi (by rw [hlen]; omega), getElem_map_range, diagItem_val,
      Nat.add_zero]
    rfl
  · intro x hx
    obtain ⟨i, hi, hix⟩ := getElem_of_mem _ hx
    rw [← hix, parseDiag_val _ i hi (by rw [hlen]; omega), getElem_map_range, diagItem_val]
    exact topValue_pos S.tower.base (S.tower.hpos i)
  · intro x hx
    obtain ⟨i, hi, hix⟩ := getElem_of_mem _ hx
    rw [← hix, parseDiag_pos _ i hi]
    omega
  · intro c _ hcn _
    refine ⟨_, mem_of_getElem _ c (by omega), ?_⟩
    rw [parseDiag_pos _ c (by omega)]
    omega

/-- **抽出段が閉じた。** 読み直して行 0 に親を付けた行は、Phyrion の `rawExtract`
そのものである。 -/
theorem parRep_extract (S : Setting) (M : List Rowj) (hM : MtRep S M) :
    ParRep (assignParents none
        (parseDiag (calcDiagonal (M)))) 0
      (extractOf S).forest := by
  rw [calcDiagonal_eq' S M hM]
  have hlen : ((List.range S.n).map (diagItem S)).length = S.n := by simp
  have hsz : (parseDiag ((List.range S.n).map (diagItem S))).size = S.n := by
    rw [parseDiag_size, hlen]
  have hval : ∀ j, ∀ hj : j < (parseDiag ((List.range S.n).map (diagItem S))).size,
      ((parseDiag ((List.range S.n).map (diagItem S)))[j]'hj).val
        = topValue S.tower.base j := by
    intro j hj
    rw [parseDiag_val _ j hj (by rw [hlen]; omega), getElem_map_range, diagItem_val]
  intro y hy
  obtain ⟨i, hi, hiy⟩ := getElem_of_mem _ hy
  have hsz2 := assignParents_size none
    (parseDiag ((List.range S.n).map (diagItem S)))
  have hi' : i < (parseDiag ((List.range S.n).map (diagItem S))).size := by omega
  have hpos : ((assignParents none
      (parseDiag ((List.range S.n).map (diagItem S))))[i]'hi).pos = i := by
    rw [assignParents_pos none _ i hi hi', parseDiag_pos _ i hi']
  -- 親は「`"v"` 付きならそのまま、素の数なら左スキャン」
  have hpar : ((assignParents none
      (parseDiag ((List.range S.n).map (diagItem S))))[i]'hi).par
      = restrictedParent (Pseudo.forest (mountainOf' S)) (topValue S.tower.base) i := by
    rw [← diagItem_par S i]
    by_cases hfo : (diagItem S i).forced = true
    · have hfo' : ((parseDiag ((List.range S.n).map (diagItem S)))[i]'hi').forced
          = true := by
        rw [parseDiag_forced _ i hi' (by rw [hlen]; omega), getElem_map_range]
        exact hfo
      rw [forced_keeps none _ i hi hi' hfo',
        parseDiag_par _ i hi' (by rw [hlen]; omega), getElem_map_range, if_pos hfo,
        if_pos hfo]
    · have hfo' : ((parseDiag ((List.range S.n).map (diagItem S)))[i]'hi').forced
          = false := by
        rw [parseDiag_forced _ i hi' (by rw [hlen]; omega), getElem_map_range]
        exact Bool.not_eq_true _ ▸ hfo
      rw [assignParents_none_par _ i hi hi' hfo', parseDiag_pos _ i hi',
        searchBase_eq_scanLeft' _ (topValue S.tower.base) i hi' hval i (Nat.le_refl _),
        if_neg hfo]
  rw [← hiy, hpar, hpos]
  cases hrp : restrictedParent (Pseudo.forest (mountainOf' S))
      (topValue S.tower.base) i with
  | none =>
      show (extractOf S).forest.parent (i + 0) = none
      rw [Nat.add_zero]
      exact hrp
  | some p =>
      have hpi : p < i := restrictedParent_left _ _ hrp
      refine ⟨by omega, ?_⟩
      show (extractOf S).forest.parent (i + 0)
        = some (((assignParents none
            (parseDiag ((List.range S.n).map (diagItem S))))[p]'(by omega)).pos + 0)
      rw [Nat.add_zero, Nat.add_zero,
        assignParents_pos none _ p (by omega) (by omega), parseDiag_pos _ p (by omega)]
      exact hrp

/-- 読み直して親を付けた行の `Rep`。 -/
theorem rep_extract (S : Setting) (M : List Rowj) (hM : MtRep S M) :
    Rep (assignParents none
        (parseDiag (calcDiagonal (M)))) 0 S.n
      (extractOf S).value :=
  rep_assignParents none _ 0 S.n _ (rep_parseDiag S M hM)

/-! ## 入力列から作る山への特殊化 -/

/-- 入力列から作る山は設定に対応している。 -/
theorem mtRep_calcMountain (s : List Nat) (hs : ∀ x ∈ s, 0 < x) (fuel : Nat)
    (hf : sequenceBound s ≤ fuel) :
    MtRep (linearSetting s hs) (calcMountain s (fuel + 1)) where
  rowRep := fun r hr => calcMountain_rep s hs fuel r hr
  size0 := size_rowAt_calcMountain_zero s fuel
  tall := fun i hi => height_lt_length s hs fuel hf i hi

/-! ## 抽出した設定

設定を 1 回抽出した設定を作る。これで抽出を任意回繰り返せる。 -/

/-- 上限より右の列は抽出後も値 1。 -/
theorem extractOf_tail_one (S : Setting) (c : Nat) (hc : S.n ≤ c) :
    (extractOf S).value c = 1 := by
  show topValue S.tower.base c = 1
  have hz : height S.tower.base c = 0 := by
    rcases Nat.eq_zero_or_pos (height S.tower.base c) with h | h
    · exact h
    · exfalso
      have hlive := height_live S.tower.base (S.tower.hpos c)
      rw [setting_value_zero_of_ge S (height S.tower.base c) c h hc] at hlive
      omega
  show (rows S.tower.base (height S.tower.base c)).value c = 1
  rw [hz]
  exact S.htail c hc

/-- 設定を 1 回抽出した設定。 -/
def extractSet (S : Setting) : Setting where
  tower := extractTowerOf S.tower
  n := S.n
  htail := fun c h => extractOf_tail_one S c h
  bnd := S.bnd
  hbnd := fun c => Nat.le_trans (topValue_le S.tower.base c) (S.hbnd c)

/-- **抽出後の行から作った山も設定に対応している。** これで抽出を繰り返せる。 -/
theorem mtRep_extract (S : Setting) (M : List Rowj) (hM : MtRep S M) (fuel : Nat)
    (hf : S.bnd ≤ fuel) :
    MtRep (extractSet S)
      (calcMountainFrom (parseDiag (calcDiagonal M)) (fuel + 1)) where
  rowRep := fun r hr =>
    calcMountainFrom_rep (extractSet S) _ fuel r
      (rep_extract S M hM) (parRep_extract S M hM) hr
  size0 := by
    rw [rowAt_calcMountainFrom_zero, assignParents_size, parseDiag_size,
      calcDiagonal_eq' S M hM]
    simp
    rfl
  tall := by
    intro i hi
    have hb : height (extractOf S) i < S.bnd := by
      have h1 : height (extractOf S) i < (extractOf S).value i :=
        height_lt (extractOf S) ((extractSet S).tower.hpos i)
      have h2 : (extractOf S).value i ≤ S.bnd := (extractSet S).hbnd i
      omega
    have hlive : 0 < (rows (extractOf S) (0 + height (extractOf S) i)).value i := by
      rw [Nat.zero_add]
      exact height_live _ ((extractSet S).tower.hpos i)
    exact mountainGo_length (extractSet S) fuel
      (assignParents none (parseDiag (calcDiagonal M))) 0
      (rep_extract S M hM) (parRep_extract S M hM) (height (extractOf S) i)
      (by omega) ⟨i, hi, hlive⟩

end Yukito
