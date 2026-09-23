/-
From koteitan, 1y-expand-equiv, `Equiv/Spec.lean`
(https://github.com/koteitan/1y-expand-equiv, revision c9a5368a09ceb62ec671a6c3447a4719d035dfc0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.Y.WellOrder.`; the transcription `Equiv/Yukito.lean` is replaced by
`Googology.Notation.Y.Yukito` (opened below).
This file is part of googology-lean and is licensed under its MIT license.
-/
import Googology.Notation.Y.WellOrder.Equiv.Yama

open Googology.Notation.Y

/-!
# Mt.Fuji シェルの結果が原文の山を表すこと（枝によらない部分）

JS の Mt.Fuji シェルは、原文の層 `k = K`（山崎噴火の枝）と `k < K` を 1 つの
三重ループで作る。2 つの枝で違うのは、コピー先の山 `G` と、新しく積んだセルの
親についての事実だけである。それを `FujiSpec` にまとめ、`ShapeRep` から出力までを
一度だけ組み立てる。

```
yamaSpec   層 k = K の枝（本ファイル）
lowerSpec  層 k < K の枝（Lower.lean）
```
-/

namespace Yukito

open OneY OneY.Numeric OneY.RootGeometry

/-- **Mt.Fuji シェルの枝ごとの事実。** `G` はその枝で原文が作る山、`y` は継ぎ目、
`x` は切ったあとの長さ。上の層（`cover` から `outJS` まで）はこれだけから組み立てる。 -/
structure FujiSpec (S : Setting) (M : List Rowj) (mfuel : Nat) (G : RowMountain) (y x : Nat) :
    Prop where
  hM : MtRep S M
  hn : 1 < S.n
  hM2 : 2 ≤ M.length
  hx : x = S.n - 1
  hyx : y < x
  hsm : (expP M mfuel).badRootSeam = y
  hkm : ∀ i j, kmaxAt M (expP M mfuel) i j (expRes M).length mfuel
    ≤ j + (expP M mfuel).len * i + 1
  heightOrig : ∀ c, c < x → G.height c = height S.tower.base c
  parentOrig : ∀ r c, c < x → (G.row r).parent c = (rows S.tower.base r).forest.parent c
  kmaxHeight : ∀ i j, 0 < i → y ≤ j → j < x →
    kmaxAt M (expP M mfuel) i j (expRes M).length mfuel
      = G.height (j + (expP M mfuel).len * i) + 1
  parNoneCell : ∀ (nd : Nat → Nat) (st : List Rowj) (i' t' m : Nat), t' < (expP M mfuel).len →
    m < kmaxAt M (expP M mfuel) (i' + 1) (y + t') (expRes M).length mfuel →
    PosMono (rowAt st m) →
    (∀ pc, pc < (y + t') + (expP M mfuel).len * (i' + 1) → m ≤ G.height pc → HasCol st m pc) →
    (fujiCellAt M (expP M mfuel) nd (i' + 1) (y + t') (isRepAt (expP M mfuel) (y + t'))
      (isAscAt M (expP M mfuel) (y + t') mfuel) st m).par = none →
    (G.row m).parent ((y + t') + (expP M mfuel).len * (i' + 1)) = none
  parColCell : ∀ (nd : Nat → Nat) (st : List Rowj) (i' t' m p : Nat), t' < (expP M mfuel).len →
    m < kmaxAt M (expP M mfuel) (i' + 1) (y + t') (expRes M).length mfuel →
    (fujiCellAt M (expP M mfuel) nd (i' + 1) (y + t') (isRepAt (expP M mfuel) (y + t'))
      (isAscAt M (expP M mfuel) (y + t') mfuel) st m).par = some p →
    ∃ hp : p < (rowAt st m).size,
      (G.row m).parent ((y + t') + (expP M mfuel).len * (i' + 1))
        = some (((rowAt st m)[p]'hp).pos + m)

namespace FujiSpec

variable {S : Setting} {M : List Rowj} {mfuel : Nat} {G : RowMountain} {y x : Nat}

theorem hcutH (h : FujiSpec S M mfuel G y x) : expCutH M = height S.tower.base (S.n - 1) :=
  expCutH_eq S M h.hM h.hn

theorem hacl (h : FujiSpec S M mfuel G y x) : (expP M mfuel).afterCutLength = S.n - 1 :=
  expP_afterCutLength S M h.hM mfuel (expRes_length_pos M h.hM2)

theorem hlen (h : FujiSpec S M mfuel G y x) : (expP M mfuel).len = x - y := by
  rw [expP_len_yama S M h.hM mfuel (expRes_length_pos M h.hM2) y h.hsm, h.hx]

/-- 切ったあとの山は、三重ループを始める条件を満たす。 -/
theorem start (h : FujiSpec S M mfuel G y x) :
    ColLt (expRes M) (expP M mfuel).afterCutLength ∧
      (expP M mfuel).badRootSeam + (expP M mfuel).len = (expP M mfuel).afterCutLength ∧
      RowsMono (expRes M) := by
  have hyx := h.hyx
  have hx := h.hx
  have hacl := h.hacl
  refine ⟨?_, badRootSeam_add_len _ (by rw [h.hsm, hacl]; omega),
    rowsMono_cutChild M (expCutH M) (rowsMono_of_mtRep S M h.hM)⟩
  rw [hacl]
  exact colLt_cutChild S M h.hM (expCutH M) h.hn (Nat.le_of_eq h.hcutH.symm)

theorem rowsMono (h : FujiSpec S M mfuel G y x) (nd : Nat → Nat) (nrep : Nat) :
    RowsMono (fujiRs M mfuel nd nrep) := by
  obtain ⟨hcolLt, hsum, hmono⟩ := h.start
  exact rowsMono_dropEmptyTop _
    (fujiIters_invariant M (expP M mfuel) nd (expRes M).length mfuel h.hkm nrep (expRes M)
      (expP M mfuel).afterCutLength hcolLt (by omega) hmono).1

/-- 積む途中の状態でも位置は真に増加している。 -/
theorem rowsMonoState (h : FujiSpec S M mfuel G y x) (nd : Nat → Nat) (i' t' : Nat) :
    RowsMono (fujiSeams M (expP M mfuel) nd (i' + 1) (expRes M).length mfuel t'
        (fujiIters M (expP M mfuel) nd (expRes M).length mfuel i' (expRes M))) := by
  obtain ⟨hcolLt, hsum, hmono⟩ := h.start
  obtain ⟨hm1, hb1⟩ := fujiIters_invariant M (expP M mfuel) nd (expRes M).length mfuel h.hkm i'
    (expRes M) (expP M mfuel).afterCutLength hcolLt (by omega) hmono
  have hmul : (expP M mfuel).len * (i' + 1)
      = (expP M mfuel).len * i' + (expP M mfuel).len := Nat.mul_succ _ _
  exact (fujiSeams_invariant M (expP M mfuel) nd (i' + 1) (expRes M).length mfuel h.hkm t'
    (fujiIters M (expP M mfuel) nd (expRes M).length mfuel i' (expRes M))
    ((expP M mfuel).badRootSeam + (expP M mfuel).len + (expP M mfuel).len * i')
    hb1 (by omega) hm1).1

/-- **高さ `m` 以下の列は段 `m` に載る。** -/
theorem cover (h : FujiSpec S M mfuel G y x) (nd : Nat → Nat) (nrep m c : Nat)
    (hc : c < x + (expP M mfuel).len * nrep) (hm : m ≤ G.height c) :
    HasCol (fujiRaw M mfuel nd nrep) m c := by
  have hyx := h.hyx
  have hx := h.hx
  have hlen := h.hlen
  rcases Nat.lt_or_ge c x with hcx | hcx
  · rw [h.heightOrig c hcx] at hm
    have hml : m < (expRes M).length := by
      have := height_lt_expRes_length S M h.hM h.hn h.hM2 c (by omega)
      omega
    exact hasCol_fujiIters_old M (expP M mfuel) nd (expRes M).length mfuel nrep (expRes M) m c
      (hasCol_cutChild S M h.hM h.hn (expCutH M) h.hcutH m c (by omega) hm hml)
  · obtain ⟨i2, j2, hi2, hi2n, hj2y, hj2x, hceq⟩ :=
      col_decomp y x (expP M mfuel).len nrep c hlen (by omega) hyx hcx hc
    have hsm := h.hsm
    rw [hceq]
    refine hasCol_fujiIters M (expP M mfuel) nd (expRes M).length mfuel h.hkm nrep (expRes M)
      m i2 j2 hi2 hi2n (by omega) (by omega) ?_
    rw [h.kmaxHeight i2 j2 hi2 hj2y hj2x, ← hceq]
    omega

/-- **段 `m` にあるセルの列は高さ `m` 以上。** -/
theorem cellCol (h : FujiSpec S M mfuel G y x) (nd : Nat → Nat) (nrep m t : Nat) (d : Cell)
    (hd : (rowAt (fujiRaw M mfuel nd nrep) m)[t]? = some d) :
    m ≤ G.height (d.pos + m) := by
  have hyx := h.hyx
  have hx := h.hx
  rcases cell_fujiIters M (expP M mfuel) nd (expRes M).length mfuel h.hkm nrep (expRes M) m t d hd
    with hold | ⟨i2, j2, hi2, _, hj2y, hj2x, hkmax, hceq⟩
  · obtain ⟨hlive, hbound⟩ := cutChild_cell_live S M h.hM h.hn (expCutH M) h.hcutH m t d hold
    rw [h.heightOrig (d.pos + m) (by omega)]
    exact hlive
  · have hlen := h.hlen
    have hsm := h.hsm
    rw [hceq]
    have := h.kmaxHeight i2 j2 hi2 (by omega) (by omega)
    omega

theorem parNoneOrig (h : FujiSpec S M mfuel G y x)
    (m t : Nat) (d : Cell) (hd : (rowAt (expRes M) m)[t]? = some d) (hp : d.par = none) :
    (G.row m).parent (d.pos + m) = none := by
  obtain ⟨_, hbound⟩ := cutChild_cell_live S M h.hM h.hn (expCutH M) h.hcutH m t d hd
  obtain ⟨_, hmM, htM, hdt⟩ := expRes_cell M m t d hd
  have hF := parRep_none S M h.hM m hmM t htM (by rw [hdt]; exact hp)
  rw [hdt] at hF
  rw [h.parentOrig m (d.pos + m) (by have := h.hx; omega)]
  exact hF

theorem parColOrig (h : FujiSpec S M mfuel G y x)
    (st : List Rowj) (m t : Nat) (d : Cell) (hd : (rowAt (expRes M) m)[t]? = some d)
    (hext : RowExt (rowAt (expRes M) m) (rowAt st m)) (p : Nat) (hp : d.par = some p) :
    ∃ hp' : p < (rowAt st m).size,
      (G.row m).parent (d.pos + m) = some (((rowAt st m)[p]'hp').pos + m) := by
  obtain ⟨_, hbound⟩ := cutChild_cell_live S M h.hM h.hn (expCutH M) h.hcutH m t d hd
  obtain ⟨hm, hmM, htM, hdt⟩ := expRes_cell M m t d hd
  obtain ⟨hpM, hF⟩ := parRep_some S M h.hM m hmM t htM p (by rw [hdt]; exact hp)
  rw [hdt] at hF
  have hpt : p < t := (par_index_lt S M h.hM m hmM t p htM (by rw [hdt]; exact hp)).2
  have hts : t < (rowAt (expRes M) m).size := lt_size_of_getElem? hd
  have hpc : p < (rowAt (expRes M) m).size := by omega
  have hpe : (rowAt (expRes M) m)[p]? = (rowAt M m)[p]? :=
    rowAt_cutChild_getElem? M (expCutH M) m p hm hpc
  obtain ⟨hp', hpeq⟩ := hext.getElem p hpc
  refine ⟨hp', ?_⟩
  rw [h.parentOrig m (d.pos + m) (by have := h.hx; omega), hF]
  have hcell : (rowAt st m)[p]'hp' = (rowAt M m)[p]'hpM := by
    rw [hpeq]
    rw [Array.getElem?_eq_getElem hpc, Array.getElem?_eq_getElem hpM] at hpe
    exact Option.some.inj hpe
  rw [hcell]

/-- **段が足りている。** -/
theorem tall (h : FujiSpec S M mfuel G y x) (nd : Nat → Nat) (nrep c : Nat)
    (hc : c < x + (expP M mfuel).len * nrep) :
    G.height c < (fujiRs M mfuel nd nrep).length := by
  obtain ⟨t, d, hd, _⟩ := h.cover nd nrep (G.height c) c hc (Nat.le_refl _)
  have hts : t < (rowAt (fujiRaw M mfuel nd nrep) (G.height c)).size := lt_size_of_getElem? hd
  have hlen : G.height c < (fujiRaw M mfuel nd nrep).length := by
    rcases Nat.lt_or_ge (G.height c) (fujiRaw M mfuel nd nrep).length with h1 | h1
    · exact h1
    · exfalso
      rw [rowAt_of_ge _ _ h1] at hts
      simp at hts
  exact lt_dropEmptyTop_length (fujiRaw M mfuel nd nrep).length (fujiRaw M mfuel nd nrep)
    (G.height c) (Nat.le_refl _) hlen (by omega)

/-- **元からある列の値は元の山の値のまま。** JS の `fillRow` は値が 0 でない
セルを触らないからである。 -/
theorem colValOrig (h : FujiSpec S M mfuel G y x) (nd : Nat → Nat) (nrep r c : Nat)
    (hc : c < x) (hlive : r ≤ height S.tower.base c) :
    colVal (fujiRs M mfuel nd nrep) r c = (rows S.tower.base r).value c := by
  have hx := h.hx
  have hyx := h.hyx
  have hG := h.heightOrig c hc
  have hcov : HasCol (fujiRs M mfuel nd nrep) r c :=
    hasCol_dropEmptyTop _ r c (h.cover nd nrep r c (by omega) (by omega))
  obtain ⟨t, ht, hpos⟩ := hasCol_pos _ r c hcov
  have hdRs : (rowAt (fujiRs M mfuel nd nrep) r)[t]?
      = some ((rowAt (fujiRs M mfuel nd nrep) r)[t]'ht) := Array.getElem?_eq_getElem ht
  have hrow : rowAt (fujiRs M mfuel nd nrep) r = rowAt (fujiRaw M mfuel nd nrep) r :=
    rowAt_dropEmptyTop_of_cell _ r t _ hdRs
  have hdRaw : (rowAt (fujiRaw M mfuel nd nrep) r)[t]?
      = some ((rowAt (fujiRs M mfuel nd nrep) r)[t]'ht) := by
    rw [← hrow]
    exact hdRs
  have hdOrig : (rowAt (expRes M) r)[t]? = some ((rowAt (fujiRs M mfuel nd nrep) r)[t]'ht) :=
    cell_orig_of_col_lt S M h.hM mfuel h.hn h.hM2 h.hkm y (by omega) h.hsm nd nrep r t _ hdRaw
      (by omega)
  obtain ⟨hval, hvpos⟩ := cutChild_cell_val S M h.hM (expCutH M) r t _ hdOrig
  have htall := h.tall nd nrep c (by omega)
  rw [hpos] at hval
  rcases Nat.lt_or_ge (r + 1) (fujiRs M mfuel nd nrep).length with hlt | hge
  · rw [colVal, colVal_top (fujiRs M mfuel nd nrep)
      (parLt_fujiRs S M h.hM mfuel nd nrep).dep r hlt t ht (h.rowsMono nd nrep r) c hpos
      (by omega), hval]
  · rw [colVal, colVal_top_last (fujiRs M mfuel nd nrep) r (by omega) t ht
      (h.rowsMono nd nrep r) c hpos, hval]

/-- **`ShapeRep` の `step`（元からある列）。** -/
theorem stepOrig (h : FujiSpec S M mfuel G y x) (nd : Nat → Nat) (nrep r c p : Nat)
    (hc : c < x) (hp : (G.row r).parent c = some p) :
    colVal (fujiRs M mfuel nd nrep) r c
      = colVal (fujiRs M mfuel nd nrep) r p + colVal (fujiRs M mfuel nd nrep) (r + 1) c := by
  rw [h.parentOrig r c hc] at hp
  have hpc : p < c := (rows S.tower.base r).forest.parent_left hp
  have hfp : ((mountainOf' S).row r).parent c = some p := hp
  have hrc : r < height S.tower.base c := (mountainOf' S).parent_source hfp
  have hrp : r ≤ height S.tower.base p := (mountainOf' S).parent_endpoint hfp
  rw [h.colValOrig nd nrep r c hc (by omega), h.colValOrig nd nrep r p (by omega) hrp,
    h.colValOrig nd nrep (r + 1) c hc (by omega)]
  exact rows_diff S.tower.base r c p hp

/-- **積む途中の状態でも、それより左の列は高さまで載っている。** -/
theorem hasColState (h : FujiSpec S M mfuel G y x) (nd : Nat → Nat) (i' t k pc : Nat)
    (ht : t < (expP M mfuel).len) (hlt : pc < (y + t) + (expP M mfuel).len * (i' + 1))
    (hk : k ≤ G.height pc) :
    HasCol (fujiSeams M (expP M mfuel) nd (i' + 1) (expRes M).length mfuel t
      (fujiIters M (expP M mfuel) nd (expRes M).length mfuel i' (expRes M))) k pc := by
  have hyx := h.hyx
  have hx := h.hx
  have hlen := h.hlen
  have hsm := h.hsm
  rcases Nat.lt_or_ge pc x with hpc | hpc
  · rw [h.heightOrig pc hpc] at hk
    have hkl : k < (expRes M).length := by
      have := height_lt_expRes_length S M h.hM h.hn h.hM2 pc (by omega)
      omega
    exact HasCol.ext (rowExt_fujiSeams _ _ _ _ _ _ _ _ _)
      (hasCol_fujiIters_old M (expP M mfuel) nd (expRes M).length mfuel i' (expRes M) k pc
        (hasCol_cutChild S M h.hM h.hn (expCutH M) h.hcutH k pc (by omega) hk hkl))
  · obtain ⟨i2, j2, hi2, hi2n, hj2y, hj2x, hpceq⟩ :=
      col_decomp y x (expP M mfuel).len (i' + 1) pc hlen (by omega) hyx hpc (by omega)
    have hkmax : k < kmaxAt M (expP M mfuel) i2 j2 (expRes M).length mfuel := by
      rw [h.kmaxHeight i2 j2 hi2 hj2y hj2x, ← hpceq]
      omega
    rcases col_lt_lex y x (expP M mfuel).len hlen (by omega) j2 i2 (y + t) (i' + 1)
      hj2y hj2x (by omega) (by omega) (by omega) with hlex | ⟨hie, hje⟩
    · rw [hpceq]
      exact HasCol.ext (rowExt_fujiSeams _ _ _ _ _ _ _ _ _)
        (hasCol_fujiIters M (expP M mfuel) nd (expRes M).length mfuel h.hkm i' (expRes M) k i2 j2
          hi2 (by omega) (by omega) (by omega) hkmax)
    · rw [hpceq, hie]
      exact hasCol_fujiSeams M (expP M mfuel) nd (i' + 1) (expRes M).length mfuel h.hkm t
        (fujiIters M (expP M mfuel) nd (expRes M).length mfuel i' (expRes M)) k j2
        (by omega) (by omega) (by rw [← hie]; exact hkmax)

theorem parNone (h : FujiSpec S M mfuel G y x) (nd : Nat → Nat) (nrep m u : Nat) (d : Cell)
    (hd : (rowAt (fujiRs M mfuel nd nrep) m)[u]? = some d) (hp : d.par = none) :
    (G.row m).parent (d.pos + m) = none := by
  rcases fujiRs_cell S M h.hM mfuel y h.hsm nd nrep m u d hd
    with hold | ⟨i', t', _, ht', hk', hde⟩
  · exact h.parNoneOrig m u d hold hp
  · rw [hde, fujiCellAt_col_exp M mfuel nd (i' + 1) (y + t') m _ _ _ (h.hkm _ _) hk']
    exact h.parNoneCell nd _ i' t' m ht' hk' (h.rowsMonoState nd i' t' m)
      (fun pc hlt hge => h.hasColState nd i' t' m pc ht' hlt hge) (by rw [hde] at hp; exact hp)

theorem parCol (h : FujiSpec S M mfuel G y x) (nd : Nat → Nat) (nrep m u : Nat) (d : Cell)
    (hd : (rowAt (fujiRs M mfuel nd nrep) m)[u]? = some d) (p : Nat) (hp : d.par = some p) :
    ∃ hp' : p < (rowAt (fujiRs M mfuel nd nrep) m).size,
      (G.row m).parent (d.pos + m)
        = some (((rowAt (fujiRs M mfuel nd nrep) m)[p]'hp').pos + m) := by
  have hne : 0 < (rowAt (fujiRs M mfuel nd nrep) m).size := by
    have := lt_size_of_getElem? hd
    omega
  rcases fujiRs_cell S M h.hM mfuel y h.hsm nd nrep m u d hd
    with hold | ⟨i', t', hi', ht', hk', hde⟩
  · refine h.parColOrig (fujiRs M mfuel nd nrep) m u d hold ?_ p hp
    have hrow : rowAt (fujiRs M mfuel nd nrep) m = rowAt (fujiRaw M mfuel nd nrep) m :=
      rowAt_dropEmptyTop_of_cell _ m u d hd
    rw [hrow]
    exact rowExt_fujiIters M (expP M mfuel) nd (expRes M).length mfuel nrep (expRes M) m
  · obtain ⟨hp'', hcolp⟩ := h.parColCell nd (fujiSeams M (expP M mfuel) nd (i' + 1) (expRes M).length mfuel t'
        (fujiIters M (expP M mfuel) nd (expRes M).length mfuel i' (expRes M))) i' t' m p ht' hk'
      (by rw [hde] at hp; exact hp)
    obtain ⟨hp', hpeq⟩ :=
      (rowExt_state_to_fujiRs M mfuel nd nrep m i' t' hi' (by omega) hne).getElem p hp''
    refine ⟨hp', ?_⟩
    rw [hde, fujiCellAt_col_exp M mfuel nd (i' + 1) (y + t') m _ _ _ (h.hkm _ _) hk', hcolp,
      hpeq]

/-- **`ShapeRep` の `step`（コピーで積んだ列）。** -/
theorem stepPush (h : FujiSpec S M mfuel G y x) (nd : Nat → Nat) (nrep r c p : Nat)
    (hc : c < x + (expP M mfuel).len * nrep) (hcx : x ≤ c) (hp : (G.row r).parent c = some p) :
    colVal (fujiRs M mfuel nd nrep) r c
      = colVal (fujiRs M mfuel nd nrep) r p + colVal (fujiRs M mfuel nd nrep) (r + 1) c := by
  have hx := h.hx
  have hrh : r < G.height c := G.parent_source hp
  have hhc : G.height c ≤ c := rowMountain_height_le G c
  have htall := h.tall nd nrep c hc
  have hcov : HasCol (fujiRs M mfuel nd nrep) r c :=
    hasCol_dropEmptyTop _ r c (h.cover nd nrep r c hc (by omega))
  obtain ⟨i, hi, hposi⟩ := hasCol_pos _ r c hcov
  have hd : (rowAt (fujiRs M mfuel nd nrep) r)[i]?
      = some ((rowAt (fujiRs M mfuel nd nrep) r)[i]'hi) := Array.getElem?_eq_getElem hi
  cases hq : ((rowAt (fujiRs M mfuel nd nrep) r)[i]'hi).par with
  | none =>
      have := h.parNone nd nrep r i _ hd hq
      rw [hposi, hp] at this
      exact absurd this (by simp)
  | some q =>
      obtain ⟨hq', hcolq⟩ := h.parCol nd nrep r i _ hd q hq
      rw [hposi, hp] at hcolq
      have hpq : ((rowAt (fujiRs M mfuel nd nrep) r)[q]'hq').pos + r = p :=
        (Option.some.inj hcolq).symm
      have hval : ((rowAt (fujiRs M mfuel nd nrep) r)[i]'hi).val = 0 := by
        rcases fujiRs_cell S M h.hM mfuel y h.hsm nd nrep r i _ hd
          with hold | ⟨i', t', _, _, _, hde⟩
        · exfalso
          obtain ⟨_, hbound⟩ := cutChild_cell_live S M h.hM h.hn (expCutH M) h.hcutH r i _ hold
          omega
        · rw [hde]
          exact fujiCellAt_val_of_par_some M (expP M mfuel) nd (i' + 1) (y + t')
            (isRepAt (expP M mfuel) (y + t')) _ _ r q (by rw [← hde]; exact hq)
      exact colVal_step_col (fujiRs M mfuel nd nrep)
        (parLt_fujiRs S M h.hM mfuel nd nrep).dep r (by omega) i hi
        (h.rowsMono nd nrep r) c hposi (by omega) hval q hq hq' p hpq

/-- **`ShapeRep` の構成。** -/
theorem shapeRep (h : FujiSpec S M mfuel G y x) (nd : Nat → Nat)
    (hnd : ∀ c, c < S.n - 1 → nd c = topValue S.tower.base c) (nrep : Nat)
    (hndpos : ∀ c, c < x + (expP M mfuel).len * nrep → 0 < nd c) :
    ShapeRep (fujiRs M mfuel nd nrep) G nd (x + (expP M mfuel).len * nrep) where
  mono := h.rowsMono nd nrep
  parLt := (parLt_fujiRs S M h.hM mfuel nd nrep).dep
  cellCol := fun r i hi =>
    h.cellCol nd nrep r i _ (getElem?_dropEmptyTop (fujiRaw M mfuel nd nrep) r i _
      (Array.getElem?_eq_getElem hi))
  cover := fun r c hc hr =>
    hasCol_pos _ r c (hasCol_dropEmptyTop _ r c (h.cover nd nrep r c hc hr))
  parCol := fun r i hi p hp => h.parCol nd nrep r i _ (Array.getElem?_eq_getElem hi) p hp
  parNone := fun r i hi hp => h.parNone nd nrep r i _ (Array.getElem?_eq_getElem hi) hp
  step := fun r c p hc hp => by
    rcases Nat.lt_or_ge c x with h1 | h1
    · exact h.stepOrig nd nrep r c p h1 hp
    · exact h.stepPush nd nrep r c p hc h1 hp
  valTop := fun r i hi hp =>
    valTop_exp S M h.hM mfuel h.hn h.hkm y h.hsm h.hcutH nd hnd nrep r i _
      (Array.getElem?_eq_getElem hi) hp
  topPos := hndpos
  tall := fun c hc => h.tall nd nrep c hc

/-- **JS の出力は原文の復元値そのもの。** -/
theorem out (h : FujiSpec S M mfuel G y x) (nd : Nat → Nat)
    (hnd : ∀ c, c < S.n - 1 → nd c = topValue S.tower.base c) (nrep : Nat)
    (hndpos : ∀ c, c < x + (expP M mfuel).len * nrep → 0 < nd c) :
    expandOut (fillValues (fujiRs M mfuel nd nrep))
      = (List.range (x + (expP M mfuel).len * nrep)).map (Reconstruction.value G nd 0) := by
  obtain ⟨hsz, hpos⟩ := row0_fujiRs S M h.hM mfuel h.hn h.hM2 h.hkm y
    (by have := h.hyx; have := h.hx; omega) h.hsm nd nrep
  rw [← h.hx] at hsz
  exact expandOut_eq_value (fujiRs M mfuel nd nrep) G nd _ (h.shapeRep nd hnd nrep hndpos) hsz hpos

/-- JS の `expand` の枝そのもので書いた形。 -/
theorem outJS (h : FujiSpec S M mfuel G y x) (nrep efuel : Nat)
    (hnd : ∀ c, c < S.n - 1 → expNd nrep mfuel efuel M c = topValue S.tower.base c)
    (hndpos : ∀ c, c < x + (expP M mfuel).len * nrep → 0 < expNd nrep mfuel efuel M c)
    (hhas : (if hlt : (rowAt M 0).size - 1 < (rowAt M 0).size
          then (((rowAt M 0)[(rowAt M 0).size - 1]'hlt).par).isSome else false) = true) :
    expandOut (expandJS nrep mfuel (efuel + 1) M)
      = (List.range (x + (expP M mfuel).len * nrep)).map
          (Reconstruction.value G (expNd nrep mfuel efuel M) 0) := by
  rw [expandJS_some nrep mfuel efuel M hhas]
  exact h.out (expNd nrep mfuel efuel M) hnd nrep hndpos

end FujiSpec

/-- **山崎噴火の枝（層 `k = K`）の `FujiSpec`。** -/
theorem yamaSpec (S : Setting) (M : List Rowj) (hM : MtRep S M) (mfuel : Nat)
    (hn : 1 < S.n) (hM2 : 2 ≤ M.length) (hyama : expYama M mfuel)
    (y : Nat) (hy : y < S.n - 1)
    (hpar : ((mountainOf' S).row (height S.tower.base (S.n - 1) - 1)).parent (S.n - 1) = some y)
    (hh : 0 < height S.tower.base (S.n - 1))
    (hseam : (expP M mfuel).badRootSeam = y)
    (hasc : isAscAt M (expP M mfuel) (expP M mfuel).badRootSeam mfuel = true) :
    FujiSpec S M mfuel (yamaContext S y hy hpar hh).toRowMountain y (S.n - 1) where
  hM := hM
  hn := hn
  hM2 := hM2
  hx := rfl
  hyx := hy
  hsm := hseam
  hkm := fun i j => kmaxAt_le_yama' M (expP M mfuel) i j _ _ (expP_yama_cut M mfuel hyama)
  heightOrig := fun c hc => yamaContext_height_orig S y hy hpar hh c hc
  parentOrig := fun r c hc => yamaContext_parent_orig S y hy hpar hh r c hc
  kmaxHeight := fun i j hi hjy hjx => by
    rw [kmaxAt_expRes_eq S M hM mfuel hn hM2 hyama i j hjx,
      expP_len_yama S M hM mfuel (expRes_length_pos M hM2) y hseam]
    rcases Decidable.em (j = y) with hje | hjne
    · rw [hje]
      show height S.tower.base y + 1
        = (yamaContext S y hy hpar hh).height (y + (S.n - 1 - y) * i) + 1
      rw [yamaContext_height_seam' S y hy hpar hh i hi]
    · show height S.tower.base j + 1
        = (yamaContext S y hy hpar hh).height (j + (S.n - 1 - y) * i) + 1
      rw [yamaContext_height_other' S y hy hpar hh j i (by omega) hjx]
  parNoneCell := fun nd st i' t' m ht' hk' hmono hcov hnone => by
    obtain ⟨_, _, hmM, hmj, hlivej⟩ :=
      push_side S M hM mfuel hn hM2 hyama y hy hseam i' t' m ht' hk'
    exact fujiCellAt_parNone_yama S M hM mfuel hn hyama y hy hpar hh (expRes_length_pos M hM2)
      hseam nd st (i' + 1) t' m _ (hra_of_seamAsc M (expP M mfuel) mfuel (y + t') hasc)
      (by omega) ht' hmM hmj hlivej hmono hcov hnone
  parColCell := fun nd st i' t' m p ht' hk' hsome => by
    have h0 : 0 < (expRes M).length := expRes_length_pos M hM2
    obtain ⟨hjx, _, hmM, hmj, hlivej⟩ :=
      push_side S M hM mfuel hn hM2 hyama y hy hseam i' t' m ht' hk'
    rw [expP_len_yama S M hM mfuel h0 y hseam]
    exact fujiCellAt_parCol_yama S M hM mfuel hn hyama y hy hpar hh h0 hseam nd st (i' + 1)
      (y + t') m (by omega) (by omega) hjx hmM hmj hlivej p _
      (hra_of_seamAsc M (expP M mfuel) mfuel (y + t') hasc) hsome

end Yukito
