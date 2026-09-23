/-
From koteitan, 1y-expand-equiv, `Equiv/Fuji.lean`
(https://github.com/koteitan/1y-expand-equiv, revision c9a5368a09ceb62ec671a6c3447a4719d035dfc0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.Y.WellOrder.`; the transcription `Equiv/Yukito.lean` is replaced by
`Googology.Notation.Y.Yukito` (opened below).
This file is part of googology-lean and is licensed under its MIT license.
-/
import Googology.Notation.Y.WellOrder.Equiv.Recon

open Googology.Notation.Y

/-!
# Mt.Fuji シェルの補助スキャン

`expand` の本体で使う 3 つの走査（`hasCol` / `seamHeightOf` / `isAscending`）を
密表現の言葉に翻訳する。
-/

namespace Yukito

open OneY OneY.Numeric

/-- **列がその段にあることの判定。** -/
theorem hasCol_iff (S : Setting) (M : List Rowj) (hM : MtRep S M) (r j : Nat)
    (hr : r < M.length) (hj : j < S.n) :
    hasCol M r j = true ↔ 0 < (rows S.tower.base r).value j := by
  have hrep := rep_top S M hM r hr
  constructor
  · intro h
    rw [hasCol] at h
    cases hlk : lookupPos (rowAt M r) (j - r) with
    | none => rw [hlk] at h; cases h
    | some m =>
        rw [hlk] at h
        dsimp only at h
        by_cases hm : m < (rowAt M r).size
        · rw [dif_pos hm] at h
          have he : ((rowAt M r)[m]'hm).pos + r = j := by simpa using h
          have h1 := hrep.val _ (mem_of_getElem _ m hm)
          have h2 := hrep.live _ (mem_of_getElem _ m hm)
          rw [he] at h1
          omega
        · rw [dif_neg hm] at h; cases h
  · intro hlive
    have hrj : r ≤ j := by
      rcases Nat.lt_or_ge j r with hx | hx
      · rw [rows_value_zero_of_lt S.tower.base r j hx] at hlive; omega
      · exact hx
    obtain ⟨m, hm, hlk, hcm⟩ := lookupPos_some (rowAt M r) r S.n _ hrep j hrj hj hlive
    rw [hasCol, hlk]
    dsimp only
    rw [dif_pos hm]
    simp [hcm]

/-- **`seamHeight` は「列 `j` を含む最上段の 1 つ上」。** 上限が足りていれば
`height j + 1` である。 -/
theorem seamHeightOf_eq (S : Setting) (M : List Rowj) (hM : MtRep S M) (j : Nat)
    (hj : j < S.n) :
    ∀ hi, hi ≤ M.length → height S.tower.base j < hi →
      seamHeightOf M j hi = height S.tower.base j + 1 := by
  intro hi
  induction hi with
  | zero => intro _ h; omega
  | succ h ih =>
    intro hhM hjh
    rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hjh) with heq | hlt
    · rw [seamHeightOf, if_pos ((hasCol_iff S M hM h j (by omega) hj).mpr
        ((live_iff_le_height S.tower.base (S.tower.hpos j) h).mpr (by omega))), heq]
    · have hdead : ¬ (0 < (rows S.tower.base h).value j) := by
        intro hcon
        exact absurd ((live_iff_le_height S.tower.base (S.tower.hpos j) h).mp hcon)
          (by omega)
      rw [seamHeightOf, if_neg (fun hcon =>
        hdead ((hasCol_iff S M hM h j (by omega) hj).mp hcon))]
      exact ih (by omega) hlt

/-- **`topRowWithCol` は列 `j` を含む最上段。** -/
theorem topRowWithCol_eq (S : Setting) (M : List Rowj) (hM : MtRep S M) (j : Nat)
    (hj : j < S.n) :
    ∀ hi, hi ≤ M.length → height S.tower.base j < hi →
      topRowWithCol M j hi = some (height S.tower.base j) := by
  intro hi
  induction hi with
  | zero => intro _ h; omega
  | succ h ih =>
    intro hhM hjh
    rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hjh) with heq | hlt
    · rw [topRowWithCol, if_pos ((hasCol_iff S M hM h j (by omega) hj).mpr
        ((live_iff_le_height S.tower.base (S.tower.hpos j) h).mpr (by omega))), heq]
    · have hdead : ¬ (0 < (rows S.tower.base h).value j) := by
        intro hcon
        exact absurd ((live_iff_le_height S.tower.base (S.tower.hpos j) h).mp hcon)
          (by omega)
      rw [topRowWithCol, if_neg (fun hcon =>
        hdead ((hasCol_iff S M hM h j (by omega) hj).mp hcon))]
      exact ih (by omega) hlt

/-! ## `isAscending`

行 `bh` で列 `j` の親鎖が列 `seam` に届くか。密表現では「`seam` が `j` の祖先か
`j` 自身」である。鎖は列について真に減るので、`seam` より左に出たらもう届かない。 -/

/-- 親の添字は子の添字より小さい。 -/
theorem par_index_lt (S : Setting) (M : List Rowj) (hM : MtRep S M) (r : Nat)
    (hr : r < M.length) (p q : Nat) (hp : p < (rowAt M r).size)
    (hpar : ((rowAt M r)[p]'hp).par = some q) : q < (rowAt M r).size ∧ q < p := by
  have hrep := rep_top S M hM r hr
  have hP : ParRep (rowAt M r) r (rows S.tower.base r).forest := by
    rw [rowAt_eq M r hr]; exact (hM.rowRep r hr).2
  have h := hP _ (mem_of_getElem _ p hp)
  rw [hpar] at h
  obtain ⟨hq, hFc⟩ := h
  refine ⟨hq, ?_⟩
  have hlt := (rows S.tower.base r).forest.parent_left hFc
  exact index_lt_of_pos_lt (rowAt M r) hrep.posMono q p hq hp (by omega)

/-- **親鎖の走査の翻訳。** -/
theorem ascendTo_iff (S : Setting) (M : List Rowj) (hM : MtRep S M) (bh seam : Nat)
    (hbh : bh < M.length) :
    ∀ fuel p, ∀ hp : p < (rowAt M bh).size, p < fuel →
      (ascendTo M bh seam fuel p = true ↔
        (((rowAt M bh)[p]'hp).pos + bh = seam ∨
          ZeroY.Forest.Ancestor (rows S.tower.base bh).forest.parent
            (((rowAt M bh)[p]'hp).pos + bh) seam)) := by
  have hrep := rep_top S M hM bh hbh
  have hP : ParRep (rowAt M bh) bh (rows S.tower.base bh).forest := by
    rw [rowAt_eq M bh hbh]; exact (hM.rowRep bh hbh).2
  intro fuel
  induction fuel with
  | zero => intro p hp h; omega
  | succ fuel ih =>
    intro p hp hpf
    rw [ascendTo]
    dsimp only
    rw [dif_pos hp]
    by_cases hlt : ((rowAt M bh)[p]'hp).pos + bh < seam
    · rw [if_pos hlt]
      constructor
      · intro h; cases h
      · intro h
        exfalso
        rcases h with he | ha
        · omega
        · have := ZeroY.Forest.ancestor_lt (rows S.tower.base bh).forest.parent_left ha
          omega
    · rw [if_neg hlt]
      by_cases heq : ((rowAt M bh)[p]'hp).pos + bh = seam
      · rw [if_pos heq]
        exact ⟨fun _ => Or.inl heq, fun _ => rfl⟩
      · rw [if_neg heq]
        have hPp := hP _ (mem_of_getElem _ p hp)
        cases hpar : ((rowAt M bh)[p]'hp).par with
        | none =>
            rw [hpar] at hPp
            constructor
            · intro h; cases h
            · intro h
              exfalso
              rcases h with he | ha
              · exact heq he
              · obtain ⟨t, ht⟩ := ancestor_parent_exists'
                  (ParentForest.ancestor_of_zeroY ha)
                rw [hPp] at ht
                cases ht
        | some q =>
            rw [hpar] at hPp
            obtain ⟨hq, hFc⟩ := hPp
            obtain ⟨_, hqp⟩ := par_index_lt S M hM bh hbh p q hp hpar
            rw [ih q hq (by omega)]
            constructor
            · intro h
              refine Or.inr ?_
              rcases h with he | ha
              · rw [he] at hFc
                exact Relation.TransGen.single hFc
              · exact Relation.TransGen.trans (Relation.TransGen.single hFc) ha
            · intro h
              rcases h with he | ha
              · exact absurd he heq
              · rcases ancestor_cases hFc (ParentForest.ancestor_of_zeroY ha) with hx | hx
                · exact Or.inl hx.symm
                · exact Or.inr (ParentForest.ancestor_to_zeroY hx)

/-- **`isAscending` の翻訳。** 行 `bh` に列 `j` があり、`seam` が `j` 自身かその祖先
であることと同値。 -/
theorem isAscending_iff (S : Setting) (M : List Rowj) (hM : MtRep S M)
    (bh seam j fuel : Nat) (hbh : bh < M.length) (hj : j < S.n)
    (hfuel : (rowAt M bh).size ≤ fuel) :
    isAscending M bh seam j fuel = true ↔
      (0 < (rows S.tower.base bh).value j ∧
        (j = seam ∨ ZeroY.Forest.Ancestor (rows S.tower.base bh).forest.parent j seam)) := by
  have hrep := rep_top S M hM bh hbh
  rw [isAscending]
  cases hlk : lookupPos (rowAt M bh) (j - bh) with
  | none =>
      dsimp only
      constructor
      · intro h; cases h
      · rintro ⟨hlive, _⟩
        exfalso
        have hrj : bh ≤ j := by
          rcases Nat.lt_or_ge j bh with hx | hx
          · rw [rows_value_zero_of_lt S.tower.base bh j hx] at hlive; omega
          · exact hx
        obtain ⟨m, hm, hlk', _⟩ :=
          lookupPos_some (rowAt M bh) bh S.n _ hrep j hrj hj hlive
        rw [hlk] at hlk'
        cases hlk'
  | some m =>
      dsimp only
      by_cases hm : m < (rowAt M bh).size
      · rw [dif_pos hm]
        by_cases hcm : ((rowAt M bh)[m]'hm).pos + bh = j
        · rw [if_pos hcm, ascendTo_iff S M hM bh seam hbh fuel m hm (by omega), hcm]
          have hlive : 0 < (rows S.tower.base bh).value j := by
            have h1 := hrep.val _ (mem_of_getElem _ m hm)
            have h2 := hrep.live _ (mem_of_getElem _ m hm)
            rw [hcm] at h1
            omega
          exact ⟨fun h => ⟨hlive, h⟩, fun h => h.2⟩
        · rw [if_neg hcm]
          constructor
          · intro h; cases h
          · rintro ⟨hlive, _⟩
            exfalso
            have hrj : bh ≤ j := by
              rcases Nat.lt_or_ge j bh with hx | hx
              · rw [rows_value_zero_of_lt S.tower.base bh j hx] at hlive; omega
              · exact hx
            obtain ⟨m', hm', hlk', hcm'⟩ :=
              lookupPos_some (rowAt M bh) bh S.n _ hrep j hrj hj hlive
            rw [hlk] at hlk'
            have : m' = m := (Option.some.inj hlk').symm
            subst this
            exact hcm hcm'
      · rw [dif_neg hm]
        constructor
        · intro h; cases h
        · rintro ⟨hlive, _⟩
          exfalso
          have hrj : bh ≤ j := by
            rcases Nat.lt_or_ge j bh with hx | hx
            · rw [rows_value_zero_of_lt S.tower.base bh j hx] at hlive; omega
            · exact hx
          obtain ⟨m', hm', hlk', _⟩ :=
            lookupPos_some (rowAt M bh) bh S.n _ hrep j hrj hj hlive
          rw [hlk] at hlk'
          have : m' = m := (Option.some.inj hlk').symm
          subst this
          exact hm hm'

end Yukito
