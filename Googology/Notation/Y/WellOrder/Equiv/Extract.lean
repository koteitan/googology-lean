/-
From koteitan, 1y-expand-equiv, `Equiv/Extract.lean`
(https://github.com/koteitan/1y-expand-equiv, revision c9a5368a09ceb62ec671a6c3447a4719d035dfc0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.Y.WellOrder.`; the transcription `Equiv/Yukito.lean` is replaced by
`Googology.Notation.Y.Yukito` (opened below).
This file is part of googology-lean and is licensed under its MIT license.
-/
import Googology.Notation.Y.WellOrder.Equiv.Tower
import Googology.Notation.Y.WellOrder.Equiv.Chain
import Googology.Notation.Y.WellOrder.OneY.Pseudo

open Googology.Notation.Y

/-!
# 抽出段の対応

JS の `calcDiagonal` は、列 `c` の頂から出発して脚をたどり、
**その行で親を持たない節点**に着いたら止まる。

```js
if (!mountain[height][lastIndex] || mountain[height][lastIndex].parentIndex == -1) {
  diagonal.push(...); break;
}
```

Lean の `Pseudo.parent` は代わりに高さの条件を課す。

```
eligible M c p = p は行 (H c − 1) で c の祖先 ∧ (H p = H c ∨ H p + 1 = H c)
Pseudo.parent M c = greatestBelow? c (eligible M c)
```

見た目は違うが同じことを言っている。JS が訪れる節点 `(h, p)` は必ず行 `h` で
生きている、すなわち `h ≤ H p` を満たす。その状況で

```
その行で親を持たない  ⟺  H p ≤ h  ⟺  H p = h
```

となる。`≤` は `RowMountain.parent_none_iff` が与える。

歩行は高さ `H c` から始まり、脚を 1 つ進むごとに高さが変わらないか 1 下がる。
したがって止まった時点の高さは `H c` か `H c − 1` であり、そこで
`H p = h ∈ {H c − 1, H c}` が成り立つ。これが Lean の条件である。
-/

namespace Yukito

open OneY OneY.RootGeometry

/-! ## 歩行の停止位置

JS は「その行で親を持たない」で止まるので、実質「高さが `H c` 以下」で止まる。
Lean は `H p ∈ {H c − 1, H c}` を課す。この 2 つは歩行が辿る鎖の上で同値である。

理由は、行 `r` の祖先鎖の要素はその行で生きている、すなわち高さが `r` 以上だから。
歩行が辿るのは行 `H c − 1` の鎖なので、要素の高さは `H c − 1` 以上に押さえられる。
そこに上からの `≤ H c` を合わせると、ちょうど 2 通りに絞られる。 -/

/-! ## 脚歩行

JS `calcDiagonal` の内側のループを、疎配列を外した列座標で書き写す。

```js
var l=0; while (mountain[height-1][l].position!=mountain[height][lastIndex].position+1) l++;
l=mountain[height-1][l].parentIndex;
var m=0; while (mountain[height][m].position<mountain[height-1][l].position-1) m++;
if (mountain[height][m].position==mountain[height-1][l].position-1){ lastIndex=m; }
else { height--; lastIndex=l; }
```

行 `r` の `position` は `列 − r` である。したがって

* 「`position` が 1 大きい 1 段下のセル」＝ **同じ列の 1 段下**
* 「`position` が 1 小さい同じ段のセル」＝ **同じ列の 1 段上**

なので、1 歩は次になる。

```
q := 行 h−1 での c の親
h ≤ M.height q（q が行 h で生きている）なら  (h,   q)
そうでなければ                               (h−1, q)
```

`height==0` の枝 `lastIndex=mountain[0][lastIndex].parentIndex` は、上の式で
`h−1` を自然数の切り捨て引き算にしたものと一致する。`h=0` では行 `0` の親を取り、
`0 ≤ M.height q` が常に成り立つので行は下がらない。JS の 2 つの枝は 1 つの式で足りる。 -/

/-- JS の脚 1 歩。状態は `(行, 列)`。 -/
def legStep (M : RowMountain) (h c : Nat) : Option (Nat × Nat) :=
  match (M.row (h - 1)).parent c with
  | none => none
  | some q => if h ≤ M.height q then some (h, q) else some (h - 1, q)

/-- 脚 1 歩で段は上がらない。 -/
theorem legStep_row_le (M : RowMountain) {h c h' c' : Nat}
    (hst : legStep M h c = some (h', c')) : h' ≤ h := by
  rw [legStep] at hst
  cases hp : (M.row (h - 1)).parent c with
  | none => rw [hp] at hst; cases hst
  | some q =>
      rw [hp] at hst
      dsimp only at hst
      by_cases hq : h ≤ M.height q
      · rw [if_pos hq] at hst
        simp only [Option.some.injEq, Prod.mk.injEq] at hst
        omega
      · rw [if_neg hq] at hst
        simp only [Option.some.injEq, Prod.mk.injEq] at hst
        omega

/-- 脚 1 歩で列は真に左へ動く。 -/
theorem legStep_col_lt (M : RowMountain) {h c h' c' : Nat}
    (hst : legStep M h c = some (h', c')) : c' < c := by
  rw [legStep] at hst
  cases hp : (M.row (h - 1)).parent c with
  | none => rw [hp] at hst; cases hst
  | some q =>
      rw [hp] at hst
      dsimp only at hst
      have hlt := (M.row (h - 1)).parent_left hp
      by_cases hq : h ≤ M.height q
      · rw [if_pos hq] at hst
        simp only [Option.some.injEq, Prod.mk.injEq] at hst
        omega
      · rw [if_neg hq] at hst
        simp only [Option.some.injEq, Prod.mk.injEq] at hst
        omega

/-- JS の脚歩行。「その行で親を持たない」で止まり、その列を返す。 -/
def jsWalk (M : RowMountain) : Nat → Nat → Nat → Option Nat
  | 0, _, _ => none
  | fuel + 1, h, c =>
    match legStep M h c with
    | none => none
    | some (h', c') =>
      if (M.row h').parent c' = none then some c' else jsWalk M fuel h' c'

/-- 列だけを見た歩行。行 `r` の親を辿り、高さが `bound` 以下の列で止まる。 -/
def legWalk (M : RowMountain) (r bound : Nat) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, c =>
    match (M.row r).parent c with
    | none => none
    | some q => if M.height q ≤ bound then some q else legWalk M r bound fuel q

/-- 行の記録は要らない。`h = bound` から始めた歩行は、列だけの歩行と一致する。

理由は、行が下がるのは `M.height q < bound` のときだけで、そのとき
`M.parent_endpoint` から `M.height q = bound − 1` となり、下がった先で
必ず停止条件が成り立つからである。すなわち歩行は高々 1 回しか降りず、
降りたその場で止まる。 -/
theorem jsWalk_eq_legWalk (M : RowMountain) (bound : Nat) :
    ∀ fuel c, jsWalk M fuel bound c = legWalk M (bound - 1) bound fuel c := by
  intro fuel
  induction fuel with
  | zero => intro c; rfl
  | succ fuel ih =>
    intro c
    rw [jsWalk, legWalk, legStep]
    cases hp : (M.row (bound - 1)).parent c with
    | none => rfl
    | some q =>
      dsimp only
      by_cases hq : bound ≤ M.height q
      · rw [if_pos hq]
        dsimp only
        by_cases hs : M.height q ≤ bound
        · rw [if_pos ((M.parent_none_iff bound q).mpr hs), if_pos hs]
        · have hne : ¬ ((M.row bound).parent q = none) := fun h0 =>
            hs ((M.parent_none_iff bound q).mp h0)
          rw [if_neg hne, if_neg hs]
          exact ih q
      · rw [if_neg hq]
        dsimp only
        have hend := M.parent_endpoint hp
        rw [if_pos ((M.parent_none_iff (bound - 1) q).mpr (by omega)),
          if_pos (show M.height q ≤ bound by omega)]

/-! ## 列歩行が Phyrion の擬親と一致すること -/

/-- 行 `r` の祖先鎖の要素は、その行で生きている。 -/
theorem chain_height_ge' (M : RowMountain) {r c p : Nat}
    (h : (M.row r).Ancestor p c) : r ≤ M.height p := by
  induction h with
  | direct hp => exact M.parent_endpoint hp
  | step _ _ ih => exact ih

/-- 歩行が止まったら、その列は鎖の上にあり、高さ条件を満たし、
それより右の鎖の要素はすべて高さ条件を破る。 -/
theorem legWalk_sound (M : RowMountain) (r bound : Nat) :
    ∀ fuel c p, legWalk M r bound fuel c = some p →
      (M.row r).Ancestor p c ∧ M.height p ≤ bound ∧
        ∀ q, (M.row r).Ancestor q c → p < q → bound < M.height q := by
  intro fuel
  induction fuel with
  | zero => intro c p h; cases h
  | succ fuel ih =>
    intro c p h
    rw [legWalk] at h
    cases hp : (M.row r).parent c with
    | none => rw [hp] at h; cases h
    | some q =>
      rw [hp] at h
      dsimp only at h
      by_cases hq : M.height q ≤ bound
      · rw [if_pos hq] at h
        injection h with he
        subst he
        refine ⟨ParentForest.Ancestor.direct hp, hq, ?_⟩
        intro q' ha hlt
        have := ancestor_le_of_parent hp ha
        omega
      · rw [if_neg hq] at h
        obtain ⟨ha, hle, hmax⟩ := ih q p h
        refine ⟨ha.trans (ParentForest.Ancestor.direct hp), hle, ?_⟩
        intro q' ha' hlt
        rcases ancestor_cases hp ha' with he | ha''
        · subst he; omega
        · exact hmax q' ha'' hlt

/-- 高さ条件を満たす鎖の要素が 1 つでもあれば、燃料が足りている限り歩行は止まる。 -/
theorem legWalk_isSome (M : RowMountain) (r bound : Nat) :
    ∀ fuel c p, c ≤ fuel → (M.row r).Ancestor p c → M.height p ≤ bound →
      ∃ p', legWalk M r bound fuel c = some p' := by
  intro fuel
  induction fuel with
  | zero =>
    intro c p hf ha _
    have := ha.lt
    omega
  | succ fuel ih =>
    intro c p hf ha hle
    obtain ⟨q, hq⟩ := ancestor_parent_exists' ha
    rw [legWalk, hq]
    dsimp only
    by_cases hb : M.height q ≤ bound
    · exact ⟨q, by rw [if_pos hb]⟩
    · rw [if_neg hb]
      rcases ancestor_cases hq ha with he | ha'
      · subst he; exact absurd hle hb
      · have := (M.row r).parent_left hq
        exact ih q p (by omega) ha' hle

/-- 親を持たない列では歩行は何も返さない。 -/
theorem legWalk_none (M : RowMountain) (r bound : Nat) {c : Nat}
    (hp : (M.row r).parent c = none) : ∀ fuel, legWalk M r bound fuel c = none := by
  intro fuel
  cases fuel with
  | zero => rfl
  | succ fuel => rw [legWalk, hp]

/-- **抽出段の主定理。** JS の脚歩行の結果は Phyrion の `Pseudo.parent` に一致する。 -/
theorem jsWalk_eq_pseudo (M : RowMountain) (c fuel : Nat) (hf : c ≤ fuel) :
    jsWalk M fuel (M.height c) c = Pseudo.parent M c := by
  rw [jsWalk_eq_legWalk]
  by_cases hz : M.height c = 0
  · rw [legWalk_none M _ _ ((M.parent_none_iff _ c).mpr (by omega)) fuel,
      (Pseudo.parent_none_iff M c).mpr hz]
  · have hc : 0 < M.height c := by omega
    obtain ⟨p0, hanc0, hh0⟩ := Pseudo.candidate_exists M hc
    obtain ⟨p, hw⟩ := legWalk_isSome M (M.height c - 1) (M.height c) fuel c p0 hf
      hanc0 (by omega)
    obtain ⟨hanc, hle, hmax⟩ := legWalk_sound M (M.height c - 1) (M.height c) fuel c p hw
    have hge := chain_height_ge' M hanc
    rw [hw, (Pseudo.parent_some_iff M c p).mpr ⟨hc, ⟨hanc, by omega⟩, ?_⟩]
    rintro q ⟨hancq, hhq⟩
    rcases Nat.lt_or_ge p q with hlt | hge'
    · have := hmax q hancq hlt
      omega
    · exact hge'

end Yukito
