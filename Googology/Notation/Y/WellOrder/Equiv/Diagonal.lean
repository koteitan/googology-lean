/-
From koteitan, 1y-expand-equiv, `Equiv/Diagonal.lean`
(https://github.com/koteitan/1y-expand-equiv, revision c9a5368a09ceb62ec671a6c3447a4719d035dfc0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.Y.WellOrder.`; the transcription `Equiv/Yukito.lean` is replaced by
`Googology.Notation.Y.Yukito` (opened below).
This file is part of googology-lean and is licensed under its MIT license.
-/
import Googology.Notation.Y.WellOrder.Equiv.Extract
import Googology.Notation.Y.WellOrder.Equiv.Row0

open Googology.Notation.Y

/-!
# 対角の親

JS `calcDiagonal` の後半である。前半（脚歩行）は `Extract.lean` で
`Pseudo.parent` に一致することを示した。ここではその上に載る 2 つの探索を扱う。

```js
var pw=[];
for (var i=0;i<diagonal.length;i++){
  var p=-1;
  for (var j=i-1;j>=0;j--){ if (diagonal[j]<diagonal[i]){ p=j; break; } }
  pw.push(p);
}
var r=[];
for (var i=0;i<diagonal.length;i++){
  var p=i;
  while (true){ p=diagonalTree[p]; if (p<0||diagonal[p]<diagonal[i]) break; }
  if (p==pw[i]) r.push(diagonal[i]);
  else r.push(diagonal[i]+"v"+p);
}
```

`diagonal[i]` は列 `i` の頂の値、すなわち Phyrion の `topValue base i` である。
`diagonalTree[i]` は脚歩行の結果、すなわち `Pseudo.parent` である。

2 つの探索はどちらも「森の親を辿り、最初に値が小さい所で止まる」形をしている。

* `pw` は線形森（`i-1, i-2, …`）を辿る
* 後半のループは `diagonalTree`（擬親森）を辿る

Phyrion 側で対応するのは

```
rawExtract base hpos = select (Pseudo.forest (mountain base hpos)) (topValue base)
```

であり、その値は `topValue base`、その親は
`restrictedParent (Pseudo.forest …) (topValue base)` である。

## 文字列を経由すること

JS は対角を文字列にしてから `calcMountain` に渡す。素の数として書けば
読み直しの際に行 0 の規則で親が振られ、それは `restrictedParent linearForest`
（`Row0.lean` の `restrictedParent_linear`）である。一致しないときだけ
`"値v親"` の形で親を明示し、`parseSequenceElement` が `forcedParent` を立てて
行 0 の規則を飛ばす。したがってどちらの枝でも復元される親は擬親森の
`restrictedParent` である。

明示側の添字は `Math.max(Math.min(i-1,p),-1)` で丸められるが、`p` は `i` の
祖先なので `p < i`、すなわち `min(i-1,p) = p` であり丸めは効かない。親が無い
場合は `"値v-1"` と書かれ、読み直しでも `-1` に戻る。
-/

namespace Yukito

open OneY OneY.Numeric OneY.RootGeometry

/-- 森 `F` の親を辿り、最初に `pred` を満たした列で止まる探索。
JS の `while (true){ p=tree[p]; if (p<0||小さい) break; }` である。 -/
def chainFind (F : ParentForest) (pred : Nat → Bool) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, c =>
    match F.parent c with
    | none => none
    | some q => if pred q then some q else chainFind F pred fuel q

/-- 止まったら、その列は鎖の上にあり `pred` を満たし、
それより右の鎖の要素はすべて `pred` を満たさない。 -/
theorem chainFind_some {F : ParentForest} {pred : Nat → Bool} :
    ∀ fuel c p, chainFind F pred fuel c = some p →
      F.Ancestor p c ∧ pred p = true ∧
        ∀ q, F.Ancestor q c → p < q → pred q = false := by
  intro fuel
  induction fuel with
  | zero => intro c p h; cases h
  | succ fuel ih =>
    intro c p h
    rw [chainFind] at h
    cases hp : F.parent c with
    | none => rw [hp] at h; cases h
    | some q =>
      rw [hp] at h
      dsimp only at h
      by_cases hq : pred q = true
      · rw [if_pos hq] at h
        injection h with he
        subst he
        refine ⟨ParentForest.Ancestor.direct hp, hq, ?_⟩
        intro q' ha hlt
        have := ancestor_le_of_parent hp ha
        omega
      · rw [if_neg hq] at h
        obtain ⟨ha, hpr, hmax⟩ := ih q p h
        refine ⟨ha.trans (ParentForest.Ancestor.direct hp), hpr, ?_⟩
        intro q' ha' hlt
        rcases ancestor_cases hp ha' with he | ha''
        · rw [he]
          cases hb : pred q with
          | false => rfl
          | true => exact absurd hb hq
        · exact hmax q' ha'' hlt

/-- 燃料が足りていて止まらなかったなら、鎖の上に `pred` を満たす列は無い。 -/
theorem chainFind_none {F : ParentForest} {pred : Nat → Bool} :
    ∀ fuel c, c ≤ fuel → chainFind F pred fuel c = none →
      ∀ p, F.Ancestor p c → pred p = false := by
  intro fuel
  induction fuel with
  | zero =>
    intro c hf _ p ha
    exfalso
    have := ha.lt
    omega
  | succ fuel ih =>
    intro c hf h p ha
    rw [chainFind] at h
    obtain ⟨q, hq⟩ := ancestor_parent_exists' ha
    rw [hq] at h
    dsimp only at h
    by_cases hb : pred q = true
    · rw [if_pos hb] at h; cases h
    · rw [if_neg hb] at h
      have hqf : pred q = false := by
        cases hbb : pred q with
        | false => rfl
        | true => exact absurd hbb hb
      rcases ancestor_cases hq ha with he | ha'
      · rw [he]; exact hqf
      · have := F.parent_left hq
        exact ih q (by omega) h p ha'

/-- 親を持たない列では探索は何も返さない。 -/
theorem chainFind_none_of_no_parent {F : ParentForest} {pred : Nat → Bool} {c : Nat}
    (h : F.parent c = none) : ∀ fuel, chainFind F pred fuel c = none := by
  intro fuel
  cases fuel with
  | zero => rfl
  | succ f => rw [chainFind, h]

/-! ## 燃料

`chainFind` の燃料は鎖の長さぶんあれば足りる。鎖に沿って真に減る量 `m` があれば、
`m c` 以上の燃料で答えは変わらない。山では `m` として「その列の疎配列での添字」を
取る。JS の探索も添字を辿るので、燃料 `prev.size + 1` がそのまま足りる。 -/

/-- 燃料を 1 増やしても答えは変わらない。 -/
theorem chainFind_stable {F : ParentForest} {pred : Nat → Bool} (m : Nat → Nat)
    (hm : ∀ a b, F.parent a = some b → m b < m a) :
    ∀ fuel c, m c ≤ fuel → chainFind F pred (fuel + 1) c = chainFind F pred fuel c := by
  intro fuel
  induction fuel with
  | zero =>
      intro c hc
      have hnp : F.parent c = none := by
        cases hp : F.parent c with
        | none => rfl
        | some q => have := hm c q hp; omega
      exact chainFind_none_of_no_parent hnp (0 + 1)
  | succ fuel ih =>
      intro c hc
      rw [chainFind, chainFind]
      cases hp : F.parent c with
      | none => rfl
      | some q =>
          dsimp only
          by_cases hq : pred q = true
          · rw [if_pos hq, if_pos hq]
          · rw [if_neg hq, if_neg hq]
            have := hm c q hp
            exact ih q (by omega)

/-- 燃料が足りていれば、増やしても答えは変わらない。 -/
theorem chainFind_ge {F : ParentForest} {pred : Nat → Bool} (m : Nat → Nat)
    (hm : ∀ a b, F.parent a = some b → m b < m a) (c fuel : Nat) (h : m c ≤ fuel) :
    ∀ d, chainFind F pred (fuel + d) c = chainFind F pred fuel c := by
  intro d
  induction d with
  | zero => rfl
  | succ d ih =>
      rw [show fuel + (d + 1) = (fuel + d) + 1 from by omega,
        chainFind_stable m hm (fuel + d) c (by omega), ih]

/-- **探索は `restrictedParent` である。** 止まる条件に「値が正」も入れた形。
疎配列では死んだ列がそもそも見えないので、JS 側ではこの条件が自動になる。 -/
theorem chainFind_eq_restrictedParent' (F : ParentForest) (U : Nat → Nat)
    (fuel c : Nat) (hf : c ≤ fuel) :
    chainFind F (fun p => decide (0 < U p) && decide (U p < U c)) fuel c
      = restrictedParent F U c := by
  cases hw : chainFind F (fun p => decide (0 < U p) && decide (U p < U c)) fuel c with
  | none =>
    refine ((restrictedParent_none_iff F U c).mpr ?_).symm
    intro p ha hp
    have h := chainFind_none fuel c hf hw p ha
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not] at h
    rcases h with h | h
    · omega
    · omega
  | some p =>
    obtain ⟨ha, hp, hmax⟩ := chainFind_some fuel c p hw
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
    refine ((restrictedParent_some_iff F U c p).mpr
      ⟨ParentForest.ancestor_to_zeroY ha, hp.1, hp.2, ?_⟩).symm
    intro q hq hqp hqc
    rcases Nat.lt_or_ge p q with hlt | hge
    · have h := hmax q (ParentForest.ancestor_of_zeroY hq) hlt
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not] at h
      rcases h with h | h
      · omega
      · omega
    · exact hge

/-- **探索は `restrictedParent` である。** 値がすべて正なら、
`0 < value p` の条件は自動なので、JS の「値が小さい所で止まる」がそのまま
Phyrion の `restrictedParent` に一致する。 -/
theorem chainFind_eq_restrictedParent (F : ParentForest) (U : Nat → Nat)
    (hpos : ∀ p, 0 < U p) (fuel c : Nat) (hf : c ≤ fuel) :
    chainFind F (fun p => decide (U p < U c)) fuel c = restrictedParent F U c := by
  rw [← chainFind_eq_restrictedParent' F U fuel c hf]
  have he : (fun p => decide (0 < U p) && decide (U p < U c))
      = (fun p => decide (U p < U c)) := by
    funext p
    simp only [decide_eq_true (hpos p), Bool.true_and]
  rw [he]

/-! ## 対角の行

JS の `diagonal` と `diagonalTree` から作られる行が、Phyrion の `rawExtract`
そのものであることを、値と親の両方について述べる。 -/

end Yukito
