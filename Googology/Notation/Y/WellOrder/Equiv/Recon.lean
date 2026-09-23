/-
From koteitan, 1y-expand-equiv, `Equiv/Recon.lean`
(https://github.com/koteitan/1y-expand-equiv, revision c9a5368a09ceb62ec671a6c3447a4719d035dfc0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.Y.WellOrder.`; the transcription `Equiv/Yukito.lean` is replaced by
`Googology.Notation.Y.Yukito` (opened below).
This file is part of googology-lean and is licensed under its MIT license.
-/
import Googology.Notation.Y.WellOrder.Equiv.BadRoot
import Googology.Notation.Y.WellOrder.OneY.Reconstruction

open Googology.Notation.Y

/-!
# 値の復元

JS は展開後の山の値を、下の行から

```js
result[i][j].value = result[i][result[i][j].parentIndex].value + result[i+1][k].value;
```

で埋める。すなわち

```
V r c = V r (行 r での c の親) + V (r+1) c
```

である。Phyrion 側の `Reconstruction.value` はこれを展開した閉じた式

```
value M top r c = if r ≤ height c then top c + Σ_{u=r}^{height c − 1}（行 u での親の値）
                  else 0
```

を使う。本ファイルは、**差分の関係を満たす値はこの式に一致する**ことを示す。森の形に
よらないので、コピー層の具体形を決める前に片付けられる。
-/

namespace Yukito

open OneY OneY.RootGeometry

/-- 行 `r` を 1 つ剥がす。 -/
theorem recon_step (M : RowMountain) (top : Nat → Nat) (r c : Nat) (h : r < M.height c) :
    Reconstruction.value M top r c
      = Reconstruction.parentValue M top r c + Reconstruction.value M top (r + 1) c := by
  rw [Reconstruction.value_eq M top r c, Reconstruction.value_eq M top (r + 1) c,
    if_pos (by omega), if_pos (by omega),
    show M.height c - r = (M.height c - (r + 1)) + 1 from by omega,
    List.range'_succ]
  simp only [List.map_cons, List.sum_cons]
  omega

/-- 頂では復元値は `top`。 -/
theorem recon_top (M : RowMountain) (top : Nat → Nat) (c : Nat) :
    Reconstruction.value M top (M.height c) c = top c := by
  rw [Reconstruction.value_eq, if_pos (Nat.le_refl _),
    show M.height c - M.height c = 0 from by omega]
  simp

/-- 頂より上では 0。 -/
theorem recon_above (M : RowMountain) (top : Nat → Nat) (r c : Nat)
    (h : M.height c < r) : Reconstruction.value M top r c = 0 := by
  rw [Reconstruction.value_eq, if_neg (by omega)]

/-- **前半だけでの版。** 列 `W` 未満についてだけ仮定があれば、そこでの値は一致する。
親は真に左へ動くので、帰納の中で使う列はすべて `W` 未満に留まる。 -/
theorem value_of_diff_prefix (M : RowMountain) (top : Nat → Nat) (V : Nat → Nat → Nat)
    (W : Nat)
    (hstep : ∀ r c p, c < W → (M.row r).parent c = some p → V r c = V r p + V (r + 1) c)
    (htop : ∀ c, c < W → V (M.height c) c = top c)
    (hzero : ∀ r c, c < W → M.height c < r → V r c = 0) :
    ∀ c, c < W → ∀ r, V r c = Reconstruction.value M top r c := by
  intro c
  induction c using Nat.strongRecOn with
  | ind c ih =>
    intro hcW r
    rcases Nat.lt_or_ge (M.height c) r with hgt | hle
    · rw [hzero r c hcW hgt, recon_above M top r c hgt]
    · obtain ⟨d, hd⟩ : ∃ d, M.height c - r = d := ⟨_, rfl⟩
      induction d generalizing r with
      | zero =>
          have hre : r = M.height c := by omega
          rw [hre, htop c hcW, recon_top]
      | succ d ihd =>
          have hlt : r < M.height c := by omega
          obtain ⟨p, hp⟩ := M.parent_exists r c hlt
          have hpc : p < c := (M.row r).parent_left hp
          rw [hstep r c p hcW hp, ih p hpc (by omega) r, recon_step M top r c hlt]
          have hnext := ihd (r + 1) (by omega) (by omega)
          rw [hnext]
          simp only [Reconstruction.parentValue, hp]

end Yukito
