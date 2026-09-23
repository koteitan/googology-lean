/-
Ported verbatim from koteitan/trio, `lean/Trio.lean`:
https://github.com/koteitan/trio/blob/74ef7af49eefaef06ce4c9b57c02ecdcb9975606/lean/Trio.lean
Only the module names of the imports and the namespace (`TRIO` →
`Googology.Trans.BMS.TrioCof`) were changed. The bridge to this library's
Bashicu matrices is `Googology/Trans/BMS/TrioCofinal.lean`.
-/
/-
トリオ数列システム（3 行バシク行列）の定義。

展開規則は BM4（ユーザーブログ:Koteitan/バシク行列の数式的定義 —
バシク行列システム(BM4) の節）に従う。

    B_xy^(a) = S_(r+x)y + a Δ_y A_xy
    Δ_y      = S_(X-1)y - S_ry   (y < t) / 0 (y ≥ t)
    A_xy     = 1 (バッドルート r が行 y の木で列 r+x の祖先) / 0 (それ以外)
    t        = max{y | S_(X-1)y > 0}
    r        = P_t(X-1)
    P_y(x)   = 行 y の親（候補は行 y-1 の木での x の祖先に限る: UBI）

対象は一旦 z < 2 の断片とする。生成元は z 頭打ち対角列
`D_v = (0,0,0)(1,1,1)(2,2,1)...(v,v,1)`。これは完全な BM4 では
`(0,0,0)(1,1,1)(2,2,2)[v]` に等しく（tools/verify_trio.py で検査）、
断片は「3 列のトリオ対角列より真に下」の全体にあたる。展開は行 2 の値を
変えないから z < 2 は展開で閉じている。

2 行の形式化 https://github.com/koteitan/yet-another-pss-proof/blob/main/lean/Pss.lean と同じ設計。
-/
import Mathlib.Logic.Relation
import Mathlib.Data.List.Basic

namespace Googology.Trans.BMS.TrioCof

/-- A trio sequence: a list of triples of naturals. -/
abbrev TrioSeq := List (ℕ × ℕ × ℕ)

/-- `entry M i j` = `M_{i,j}`: the `i`-th row of the `j`-th column. -/
def entry (M : TrioSeq) (i j : ℕ) : ℕ :=
  let c := M.getD j (0, 0, 0)
  if i = 0 then c.1 else if i = 1 then c.2.1 else c.2.2

/-! ### 親子関係（UBI: 行 y の親候補は行 y-1 の木での祖先に限る） -/

/-- Row-0 "next" relation: nearest preceding column strictly lower in row 0,
with no dip in between. -/
def nextrel0 (M : TrioSeq) (j0 j1 : ℕ) : Prop :=
  j0 < M.length ∧ j1 < M.length ∧ j0 < j1 ∧
  entry M 0 j0 < entry M 0 j1 ∧
  (∀ j, j0 < j ∧ j < j1 → entry M 0 j1 ≤ entry M 0 j)

/-- Row-0 ancestry: reflexive-transitive closure of `nextrel0`. -/
def le0 (M : TrioSeq) (j0 j1 : ℕ) : Prop :=
  j0 < M.length ∧ j1 < M.length ∧ Relation.ReflTransGen (nextrel0 M) j0 j1

/-- Row-1 "next" relation (candidates restricted to row-0 ancestors). -/
def nextrel1 (M : TrioSeq) (j0 j1 : ℕ) : Prop :=
  j0 < M.length ∧ j1 < M.length ∧ j0 < j1 ∧
  entry M 1 j0 < entry M 1 j1 ∧
  le0 M j0 j1 ∧
  (∀ j, j0 < j ∧ le0 M j j1 → entry M 1 j1 ≤ entry M 1 j)

/-- Row-1 ancestry: reflexive-transitive closure of `nextrel1`. -/
def le1 (M : TrioSeq) (j0 j1 : ℕ) : Prop :=
  j0 < M.length ∧ j1 < M.length ∧ Relation.ReflTransGen (nextrel1 M) j0 j1

/-- Row-2 "next" relation (candidates restricted to row-1 ancestors). -/
def nextrel2 (M : TrioSeq) (j0 j1 : ℕ) : Prop :=
  j0 < M.length ∧ j1 < M.length ∧ j0 < j1 ∧
  entry M 2 j0 < entry M 2 j1 ∧
  le1 M j0 j1 ∧
  (∀ j, j0 < j ∧ le1 M j j1 → entry M 2 j1 ≤ entry M 2 j)

/-- Row-indexed "next" relation. -/
def nextR (M : TrioSeq) (i j0 j1 : ℕ) : Prop :=
  if i = 0 then nextrel0 M j0 j1
  else if i = 1 then nextrel1 M j0 j1
  else nextrel2 M j0 j1

/-! ### 前者 -/

/-- Drop the last column (identity on sequences of length ≤ 1). -/
def Pred (M : TrioSeq) : TrioSeq :=
  if M.length ≤ 1 then M else M.dropLast

/-! ### 基本列 -/

/-- 非零最下行 `t`: the row used to find the parent of column `j1`. -/
def srow (M : TrioSeq) (j1 : ℕ) : ℕ :=
  if 0 < entry M 2 j1 then 2 else if 0 < entry M 1 j1 then 1 else 0

/-- The last column has a (unique) parent in row `i`. -/
def hasParent (M : TrioSeq) (i j1 : ℕ) : Prop :=
  ∃! j0, nextR M i j0 j1

/-- The parent of `j1` in row `i` (Hilbert choice under the `hasParent` guard). -/
noncomputable def parent (M : TrioSeq) (i j1 : ℕ) : ℕ :=
  Classical.epsilon fun j0 => nextR M i j0 j1

open Classical in
/-- The fundamental sequence `M[n]` (BM4 expansion with copy count `n`).

行 y の上昇は、バッドルート `j0` が行 y の木でその列の祖先であるときに
限って乗る（上昇行列 `A_xy`）。行 2 は上昇しない（`Δ_y = 0` for `y ≥ t`,
`t ≤ 2`）。 -/
noncomputable def oper (M : TrioSeq) (n : ℕ) : TrioSeq :=
  let j1 := M.length - 1
  if j1 = 0 then M
  else if entry M 0 j1 = 0 ∧ entry M 1 j1 = 0 ∧ entry M 2 j1 = 0 then Pred M
  else
    let i1 := srow M j1
    if ¬ hasParent M i1 j1 then Pred M
    else
      let j0 := parent M i1 j1
      let d0 := if 0 < i1 then entry M 0 j1 - entry M 0 j0 else 0
      let d1 := if 1 < i1 then entry M 1 j1 - entry M 1 j0 else 0
      M.take j0 ++
        (List.range n).flatMap fun k =>
          (List.range' j0 (j1 - j0)).map fun j =>
            (entry M 0 j + (if le0 M j0 j then k * d0 else 0),
             entry M 1 j + (if le1 M j0 j then k * d1 else 0),
             entry M 2 j)

@[inherit_doc] notation:max M "⟦" n "⟧" => oper M n

/-! ### 標準形と展開 -/

/-- z 頭打ち対角列 `((j, j, min j 1))_{j=a}^{b}`. -/
def diagSeqT (a b : ℕ) : TrioSeq :=
  (List.range' a (b + 1 - a)).map fun j => (j, j, min j 1)

/-- The least set of *standard forms* of the `z < 2` fragment: trio sequences
reachable from a capped diagonal `diagSeqT 0 v` by the expansion `M ↦ M⟦n⟧`
(`n ≥ 1`). -/
inductive ST_TS : TrioSeq → Prop where
  | diag (v : ℕ) : ST_TS (diagSeqT 0 v)
  | oper {M : TrioSeq} {n : ℕ} : ST_TS M → 1 ≤ n → ST_TS (M⟦n⟧)

/-- One expansion step of the system. -/
inductive step : TrioSeq → TrioSeq → Prop where
  | step_oper {M : TrioSeq} {n : ℕ} :
      1 < M.length → 1 ≤ n → step M (M⟦n⟧)

end Googology.Trans.BMS.TrioCof
