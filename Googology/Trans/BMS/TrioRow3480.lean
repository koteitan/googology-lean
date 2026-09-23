import Googology.Trans.BMS.TrioSheet41
import Googology.Trans.BMS.TrioCofPsi

/-!
# Row 3480 of the trio sheet: `ψ_0(Ω_{Ω_ω·Ω+Ω_3})`

Row 3480 of
[`tools/omega_alpha_rows.tsv`](https://github.com/koteitan/trio/blob/main/tools/omega_alpha_rows.tsv)
is labelled `Ω_ω·Ω+Ω_3`.  Its matrix is the rule-built matrix of `Ω_ω·Ω+Ω·ω`, and
the rule-built matrix of the label ends in the leaf `(8,3,0)`, which is not a
standard form.  [TRIO-ROW-3480.md](TRIO-ROW-3480.md) decides the row: neither
side is right, and `M(Ω_ω·Ω+Ω_3)` is `c2` below.

Write `β = Ω_ω·Ω` and `w2` for the rule-built `M(β+Ω_2)`.

* `c2 = w2 ++ storey`, where `storey` is the part of `w2` after `M(β)`, raised
  by `(1,1,0)`.  The one exception is the column `(6,1,0)`: its row-1 parent is
  the root `(0,0,0)`, so it keeps its row-1 entry and becomes `(7,1,0)`, as a
  BM4 copy does.  `M(Ω_ω+Ω_3)`, on which the sheet and the rules agree, is
  built from `M(Ω_ω+Ω_2)` in the same way.
* `c2` is standard: `trioStdL_c2`.  The proof follows 64 expansion steps from
  the generator `(0,0,0)(1,1,1)(2,2,1)`.  After each step it keeps only a
  prefix, which is again standard (`trioStdL_prefix`).
* `c2 = lM[1]` with `lM[0] = w2`, where `lM = w2 ++ (2,2,1)` is `M(β+Ω_ω)`.
  This is the pattern of `M(Ω_ω·2)[n] = M(Ω_ω+Ω_{n+1})` and
  `M(Ω_ω^2)[n] = M(Ω_ω·Ω_{n+1})`, which hold on rows the rules and the sheet
  agree on.  Here the index is one higher, because `w2`'s leaf names the root
  of the storey.
* The rules read `w2 ++ (7,4,1)` as `β+Ω_2·ω`, which would put it below
  `M(β+Ω_3)`.  But `M(β·ω)[1] = w2 ++ (7,4,1)(8,1,0)`, and on agreeing rows
  `(X·ω)[1] = X·2` whenever `X` ends in a factor `Ω_v` with `v` a successor.
  So `w2 ++ (7,4,1)(8,1,0)` is `M(β·2)`, and `w2 ++ (7,4,1)` is `β+Ω_ω·ω`,
  which is above `M(β+Ω_ω)`.

All `#guard`s are finite checks.  The theorems are `trioStdL_lM` and
`trioStdL_c2`.
-/

namespace Googology.Trans.BMS.TrioRules

open Googology.Trans.BMS (expandRL)
open Googology.Trans.BMS.TrioCofinal (TrioStdL trioGen)

/-! ## The matrices -/

/-- `M(Ω_ω·Ω)`, the sheet's row 3460 (the rules agree). -/
abbrev mBeta : List (List Nat) :=
  [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,0],[3,2,1],[4,2,1],[5,1,0],[4,2,1],[5,1,0]]

/-- The rule-built `M(Ω_ω·Ω+Ω_2)`. -/
abbrev w2 : List (List Nat) :=
  mBeta ++ [[1,1,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,0],[4,3,1],[5,3,1],[6,2,0],[5,3,1],[6,1,0],
    [5,3,0],[6,4,1],[7,4,1],[8,2,0]]

/-- The second storey: `w2` after `M(Ω_ω·Ω)`, raised by `(1,1,0)`, except
`(6,1,0)`, whose row-1 parent is the root `(0,0,0)`. -/
abbrev storey2 : List (List Nat) :=
  [[2,2,0],[3,3,1],[4,3,1],[5,3,0],[3,3,1],[4,3,0],[5,4,1],[6,4,1],[7,3,0],[6,4,1],[7,1,0],
    [6,4,0],[7,5,1],[8,5,1],[9,3,0]]

/-- `M(Ω_ω·Ω+Ω_3)`, the verdict for row 3480. -/
abbrev c2 : List (List Nat) := w2 ++ storey2

/-- `M(Ω_ω·Ω+Ω_ω)`: `w2` followed by the mark `(2,2,1)` one storey up. -/
abbrev lM : List (List Nat) := w2 ++ [[2,2,1]]

/-- The sheet's matrix of row 3480. -/
abbrev sheet3480 : List (List Nat) :=
  [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,0],[3,2,1],[4,2,1],[5,1,0],[4,2,1],[5,1,0],
    [1,1,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,0],[4,3,1],[5,3,1],[6,2,0],[5,3,1],[6,1,0],
    [5,3,0],[6,4,1],[7,4,1],[8,1,0],[7,4,1]]

#guard ruleOf "(W_w*W)" = mBeta
#guard ruleOf "(W_w*W+W_2)" = w2
-- the sheet's matrix is the rule-built `M(Ω_ω·Ω+Ω·ω)`
#guard ruleOf "(W_w*W+W*w)" = sheet3480
-- the rule-built matrix of the label: `w2` with the leaf `(8,3,0)`, not standard (yaBMS)
#guard ruleOf "(W_w*W+W_3)" = mBeta ++ [[1,1,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,0],[4,3,1],
    [5,3,1],[6,2,0],[5,3,1],[6,1,0],[5,3,0],[6,4,1],[7,4,1],[8,3,0]]
#guard c2 ≠ sheet3480 ∧ c2 ≠ ruleOf "(W_w*W+W_3)"

/-! ## `c2` and `lM` are standard -/

/-- One step: expand, then drop the last `s.2` columns. -/
def stepP (l : List (List Nat)) (s : Nat × Nat) : List (List Nat) :=
  (expandRL 3 s.1 l).take ((expandRL 3 s.1 l).length - s.2)

/-- A run of steps. -/
def runP (l : List (List Nat)) (ss : List (Nat × Nat)) : List (List Nat) :=
  ss.foldl stepP l

theorem trioStdL_stepP {l : List (List Nat)} (h : TrioStdL l) (s : Nat × Nat) :
    TrioStdL (stepP l s) := by
  have h1 := TrioStdL.step s.1 h
  rw [← List.take_append_drop ((expandRL 3 s.1 l).length - s.2) (expandRL 3 s.1 l)] at h1
  exact TrioCofPsi.trioStdL_prefix _ _ h1

theorem trioStdL_runP : ∀ (ss : List (Nat × Nat)) {l : List (List Nat)},
    TrioStdL l → TrioStdL (runP l ss)
  | [], _, h => h
  | s :: ss, _, h => trioStdL_runP ss (trioStdL_stepP h s)

/-- The steps from `trioGen 2 = (0,0,0)(1,1,1)(2,2,1)` to `lM`: at each step the
least `n` with `A[n] ≥ lM`, then the shortest prefix that is still `≥ lM`. -/
def pathLM : List (Nat × Nat) :=
  [(1, 1), (2, 0), (1, 1), (1, 0), (1, 0), (1, 3), (1, 0), (1, 3), (1, 1), (1, 3), (1, 3),
   (1, 1), (1, 1), (1, 1), (1, 0), (1, 0), (1, 8), (1, 0), (1, 8), (2, 1), (1, 5), (1, 5),
   (1, 10), (1, 4), (1, 5), (1, 5), (1, 10), (1, 5), (1, 10), (1, 6), (1, 0), (1, 8), (1, 0),
   (1, 0), (1, 21), (1, 0), (1, 21), (1, 1), (1, 1), (1, 3), (1, 3), (1, 9), (1, 14), (1, 25),
   (1, 2), (1, 3), (1, 3), (1, 9), (1, 14), (1, 25), (1, 3), (1, 9), (1, 14), (1, 25), (1, 8),
   (1, 9), (1, 9), (1, 14), (1, 25), (1, 9), (1, 14), (1, 25), (1, 10)]

theorem runP_pathLM : runP (trioGen 2) pathLM = lM := by decide +kernel

/-- `M(Ω_ω·Ω+Ω_ω)` is a standard trio sequence. -/
theorem trioStdL_lM : TrioStdL lM := by
  have := trioStdL_runP pathLM (TrioStdL.gen 2)
  rwa [runP_pathLM] at this

theorem expandRL_lM_one : expandRL 3 1 lM = c2 := by decide +kernel

/-- `M(Ω_ω·Ω+Ω_3)` is a standard trio sequence. -/
theorem trioStdL_c2 : TrioStdL c2 := by
  have := TrioStdL.step 1 trioStdL_lM
  rwa [expandRL_lM_one] at this

/-! ## Expansion: `lM[n] = M(β+Ω_{n+2})`

The same pattern on agreeing rows: a final mark `(1,1,1)` steps the level of
the last `Ω` by one per copy. -/

#guard expandRL 3 0 lM = w2
#guard expandRL 3 1 lM = c2
#guard expandRL 3 0 (ruleOf "(W_w*2)") = ruleOf "(W_w+W)"
#guard expandRL 3 1 (ruleOf "(W_w*2)") = ruleOf "(W_w+W_2)"
#guard expandRL 3 2 (ruleOf "(W_w*2)") = ruleOf "(W_w+W_3)"
#guard expandRL 3 0 (ruleOf "(W_w^2)") = ruleOf "(W_w*W)"
#guard expandRL 3 1 (ruleOf "(W_w^2)") = ruleOf "(W_w*W_2)"
#guard expandRL 3 2 (ruleOf "(W_w^2)") = ruleOf "(W_w*W_3)"
-- `M(Ω_ω+Ω_3)` (row 3377, agreeing) is `M(Ω_ω+Ω_2)` followed by its own storey raised
-- by `(1,1,0)`: the construction of `c2`
#guard ruleOf "(W_w+W_3)" = ruleOf "(W_w+W_2)" ++
  [[2,2,0],[3,3,1],[4,3,1],[5,3,0],[3,3,1],[4,3,0],[5,4,1],[6,4,1],[7,3,0],[6,4,0],[7,5,1],
   [8,5,1],[9,3,0]]
#guard (ruleOf "(W_w+W_2)").drop 13 = [[1,1,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,0],[4,3,1],
  [5,3,1],[6,2,0],[5,3,0],[6,4,1],[7,4,1],[8,2,0]]

/-! ## `(X·ω)[1] = X·2`: why `w2 ++ (7,4,1)` is not `β+Ω_2·ω`

On agreeing rows, when `X` ends in a factor `Ω_v` with `v` a successor, the
first expansion of `X·ω` is `X·2`.  When the last factor is `Ω_ω`, it drops
to `Ω` (`Ω_ω·ω`, `Ω_ω^2·ω`), and a leading `Ω_ω` stays (`Ω_ω^2·ω`). -/

#guard expandRL 3 1 (ruleOf "(W_2*W*w)") = ruleOf "(W_2*W2)"
#guard expandRL 3 1 (ruleOf "(W^2*w)") = ruleOf "(W^2*2)"
#guard expandRL 3 1 (ruleOf "(W_2^2*w)") = ruleOf "(W_2^2*2)"
#guard expandRL 3 1 (ruleOf "(W_(w+1)*w)") = ruleOf "(W_(w+1)*2)"
#guard expandRL 3 1 (ruleOf "(W_w*w)") = ruleOf "(W_w+W)"
#guard expandRL 3 1 (ruleOf "(W_w^2*w)") = ruleOf "(W_w^2+W_w*W)"
-- `M(β·ω)` (row 3483, agreeing): its first expansion is `w2 ++ (7,4,1)(8,1,0)`, so that is `M(β·2)`
#guard expandRL 3 1 (ruleOf "(W_w*W*w)") = w2 ++ [[7,4,1],[8,1,0]]
-- … and the rules call `w2 ++ (7,4,1)` `β+Ω_2·ω`
#guard ruleOf "(W_w*W+W_2*w)" = w2 ++ [[7,4,1]]

/-! ## Order

The agreeing neighbours of the label are row 3479 (`β+ω`) and row 3483
(`β·ω`).  `c2` is strictly between them, so it is on the right side of all 744
agreeing rows, which the note checks one by one. -/

#guard ruleOf "(W_w*W+w)" < c2 ∧ c2 < ruleOf "(W_w*W*w)"
-- `β+Ω < β+Ω·ω < β+Ω_2 < β+Ω_3 < β+Ω_ω < β+Ω_ω·ω < β·2`
#guard ruleOf "(W_w*W+W)" < sheet3480 ∧ sheet3480 < w2 ∧ w2 < c2 ∧ c2 < lM
#guard lM < w2 ++ [[7,4,1]] ∧ w2 ++ [[7,4,1]] < w2 ++ [[7,4,1],[8,1,0]]
-- `β+Ω_2+1`, `β+Ω_2·ω`, `β+Ω_2·Ω` and `β+Ω_2^2` fit between `w2` and `c2`: the second
-- storey with the leaf `(9,2,0)`, then `+1`, `·ω`, `·Ω`, `·Ω_2`
#guard w2 < w2 ++ storey2.dropLast ++ [[9,2,0],[8,5,0],[9,6,0]]
#guard w2 ++ storey2.dropLast ++ [[9,2,0],[8,5,0],[9,6,0]] < w2 ++ storey2.dropLast ++ [[9,2,0],[8,5,1]]
#guard w2 ++ storey2.dropLast ++ [[9,2,0],[8,5,1]] < w2 ++ storey2.dropLast ++ [[9,2,0],[8,5,1],[9,1,0]]
#guard w2 ++ storey2.dropLast ++ [[9,2,0],[8,5,1],[9,1,0]] < w2 ++ storey2.dropLast ++ [[9,2,0],[8,5,1],[9,2,0]]
#guard w2 ++ storey2.dropLast ++ [[9,2,0],[8,5,1],[9,2,0]] < c2

end Googology.Trans.BMS.TrioRules
