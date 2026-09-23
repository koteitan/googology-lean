import Googology.Trans.BMS.TrioRules

/-!
# The 41 rows of the sheet that rules 1–10 do not reproduce

`TrioRulesSheet.lean` checks that on 41 rows of the full sheet
([`tools/omega_alpha_rows.tsv`](https://github.com/koteitan/trio/blob/main/tools/omega_alpha_rows.tsv))
the rule-built matrix differs from the sheet's.  This file records the finite
checks behind the verdicts in [TRIO-SHEET-41.md](TRIO-SHEET-41.md): which side
each row sides with.  All of it is `#guard`s — a calibration, not a theorem.

* **Below `ε₀`** the rule-built matrix is `omegaIndexMatrix`, which
  `TrioStd.lean` and `TrioMono.lean` prove standard and order-preserving.
* **The sheet's matrix is the rule-built matrix of another ordinal**: a label
  typo, or a matrix copied from a neighbouring row.
* **The rules leave their place in the order**: the rule-built matrix is
  below (or above) the matrix of a row whose ordinal is below (above) it,
  while the sheet's matrix sits between its neighbours.
* **The rules give one matrix to two ordinals.**
* **Expansion** (`expandRL 3 N`, which is BM4 expansion on the entries by
  `EntriesR.lean`) of a row the rules and the sheet agree on.

The order on matrices is the lexicographic order of the columns, the order of
`TrioMono.lean`.
-/

namespace Googology.Trans.BMS.TrioRules

open Googology.Notation.ExBuchholz
open Googology.Notation.ExBuchholz.Term
open Googology.Trans.BMS (omegaIndexMatrix opowT expandRL)

/-- The rule-built matrix of a label, `[]` when it does not parse. -/
def ruleOf (s : String) : List (List Nat) := (trioRuleMatrixOf s).getD []

/-! ## Below `ε₀`: `omegaIndexMatrix` decides

`t5` is `5`, so `opowT t5` is `ω^5`. -/

/-- `5` as a term. -/
abbrev t5 : Term := addT t1 (addT t1 (addT t1 (addT t1 t1)))

-- row 2113, labelled `ω^5·3`: the rules give `omegaIndexMatrix (ω^5·3)`;
-- the sheet has `omegaIndexMatrix (ω^5·2)`.
#guard ruleOf "(w^5*3)" = omegaIndexMatrix (addT (opowT t5) (addT (opowT t5) (opowT t5)))
#guard omegaIndexMatrix (addT (opowT t5) (opowT t5))
  = [[0,0,0],[1,1,1],[2,1,1],[2,1,1],[2,1,1],[2,1,1],[2,1,0],[3,2,1],[4,2,1],[4,2,1],[4,2,1],[4,2,1]]
-- row 2131, labelled `ω^ω+ω·2`: the sheet has `omegaIndexMatrix (ω^ω+2)`.
#guard ruleOf "(w^w+w2)" = omegaIndexMatrix (addT (opowT (opowT t1)) (addT (opowT t1) (opowT t1)))
#guard omegaIndexMatrix (addT (opowT (opowT t1)) (addT t1 t1))
  = [[0,0,0],[1,1,1],[2,1,1],[3,0,0],[2,1,0],[3,2,0],[4,3,0]]
-- row 2133, labelled `ω^ω+ω·2` too: the sheet's matrix is not `omegaIndexMatrix (ω^ω+ω·2)`.
#guard omegaIndexMatrix (addT (opowT (opowT t1)) (addT (opowT t1) (opowT t1)))
  ≠ [[0,0,0],[1,1,1],[2,1,1],[3,0,0],[2,1,0],[3,2,1],[3,2,0],[4,3,1]]

/-! ## The sheet's matrix is the rule-built matrix of another ordinal

Each: the sheet's row, the ordinal whose rule-built matrix it is, and that this
ordinal lies between the sheet's neighbouring rows. -/

-- row 2113 (label `ω^5·3`; `ω^5·2` is not otherwise in the sheet)
#guard ruleOf "(w^5*2)" = [[0,0,0],[1,1,1],[2,1,1],[2,1,1],[2,1,1],[2,1,1],[2,1,0],[3,2,1],[4,2,1],[4,2,1],[4,2,1],[4,2,1]]
#guard ruleOf "(w^5+w^2)" < ruleOf "(w^5*2)" ∧ ruleOf "(w^5*2)" < ruleOf "(w^6)"
-- row 2131 (label `ω^ω+ω·2`, repeated at row 2133)
#guard ruleOf "(w^w+2)" = [[0,0,0],[1,1,1],[2,1,1],[3,0,0],[2,1,0],[3,2,0],[4,3,0]]
#guard ruleOf "(w^w+1)" < ruleOf "(w^w+2)" ∧ ruleOf "(w^w+2)" < ruleOf "(w^w+w)"
-- row 2532 (label `Ω^(Ω+1)`, repeated at row 2538)
#guard ruleOf "(W^(w+1))" = [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,0],[2,2,1],[3,2,1],[4,1,0],[4,0,0],[3,2,1],[4,1,0]]
#guard ruleOf "(W^w*w)" < ruleOf "(W^(w+1))" ∧ ruleOf "(W^(w+1))" < ruleOf "(W^(w2))"
-- row 2723 (label `Ω_2·2+Ω`, repeated at row 2724)
#guard ruleOf "(W_2*2+w^2)" = [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,0],[2,2,1],[3,2,1],[4,2,0],[2,2,0],[3,3,1],[4,3,1],[5,2,0],[4,3,0],[5,4,1],[6,4,1],[7,2,0],[6,4,0],[7,5,1],[8,5,1]]
#guard ruleOf "(W_2*2+w)" < ruleOf "(W_2*2+w^2)" ∧ ruleOf "(W_2*2+w^2)" < ruleOf "(W_2*2+W)"
-- row 3452 (label `…+10`: the source reads `psi(W_(W_w*w+W_w+10)`, one parenthesis short)
#guard ruleOf "(W_w*w+W_w+1)" = [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,0],[3,2,1],[4,2,1],[5,1,0],[4,2,1],[4,2,0],[5,3,1],[6,3,1],[7,1,0],[6,3,0],[7,4,0]]
#guard ruleOf "(W_w*w+W_w)" < ruleOf "(W_w*w+W_w+1)" ∧ ruleOf "(W_w*w+W_w+1)" < ruleOf "(W_w*w2)"
-- row 3552 (label `ψ_{Ω_{Ω+1}}(…)`; the row stands between rows 3551 and 3553, inside `ψ_{Ω_{ω+1}}`)
#guard ruleOf "psi_W_(w+1)(W_psi_W_(w+1)(W_(w+1)))" = [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,0],[3,2,1],[4,2,1],[5,1,0],[6,2,1],[7,2,1],[8,1,0],[9,2,0]]
#guard ruleOf "psi_W_(w+1)(W_W)" < ruleOf "psi_W_(w+1)(W_psi_W_(w+1)(W_(w+1)))" ∧ ruleOf "psi_W_(w+1)(W_psi_W_(w+1)(W_(w+1)))" < ruleOf "W_(w+1)"
-- row 3777 (label `Ω_{ω+2}+ω`, repeated at row 3778)
#guard ruleOf "(W_(w+2)+2)" = [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,0],[3,2,1],[4,2,1],[5,2,0],[3,2,0],[4,3,1],[5,3,1],[6,3,0],[4,3,0],[5,4,1],[6,4,1],[7,3,0],[6,4,0],[7,5,0],[8,6,0]]
#guard ruleOf "(W_(w+2)+1)" < ruleOf "(W_(w+2)+2)" ∧ ruleOf "(W_(w+2)+2)" < ruleOf "(W_(w+2)+w)"
-- row 4369 (label `Ω_{ω^3·Ω}`: the source reads `psi(W_(W_(w^3*W))`, one parenthesis short)
#guard ruleOf "(W_(w^3)*W)" = [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[2,1,1],[2,1,0],[3,2,1],[4,2,1],[5,1,0],[4,2,1],[5,1,0]]
#guard ruleOf "(W_(w^3)*w)" < ruleOf "(W_(w^3)*W)" ∧ ruleOf "(W_(w^3)*W)" < ruleOf "(W_(w^3)^2)"
-- row 4384 (label `Ω_{ω^2·2}`, repeated at row 4309)
#guard ruleOf "W_(w^w*2)" = [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,0,0],[2,1,0],[3,2,1],[4,2,1],[5,2,0],[3,2,1],[4,2,1],[5,0,0]]
#guard ruleOf "W_(w^w+w)" < ruleOf "W_(w^w*2)" ∧ ruleOf "W_(w^w*2)" < ruleOf "W_(w^(w+1))"
-- row 3453 (label `Ω_ω·ω+Ω_ω·2`; the sheet leaves out the mark `(1,1,1)`)
#guard ruleOf "(W_w*w+W_w+W)" = [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,0],[3,2,1],[4,2,1],[5,1,0],[4,2,1],[4,2,0],[5,3,1],[6,3,1],[7,1,0],[6,3,0],[7,4,1],[8,4,1],[9,1,0]]
#guard ruleOf "(W_w*w+W_w)" < ruleOf "(W_w*w+W_w+W)" ∧ ruleOf "(W_w*w+W_w+W)" < ruleOf "(W_w*w2)"
-- row 3706 (label `Ω_{ω+1}+Ω_ω^2`)
#guard ruleOf "(W_(w+1)+W_w^W_w)" = [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,0],[3,2,1],[4,2,1],[5,2,0],[3,2,0],[4,3,1],[5,3,1],[6,2,0],[5,3,0],[6,4,1],[7,4,1],[8,1,0],[8,1,0],[1,1,1]]
#guard ruleOf "(W_(w+1)+W_w)" < ruleOf "(W_(w+1)+W_w^W_w)" ∧ ruleOf "(W_(w+1)+W_w^W_w)" < ruleOf "(W_(w+1)*2)"
-- row 3709 (label `Ω_{ω+1}·2+Ω`)
#guard ruleOf "(W_(w+1)*2+w)" = [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,0],[3,2,1],[4,2,1],[5,2,0],[3,2,0],[4,3,1],[5,3,1],[6,2,0],[5,3,0],[6,4,1],[7,4,1],[8,2,0],[7,4,0],[8,5,1]]
#guard ruleOf "(W_(w+1)*2+1)" < ruleOf "(W_(w+1)*2+w)" ∧ ruleOf "(W_(w+1)*2+w)" < ruleOf "(W_(w+1)*3)"
-- row 4303 (label `X^X` with `X = Ω_{ω^2+ω}`)
#guard ruleOf "(W_(w^2+w)^W_(w^2+w)^W_(w^2+w))" = [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[2,1,0],[3,2,1],[4,2,1],[5,2,0],[3,2,1],[4,2,0],[5,3,1],[6,3,1],[7,2,0],[8,2,0],[3,2,1]]
#guard ruleOf "(W_(w^2+w)^2)" < ruleOf "(W_(w^2+w)^W_(w^2+w)^W_(w^2+w))" ∧ ruleOf "(W_(w^2+w)^W_(w^2+w)^W_(w^2+w))" < ruleOf "psi_W_(w^2+w+1)(W_(w^2+w+1))"
-- row 4496 (label `Ω_{Ω+ω}+1`)
#guard ruleOf "(W_(W+w)+w)" = [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,1],[4,1,0],[3,2,0],[4,3,1],[5,3,1],[6,3,0],[4,3,1],[5,3,0],[6,4,1],[7,4,1],[8,3,0],[7,4,0],[8,5,1]]
#guard ruleOf "W_(W+w)" < ruleOf "(W_(W+w)+w)" ∧ ruleOf "(W_(W+w)+w)" < ruleOf "W_(W+w+1)"
-- row 3480 (label `Ω_ω·Ω+Ω_3`)
#guard ruleOf "(W_w*W+W*w)" = [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,0],[3,2,1],[4,2,1],[5,1,0],[4,2,1],[5,1,0],[1,1,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,0],[4,3,1],[5,3,1],[6,2,0],[5,3,1],[6,1,0],[5,3,0],[6,4,1],[7,4,1],[8,1,0],[7,4,1]]
#guard ruleOf "(W_w*W+w)" < ruleOf "(W_w*W+W*w)" ∧ ruleOf "(W_w*W+W*w)" < ruleOf "(W_w*W*w)"

/-! ## The rules leave their place in the order

Each: a row the rules and the sheet agree on whose ordinal is on the other
side, and that the sheet's matrix is between the two agreeing neighbours. -/

-- row 3492, `(W_w*W_2*w)`: the rules put it above `(W_w*W_3)`
#guard ruleOf "(W_w*W_3)" < ruleOf "(W_w*W_2*w)"
#guard ruleOf "(W_w*W_2)" < [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,0],[3,2,1],[4,2,1],[5,1,0],[4,2,1],[5,1,0],[1,1,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,0],[4,3,1],[5,3,1],[6,2,0],[5,3,1],[6,2,0],[2,2,0],[3,3,1],[4,3,1],[5,3,0],[3,3,1],[4,3,0],[5,4,1],[6,4,1],[7,3,0],[6,4,1],[7,2,0],[6,4,1]] ∧ [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,0],[3,2,1],[4,2,1],[5,1,0],[4,2,1],[5,1,0],[1,1,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,0],[4,3,1],[5,3,1],[6,2,0],[5,3,1],[6,2,0],[2,2,0],[3,3,1],[4,3,1],[5,3,0],[3,3,1],[4,3,0],[5,4,1],[6,4,1],[7,3,0],[6,4,1],[7,2,0],[6,4,1]] < ruleOf "(W_w*W_3)"
-- row 4488, `(W_(W+1)+W_W)`: the rules put it below `(W_(W+1)+W_2)`
#guard ruleOf "(W_(W+1)+W_W)" < ruleOf "(W_(W+1)+W_2)"
#guard ruleOf "(W_(W+1)+W_2)" < [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,1],[4,1,0],[3,2,0],[4,3,1],[5,3,1],[6,3,0],[4,3,0],[5,4,1],[6,4,1],[7,3,0],[6,4,0],[7,5,1],[8,5,1],[9,2,0],[2,2,1],[3,2,1],[4,1,0]] ∧ [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,1],[4,1,0],[3,2,0],[4,3,1],[5,3,1],[6,3,0],[4,3,0],[5,4,1],[6,4,1],[7,3,0],[6,4,0],[7,5,1],[8,5,1],[9,2,0],[2,2,1],[3,2,1],[4,1,0]] < ruleOf "(W_(W+1)*2)"
-- row 4490, `(W_(W+1)*w)`: the rules put it below `(W_(W+1)*2)`
#guard ruleOf "(W_(W+1)*w)" < ruleOf "(W_(W+1)*2)"
#guard ruleOf "(W_(W+1)*2)" < [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,1],[4,1,0],[3,2,0],[4,3,1],[5,3,1],[6,3,0],[4,3,0],[5,4,1],[6,4,1],[7,3,0],[6,4,1]] ∧ [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,1],[4,1,0],[3,2,0],[4,3,1],[5,3,1],[6,3,0],[4,3,0],[5,4,1],[6,4,1],[7,3,0],[6,4,1]] < ruleOf "psi_W_(W+2)(W_(W+2))"
-- row 4491, `(W_(W+1)^2)`: the rules put it below `(W_(W+1)*2)`
#guard ruleOf "(W_(W+1)^2)" < ruleOf "(W_(W+1)*2)"
#guard ruleOf "(W_(W+1)*2)" < [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,1],[4,1,0],[3,2,0],[4,3,1],[5,3,1],[6,3,0],[4,3,0],[5,4,1],[6,4,1],[7,3,0],[6,4,1],[7,3,0]] ∧ [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,1],[4,1,0],[3,2,0],[4,3,1],[5,3,1],[6,3,0],[4,3,0],[5,4,1],[6,4,1],[7,3,0],[6,4,1],[7,3,0]] < ruleOf "psi_W_(W+2)(W_(W+2))"
-- row 4508, `W_psi_1(W_2)`: the rules put it below `W_(W^W)`
#guard ruleOf "W_psi_1(W_2)" < ruleOf "W_(W^W)"
#guard ruleOf "W_(W^W)" < [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,1],[4,1,0],[5,2,0]] ∧ [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,1],[4,1,0],[5,2,0]] < ruleOf "W_psi_1(W_W)"
-- row 4609, `(W_W_w+W_w)`: the rules put it above `(W_W_w+W_(w+1))`
#guard ruleOf "(W_W_w+W_(w+1))" < ruleOf "(W_W_w+W_w)"
#guard ruleOf "(W_W_w+W)" < [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,0],[3,2,1],[4,2,1],[5,2,0],[3,2,1],[4,2,1],[5,1,0],[4,2,0],[5,3,1],[6,3,1],[7,2,0],[6,3,0],[7,4,1],[8,4,1],[9,1,0],[1,1,1]] ∧ [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,0],[3,2,1],[4,2,1],[5,2,0],[3,2,1],[4,2,1],[5,1,0],[4,2,0],[5,3,1],[6,3,1],[7,2,0],[6,3,0],[7,4,1],[8,4,1],[9,1,0],[1,1,1]] < ruleOf "(W_W_w+W_(w+1))"
-- row 4613, `(W_W_w*2)`: the rules put it below `(W_W_w+W_W)`
#guard ruleOf "(W_W_w*2)" < ruleOf "(W_W_w+W_W)"
#guard ruleOf "(W_W_w+W_W)" < [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,0],[3,2,1],[4,2,1],[5,2,0],[3,2,1],[4,2,1],[5,1,0],[4,2,0],[5,3,1],[6,3,1],[7,2,0],[6,3,0],[7,4,1],[8,4,1],[9,2,0],[3,2,1],[4,2,1],[5,1,0],[1,1,1]] ∧ [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,0],[3,2,1],[4,2,1],[5,2,0],[3,2,1],[4,2,1],[5,1,0],[4,2,0],[5,3,1],[6,3,1],[7,2,0],[6,3,0],[7,4,1],[8,4,1],[9,2,0],[3,2,1],[4,2,1],[5,1,0],[1,1,1]] < ruleOf "(W_W_w*w)"
-- row 4618, `(W_W_w^2)`: the rules put it below `(W_W_w*W_W)`
#guard ruleOf "(W_W_w^2)" < ruleOf "(W_W_w*W_W)"
#guard ruleOf "(W_W_w*W_W)" < [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,0],[3,2,1],[4,2,1],[5,2,0],[3,2,1],[4,2,1],[5,1,0],[4,2,0],[5,3,1],[6,3,1],[7,2,0],[6,3,1],[7,2,0],[3,2,1],[4,2,1],[5,1,0],[1,1,1]] ∧ [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,0],[3,2,1],[4,2,1],[5,2,0],[3,2,1],[4,2,1],[5,1,0],[4,2,0],[5,3,1],[6,3,1],[7,2,0],[6,3,1],[7,2,0],[3,2,1],[4,2,1],[5,1,0],[1,1,1]] < ruleOf "psi_W_(W_w+1)(W_(W_w+1))"
-- row 4628, `W_psi_W_(w+1)(W_(w+1))`: the rules put it below `W_(W_w^2)`
#guard ruleOf "W_psi_W_(w+1)(W_(w+1))" < ruleOf "W_(W_w^2)"
#guard ruleOf "W_(W_w^2)" < [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,0],[3,2,1],[4,2,1],[5,2,0],[3,2,1],[4,2,1],[5,1,0],[6,2,0]] ∧ [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,0],[3,2,1],[4,2,1],[5,2,0],[3,2,1],[4,2,1],[5,1,0],[6,2,0]] < ruleOf "W_W_(w+1)"
-- row 4674, `W_(psi_W_(w^2+1)(W_(w^2+1)))`: the rules put it below `W_(W_(w^2)^2)`
#guard ruleOf "W_(psi_W_(w^2+1)(W_(w^2+1)))" < ruleOf "W_(W_(w^2)^2)"
#guard ruleOf "W_(W_(w^2)^2)" < [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[2,1,0],[3,2,1],[4,2,1],[5,2,0],[3,2,1],[4,2,1],[5,1,0],[6,2,0]] ∧ [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[2,1,0],[3,2,1],[4,2,1],[5,2,0],[3,2,1],[4,2,1],[5,1,0],[6,2,0]] < ruleOf "W_W_(w^2+1)"
-- row 4762, `W_psi_W_(W+1)(W_(W+1))`: the rules put it below `W_(W_W^2)`
#guard ruleOf "W_psi_W_(W+1)(W_(W+1))" < ruleOf "W_(W_W^2)"
#guard ruleOf "W_(W_W^2)" < [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,1],[4,1,0],[3,2,0],[4,3,1],[5,3,1],[6,3,0],[4,3,1],[5,3,1],[6,2,0],[7,3,0]] ∧ [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,1],[4,1,0],[3,2,0],[4,3,1],[5,3,1],[6,3,0],[4,3,1],[5,3,1],[6,2,0],[7,3,0]] < ruleOf "W_W_(W+1)"
-- row 4769, `W_W_psi_1(W_2)`: the rules put it below `W_W_(W^W)`
#guard ruleOf "W_W_psi_1(W_2)" < ruleOf "W_W_(W^W)"
#guard ruleOf "W_W_(W^W)" < [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,1],[4,1,0],[5,2,0]] ∧ [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,1],[4,1,0],[5,2,0]] < ruleOf "W_W_W_2"

/-! ## The rules give one matrix to two ordinals -/

-- rows 4488
#guard ruleOf "(W_(W+1)+W_W)" = ruleOf "(W_(W+1)+W)"
-- rows 4490, 4491
#guard ruleOf "(W_(W+1)*w)" = ruleOf "(W_(W+1)^2)"
-- rows 4508
#guard ruleOf "W_psi_1(W_2)" = ruleOf "W_(W^W^W)"
-- rows 4609, 4613
#guard ruleOf "(W_W_w+W_w)" = ruleOf "(W_W_w*2)"
-- rows 4613, 4611
#guard ruleOf "(W_W_w*2)" = ruleOf "(W_W_w+W_(w2))"
-- rows 4618
#guard ruleOf "(W_W_w^2)" = ruleOf "(W_W_w*W_w)"
-- rows 4667
#guard ruleOf "(W_W_(w^2)*2)" = ruleOf "(W_W_(w^2)+W_(w^2))"
-- rows 4497
#guard ruleOf "(W_(W+w)*w)" = ruleOf "(W_(W+w)*W)"
-- rows 4744, 4746
#guard ruleOf "(W_W_W+W_W)" = ruleOf "(W_W_W+W_W_2)"
-- rows 4745, 4747
#guard ruleOf "(W_W_W+W_(W+1))" = ruleOf "(W_W_W*2)"
-- rows 4750, 4752
#guard ruleOf "(W_W_W*W_W)" = ruleOf "(W_W_W*W_W_2)"
-- rows 4751, 4753
#guard ruleOf "(W_W_W*W_(W+1))" = ruleOf "(W_W_W^2)"

/-! ## Expansion

`expandRL 3 N` keeps `N + 1` copies of the bad part, as yaBMS's `[N]` does. -/

-- `(ω^6)[1]` is the sheet's row 2113 and `(ω^6)[2]` the rule-built `ω^5·3`.
#guard expandRL 3 1 (ruleOf "(w^6)") = [[0,0,0],[1,1,1],[2,1,1],[2,1,1],[2,1,1],[2,1,1],[2,1,0],[3,2,1],[4,2,1],[4,2,1],[4,2,1],[4,2,1]]
#guard expandRL 3 2 (ruleOf "(w^6)") = ruleOf "(w^5*3)"
-- `(ω^ω+ω^2)[1]` is the rule-built `ω^ω+ω·2`.
#guard expandRL 3 1 (ruleOf "(w^w+w^2)") = ruleOf "(w^w+w2)"
-- `(Ω_v·ω)[1] = Ω_v + Ω_{u+1}` when `v = Ω_u`, on rows the rules and the sheet agree on …
#guard expandRL 3 1 (ruleOf "(W_W*w)") = ruleOf "(W_W+W_2)"
#guard expandRL 3 1 (ruleOf "(W_W_w*w)") = ruleOf "(W_W_w+W_(w+1))"
#guard expandRL 3 1 (ruleOf "(W_W_(w^2)*w)") = ruleOf "(W_W_(w^2)+W_(w^2+1))"
-- … and at `u = Ω` it gives the sheet's row 4745, `Ω_{Ω_Ω}+Ω_{Ω+1}`, not the rules' matrix.
#guard expandRL 3 1 (ruleOf "(W_W_W*w)") = [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,1],[4,1,0],[3,2,0],[4,3,1],[5,3,1],[6,3,0],[4,3,1],[5,3,1],[6,2,0],[5,3,0],[6,4,1],[7,4,1],[8,3,0],[7,4,0],[8,5,1],[9,5,1],[10,3,0]]
#guard expandRL 3 1 (ruleOf "(W_W_W*w)") ≠ ruleOf "(W_W_W+W_(W+1))"
-- `(Ω_ω·ω)[1] = Ω_ω+Ω`, and `(Ω_ω·ω·2)[1]` is the sheet's row 3453: `Ω_ω·ω+Ω_ω+Ω`.
#guard expandRL 3 1 (ruleOf "(W_w*w)") = ruleOf "(W_w+W)"
#guard expandRL 3 1 (ruleOf "(W_w*w2)") = [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,0],[3,2,1],[4,2,1],[5,1,0],[4,2,1],[4,2,0],[5,3,1],[6,3,1],[7,1,0],[6,3,0],[7,4,1],[8,4,1],[9,1,0]]
-- `M(Ω_{Ω_ω})[0] = M(Ω_Ω)` and `[1] = M(Ω_{Ω_2})`: the trailing `(1,1,1)` is the mark.
#guard expandRL 3 0 (ruleOf "W_W_w") = ruleOf "W_W"
#guard expandRL 3 1 (ruleOf "W_W_w") = ruleOf "W_W_2"
-- The sheet's row 4496 expands at `[1]` to the rule-built `Ω_{Ω+ω}+1`,
-- and the sheet's row 4497 at `[0]` to the rule-built `Ω_{Ω+ω}·ω`.
#guard expandRL 3 1 [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,1],[4,1,0],[3,2,0],[4,3,1],[5,3,1],[6,3,0],[4,3,1],[5,3,0],[6,4,1],[7,4,1],[8,3,0],[7,4,0],[8,5,1]] = ruleOf "(W_(W+w)+1)"
#guard expandRL 3 0 [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,1],[4,1,0],[3,2,0],[4,3,1],[5,3,1],[6,3,0],[4,3,1],[5,3,0],[6,4,1],[7,4,1],[8,3,0],[7,4,1]] = ruleOf "(W_(W+w)*w)"

end Googology.Trans.BMS.TrioRules
