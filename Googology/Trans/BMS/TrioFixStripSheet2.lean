import Googology.Trans.BMS.TrioFixStrip
import Googology.Trans.BMS.TrioRulesAllSheet
import Googology.Trans.BMS.TrioTree

/-!
# Patch "strip": the checks, continued

See `TrioFixStripSheet.lean` for the summary.  Parts 2–8: Fixes A–D, Fix E (`TrioRules3Sheet.lean`), Fix N
(`TrioRulesNonLastSheet.lean`), the interactions with rules 1–10 and the single-fix
versions, where Fix E and Fix N meet, one step against rules 1–10, and the patch's own
checks (the corpus of 1,225 labels unchanged; `ω^{ε₀·ω}`; `β`).
All of it is `#guard`s: a calibration, not a theorem.
-/

namespace Googology.Trans.BMS.TrioFixStrip

open Googology.Notation.ExBuchholz
open Googology.Notation.ExBuchholz.Term
open Googology.Trans.BMS.TrioRules
open Googology.Trans.BMS.TrioRules2
open Googology.Trans.BMS.TrioRules3
open Googology.Trans.BMS.TrioRulesNL
open Googology.Trans.BMS.TrioRulesAll
open Googology.Trans.BMS (expandRL te0)
open Googology.Trans.BMS.TrioFixOfTerm (ofTermFix trioMatrixLFix summandFix tα tβ)
open Googology.Trans.BMS.TrioTree (smallFrag)

def chosenDataSt : Array (Od × List (List Nat)) :=
  (chosen.map fun s => ((parse s).getD [], stOf s)).toArray
/-! ## Part 2: the guards of `TrioRules2.lean` (Fixes A–D, one row each) -/

-- Fix A, row 4508 `Ω_{ψ_1(Ω_2)}`: the kept column `(5,2,0)`.
#guard trioRuleMatrixOfSt "W_psi_1(W_2)" = some [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,1],[4,1,0],[5,2,0]]
-- Fix B, row 4747 `Ω_{Ω_Ω}·2`: leaf 3, then the sub-units at heights 3 and 2.
#guard trioRuleMatrixOfSt "(W_W_W*2)" = some [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,1],[4,1,0],[3,2,0],[4,3,1],[5,3,1],[6,3,0],[4,3,1],[5,3,1],[6,2,0],[5,3,0],[6,4,1],[7,4,1],[8,3,0],[7,4,0],[8,5,1],[9,5,1],[10,3,0],[4,3,1],[5,3,1],[6,2,0],[2,2,1],[3,2,1],[4,1,0]]
-- Fix C, row 4490 `Ω_{Ω+1}·ω`: the digit `(6,4,1)` of `+1`.
#guard trioRuleMatrixOfSt "(W_(W+1)*w)" = some [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,1],[4,1,0],[3,2,0],[4,3,1],[5,3,1],[6,3,0],[4,3,0],[5,4,1],[6,4,1],[7,3,0],[6,4,1]]
-- Fix D, row 3492 `Ω_ω·Ω_2·ω`: two storeys, then the digit.
#guard trioRuleMatrixOfSt "(W_w*W_2*w)" = some [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,0],[3,2,1],[4,2,1],[5,1,0],[4,2,1],[5,1,0],[1,1,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,0],[4,3,1],[5,3,1],[6,2,0],[5,3,1],[6,2,0],[2,2,0],[3,3,1],[4,3,1],[5,3,0],[3,3,1],[4,3,0],[5,4,1],[6,4,1],[7,3,0],[6,4,1],[7,2,0],[6,4,1]]

/-! ## Part 3: `TrioRules3Sheet.lean` and the guards of `TrioRules3.lean` (Fix E) -/

-- The 817 distinct labels: `TrioRules3`'s matrix everywhere, `TrioRules2`'s except
-- on the printed label of row 3552.
#guard allLabels.all fun s => trioRuleMatrixOfSt s == trioRuleMatrixOf3 s
#guard (allLabels.filter (· != printed3552)).all fun s => trioRuleMatrixOfSt s == trioRuleMatrixOf2 s
#guard trioRuleMatrixOfSt printed3552 != trioRuleMatrixOf2 printed3552

/-- The 783 labels and the printed label of row 3552, with the merged matrices. -/
def chosenDataSt3 : Array (Od × List (List Nat)) :=
  ((chosen ++ [printed3552]).map fun s => ((parse s).getD [], stOf s)).toArray

#guard chosenDataSt3.size = 784
#guard chosenDataSt3.all fun p => !p.1.isEmpty && !p.2.isEmpty
#guard orderDisagreements chosenDataSt3 = 0

#guard stOf printed3552 = [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,1],[4,1,0],[3,2,0],[4,3,1],[5,3,1],[6,2,0],[7,3,1],[8,3,1],[9,2,0],[2,2,1],[3,2,0],[4,3,1],[5,3,1],[6,2,0],[7,3,0]]
#guard stOf printed3552 =
  stOf "psi_W_(W+1)(W_W_2)" ++ liftRows ((stOf "psi_W_(w+1)(W_(w+1))").drop 4)
#guard stOf "psi_W_(W+1)(W_W_2)" < stOf "psi_W_(W+1)(W_W_w)"
#guard stOf "psi_W_(W+1)(W_W_w)" < stOf printed3552
#guard stOf printed3552 < stOf "W_(W+1)"
#guard (List.range 4).all fun n =>
  expandRL 3 n (stOf printed3552) =
    stOf "psi_W_(W+1)(W_W_2)" ++
      liftRows ((expandRL 3 n (stOf "psi_W_(w+1)(W_(w+1))")).drop 4)
#guard stOf "psi_W_(W+1)(W_W_w)" = stOf "psi_W_(W+1)(W_W_2)" ++ [[2,2,1]]
#guard expandRL 3 1 (stOf "psi_W_(W+1)(W_W_w)") =
  stOf "psi_W_(W+1)(W_W_2)" ++
    [[2,2,0],[3,3,1],[4,3,1],[5,3,0],[3,3,1],[4,3,1],[5,1,0],[4,3,0],[5,4,1],[6,4,1],[7,3,0],[8,4,1],[9,4,1],[10,3,0]]
#guard expandRL 3 2 (stOf "W_(W+1)") = stOf "psi_W_(W+1)(W_W_2)" ++ [[10,3,1],[11,3,1]]
#guard stOf "psi_W_(W+1)(W_psi_W_(W+1)(W_(W+1)))" = stOf "psi_W_(W+1)(W_W_2)" ++ [[10,3,0]]
#guard expandRL 3 2 (stOf "psi_W_(W+1)(W_psi_W_(W+1)(W_(W+1)))") =
  stOf "psi_W_(W+1)(W_W_2)" ++ [[10,2,0],[11,2,0]]
#guard stOf printed3552 < stOf "psi_W_(W+1)(W_psi_W_(W+1)(W_(W+1)))"
#guard stOf "psi_W_(w+1)(W_W)" = row3550
#guard stOf "psi_W_(w+1)(W_W_w)" = row3550 ++ [[6,2,1]]
#guard expandRL 3 1 (row3550 ++ [[6,2,1]]) = row3550 ++ [[6,2,0],[7,3,1],[8,3,1],[9,1,0]]
#guard expandRL 3 2 (row3550 ++ [[6,2,1]]) =
  row3550 ++ [[6,2,0],[7,3,1],[8,3,1],[9,1,0],[7,3,0],[8,4,1],[9,4,1],[10,1,0]]
#guard expandRL 3 1 (row3550 ++ [[1,1,1]]) =
  row3550 ++ [[1,1,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,0],[4,3,1],[5,3,1],[6,2,0],[7,3,1],[8,3,1],[9,2,0]]

/-! ## Part 4: `TrioRulesNonLastSheet.lean` (Fix N) -/

-- The 822 labels: `TrioRulesNonLast`'s matrix except on the printed label of row 3552.
#guard sheetLabels.length = 822
#guard (sheetLabels.filter (· != printed3552)).all fun s => trioRuleMatrixOfSt s == trioRuleMatrixOfN s
#guard sheetLabels.all fun s => trioRuleMatrixOfSt s == trioRuleMatrixOf3 s

-- Fix N on the plan's case, the lifted copy, and BMS expansion.
#guard stOf "(W_W_W+W_W_2+1)" = [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,1],[4,1,0],[3,2,0],[4,3,1],[5,3,1],[6,3,0],[4,3,1],[5,3,1],[6,2,0],[5,3,0],[6,4,1],[7,4,1],[8,3,0],[7,4,0],[8,5,1],[9,5,1],[10,3,0],[4,3,1],[5,3,1],[6,2,0],[2,2,0],[3,3,1],[4,3,1],[5,3,0],[3,3,1],[4,3,1],[5,3,0],[3,3,1],[4,3,1],[5,1,0],[4,3,0],[5,4,1],[6,4,1],[7,4,0],[5,4,1],[6,4,1],[7,3,0],[6,4,0],[7,5,1],[8,5,1],[9,4,0],[8,5,0],[9,6,1],[10,6,1],[11,4,0],[5,4,1],[6,4,1],[7,2,0],[6,4,0],[7,5,0]]
#guard stOf "(W_W_W+W_(W+1)+1)" = [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,1],[4,1,0],[3,2,0],[4,3,1],[5,3,1],[6,3,0],[4,3,1],[5,3,1],[6,2,0],[5,3,0],[6,4,1],[7,4,1],[8,3,0],[7,4,0],[8,5,1],[9,5,1],[10,3,0],[4,3,0],[5,4,1],[6,4,1],[7,4,0],[5,4,1],[6,4,1],[7,2,0],[6,4,0],[7,5,1],[8,5,1],[9,4,0],[8,5,0],[9,6,1],[10,6,1],[11,3,0],[10,6,0],[11,7,0]]
#guard stOf "(W_W_W*2+1)" = [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,1],[4,1,0],[3,2,0],[4,3,1],[5,3,1],[6,3,0],[4,3,1],[5,3,1],[6,2,0],[5,3,0],[6,4,1],[7,4,1],[8,3,0],[7,4,0],[8,5,1],[9,5,1],[10,3,0],[9,5,0],[10,6,0]]
#guard stOf "(W_W+W_2+1)" = [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,1],[4,1,0],[3,2,0],[4,3,1],[5,3,1],[6,2,0],[5,3,0],[6,4,1],[7,4,1],[8,2,0],[2,2,0],[3,3,1],[4,3,1],[5,3,0],[3,3,1],[4,3,1],[5,1,0],[4,3,0],[5,4,1],[6,4,1],[7,3,0],[6,4,0],[7,5,1],[8,5,1],[9,2,0],[8,5,0],[9,6,0]]
#guard stOf "(W_W*2+1)" = [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,1],[4,1,0],[3,2,0],[4,3,1],[5,3,1],[6,2,0],[5,3,0],[6,4,1],[7,4,1],[8,2,0],[7,4,0],[8,5,0]]
#guard stOf "(W_W_W+W_W_2*2)" = [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,1],[4,1,0],[3,2,0],[4,3,1],[5,3,1],[6,3,0],[4,3,1],[5,3,1],[6,2,0],[5,3,0],[6,4,1],[7,4,1],[8,3,0],[7,4,0],[8,5,1],[9,5,1],[10,3,0],[4,3,1],[5,3,1],[6,2,0],[2,2,0],[3,3,1],[4,3,1],[5,3,0],[3,3,1],[4,3,1],[5,3,0],[3,3,1],[4,3,1],[5,1,0],[4,3,0],[5,4,1],[6,4,1],[7,4,0],[5,4,1],[6,4,1],[7,3,0],[6,4,0],[7,5,1],[8,5,1],[9,4,0],[8,5,0],[9,6,1],[10,6,1],[11,4,0],[5,4,1],[6,4,1],[7,2,0],[6,4,0],[7,5,1],[8,5,1],[9,3,0],[5,4,1],[6,4,1],[7,2,0]]
#guard stOf "(W_W_W+W_W_2*w)" = [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,1],[4,1,0],[3,2,0],[4,3,1],[5,3,1],[6,3,0],[4,3,1],[5,3,1],[6,2,0],[5,3,0],[6,4,1],[7,4,1],[8,3,0],[7,4,0],[8,5,1],[9,5,1],[10,3,0],[4,3,1],[5,3,1],[6,2,0],[2,2,0],[3,3,1],[4,3,1],[5,3,0],[3,3,1],[4,3,1],[5,3,0],[3,3,1],[4,3,1],[5,1,0],[4,3,0],[5,4,1],[6,4,1],[7,4,0],[5,4,1],[6,4,1],[7,3,0],[6,4,0],[7,5,1],[8,5,1],[9,4,0],[8,5,0],[9,6,1],[10,6,1],[11,4,0],[5,4,1],[6,4,1],[7,2,0],[6,4,0],[7,5,1],[8,5,1],[9,3,0],[8,5,1]]
#guard stOf "(W_W_W*W_W_2*w)" = [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,1],[4,1,0],[3,2,0],[4,3,1],[5,3,1],[6,3,0],[4,3,1],[5,3,1],[6,2,0],[5,3,0],[6,4,1],[7,4,1],[8,3,0],[7,4,1],[8,3,0],[4,3,1],[5,3,1],[6,2,0],[2,2,0],[3,3,1],[4,3,1],[5,3,0],[3,3,1],[4,3,1],[5,3,0],[3,3,1],[4,3,1],[5,1,0],[4,3,0],[5,4,1],[6,4,1],[7,4,0],[5,4,1],[6,4,1],[7,3,0],[6,4,0],[7,5,1],[8,5,1],[9,4,0],[8,5,1],[9,4,0],[5,4,1],[6,4,1],[7,2,0],[6,4,0],[7,5,1],[8,5,1],[9,4,0],[8,5,1],[9,3,0],[8,5,1]]
#guard cmpMat (stOf "(W_W_W+W_W_2)") (stOf "(W_W_W+W_W_2+1)") = .lt
#guard cmpMat (stOf "(W_W_W+W_W_2+1)") (stOf "(W_W_W+W_W_2*2)") = .lt
#guard cmpMat (stOf "(W_W_W+W_W_2*2)") (stOf "(W_W_W*2)") = .lt
#guard cmpMat (stOf "(W_W_W+W_(W+1)+1)") (stOf "(W_W_W+W_W_2)") = .lt
#guard cmpMat (stOf "(W_W_W*2)") (stOf "(W_W_W*2+1)") = .lt
#guard cmpMat (stOf "(W_W+W_2+1)") (stOf "(W_W*2)") = .lt
#guard cmpMat (stOf "(W_W+W_2+1)") (stOf "(W_W+W_w)") = .lt
#guard expandRL 3 1 (stOf "(W_W_W+W_W_w)") =
  toRows (MSt ((parse "(W_W_W+W_W_2)").getD []) ++ bliftUp (MSt ((parse "(W_W_W+W_W_2)").getD [])) 10)
#guard expandRL 3 1 (stOf "(W_W_W+W_w)") =
  toRows (MSt ((parse "(W_W_W+W_2)").getD []) ++ bliftUp (MSt ((parse "(W_W_W+W_2)").getD [])) 10)
#guard expandRL 3 1 (stOf "(W_W+W_w)") =
  toRows (MSt ((parse "(W_W+W_2)").getD []) ++ bliftUp (MSt ((parse "(W_W+W_2)").getD [])) 7)
#guard expandRL 3 1 (stOf "(W_W*w)") = stOf "(W_W+W_2)"
#guard expandRL 3 2 (stOf "(W_W*w)") = stOf "(W_W*2+W_2)"
#guard expandRL 3 1 (stOf "(W_W_W*w)") = stOf "(W_W_W+W_(W+1))"
#guard expandRL 3 2 (stOf "(W_W_W*w)") = stOf "(W_W_W*2+W_(W+1))"
#guard expandRL 3 1 (stOf "(W_W_W^2*w)") = stOf "(W_W_W^2+W_W_W*W_(W+1))"
#guard expandRL 3 2 (stOf "(W_W_W^2*w)") = stOf "(W_W_W^2*2+W_W_W*W_(W+1))"
#guard expandRL 3 1 (stOf "(W_W_W+W_2*w)") = stOf "(W_W_W+W_2*2)"
#guard expandRL 3 2 (stOf "(W_W_W+W_2*w)") = stOf "(W_W_W+W_2*3)"
#guard expandRL 3 1 (stOf "(W_W_W+W_(W+1)*w)") = stOf "(W_W_W+W_(W+1)*2)"
#guard expandRL 3 2 (stOf "(W_W_W+W_(W+1)*w)") = stOf "(W_W_W+W_(W+1)*3)"
#guard expandRL 3 1 (stOf "(W_W_W+W_W_2*w)") = stOf "(W_W_W+W_W_2*2+W_(W+1))"
#guard expandRL 3 2 (stOf "(W_W_W+W_W_2*w)") = stOf "(W_W_W+W_W_2*3+W_(W+1))"
#guard expandRL 3 1 (stOf "(W_W_W*W_2*w)") = stOf "(W_W_W*W_2*2)"
#guard expandRL 3 2 (stOf "(W_W_W*W_2*w)") = stOf "(W_W_W*W_2*3)"
#guard expandRL 3 1 (stOf "(W_W_W*W_(W+1)*w)") = stOf "(W_W_W*W_(W+1)*2)"
#guard expandRL 3 2 (stOf "(W_W_W*W_(W+1)*w)") = stOf "(W_W_W*W_(W+1)*3)"
#guard expandRL 3 1 (stOf "(W_W_W*W_W_2*w)") = stOf "(W_W_W*W_W_2*2+W_W_W*W_(W+1))"
#guard expandRL 3 1 (stOf "(W_W_W+W_W_2+W_2*w)") = stOf "(W_W_W+W_W_2+W_2*2)"
#guard expandRL 3 2 (stOf "(W_W_W+W_W_2+W_2*w)") = stOf "(W_W_W+W_W_2+W_2*3)"
#guard expandRL 3 1 (stOf "(W_W_W+W_(W+1)+W_2*w)") = stOf "(W_W_W+W_(W+1)+W_2*2)"
#guard expandRL 3 2 (stOf "(W_W_W+W_(W+1)+W_2*w)") = stOf "(W_W_W+W_(W+1)+W_2*3)"
#guard expandRL 3 1 (stOf "(W_W_W+W_W_2+W_(W+1)*w)") = stOf "(W_W_W+W_W_2+W_(W+1)*2)"
#guard expandRL 3 2 (stOf "(W_W_W+W_W_2+W_(W+1)*w)") = stOf "(W_W_W+W_W_2+W_(W+1)*3)"
#guard expandRL 3 1 (stOf "(W_W+W_2*w)") = stOf "(W_W+W_2*2)"
#guard expandRL 3 2 (stOf "(W_W+W_2*w)") = stOf "(W_W+W_2*3)"
#guard expandRL 3 1 (stOf "(W_W+W_2+W*w)") = stOf "(W_W+W_2+W*2)"
#guard expandRL 3 2 (stOf "(W_W+W_2+W*w)") = stOf "(W_W+W_2+W*3)"

-- The nearby families: the same counts as with Fix N alone.
#guard pairDisagreements (withM stOf familyW) = 1 ∧ collisions (withM stOf familyW) = 1
#guard pairDisagreements (withM stOf family1) = 0 ∧ collisions (withM stOf family1) = 0
#guard pairDisagreements (withM stOf probes) = 25
#guard crossDisagreements (withM stOf probes) chosenDataSt = 20
#guard crossDisagreements (withM stOf probes) chosenDataSt3 = 20

/-! ## Part 5: against rules 1–10 and the single-fix versions

`interactionsSt ls` lists the labels of `ls` where the merged matrix is not the one
expected with no interaction: `TrioRulesNonLast`'s when Fix E changes nothing
(`TrioRules3` = `TrioRules2`), `TrioRules3`'s when Fix N changes nothing, and any
label that both fixes change. -/

/-- The labels where Fix E and Fix N interact, or the merged matrix is unexpected. -/
def interactionsSt (ls : List String) : List String :=
  ls.filter fun s =>
    let a := stOf s
    let o := ruleOf2 s
    let e := ruleOf3 s
    let n := nOf s
    (e == o && a != n) || (n == o && a != e) || (e != o && n != o)

#guard interactionsSt sheetLabels = []
#guard interactionsSt familyW = []
#guard interactionsSt family1 = []
#guard interactionsSt probes = []

-- Against rules 1–10: 24 labels differ (22 `S` rows, row 4533, printed row 3552);
-- `TrioRules2` differs on 23 of them.
#guard (sheetLabels.filter fun s => trioRuleMatrixOfSt s != trioRuleMatrixOf s).length = 24
#guard (sheetLabels.filter fun s => trioRuleMatrixOf2 s != trioRuleMatrixOf s).length = 23
#guard (sheetLabels.filter fun s => trioRuleMatrixOfSt s != trioRuleMatrixOf s).all fun s =>
  s == printed3552 || trioRuleMatrixOf2 s != trioRuleMatrixOf s
#guard trioRuleMatrixOf2 printed3552 == trioRuleMatrixOf printed3552

/-! ## Part 6: where Fix E and Fix N meet

Hand-made labels where a level named by Fix E is a leaf in a Fix N regime, and where
a Fix N subscript sits in a Fix E argument.  `p` is the printed ordinal of row 3552,
`ψ_{Ω_{Ω+1}}(Ω_{ψ_{Ω_{ω+1}}(Ω_{ω+1})})`.  Columns of the tuple: Fix E changes the
label (vs `TrioRules2`), Fix N changes it, merged = `TrioRules3`, merged =
`TrioRulesNonLast`. -/

#guard probesEN.all fun s => (parse s).isSome

/-- `(Fix E changes it, Fix N changes it, merged = E, merged = N)`. -/
def meetSt (s : String) : Bool × Bool × Bool × Bool :=
  (ruleOf3 s != ruleOf2 s, nOf s != ruleOf2 s, stOf s == ruleOf3 s, stOf s == nOf s)

-- Both fixes change the label, and the merged matrix is neither single-fix matrix:
-- `p` as a leaf with more after it in the regime `Ω_{Ω_Ω}`, and Fix N subscripts
-- (`Ω_{Ω_Ω}+Ω_{Ω_2}+1`, `Ω_Ω+Ω_2+1`, `Ω_{Ω_Ω}+Ω_{Ω+1}+1`) in the argument of
-- `ψ_{Ω_{ω+1}}` inside a Fix E argument.
#guard interactionsSt probesEN = [
  "(W_W_W_W+W_psi_W_(W+1)(W_psi_W_(w+1)(W_(w+1)))+1)",
  "(W_W_W_W+W_psi_W_(W+1)(W_psi_W_(w+1)(W_(w+1)))+W_2)",
  "(W_W_W_W+W_psi_W_(W+1)(W_psi_W_(w+1)(W_(w+1)))+W)",
  "(W_W_W_W+W_psi_W_(W+1)(W_psi_W_(w+1)(W_(w+1)))*2)",
  "(W_W_W_W*W_psi_W_(W+1)(W_psi_W_(w+1)(W_(w+1)))*2)",
  "psi_W_(W+1)(W_psi_W_(w+1)(W_(W_W_W+W_W_2+1)))",
  "psi_W_(W+1)(W_psi_W_(w+1)(W_(W_W+W_2+1)))",
  "psi_W_(W+1)(W_psi_W_(w+1)(W_(W_W_W+W_(W+1)+1)))"]
#guard (interactionsSt probesEN).all fun s => meetSt s == (true, true, false, false)
-- On the other 12, only one fix acts and the merged matrix is that version's.
#guard (probesEN.filter fun s => !(interactionsSt probesEN).contains s).all fun s =>
  let m := meetSt s
  (m.1 && !m.2.1 && m.2.2.1) || (!m.1 && m.2.1 && m.2.2.2)

-- Order: the merged matrices of the 20 labels against the 784 chosen ones, 0
-- disagreements (Fix N alone: 5).  Among themselves 3, all collisions: rule 9 reads
-- only the level of its argument, so `ψ_{Ω_{Ω+1}}(Ω_{Ω_ω})` and
-- `ψ_{Ω_{Ω+1}}(Ω_{Ω_ω}+1)` share a matrix (Fix E alone: 11 disagreements, 8
-- collisions).
#guard crossDisagreements (withM stOf probesEN) chosenDataSt3 = 0
#guard crossDisagreements (withM nOf probesEN)
  (((chosen ++ [printed3552]).map fun s => ((parse s).getD [], nOf s)).toArray) = 5
#guard pairDisagreements (withM stOf probesEN) = 3 ∧ collisions (withM stOf probesEN) = 3
#guard pairDisagreements (withM ruleOf3 probesEN) = 11 ∧ collisions (withM ruleOf3 probesEN) = 8
#guard stOf "psi_W_(W+1)(W_W_w)" = stOf "psi_W_(W+1)(W_W_w+1)"

/-! ## Part 7: one step against rules 1–10

As in `TrioRulesAllSheet.lean`, with the patched step `MstepSt` and the patched
builder one step of fuel down: the counts are the same (on countable `α` the
patched step is rules 1–10's everywhere on the corpus; `ψ`, `Ω_v`, sums: 6, 7, 257). -/

/-- The patched builder one step of fuel down. -/
def MfPrevSt : Od → Cols := MfuelSt (fuel - 1)

/-- The patched step and rules 1–10's step differ on the label, with the same `Mf`. -/
def stepDiffersSt (s : String) : Bool :=
  let a := (parse s).getD []
  MstepSt MfPrevSt a != Mstep MfPrevSt a

/-- `MSt` is one patched step on `MfPrevSt`. -/
theorem MSt_eq_step : MSt = MstepSt MfPrevSt := rfl

#guard (["countable", "psi", "omega", "sum"].map fun k =>
    let ls := corpus.filter fun s => branch ((parse s).getD []) == k
    (k, ls.length, (ls.filter stepDiffersSt).length)) =
  [("countable", 171, 0), ("psi", 32, 6), ("omega", 152, 7), ("sum", 870, 257)]
#guard (corpus.filter fun s => branch ((parse s).getD []) == "psi").all fun s =>
  match isPsiLevel ((parse s).getD []) with
  | some uX => stepDiffersSt s == (fixAFires MfPrevSt uX.1 || fixEFires MfPrevSt uX.1 uX.2)
  | none => false
#guard (corpus.filter fun s => branch ((parse s).getD []) == "omega").all fun s =>
  match lvlO ((parse s).getD []) with
  | some v => stepDiffersSt s == fixAFires MfPrevSt v
  | none => false

/-! ## Part 8: the patch's own checks -/

-- The patch changes no label of the corpus of `TrioRulesAllSheet.lean`, nor any step.
#guard corpus.length = 1225
#guard corpus.all fun s => stOf s == allOf s
#guard corpus.all fun s => let a := (parse s).getD []; MstepSt MfPrevSt a == MstepAll MfPrevSt a

-- Rule 1 on `ω^{ε₀·ω}` (theorems `strip_e0w`, `stripSt_e0w` in `TrioFixStrip.lean`).
#guard strip (.o [(e0w, 1)]) == [(e0w, 1)]
#guard stripSt (.o [(e0w, 1)]) == [(.W one, 1), (e0w, 1)]
#guard uncollapses (.o [(e0w, 1)]) && !headIsPsi (ato (.o [(e0w, 1)]))

-- `β`: the tree of the term, which is also the old map's matrix; now above `ε_{ε₀}`.
#guard trioMatrixLSt tβ = trioRuleMatrixAll (TrioRules.ofTerm tβ)
#guard trioMatrixLSt tβ = [[0,0,0],[1,1,1],[2,1,1],[3,0,0],[4,1,0],[5,0,0],[6,1,0],[6,0,0],[7,1,0],[7,0,0]]
#guard cmpMat (trioMatrixLSt tα) (trioMatrixLSt tβ) = .lt
#guard trioMatrixLFix tβ ≠ trioMatrixLSt tβ

end Googology.Trans.BMS.TrioFixStrip
