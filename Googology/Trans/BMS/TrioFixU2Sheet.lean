import Googology.Trans.BMS.TrioFixU2
import Googology.Trans.BMS.TrioRulesAllSheet

/-!
# Fix U2 against the sheet corpus and on its probe labels

`TrioFixU2.lean` is `TrioFixU.lean` with rule 9 replaced by `MpsiLevelU2` (Fix K and the
shift row).  All of this file is `#guard`s: a calibration, not a theorem.  The notes are in
[TRIO-FIX-U2.md](TRIO-FIX-U2.md).

* **Part 1.**  Fix U2 changes none of the 1,209 labels of the sheet corpus that
  `TrioFixUSheet.lean` checks (`corpus ++ chosen ++ allLabels`), so every guard there holds
  with the same counts.
* **Part 2.**  Fix U2 changes none of Fix U's 562 probe labels in Fix U's domain.
* **Part 3.**  The three counterexamples (a) and the repair by Fix K.
* **Part 4.**  The shift row (b), one label each for `L = 2` and `L = 3`.
* **Part 5.**  The 1,334 probe labels in `inDomainU2` whose argument matrix `M(w)` is itself
  standard and in order: their Fix U2 matrices are in the order of the labels (with the
  784 chosen labels too).  Standardness (1,334 / 1,334) is checked outside Lean with yaBMS
  `bms -s`.
-/

namespace Googology.Trans.BMS.TrioFixU2

open Googology.Trans.BMS.TrioRules
open Googology.Trans.BMS.TrioRules2
open Googology.Trans.BMS.TrioRules3
open Googology.Trans.BMS.TrioRulesNL
open Googology.Trans.BMS.TrioRulesAll
open Googology.Trans.BMS.TrioFixU

/-! ## Part 1: the sheet corpus is unchanged -/

/-- Every label used in the sheet checks of Fix U (1,209 distinct). -/
def everyLabel : List String := (corpus ++ chosen ++ allLabels).eraseDups

#guard everyLabel.length = 1209
#guard everyLabel.all fun s => u2Of s == uOf s

/-! ## Part 2: Fix U's probe labels in its domain are unchanged -/

/-- The 562 probe labels of `TrioFixUSheet.lean` in Fix U's domain. -/
def fixUDomain : List String := [
  "psi_W_(W+1)(W_(W+1))", "psi_W_(W+1)(W_(W+2))", "psi_W_(W+1)(W_(W+3))",
  "psi_W_(W+1)(W_(W+w))", "psi_W_(W+1)(W_(W*2))", "psi_W_(W+1)(W_(W*2+1))",
  "psi_W_(W+1)(W_(W*2+2))", "psi_W_(W+1)(W_(W*3))", "psi_W_(W+1)(W_(W^2))",
  "psi_W_(W+1)(W_(W^2+1))", "psi_W_(W+1)(W_psi_1(W_2))", "psi_W_(W+1)(W_psi_1(W_2*2))",
  "psi_W_(W+1)(W_psi_W_2(W_W))", "psi_W_(W+1)(W_W_2)", "psi_W_(W+1)(W_(W_2+1))",
  "psi_W_(W+1)(W_(W_2+2))", "psi_W_(W+1)(W_(W_2+w))", "psi_W_(W+1)(W_(W_2+W))",
  "psi_W_(W+1)(W_(W_2*2))", "psi_W_(W+1)(W_(W_2*w))", "psi_W_(W+1)(W_(W_2*W))",
  "psi_W_(W+1)(W_(W_2*W_2))", "psi_W_(W+1)(W_(W_2^W_2))", "psi_W_(W+1)(W_psi_2(W_3))",
  "psi_W_(W+1)(W_psi_2(W_3*2))", "psi_W_(W+1)(W_W_3)", "psi_W_(W+1)(W_(W_3+1))",
  "psi_W_(W+1)(W_(W_3+W))", "psi_W_(W+1)(W_(W_3+W_2))", "psi_W_(W+1)(W_(W_3*2))",
  "psi_W_(W+1)(W_(W_3^2))", "psi_W_(W+1)(W_W_4)", "psi_W_(W+1)(W_(W_4+1))",
  "psi_W_(W+1)(W_W_5)", "psi_W_(W+1)(W_W_w)", "psi_W_(W+1)(W_(W_w+1))",
  "psi_W_(W+1)(W_(W_w*2))", "psi_W_(W+1)(W_W_(w+1))", "psi_W_(W+1)(W_(W_(w+1)+1))",
  "psi_W_(W+1)(W_W_(w+2))", "psi_W_(W+1)(W_W_(w2))", "psi_W_(W+1)(W_W_(w^2))",
  "psi_W_(W+1)(W_W_(w^w))", "psi_W_(W+1)(W_W_(w^w+1))", "psi_W_(W+1)(W_W_psi(W))",
  "psi_W_(W+1)(W_W_psi(W_w))", "psi_W_(W+1)(W_W_W)", "psi_W_(W+1)(W_(W_W+1))",
  "psi_W_(W+1)(W_(W_W+2))", "psi_W_(W+1)(W_(W_W+w))", "psi_W_(W+1)(W_(W_W+W))",
  "psi_W_(W+1)(W_(W_W+W_2))", "psi_W_(W+1)(W_(W_W+W_w))", "psi_W_(W+1)(W_(W_W*2))",
  "psi_W_(W+1)(W_(W_W*2+1))", "psi_W_(W+1)(W_(W_W*w))", "psi_W_(W+1)(W_(W_W*W))",
  "psi_W_(W+1)(W_(W_W^2))", "psi_W_(W+1)(W_(W_W^W_W))", "psi_W_(W+1)(W_psi_W_(W+1)(W_(W+1)))",
  "psi_W_(W+1)(W_psi_W_(W+1)(W_W_2))", "psi_W_(W+1)(W_psi_W_(W+1)(W_W_W))", "psi_W_(W+1)(W_psi_W_(W+1)(W_(W_W+1)))",
  "psi_W_(W+1)(W_psi_W_(W+1)(W_psi_W_(W+1)(W_(W+1))))", "psi_W_(W+2)(W_(W+2))", "psi_W_(W+2)(W_(W+3))",
  "psi_W_(W+2)(W_(W+w))", "psi_W_(W+2)(W_(W*2))", "psi_W_(W+2)(W_(W*2+1))",
  "psi_W_(W+2)(W_(W*2+2))", "psi_W_(W+2)(W_(W*3))", "psi_W_(W+2)(W_(W^2))",
  "psi_W_(W+2)(W_(W^2+1))", "psi_W_(W+2)(W_psi_1(W_2))", "psi_W_(W+2)(W_psi_1(W_2*2))",
  "psi_W_(W+2)(W_psi_W_2(W_W))", "psi_W_(W+2)(W_W_2)", "psi_W_(W+2)(W_(W_2+1))",
  "psi_W_(W+2)(W_(W_2+2))", "psi_W_(W+2)(W_(W_2+w))", "psi_W_(W+2)(W_(W_2+W))",
  "psi_W_(W+2)(W_(W_2*2))", "psi_W_(W+2)(W_(W_2*w))", "psi_W_(W+2)(W_(W_2*W))",
  "psi_W_(W+2)(W_(W_2*W_2))", "psi_W_(W+2)(W_(W_2^W_2))", "psi_W_(W+2)(W_psi_2(W_3))",
  "psi_W_(W+2)(W_psi_2(W_3*2))", "psi_W_(W+2)(W_W_3)", "psi_W_(W+2)(W_(W_3+1))",
  "psi_W_(W+2)(W_(W_3+W))", "psi_W_(W+2)(W_(W_3+W_2))", "psi_W_(W+2)(W_(W_3*2))",
  "psi_W_(W+2)(W_(W_3^2))", "psi_W_(W+2)(W_W_4)", "psi_W_(W+2)(W_(W_4+1))",
  "psi_W_(W+2)(W_W_5)", "psi_W_(W+2)(W_W_w)", "psi_W_(W+2)(W_(W_w+1))",
  "psi_W_(W+2)(W_(W_w*2))", "psi_W_(W+2)(W_W_(w+1))", "psi_W_(W+2)(W_(W_(w+1)+1))",
  "psi_W_(W+2)(W_W_(w+2))", "psi_W_(W+2)(W_W_(w2))", "psi_W_(W+2)(W_W_(w^2))",
  "psi_W_(W+2)(W_W_(w^w))", "psi_W_(W+2)(W_W_(w^w+1))", "psi_W_(W+2)(W_W_psi(W))",
  "psi_W_(W+2)(W_W_psi(W_w))", "psi_W_(W+2)(W_W_W)", "psi_W_(W+2)(W_(W_W+1))",
  "psi_W_(W+2)(W_(W_W+2))", "psi_W_(W+2)(W_(W_W+w))", "psi_W_(W+2)(W_(W_W+W))",
  "psi_W_(W+2)(W_(W_W+W_2))", "psi_W_(W+2)(W_(W_W+W_w))", "psi_W_(W+2)(W_(W_W*2))",
  "psi_W_(W+2)(W_(W_W*2+1))", "psi_W_(W+2)(W_(W_W*w))", "psi_W_(W+2)(W_(W_W*W))",
  "psi_W_(W+2)(W_(W_W^2))", "psi_W_(W+2)(W_(W_W^W_W))", "psi_W_(W+2)(W_psi_W_(W+1)(W_(W+1)))",
  "psi_W_(W+2)(W_psi_W_(W+1)(W_W_2))", "psi_W_(W+2)(W_psi_W_(W+1)(W_W_W))", "psi_W_(W+2)(W_psi_W_(W+1)(W_(W_W+1)))",
  "psi_W_(W+2)(W_psi_W_(W+1)(W_psi_W_(W+1)(W_(W+1))))", "psi_W_(W+2)(W_W_(W+1))", "psi_W_(W+2)(W_(W_(W+1)+1))",
  "psi_W_(W+2)(W_(W_(W+1)*2))", "psi_W_(W+2)(W_psi_W_(W+2)(W_(W+2)))", "psi_W_(W+2)(W_psi_W_(W+2)(W_W_2))",
  "psi_W_(W+2)(W_psi_W_(W+2)(W_W_W))", "psi_W_(W+2)(W_psi_W_(W+2)(W_(W_W+1)))", "psi_W_(W+2)(W_psi_W_(W+2)(W_W_(W+1)))",
  "psi_W_(W+2)(W_psi_W_(W+2)(W_psi_W_(W+2)(W_(W+2))))", "psi_W_(W+3)(W_(W+3))", "psi_W_(W+3)(W_(W+w))",
  "psi_W_(W+3)(W_(W*2))", "psi_W_(W+3)(W_(W*2+1))", "psi_W_(W+3)(W_(W*2+2))",
  "psi_W_(W+3)(W_(W*3))", "psi_W_(W+3)(W_(W^2))", "psi_W_(W+3)(W_(W^2+1))",
  "psi_W_(W+3)(W_psi_1(W_2))", "psi_W_(W+3)(W_psi_1(W_2*2))", "psi_W_(W+3)(W_psi_W_2(W_W))",
  "psi_W_(W+3)(W_W_2)", "psi_W_(W+3)(W_(W_2+1))", "psi_W_(W+3)(W_(W_2+2))",
  "psi_W_(W+3)(W_(W_2+w))", "psi_W_(W+3)(W_(W_2+W))", "psi_W_(W+3)(W_(W_2*2))",
  "psi_W_(W+3)(W_(W_2*w))", "psi_W_(W+3)(W_(W_2*W))", "psi_W_(W+3)(W_(W_2*W_2))",
  "psi_W_(W+3)(W_(W_2^W_2))", "psi_W_(W+3)(W_psi_2(W_3))", "psi_W_(W+3)(W_psi_2(W_3*2))",
  "psi_W_(W+3)(W_W_3)", "psi_W_(W+3)(W_(W_3+1))", "psi_W_(W+3)(W_(W_3+W))",
  "psi_W_(W+3)(W_(W_3+W_2))", "psi_W_(W+3)(W_(W_3*2))", "psi_W_(W+3)(W_(W_3^2))",
  "psi_W_(W+3)(W_W_4)", "psi_W_(W+3)(W_(W_4+1))", "psi_W_(W+3)(W_W_5)",
  "psi_W_(W+3)(W_W_w)", "psi_W_(W+3)(W_(W_w+1))", "psi_W_(W+3)(W_(W_w*2))",
  "psi_W_(W+3)(W_W_(w+1))", "psi_W_(W+3)(W_(W_(w+1)+1))", "psi_W_(W+3)(W_W_(w+2))",
  "psi_W_(W+3)(W_W_(w2))", "psi_W_(W+3)(W_W_(w^2))", "psi_W_(W+3)(W_W_(w^w))",
  "psi_W_(W+3)(W_W_(w^w+1))", "psi_W_(W+3)(W_W_psi(W))", "psi_W_(W+3)(W_W_psi(W_w))",
  "psi_W_(W+3)(W_W_W)", "psi_W_(W+3)(W_(W_W+1))", "psi_W_(W+3)(W_(W_W+2))",
  "psi_W_(W+3)(W_(W_W+w))", "psi_W_(W+3)(W_(W_W+W))", "psi_W_(W+3)(W_(W_W+W_2))",
  "psi_W_(W+3)(W_(W_W+W_w))", "psi_W_(W+3)(W_(W_W*2))", "psi_W_(W+3)(W_(W_W*2+1))",
  "psi_W_(W+3)(W_(W_W*w))", "psi_W_(W+3)(W_(W_W*W))", "psi_W_(W+3)(W_(W_W^2))",
  "psi_W_(W+3)(W_(W_W^W_W))", "psi_W_(W+3)(W_psi_W_(W+1)(W_(W+1)))", "psi_W_(W+3)(W_psi_W_(W+1)(W_W_2))",
  "psi_W_(W+3)(W_psi_W_(W+1)(W_W_W))", "psi_W_(W+3)(W_psi_W_(W+1)(W_(W_W+1)))", "psi_W_(W+3)(W_psi_W_(W+1)(W_psi_W_(W+1)(W_(W+1))))",
  "psi_W_(W+3)(W_W_(W+1))", "psi_W_(W+3)(W_(W_(W+1)+1))", "psi_W_(W+3)(W_(W_(W+1)*2))",
  "psi_W_(W+3)(W_psi_W_(W+2)(W_(W+2)))", "psi_W_(W+3)(W_psi_W_(W+2)(W_W_2))", "psi_W_(W+3)(W_psi_W_(W+2)(W_W_W))",
  "psi_W_(W+3)(W_psi_W_(W+2)(W_(W_W+1)))", "psi_W_(W+3)(W_psi_W_(W+2)(W_W_(W+1)))", "psi_W_(W+3)(W_psi_W_(W+2)(W_psi_W_(W+2)(W_(W+2))))",
  "psi_W_(W+3)(W_W_(W+2))", "psi_W_(W+3)(W_(W_(W+2)+1))", "psi_W_(W+3)(W_(W_(W+2)*2))",
  "psi_W_(W+3)(W_psi_W_(W+3)(W_(W+3)))", "psi_W_(W+3)(W_psi_W_(W+3)(W_W_2))", "psi_W_(W+3)(W_psi_W_(W+3)(W_W_W))",
  "psi_W_(W+3)(W_psi_W_(W+3)(W_(W_W+1)))", "psi_W_(W+3)(W_psi_W_(W+3)(W_W_(W+1)))", "psi_W_(W+3)(W_psi_W_(W+3)(W_psi_W_(W+3)(W_(W+3))))",
  "psi_W_(W+w+1)(W_(W*2))", "psi_W_(W+w+1)(W_(W*2+1))", "psi_W_(W+w+1)(W_(W*2+2))",
  "psi_W_(W+w+1)(W_(W*3))", "psi_W_(W+w+1)(W_(W^2))", "psi_W_(W+w+1)(W_(W^2+1))",
  "psi_W_(W+w+1)(W_psi_1(W_2))", "psi_W_(W+w+1)(W_psi_1(W_2*2))", "psi_W_(W+w+1)(W_psi_W_2(W_W))",
  "psi_W_(W+w+1)(W_W_2)", "psi_W_(W+w+1)(W_(W_2+1))", "psi_W_(W+w+1)(W_(W_2+2))",
  "psi_W_(W+w+1)(W_(W_2+w))", "psi_W_(W+w+1)(W_(W_2+W))", "psi_W_(W+w+1)(W_(W_2*2))",
  "psi_W_(W+w+1)(W_(W_2*w))", "psi_W_(W+w+1)(W_(W_2*W))", "psi_W_(W+w+1)(W_(W_2*W_2))",
  "psi_W_(W+w+1)(W_(W_2^W_2))", "psi_W_(W+w+1)(W_psi_2(W_3))", "psi_W_(W+w+1)(W_psi_2(W_3*2))",
  "psi_W_(W+w+1)(W_W_3)", "psi_W_(W+w+1)(W_(W_3+1))", "psi_W_(W+w+1)(W_(W_3+W))",
  "psi_W_(W+w+1)(W_(W_3+W_2))", "psi_W_(W+w+1)(W_(W_3*2))", "psi_W_(W+w+1)(W_(W_3^2))",
  "psi_W_(W+w+1)(W_W_4)", "psi_W_(W+w+1)(W_(W_4+1))", "psi_W_(W+w+1)(W_W_5)",
  "psi_W_(W+w+1)(W_W_w)", "psi_W_(W+w+1)(W_(W_w+1))", "psi_W_(W+w+1)(W_(W_w*2))",
  "psi_W_(W+w+1)(W_W_(w+1))", "psi_W_(W+w+1)(W_(W_(w+1)+1))", "psi_W_(W+w+1)(W_W_(w+2))",
  "psi_W_(W+w+1)(W_W_(w2))", "psi_W_(W+w+1)(W_W_(w^2))", "psi_W_(W+w+1)(W_W_(w^w))",
  "psi_W_(W+w+1)(W_W_(w^w+1))", "psi_W_(W+w+1)(W_W_psi(W))", "psi_W_(W+w+1)(W_W_psi(W_w))",
  "psi_W_(W+w+1)(W_W_W)", "psi_W_(W+w+1)(W_(W_W+1))", "psi_W_(W+w+1)(W_(W_W+2))",
  "psi_W_(W+w+1)(W_(W_W+w))", "psi_W_(W+w+1)(W_(W_W+W))", "psi_W_(W+w+1)(W_(W_W+W_2))",
  "psi_W_(W+w+1)(W_(W_W+W_w))", "psi_W_(W+w+1)(W_(W_W*2))", "psi_W_(W+w+1)(W_(W_W*2+1))",
  "psi_W_(W+w+1)(W_(W_W*w))", "psi_W_(W+w+1)(W_(W_W*W))", "psi_W_(W+w+1)(W_(W_W^2))",
  "psi_W_(W+w+1)(W_(W_W^W_W))", "psi_W_(W+w+1)(W_psi_W_(W+1)(W_(W+1)))", "psi_W_(W+w+1)(W_psi_W_(W+1)(W_W_2))",
  "psi_W_(W+w+1)(W_psi_W_(W+1)(W_W_W))", "psi_W_(W+w+1)(W_psi_W_(W+1)(W_(W_W+1)))", "psi_W_(W+w+1)(W_psi_W_(W+1)(W_psi_W_(W+1)(W_(W+1))))",
  "psi_W_(W*2+1)(W_(W*2+1))", "psi_W_(W*2+1)(W_(W*2+2))", "psi_W_(W*2+1)(W_(W*3))",
  "psi_W_(W*2+1)(W_(W^2))", "psi_W_(W*2+1)(W_(W^2+1))", "psi_W_(W*2+1)(W_psi_1(W_2))",
  "psi_W_(W*2+1)(W_psi_1(W_2*2))", "psi_W_(W*2+1)(W_psi_W_2(W_W))", "psi_W_(W*2+1)(W_W_2)",
  "psi_W_(W*2+1)(W_(W_2+1))", "psi_W_(W*2+1)(W_(W_2+2))", "psi_W_(W*2+1)(W_(W_2+w))",
  "psi_W_(W*2+1)(W_(W_2+W))", "psi_W_(W*2+1)(W_(W_2*2))", "psi_W_(W*2+1)(W_(W_2*w))",
  "psi_W_(W*2+1)(W_(W_2*W))", "psi_W_(W*2+1)(W_(W_2*W_2))", "psi_W_(W*2+1)(W_(W_2^W_2))",
  "psi_W_(W*2+1)(W_psi_2(W_3))", "psi_W_(W*2+1)(W_psi_2(W_3*2))", "psi_W_(W*2+1)(W_W_3)",
  "psi_W_(W*2+1)(W_(W_3+1))", "psi_W_(W*2+1)(W_(W_3+W))", "psi_W_(W*2+1)(W_(W_3+W_2))",
  "psi_W_(W*2+1)(W_(W_3*2))", "psi_W_(W*2+1)(W_(W_3^2))", "psi_W_(W*2+1)(W_W_4)",
  "psi_W_(W*2+1)(W_(W_4+1))", "psi_W_(W*2+1)(W_W_5)", "psi_W_(W*2+1)(W_W_w)",
  "psi_W_(W*2+1)(W_(W_w+1))", "psi_W_(W*2+1)(W_(W_w*2))", "psi_W_(W*2+1)(W_W_(w+1))",
  "psi_W_(W*2+1)(W_(W_(w+1)+1))", "psi_W_(W*2+1)(W_W_(w+2))", "psi_W_(W*2+1)(W_W_(w2))",
  "psi_W_(W*2+1)(W_W_(w^2))", "psi_W_(W*2+1)(W_W_(w^w))", "psi_W_(W*2+1)(W_W_(w^w+1))",
  "psi_W_(W*2+1)(W_W_psi(W))", "psi_W_(W*2+1)(W_W_psi(W_w))", "psi_W_(W*2+1)(W_W_W)",
  "psi_W_(W*2+1)(W_(W_W+1))", "psi_W_(W*2+1)(W_(W_W+2))", "psi_W_(W*2+1)(W_(W_W+w))",
  "psi_W_(W*2+1)(W_(W_W+W))", "psi_W_(W*2+1)(W_(W_W+W_2))", "psi_W_(W*2+1)(W_(W_W+W_w))",
  "psi_W_(W*2+1)(W_(W_W*2))", "psi_W_(W*2+1)(W_(W_W*2+1))", "psi_W_(W*2+1)(W_(W_W*w))",
  "psi_W_(W*2+1)(W_(W_W*W))", "psi_W_(W*2+1)(W_(W_W^2))", "psi_W_(W*2+1)(W_(W_W^W_W))",
  "psi_W_(W*2+1)(W_psi_W_(W+1)(W_(W+1)))", "psi_W_(W*2+1)(W_psi_W_(W+1)(W_W_2))", "psi_W_(W*2+1)(W_psi_W_(W+1)(W_W_W))",
  "psi_W_(W*2+1)(W_psi_W_(W+1)(W_(W_W+1)))", "psi_W_(W*2+1)(W_psi_W_(W+1)(W_psi_W_(W+1)(W_(W+1))))", "psi_W_(W^2+1)(W_(W^2+1))",
  "psi_W_(W^2+1)(W_psi_1(W_2))", "psi_W_(W^2+1)(W_psi_1(W_2*2))", "psi_W_(W^2+1)(W_psi_W_2(W_W))",
  "psi_W_(W^2+1)(W_W_2)", "psi_W_(W^2+1)(W_(W_2+1))", "psi_W_(W^2+1)(W_(W_2+2))",
  "psi_W_(W^2+1)(W_(W_2+w))", "psi_W_(W^2+1)(W_(W_2+W))", "psi_W_(W^2+1)(W_(W_2*2))",
  "psi_W_(W^2+1)(W_(W_2*w))", "psi_W_(W^2+1)(W_(W_2*W))", "psi_W_(W^2+1)(W_(W_2*W_2))",
  "psi_W_(W^2+1)(W_(W_2^W_2))", "psi_W_(W^2+1)(W_psi_2(W_3))", "psi_W_(W^2+1)(W_psi_2(W_3*2))",
  "psi_W_(W^2+1)(W_W_3)", "psi_W_(W^2+1)(W_(W_3+1))", "psi_W_(W^2+1)(W_(W_3+W))",
  "psi_W_(W^2+1)(W_(W_3+W_2))", "psi_W_(W^2+1)(W_(W_3*2))", "psi_W_(W^2+1)(W_(W_3^2))",
  "psi_W_(W^2+1)(W_W_4)", "psi_W_(W^2+1)(W_(W_4+1))", "psi_W_(W^2+1)(W_W_5)",
  "psi_W_(W^2+1)(W_W_w)", "psi_W_(W^2+1)(W_(W_w+1))", "psi_W_(W^2+1)(W_(W_w*2))",
  "psi_W_(W^2+1)(W_W_(w+1))", "psi_W_(W^2+1)(W_(W_(w+1)+1))", "psi_W_(W^2+1)(W_W_(w+2))",
  "psi_W_(W^2+1)(W_W_(w2))", "psi_W_(W^2+1)(W_W_(w^2))", "psi_W_(W^2+1)(W_W_(w^w))",
  "psi_W_(W^2+1)(W_W_(w^w+1))", "psi_W_(W^2+1)(W_W_psi(W))", "psi_W_(W^2+1)(W_W_psi(W_w))",
  "psi_W_(W^2+1)(W_W_W)", "psi_W_(W^2+1)(W_(W_W+1))", "psi_W_(W^2+1)(W_(W_W+2))",
  "psi_W_(W^2+1)(W_(W_W+w))", "psi_W_(W^2+1)(W_(W_W+W))", "psi_W_(W^2+1)(W_(W_W+W_2))",
  "psi_W_(W^2+1)(W_(W_W+W_w))", "psi_W_(W^2+1)(W_(W_W*2))", "psi_W_(W^2+1)(W_(W_W*2+1))",
  "psi_W_(W^2+1)(W_(W_W*w))", "psi_W_(W^2+1)(W_(W_W*W))", "psi_W_(W^2+1)(W_(W_W^2))",
  "psi_W_(W^2+1)(W_(W_W^W_W))", "psi_W_(W^2+1)(W_psi_W_(W+1)(W_(W+1)))", "psi_W_(W^2+1)(W_psi_W_(W+1)(W_W_2))",
  "psi_W_(W^2+1)(W_psi_W_(W+1)(W_W_W))", "psi_W_(W^2+1)(W_psi_W_(W+1)(W_(W_W+1)))", "psi_W_(W^2+1)(W_psi_W_(W+1)(W_psi_W_(W+1)(W_(W+1))))",
  "psi_W_(W_2+1)(W_(W_2+1))", "psi_W_(W_2+1)(W_(W_2+2))", "psi_W_(W_2+1)(W_(W_2+w))",
  "psi_W_(W_2+1)(W_(W_2+W))", "psi_W_(W_2+1)(W_(W_2*2))", "psi_W_(W_2+1)(W_(W_2*w))",
  "psi_W_(W_2+1)(W_(W_2*W))", "psi_W_(W_2+1)(W_(W_2*W_2))", "psi_W_(W_2+1)(W_(W_2^W_2))",
  "psi_W_(W_2+1)(W_psi_2(W_3))", "psi_W_(W_2+1)(W_psi_2(W_3*2))", "psi_W_(W_2+1)(W_W_3)",
  "psi_W_(W_2+1)(W_(W_3+1))", "psi_W_(W_2+1)(W_(W_3+W))", "psi_W_(W_2+1)(W_(W_3+W_2))",
  "psi_W_(W_2+1)(W_(W_3*2))", "psi_W_(W_2+1)(W_(W_3^2))", "psi_W_(W_2+1)(W_W_4)",
  "psi_W_(W_2+1)(W_(W_4+1))", "psi_W_(W_2+1)(W_W_5)", "psi_W_(W_2+1)(W_W_w)",
  "psi_W_(W_2+1)(W_(W_w+1))", "psi_W_(W_2+1)(W_(W_w*2))", "psi_W_(W_2+1)(W_W_(w+1))",
  "psi_W_(W_2+1)(W_(W_(w+1)+1))", "psi_W_(W_2+1)(W_W_(w+2))", "psi_W_(W_2+1)(W_W_(w2))",
  "psi_W_(W_2+1)(W_W_(w^2))", "psi_W_(W_2+1)(W_W_(w^w))", "psi_W_(W_2+1)(W_W_(w^w+1))",
  "psi_W_(W_2+1)(W_W_psi(W))", "psi_W_(W_2+1)(W_W_psi(W_w))", "psi_W_(W_2+1)(W_W_W)",
  "psi_W_(W_2+1)(W_psi_W_(W_2+1)(W_(W_2+1)))", "psi_W_(W_2+1)(W_psi_W_(W_2+1)(W_W_W))", "psi_W_(W_2+1)(W_psi_W_(W_2+1)(W_psi_W_(W_2+1)(W_(W_2+1))))",
  "psi_W_(W_2+2)(W_(W_2+2))", "psi_W_(W_2+2)(W_(W_2+w))", "psi_W_(W_2+2)(W_(W_2+W))",
  "psi_W_(W_2+2)(W_(W_2*2))", "psi_W_(W_2+2)(W_(W_2*w))", "psi_W_(W_2+2)(W_(W_2*W))",
  "psi_W_(W_2+2)(W_(W_2*W_2))", "psi_W_(W_2+2)(W_(W_2^W_2))", "psi_W_(W_2+2)(W_psi_2(W_3))",
  "psi_W_(W_2+2)(W_psi_2(W_3*2))", "psi_W_(W_2+2)(W_W_3)", "psi_W_(W_2+2)(W_(W_3+1))",
  "psi_W_(W_2+2)(W_(W_3+W))", "psi_W_(W_2+2)(W_(W_3+W_2))", "psi_W_(W_2+2)(W_(W_3*2))",
  "psi_W_(W_2+2)(W_(W_3^2))", "psi_W_(W_2+2)(W_W_4)", "psi_W_(W_2+2)(W_(W_4+1))",
  "psi_W_(W_2+2)(W_W_5)", "psi_W_(W_2+2)(W_W_w)", "psi_W_(W_2+2)(W_(W_w+1))",
  "psi_W_(W_2+2)(W_(W_w*2))", "psi_W_(W_2+2)(W_W_(w+1))", "psi_W_(W_2+2)(W_(W_(w+1)+1))",
  "psi_W_(W_2+2)(W_W_(w+2))", "psi_W_(W_2+2)(W_W_(w2))", "psi_W_(W_2+2)(W_W_(w^2))",
  "psi_W_(W_2+2)(W_W_(w^w))", "psi_W_(W_2+2)(W_W_(w^w+1))", "psi_W_(W_2+2)(W_W_psi(W))",
  "psi_W_(W_2+2)(W_W_psi(W_w))", "psi_W_(W_2+2)(W_W_W)", "psi_W_(W_2+2)(W_psi_W_(W_2+2)(W_(W_2+2)))",
  "psi_W_(W_2+2)(W_psi_W_(W_2+2)(W_W_W))", "psi_W_(W_2+2)(W_psi_W_(W_2+2)(W_psi_W_(W_2+2)(W_(W_2+2))))", "psi_W_(W_2+W+1)(W_(W_2*2))",
  "psi_W_(W_2+W+1)(W_(W_2*w))", "psi_W_(W_2+W+1)(W_(W_2*W))", "psi_W_(W_2+W+1)(W_(W_2*W_2))",
  "psi_W_(W_2+W+1)(W_(W_2^W_2))", "psi_W_(W_2+W+1)(W_psi_2(W_3))", "psi_W_(W_2+W+1)(W_psi_2(W_3*2))",
  "psi_W_(W_2+W+1)(W_W_3)", "psi_W_(W_2+W+1)(W_(W_3+1))", "psi_W_(W_2+W+1)(W_(W_3+W))",
  "psi_W_(W_2+W+1)(W_(W_3+W_2))", "psi_W_(W_2+W+1)(W_(W_3*2))", "psi_W_(W_2+W+1)(W_(W_3^2))",
  "psi_W_(W_2+W+1)(W_W_4)", "psi_W_(W_2+W+1)(W_(W_4+1))", "psi_W_(W_2+W+1)(W_W_5)",
  "psi_W_(W_2+W+1)(W_W_w)", "psi_W_(W_2+W+1)(W_(W_w+1))", "psi_W_(W_2+W+1)(W_(W_w*2))",
  "psi_W_(W_2+W+1)(W_W_(w+1))", "psi_W_(W_2+W+1)(W_(W_(w+1)+1))", "psi_W_(W_2+W+1)(W_W_(w+2))",
  "psi_W_(W_2+W+1)(W_W_(w2))", "psi_W_(W_2+W+1)(W_W_(w^2))", "psi_W_(W_2+W+1)(W_W_(w^w))",
  "psi_W_(W_2+W+1)(W_W_(w^w+1))", "psi_W_(W_2+W+1)(W_W_psi(W))", "psi_W_(W_2+W+1)(W_W_psi(W_w))",
  "psi_W_(W_2+W+1)(W_W_W)", "psi_W_(W_2*2+1)(W_(W_2*w))", "psi_W_(W_2*2+1)(W_(W_2*W))",
  "psi_W_(W_2*2+1)(W_(W_2*W_2))", "psi_W_(W_2*2+1)(W_(W_2^W_2))", "psi_W_(W_2*2+1)(W_psi_2(W_3))",
  "psi_W_(W_2*2+1)(W_psi_2(W_3*2))", "psi_W_(W_2*2+1)(W_W_3)", "psi_W_(W_2*2+1)(W_(W_3+1))",
  "psi_W_(W_2*2+1)(W_(W_3+W))", "psi_W_(W_2*2+1)(W_(W_3+W_2))", "psi_W_(W_2*2+1)(W_(W_3*2))",
  "psi_W_(W_2*2+1)(W_(W_3^2))", "psi_W_(W_2*2+1)(W_W_4)", "psi_W_(W_2*2+1)(W_(W_4+1))",
  "psi_W_(W_2*2+1)(W_W_5)", "psi_W_(W_2*2+1)(W_W_w)", "psi_W_(W_2*2+1)(W_(W_w+1))",
  "psi_W_(W_2*2+1)(W_(W_w*2))", "psi_W_(W_2*2+1)(W_W_(w+1))", "psi_W_(W_2*2+1)(W_(W_(w+1)+1))",
  "psi_W_(W_2*2+1)(W_W_(w+2))", "psi_W_(W_2*2+1)(W_W_(w2))", "psi_W_(W_2*2+1)(W_W_(w^2))",
  "psi_W_(W_2*2+1)(W_W_(w^w))", "psi_W_(W_2*2+1)(W_W_(w^w+1))", "psi_W_(W_2*2+1)(W_W_psi(W))",
  "psi_W_(W_2*2+1)(W_W_psi(W_w))", "psi_W_(W_2*2+1)(W_W_W)", "psi_W_(W_2*2+1)(W_psi_W_(W_2*2+1)(W_(W_2*2+1)))",
  "psi_W_(W_2*2+1)(W_psi_W_(W_2*2+1)(W_W_W))", "psi_W_(W_2*2+1)(W_psi_W_(W_2*2+1)(W_psi_W_(W_2*2+1)(W_(W_2*2+1))))", "psi_W_(W_3+1)(W_(W_3+1))",
  "psi_W_(W_3+1)(W_(W_3+W))", "psi_W_(W_3+1)(W_(W_3+W_2))", "psi_W_(W_3+1)(W_(W_3*2))",
  "psi_W_(W_3+1)(W_(W_3^2))", "psi_W_(W_3+1)(W_W_4)", "psi_W_(W_3+1)(W_(W_4+1))",
  "psi_W_(W_3+1)(W_W_5)", "psi_W_(W_3+1)(W_W_w)", "psi_W_(W_3+1)(W_(W_w+1))",
  "psi_W_(W_3+1)(W_(W_w*2))", "psi_W_(W_3+1)(W_W_(w+1))", "psi_W_(W_3+1)(W_(W_(w+1)+1))",
  "psi_W_(W_3+1)(W_W_(w+2))", "psi_W_(W_3+1)(W_W_(w2))", "psi_W_(W_3+1)(W_W_(w^2))",
  "psi_W_(W_3+1)(W_W_(w^w))", "psi_W_(W_3+1)(W_W_(w^w+1))", "psi_W_(W_3+1)(W_W_psi(W))",
  "psi_W_(W_3+1)(W_W_psi(W_w))", "psi_W_(W_3+1)(W_W_W)", "psi_W_(W_3+1)(W_psi_W_(W_3+1)(W_(W_3+1)))",
  "psi_W_(W_3+1)(W_psi_W_(W_3+1)(W_W_W))", "psi_W_(W_3+1)(W_psi_W_(W_3+1)(W_psi_W_(W_3+1)(W_(W_3+1))))", "psi_W_(W_4+1)(W_(W_4+1))",
  "psi_W_(W_4+1)(W_W_5)", "psi_W_(W_4+1)(W_W_w)", "psi_W_(W_4+1)(W_(W_w+1))",
  "psi_W_(W_4+1)(W_(W_w*2))", "psi_W_(W_4+1)(W_W_(w+1))", "psi_W_(W_4+1)(W_(W_(w+1)+1))",
  "psi_W_(W_4+1)(W_W_(w+2))", "psi_W_(W_4+1)(W_W_(w2))", "psi_W_(W_4+1)(W_W_(w^2))",
  "psi_W_(W_4+1)(W_W_(w^w))", "psi_W_(W_4+1)(W_W_(w^w+1))", "psi_W_(W_4+1)(W_W_psi(W))",
  "psi_W_(W_4+1)(W_W_psi(W_w))", "psi_W_(W_4+1)(W_W_W)", "psi_W_(W_w+1)(W_(W_w+1))",
  "psi_W_(W_W+1)(W_(W_W+1))"]

#guard fixUDomain.length = 562
#guard fixUDomain.all fun s => labelInDomain ((parse s).getD []) && labelInDomainU2 ((parse s).getD [])
#guard fixUDomain.all fun s => u2Of s == uOf s

/-! ## Part 3: (a) `u = Ω+k`, `w ≥ Ω_{Ω+1}`, an upgrade mark at the end

Fix U (= rules 1–10 here) shifts the mark `Ω_Ω` of `M(w)`, `(2,2,1)(3,2,1)(4,1,0)`, with the
tail; Fix K keeps it where it stands in `M(w)` and in `base`. -/

-- The mark of `M(Ω_{Ω+1}+Ω_Ω)` hangs from the storey anchor `(1,1,0)` (index 7).
#guard (uOf "(W_(W+1)+W_W)").drop 26 = [[2,2,1],[3,2,1],[4,1,0]]
#guard (uOf "(W_(W+1)+W_W)").take 8 = (u2Of "psi_W_(W+2)(W_W_(W+1))").take 8
#guard (uOf "psi_W_(W+2)(W_(W_(W+1)+W_W))").drop 29 = [[5,2,1],[6,2,1],[7,1,0]]
#guard u2Of "psi_W_(W+2)(W_(W_(W+1)+W_W))" =
  (uOf "psi_W_(W+2)(W_(W_(W+1)+W_W))").take 29 ++ [[2,2,1],[3,2,1],[4,1,0]]
#guard (uOf "psi_W_(W+2)(W_(W_(W+1)*W_W))").drop 27 = [[5,2,1],[6,2,1],[7,1,0]]
#guard u2Of "psi_W_(W+2)(W_(W_(W+1)*W_W))" =
  (uOf "psi_W_(W+2)(W_(W_(W+1)*W_W))").take 27 ++ [[2,2,1],[3,2,1],[4,1,0]]
#guard (uOf "psi_W_(W+3)(W_(W_(W+1)+W_W))").drop 33 = [[6,3,1],[7,3,1],[8,1,0]]
#guard u2Of "psi_W_(W+3)(W_(W_(W+1)+W_W))" =
  (uOf "psi_W_(W+3)(W_(W_(W+1)+W_W))").take 33 ++ [[2,2,1],[3,2,1],[4,1,0]]

/-! ## Part 4: (b) the shift row -/

/-- The shift row on rows: `M(w)[8:]` moved right by `k`. -/
def shiftRows (k : Nat) (m : List (List Nat)) : List (List Nat) :=
  (m.drop 8).map fun c => [c.getD 0 0 + k, c.getD 1 0, c.getD 2 0]

-- `L = 2`, `u = Ω_2+1`: after the argument `Ω_Ω` (Fix U's table), `M(w)[8:]` moved by 4.
#guard ["(W_W+1)", "(W_W*2)", "W_(W+1)", "(W_(W+1)+W_W)", "W_psi_1(W_2)", "W_W_2",
    "psi_W_W_2(W_W_W)"].all fun w =>
  u2Of ("psi_W_(W_2+1)(W_" ++ w ++ ")") = u2Of "psi_W_(W_2+1)(W_W_W)" ++ shiftRows 4 (u2Of w)
-- `L = 3`, `u = Ω_3+1`: moved by 5.
#guard ["(W_W+1)", "W_(W+1)", "W_W_2", "(W_W_2+1)", "W_W_3"].all fun w =>
  u2Of ("psi_W_(W_3+1)(W_" ++ w ++ ")") = u2Of "psi_W_(W_3+1)(W_W_W)" ++ shiftRows 5 (u2Of w)
-- The argument `Ω_Ω` is `P ++ (L+1,L+1,1)(L+2,L+1,1)(L+3,1,0)`, unchanged from Fix U.
#guard u2Of "psi_W_(W_2+1)(W_W_W)" = uOf "psi_W_(W_2+1)(W_W_3)" ++ [[3,3,1],[4,3,1],[5,1,0]]
-- Fix U put `Ω_{Ω_2}` below `Ω_3` (`P`); Fix U2 puts it above `Ω_Ω`.
#guard cmpMat (uOf "psi_W_(W_2+1)(W_W_W_2)") (uOf "psi_W_(W_2+1)(W_W_3)") = .lt
#guard cmpMat (u2Of "psi_W_(W_2+1)(W_W_W_2)") (u2Of "psi_W_(W_2+1)(W_W_W)") = .gt
-- Above `Ω_{Ω_2}`: `M(w)` starts with `base`, and Fix K's rule 9 is Fix U's reroot onto `P`.
#guard (uOf "(W_W_2+1)").take 25 = (uOf "psi_W_(W_2+1)(W_W_3)").take 25
#guard u2Of "psi_W_(W_2+1)(W_(W_W_2+1))" = uOf "psi_W_(W_2+1)(W_W_3)" ++ [[9,4,0],[10,5,0]]

/-! ## Part 5: the claimed domain, order -/

/-- The probe labels in `inDomainU2` outside Fix U's 562, whose `M(w)` is standard and in
order (772). -/
def newDomain : List String := [
  "psi_W_(W*2+1)(W_(W_W*W_2))", "psi_W_(W*2+1)(W_psi_1(W_w))", "psi_W_(W*2+1)(W_psi_W_(W+1)(W_(W+2)))",
  "psi_W_(W+1)(W_(W_(w+1)+W_w))", "psi_W_(W+1)(W_(W_(w2)+W_(w+1)))", "psi_W_(W+1)(W_(W_2*2+W))",
  "psi_W_(W+1)(W_(W_2*W+W_2))", "psi_W_(W+1)(W_(W_2+W+1))", "psi_W_(W+1)(W_(W_3+W_2+W))",
  "psi_W_(W+1)(W_(W_4*W_3))", "psi_W_(W+1)(W_(W_W*2+W_2))", "psi_W_(W+1)(W_(W_W*W_2))",
  "psi_W_(W+1)(W_(W_W*W_w))", "psi_W_(W+1)(W_(W_W^W))", "psi_W_(W+1)(W_(W_W^W_2))",
  "psi_W_(W+1)(W_(W_W^W_W+W_W))", "psi_W_(W+1)(W_(W_w*W))", "psi_W_(W+1)(W_(W_w*W_2))",
  "psi_W_(W+1)(W_(W_w+W_3))", "psi_W_(W+1)(W_(W_w^2))", "psi_W_(W+1)(W_psi_1(W_3))",
  "psi_W_(W+1)(W_psi_1(W_w))", "psi_W_(W+1)(W_psi_2(W_4))", "psi_W_(W+1)(W_psi_2(W_w))",
  "psi_W_(W+1)(W_psi_3(W_4))", "psi_W_(W+1)(W_psi_W_(W+1)(W_(W+2)))", "psi_W_(W+1)(W_psi_W_(W+1)(W_(W_W*2)))",
  "psi_W_(W+1)(W_psi_W_2(W_(W*2)))", "psi_W_(W+1)(W_psi_W_2(W_(W+1)))", "psi_W_(W+2)(W_(W_(W+1)*2+W_W))",
  "psi_W_(W+2)(W_(W_(W+1)*W))", "psi_W_(W+2)(W_(W_(W+1)*W_(W+1)))", "psi_W_(W+2)(W_(W_(W+1)*W_(w+1)))",
  "psi_W_(W+2)(W_(W_(W+1)*W_W))", "psi_W_(W+2)(W_(W_(W+1)*W_W*2))", "psi_W_(W+2)(W_(W_(W+1)*W_W+1))",
  "psi_W_(W+2)(W_(W_(W+1)*W_W^2))", "psi_W_(W+2)(W_(W_(W+1)*w))", "psi_W_(W+2)(W_(W_(W+1)+2))",
  "psi_W_(W+2)(W_(W_(W+1)+W))", "psi_W_(W+2)(W_(W_(W+1)+W_(W+1)))", "psi_W_(W+2)(W_(W_(W+1)+W_(W+1)*W_W))",
  "psi_W_(W+2)(W_(W_(W+1)+W_(w+1)))", "psi_W_(W+2)(W_(W_(W+1)+W_(w2)))", "psi_W_(W+2)(W_(W_(W+1)+W_W))",
  "psi_W_(W+2)(W_(W_(W+1)+W_W*2))", "psi_W_(W+2)(W_(W_(W+1)+W_W+1))", "psi_W_(W+2)(W_(W_(W+1)+W_W+W_2))",
  "psi_W_(W+2)(W_(W_(W+1)+W_W^2))", "psi_W_(W+2)(W_(W_(W+1)+W_W^W_W))", "psi_W_(W+2)(W_(W_(W+1)+w))",
  "psi_W_(W+2)(W_(W_(W+1)^2))", "psi_W_(W+2)(W_(W_(W+1)^2+W_W))", "psi_W_(W+2)(W_(W_w*W))",
  "psi_W_(W+2)(W_psi_1(W_3))", "psi_W_(W+2)(W_psi_W_(W+1)(W_(W_W*2)))", "psi_W_(W+2)(W_psi_W_(W+2)(W_(W_(W+1)*W)))",
  "psi_W_(W+2)(W_psi_W_(W+2)(W_(W_(W+1)+1)))", "psi_W_(W+2)(W_psi_W_(W+2)(W_psi_W_(W+1)(W_W_W)))", "psi_W_(W+3)(W_(W_(W+1)*2+W_W))",
  "psi_W_(W+3)(W_(W_(W+1)*W))", "psi_W_(W+3)(W_(W_(W+1)*W_(W+1)))", "psi_W_(W+3)(W_(W_(W+1)*W_(w+1)))",
  "psi_W_(W+3)(W_(W_(W+1)*W_W))", "psi_W_(W+3)(W_(W_(W+1)*W_W*2))", "psi_W_(W+3)(W_(W_(W+1)*W_W+1))",
  "psi_W_(W+3)(W_(W_(W+1)*W_W^2))", "psi_W_(W+3)(W_(W_(W+1)+W))", "psi_W_(W+3)(W_(W_(W+1)+W_(W+1)))",
  "psi_W_(W+3)(W_(W_(W+1)+W_(W+1)*W_W))", "psi_W_(W+3)(W_(W_(W+1)+W_(w+1)))", "psi_W_(W+3)(W_(W_(W+1)+W_(w2)))",
  "psi_W_(W+3)(W_(W_(W+1)+W_W))", "psi_W_(W+3)(W_(W_(W+1)+W_W*2))", "psi_W_(W+3)(W_(W_(W+1)+W_W+1))",
  "psi_W_(W+3)(W_(W_(W+1)+W_W+W_2))", "psi_W_(W+3)(W_(W_(W+1)+W_W^2))", "psi_W_(W+3)(W_(W_(W+1)+W_W^W_W))",
  "psi_W_(W+3)(W_(W_(W+1)+w))", "psi_W_(W+3)(W_(W_(W+1)^2))", "psi_W_(W+3)(W_(W_(W+1)^2+W_W))",
  "psi_W_(W+3)(W_(W_(W+2)*W_(W+1)))", "psi_W_(W+3)(W_(W_(W+2)*W_W))", "psi_W_(W+3)(W_(W_(W+2)+W))",
  "psi_W_(W+3)(W_(W_(W+2)+W_(W+1)))", "psi_W_(W+3)(W_(W_(W+2)+W_(W+1)*W_W))", "psi_W_(W+3)(W_(W_(W+2)+W_(W+1)+W_W))",
  "psi_W_(W+3)(W_(W_(W+2)+W_2))", "psi_W_(W+3)(W_(W_(W+2)+W_W))", "psi_W_(W+3)(W_(W_(W+2)^2))",
  "psi_W_(W+3)(W_psi_W_(W+3)(W_(W_(W+2)+1)))", "psi_W_(W+3)(W_psi_W_(W+3)(W_W_(W+2)))", "psi_W_(W+4)(W_(W_(W+1)*2))",
  "psi_W_(W+4)(W_(W_(W+1)*2+W_W))", "psi_W_(W+4)(W_(W_(W+1)*W_(w+1)))", "psi_W_(W+4)(W_(W_(W+1)*W_W))",
  "psi_W_(W+4)(W_(W_(W+1)*W_W*2))", "psi_W_(W+4)(W_(W_(W+1)*W_W+1))", "psi_W_(W+4)(W_(W_(W+1)*W_W^2))",
  "psi_W_(W+4)(W_(W_(W+1)+W_(W+1)*W_W))", "psi_W_(W+4)(W_(W_(W+1)+W_(w+1)))", "psi_W_(W+4)(W_(W_(W+1)+W_(w2)))",
  "psi_W_(W+4)(W_(W_(W+1)+W_W))", "psi_W_(W+4)(W_(W_(W+1)+W_W*2))", "psi_W_(W+4)(W_(W_(W+1)+W_W+1))",
  "psi_W_(W+4)(W_(W_(W+1)+W_W+W_2))", "psi_W_(W+4)(W_(W_(W+1)+W_W^2))", "psi_W_(W+4)(W_(W_(W+1)+W_W^W_W))",
  "psi_W_(W+4)(W_(W_(W+1)^2))", "psi_W_(W+4)(W_(W_(W+1)^2+W_W))", "psi_W_(W+4)(W_(W_(W+2)*W_W))",
  "psi_W_(W+4)(W_(W_(W+2)+W_(W+1)))", "psi_W_(W+4)(W_(W_(W+2)+W_(W+1)*W_W))", "psi_W_(W+4)(W_(W_(W+2)+W_(W+1)+W_W))",
  "psi_W_(W+4)(W_(W_(W+2)+W_2))", "psi_W_(W+4)(W_(W_(W+2)+W_W))", "psi_W_(W+4)(W_W_(W+1))",
  "psi_W_(W+4)(W_W_(W+2))", "psi_W_(W+w+1)(W_(W_W*W_2))", "psi_W_(W+w+1)(W_(W_w^2))",
  "psi_W_(W+w+1)(W_psi_1(W_3))", "psi_W_(W+w+1)(W_psi_1(W_w))", "psi_W_(W_2*2+1)(W_(W_(W*2+1)*2))",
  "psi_W_(W_2*2+1)(W_(W_(W*2+1)+1))", "psi_W_(W_2*2+1)(W_(W_(W+1)*2))", "psi_W_(W_2*2+1)(W_(W_(W+1)+1))",
  "psi_W_(W_2*2+1)(W_(W_(W+2)*2))", "psi_W_(W_2*2+1)(W_(W_(W+2)+1))", "psi_W_(W_2*2+1)(W_(W_(W+3)*2))",
  "psi_W_(W_2*2+1)(W_(W_(W+3)+1))", "psi_W_(W_2*2+1)(W_(W_(W+w)*2))", "psi_W_(W_2*2+1)(W_(W_(W+w)+1))",
  "psi_W_(W_2*2+1)(W_(W_(W^2+1)*2))", "psi_W_(W_2*2+1)(W_(W_(W^2+1)+1))", "psi_W_(W_2*2+1)(W_(W_W*2))",
  "psi_W_(W_2*2+1)(W_(W_W*2+1))", "psi_W_(W_2*2+1)(W_(W_W*W))", "psi_W_(W_2*2+1)(W_(W_W*w))",
  "psi_W_(W_2*2+1)(W_(W_W+1))", "psi_W_(W_2*2+1)(W_(W_W+2))", "psi_W_(W_2*2+1)(W_(W_W+W))",
  "psi_W_(W_2*2+1)(W_(W_W+W_2))", "psi_W_(W_2*2+1)(W_(W_W+W_w))", "psi_W_(W_2*2+1)(W_(W_W+w))",
  "psi_W_(W_2*2+1)(W_(W_W^2))", "psi_W_(W_2*2+1)(W_(W_W^W_W))", "psi_W_(W_2*2+1)(W_(W_W_2*2))",
  "psi_W_(W_2*2+1)(W_(W_W_2+1))", "psi_W_(W_2*2+1)(W_W_(W*2))", "psi_W_(W_2*2+1)(W_W_(W*2+1))",
  "psi_W_(W_2*2+1)(W_W_(W+1))", "psi_W_(W_2*2+1)(W_W_(W+2))", "psi_W_(W_2*2+1)(W_W_(W+3))",
  "psi_W_(W_2*2+1)(W_W_(W+w))", "psi_W_(W_2*2+1)(W_W_(W^2+1))", "psi_W_(W_2*2+1)(W_W_W_2)",
  "psi_W_(W_2*2+1)(W_W_psi_1(W_2))", "psi_W_(W_2*2+1)(W_W_psi_W_2(W_W))", "psi_W_(W_2*2+1)(W_psi_W_(W*2)(W_(W*2)))",
  "psi_W_(W_2*2+1)(W_psi_W_(W*2)(W_(W_W+1)))", "psi_W_(W_2*2+1)(W_psi_W_(W*2)(W_W_(W+1)))", "psi_W_(W_2*2+1)(W_psi_W_(W*2)(W_W_2))",
  "psi_W_(W_2*2+1)(W_psi_W_(W*2)(W_W_W))", "psi_W_(W_2*2+1)(W_psi_W_(W*2)(W_psi_W_(W*2)(W_(W*2))))", "psi_W_(W_2*2+1)(W_psi_W_(W*2+1)(W_(W*2+1)))",
  "psi_W_(W_2*2+1)(W_psi_W_(W*2+1)(W_(W_W+1)))", "psi_W_(W_2*2+1)(W_psi_W_(W*2+1)(W_W_(W+1)))", "psi_W_(W_2*2+1)(W_psi_W_(W*2+1)(W_W_2))",
  "psi_W_(W_2*2+1)(W_psi_W_(W*2+1)(W_W_W))", "psi_W_(W_2*2+1)(W_psi_W_(W*2+1)(W_psi_W_(W*2+1)(W_(W*2+1))))", "psi_W_(W_2*2+1)(W_psi_W_(W+1)(W_(W+1)))",
  "psi_W_(W_2*2+1)(W_psi_W_(W+1)(W_(W_W+1)))", "psi_W_(W_2*2+1)(W_psi_W_(W+1)(W_W_2))", "psi_W_(W_2*2+1)(W_psi_W_(W+1)(W_W_W))",
  "psi_W_(W_2*2+1)(W_psi_W_(W+1)(W_psi_W_(W+1)(W_(W+1))))", "psi_W_(W_2*2+1)(W_psi_W_(W+2)(W_(W+2)))", "psi_W_(W_2*2+1)(W_psi_W_(W+2)(W_(W_W+1)))",
  "psi_W_(W_2*2+1)(W_psi_W_(W+2)(W_W_(W+1)))", "psi_W_(W_2*2+1)(W_psi_W_(W+2)(W_W_2))", "psi_W_(W_2*2+1)(W_psi_W_(W+2)(W_W_W))",
  "psi_W_(W_2*2+1)(W_psi_W_(W+2)(W_psi_W_(W+2)(W_(W+2))))", "psi_W_(W_2*2+1)(W_psi_W_(W+3)(W_(W+3)))", "psi_W_(W_2*2+1)(W_psi_W_(W+3)(W_(W_W+1)))",
  "psi_W_(W_2*2+1)(W_psi_W_(W+3)(W_W_(W+1)))", "psi_W_(W_2*2+1)(W_psi_W_(W+3)(W_W_2))", "psi_W_(W_2*2+1)(W_psi_W_(W+3)(W_W_W))",
  "psi_W_(W_2*2+1)(W_psi_W_(W+3)(W_psi_W_(W+3)(W_(W+3))))", "psi_W_(W_2*2+1)(W_psi_W_(W^2+1)(W_(W^2+1)))", "psi_W_(W_2*2+1)(W_psi_W_(W^2+1)(W_(W_W+1)))",
  "psi_W_(W_2*2+1)(W_psi_W_(W^2+1)(W_W_2))", "psi_W_(W_2*2+1)(W_psi_W_(W^2+1)(W_W_W))", "psi_W_(W_2*2+1)(W_psi_W_(W_2+1)(W_(W_2+1)))",
  "psi_W_(W_2*2+1)(W_psi_W_(W_2+1)(W_(W_W+1)))", "psi_W_(W_2*2+1)(W_psi_W_(W_2+1)(W_W_(W+1)))", "psi_W_(W_2*2+1)(W_psi_W_(W_2+1)(W_W_W))",
  "psi_W_(W_2*2+1)(W_psi_W_(W_2+1)(W_W_W_2))", "psi_W_(W_2*2+1)(W_psi_W_(W_2+1)(W_psi_W_(W_2+1)(W_(W_2+1))))", "psi_W_(W_2*2+1)(W_psi_W_W_2(W_(W_W+1)))",
  "psi_W_(W_2*2+1)(W_psi_W_W_2(W_W_(W+1)))", "psi_W_(W_2*2+1)(W_psi_W_W_2(W_W_W))", "psi_W_(W_2*2+1)(W_psi_W_W_2(W_psi_W_W_2(W_W_2)))",
  "psi_W_(W_2*2+1)(W_psi_W_psi_W_2(W_W)(W_(W_W+1)))", "psi_W_(W_2*2+1)(W_psi_W_psi_W_2(W_W)(W_W_(W+1)))", "psi_W_(W_2*2+1)(W_psi_W_psi_W_2(W_W)(W_W_2))",
  "psi_W_(W_2*2+1)(W_psi_W_psi_W_2(W_W)(W_W_W))", "psi_W_(W_2*2+1)(W_psi_W_psi_W_2(W_W)(W_psi_W_2(W_W)))", "psi_W_(W_2*2+1)(W_psi_W_psi_W_2(W_W)(W_psi_W_psi_W_2(W_W)(W_psi_W_2(W_W))))",
  "psi_W_(W_2+1)(W_(W_(W*2+1)*2))", "psi_W_(W_2+1)(W_(W_(W*2+1)+1))", "psi_W_(W_2+1)(W_(W_(W+1)*2))",
  "psi_W_(W_2+1)(W_(W_(W+1)*W_W))", "psi_W_(W_2+1)(W_(W_(W+1)+1))", "psi_W_(W_2+1)(W_(W_(W+1)+W_(W+1)))",
  "psi_W_(W_2+1)(W_(W_(W+1)+W_W))", "psi_W_(W_2+1)(W_(W_(W+2)*2))", "psi_W_(W_2+1)(W_(W_(W+2)+1))",
  "psi_W_(W_2+1)(W_(W_(W+3)*2))", "psi_W_(W_2+1)(W_(W_(W+3)+1))", "psi_W_(W_2+1)(W_(W_(W+w)*2))",
  "psi_W_(W_2+1)(W_(W_(W+w)+1))", "psi_W_(W_2+1)(W_(W_(W^2+1)*2))", "psi_W_(W_2+1)(W_(W_(W^2+1)+1))",
  "psi_W_(W_2+1)(W_(W_(w+1)*W_3))", "psi_W_(W_2+1)(W_(W_(w+1)+W_w))", "psi_W_(W_2+1)(W_(W_3*W_2))",
  "psi_W_(W_2+1)(W_(W_3*w))", "psi_W_(W_2+1)(W_(W_3+W_2+W+1))", "psi_W_(W_2+1)(W_(W_3^W_3))",
  "psi_W_(W_2+1)(W_(W_4*W_3))", "psi_W_(W_2+1)(W_(W_4+W_3))", "psi_W_(W_2+1)(W_(W_4^W_4))",
  "psi_W_(W_2+1)(W_(W_5+W_4))", "psi_W_(W_2+1)(W_(W_W*2))", "psi_W_(W_2+1)(W_(W_W*2+1))",
  "psi_W_(W_2+1)(W_(W_W*W))", "psi_W_(W_2+1)(W_(W_W*w))", "psi_W_(W_2+1)(W_(W_W+1))",
  "psi_W_(W_2+1)(W_(W_W+2))", "psi_W_(W_2+1)(W_(W_W+W))", "psi_W_(W_2+1)(W_(W_W+W_2))",
  "psi_W_(W_2+1)(W_(W_W+W_W))", "psi_W_(W_2+1)(W_(W_W+W_w))", "psi_W_(W_2+1)(W_(W_W+w))",
  "psi_W_(W_2+1)(W_(W_W^2))", "psi_W_(W_2+1)(W_(W_W^W_W))", "psi_W_(W_2+1)(W_(W_W_2*2))",
  "psi_W_(W_2+1)(W_(W_W_2*W_W))", "psi_W_(W_2+1)(W_(W_W_2+1))", "psi_W_(W_2+1)(W_(W_W_2+W))",
  "psi_W_(W_2+1)(W_(W_W_2+W_(W+1)))", "psi_W_(W_2+1)(W_(W_W_2+W_W))", "psi_W_(W_2+1)(W_(W_W_2^2))",
  "psi_W_(W_2+1)(W_(W_W_2^W_W_2))", "psi_W_(W_2+1)(W_(W_w*W))", "psi_W_(W_2+1)(W_(W_w*W_2))",
  "psi_W_(W_2+1)(W_(W_w*W_3))", "psi_W_(W_2+1)(W_(W_w+W_3))", "psi_W_(W_2+1)(W_(W_w^2))",
  "psi_W_(W_2+1)(W_W_(W*2))", "psi_W_(W_2+1)(W_W_(W*2+1))", "psi_W_(W_2+1)(W_W_(W+1))",
  "psi_W_(W_2+1)(W_W_(W+2))", "psi_W_(W_2+1)(W_W_(W+3))", "psi_W_(W_2+1)(W_W_(W+w))",
  "psi_W_(W_2+1)(W_W_(W^2))", "psi_W_(W_2+1)(W_W_(W^2+1))", "psi_W_(W_2+1)(W_W_(W^W))",
  "psi_W_(W_2+1)(W_W_W_2)", "psi_W_(W_2+1)(W_W_psi_1(W_2))", "psi_W_(W_2+1)(W_W_psi_W_2(W_W))",
  "psi_W_(W_2+1)(W_psi_2(W_W))", "psi_W_(W_2+1)(W_psi_2(W_w))", "psi_W_(W_2+1)(W_psi_3(W_4))",
  "psi_W_(W_2+1)(W_psi_4(W_5))", "psi_W_(W_2+1)(W_psi_W_(W*2)(W_(W*2)))", "psi_W_(W_2+1)(W_psi_W_(W*2)(W_(W_W+1)))",
  "psi_W_(W_2+1)(W_psi_W_(W*2)(W_W_(W+1)))", "psi_W_(W_2+1)(W_psi_W_(W*2)(W_W_2))", "psi_W_(W_2+1)(W_psi_W_(W*2)(W_W_W))",
  "psi_W_(W_2+1)(W_psi_W_(W*2)(W_psi_W_(W*2)(W_(W*2))))", "psi_W_(W_2+1)(W_psi_W_(W*2+1)(W_(W*2+1)))", "psi_W_(W_2+1)(W_psi_W_(W*2+1)(W_(W_W+1)))",
  "psi_W_(W_2+1)(W_psi_W_(W*2+1)(W_W_(W+1)))", "psi_W_(W_2+1)(W_psi_W_(W*2+1)(W_W_2))", "psi_W_(W_2+1)(W_psi_W_(W*2+1)(W_W_W))",
  "psi_W_(W_2+1)(W_psi_W_(W*2+1)(W_psi_W_(W*2+1)(W_(W*2+1))))", "psi_W_(W_2+1)(W_psi_W_(W+1)(W_(W+1)))", "psi_W_(W_2+1)(W_psi_W_(W+1)(W_(W_W+1)))",
  "psi_W_(W_2+1)(W_psi_W_(W+1)(W_W_2))", "psi_W_(W_2+1)(W_psi_W_(W+1)(W_W_W))", "psi_W_(W_2+1)(W_psi_W_(W+1)(W_psi_W_(W+1)(W_(W+1))))",
  "psi_W_(W_2+1)(W_psi_W_(W+2)(W_(W+2)))", "psi_W_(W_2+1)(W_psi_W_(W+2)(W_(W_W+1)))", "psi_W_(W_2+1)(W_psi_W_(W+2)(W_W_(W+1)))",
  "psi_W_(W_2+1)(W_psi_W_(W+2)(W_W_2))", "psi_W_(W_2+1)(W_psi_W_(W+2)(W_W_W))", "psi_W_(W_2+1)(W_psi_W_(W+2)(W_psi_W_(W+2)(W_(W+2))))",
  "psi_W_(W_2+1)(W_psi_W_(W+3)(W_(W+3)))", "psi_W_(W_2+1)(W_psi_W_(W+3)(W_(W_W+1)))", "psi_W_(W_2+1)(W_psi_W_(W+3)(W_W_(W+1)))",
  "psi_W_(W_2+1)(W_psi_W_(W+3)(W_W_2))", "psi_W_(W_2+1)(W_psi_W_(W+3)(W_W_W))", "psi_W_(W_2+1)(W_psi_W_(W+3)(W_psi_W_(W+3)(W_(W+3))))",
  "psi_W_(W_2+1)(W_psi_W_(W^2+1)(W_(W^2+1)))", "psi_W_(W_2+1)(W_psi_W_(W^2+1)(W_(W_W+1)))", "psi_W_(W_2+1)(W_psi_W_(W^2+1)(W_W_2))",
  "psi_W_(W_2+1)(W_psi_W_(W^2+1)(W_W_W))", "psi_W_(W_2+1)(W_psi_W_(W_2+1)(W_(W_W+1)))", "psi_W_(W_2+1)(W_psi_W_(W_2+1)(W_W_(W+1)))",
  "psi_W_(W_2+1)(W_psi_W_(W_2+1)(W_W_W_2))", "psi_W_(W_2+1)(W_psi_W_W_2(W_(W_W+1)))", "psi_W_(W_2+1)(W_psi_W_W_2(W_W_(W+1)))",
  "psi_W_(W_2+1)(W_psi_W_W_2(W_W_W))", "psi_W_(W_2+1)(W_psi_W_W_2(W_psi_W_W_2(W_W_2)))", "psi_W_(W_2+1)(W_psi_W_psi_W_2(W_W)(W_(W_W+1)))",
  "psi_W_(W_2+1)(W_psi_W_psi_W_2(W_W)(W_W_(W+1)))", "psi_W_(W_2+1)(W_psi_W_psi_W_2(W_W)(W_W_2))", "psi_W_(W_2+1)(W_psi_W_psi_W_2(W_W)(W_W_W))",
  "psi_W_(W_2+1)(W_psi_W_psi_W_2(W_W)(W_psi_W_2(W_W)))", "psi_W_(W_2+1)(W_psi_W_psi_W_2(W_W)(W_psi_W_psi_W_2(W_W)(W_psi_W_2(W_W))))", "psi_W_(W_2+2)(W_(W_(W*2+1)*2))",
  "psi_W_(W_2+2)(W_(W_(W*2+1)+1))", "psi_W_(W_2+2)(W_(W_(W+1)*2))", "psi_W_(W_2+2)(W_(W_(W+1)*W_W))",
  "psi_W_(W_2+2)(W_(W_(W+1)+1))", "psi_W_(W_2+2)(W_(W_(W+1)+W_(W+1)))", "psi_W_(W_2+2)(W_(W_(W+1)+W_W))",
  "psi_W_(W_2+2)(W_(W_(W+2)*2))", "psi_W_(W_2+2)(W_(W_(W+2)+1))", "psi_W_(W_2+2)(W_(W_(W+3)*2))",
  "psi_W_(W_2+2)(W_(W_(W+3)+1))", "psi_W_(W_2+2)(W_(W_(W+w)*2))", "psi_W_(W_2+2)(W_(W_(W+w)+1))",
  "psi_W_(W_2+2)(W_(W_(W^2+1)*2))", "psi_W_(W_2+2)(W_(W_(W^2+1)+1))", "psi_W_(W_2+2)(W_(W_(W_2+1)*2))",
  "psi_W_(W_2+2)(W_(W_(W_2+1)+1))", "psi_W_(W_2+2)(W_(W_4*W_3))", "psi_W_(W_2+2)(W_(W_W*2))",
  "psi_W_(W_2+2)(W_(W_W*2+1))", "psi_W_(W_2+2)(W_(W_W*W))", "psi_W_(W_2+2)(W_(W_W*w))",
  "psi_W_(W_2+2)(W_(W_W+1))", "psi_W_(W_2+2)(W_(W_W+2))", "psi_W_(W_2+2)(W_(W_W+W))",
  "psi_W_(W_2+2)(W_(W_W+W_2))", "psi_W_(W_2+2)(W_(W_W+W_W))", "psi_W_(W_2+2)(W_(W_W+W_w))",
  "psi_W_(W_2+2)(W_(W_W+w))", "psi_W_(W_2+2)(W_(W_W^2))", "psi_W_(W_2+2)(W_(W_W^W_W))",
  "psi_W_(W_2+2)(W_(W_W_2*2))", "psi_W_(W_2+2)(W_(W_W_2*W_W))", "psi_W_(W_2+2)(W_(W_W_2+1))",
  "psi_W_(W_2+2)(W_(W_W_2+W))", "psi_W_(W_2+2)(W_(W_W_2+W_(W+1)))", "psi_W_(W_2+2)(W_(W_W_2+W_W))",
  "psi_W_(W_2+2)(W_(W_W_2^2))", "psi_W_(W_2+2)(W_(W_W_2^W_W_2))", "psi_W_(W_2+2)(W_(W_w*W))",
  "psi_W_(W_2+2)(W_(W_w+W_3))", "psi_W_(W_2+2)(W_W_(W*2))", "psi_W_(W_2+2)(W_W_(W*2+1))",
  "psi_W_(W_2+2)(W_W_(W+1))", "psi_W_(W_2+2)(W_W_(W+2))", "psi_W_(W_2+2)(W_W_(W+3))",
  "psi_W_(W_2+2)(W_W_(W+w))", "psi_W_(W_2+2)(W_W_(W^2))", "psi_W_(W_2+2)(W_W_(W^2+1))",
  "psi_W_(W_2+2)(W_W_(W^W))", "psi_W_(W_2+2)(W_W_(W_2+1))", "psi_W_(W_2+2)(W_W_W_2)",
  "psi_W_(W_2+2)(W_W_psi_1(W_2))", "psi_W_(W_2+2)(W_W_psi_W_2(W_W))", "psi_W_(W_2+2)(W_psi_2(W_w))",
  "psi_W_(W_2+2)(W_psi_3(W_4))", "psi_W_(W_2+2)(W_psi_W_(W*2)(W_(W*2)))", "psi_W_(W_2+2)(W_psi_W_(W*2)(W_(W_W+1)))",
  "psi_W_(W_2+2)(W_psi_W_(W*2)(W_W_(W+1)))", "psi_W_(W_2+2)(W_psi_W_(W*2)(W_W_2))", "psi_W_(W_2+2)(W_psi_W_(W*2)(W_W_W))",
  "psi_W_(W_2+2)(W_psi_W_(W*2)(W_psi_W_(W*2)(W_(W*2))))", "psi_W_(W_2+2)(W_psi_W_(W*2+1)(W_(W*2+1)))", "psi_W_(W_2+2)(W_psi_W_(W*2+1)(W_(W_W+1)))",
  "psi_W_(W_2+2)(W_psi_W_(W*2+1)(W_W_(W+1)))", "psi_W_(W_2+2)(W_psi_W_(W*2+1)(W_W_2))", "psi_W_(W_2+2)(W_psi_W_(W*2+1)(W_W_W))",
  "psi_W_(W_2+2)(W_psi_W_(W*2+1)(W_psi_W_(W*2+1)(W_(W*2+1))))", "psi_W_(W_2+2)(W_psi_W_(W+1)(W_(W+1)))", "psi_W_(W_2+2)(W_psi_W_(W+1)(W_(W_W+1)))",
  "psi_W_(W_2+2)(W_psi_W_(W+1)(W_W_2))", "psi_W_(W_2+2)(W_psi_W_(W+1)(W_W_W))", "psi_W_(W_2+2)(W_psi_W_(W+1)(W_psi_W_(W+1)(W_(W+1))))",
  "psi_W_(W_2+2)(W_psi_W_(W+2)(W_(W+2)))", "psi_W_(W_2+2)(W_psi_W_(W+2)(W_(W_W+1)))", "psi_W_(W_2+2)(W_psi_W_(W+2)(W_W_(W+1)))",
  "psi_W_(W_2+2)(W_psi_W_(W+2)(W_W_2))", "psi_W_(W_2+2)(W_psi_W_(W+2)(W_W_W))", "psi_W_(W_2+2)(W_psi_W_(W+2)(W_psi_W_(W+2)(W_(W+2))))",
  "psi_W_(W_2+2)(W_psi_W_(W+3)(W_(W+3)))", "psi_W_(W_2+2)(W_psi_W_(W+3)(W_(W_W+1)))", "psi_W_(W_2+2)(W_psi_W_(W+3)(W_W_(W+1)))",
  "psi_W_(W_2+2)(W_psi_W_(W+3)(W_W_2))", "psi_W_(W_2+2)(W_psi_W_(W+3)(W_W_W))", "psi_W_(W_2+2)(W_psi_W_(W+3)(W_psi_W_(W+3)(W_(W+3))))",
  "psi_W_(W_2+2)(W_psi_W_(W^2+1)(W_(W^2+1)))", "psi_W_(W_2+2)(W_psi_W_(W^2+1)(W_(W_W+1)))", "psi_W_(W_2+2)(W_psi_W_(W^2+1)(W_W_2))",
  "psi_W_(W_2+2)(W_psi_W_(W^2+1)(W_W_W))", "psi_W_(W_2+2)(W_psi_W_(W_2+1)(W_(W_2+1)))", "psi_W_(W_2+2)(W_psi_W_(W_2+1)(W_(W_W+1)))",
  "psi_W_(W_2+2)(W_psi_W_(W_2+1)(W_W_(W+1)))", "psi_W_(W_2+2)(W_psi_W_(W_2+1)(W_W_W))", "psi_W_(W_2+2)(W_psi_W_(W_2+1)(W_W_W_2))",
  "psi_W_(W_2+2)(W_psi_W_(W_2+1)(W_psi_W_(W_2+1)(W_(W_2+1))))", "psi_W_(W_2+2)(W_psi_W_(W_2+2)(W_(W_W+1)))", "psi_W_(W_2+2)(W_psi_W_(W_2+2)(W_W_(W+1)))",
  "psi_W_(W_2+2)(W_psi_W_(W_2+2)(W_W_W_2))", "psi_W_(W_2+2)(W_psi_W_W_2(W_(W_W+1)))", "psi_W_(W_2+2)(W_psi_W_W_2(W_W_(W+1)))",
  "psi_W_(W_2+2)(W_psi_W_W_2(W_W_W))", "psi_W_(W_2+2)(W_psi_W_W_2(W_psi_W_W_2(W_W_2)))", "psi_W_(W_2+2)(W_psi_W_psi_W_2(W_W)(W_(W_W+1)))",
  "psi_W_(W_2+2)(W_psi_W_psi_W_2(W_W)(W_W_(W+1)))", "psi_W_(W_2+2)(W_psi_W_psi_W_2(W_W)(W_W_2))", "psi_W_(W_2+2)(W_psi_W_psi_W_2(W_W)(W_W_W))",
  "psi_W_(W_2+2)(W_psi_W_psi_W_2(W_W)(W_psi_W_2(W_W)))", "psi_W_(W_2+2)(W_psi_W_psi_W_2(W_W)(W_psi_W_psi_W_2(W_W)(W_psi_W_2(W_W))))", "psi_W_(W_2+W+1)(W_(W_(W*2+1)*2))",
  "psi_W_(W_2+W+1)(W_(W_(W*2+1)+1))", "psi_W_(W_2+W+1)(W_(W_(W+1)*2))", "psi_W_(W_2+W+1)(W_(W_(W+1)+1))",
  "psi_W_(W_2+W+1)(W_(W_(W+2)*2))", "psi_W_(W_2+W+1)(W_(W_(W+2)+1))", "psi_W_(W_2+W+1)(W_(W_(W+3)*2))",
  "psi_W_(W_2+W+1)(W_(W_(W+3)+1))", "psi_W_(W_2+W+1)(W_(W_(W+w)*2))", "psi_W_(W_2+W+1)(W_(W_(W+w)+1))",
  "psi_W_(W_2+W+1)(W_(W_(W^2+1)*2))", "psi_W_(W_2+W+1)(W_(W_(W^2+1)+1))", "psi_W_(W_2+W+1)(W_(W_W*2))",
  "psi_W_(W_2+W+1)(W_(W_W*2+1))", "psi_W_(W_2+W+1)(W_(W_W*W))", "psi_W_(W_2+W+1)(W_(W_W*w))",
  "psi_W_(W_2+W+1)(W_(W_W+1))", "psi_W_(W_2+W+1)(W_(W_W+2))", "psi_W_(W_2+W+1)(W_(W_W+W))",
  "psi_W_(W_2+W+1)(W_(W_W+W_2))", "psi_W_(W_2+W+1)(W_(W_W+W_w))", "psi_W_(W_2+W+1)(W_(W_W+w))",
  "psi_W_(W_2+W+1)(W_(W_W^2))", "psi_W_(W_2+W+1)(W_(W_W^W_W))", "psi_W_(W_2+W+1)(W_(W_W_2*2))",
  "psi_W_(W_2+W+1)(W_(W_W_2+1))", "psi_W_(W_2+W+1)(W_W_(W*2))", "psi_W_(W_2+W+1)(W_W_(W*2+1))",
  "psi_W_(W_2+W+1)(W_W_(W+1))", "psi_W_(W_2+W+1)(W_W_(W+2))", "psi_W_(W_2+W+1)(W_W_(W+3))",
  "psi_W_(W_2+W+1)(W_W_(W+w))", "psi_W_(W_2+W+1)(W_W_(W^2+1))", "psi_W_(W_2+W+1)(W_W_W_2)",
  "psi_W_(W_2+W+1)(W_W_psi_1(W_2))", "psi_W_(W_2+W+1)(W_W_psi_W_2(W_W))", "psi_W_(W_2+W+1)(W_psi_W_(W*2)(W_(W*2)))",
  "psi_W_(W_2+W+1)(W_psi_W_(W*2)(W_(W_W+1)))", "psi_W_(W_2+W+1)(W_psi_W_(W*2)(W_W_(W+1)))", "psi_W_(W_2+W+1)(W_psi_W_(W*2)(W_W_2))",
  "psi_W_(W_2+W+1)(W_psi_W_(W*2)(W_W_W))", "psi_W_(W_2+W+1)(W_psi_W_(W*2)(W_psi_W_(W*2)(W_(W*2))))", "psi_W_(W_2+W+1)(W_psi_W_(W*2+1)(W_(W*2+1)))",
  "psi_W_(W_2+W+1)(W_psi_W_(W*2+1)(W_(W_W+1)))", "psi_W_(W_2+W+1)(W_psi_W_(W*2+1)(W_W_(W+1)))", "psi_W_(W_2+W+1)(W_psi_W_(W*2+1)(W_W_2))",
  "psi_W_(W_2+W+1)(W_psi_W_(W*2+1)(W_W_W))", "psi_W_(W_2+W+1)(W_psi_W_(W*2+1)(W_psi_W_(W*2+1)(W_(W*2+1))))", "psi_W_(W_2+W+1)(W_psi_W_(W+1)(W_(W+1)))",
  "psi_W_(W_2+W+1)(W_psi_W_(W+1)(W_(W_W+1)))", "psi_W_(W_2+W+1)(W_psi_W_(W+1)(W_W_2))", "psi_W_(W_2+W+1)(W_psi_W_(W+1)(W_W_W))",
  "psi_W_(W_2+W+1)(W_psi_W_(W+1)(W_psi_W_(W+1)(W_(W+1))))", "psi_W_(W_2+W+1)(W_psi_W_(W+2)(W_(W+2)))", "psi_W_(W_2+W+1)(W_psi_W_(W+2)(W_(W_W+1)))",
  "psi_W_(W_2+W+1)(W_psi_W_(W+2)(W_W_(W+1)))", "psi_W_(W_2+W+1)(W_psi_W_(W+2)(W_W_2))", "psi_W_(W_2+W+1)(W_psi_W_(W+2)(W_W_W))",
  "psi_W_(W_2+W+1)(W_psi_W_(W+2)(W_psi_W_(W+2)(W_(W+2))))", "psi_W_(W_2+W+1)(W_psi_W_(W+3)(W_(W+3)))", "psi_W_(W_2+W+1)(W_psi_W_(W+3)(W_(W_W+1)))",
  "psi_W_(W_2+W+1)(W_psi_W_(W+3)(W_W_(W+1)))", "psi_W_(W_2+W+1)(W_psi_W_(W+3)(W_W_2))", "psi_W_(W_2+W+1)(W_psi_W_(W+3)(W_W_W))",
  "psi_W_(W_2+W+1)(W_psi_W_(W+3)(W_psi_W_(W+3)(W_(W+3))))", "psi_W_(W_2+W+1)(W_psi_W_(W^2+1)(W_(W^2+1)))", "psi_W_(W_2+W+1)(W_psi_W_(W^2+1)(W_(W_W+1)))",
  "psi_W_(W_2+W+1)(W_psi_W_(W^2+1)(W_W_2))", "psi_W_(W_2+W+1)(W_psi_W_(W^2+1)(W_W_W))", "psi_W_(W_2+W+1)(W_psi_W_(W_2+1)(W_(W_2+1)))",
  "psi_W_(W_2+W+1)(W_psi_W_(W_2+1)(W_(W_W+1)))", "psi_W_(W_2+W+1)(W_psi_W_(W_2+1)(W_W_(W+1)))", "psi_W_(W_2+W+1)(W_psi_W_(W_2+1)(W_W_W))",
  "psi_W_(W_2+W+1)(W_psi_W_(W_2+1)(W_W_W_2))", "psi_W_(W_2+W+1)(W_psi_W_(W_2+1)(W_psi_W_(W_2+1)(W_(W_2+1))))", "psi_W_(W_2+W+1)(W_psi_W_W_2(W_(W_W+1)))",
  "psi_W_(W_2+W+1)(W_psi_W_W_2(W_W_(W+1)))", "psi_W_(W_2+W+1)(W_psi_W_W_2(W_W_W))", "psi_W_(W_2+W+1)(W_psi_W_W_2(W_psi_W_W_2(W_W_2)))",
  "psi_W_(W_2+W+1)(W_psi_W_psi_W_2(W_W)(W_(W_W+1)))", "psi_W_(W_2+W+1)(W_psi_W_psi_W_2(W_W)(W_W_(W+1)))", "psi_W_(W_2+W+1)(W_psi_W_psi_W_2(W_W)(W_W_2))",
  "psi_W_(W_2+W+1)(W_psi_W_psi_W_2(W_W)(W_W_W))", "psi_W_(W_2+W+1)(W_psi_W_psi_W_2(W_W)(W_psi_W_2(W_W)))", "psi_W_(W_2+W+1)(W_psi_W_psi_W_2(W_W)(W_psi_W_psi_W_2(W_W)(W_psi_W_2(W_W))))",
  "psi_W_(W_3+1)(W_(W_(W*2+1)*2))", "psi_W_(W_3+1)(W_(W_(W*2+1)+1))", "psi_W_(W_3+1)(W_(W_(W+1)*2))",
  "psi_W_(W_3+1)(W_(W_(W+1)*W_W))", "psi_W_(W_3+1)(W_(W_(W+1)+1))", "psi_W_(W_3+1)(W_(W_(W+1)+W_(W+1)))",
  "psi_W_(W_3+1)(W_(W_(W+1)+W_W))", "psi_W_(W_3+1)(W_(W_(W+2)*2))", "psi_W_(W_3+1)(W_(W_(W+2)+1))",
  "psi_W_(W_3+1)(W_(W_(W+3)*2))", "psi_W_(W_3+1)(W_(W_(W+3)+1))", "psi_W_(W_3+1)(W_(W_(W+w)*2))",
  "psi_W_(W_3+1)(W_(W_(W+w)+1))", "psi_W_(W_3+1)(W_(W_(W^2+1)*2))", "psi_W_(W_3+1)(W_(W_(W^2+1)+1))",
  "psi_W_(W_3+1)(W_(W_(W_2*2+1)*2))", "psi_W_(W_3+1)(W_(W_(W_2*2+1)+1))", "psi_W_(W_3+1)(W_(W_(W_2+1)*2))",
  "psi_W_(W_3+1)(W_(W_(W_2+1)+1))", "psi_W_(W_3+1)(W_(W_(W_2+2)*2))", "psi_W_(W_3+1)(W_(W_(W_2+2)+1))",
  "psi_W_(W_3+1)(W_(W_5*W_4))", "psi_W_(W_3+1)(W_(W_5+W_4))", "psi_W_(W_3+1)(W_(W_W*2))",
  "psi_W_(W_3+1)(W_(W_W*2+1))", "psi_W_(W_3+1)(W_(W_W*W))", "psi_W_(W_3+1)(W_(W_W*w))",
  "psi_W_(W_3+1)(W_(W_W+1))", "psi_W_(W_3+1)(W_(W_W+2))", "psi_W_(W_3+1)(W_(W_W+W))",
  "psi_W_(W_3+1)(W_(W_W+W_2))", "psi_W_(W_3+1)(W_(W_W+W_W))", "psi_W_(W_3+1)(W_(W_W+W_w))",
  "psi_W_(W_3+1)(W_(W_W+w))", "psi_W_(W_3+1)(W_(W_W^2))", "psi_W_(W_3+1)(W_(W_W^W_W))",
  "psi_W_(W_3+1)(W_(W_W_2*2))", "psi_W_(W_3+1)(W_(W_W_2*W_W))", "psi_W_(W_3+1)(W_(W_W_2+1))",
  "psi_W_(W_3+1)(W_(W_W_2+W))", "psi_W_(W_3+1)(W_(W_W_2+W_(W+1)))", "psi_W_(W_3+1)(W_(W_W_2+W_W))",
  "psi_W_(W_3+1)(W_(W_W_2^2))", "psi_W_(W_3+1)(W_(W_W_2^W_W_2))", "psi_W_(W_3+1)(W_(W_W_3*2))",
  "psi_W_(W_3+1)(W_(W_W_3+1))", "psi_W_(W_3+1)(W_(W_w*W_3))", "psi_W_(W_3+1)(W_(W_w+W_4))",
  "psi_W_(W_3+1)(W_W_(W*2))", "psi_W_(W_3+1)(W_W_(W*2+1))", "psi_W_(W_3+1)(W_W_(W+1))",
  "psi_W_(W_3+1)(W_W_(W+2))", "psi_W_(W_3+1)(W_W_(W+3))", "psi_W_(W_3+1)(W_W_(W+w))",
  "psi_W_(W_3+1)(W_W_(W^2))", "psi_W_(W_3+1)(W_W_(W^2+1))", "psi_W_(W_3+1)(W_W_(W^W))",
  "psi_W_(W_3+1)(W_W_(W_2*2))", "psi_W_(W_3+1)(W_W_(W_2*2+1))", "psi_W_(W_3+1)(W_W_(W_2+1))",
  "psi_W_(W_3+1)(W_W_(W_2+2))", "psi_W_(W_3+1)(W_W_W_2)", "psi_W_(W_3+1)(W_W_W_3)",
  "psi_W_(W_3+1)(W_W_psi_1(W_2))", "psi_W_(W_3+1)(W_W_psi_W_2(W_W))", "psi_W_(W_3+1)(W_psi_3(W_4))",
  "psi_W_(W_3+1)(W_psi_3(W_w))", "psi_W_(W_3+1)(W_psi_4(W_5))", "psi_W_(W_3+1)(W_psi_W_(W*2)(W_(W*2)))",
  "psi_W_(W_3+1)(W_psi_W_(W*2)(W_(W_W+1)))", "psi_W_(W_3+1)(W_psi_W_(W*2)(W_W_(W+1)))", "psi_W_(W_3+1)(W_psi_W_(W*2)(W_W_2))",
  "psi_W_(W_3+1)(W_psi_W_(W*2)(W_W_W))", "psi_W_(W_3+1)(W_psi_W_(W*2)(W_psi_W_(W*2)(W_(W*2))))", "psi_W_(W_3+1)(W_psi_W_(W*2+1)(W_(W*2+1)))",
  "psi_W_(W_3+1)(W_psi_W_(W*2+1)(W_(W_W+1)))", "psi_W_(W_3+1)(W_psi_W_(W*2+1)(W_W_(W+1)))", "psi_W_(W_3+1)(W_psi_W_(W*2+1)(W_W_2))",
  "psi_W_(W_3+1)(W_psi_W_(W*2+1)(W_W_W))", "psi_W_(W_3+1)(W_psi_W_(W*2+1)(W_psi_W_(W*2+1)(W_(W*2+1))))", "psi_W_(W_3+1)(W_psi_W_(W+1)(W_(W+1)))",
  "psi_W_(W_3+1)(W_psi_W_(W+1)(W_(W_W+1)))", "psi_W_(W_3+1)(W_psi_W_(W+1)(W_W_2))", "psi_W_(W_3+1)(W_psi_W_(W+1)(W_W_W))",
  "psi_W_(W_3+1)(W_psi_W_(W+1)(W_psi_W_(W+1)(W_(W+1))))", "psi_W_(W_3+1)(W_psi_W_(W+2)(W_(W+2)))", "psi_W_(W_3+1)(W_psi_W_(W+2)(W_(W_W+1)))",
  "psi_W_(W_3+1)(W_psi_W_(W+2)(W_W_(W+1)))", "psi_W_(W_3+1)(W_psi_W_(W+2)(W_W_2))", "psi_W_(W_3+1)(W_psi_W_(W+2)(W_W_W))",
  "psi_W_(W_3+1)(W_psi_W_(W+2)(W_psi_W_(W+2)(W_(W+2))))", "psi_W_(W_3+1)(W_psi_W_(W+3)(W_(W+3)))", "psi_W_(W_3+1)(W_psi_W_(W+3)(W_(W_W+1)))",
  "psi_W_(W_3+1)(W_psi_W_(W+3)(W_W_(W+1)))", "psi_W_(W_3+1)(W_psi_W_(W+3)(W_W_2))", "psi_W_(W_3+1)(W_psi_W_(W+3)(W_W_W))",
  "psi_W_(W_3+1)(W_psi_W_(W+3)(W_psi_W_(W+3)(W_(W+3))))", "psi_W_(W_3+1)(W_psi_W_(W^2+1)(W_(W^2+1)))", "psi_W_(W_3+1)(W_psi_W_(W^2+1)(W_(W_W+1)))",
  "psi_W_(W_3+1)(W_psi_W_(W^2+1)(W_W_2))", "psi_W_(W_3+1)(W_psi_W_(W^2+1)(W_W_W))", "psi_W_(W_3+1)(W_psi_W_(W_2*2+1)(W_(W_2*2+1)))",
  "psi_W_(W_3+1)(W_psi_W_(W_2*2+1)(W_(W_W+1)))", "psi_W_(W_3+1)(W_psi_W_(W_2*2+1)(W_W_(W+1)))", "psi_W_(W_3+1)(W_psi_W_(W_2*2+1)(W_W_W))",
  "psi_W_(W_3+1)(W_psi_W_(W_2*2+1)(W_W_W_2))", "psi_W_(W_3+1)(W_psi_W_(W_2*2+1)(W_psi_W_(W_2*2+1)(W_(W_2*2+1))))", "psi_W_(W_3+1)(W_psi_W_(W_2+1)(W_(W_2+1)))",
  "psi_W_(W_3+1)(W_psi_W_(W_2+1)(W_(W_W+1)))", "psi_W_(W_3+1)(W_psi_W_(W_2+1)(W_W_(W+1)))", "psi_W_(W_3+1)(W_psi_W_(W_2+1)(W_W_W))",
  "psi_W_(W_3+1)(W_psi_W_(W_2+1)(W_W_W_2))", "psi_W_(W_3+1)(W_psi_W_(W_2+1)(W_psi_W_(W_2+1)(W_(W_2+1))))", "psi_W_(W_3+1)(W_psi_W_(W_2+2)(W_(W_2+2)))",
  "psi_W_(W_3+1)(W_psi_W_(W_2+2)(W_(W_W+1)))", "psi_W_(W_3+1)(W_psi_W_(W_2+2)(W_W_(W+1)))", "psi_W_(W_3+1)(W_psi_W_(W_2+2)(W_W_W))",
  "psi_W_(W_3+1)(W_psi_W_(W_2+2)(W_W_W_2))", "psi_W_(W_3+1)(W_psi_W_(W_2+2)(W_psi_W_(W_2+2)(W_(W_2+2))))", "psi_W_(W_3+1)(W_psi_W_(W_3+1)(W_(W_W+1)))",
  "psi_W_(W_3+1)(W_psi_W_(W_3+1)(W_W_(W+1)))", "psi_W_(W_3+1)(W_psi_W_(W_3+1)(W_W_W_2))", "psi_W_(W_3+1)(W_psi_W_4(W_W))",
  "psi_W_(W_3+1)(W_psi_W_W_2(W_(W_W+1)))", "psi_W_(W_3+1)(W_psi_W_W_2(W_W_(W+1)))", "psi_W_(W_3+1)(W_psi_W_W_2(W_W_W))",
  "psi_W_(W_3+1)(W_psi_W_W_2(W_psi_W_W_2(W_W_2)))", "psi_W_(W_3+1)(W_psi_W_W_3(W_W_3))", "psi_W_(W_3+1)(W_psi_W_W_3(W_W_W))",
  "psi_W_(W_3+1)(W_psi_W_W_3(W_W_W_2))", "psi_W_(W_3+1)(W_psi_W_W_3(W_psi_W_W_3(W_W_3)))", "psi_W_(W_3+1)(W_psi_W_psi_W_2(W_W)(W_(W_W+1)))",
  "psi_W_(W_3+1)(W_psi_W_psi_W_2(W_W)(W_W_(W+1)))", "psi_W_(W_3+1)(W_psi_W_psi_W_2(W_W)(W_W_2))", "psi_W_(W_3+1)(W_psi_W_psi_W_2(W_W)(W_W_W))",
  "psi_W_(W_3+1)(W_psi_W_psi_W_2(W_W)(W_psi_W_2(W_W)))", "psi_W_(W_3+1)(W_psi_W_psi_W_2(W_W)(W_psi_W_psi_W_2(W_W)(W_psi_W_2(W_W))))", "psi_W_(W_4+1)(W_(W_(W*2+1)*2))",
  "psi_W_(W_4+1)(W_(W_(W*2+1)+1))", "psi_W_(W_4+1)(W_(W_(W+1)*2))", "psi_W_(W_4+1)(W_(W_(W+1)+1))",
  "psi_W_(W_4+1)(W_(W_(W+2)*2))", "psi_W_(W_4+1)(W_(W_(W+2)+1))", "psi_W_(W_4+1)(W_(W_(W+3)*2))",
  "psi_W_(W_4+1)(W_(W_(W+3)+1))", "psi_W_(W_4+1)(W_(W_(W+w)*2))", "psi_W_(W_4+1)(W_(W_(W+w)+1))",
  "psi_W_(W_4+1)(W_(W_(W^2+1)*2))", "psi_W_(W_4+1)(W_(W_(W^2+1)+1))", "psi_W_(W_4+1)(W_(W_(W_2*2+1)*2))",
  "psi_W_(W_4+1)(W_(W_(W_2*2+1)+1))", "psi_W_(W_4+1)(W_(W_(W_2+1)*2))", "psi_W_(W_4+1)(W_(W_(W_2+1)+1))",
  "psi_W_(W_4+1)(W_(W_(W_2+2)*2))", "psi_W_(W_4+1)(W_(W_(W_2+2)+1))", "psi_W_(W_4+1)(W_(W_(W_3+1)*2))",
  "psi_W_(W_4+1)(W_(W_(W_3+1)+1))", "psi_W_(W_4+1)(W_(W_W*2))", "psi_W_(W_4+1)(W_(W_W*2+1))",
  "psi_W_(W_4+1)(W_(W_W*W))", "psi_W_(W_4+1)(W_(W_W*w))", "psi_W_(W_4+1)(W_(W_W+1))",
  "psi_W_(W_4+1)(W_(W_W+2))", "psi_W_(W_4+1)(W_(W_W+W))", "psi_W_(W_4+1)(W_(W_W+W_2))",
  "psi_W_(W_4+1)(W_(W_W+W_w))", "psi_W_(W_4+1)(W_(W_W+w))", "psi_W_(W_4+1)(W_(W_W^2))",
  "psi_W_(W_4+1)(W_(W_W^W_W))", "psi_W_(W_4+1)(W_(W_W_2*2))", "psi_W_(W_4+1)(W_(W_W_2+1))",
  "psi_W_(W_4+1)(W_(W_W_3*2))", "psi_W_(W_4+1)(W_(W_W_3+1))", "psi_W_(W_4+1)(W_W_(W*2))",
  "psi_W_(W_4+1)(W_W_(W*2+1))", "psi_W_(W_4+1)(W_W_(W+1))", "psi_W_(W_4+1)(W_W_(W+2))",
  "psi_W_(W_4+1)(W_W_(W+3))", "psi_W_(W_4+1)(W_W_(W+w))", "psi_W_(W_4+1)(W_W_(W^2+1))",
  "psi_W_(W_4+1)(W_W_(W_2*2+1))", "psi_W_(W_4+1)(W_W_(W_2+1))", "psi_W_(W_4+1)(W_W_(W_2+2))",
  "psi_W_(W_4+1)(W_W_(W_3+1))", "psi_W_(W_4+1)(W_W_W_2)", "psi_W_(W_4+1)(W_W_W_3)",
  "psi_W_(W_4+1)(W_W_psi_1(W_2))", "psi_W_(W_4+1)(W_W_psi_W_2(W_W))", "psi_W_(W_4+1)(W_psi_W_(W*2)(W_(W*2)))",
  "psi_W_(W_4+1)(W_psi_W_(W*2)(W_(W_W+1)))", "psi_W_(W_4+1)(W_psi_W_(W*2)(W_W_(W+1)))", "psi_W_(W_4+1)(W_psi_W_(W*2)(W_W_2))",
  "psi_W_(W_4+1)(W_psi_W_(W*2)(W_W_W))", "psi_W_(W_4+1)(W_psi_W_(W*2)(W_psi_W_(W*2)(W_(W*2))))", "psi_W_(W_4+1)(W_psi_W_(W*2+1)(W_(W*2+1)))",
  "psi_W_(W_4+1)(W_psi_W_(W*2+1)(W_(W_W+1)))", "psi_W_(W_4+1)(W_psi_W_(W*2+1)(W_W_(W+1)))", "psi_W_(W_4+1)(W_psi_W_(W*2+1)(W_W_2))",
  "psi_W_(W_4+1)(W_psi_W_(W*2+1)(W_W_W))", "psi_W_(W_4+1)(W_psi_W_(W*2+1)(W_psi_W_(W*2+1)(W_(W*2+1))))", "psi_W_(W_4+1)(W_psi_W_(W+1)(W_(W+1)))",
  "psi_W_(W_4+1)(W_psi_W_(W+1)(W_(W_W+1)))", "psi_W_(W_4+1)(W_psi_W_(W+1)(W_W_2))", "psi_W_(W_4+1)(W_psi_W_(W+1)(W_W_W))",
  "psi_W_(W_4+1)(W_psi_W_(W+1)(W_psi_W_(W+1)(W_(W+1))))", "psi_W_(W_4+1)(W_psi_W_(W+2)(W_(W+2)))", "psi_W_(W_4+1)(W_psi_W_(W+2)(W_(W_W+1)))",
  "psi_W_(W_4+1)(W_psi_W_(W+2)(W_W_(W+1)))", "psi_W_(W_4+1)(W_psi_W_(W+2)(W_W_2))", "psi_W_(W_4+1)(W_psi_W_(W+2)(W_W_W))",
  "psi_W_(W_4+1)(W_psi_W_(W+2)(W_psi_W_(W+2)(W_(W+2))))", "psi_W_(W_4+1)(W_psi_W_(W+3)(W_(W+3)))", "psi_W_(W_4+1)(W_psi_W_(W+3)(W_(W_W+1)))",
  "psi_W_(W_4+1)(W_psi_W_(W+3)(W_W_(W+1)))", "psi_W_(W_4+1)(W_psi_W_(W+3)(W_W_2))", "psi_W_(W_4+1)(W_psi_W_(W+3)(W_W_W))",
  "psi_W_(W_4+1)(W_psi_W_(W+3)(W_psi_W_(W+3)(W_(W+3))))", "psi_W_(W_4+1)(W_psi_W_(W^2+1)(W_(W^2+1)))", "psi_W_(W_4+1)(W_psi_W_(W^2+1)(W_(W_W+1)))",
  "psi_W_(W_4+1)(W_psi_W_(W^2+1)(W_W_2))", "psi_W_(W_4+1)(W_psi_W_(W^2+1)(W_W_W))", "psi_W_(W_4+1)(W_psi_W_(W_2*2+1)(W_(W_2*2+1)))",
  "psi_W_(W_4+1)(W_psi_W_(W_2*2+1)(W_(W_W+1)))", "psi_W_(W_4+1)(W_psi_W_(W_2*2+1)(W_W_(W+1)))", "psi_W_(W_4+1)(W_psi_W_(W_2*2+1)(W_W_W))",
  "psi_W_(W_4+1)(W_psi_W_(W_2*2+1)(W_W_W_2))", "psi_W_(W_4+1)(W_psi_W_(W_2*2+1)(W_psi_W_(W_2*2+1)(W_(W_2*2+1))))", "psi_W_(W_4+1)(W_psi_W_(W_2+1)(W_(W_2+1)))",
  "psi_W_(W_4+1)(W_psi_W_(W_2+1)(W_(W_W+1)))", "psi_W_(W_4+1)(W_psi_W_(W_2+1)(W_W_(W+1)))", "psi_W_(W_4+1)(W_psi_W_(W_2+1)(W_W_W))",
  "psi_W_(W_4+1)(W_psi_W_(W_2+1)(W_W_W_2))", "psi_W_(W_4+1)(W_psi_W_(W_2+1)(W_psi_W_(W_2+1)(W_(W_2+1))))", "psi_W_(W_4+1)(W_psi_W_(W_2+2)(W_(W_2+2)))",
  "psi_W_(W_4+1)(W_psi_W_(W_2+2)(W_(W_W+1)))", "psi_W_(W_4+1)(W_psi_W_(W_2+2)(W_W_(W+1)))", "psi_W_(W_4+1)(W_psi_W_(W_2+2)(W_W_W))",
  "psi_W_(W_4+1)(W_psi_W_(W_2+2)(W_W_W_2))", "psi_W_(W_4+1)(W_psi_W_(W_2+2)(W_psi_W_(W_2+2)(W_(W_2+2))))", "psi_W_(W_4+1)(W_psi_W_(W_3+1)(W_(W_3+1)))",
  "psi_W_(W_4+1)(W_psi_W_(W_3+1)(W_(W_W+1)))", "psi_W_(W_4+1)(W_psi_W_(W_3+1)(W_W_(W+1)))", "psi_W_(W_4+1)(W_psi_W_(W_3+1)(W_W_W))",
  "psi_W_(W_4+1)(W_psi_W_(W_3+1)(W_W_W_2))", "psi_W_(W_4+1)(W_psi_W_(W_3+1)(W_psi_W_(W_3+1)(W_(W_3+1))))", "psi_W_(W_4+1)(W_psi_W_W_2(W_(W_W+1)))",
  "psi_W_(W_4+1)(W_psi_W_W_2(W_W_(W+1)))", "psi_W_(W_4+1)(W_psi_W_W_2(W_W_W))", "psi_W_(W_4+1)(W_psi_W_W_2(W_psi_W_W_2(W_W_2)))",
  "psi_W_(W_4+1)(W_psi_W_W_3(W_W_3))", "psi_W_(W_4+1)(W_psi_W_W_3(W_W_W))", "psi_W_(W_4+1)(W_psi_W_W_3(W_W_W_2))",
  "psi_W_(W_4+1)(W_psi_W_W_3(W_psi_W_W_3(W_W_3)))", "psi_W_(W_4+1)(W_psi_W_psi_W_2(W_W)(W_(W_W+1)))", "psi_W_(W_4+1)(W_psi_W_psi_W_2(W_W)(W_W_(W+1)))",
  "psi_W_(W_4+1)(W_psi_W_psi_W_2(W_W)(W_W_2))", "psi_W_(W_4+1)(W_psi_W_psi_W_2(W_W)(W_W_W))", "psi_W_(W_4+1)(W_psi_W_psi_W_2(W_W)(W_psi_W_2(W_W)))",
  "psi_W_(W_4+1)(W_psi_W_psi_W_2(W_W)(W_psi_W_psi_W_2(W_W)(W_psi_W_2(W_W))))"]

#guard newDomain.length = 772
#guard newDomain.all fun s => labelInDomainU2 ((parse s).getD [])

/-- Labels sorted by `cmpOrd` have their matrices in the same order (neighbouring pairs). -/
def sortedAgree (xs : List (Od × List (List Nat))) : Bool :=
  let s := xs.mergeSort fun a b => cmpOrd a.1 b.1 != .gt
  (s.zip s.tail).all fun p => cmpOrd p.1.1 p.2.1 == cmpMat p.1.2 p.2.2

/-- A label with its Fix U2 matrix. -/
def withU2 (ls : List String) : List (Od × List (List Nat)) :=
  ls.map fun s => ((parse s).getD [], u2Of s)

-- The 1,334 labels: matrices in the order of the labels, also with the 784 chosen labels.
#guard sortedAgree (withU2 (fixUDomain ++ newDomain))
#guard sortedAgree (withU2 (fixUDomain ++ newDomain ++ chosen ++ [printed3552]))
-- Without Fix U2 (Fix U's matrices) the order fails on them.
#guard !sortedAgree ((fixUDomain ++ newDomain).map fun s => ((parse s).getD [], uOf s))
-- Fix U2 changes 634 of the 772.
#guard (newDomain.filter fun s => u2Of s != uOf s).length = 634

/-- The 22 labels of (b) that stay wrong (`u = Ω_2+Ω+1`, `Ω_2·2+1`, `w ≥ Ω_{Ω_2+1}`, not
standard): they lie outside the claimed domain. -/
def openB : List String := [
  "psi_W_(W_2*2+1)(W_(W_(W_2+1)*2))",
  "psi_W_(W_2*2+1)(W_(W_(W_2+1)+1))",
  "psi_W_(W_2*2+1)(W_(W_(W_2+2)*2))",
  "psi_W_(W_2*2+1)(W_(W_(W_2+2)+1))",
  "psi_W_(W_2*2+1)(W_W_(W_2+2))",
  "psi_W_(W_2*2+1)(W_psi_W_(W_2+2)(W_(W_2+2)))",
  "psi_W_(W_2*2+1)(W_psi_W_(W_2+2)(W_(W_W+1)))",
  "psi_W_(W_2*2+1)(W_psi_W_(W_2+2)(W_W_(W+1)))",
  "psi_W_(W_2*2+1)(W_psi_W_(W_2+2)(W_W_W))",
  "psi_W_(W_2*2+1)(W_psi_W_(W_2+2)(W_W_W_2))",
  "psi_W_(W_2*2+1)(W_psi_W_(W_2+2)(W_psi_W_(W_2+2)(W_(W_2+2))))",
  "psi_W_(W_2+W+1)(W_(W_(W_2+1)*2))",
  "psi_W_(W_2+W+1)(W_(W_(W_2+1)+1))",
  "psi_W_(W_2+W+1)(W_(W_(W_2+2)*2))",
  "psi_W_(W_2+W+1)(W_(W_(W_2+2)+1))",
  "psi_W_(W_2+W+1)(W_W_(W_2+2))",
  "psi_W_(W_2+W+1)(W_psi_W_(W_2+2)(W_(W_2+2)))",
  "psi_W_(W_2+W+1)(W_psi_W_(W_2+2)(W_(W_W+1)))",
  "psi_W_(W_2+W+1)(W_psi_W_(W_2+2)(W_W_(W+1)))",
  "psi_W_(W_2+W+1)(W_psi_W_(W_2+2)(W_W_W))",
  "psi_W_(W_2+W+1)(W_psi_W_(W_2+2)(W_W_W_2))",
  "psi_W_(W_2+W+1)(W_psi_W_(W_2+2)(W_psi_W_(W_2+2)(W_(W_2+2))))"]

#guard openB.length = 22
#guard openB.all fun s => !labelInDomainU2 ((parse s).getD [])

end Googology.Trans.BMS.TrioFixU2
