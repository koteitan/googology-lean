import Googology.Trans.BMS.TrioFixStrip
import Googology.Trans.BMS.TrioRulesAllSheet
import Googology.Trans.BMS.TrioTree

/-!
# Patch "strip": the checks

`TrioFixStrip.lean` corrects rule 1 (`strip`) of the merged rules (`TrioRulesAll.lean`,
rules 1–10 of [koteitan/trio](https://github.com/koteitan/trio) with Fixes A–E and N),
on top of the reading `ofTermFix` of `TrioFixOfTerm.lean`.  This file re-runs every
check of `TrioRulesAllSheet.lean` (Parts 1–7, `stOf` / `trioRuleMatrixOfSt` in place
of `allOf` / `trioRuleMatrixOfAll`) and the checks of `TrioFixOfTermSheet.lean` on
the map `trioMatrixLFix` (Part 9, `trioMatrixLSt` in place of `trioMatrixLFix`; the
checks there on the old reading `ofTerm` and the old maps are not repeated, and its
127 disagreements of `trioMatrixLFix` become 0), and adds the patch's own
checks (Part 8).  All of it is `#guard`s: a calibration, not a theorem.

* **The sheet** ([`tools/omega_alpha_rows.tsv`](https://github.com/koteitan/trio/blob/main/tools/omega_alpha_rows.tsv)):
  every guard of Parts 1–7 holds unchanged.  The patch changes no label of the
  corpus of `TrioRulesAllSheet.lean` (1,225 labels: the 822 of the sheet, the
  families and the probes): `stOf s = allOf s` on all of them (Part 8), and the
  patched step equals `MstepAll` on each.  So the order checks (783 and 784 chosen
  matrices) give 0 disagreements, as before.
* **Part 8, the patch.**  `strip` and `stripSt` on `ω^{ε₀·ω}`; the matrix of
  `β = ψ_0(ψ_1(ψ_0(Ω + ψ_0(Ω+1))))` is now the tree of the term (the old map's matrix).
* **Part 9, the terms** (the checks of `TrioFixOfTermSheet.lean`).  The 42 terms with
  a sheet row: matrix = the sheet's on all 42, 0 disagreements against the 784.
  `(ε₀·ω)[n] = ε₀·(n+1)`.  `smallFrag 6` (610): 0 disagreements, 0 collisions.  The
  2,397 terms with at most 7 `ψ`s, subscripts `0`/`1`, countable: **0 disagreements
  (was 127), 0 collisions**; the patched map differs from `trioMatrixLFix` only on
  `β`.  Wider families: unchanged (`famC` 75/8, `famU` 0/0, `famW` 63/11, `famO`
  137/29); on all four the patched map equals `trioMatrixLFix` term by term, so their
  failures are other defects of the builder.
* **Standard forms** (yaBMS `bms -s`, run outside Lean on the matrices of Part 9):
  all 2,397 matrices of the 7-`ψ` family are standard (with `trioMatrixLFix`: all
  but `β`'s).  Wider families as with `trioMatrixLFix`: `famC` 2 of 483 distinct not
  standard, `famU` 0 of 524, `famW` 30 of 527, `famO` 59 of 512.

## The files

The checks are split so that each file checks in a few minutes on a loaded machine:
`TrioFixStripSheet.lean` (this file: the summary and the first rows of Part 1),
`TrioFixStripSheet1b.lean` … `TrioFixStripSheet1h.lean` (the other rows of Part 1;
the last one has its order check), `TrioFixStripSheet2.lean` (Parts 2–8),
`TrioFixStripSheet9.lean`, `TrioFixStripSheet9Frag7.lean`,
`TrioFixStripSheet9Wide.lean` (Part 9).  Each imports only `TrioFixStrip` and tracked
modules; the few shared definitions (`chosenDataSt`, `chosenDataSt3`, the term
families) are repeated where needed.
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


/-! ## Part 1: the guards of `TrioRules2Sheet.lean`, for the merged rules -/

/-! ### The 744 rows where rules 1–10 and the sheet agree -/

#guard trioRuleMatrixOfSt "1" -- row 31
  = some [[0,0,0],[1,1,0]]
#guard trioRuleMatrixOfSt "2" -- row 180
  = some [[0,0,0],[1,1,0],[2,2,0]]
#guard trioRuleMatrixOfSt "3" -- row 241
  = some [[0,0,0],[1,1,0],[2,2,0],[3,3,0]]
#guard trioRuleMatrixOfSt "4" -- row 261
  = some [[0,0,0],[1,1,0],[2,2,0],[3,3,0],[4,4,0]]
#guard trioRuleMatrixOfSt "5" -- row 265
  = some [[0,0,0],[1,1,0],[2,2,0],[3,3,0],[4,4,0],[5,5,0]]
#guard trioRuleMatrixOfSt "6" -- row 266
  = some [[0,0,0],[1,1,0],[2,2,0],[3,3,0],[4,4,0],[5,5,0],[6,6,0]]
#guard trioRuleMatrixOfSt "w" -- row 267
  = some [[0,0,0],[1,1,1]]
#guard trioRuleMatrixOfSt "(w+1)" -- row 780
  = some [[0,0,0],[1,1,1],[2,1,0],[3,2,0]]
#guard trioRuleMatrixOfSt "(w+2)" -- row 913
  = some [[0,0,0],[1,1,1],[2,1,0],[3,2,0],[4,3,0]]
#guard trioRuleMatrixOfSt "(w+3)" -- row 966
  = some [[0,0,0],[1,1,1],[2,1,0],[3,2,0],[4,3,0],[5,4,0]]
#guard trioRuleMatrixOfSt "(w+4)" -- row 983
  = some [[0,0,0],[1,1,1],[2,1,0],[3,2,0],[4,3,0],[5,4,0],[6,5,0]]
#guard trioRuleMatrixOfSt "(w+5)" -- row 986
  = some [[0,0,0],[1,1,1],[2,1,0],[3,2,0],[4,3,0],[5,4,0],[6,5,0],[7,6,0]]
#guard trioRuleMatrixOfSt "(w+6)" -- row 987
  = some [[0,0,0],[1,1,1],[2,1,0],[3,2,0],[4,3,0],[5,4,0],[6,5,0],[7,6,0],[8,7,0]]
#guard trioRuleMatrixOfSt "(w2)" -- row 988
  = some [[0,0,0],[1,1,1],[2,1,0],[3,2,1]]
#guard trioRuleMatrixOfSt "(w2+1)" -- row 1218
  = some [[0,0,0],[1,1,1],[2,1,0],[3,2,1],[4,2,0],[5,3,0]]
#guard trioRuleMatrixOfSt "(w2+2)" -- row 1266
  = some [[0,0,0],[1,1,1],[2,1,0],[3,2,1],[4,2,0],[5,3,0],[6,4,0]]
#guard trioRuleMatrixOfSt "(w2+3)" -- row 1275
  = some [[0,0,0],[1,1,1],[2,1,0],[3,2,1],[4,2,0],[5,3,0],[6,4,0],[7,5,0]]
#guard trioRuleMatrixOfSt "(w2+4)" -- row 1276
  = some [[0,0,0],[1,1,1],[2,1,0],[3,2,1],[4,2,0],[5,3,0],[6,4,0],[7,5,0],[8,6,0]]
#guard trioRuleMatrixOfSt "(w3)" -- row 1277
  = some [[0,0,0],[1,1,1],[2,1,0],[3,2,1],[4,2,0],[5,3,1]]
#guard trioRuleMatrixOfSt "(w3+1)" -- row 1306
  = some [[0,0,0],[1,1,1],[2,1,0],[3,2,1],[4,2,0],[5,3,1],[6,3,0],[7,4,0]]
#guard trioRuleMatrixOfSt "(w3+2)" -- row 1310
  = some [[0,0,0],[1,1,1],[2,1,0],[3,2,1],[4,2,0],[5,3,1],[6,3,0],[7,4,0],[8,5,0]]
#guard trioRuleMatrixOfSt "(w4)" -- row 1311
  = some [[0,0,0],[1,1,1],[2,1,0],[3,2,1],[4,2,0],[5,3,1],[6,3,0],[7,4,1]]
#guard trioRuleMatrixOfSt "(w4+1)" -- row 1314
  = some [[0,0,0],[1,1,1],[2,1,0],[3,2,1],[4,2,0],[5,3,1],[6,3,0],[7,4,1],[8,4,0],[9,5,0]]
#guard trioRuleMatrixOfSt "(w5)" -- row 1315
  = some [[0,0,0],[1,1,1],[2,1,0],[3,2,1],[4,2,0],[5,3,1],[6,3,0],[7,4,1],[8,4,0],[9,5,1]]
#guard trioRuleMatrixOfSt "(w6)" -- row 1316
  = some [[0,0,0],[1,1,1],[2,1,0],[3,2,1],[4,2,0],[5,3,1],[6,3,0],[7,4,1],[8,4,0],[9,5,1],[10,5,0],[11,6,1]]
#guard trioRuleMatrixOfSt "(w^2)" -- row 1317
  = some [[0,0,0],[1,1,1],[2,1,1]]
#guard trioRuleMatrixOfSt "(w^2+1)" -- row 1647
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,0],[3,2,0]]
#guard trioRuleMatrixOfSt "(w^2+2)" -- row 1703
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,0],[3,2,0],[4,3,0]]
#guard trioRuleMatrixOfSt "(w^2+3)" -- row 1711
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,0],[3,2,0],[4,3,0],[5,4,0]]
#guard trioRuleMatrixOfSt "(w^2+4)" -- row 1713
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,0],[3,2,0],[4,3,0],[5,4,0],[6,5,0]]
#guard trioRuleMatrixOfSt "(w^2+5)" -- row 1714
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,0],[3,2,0],[4,3,0],[5,4,0],[6,5,0],[7,6,0]]
#guard trioRuleMatrixOfSt "(w^2+w)" -- row 1715
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,0],[3,2,1]]
#guard trioRuleMatrixOfSt "(w^2+w+1)" -- row 1784
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,0],[3,2,1],[4,2,0],[5,3,0]]
#guard trioRuleMatrixOfSt "(w^2+w+2)" -- row 1801
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,0],[3,2,1],[4,2,0],[5,3,0],[6,4,0]]
#guard trioRuleMatrixOfSt "(w^2+w+3)" -- row 1804
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,0],[3,2,1],[4,2,0],[5,3,0],[6,4,0],[7,5,0]]
#guard trioRuleMatrixOfSt "(w^2+w2)" -- row 1805
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,0],[3,2,1],[4,2,0],[5,3,1]]
#guard trioRuleMatrixOfSt "(w^2+w2+1)" -- row 1823
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,0],[3,2,1],[4,2,0],[5,3,1],[6,3,0],[7,4,0]]
#guard trioRuleMatrixOfSt "(w^2+w2+2)" -- row 1832
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,0],[3,2,1],[4,2,0],[5,3,1],[6,3,0],[7,4,0],[8,5,0]]
#guard trioRuleMatrixOfSt "(w^2+w2+3)" -- row 1833
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,0],[3,2,1],[4,2,0],[5,3,1],[6,3,0],[7,4,0],[8,5,0],[9,6,0]]
#guard trioRuleMatrixOfSt "(w^2+w3)" -- row 1834
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,0],[3,2,1],[4,2,0],[5,3,1],[6,3,0],[7,4,1]]
#guard trioRuleMatrixOfSt "(w^2+w3+1)" -- row 1842
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,0],[3,2,1],[4,2,0],[5,3,1],[6,3,0],[7,4,1],[8,4,0],[9,5,0]]
#guard trioRuleMatrixOfSt "(w^2+w4)" -- row 1843
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,0],[3,2,1],[4,2,0],[5,3,1],[6,3,0],[7,4,1],[8,4,0],[9,5,1]]
#guard trioRuleMatrixOfSt "(w^2+w5)" -- row 1844
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,0],[3,2,1],[4,2,0],[5,3,1],[6,3,0],[7,4,1],[8,4,0],[9,5,1],[10,5,0],[11,6,1]]
#guard trioRuleMatrixOfSt "(w^2*2)" -- row 1845
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,0],[3,2,1],[4,2,1]]
#guard trioRuleMatrixOfSt "(w^2*2+1)" -- row 1895
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,0],[3,2,1],[4,2,1],[4,2,0],[5,3,0]]
#guard trioRuleMatrixOfSt "(w^2*2+2)" -- row 1911
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,0],[3,2,1],[4,2,1],[4,2,0],[5,3,0],[6,4,0]]
#guard trioRuleMatrixOfSt "(w^2*2+3)" -- row 1913
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,0],[3,2,1],[4,2,1],[4,2,0],[5,3,0],[6,4,0],[7,5,0]]
#guard trioRuleMatrixOfSt "(w^2*2+w)" -- row 1914
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,0],[3,2,1],[4,2,1],[4,2,0],[5,3,1]]
#guard trioRuleMatrixOfSt "(w^2*2+w+1)" -- row 1925
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,0],[3,2,1],[4,2,1],[4,2,0],[5,3,1],[6,3,0],[7,4,0]]
#guard trioRuleMatrixOfSt "(w^2*2+w+2)" -- row 1927
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,0],[3,2,1],[4,2,1],[4,2,0],[5,3,1],[6,3,0],[7,4,0],[8,5,0]]
#guard trioRuleMatrixOfSt "(w^2*2+w2)" -- row 1928
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,0],[3,2,1],[4,2,1],[4,2,0],[5,3,1],[6,3,0],[7,4,1]]
#guard trioRuleMatrixOfSt "(w^2*2+w3)" -- row 1929
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,0],[3,2,1],[4,2,1],[4,2,0],[5,3,1],[6,3,0],[7,4,1],[8,4,0],[9,5,1]]
#guard trioRuleMatrixOfSt "(w^2*3)" -- row 1930
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,0],[3,2,1],[4,2,1],[4,2,0],[5,3,1],[6,3,1]]
#guard trioRuleMatrixOfSt "(w^2*3+1)" -- row 1939
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,0],[3,2,1],[4,2,1],[4,2,0],[5,3,1],[6,3,1],[6,3,0],[7,4,0]]
#guard trioRuleMatrixOfSt "(w^2*3+2)" -- row 1940
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,0],[3,2,1],[4,2,1],[4,2,0],[5,3,1],[6,3,1],[6,3,0],[7,4,0],[8,5,0]]
#guard trioRuleMatrixOfSt "(w^2*3+w)" -- row 1941
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,0],[3,2,1],[4,2,1],[4,2,0],[5,3,1],[6,3,1],[6,3,0],[7,4,1]]
#guard trioRuleMatrixOfSt "(w^2*3+w2)" -- row 1942
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,0],[3,2,1],[4,2,1],[4,2,0],[5,3,1],[6,3,1],[6,3,0],[7,4,1],[8,4,0],[9,5,1]]
#guard trioRuleMatrixOfSt "(w^2*4)" -- row 1943
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,0],[3,2,1],[4,2,1],[4,2,0],[5,3,1],[6,3,1],[6,3,0],[7,4,1],[8,4,1]]
#guard trioRuleMatrixOfSt "(w^2*4+1)" -- row 1944
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,0],[3,2,1],[4,2,1],[4,2,0],[5,3,1],[6,3,1],[6,3,0],[7,4,1],[8,4,1],[8,4,0],[9,5,0]]
#guard trioRuleMatrixOfSt "(w^2*4+w)" -- row 1945
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,0],[3,2,1],[4,2,1],[4,2,0],[5,3,1],[6,3,1],[6,3,0],[7,4,1],[8,4,1],[8,4,0],[9,5,1]]
#guard trioRuleMatrixOfSt "(w^2*5)" -- row 1946
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,0],[3,2,1],[4,2,1],[4,2,0],[5,3,1],[6,3,1],[6,3,0],[7,4,1],[8,4,1],[8,4,0],[9,5,1],[10,5,1]]
#guard trioRuleMatrixOfSt "(w^3)" -- row 1948
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,1]]
#guard trioRuleMatrixOfSt "(w^3+1)" -- row 2022
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,1],[2,1,0],[3,2,0]]
#guard trioRuleMatrixOfSt "(w^3+2)" -- row 2040
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,1],[2,1,0],[3,2,0],[4,3,0]]
#guard trioRuleMatrixOfSt "(w^3+3)" -- row 2041
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,1],[2,1,0],[3,2,0],[4,3,0],[5,4,0]]
#guard trioRuleMatrixOfSt "(w^3+w)" -- row 2042
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,1],[2,1,0],[3,2,1]]
#guard trioRuleMatrixOfSt "(w^3+w+1)" -- row 2049
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,1],[2,1,0],[3,2,1],[4,2,0],[5,3,0]]
#guard trioRuleMatrixOfSt "(w^3+w+2)" -- row 2050
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,1],[2,1,0],[3,2,1],[4,2,0],[5,3,0],[6,4,0]]
#guard trioRuleMatrixOfSt "(w^3+w2)" -- row 2051
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,1],[2,1,0],[3,2,1],[4,2,0],[5,3,1]]
#guard trioRuleMatrixOfSt "(w^3+w3)" -- row 2052
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,1],[2,1,0],[3,2,1],[4,2,0],[5,3,1],[6,3,0],[7,4,1]]
#guard trioRuleMatrixOfSt "(w^3+w^2)" -- row 2053
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,1],[2,1,0],[3,2,1],[4,2,1]]
#guard trioRuleMatrixOfSt "(w^3+w^2+1)" -- row 2062
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,1],[2,1,0],[3,2,1],[4,2,1],[4,2,0],[5,3,0]]
#guard trioRuleMatrixOfSt "(w^3+w^2+2)" -- row 2063
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,1],[2,1,0],[3,2,1],[4,2,1],[4,2,0],[5,3,0],[6,4,0]]
#guard trioRuleMatrixOfSt "(w^3+w^2+w)" -- row 2064
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,1],[2,1,0],[3,2,1],[4,2,1],[4,2,0],[5,3,1]]
#guard trioRuleMatrixOfSt "(w^3+w^2+w2)" -- row 2065
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,1],[2,1,0],[3,2,1],[4,2,1],[4,2,0],[5,3,1],[6,3,0],[7,4,1]]
#guard trioRuleMatrixOfSt "(w^3+w^2*2)" -- row 2066
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,1],[2,1,0],[3,2,1],[4,2,1],[4,2,0],[5,3,1],[6,3,1]]
#guard trioRuleMatrixOfSt "(w^3+w^2*3)" -- row 2067
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,1],[2,1,0],[3,2,1],[4,2,1],[4,2,0],[5,3,1],[6,3,1],[6,3,0],[7,4,1],[8,4,1]]
#guard trioRuleMatrixOfSt "(w^3*2)" -- row 2068
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,1],[2,1,0],[3,2,1],[4,2,1],[4,2,1]]
#guard trioRuleMatrixOfSt "(w^3*2+1)" -- row 2078
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,1],[2,1,0],[3,2,1],[4,2,1],[4,2,1],[4,2,0],[5,3,0]]
#guard trioRuleMatrixOfSt "(w^3*2+2)" -- row 2079
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,1],[2,1,0],[3,2,1],[4,2,1],[4,2,1],[4,2,0],[5,3,0],[6,4,0]]
#guard trioRuleMatrixOfSt "(w^3*2+w)" -- row 2080
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,1],[2,1,0],[3,2,1],[4,2,1],[4,2,1],[4,2,0],[5,3,1]]
#guard trioRuleMatrixOfSt "(w^3*2+w2)" -- row 2081
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,1],[2,1,0],[3,2,1],[4,2,1],[4,2,1],[4,2,0],[5,3,1],[6,3,0],[7,4,1]]
#guard trioRuleMatrixOfSt "(w^3*2+w^2)" -- row 2082
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,1],[2,1,0],[3,2,1],[4,2,1],[4,2,1],[4,2,0],[5,3,1],[6,3,1]]
#guard trioRuleMatrixOfSt "(w^3*2+w^2*2)" -- row 2083
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,1],[2,1,0],[3,2,1],[4,2,1],[4,2,1],[4,2,0],[5,3,1],[6,3,1],[6,3,0],[7,4,1],[8,4,1]]
#guard trioRuleMatrixOfSt "(w^3*3)" -- row 2084
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,1],[2,1,0],[3,2,1],[4,2,1],[4,2,1],[4,2,0],[5,3,1],[6,3,1],[6,3,1]]
#guard trioRuleMatrixOfSt "(w^3*4)" -- row 2085
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,1],[2,1,0],[3,2,1],[4,2,1],[4,2,1],[4,2,0],[5,3,1],[6,3,1],[6,3,1],[6,3,0],[7,4,1],[8,4,1],[8,4,1]]
#guard trioRuleMatrixOfSt "(w^4)" -- row 2086
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,1],[2,1,1]]
#guard trioRuleMatrixOfSt "(w^4+1)" -- row 2098
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,1],[2,1,1],[2,1,0],[3,2,0]]
#guard trioRuleMatrixOfSt "(w^4+2)" -- row 2099
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,1],[2,1,1],[2,1,0],[3,2,0],[4,3,0]]
#guard trioRuleMatrixOfSt "(w^4+w)" -- row 2100
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,1],[2,1,1],[2,1,0],[3,2,1]]
#guard trioRuleMatrixOfSt "(w^4+w2)" -- row 2101
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,1],[2,1,1],[2,1,0],[3,2,1],[4,2,0],[5,3,1]]
#guard trioRuleMatrixOfSt "(w^4+w^2)" -- row 2102
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,1],[2,1,1],[2,1,0],[3,2,1],[4,2,1]]
#guard trioRuleMatrixOfSt "(w^4+w^2*2)" -- row 2103
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,1],[2,1,1],[2,1,0],[3,2,1],[4,2,1],[4,2,0],[5,3,1],[6,3,1]]
#guard trioRuleMatrixOfSt "(w^4+w^3)" -- row 2104
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,1],[2,1,1],[2,1,0],[3,2,1],[4,2,1],[4,2,1]]
#guard trioRuleMatrixOfSt "(w^4+w^3*2)" -- row 2105
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,1],[2,1,1],[2,1,0],[3,2,1],[4,2,1],[4,2,1],[4,2,0],[5,3,1],[6,3,1],[6,3,1]]
#guard trioRuleMatrixOfSt "(w^4*2)" -- row 2106
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,1],[2,1,1],[2,1,0],[3,2,1],[4,2,1],[4,2,1],[4,2,1]]
#guard trioRuleMatrixOfSt "(w^4*3)" -- row 2107
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,1],[2,1,1],[2,1,0],[3,2,1],[4,2,1],[4,2,1],[4,2,1],[4,2,0],[5,3,1],[6,3,1],[6,3,1],[6,3,1]]
#guard trioRuleMatrixOfSt "(w^5)" -- row 2108
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,1],[2,1,1],[2,1,1]]
#guard trioRuleMatrixOfSt "(w^5+1)" -- row 2110
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,1],[2,1,1],[2,1,1],[2,1,0],[3,2,0]]
#guard trioRuleMatrixOfSt "(w^5+w)" -- row 2111
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,1],[2,1,1],[2,1,1],[2,1,0],[3,2,1]]
#guard trioRuleMatrixOfSt "(w^5+w^2)" -- row 2112
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,1],[2,1,1],[2,1,1],[2,1,0],[3,2,1],[4,2,1]]
#guard trioRuleMatrixOfSt "(w^6)" -- row 2114
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,1],[2,1,1],[2,1,1],[2,1,1]]
#guard trioRuleMatrixOfSt "(w^7)" -- row 2115
  = some [[0,0,0],[1,1,1],[2,1,1],[2,1,1],[2,1,1],[2,1,1],[2,1,1],[2,1,1]]
#guard trioRuleMatrixOfSt "(w^w)" -- row 2116
  = some [[0,0,0],[1,1,1],[2,1,1],[3,0,0]]
end Googology.Trans.BMS.TrioFixStrip
