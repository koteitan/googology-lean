import Googology.Trans.BMS.TrioFixOfTerm
import Googology.Trans.BMS.TrioRulesAllSheet
import Googology.Trans.BMS.TrioTree

/-!
# Patch "ofTerm": the checks

`TrioFixOfTerm.lean` changes how a term of the extended Buchholz notation is read
into the normal form of the rules (`ofTermFix` for `TrioRules.ofTerm`); it changes
no definition of the builder.  This file checks the new reading against the sheet
([`tools/omega_alpha_rows.tsv`](https://github.com/koteitan/trio/blob/main/tools/omega_alpha_rows.tsv)
of [koteitan/trio](https://github.com/koteitan/trio)), against BMS expansion, and on
the families of terms `TrioTree.lean` works on.  All of it is `#guard`s: a
calibration, not a theorem.

* **Part 1, the sheet.**  The label map `trioRuleMatrixOfAll` is the one of
  `TrioRulesAll.lean` (`labelMap_unchanged`), so every check of
  `TrioRulesAllSheet.lean` (imported, so already run) holds for the patched rules as
  it stands.  Its two order checks are re-run below: 0 disagreements.
* **Part 2, terms with a sheet row.**  42 standard terms whose value is a label of the
  sheet (the value worked out by hand in each comment): the new reading gives the
  label's normal form exactly on all 42, hence the sheet's matrix; the old reading on
  14 (its matrix is right on 25, wrong on 17).  Against the 784 chosen matrices the new matrices
  are in order (0 disagreements), the old ones are not (710).
* **Part 3, `ψ_0(Ω+1) = ε₀·ω`.**  The new matrix is row 2158 `(psi(W)*w)`, and its
  BMS expansions `[0], [1], [2], [3]` are the matrices of `ε₀, ε₀·2, ε₀·3, ε₀·4`.
  The old matrix is row 2163 `(psi(W)^psi(W)^w)`, whose expansions `[1], [2]` are
  `ε₀^{ε₀}` and `ε₀^{ε₀^2}`.
* **Part 4, `TrioTree`'s terms** (subscripts `0`/`1`, countable).  On the 610 terms
  of `smallFrag 6` the new map differs from the old on 484 and keeps the order
  (0 disagreements, 0 collisions).  On the 2,397 terms with at most 7 `ψ`s it has
  127 disagreements, all against the one term
  `β = ψ_0(ψ_1(ψ_0(Ω + ψ_0(Ω+1))))` (label `psi(W*psi(W)^psi(W)^w)`, `ε_{ε₀^{ε₀^ω}}`), whose
  matrix is below that of `ψ_0(ψ_1(ψ_0(Ω))) = ε_{ε₀}`; with `β`'s matrix replaced by
  the tree of the term (the old map's matrix) there are 0.  So `TrioTree`'s
  theorems (standard forms, order) do not carry over to the new map; the one
  failure up to 7 `ψ`s is a builder defect exposed by the correct reading.
* **Part 5, wider families.**  Countable `α` with subscripts `0, 1, 2` (491 terms, at
  most 5 `ψ`s): 75 disagreements, 8 collisions, with either reading (the builder, not
  the reading).  Uncountable `α < Ω_2` with subscripts `0, 1` (524): 0, 0 with
  either.  `α < Ω_Ω` with subscripts `0, 1, ω` (537, at most 4 `ψ`s): new 63 and 11,
  old 0 and 0; with subscripts `0, 1, Ω` below `Ω_{Ω_Ω}` (537): new 137 and 29, old
  58,277 and 2,743.  On every family the reading itself keeps the order (the
  program's `cmpOrd` of the normal forms against the order of the terms: 0).
* **Standard forms** (yaBMS `bms -s`, run outside Lean on the matrices of these
  families): smallFrag 6 new: all 610 standard; 7 `ψ`s new: 2,396 of 2,397 (not
  `β`); subscripts `0,1,2`: 481 of 483 distinct with either reading; `α < Ω_2`: all 524;
  subscripts `0,1,ω`: new 30 of 527 distinct not standard, old 61 of 537; subscripts
  `0,1,Ω`: new 59 of 512, old 46 of 291.
-/

namespace Googology.Trans.BMS.TrioFixOfTerm

open Googology.Notation.ExBuchholz
open Googology.Notation.ExBuchholz.Term
open Googology.Trans.BMS.TrioRules
open Googology.Trans.BMS.TrioRulesAll
open Googology.Trans.BMS.TrioRules2 (cmpMat chosen orderDisagreements)
open Googology.Trans.BMS.TrioRules3 (allLabels printed3552)
open Googology.Trans.BMS.TrioRulesNL (sheetLabels crossDisagreements)
open Googology.Trans.BMS (expandRL te0)
open Googology.Trans.BMS.TrioTree (smallFrag)

/-! ## Part 1: the sheet checks of the merged rules -/

/-- The patch changes no builder: the matrix of a term is the merged rules' matrix
of its normal form, and the map on labels is `trioRuleMatrixOfAll` itself. -/
theorem labelMap_unchanged (α : Term) : trioMatrixLFix α = trioRuleMatrixAll (ofTermFix α) := rfl

#guard orderDisagreements chosenDataAll = 0
#guard orderDisagreements chosenDataAll3 = 0

/-! ## Part 2: terms whose value is a label of the sheet -/

/-- `2`. -/
abbrev two : Term := cons nil nil t1
/-- `Ω_2`. -/
abbrev W2 : Term := psi two nil
/-- `ψ_0(Ω + t)`. -/
abbrev pOm (t : Term) : Term := psi nil (cons t1 nil t)
/-- `ω + 1`, `ω + 2`, `Ω + 1`. -/
abbrev wp1 : Term := cons nil t1 t1
abbrev wp2 : Term := cons nil t1 two
abbrev Wp1 : Term := cons t1 nil t1

/-- A term and the label of the sheet with the same value (worked out by hand:
`ψ_0(Ω + x) = ε₀·ω^x`, `ψ_a(b_hi + b_lo) = ω^{ψ_a(b_hi) + b_lo}`). -/
def sheetPairs : List (Term × String) := [
  (te0, "psi(W)"),                                    -- ψ_0(Ω) = ε₀
  (cons nil tW t1, "(psi(W)+1)"),
  (cons nil tW tw, "(psi(W)+w)"),
  (cons nil tW (psi nil two), "(psi(W)+w^2)"),
  (cons nil tW (psi nil tw), "(psi(W)+w^w)"),
  (cons nil tW te0, "(psi(W)*2)"),
  (pOm t1, "(psi(W)*w)"),                             -- ε₀·ω
  (pOm tw, "(psi(W)*w^w)"),                           -- ε₀·ω^ω
  (pOm te0, "(psi(W)^2)"),                            -- ε₀·ω^ε₀ = ε₀^2
  (pOm (pOm t1), "(psi(W)^w)"),                       -- ω^{ε₀ + ε₀·ω} = ε₀^ω
  (pOm (pOm te0), "(psi(W)^psi(W))"),                 -- ω^{ε₀ + ω^{ε₀·2}} = ε₀^ε₀
  (pOm (pOm (pOm t1)), "(psi(W)^psi(W)^w)"),
  (pOm (pOm (pOm te0)), "(psi(W)^psi(W)^psi(W))"),
  (pOm tW, "psi(W2)"),                                -- ψ_0(Ω·2) = ε₁
  (pOm (cons t1 nil tW), "psi(W3)"),
  (psi nil (psi t1 t1), "psi(W*w)"),                  -- ψ_1(1) = Ω·ω
  (psi nil (psi t1 te0), "psi(W*psi(W))"),            -- ψ_1(ε₀) = Ω·ε₀
  (psi nil (psi t1 tW), "psi(W^2)"),                  -- ψ_1(Ω) = Ω^2
  (psi nil (psi t1 (cons t1 nil tW)), "psi(W^3)"),
  (psi nil (psi t1 (psi t1 t1)), "psi(W^w)"),         -- ψ_1(Ω·ω) = Ω^ω
  (psi nil (psi t1 (psi t1 tW)), "psi(W^W)"),         -- ψ_1(Ω^2) = Ω^Ω
  (psi nil (psi t1 (psi t1 (psi t1 tW))), "psi(W^W^W)"),
  (psi nil W2, "psi(W_2)"),
  (psi nil (psi two W2), "psi(W_2^2)"),               -- ψ_2(Ω_2) = Ω_2^2
  (tW, "W"),
  (cons t1 nil t1, "(W+1)"),
  (psi t1 t1, "(W*w)"),
  (cons t1 t1 t1, "(W*w+1)"),
  (psi t1 tW, "(W^2)"),
  (cons t1 tW tW, "(W^2+W)"),
  (psi t1 (psi t1 t1), "(W^w)"),
  (cons t1 nil te0, "(W+psi(W))"),
  (psi t1 te0, "(W*psi(W))"),
  (psi t1 W2, "psi_1(W_2)"),
  (psi t1 (cons two nil W2), "psi_1(W_2*2)"),
  (psi t1 (psi two tW), "psi_1(W_2*W)"),              -- ψ_2(Ω) = Ω_2·Ω
  (psi t1 (psi two W2), "psi_1(W_2^2)"),
  -- infinite subscripts (change 2): `ψ_c` is the program's `psi_{Ω_{c+1}}`
  (psi tw (psi wp1 nil), "psi_W_(w+1)(W_(w+1))"),
  (psi tw (psi wp2 nil), "psi_W_(w+1)(W_(w+2))"),
  (psi tw (psi tW nil), "psi_W_(w+1)(W_W)"),
  (psi tW (psi Wp1 nil), "psi_W_(W+1)(W_(W+1))"),
  (psi wp1 (psi wp2 nil), "psi_W_(w+2)(W_(w+2))")]

#guard sheetPairs.length = 42
#guard sheetPairs.all fun p => isOT p.1 && allLabels.contains p.2
-- The new reading is the label's normal form on all 42, so the matrix is the sheet's.
#guard sheetPairs.all fun p => ofTermFix p.1 == (parse p.2).getD []
#guard sheetPairs.all fun p => trioMatrixLFix p.1 == allOf p.2
-- The old reading: the normal form on 14, the matrix on 25.
#guard (sheetPairs.filter fun p => ofTerm p.1 == (parse p.2).getD []).length = 14
#guard (sheetPairs.filter fun p => trioRuleMatrixAll (ofTerm p.1) == allOf p.2).length = 25

/-- The pairs, valued by their labels, with the matrices a reading gives the terms. -/
def pairData (f : Term → List (List Nat)) : Array (Od × List (List Nat)) :=
  (sheetPairs.map fun p => ((parse p.2).getD [], f p.1)).toArray

/-- The 784 chosen labels with the merged matrices (`TrioRulesAllSheet.lean`). -/
def chosenAll : Array (Od × List (List Nat)) := chosenDataAll3

#guard crossDisagreements (pairData trioMatrixLFix) chosenAll = 0
#guard crossDisagreements (pairData fun a => trioRuleMatrixAll (ofTerm a)) chosenAll = 710

/-! ## Part 3: `ψ_0(Ω+1) = ε₀·ω` and BMS expansion -/

#guard trioMatrixLFix (pOm t1) = allOf "(psi(W)*w)"
#guard trioMatrixLFix (pOm t1) = [[0,0,0],[1,1,1],[2,1,1],[3,0,0],[4,1,0],[2,1,1]]
#guard trioRuleMatrixAll (ofTerm (pOm t1)) = allOf "(psi(W)^psi(W)^w)"
#guard TrioRules.trioMatrixL (pOm t1) = [[0,0,0],[1,1,1],[2,1,1],[3,0,0],[4,1,0],[4,0,0]]
-- `(ε₀·ω)[n] = ε₀·(n+1)`: the new matrix expands to `ε₀·(n+1)`, as the term's
-- fundamental sequence does.
#guard (List.range 4).all fun n =>
  expandRL 3 n (trioMatrixLFix (pOm t1)) =
    trioMatrixLFix (Googology.Notation.ExBuchholz.Term.repeatPrin nil tW (n + 1))
-- The old matrix expands to `ε₀^{ε₀}`, `ε₀^{ε₀^2}`: far above every `ε₀·n`.
#guard expandRL 3 1 (TrioRules.trioMatrixL (pOm t1)) = allOf "(psi(W)^psi(W))"
#guard expandRL 3 2 (TrioRules.trioMatrixL (pOm t1)) = allOf "(psi(W)^psi(W)^2)"
-- The value, proved in `TrioFixOfTerm.lean`: `ψ_0(Ω + t) = ω^{ε₀ + t}`.
example (t : Term) (h : t.val < Ord.eps1.{0}) :
    (pOm t).val = Ordinal.omega0 ^ (Ord.eps0.{0} + t.val) := (val_psi_Omega_add t h).2

/-! ## Part 4: `TrioTree`'s terms -/

/-- The terms with `n` `ψ`s outside the subscripts, subscripts from `S`. -/
def genS (S : List Term) : Nat → Array (List Term)
  | 0 => #[[nil]]
  | n + 1 =>
    let T := genS S n
    T.push ((List.range (n + 1)).flatMap fun k =>
      (T.getD k []).flatMap fun b =>
        (T.getD (n - k) []).flatMap fun t => S.map fun a => cons a b t)

/-- The nonzero standard ones among them up to `n`, below `bound`. -/
def fam (S : List Term) (n : Nat) (bound : Term) : List Term :=
  ((List.range (n + 1)).flatMap fun k => (genS S n).getD k []).filter
    fun a => isOT a && decide (a < bound) && a != nil

/-- Pairs of terms whose order and the order of their matrices differ. -/
def badPairs (xs : List Term) (f : Term → List (List Nat)) : List (Term × Term) := Id.run do
  let ar := (xs.map fun a => (a, f a)).toArray
  let mut out := []
  for i in [0:ar.size] do
    for j in [i+1:ar.size] do
      let x := ar.getD i (nil, [])
      let y := ar.getD j (nil, [])
      if Term.cmp x.1 y.1 != cmpMat x.2 y.2 then out := (x.1, y.1) :: out
  return out

/-- Pairs of terms with one matrix. -/
def collide (xs : List Term) (f : Term → List (List Nat)) : Nat := Id.run do
  let ar := (xs.map f).toArray
  let mut k := 0
  for i in [0:ar.size] do
    for j in [i+1:ar.size] do
      if ar.getD i [] == ar.getD j [] then k := k + 1
  return k

/-- Pairs of terms whose order and the program's order of their normal forms differ. -/
def readBad (xs : List Term) (f : Term → Od) : Nat := Id.run do
  let ar := (xs.map fun a => (a, f a)).toArray
  let mut bad := 0
  for i in [0:ar.size] do
    for j in [i+1:ar.size] do
      let x := ar.getD i (nil, [])
      let y := ar.getD j (nil, [])
      if Term.cmp x.1 y.1 != cmpOrd x.2 y.2 then bad := bad + 1
  return bad

/-- The old map on terms, with the merged rules. -/
def oldAll (a : Term) : List (List Nat) := trioRuleMatrixAll (ofTerm a)

-- On `TrioTree`'s terms the merged rules and rules 1–10 agree for the old reading.
#guard (smallFrag 6).all fun a => oldAll a == TrioRules.trioMatrixL a
-- `smallFrag 6`: 610 terms, 484 read differently; the new map keeps the order.
#guard (smallFrag 6).length = 610
#guard ((smallFrag 6).filter fun a => ofTermFix a != ofTerm a).length = 484
#guard (badPairs (smallFrag 6) trioMatrixLFix).length = 0
#guard collide (smallFrag 6) trioMatrixLFix = 0

-- `β = ψ_0(ψ_1(ψ_0(Ω + ψ_0(Ω+1))))` (`tβ`, in `TrioFixOfTerm.lean`): `ψ_1(x) = Ω·ω^x`
-- and `ψ_0(Ω+ψ_0(Ω+1)) = ε₀^ω`, so `β = ψ_0(Ω·ε₀^{ε₀^ω})`, `ε_{ε₀^{ε₀^ω}}`.
-- The order failure against `ε_{ε₀}` is the theorem `trioMatrixLFix_order_fails`.
#guard tβ == psi nil (psi t1 (pOm (pOm t1)))

#guard ofTermFix tβ == (parse "psi(W*psi(W)^psi(W)^w)").getD []
#guard trioMatrixLFix tβ = [[0,0,0],[1,1,1],[2,1,1],[3,0,0],[4,1,0],[5,0,0],[6,0,0],[7,1,0],[7,0,0]]
-- `ε_{ε₀} < ε_{ε₀^{ε₀^ω}}`, but the matrices are the other way round.
#guard decide (psi nil (psi t1 te0) < tβ)
#guard cmpMat (trioMatrixLFix (psi nil (psi t1 te0))) (trioMatrixLFix tβ) = .gt
-- The argument's `ω^{ε₀·ω}` is written as the tree of `ψ_0(ψ_0(Ω+1))`; the tree of
-- the term, `ψ_0(Ω + ψ_0(Ω+1))`, is the old map's matrix.
#guard oldAll tβ = [[0,0,0],[1,1,1],[2,1,1],[3,0,0],[4,1,0],[5,0,0],[6,1,0],[6,0,0],[7,1,0],[7,0,0]]

/-- The terms of `TrioTree`'s kind with at most 7 `ψ`s. -/
def frag7 : List Term := fam [nil, t1] 7 tW

/-- The new map with `β`'s matrix replaced by the tree of the term. -/
def newPatched (a : Term) : List (List Nat) := if a == tβ then oldAll a else trioMatrixLFix a

#guard frag7.length = 2397
#guard (badPairs frag7 trioMatrixLFix).length = 127
#guard (badPairs frag7 trioMatrixLFix).all fun p => p.1 == tβ || p.2 == tβ
#guard collide frag7 trioMatrixLFix = 0
#guard (badPairs frag7 newPatched).length = 0
#guard (badPairs frag7 oldAll).length = 0
#guard readBad frag7 ofTermFix = 0

/-! ## Part 5: wider families -/

/-- Countable, subscripts `0, 1, 2`, at most 5 `ψ`s. -/
def famC : List Term := fam [nil, t1, two] 5 tW
/-- Uncountable below `Ω_2`, subscripts `0, 1`, at most 5 `ψ`s (and countable ones). -/
def famU : List Term := fam [nil, t1] 5 W2
/-- Below `Ω_Ω`, subscripts `0, 1, ω`, at most 4 `ψ`s. -/
def famW : List Term := fam [nil, t1, tw] 4 (psi tW nil)
/-- Below `Ω_{Ω_Ω}`, subscripts `0, 1, Ω`, at most 4 `ψ`s. -/
def famO : List Term := fam [nil, t1, tW] 4 (psi (psi tW nil) nil)

#guard (famC.length, famU.length, famW.length, famO.length) = (491, 524, 537, 537)
#guard ((badPairs famC trioMatrixLFix).length, collide famC trioMatrixLFix) = (75, 8)
#guard ((badPairs famC oldAll).length, collide famC oldAll) = (75, 8)
#guard ((badPairs famU trioMatrixLFix).length, collide famU trioMatrixLFix) = (0, 0)
#guard ((badPairs famU oldAll).length, collide famU oldAll) = (0, 0)
#guard ((badPairs famW trioMatrixLFix).length, collide famW trioMatrixLFix) = (63, 11)
#guard ((badPairs famW oldAll).length, collide famW oldAll) = (0, 0)
#guard ((badPairs famO trioMatrixLFix).length, collide famO trioMatrixLFix) = (137, 29)
#guard ((badPairs famO oldAll).length, collide famO oldAll) = (58277, 2743)
-- The reading keeps the order on every family (`cmpOrd` of the normal forms).
#guard [famC, famU, famW, famO].all fun xs => readBad xs ofTermFix == 0
-- No pair that fails in `famW` has a sheet row at both ends.
#guard (badPairs famW trioMatrixLFix).all fun p =>
  !(sheetLabels.any fun l => (parse l).getD [] == ofTermFix p.1) ||
  !(sheetLabels.any fun l => (parse l).getD [] == ofTermFix p.2)

/-! ## Part 6: the ψ_0-only variant

Change 1 applied to `ψ_0` alone (a nonzero subscript keeps the old atom
`ψ_c(b)`) is not enough for the sheet: it misreads `ψ_1(1) = Ω·ω` and every row
built on it. -/

/-- `ofTermFix` with change 1 only for the subscript `0`. -/
def partsPsi0 : Term → Term → Od × Od × Od
  | nil, _ => ([], [], [])
  | cons c d u, a =>
    let q := partsPsi0 d c
    let cf := (partsPsi0 c nil).1
    let s := if c == nil then summandFix true cf q.2.1 q.2.2
      else if q.1.isEmpty then [(.W cf, 1)] else [(.psi cf q.1, 1)]
    let p := partsPsi0 u a
    (add s p.1, if Term.cmp c a == .gt then (add s p.2.1, p.2.2) else (p.2.1, add s p.2.2))

#guard (sheetPairs.filter fun p => (partsPsi0 p.1 nil).1 == (parse p.2).getD []).length = 21

end Googology.Trans.BMS.TrioFixOfTerm
