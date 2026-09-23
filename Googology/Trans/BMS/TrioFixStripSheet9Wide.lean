import Googology.Trans.BMS.TrioFixStrip
import Googology.Trans.BMS.TrioRulesAllSheet
import Googology.Trans.BMS.TrioTree

/-!
# Patch "strip": the checks, continued

See `TrioFixStripSheet.lean` for the summary.  Part 9, the wider families (subscripts `0,1,2`; below `Ω_2`; `0,1,ω`;
`0,1,Ω`): the patch changes no matrix, so the counts (75/8, 0/0, 63/11, 137/29) are
those of `trioMatrixLFix`; and the `ψ_0`-only variant of the reading.
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

def chosenDataSt3 : Array (Od × List (List Nat)) :=
  ((chosen ++ [printed3552]).map fun s => ((parse s).getD [], stOf s)).toArray
/-! ## Part 9: the checks of `TrioFixOfTermSheet.lean` with the patched builder -/

/-- The map on terms is the reading, then the patched builder. -/
theorem trioMatrixLSt_def (α : Term) : trioMatrixLSt α = trioRuleMatrixSt (ofTermFix α) := rfl

/-! ### Terms whose value is a label of the sheet -/

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

/-- The 42 pairs (term, label) of `TrioFixOfTermSheet.lean`. -/
def sheetPairs : List (Term × String) := [
  (te0, "psi(W)"),
  (cons nil tW t1, "(psi(W)+1)"),
  (cons nil tW tw, "(psi(W)+w)"),
  (cons nil tW (psi nil two), "(psi(W)+w^2)"),
  (cons nil tW (psi nil tw), "(psi(W)+w^w)"),
  (cons nil tW te0, "(psi(W)*2)"),
  (pOm t1, "(psi(W)*w)"),
  (pOm tw, "(psi(W)*w^w)"),
  (pOm te0, "(psi(W)^2)"),
  (pOm (pOm t1), "(psi(W)^w)"),
  (pOm (pOm te0), "(psi(W)^psi(W))"),
  (pOm (pOm (pOm t1)), "(psi(W)^psi(W)^w)"),
  (pOm (pOm (pOm te0)), "(psi(W)^psi(W)^psi(W))"),
  (pOm tW, "psi(W2)"),
  (pOm (cons t1 nil tW), "psi(W3)"),
  (psi nil (psi t1 t1), "psi(W*w)"),
  (psi nil (psi t1 te0), "psi(W*psi(W))"),
  (psi nil (psi t1 tW), "psi(W^2)"),
  (psi nil (psi t1 (cons t1 nil tW)), "psi(W^3)"),
  (psi nil (psi t1 (psi t1 t1)), "psi(W^w)"),
  (psi nil (psi t1 (psi t1 tW)), "psi(W^W)"),
  (psi nil (psi t1 (psi t1 (psi t1 tW))), "psi(W^W^W)"),
  (psi nil W2, "psi(W_2)"),
  (psi nil (psi two W2), "psi(W_2^2)"),
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
  (psi t1 (psi two tW), "psi_1(W_2*W)"),
  (psi t1 (psi two W2), "psi_1(W_2^2)"),
  (psi tw (psi wp1 nil), "psi_W_(w+1)(W_(w+1))"),
  (psi tw (psi wp2 nil), "psi_W_(w+1)(W_(w+2))"),
  (psi tw (psi tW nil), "psi_W_(w+1)(W_W)"),
  (psi tW (psi Wp1 nil), "psi_W_(W+1)(W_(W+1))"),
  (psi wp1 (psi wp2 nil), "psi_W_(w+2)(W_(w+2))")]


/-- The pairs, valued by their labels, with the matrices a map gives the terms. -/
def pairData (f : Term → List (List Nat)) : Array (Od × List (List Nat)) :=
  (sheetPairs.map fun p => ((parse p.2).getD [], f p.1)).toArray


/-! ### `ψ_0(Ω+1) = ε₀·ω` and BMS expansion -/


/-! ### `TrioTree`'s terms -/

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

-- `smallFrag 6`: 610 terms, in order, no collisions.

/-- The terms of `TrioTree`'s kind with at most 7 `ψ`s. -/
def frag7 : List Term := fam [nil, t1] 7 tW

-- **The 7-`ψ` family: 0 disagreements** (127 with `trioMatrixLFix`), 0 collisions;
-- the patched map differs from `trioMatrixLFix` only on `β`.

/-! ### Wider families -/

/-- Countable, subscripts `0, 1, 2`, at most 5 `ψ`s. -/
def famC : List Term := fam [nil, t1, two] 5 tW
/-- Uncountable below `Ω_2`, subscripts `0, 1`, at most 5 `ψ`s (and countable ones). -/
def famU : List Term := fam [nil, t1] 5 W2
/-- Below `Ω_Ω`, subscripts `0, 1, ω`, at most 4 `ψ`s. -/
def famW : List Term := fam [nil, t1, tw] 4 (psi tW nil)
/-- Below `Ω_{Ω_Ω}`, subscripts `0, 1, Ω`, at most 4 `ψ`s. -/
def famO : List Term := fam [nil, t1, tW] 4 (psi (psi tW nil) nil)

#guard (famC.length, famU.length, famW.length, famO.length) = (491, 524, 537, 537)
-- The patch changes no matrix of these families, so the counts are those of
-- `trioMatrixLFix`: these failures are other defects of the builder.
#guard [famC, famU, famW, famO].all fun xs => xs.all fun a => trioMatrixLSt a == trioMatrixLFix a
#guard ((badPairs famC trioMatrixLSt).length, collide famC trioMatrixLSt) = (75, 8)
#guard ((badPairs famU trioMatrixLSt).length, collide famU trioMatrixLSt) = (0, 0)
#guard ((badPairs famW trioMatrixLSt).length, collide famW trioMatrixLSt) = (63, 11)
#guard ((badPairs famO trioMatrixLSt).length, collide famO trioMatrixLSt) = (137, 29)
#guard [famC, famU, famW, famO].all fun xs => readBad xs ofTermFix == 0
#guard (badPairs famW trioMatrixLSt).all fun p =>
  !(sheetLabels.any fun l => (parse l).getD [] == ofTermFix p.1) ||
  !(sheetLabels.any fun l => (parse l).getD [] == ofTermFix p.2)

/-! ### The ψ_0-only variant of the reading (reading only, unchanged) -/

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


end Googology.Trans.BMS.TrioFixStrip
