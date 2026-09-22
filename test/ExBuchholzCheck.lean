import Googology

/-!
# Computational evidence for the last gap

`Googology.Notation.ExBuchholz.FS` proves that one expansion step strictly
decreases a countable standard form (`step_lt`).  What is not proved is that
the step *keeps* a term standard and countable — Buchholz's Lemma 3.3 for the
extended system — and that is the only thing between the library and
`exb.WF`.

This file checks it by computation.  These are `#guard` lines: finite checks,
not theorems, and they are kept out of the library for that reason.
-/

namespace Googology.Notation.ExBuchholz.Term

/-- `bySize n` lists, for each `i ≤ n`, the terms of size exactly `i`. -/
def bySize : Nat → Array (List Term)
  | 0 => #[[nil]]
  | n + 1 =>
      let prev := bySize n
      let here := (List.range (n + 1)).flatMap fun i =>
        (List.range (n + 1 - i)).flatMap fun j =>
          let k := n - i - j
          (prev[i]!).flatMap fun a =>
            (prev[j]!).flatMap fun b =>
              (prev[k]!).map fun t => cons a b t
      prev.push here

/-- Every term of size at most `n`, each exactly once. -/
def upTo (n : Nat) : List Term := ((bySize n).toList).flatten

/-- The countable standard forms of size at most `n`, other than `0`. -/
def ctbl (n : Nat) : List Term :=
  (upTo n).filter (fun X => isOT X && decide (X < tW) && !(X == nil))

/-! The term counts by size are the ternary-tree numbers. -/

#guard (bySize 8).toList.map List.length == [1, 1, 3, 12, 55, 273, 1428, 7752, 43263]
#guard (upTo 8).length == 52788
#guard (ctbl 8).length == 3835

/-! **The check.**  Every countable standard form of size at most 8, expanded
at any of `0`–`4`, stays standard, stays below `Ω`, and strictly decreases.
That is 3835 × 5 expansions with no exception.  The same holds at size 9
(15890 forms); only size 8 is run here, to keep the build quick. -/

#guard (ctbl 8).all fun X => (List.range 5).all fun n =>
  isOT (fs X (idx X n)) && decide (fs X (idx X n) < X) && decide (fs X (idx X n) < tW)

/-- Expand `X` at `n` until `0`.  `none` if a step ever leaves `OT`, leaves the
countable part, or fails to decrease; `some k` if `0` is reached in `k` steps. -/
def runOT : Term → Nat → Nat → Nat → Option Nat
  | X, n, k, fuel + 1 =>
      if X == nil then some k
      else
        let X' := fs X (idx X n)
        if isOT X' && decide (X' < X) && decide (X' < tW) then runOT X' n (k + 1) fuel
        else none
  | _, _, _, 0 => none

/-! Named ordinals, expanded all the way down to `0`, every intermediate term
standard. -/

#guard runOT (psi nil tW) 1 0 200 == some 4                              -- ε₀
#guard runOT (psi nil tW) 2 0 400 == some 39                             -- ε₀
#guard runOT (psi nil (cons t1 nil (cons t1 nil nil))) 1 0 400 == some 10 -- ψ_0(Ω+Ω)
#guard runOT (psi nil (psi t1 t1)) 1 0 400 == some 5                     -- ψ_0(ψ_1(1))
#guard runOT (psi nil (psi t2 nil)) 1 0 800 == some 11                   -- ψ_0(Ω_2), BHO
#guard runOT (psi nil (psi tW nil)) 1 0 800 == some 8                    -- ψ_0(ψ_Ω(0))

/-! ## The tower of Buchholz's case 4

`Closure.lean` proves Lemma 3.6 from one statement, `TowerBound`: what `G`
sees in a rung of the tower is below the value that rung produces.  `G` is
antitone in its level, so checking it at level `0` checks it at every level.
-/

/-- Is `X = ψ_{X₁}(X₂)` in the configuration of Buchholz's case 4? -/
def isCase4 : Term → Bool
  | cons X₁ X₂ nil =>
      !(dom X₂ == nil) && !(dom X₂ == t1) && !(dom X₂ == tw)
        && !(decide (dom X₂ < cons X₁ X₂ nil))
  | _ => false

/-- The `i`-th rung `W_i` of the tower, and the value `X₂[W_i]` it produces. -/
def rung : Term → Nat → Term
  | cons _ X₂ nil, i => tower (fs (subOf (dom X₂)) nil) X₂ i
  | _, _ => nil

def rungVal : Term → Nat → Term
  | cons _ X₂ nil, i => fs X₂ (tower (fs (subOf (dom X₂)) nil) X₂ i)
  | _, _ => nil

#guard ((ctbl 8).filter isCase4).length == 532

/-! **`TowerBound`**, at level `0`, on five rungs of each of those 532 forms. -/

#guard ((ctbl 8).filter isCase4).all fun X => (List.range 5).all fun i =>
  (G nil (rung X i)).all (fun x => decide (x < rungVal X i))

/-! The other half of the same invariant: every rung is a standard form. -/

#guard ((ctbl 8).filter isCase4).all fun X => (List.range 5).all fun i =>
  isOT (rung X i)

/-! A case-4 form need not be countable, and the check does not depend on it:
all 158 standard case-4 forms of size at most 7, countable or not, pass both
halves on four rungs. -/

#guard ((upTo 7).filter (fun X => isOT X && isCase4 X)).length == 158
#guard ((upTo 7).filter (fun X => isOT X && isCase4 X)).all fun X =>
  (List.range 4).all fun i =>
    isOT (rung X i) && (G nil (rung X i)).all (fun x => decide (x < rungVal X i))

/-! `TowerBound` needs `G_0(X₂) < X₂`, and the case-4 configuration supplies
it. -/

#guard ((upTo 7).filter (fun X => isOT X && isCase4 X)).all fun X =>
  match X with
  | cons _ X₂ nil => (G nil X₂).all (fun x => decide (x < X₂))
  | _ => true

/-! That is not a fact about standard forms in general.  `ψ_Ω(ε₀)` is
standard, and `G_0(ε₀)` holds `Ω`, which is above `ε₀`. -/

#guard isOT (psi t1 (psi nil tW))
#guard !((G nil (psi nil tW)).all (fun x => decide (x < psi nil tW)))

end Googology.Notation.ExBuchholz.Term
