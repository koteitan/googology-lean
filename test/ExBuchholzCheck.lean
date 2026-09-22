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

`Closure.lean` proves Lemma 3.6 from one statement, `SubBound`: what `G` sees
in the subscript `Z` of `dom X₂` is bounded by any `c` between `X₂[W₀]`, the
first value the tower produces, and `X₂` itself, together with `0`.
`sub_G_le` carries that bound from `Z` to `Z[0]`, and `tower_G_le` carries it
from there up the whole tower.
-/

/-- Is `X = ψ_{X₁}(X₂)` in the configuration of Buchholz's case 4? -/
def isCase4 : Term → Bool
  | cons X₁ X₂ nil =>
      !(dom X₂ == nil) && !(dom X₂ == t1) && !(dom X₂ == tw)
        && !(decide (dom X₂ < cons X₁ X₂ nil))
  | _ => false

/-- The subscript `Z` of `dom X₂`, the `i`-th rung `W_i` of the tower, the
value `X₂[W_i]` that rung produces, and `X₂` itself. -/
def zsub : Term → Term
  | cons _ X₂ nil => subOf (dom X₂)
  | _ => nil

def rung : Term → Nat → Term
  | cons _ X₂ nil, i => tower (fs (subOf (dom X₂)) nil) X₂ i
  | _, _ => nil

def rungVal : Term → Nat → Term
  | cons _ X₂ nil, i => fs X₂ (tower (fs (subOf (dom X₂)) nil) X₂ i)
  | _, _ => nil

def argOf : Term → Term
  | cons _ X₂ _ => X₂
  | nil => nil

/-- `SubBound` at one level `u` and one `c`. -/
def subRel (X : Term) (u c : Term) : Bool :=
  (G u (zsub X)).all fun x => (c :: (G u c ++ [nil])).any fun y => decide (x ≤ y)

/-- Those members of `cs` that lie between `X₂[W₀]` and `X₂`. -/
def betweens (X : Term) (cs : List Term) : List Term :=
  cs.filter fun c => decide (rungVal X 0 ≤ c) && decide (c ≤ argOf X)

/-! A case-4 form need not be countable, so the check runs over every standard
form, not only `ctbl`. -/

#guard ((upTo 7).filter (fun X => isOT X && isCase4 X)).length == 158

/-! **The check.**  Each of those 158 forms, at every level of size at most 2,
against `X₂[W₀]`, `X₂`, and every term of size at most 4 in between.  The same
run at size 8 (651 forms, levels up to size 3, terms up to size 5) also
passes; only size 7 is kept here, to keep the build quick. -/

#guard ((upTo 7).filter (fun X => isOT X && isCase4 X)).all fun X =>
  (upTo 2).all fun u =>
    (rungVal X 0 :: argOf X :: betweens X (upTo 4)).all fun c => subRel X u c

/-! Stronger than `SubBound` needs, and observed to hold: the `{c}` witness is
never used — everything `G` sees in `Z` is already at or below something `G`
sees in `c`, or is `0`. -/

#guard ((upTo 7).filter (fun X => isOT X && isCase4 X)).all fun X =>
  (upTo 2).all fun u =>
    (rungVal X 0 :: argOf X :: betweens X (upTo 4)).all fun c =>
      (G u (zsub X)).all fun x => (G u c ++ [nil]).any fun y => decide (x ≤ y)

/-! The bound that `tower_G_le` carries up the tower has to be relative to
`c`.  Buchholz's own invariant is the absolute `G_u(W_i) < X₂[W_i]`, which
works in his system because his subscripts are numbers and `G` never enters
them.  Here they are terms.  Write `A = ψ_0(ψ_Ω(0))`.  For
`X = ψ_Ω(ψ_{A+1}(0))` the first rung is `ψ_A(0)`, which is also the value it
produces, and `G_0` of it holds `ψ_Ω(0)`, which is above `ψ_A(0)` because `A`
is countable. -/

def caseA : Term := psi nil (psi tW nil)
def caseX : Term := psi t1 (psi (cons nil (psi tW nil) t1) nil)

#guard isOT caseX && isCase4 caseX
#guard rung caseX 0 == psi caseA nil && rungVal caseX 0 == psi caseA nil
#guard !((G nil (rung caseX 0)).all (fun x => decide (x < rungVal caseX 0)))
#guard subRel caseX nil (rungVal caseX 0)

end Googology.Notation.ExBuchholz.Term
