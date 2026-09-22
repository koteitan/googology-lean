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

/-! ## The last gap: Buchholz 3.3

`Closure.lean` proves Lemma 3.6, and with it `SubBound` — the bound on the
tower of Buchholz's case 4 — from `OTFS` alone, which is his Lemma 3.3 for the
extended system: the fundamental sequence keeps a term standard.  Nothing else
is assumed.

**The check.**  Every standard form of size at most 6, expanded at every
standard index of size at most 3 below its domain, stays standard.
-/

#guard ((upTo 6).filter isOT).all fun X =>
  ((upTo 3).filter (fun Y => isOT Y && decide (Y < dom X))).all fun Y =>
    isOT (fs X Y)

/-! ## Two terms the proof of 3.6 is shaped around

Has `X` a domain indexed by terms? -/

def domTerm (X : Term) : Bool :=
  !(dom X == nil) && !(dom X == t1) && !(dom X == tw)

/-! The index in `SubBound` has to be `ψ_{Z[0]}(0)`; an arbitrary `W < dom X`
will not do.  For `X = ψ_{ω+1}(0)` the domain is `X` itself and `X[0] = 0`, so
the bound would have to hold against `G_u(0)`, which is empty, while `G_0` does
see something in `Z = ω + 1`. -/

def caseW : Term := psi (cons nil t1 t1) nil

#guard isOT caseW && domTerm caseW
#guard fs caseW nil == nil
#guard !((G nil (subOf (dom caseW))).all (fun x => (G nil nil ++ [nil]).any
  (fun y => decide (x ≤ y))))

/-! The bound that `tower_G_le` carries up the tower has to be relative to
`c`.  Buchholz's own invariant is the absolute `G_u(W_i) < X₂[W_i]`, which
works in his system because his subscripts are numbers and `G` never enters
them.  Here they are terms.  Write `A = ψ_0(ψ_Ω(0))`.  For
`X = ψ_Ω(ψ_{A+1}(0))` the first rung of the tower is `ψ_A(0)`, which is also
the value it produces, and `G_0` of it holds `ψ_Ω(0)`, which is above
`ψ_A(0)` because `A` is countable. -/

def caseA : Term := psi nil (psi tW nil)
def caseB : Term := psi (cons nil (psi tW nil) t1) nil
def caseX : Term := psi t1 caseB

#guard isOT caseX
#guard tower (fs (subOf (dom caseB)) nil) caseB 0 == psi caseA nil
#guard !((G nil (psi caseA nil)).all (fun x => decide (x < fs caseB (psi caseA nil))))

end Googology.Notation.ExBuchholz.Term
