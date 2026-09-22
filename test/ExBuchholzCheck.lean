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

/-! ## The last gap: the Bachmann property

`Closure.lean` proves 3.3 — and with it 3.6, `SubBound` and the tower
invariant of Buchholz's case 4 — from `Bachmann` alone: for `ψ_A(B)` in the
configuration of case 4, everything `G_A` sees in `B` is below `B[ψ_{Z[0]}(0)]`,
the first value the tower produces.  That is the only thing left.
-/

/-- Is `X = ψ_A(B)` in the configuration of Buchholz's case 4? -/
def isCase4 : Term → Bool
  | cons A B nil =>
      !(dom B == nil) && !(dom B == t1) && !(dom B == tw)
        && !(decide (dom B < cons A B nil))
  | _ => false

/-- The level of the collapse, its argument, the `i`-th rung of the tower and
the value that rung produces. -/
def lvl : Term → Term | cons A _ _ => A | nil => nil
def argB : Term → Term | cons _ B _ => B | nil => nil

def rung : Term → Nat → Term
  | cons _ B nil, i => tower (fs (subOf (dom B)) nil) B i
  | _, _ => nil

def rungVal : Term → Nat → Term
  | cons _ B nil, i => fs B (tower (fs (subOf (dom B)) nil) B i)
  | _, _ => nil

/-! A case-4 form need not be countable, so the check runs over every standard
form, not only `ctbl`.  **The check** is `Bachmann` on all 651 of size at most
8. -/

#guard ((upTo 8).filter (fun X => isOT X && isCase4 X)).length == 651

#guard ((upTo 8).filter (fun X => isOT X && isCase4 X)).all fun X =>
  (G (lvl X) (argB X)).all fun x => decide (x < rungVal X 0)

/-! `Bachmann` has to be proved together with its `ψ` form: the branch where
`dom B` comes from the subscript reduces to the statement with `x < B`
replaced by `x < ψ_B(0)` on both sides.  Both are checked here, over every
standard form of size at most 6 with a term-indexed domain and every level of
size at most 2 that the hypothesis holds at. -/

def domTerm (X : Term) : Bool :=
  !(dom X == nil) && !(dom X == t1) && !(dom X == tw)

#guard ((upTo 6).filter (fun B => isOT B && domTerm B)).all fun B =>
  (upTo 2).all fun u =>
    (!((G u B).all (fun y => decide (y < B)))) ||
      (G u B).all (fun x => decide (x < fs B (W0 B)))

#guard ((upTo 6).filter (fun B => isOT B && domTerm B)).all fun B =>
  (upTo 2).all fun u =>
    (!((G u B).all (fun y => decide (y < psi B nil)))) ||
      (G u B).all (fun x => decide (x < psi (fs B (W0 B)) nil))

/-! The prefixed shape, which the sum branch needs. -/

#guard (((upTo 5).filter (fun V => isOT V && domTerm V)).flatMap fun V =>
    ((upTo 4).filter (fun p => isOT (addT p V))).map fun p => (p, V)).all fun q =>
  (upTo 2).all fun u =>
    (!(decide (u ≤ subOf (dom q.2)) &&
        (G u q.2).all (fun y => decide (y < addT q.1 q.2)))) ||
      (G u q.2).all (fun x => decide (x < addT q.1 (fs q.2 (W0 q.2))))

/-! The prefix cannot be dropped.  For this `V`, `G_1` sees the head of `V`
itself inside the tail, so neither "below the head" nor "below the tail"
holds, while the conclusion does. -/

def caseV : Term := cons (psi t1 nil) nil (psi t1 (psi (psi t1 nil) nil))

#guard isOT caseV && domTerm caseV
#guard (G t1 caseV).all (fun y => decide (y < caseV))
#guard !((G t1 caseV).all (fun y => decide (y < psi (psi t1 nil) nil)))
#guard (G t1 caseV).all (fun x => decide (x < fs caseV (W0 caseV)))

/-! The level matters.  At level `0` the tower invariant that `Bachmann`
feeds is false: write `A = ψ_0(ψ_Ω(0))`; for `X = ψ_Ω(ψ_{A+1}(0))` the first
rung is `ψ_A(0)`, which is also the value it produces, and `G_0` of it holds
`ψ_Ω(0)`, which is above `ψ_A(0)` because `A` is countable.  `tower_G_le` is
stated relative to a `c` for that reason. -/

def caseA : Term := psi nil (psi tW nil)
def caseX : Term := psi t1 (psi (cons nil (psi tW nil) t1) nil)

#guard isOT caseX && isCase4 caseX
#guard rung caseX 0 == psi caseA nil && rungVal caseX 0 == psi caseA nil
#guard (G (lvl caseX) (rung caseX 0)).all (fun x => decide (x < rungVal caseX 0))
#guard !((G nil (rung caseX 0)).all (fun x => decide (x < rungVal caseX 0)))

/-! The index in `SubBound` has to be `ψ_{Z[0]}(0)`; an arbitrary `W < dom X`
will not do.  For `X = ψ_{ω+1}(0)` the domain is `X` itself and `X[0] = 0`, so
the bound would have to hold against `G_u(0)`, which is empty, while `G_0` does
see something in `Z = ω + 1`. -/

def caseW : Term := psi (cons nil t1 t1) nil

#guard isOT caseW && !(dom caseW == nil) && !(dom caseW == t1) && !(dom caseW == tw)
#guard fs caseW nil == nil
#guard !((G nil (subOf (dom caseW))).all (fun x => (G nil nil ++ [nil]).any
  (fun y => decide (x ≤ y))))

end Googology.Notation.ExBuchholz.Term
