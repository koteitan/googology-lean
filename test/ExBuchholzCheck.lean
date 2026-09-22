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

/-- All terms of size at most `n`. -/
def allTerms : Nat → List Term
  | 0 => [nil]
  | n + 1 =>
      let prev := allTerms n
      prev ++ (prev.flatMap fun a => prev.flatMap fun b => prev.map fun t =>
        cons a b t).filter (fun x => decide (size x ≤ n + 1))

/-- The countable standard forms of size at most `n`, other than `0`. -/
def ctblOT (n : Nat) : List Term :=
  (allTerms n).filter (fun X => isOT X && decide (X < tW) && !(X == nil))

/-! 109 of the 350 terms of size at most 4 are countable standard forms. -/
#guard (allTerms 4).length == 350
#guard (ctblOT 4).length == 109

/-! Every one of them, expanded at any of `0`–`4`, stays standard, stays below
`Ω`, and strictly decreases. -/
#guard (ctblOT 4).all fun X => (List.range 5).all fun n =>
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

/-! Named ordinals, expanded all the way down. -/
#guard runOT (psi nil tW) 1 0 200 == some 4                              -- ε₀
#guard runOT (psi nil tW) 2 0 400 == some 39                             -- ε₀
#guard runOT (psi nil (cons t1 nil (cons t1 nil nil))) 1 0 400 == some 10 -- ψ_0(Ω+Ω)
#guard runOT (psi nil (psi t1 t1)) 1 0 400 == some 5                     -- ψ_0(ψ_1(1))
#guard runOT (psi nil (psi t2 nil)) 1 0 800 == some 11                   -- ψ_0(Ω_2), BHO
#guard runOT (psi nil (psi tW nil)) 1 0 800 == some 8                    -- ψ_0(ψ_Ω(0))

end Googology.Notation.ExBuchholz.Term
