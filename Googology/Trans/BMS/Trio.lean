import Googology.Trans.BMS.ExBuchholz
import Googology.Trans.BMS.EntriesR

/-!
# The trio matrix of `ψ_0(Ω_α)`

A reading for the matrices at three rows needs a stated rule, and there is
one: [koteitan/trio](https://github.com/koteitan/trio) writes down the map
from `ψ_0(Ω_α)` to the standard forms of the trio sequence system (the `z < 2`
fragment of the three-row Bashicu matrices), with the general formula on its
[algorithm page](https://github.com/koteitan/trio/blob/main/ebp2bms/algorithm/1/README-en.md)
and the values in its
[table](https://github.com/koteitan/trio/blob/main/ebp2bms/sheet/1/README-en.md).
This file transcribes the formula for `α < ε₀` and checks it against that
table.

The shape is the Cantor normal form read at three levels.  Writing
`α = Σ_i ω^{β_i}` and `1 + β_i' = β_i` and `β_i' = Σ_j ω^{γ_ij}`:

* each summand `ω^{β_i}` is an **add unit** — an anchor `(r+1, i-1, 0)` that
  rebuilds the previous unit's address in `z = 0` form, then the body;
* the body is a **root** `(x₀, i, 1)` carrying the leading `1` of `β_i`, then
  one **multiply unit** per summand of `β_i'`;
* a multiply unit is a **digit** `(x₀+1, i, 1)` and the **primitive-sequence
  embedding** of `γ_ij` — which is exactly `unread`, the one-row matrix this
  library already has, offset in row `0`.

So addition is the number of add units, multiplication the number of multiply
units, and exponentiation the shape of the one-row embedding.  Nothing here is
proved: `omegaIndexMatrix` is a transcription, and the `#guard`s below are the
calibration against the published table.

Two further checks were run outside Lean, against the reference
implementation in [yaBMS](https://github.com/koteitan/yaBMS), on the thirty
matrices the `#guard`s below produce — the twenty of the `α < ε₀` table, the
seven collapse values and `M(Ω_v)` for `v = 1, 2, 3`.  Every one of them is a
standard form (`bms -s` answers `1` on all thirty), and the map is
order-preserving on the first twenty: taking the table's rows in increasing
`α`, each matrix compares `<` with the next (`bms -c`).  Neither is a theorem
here; both are what the one-row case has as `std_entries_iff` and
`val_lt_val`.
-/

namespace Googology.Trans.BMS

open Googology.Notation.ExBuchholz
open Googology.Notation.ExBuchholz.Term

/-- The primitive-sequence embedding `P(γ)` at `x`: the one-row matrix of `γ`
offset by `x`, in columns whose rows `1` and `2` are `0`. -/
def prSS (x : Nat) (γ : Term) : List (List Nat) :=
  (unread 0 γ).map (fun e => [x + e, 0, 0])

/-- Whether the term is a finite ordinal: every summand is `ψ_0(0) = 1`. -/
def isFiniteT : Term → Bool
  | nil => true
  | cons _ b t => (b == nil) && isFiniteT t

/-- The term with its last summand dropped. -/
def dropLastT : Term → Term
  | nil => nil
  | cons a b t => if t == nil then nil else cons a b (dropLastT t)

/-- `β'`, the term with `1 + β' = β`: the same term above `ω`, one summand
shorter when the term is finite. -/
def peelOne (β : Term) : Term := if isFiniteT β then dropLastT β else β

/-- The multiply units of one add unit: a digit and an embedding per summand
of `β'`. -/
def mulUnits (x0 y : Nat) : Term → List (List Nat)
  | nil => []
  | cons _ g t => ([x0 + 1, y, 1] :: prSS (x0 + 2) g) ++ mulUnits x0 y t

/-- The body of an add unit: the root and the multiply units. -/
def bodyU (β : Term) (x0 y : Nat) : List (List Nat) :=
  [x0, y, 1] :: mulUnits x0 y (peelOne β)

/-- The add units.  `rp1` is `r + 1`, the anchor's `x`, where `r` is the
previous add unit's root; `lastX` is the `x` of the last column, for the chain
of `β = 0` units; `i` is the level. -/
def addUnits (rp1 lastX : Nat) (prevZero : Bool) (i : Nat) : Term → List (List Nat)
  | nil => []
  | cons _ b t =>
      if b == nil then
        if prevZero then
          [lastX + 1, i, 0] :: addUnits rp1 (lastX + 1) true (i + 1) t
        else
          [rp1, i - 1, 0] :: [rp1 + 1, i, 0] :: addUnits rp1 (rp1 + 1) true (i + 1) t
      else
        ([rp1, i - 1, 0] :: bodyU b (rp1 + 1) i) ++
          addUnits (rp1 + 2) (rp1 + 1) false (i + 1) t

/-- **The trio matrix of `ψ_0(Ω_α)`**, for `α < ε₀` written as a term whose
subscripts are all `0`.  Columns are `[x, y, z]`, the three rows. -/
def omegaIndexMatrix (α : Term) : List (List Nat) := addUnits 0 0 false 1 α

/-! ### Calibration against the published table

The left column is `α`; the matrix is the one the table gives for
`ψ_0(Ω_α)`.  `tw` is `ω` and `t1` is `1`, so `psi nil X` is `ω^X`. -/

/-- `ω^a` as a term. -/
abbrev opowT (a : Term) : Term := psi nil a

-- `ψ_0(Ω_1) = ε₀` is the pair sequence `(0,0)(1,1)`.
#guard omegaIndexMatrix t1 = [[0,0,0],[1,1,0]]

-- `ψ_0(Ω_2)`, the Bachmann-Howard ordinal, is `(0,0)(1,1)(2,2)`.
#guard omegaIndexMatrix (addT t1 t1) = [[0,0,0],[1,1,0],[2,2,0]]

#guard omegaIndexMatrix (addT t1 (addT t1 t1)) = [[0,0,0],[1,1,0],[2,2,0],[3,3,0]]

#guard omegaIndexMatrix (opowT t1) = [[0,0,0],[1,1,1]]

#guard omegaIndexMatrix (addT (opowT t1) t1) = [[0,0,0],[1,1,1],[2,1,0],[3,2,0]]

#guard omegaIndexMatrix (addT (opowT t1) (addT t1 t1))
  = [[0,0,0],[1,1,1],[2,1,0],[3,2,0],[4,3,0]]

#guard omegaIndexMatrix (addT (opowT t1) (opowT t1)) = [[0,0,0],[1,1,1],[2,1,0],[3,2,1]]

#guard omegaIndexMatrix (addT (opowT t1) (addT (opowT t1) t1))
  = [[0,0,0],[1,1,1],[2,1,0],[3,2,1],[4,2,0],[5,3,0]]

#guard omegaIndexMatrix (addT (opowT t1) (addT (opowT t1) (opowT t1)))
  = [[0,0,0],[1,1,1],[2,1,0],[3,2,1],[4,2,0],[5,3,1]]

#guard omegaIndexMatrix (opowT (addT t1 t1)) = [[0,0,0],[1,1,1],[2,1,1]]

#guard omegaIndexMatrix (addT (opowT (addT t1 t1)) t1)
  = [[0,0,0],[1,1,1],[2,1,1],[2,1,0],[3,2,0]]

#guard omegaIndexMatrix (addT (opowT (addT t1 t1)) (opowT t1))
  = [[0,0,0],[1,1,1],[2,1,1],[2,1,0],[3,2,1]]

#guard omegaIndexMatrix (addT (opowT (addT t1 t1)) (opowT (addT t1 t1)))
  = [[0,0,0],[1,1,1],[2,1,1],[2,1,0],[3,2,1],[4,2,1]]

#guard omegaIndexMatrix (opowT (addT t1 (addT t1 t1)))
  = [[0,0,0],[1,1,1],[2,1,1],[2,1,1]]

#guard omegaIndexMatrix (opowT (opowT t1)) = [[0,0,0],[1,1,1],[2,1,1],[3,0,0]]

#guard omegaIndexMatrix (addT (opowT (opowT t1)) t1)
  = [[0,0,0],[1,1,1],[2,1,1],[3,0,0],[2,1,0],[3,2,0]]

#guard omegaIndexMatrix (opowT (addT (opowT t1) t1))
  = [[0,0,0],[1,1,1],[2,1,1],[3,0,0],[2,1,1]]

#guard omegaIndexMatrix (opowT (opowT (opowT t1)))
  = [[0,0,0],[1,1,1],[2,1,1],[3,0,0],[4,0,0]]

#guard omegaIndexMatrix (opowT (opowT (opowT (opowT t1))))
  = [[0,0,0],[1,1,1],[2,1,1],[3,0,0],[4,0,0],[5,0,0]]

#guard omegaIndexMatrix (opowT (addT (opowT (addT t1 t1)) (opowT (addT t1 t1))))
  = [[0,0,0],[1,1,1],[2,1,1],[3,0,0],[3,0,0],[2,1,1],[3,0,0],[3,0,0]]

/-! ### Collapse values and the uncountable base

Two more clauses of the
[algorithm for `ε₀ ≤ α < Λ`](https://github.com/koteitan/trio/blob/main/ebp2bms/algorithm/2/README-en.md)
are stated closed, and this section transcribes them.  When `α` is itself a
collapse `ψ_0(Ω_X)`, the matrix of the subscript goes in unchanged, three
columns to the right; and `M(Ω_1)` is the base the uncountable region is built
from, with one cardinal successor per lift.  The calibration is against the
[table for that range](https://github.com/koteitan/trio/blob/main/ebp2bms/sheet/2/README-en.md).
-/

/-- Shift every column's `x`. -/
def shiftX (d : Nat) (m : List (List Nat)) : List (List Nat) :=
  m.map (fun c => match c with | [x, y, z] => [x + d, y, z] | c => c)

/-- The lift `L(x, y, z) = (x+1, y+1, z)`. -/
def liftC (m : List (List Nat)) : List (List Nat) :=
  m.map (fun c => match c with | [x, y, z] => [x + 1, y + 1, z] | c => c)

/-- `M(Ω_1)`, the base of the uncountable region. -/
def omegaOneMatrix : List (List Nat) := [[0,0,0],[1,1,1],[2,1,1],[3,1,0]]

/-- `M(Ω_v)` for a finite `v`: one lift of the base per cardinal successor. -/
def omegaFinMatrix (v : Nat) : List (List Nat) :=
  (List.range v).flatMap (fun i => liftC^[i] omegaOneMatrix)

/-- **The trio matrix of `ψ_0(Ω_α)`**, with `α` a collapse value taken apart
recursively.  `α < ε₀` falls through to `omegaIndexMatrix`. -/
def trioMatrix : Term → List (List Nat)
  | cons nil (cons X nil nil) nil =>
      if X == nil then omegaIndexMatrix (cons nil (cons nil nil nil) nil)
      else [[0,0,0],[1,1,1],[2,1,1]] ++ shiftX 3 (trioMatrix X)
  | α => omegaIndexMatrix α

-- `ψ_0(Ω_{ε₀})`, where `ε₀ = ψ_0(Ω_1)` is `te0`.
#guard trioMatrix te0 = [[0,0,0],[1,1,1],[2,1,1],[3,0,0],[4,1,0]]

-- `ψ_0(Ω_{ψ_0(Ω_2)})`.
#guard trioMatrix (psi nil (psi (addT t1 t1) nil))
  = [[0,0,0],[1,1,1],[2,1,1],[3,0,0],[4,1,0],[5,2,0]]

-- `ψ_0(Ω_{ψ_0(Ω_ω)})`.
#guard trioMatrix (psi nil (psi (opowT t1) nil))
  = [[0,0,0],[1,1,1],[2,1,1],[3,0,0],[4,1,1]]

-- `ψ_0(Ω_{ψ_0(Ω_{ω+1})})`.
#guard trioMatrix (psi nil (psi (addT (opowT t1) t1) nil))
  = [[0,0,0],[1,1,1],[2,1,1],[3,0,0],[4,1,1],[5,1,0],[6,2,0]]

-- `ψ_0(Ω_{ψ_0(Ω_{ω·2})})`.
#guard trioMatrix (psi nil (psi (addT (opowT t1) (opowT t1)) nil))
  = [[0,0,0],[1,1,1],[2,1,1],[3,0,0],[4,1,1],[5,1,0],[6,2,1]]

-- `ψ_0(Ω_{ψ_0(Ω_{ω²})})`.
#guard trioMatrix (psi nil (psi (opowT (addT t1 t1)) nil))
  = [[0,0,0],[1,1,1],[2,1,1],[3,0,0],[4,1,1],[5,1,1]]

-- `ψ_0(Ω_{ψ_0(Ω_{ω^ω})})`.
#guard trioMatrix (psi nil (psi (opowT (opowT t1)) nil))
  = [[0,0,0],[1,1,1],[2,1,1],[3,0,0],[4,1,1],[5,1,1],[6,0,0]]

#guard omegaFinMatrix 1 = [[0,0,0],[1,1,1],[2,1,1],[3,1,0]]

#guard omegaFinMatrix 2
  = [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,0],[2,2,1],[3,2,1],[4,2,0]]

end Googology.Trans.BMS
