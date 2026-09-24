import Googology.Trans.DBMS.ThreeRowUpperNCInv

/-!
# The upper bound at `n = 2`, reduced to one shape

`ThreeRowUpperNC.lean` reduces `rkL 2 (cgen 2 4) = rkL 2 (bgen3 2)` to
`T3nRankDesc`: the nested raise `t3n` lowers the rank with every expansion on
the matrices `SReach` reached from `(cgen 2 4)[v]`.
`ThreeRowUpperNCInv.lean` shows that on `SReach`, outside the shape
`RaisedPar` (the row-`2` parent of the last column is raisable), `t3n`
commutes with expansion, `(t3n C)[N] = t3n (C[N])`.  There
`rkL 2 (t3n (C[N])) = rkL 2 ((t3n C)[N]) < rkL 2 (t3n C)` by `rkL_lt`.

So `T3nRankDesc` reduces to the shape `RaisedPar` (`t3nRankDesc_of_RP`), and
the equality of the two ranks follows from the open statement
`T3nRankDescRP` (`rkL_cgen_two_four_eq_of_RP`).

**Open.**  `T3nRankDescRP`: for `C ∈ SReach` with `RaisedPar C` and every `N`,
`rkL 2 (t3n (C[N])) < rkL 2 (t3n C)`.  There `t3n` does not commute with the
expansion: in `C` the last column `z = (z₀,z₁,1)` has as row-`2` parent a
raisable column `y = (a,1,0)`; in `t3n C` the column `y` is `(a,1,1)`, so the
row-`2` parent of `z` moves down to the row-`1` parent of `y`, which changes
the bad root.  In `t3n (C[N])` the copies of `y` are `(a+q·d₀, 1+q·d₁, 0)` with
`d₁ ≥ 1`, and are not raised.

Numerically (breadth-first from `lift 3 (trioGen v)`, `v ≤ 3`, depth `≤ 10`,
at most `14` columns, `6639` matrices, `N ≤ 2`, `19914` pairs): `RaisedPar`
occurs in `678` pairs; the commutation holds on the other `19236`.  On all
`678`, both `t3n C` and `t3n (C[N])` have an explicit path of expansions from a
trio generator (so both are in `TrioStdL`), and `t3n (C[N]) < t3n C` in the
dictionary order; by `rkL_lt_of_trio` this gives the rank inequality for each
of these pairs.
-/

namespace Googology.Trans.DBMS

open Ordinal Order
open Googology.Trans.BMS

/-- **Open.**  `t3n` lowers the rank with every expansion, on the reached
matrices in the shape `RaisedPar`. -/
def T3nRankDescRP : Prop :=
  ∀ C, SReach C → RaisedPar C → ∀ N, rkL 2 (t3n (expandRL 3 N C)) < rkL 2 (t3n C)

/-- **Outside `RaisedPar`, `t3n` lowers the rank with every expansion.** -/
theorem rkL_t3n_expand_lt_of_not_RP {C : List (List Nat)} (hC : SReach C) (hne : C ≠ [])
    (hnp : ¬ RaisedPar C) (N : Nat) : rkL 2 (t3n (expandRL 3 N C)) < rkL 2 (t3n C) := by
  rw [← expandRL_t3n_of_sReach hC hnp N]
  exact rkL_lt (valid_t3n hC.valid) (t3n_ne_nil hne) N

/-- **`T3nRankDesc` reduces to the shape `RaisedPar`.** -/
theorem t3nRankDesc_of_RP (h : T3nRankDescRP) : T3nRankDesc := by
  intro C hC hne N
  by_cases hnp : RaisedPar C
  · exact h C hC hnp N
  · exact rkL_t3n_expand_lt_of_not_RP hC hne hnp N

/-- **The upper bound at `n = 2` under the reduced hypothesis**: the DBMS content
`(0,0,0)(1,1,0)(2,2,1)(3,3,2)` and the BMS matrix `(0,0,0)(1,1,1)(2,2,2)` have
the same rank. -/
theorem rkL_cgen_two_four_eq_of_RP (h : T3nRankDescRP) : rkL 2 (cgen 2 4) = rkL 2 (bgen3 2) :=
  rkL_cgen_two_four_eq_of_t3n (t3nRankDesc_of_RP h)

end Googology.Trans.DBMS

#print axioms Googology.Trans.DBMS.t3nRankDesc_of_RP
#print axioms Googology.Trans.DBMS.rkL_cgen_two_four_eq_of_RP
