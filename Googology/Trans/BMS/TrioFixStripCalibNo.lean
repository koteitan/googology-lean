import Googology.Trans.BMS.TrioFixStripCalibRead

/-!
# `CalibSt` is false: the fuel runs out

`TrioFixStripTree.CalibSt` states that the patched program `trioMatrixLSt` (the reading
`ofTermFix` and the corrected rule 1 `stripSt`) computes `trioE2` on **every** standard
countable term with subscripts `0`/`1`.  That is false, for the same reason as for the old
map (`TrioTree.lean`, "The fuel is not enough"): every recursion of the program carries a
fuel of `200`, and the program stops going down when the fuel runs out.

The witness is the tower `T_k = ψ_0(ψ_0(⋯ψ_0(0)⋯))` (`k` copies of `ψ_0`, nesting depth `k`,
below `ε₀`).  `T_202 ≠ T_203` are standard, countable, with subscript `0` only, and
the program gives them one matrix (`trioMatrixLSt_T202`, checked in the kernel).  `trioE2` is
injective on the fragment (`TrioFixStripTree.trioE2_injective`), so `CalibSt` would give
`T_202 = T_203`.

Where the fuel runs out (the compiled checks at the end of the file, not theorems):

* towers `T_k` (depth `k`): `trioMatrixLSt T_k = trioE2 T_k` for `k ≤ 202`, not for
  `k = 203`; the matrices of `T_k` and `T_{k+1}` are equal from `k = 202` on;
* `ψ_0(Ω + T_k)` (depth `k + 1`): agrees for `k ≤ 200`, not for `k = 201`;
* `ψ_0(ψ_1(T_k))` (depth `k + 2`): agrees for `k ≤ 198`, not for `k = 199`.

So on these families the program first fails at nesting depth `201`–`203`.
The statement that is proved carries a depth bound (`TrioFixStripCalib.lean`:
`rdT α ≤ 100`, implied by `dep α ≤ 50`).

**Open: `CalibRd200`**, the same with `rdT α ≤ 200`.  Not proved.  The proof of the bound
`100` pays the fuel for the *sum* of the depths of two compared readings (a `ψ` atom
facing an `ω`-power keeps its depth for one step, `TrioFixStripCalibRead.sc_step`), so it
cannot reach `200` as it stands.  Numerically, on nine families of deep terms (the checks
at the end), the program agrees with `trioE2` at every member with `rdT ≤ 200` tried, and
fails first at `rdT = 201` (`ψ_0(ψ_1(T_199))`), so `200` cannot be raised.

(An earlier draft of this file used `ψ_0(ψ_1(G₆₆) + 1) + ψ_0(ψ_1(G₆₅) + 1)` as the witness;
that is wrong: the program separates those two terms and agrees with `trioE2` on
`G_k = ψ_0(ψ_1(G_{k-1}) + 1)` up to `k = 100`, depth `200`, first failing at `k = 101`;
the sum `G_68 + G_67` (depth `136`, `rdT = 205`) is the first failing member of that family.)
-/

namespace Googology.Trans.BMS.TrioFixStripCalibNo

open Googology.Notation.ExBuchholz
open Googology.Notation.ExBuchholz.Term
open Googology.Trans.BMS.TrioTree (Sub01 towerP)
open Googology.Trans.BMS.TrioFixStrip (trioMatrixLSt)
open Googology.Trans.BMS.TrioFixStripTree (trioE2 trioE2_injective CalibSt)
open Googology.Trans.BMS.TrioFixStripCalib (rdT)

theorem sub01_towerP : ∀ k : Nat, Sub01 (towerP k)
  | 0 => trivial
  | k + 1 => ⟨Or.inl rfl, sub01_towerP k, trivial⟩

theorem towerP_ne : towerP 202 ≠ towerP 203 := by decide +kernel

theorem OT_T202 : OT (towerP 202) := by decide +kernel
theorem OT_T203 : OT (towerP 203) := by decide +kernel
theorem T202_lt_tW : towerP 202 < tW := by decide +kernel
theorem T203_lt_tW : towerP 203 < tW := by decide +kernel

/-- **The patched map gives `T_202` and `T_203` one matrix** (checked in the kernel). -/
theorem trioMatrixLSt_T202 : trioMatrixLSt (towerP 202) = trioMatrixLSt (towerP 203) := by
  decide +kernel

/-- **The patched map is not injective on the fragment**: two different standard
countable terms with subscripts `0`/`1` get one matrix. -/
theorem trioMatrixLSt_not_injective :
    ∃ α β : Term, OT α ∧ OT β ∧ α < tW ∧ β < tW ∧ Sub01 α ∧ Sub01 β ∧ α ≠ β ∧
      trioMatrixLSt α = trioMatrixLSt β :=
  ⟨_, _, OT_T202, OT_T203, T202_lt_tW, T203_lt_tW, sub01_towerP 202, sub01_towerP 203,
    towerP_ne, trioMatrixLSt_T202⟩

/-- **`CalibSt` is false.** -/
theorem not_calibSt : ¬ CalibSt := by
  intro h
  have e1 := h _ OT_T202 T202_lt_tW (sub01_towerP 202)
  have e2 := h _ OT_T203 T203_lt_tW (sub01_towerP 203)
  exact towerP_ne (trioE2_injective OT_T202 OT_T203 T202_lt_tW T203_lt_tW
    (sub01_towerP 202) (sub01_towerP 203) (by rw [← e1, ← e2, trioMatrixLSt_T202]))

/-- **Open** (not proved): `CalibSt` with the bound `rdT α ≤ 200`.  Proved with `100`
(`TrioFixStripCalib.calibRd`); false with `201` (`ψ_0(ψ_1(T_199))`, `#guard` below). -/
def CalibRd200 : Prop :=
  ∀ α : Term, OT α → α < tW → Sub01 α → rdT α ≤ 200 → trioMatrixLSt α = trioE2 α

#print axioms not_calibSt
#print axioms trioMatrixLSt_not_injective

/-! ### Where the fuel runs out (compiled checks) -/

#guard trioMatrixLSt (towerP 202) == trioE2 (towerP 202)
#guard trioMatrixLSt (towerP 203) != trioE2 (towerP 203)
#guard trioMatrixLSt (towerP 201) != trioMatrixLSt (towerP 202)
#guard trioMatrixLSt (psi nil (cons t1 nil (towerP 200)))
  == trioE2 (psi nil (cons t1 nil (towerP 200)))
#guard trioMatrixLSt (psi nil (cons t1 nil (towerP 201)))
  != trioE2 (psi nil (cons t1 nil (towerP 201)))
#guard trioMatrixLSt (psi nil (psi t1 (towerP 198))) == trioE2 (psi nil (psi t1 (towerP 198)))
#guard trioMatrixLSt (psi nil (psi t1 (towerP 199))) != trioE2 (psi nil (psi t1 (towerP 199)))

/-! ### The boundary `rdT = 200` on nine families (compiled checks)

For each family: the last member that agrees, its `rdT`, and the first that does not. -/

/-- `G₀ = 0`, `G_{k+1} = ψ_0(ψ_1(G_k) + 1)`. -/
def G : Nat → Term
  | 0 => nil
  | k + 1 => psi nil (cons t1 (G k) t1)

def ok (a : Term) : Bool := trioMatrixLSt a == trioE2 a

/-- (name, family, first failing index `k`): all members are standard countable `Sub01`. -/
def fams : List (String × (Nat → Term) × Nat) :=
  [ ("T_k", towerP, 203),
    ("ψ_0(Ω+T_k)", fun k => psi nil (cons t1 nil (towerP k)), 201),
    ("ψ_0(ψ_1(T_k))", fun k => psi nil (psi t1 (towerP k)), 199),
    ("T_{k+1}+T_k", fun k => cons nil (towerP k) (psi nil (towerP (k-1))), 201),
    ("ψ_0(T_{k-1}+1)+T_{k+1}", fun k => cons nil (cons nil (towerP (k-1)) t1) (psi nil (towerP k)), 202),
    ("ψ_0(Ω+ψ_0(T_{k-1}+1))+ψ_0(Ω+T_k)", fun k =>
      cons nil (cons t1 nil (cons nil (towerP (k-1)) t1)) (psi nil (cons t1 nil (towerP k))), 201),
    ("ψ_0(ψ_1(T_k)+1)+ψ_0(ψ_1(T_k))", fun k =>
      cons nil (cons t1 (towerP k) t1) (psi nil (psi t1 (towerP k))), 199),
    ("G_k", G, 101),
    ("ψ_0(ψ_1(G_{k-1})+1)+ψ_0(ψ_1(G_{k-2})+1)", fun k =>
      cons nil (cons t1 (G (k-1)) t1) (psi nil (cons t1 (G (k-2)) t1)), 68) ]

#guard fams.all fun (_, f, k) => isOT (f (k-1)) && isOT (f k) && decide (f k < tW)
-- the last member agrees, with `rdT ≥ 200`; the next fails, with `rdT ≥ 201`
#guard fams.all fun (_, f, k) => ok (f (k-1)) && 200 ≤ rdT (f (k-1)) && !ok (f k) && 201 ≤ rdT (f k)
#guard (fams.map fun (_, f, k) => (rdT (f (k-1)), rdT (f k))) =
  [(202, 203), (202, 203), (200, 201), (201, 202), (202, 203), (202, 203), (201, 202), (301, 304),
    (202, 205)]
-- `rdT ≤ 200` cannot be raised: `ψ_0(ψ_1(T_199))` has `rdT = 201` and fails.
#guard rdT (psi nil (psi t1 (towerP 199))) = 201

end Googology.Trans.BMS.TrioFixStripCalibNo
