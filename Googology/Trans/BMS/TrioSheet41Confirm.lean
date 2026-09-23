import Googology.Trans.BMS.TrioSheet41
import Googology.Trans.BMS.TrioRules2Sheet

/-!
# Rows 4746, 4747, 4752 and 4753 of the trio sheet, checked by other evidence

[TRIO-SHEET-41.md](TRIO-SHEET-41.md) decides these four `S-c` rows for the sheet
of [koteitan/trio](https://github.com/koteitan/trio)
([`tools/omega_alpha_rows.tsv`](https://github.com/koteitan/trio/blob/main/tools/omega_alpha_rows.tsv)),
but only by consistency: rules 1–10 give two of them the matrix of another
ordinal.  This file records the other evidence
([TRIO-SHEET-4746.md](TRIO-SHEET-4746.md) says what it shows and what it does
not):

| row | `α` | sheet | rules 1–10 |
|---|---|---|---|
| 4746 | `Ω_{Ω_Ω}+Ω_{Ω_2}` | `M(4745) ++ s₃` | `M(4742) ++ s₃`, below `M(4745)` |
| 4747 | `Ω_{Ω_Ω}·2` | `M(4745) ++ s₃ ++ s₂` | the sheet's 4746 |
| 4752 | `Ω_{Ω_Ω}·Ω_{Ω_2}` | `M(4751) ++ s₃` | `M(4749) ++ s₃`, below `M(4751)` |
| 4753 | `Ω_{Ω_Ω}^2` | `M(4751) ++ s₃ ++ s₂` | the sheet's 4752 |

with `s₃ = (4,3,1)(5,3,1)(6,2,0)` and `s₂ = (2,2,1)(3,2,1)(4,1,0)`.
Rows 4744, 4745, 4750 and 4751 are confirmed in TRIO-SHEET-41.md (by expansion
and by shape); they are the "confirmed" rows here.

1. **The sub-unit law.**  `subLaw m` appends to `m` a copy of its last sub-unit
   `(a,L,1)(a+1,L,1)(a+2,y,0)`, where `L` is the row-1 entry of the last column.
   On 11 pairs of agreeing rows, `subLaw` sends `M(β)` to `M(β')`, where `β'`
   is `β` with its innermost successor `s+1` replaced by the least uncountable
   cardinal above `s` (`1+1 ↦ Ω`, `ω+1 ↦ Ω`, and in the towers `0+1 ↦ Ω`).
   On the confirmed rows it does the same.  Applied to the confirmed rows 4745
   and 4751 it gives the sheet's 4746 and 4752 (`Ω+1 ↦ Ω_2`), and applied again it
   gives the sheet's 4747 and 4753 (`2 ↦ Ω`).  The law fails on the pair
   4522, 4523 (`u = 2`), which is outside the 744 rows (see the last section).
2. **Order.**  The sheet's four matrices lie on the right side of all 744
   agreeing rows and of the 4 confirmed rows.  Rules 1–10's matrices for 4746
   and 4752 lie below the confirmed 4745 and 4751.  Against the 744 agreeing
   rows alone, rules 1–10 are also in order: the agreeing rows alone do not
   decide these rows.
3. **Collision.**  Rules 1–10 give 4747 the sheet's 4746, and 4753 the sheet's
   4752.
4. **Expansion.**  At `u = 1`, the agreeing rows give
   `M(Ω_Ω·(k+1)) = M(Ω_Ω·ω)[k] ++ s₂` for `k = 1, 2`.  At `u = Ω`, the sheet
   gives `M(Ω_{Ω_Ω}·2) = M(Ω_{Ω_Ω}·ω)[1] ++ s₃ ++ s₂`: the same form, with the
   upgrade `s₃ ++ s₂` of the leaf `Ω_{Ω+1}` in place of the upgrade `s₂` of `Ω_2`.
   At `u = 2` (rows 4522–4524, misprint corrected) the form has one sub-unit, as
   at `u = 1`.  That is the rules' shape at `u = Ω`, so this part alone does not
   decide.
5. **The level of the last term.**  In `M[1]`, the row-1 entry of the first
   new column is `k` when the last term of `α` has a fundamental sequence at the
   level `Ω_{k+1}`: `k = 0` for a final `Ω` or `Ω_Ω` (their sequences run
   through countable `ψ_0` terms), `k = 1` for `Ω_2`, `k = 2` for `Ω_3`.  This
   holds on 83 agreeing rows.  `Ω_{Ω_2}` diagonalises at `Ω_2`, and `Ω_{Ω_Ω}`
   at `Ω_1`.  The sheet gives `1, 0, 1, 0` on the four rows.  Rules 1–10 give
   `1, 1, 1, 1`, so their 4747 and 4753 have the wrong level.  This part also
   explains `u = 2`: there one sub-unit ends at `Ω_2`, the level of `Ω_{Ω_2}·2`.

All of it is `#guard`s: a calibration, not a theorem.
-/

namespace Googology.Trans.BMS.TrioConfirm

open Googology.Trans.BMS.TrioRules (ruleOf parse cmpOrd Od)
open Googology.Trans.BMS.TrioRules2 (trioRuleMatrixOf2 cmpMat chosen)
open Googology.Trans.BMS (expandRL)

/-! ## The sheet's matrices -/

/-- Sheet row 4744, `Ω_{Ω_Ω}+Ω_Ω` (confirmed). -/
def sheet4744 : List (List Nat) := [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,1],[4,1,0],[3,2,0],[4,3,1],[5,3,1],[6,3,0],[4,3,1],[5,3,1],[6,2,0],[5,3,0],[6,4,1],[7,4,1],[8,3,0],[7,4,0],[8,5,1],[9,5,1],[10,2,0],[2,2,1],[3,2,1],[4,1,0]]
/-- Sheet row 4745, `Ω_{Ω_Ω}+Ω_{Ω+1}` (confirmed). -/
def sheet4745 : List (List Nat) := [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,1],[4,1,0],[3,2,0],[4,3,1],[5,3,1],[6,3,0],[4,3,1],[5,3,1],[6,2,0],[5,3,0],[6,4,1],[7,4,1],[8,3,0],[7,4,0],[8,5,1],[9,5,1],[10,3,0]]
/-- Sheet row 4746, `Ω_{Ω_Ω}+Ω_{Ω_2}`. -/
def sheet4746 : List (List Nat) := [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,1],[4,1,0],[3,2,0],[4,3,1],[5,3,1],[6,3,0],[4,3,1],[5,3,1],[6,2,0],[5,3,0],[6,4,1],[7,4,1],[8,3,0],[7,4,0],[8,5,1],[9,5,1],[10,3,0],[4,3,1],[5,3,1],[6,2,0]]
/-- Sheet row 4747, `Ω_{Ω_Ω}·2`. -/
def sheet4747 : List (List Nat) := [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,1],[4,1,0],[3,2,0],[4,3,1],[5,3,1],[6,3,0],[4,3,1],[5,3,1],[6,2,0],[5,3,0],[6,4,1],[7,4,1],[8,3,0],[7,4,0],[8,5,1],[9,5,1],[10,3,0],[4,3,1],[5,3,1],[6,2,0],[2,2,1],[3,2,1],[4,1,0]]
/-- Sheet row 4750, `Ω_{Ω_Ω}·Ω_Ω` (confirmed). -/
def sheet4750 : List (List Nat) := [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,1],[4,1,0],[3,2,0],[4,3,1],[5,3,1],[6,3,0],[4,3,1],[5,3,1],[6,2,0],[5,3,0],[6,4,1],[7,4,1],[8,3,0],[7,4,1],[8,2,0],[2,2,1],[3,2,1],[4,1,0]]
/-- Sheet row 4751, `Ω_{Ω_Ω}·Ω_{Ω+1}` (confirmed). -/
def sheet4751 : List (List Nat) := [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,1],[4,1,0],[3,2,0],[4,3,1],[5,3,1],[6,3,0],[4,3,1],[5,3,1],[6,2,0],[5,3,0],[6,4,1],[7,4,1],[8,3,0],[7,4,1],[8,3,0]]
/-- Sheet row 4752, `Ω_{Ω_Ω}·Ω_{Ω_2}`. -/
def sheet4752 : List (List Nat) := [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,1],[4,1,0],[3,2,0],[4,3,1],[5,3,1],[6,3,0],[4,3,1],[5,3,1],[6,2,0],[5,3,0],[6,4,1],[7,4,1],[8,3,0],[7,4,1],[8,3,0],[4,3,1],[5,3,1],[6,2,0]]
/-- Sheet row 4753, `Ω_{Ω_Ω}^2`. -/
def sheet4753 : List (List Nat) := [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,1],[4,1,0],[3,2,0],[4,3,1],[5,3,1],[6,3,0],[4,3,1],[5,3,1],[6,2,0],[5,3,0],[6,4,1],[7,4,1],[8,3,0],[7,4,1],[8,3,0],[4,3,1],[5,3,1],[6,2,0],[2,2,1],[3,2,1],[4,1,0]]

/-- The sub-unit `s₃`. -/
def s3 : List (List Nat) := [[4,3,1],[5,3,1],[6,2,0]]
/-- The sub-unit `s₂`. -/
def s2 : List (List Nat) := [[2,2,1],[3,2,1],[4,1,0]]

-- The corrected rules (`TrioRules2.lean`) give these eight matrices.
#guard trioRuleMatrixOf2 "(W_W_W+W_W)" = some sheet4744
#guard trioRuleMatrixOf2 "(W_W_W+W_(W+1))" = some sheet4745
#guard trioRuleMatrixOf2 "(W_W_W+W_W_2)" = some sheet4746
#guard trioRuleMatrixOf2 "(W_W_W*2)" = some sheet4747
#guard trioRuleMatrixOf2 "(W_W_W*W_W)" = some sheet4750
#guard trioRuleMatrixOf2 "(W_W_W*W_(W+1))" = some sheet4751
#guard trioRuleMatrixOf2 "(W_W_W*W_W_2)" = some sheet4752
#guard trioRuleMatrixOf2 "(W_W_W^2)" = some sheet4753

/-! ## 1. The sub-unit law -/

/-- The last sub-unit `(a,L,1)(a+1,L,1)(a+2,y,0)` of `m`. -/
def findSubL (m : List (List Nat)) (L : Nat) : Option (List (List Nat)) :=
  ((List.range m.length).reverse.find? fun i =>
    match m[i]?, m[i+1]?, m[i+2]? with
    | some [a, l, 1], some [b, l', 1], some [c, _, 0] =>
      l == L && l' == L && b == a + 1 && c == a + 2
    | _, _, _ => false).map fun i => (m.drop i).take 3

/-- `m` followed by a copy of its last sub-unit at the height of its last
column, when `m` ends with a `z = 0` column. -/
def subLaw (m : List (List Nat)) : Option (List (List Nat)) :=
  match m.getLast? with
  | some [_, L, 0] => (findSubL m L).map (m ++ ·)
  | _ => none

-- Agreeing rows: `W ↦ W_W ↦ W_W_W ↦ W_W_W_W ↦ …` (`0+1 ↦ Ω`, towers) …
#guard subLaw (ruleOf "W") = some (ruleOf "W_W")
#guard subLaw (ruleOf "W_W") = some (ruleOf "W_W_W")
#guard subLaw (ruleOf "W_W_W") = some (ruleOf "W_W_W_W")
#guard subLaw (ruleOf "W_W_W_W") = some (ruleOf "W_W_W_W_W")
#guard subLaw (ruleOf "W_W_W_W_W") = some (ruleOf "W_W_W_W_W_W")
-- … a final `Ω_2 ↦ Ω_Ω` (`1+1 ↦ Ω`) …
#guard subLaw (ruleOf "(W_W+W_2)") = some (ruleOf "(W_W*2)")
#guard subLaw (ruleOf "(W_W*W_2)") = some (ruleOf "(W_W^2)")
#guard subLaw (ruleOf "W_(W_W+W_2)") = some (ruleOf "W_(W_W*2)")
#guard subLaw (ruleOf "W_(W_W*W_2)") = some (ruleOf "W_(W_W^2)")
-- … and a final `Ω_{ω+1} ↦ Ω_Ω` (`ω+1 ↦ Ω`).
#guard subLaw (ruleOf "(W_W_w+W_(w+1))") = some (ruleOf "(W_W_w+W_W)")
#guard subLaw (ruleOf "(W_W_w*W_(w+1))") = some (ruleOf "(W_W_w*W_W)")
-- Confirmed rows (TRIO-SHEET-41.md): `Ω_2 ↦ Ω_Ω` again.
#guard subLaw (ruleOf "(W_W_W+W_2)") = some sheet4744
#guard subLaw (ruleOf "(W_W_W*W_2)") = some sheet4750
#guard subLaw (ruleOf "(W_(W+1)+W_2)") = trioRuleMatrixOf2 "(W_(W+1)+W_W)"
-- The four rows: `Ω_{Ω+1} ↦ Ω_{Ω_2}` (`Ω+1 ↦ Ω_2`), then `Ω_{Ω_2} ↦ Ω_{Ω_Ω}` (`2 ↦ Ω`).
#guard subLaw sheet4745 = some sheet4746
#guard subLaw sheet4746 = some sheet4747
#guard subLaw sheet4751 = some sheet4752
#guard subLaw sheet4752 = some sheet4753
#guard sheet4746 = sheet4745 ++ s3 ∧ sheet4747 = sheet4746 ++ s2
#guard sheet4752 = sheet4751 ++ s3 ∧ sheet4753 = sheet4752 ++ s2
-- Rules 1–10 add the sub-unit `s₃` to the `Ω_2` leaf of 4742 / 4749, …
#guard ruleOf "(W_W_W+W_W_2)" = ruleOf "(W_W_W+W_2)" ++ s3
#guard ruleOf "(W_W_W*W_W_2)" = ruleOf "(W_W_W*W_2)" ++ s3
-- … and write `·2`, `^2` with one sub-unit where the law needs two.
#guard ruleOf "(W_W_W*2)" = sheet4745 ++ s3
#guard ruleOf "(W_W_W^2)" = sheet4751 ++ s3

/-! ## 2. Order -/

-- The chains of the sheet, with the agreeing rows 4748 and 4754 above them.
#guard cmpMat sheet4745 sheet4746 = .lt ∧ cmpMat sheet4746 sheet4747 = .lt ∧
  cmpMat sheet4747 (ruleOf "(W_W_W*w)") = .lt
#guard cmpMat sheet4751 sheet4752 = .lt ∧ cmpMat sheet4752 sheet4753 = .lt ∧
  cmpMat sheet4753 (ruleOf "psi_W_(W_W+1)(W_(W_W+1))") = .lt
-- Rules 1–10 put 4746 and 4752 below the confirmed 4745 and 4751.
#guard (do cmpOrd (← parse "(W_W_W+W_W_2)") (← parse "(W_W_W+W_(W+1))")) = some Ordering.gt
#guard cmpMat (ruleOf "(W_W_W+W_W_2)") sheet4745 = .lt
#guard (do cmpOrd (← parse "(W_W_W*W_W_2)") (← parse "(W_W_W*W_(W+1))")) = some Ordering.gt
#guard cmpMat (ruleOf "(W_W_W*W_W_2)") sheet4751 = .lt

/-- The labels of the 39 decided rows of TRIO-SHEET-41.md (3439 and 3480 left out),
under their corrected labels, as `chosen` lists them. -/
def decided : List String :=
  ["(w^5*2)", "(w^w+2)", "(w^w+w2)", "(W^(w+1))", "(W_2*2+w^2)", "(W_w*w+W_w+1)",
   "(W_w*w+W_w*2)", "(W_w*W_2*w)", "psi_W_(w+1)(W_W_w)",
   "psi_W_(w+1)(W_psi_W_(w+1)(W_(w+1)))", "(W_(w+1)+W_w^2)", "(W_(w+1)*2+W)",
   "(W_(w+2)+2)", "psi_W_(w2+2)(W_(w2+2))", "(W_(w^2+w)^W_(w^2+w))", "(W_(w^3)*W)",
   "W_(w^w*2)", "(W_(W+1)+W_W)", "(W_(W+1)*w)", "(W_(W+1)^2)", "(W_(W+w)+1)",
   "(W_(W+w)*w)", "W_psi_1(W_2)", "(W_W_w+W_w)", "(W_W_w*2)", "(W_W_w^2)",
   "W_psi_W_(w+1)(W_(w+1))", "(W_W_(w^2)*2)", "W_(psi_W_(w^2+1)(W_(w^2+1)))",
   "(W_W_W+W_W)", "(W_W_W+W_(W+1))", "(W_W_W+W_W_2)", "(W_W_W*2)", "(W_W_W*W_W)",
   "(W_W_W*W_(W+1))", "(W_W_W*W_W_2)", "(W_W_W^2)", "W_psi_W_(W+1)(W_(W+1))",
   "W_W_psi_1(W_2)"]

/-- The 744 rows where rules 1–10 and the sheet agree, with their matrices. -/
def agreeing : List (String × List (List Nat)) :=
  (chosen.filter fun s => !decided.contains s).map fun s => (s, ruleOf s)

/-- The 4 confirmed rows of the `Ω_{Ω_Ω}` family. -/
def confirmed : List (String × List (List Nat)) :=
  [("(W_W_W+W_W)", sheet4744), ("(W_W_W+W_(W+1))", sheet4745),
   ("(W_W_W*W_W)", sheet4750), ("(W_W_W*W_(W+1))", sheet4751)]

/-- The rows of `pool` on whose side `m` does not lie as the label `lab` does. -/
def disagree (lab : String) (m : List (List Nat)) (pool : List (String × List (List Nat))) : Nat :=
  match parse lab with
  | none => pool.length + 1
  | some a => (pool.filter fun p =>
      match parse p.1 with
      | some b => cmpOrd a b != cmpMat m p.2
      | none => true).length

/-- The four rows with the sheet's matrices and rules 1–10's. -/
def four : List (String × List (List Nat) × List (List Nat)) :=
  [("(W_W_W+W_W_2)", sheet4746, ruleOf "(W_W_W+W_W_2)"),
   ("(W_W_W*2)", sheet4747, ruleOf "(W_W_W*2)"),
   ("(W_W_W*W_W_2)", sheet4752, ruleOf "(W_W_W*W_W_2)"),
   ("(W_W_W^2)", sheet4753, ruleOf "(W_W_W^2)")]

#guard decided.length = 39 ∧ decided.all chosen.contains
#guard agreeing.length = 744
-- The sheet: in order against the 744 agreeing rows and the 4 confirmed ones.
#guard four.map (fun t => disagree t.1 t.2.1 (agreeing ++ confirmed)) = [0, 0, 0, 0]
-- Rules 1–10: in order against the 744 agreeing rows too, but not against the confirmed rows.
#guard four.map (fun t => disagree t.1 t.2.2 agreeing) = [0, 0, 0, 0]
#guard four.map (fun t => disagree t.1 t.2.2 confirmed) = [1, 0, 1, 0]

/-! ## 3. Collision -/

#guard ruleOf "(W_W_W*2)" = sheet4746
#guard ruleOf "(W_W_W^2)" = sheet4752

/-! ## 4. Expansion -/

-- `u = 1`, agreeing rows 4458, 4459, 4460: `M(Ω_Ω·(k+1)) = M(Ω_Ω·ω)[k] ++ s₂`.
#guard expandRL 3 1 (ruleOf "(W_W*w)") ++ s2 = ruleOf "(W_W*2)"
#guard expandRL 3 2 (ruleOf "(W_W*w)") ++ s2 = ruleOf "(W_W*3)"
-- `u = Ω`: `M(Ω_{Ω_Ω}·ω)[1]` is the confirmed 4745, and the sheet's 4747 is it
-- followed by the upgrade `s₃ ++ s₂`; the corrected rules give `[2] ++ s₃ ++ s₂` to `·3`.
#guard expandRL 3 1 (ruleOf "(W_W_W*w)") = sheet4745
#guard expandRL 3 1 (ruleOf "(W_W_W*w)") ++ s3 ++ s2 = sheet4747
#guard some (expandRL 3 2 (ruleOf "(W_W_W*w)") ++ s3 ++ s2) = trioRuleMatrixOf2 "(W_W_W*3)"

/-! ## 5. The level of the last term -/

/-- The row-1 entry of the first new column of `m[1]`. -/
def sig (m : List (List Nat)) : Option Nat :=
  ((expandRL 3 1 m)[m.length - 1]?).bind (·[1]?)

/-- Agreeing rows whose last term is `Ω` or `Ω_Ω` (sequence at `Ω_1`). -/
def lev0 : List String :=
  ["(W*w+W)", "(W^2+W)", "(W^W)", "(W^W^W)", "(W^W^W^W)", "(W_2+W)", "(W_2+W^W)",
   "(W_2*2+W)", "(W_2*w+W)", "(W_2*W)", "(W_2*W+W)", "(W_2^2+W)", "(W_2^2*W)", "(W_2^W)",
   "(W_3+W)", "(W_3*W)", "(W_w+W)", "(W_w+W^W)", "(W_w*2+W)", "(W_w*W)", "(W_w*W^W)",
   "(W_w^2+W)", "(W_w^2+W_w*W)", "(W_w^2*W)", "(W_w^3*W)", "(W_w^W)", "(W_(w+1)+W)",
   "(W_(w+1)*W)", "(W_(w+2)+W)", "(W_(w+2)*W)", "(W_(w2)+W)", "(W_(w2)*W)",
   "(W_(w2+1)+W)", "(W_(w2+1)*W)", "(W_(w3)+W)", "(W_(w^2)+W)", "(W_(w^2)*w+W)",
   "(W_(w^2)*W)", "(W_(w^2)^W)", "(W_(w^2+1)+W)", "(W_(w^2+1)*W)", "(W_(w^2+w)+W)",
   "(W_(w^2+w)*W)", "(W_(w^2*2)+W)", "(W_(w^2*2)*W)", "(W_(w^3)+W)", "(W_W+W)",
   "(W_W*2)", "(W_W*W)", "(W_W^2)", "(W_W^W_W)", "W_(W^W)", "(W_W_w+W)", "(W_W_w+W_W)",
   "(W_W_w*W)", "(W_W_w*W_W)", "W_(W_w*W)", "W_(W_(w^2)+W)", "W_(W_W*2)", "W_(W_W^2)",
   "W_W_(W^W)"]

/-- Agreeing rows whose last term is `Ω_2` (sequence at `Ω_2`). -/
def lev1 : List String :=
  ["(W_2*w+W_2)", "(W_2*W+W_2)", "(W_2^2+W_2)", "(W_2^W_2)", "(W_2^W_2^W_2)", "(W_3+W_2)",
   "(W_3*W_2)", "(W_w+W_2)", "(W_w*W_2)", "(W_w^2+W_2)", "(W_w^2*W_2)", "(W_w^W_2)",
   "(W_W+W_2)", "(W_W*W_2)", "(W_(W+1)+W_2)", "(W_W_W+W_2)", "(W_W_W*W_2)",
   "W_(W_W+W_2)", "W_(W_W*W_2)"]

/-- Agreeing rows whose last term is `Ω_3` (sequence at `Ω_3`). -/
def lev2 : List String := ["(W_3^W_3)", "(W_w+W_3)", "(W_w*W_3)"]

#guard lev0.length + lev1.length + lev2.length = 83
#guard (lev0 ++ lev1 ++ lev2).all fun s => (agreeing.map (·.1)).contains s
#guard lev0.all fun s => sig (ruleOf s) = some 0
#guard lev1.all fun s => sig (ruleOf s) = some 1
#guard lev2.all fun s => sig (ruleOf s) = some 2
-- The confirmed rows 4744 and 4750 (`+Ω_Ω`, `·Ω_Ω`) give 0 too.
#guard sig sheet4744 = some 0 ∧ sig sheet4750 = some 0
-- The four rows: `Ω_{Ω_2}` at `Ω_2`, `Ω_{Ω_Ω}` at `Ω_1`.  The sheet gives 1, 0, 1, 0 …
#guard four.map (fun t => sig t.2.1) = [some 1, some 0, some 1, some 0]
-- … and rules 1–10 give 1, 1, 1, 1.
#guard four.map (fun t => sig t.2.2) = [some 1, some 1, some 1, some 1]

/-! ## The `+1` after a final leaf

The fixed rules place `Ω_{Ω_Ω}+Ω_{Ω_2}+1` above `Ω_{Ω_Ω}·2` (TRIO-SHEET-41.md,
"still open").  This is not evidence against the sheet's 4746 and 4747: the same
defect already appears between the agreeing rows 4456 (`Ω_Ω+Ω_2`), 4457
(`Ω_Ω+Ω_ω`) and 4458 (`Ω_Ω·2`), where both rule sets give `Ω_Ω+Ω_2+1` one
matrix, above 4457 and 4458. -/

#guard ruleOf "(W_W+W_2+1)" = (trioRuleMatrixOf2 "(W_W+W_2+1)").getD []
#guard (do cmpOrd (← parse "(W_W+W_2+1)") (← parse "(W_W+W_w)")) = some Ordering.lt
#guard cmpMat (ruleOf "(W_W+W_2+1)") (ruleOf "(W_W+W_w)") = .gt
#guard cmpMat (ruleOf "(W_W+W_2+1)") (ruleOf "(W_W*2)") = .gt
#guard cmpMat ((trioRuleMatrixOf2 "(W_W_W+W_W_2+1)").getD []) sheet4747 = .gt

/-! ## The pair 4522, 4523 (`u = 2`), outside the 744 rows

Rows 4519–4535 are among the 28 rows whose sheet matrix is not standard, so they
are not among the 744 agreeing rows.  In 4522, 4523 and 4524 the only defect is the
misprint `(4,4,1)` for `(4,3,1)` (the same misprint as in row 4533).  Corrected,
the sheet gives rules 1–10's matrix.  On this pair the relabelling of part 1 fails:
`subLaw M(Ω_{Ω_2}+Ω_3) = M(Ω_{Ω_2}·2)`, where the law would give `Ω_{Ω_2}+Ω_Ω`.
With `M(Ω_{Ω_2}·ω)[1] = M(Ω_{Ω_2}+Ω_3)`, it says that at `u = 2` (as at `u = 1`)
`M(Ω_{Ω_u}·2)` is `M(Ω_{Ω_u}·ω)[1]` followed by one sub-unit.  That is the shape of
rules 1–10 at `u = Ω`.  Part 5 separates the two cases: the one sub-unit ends at level
`Ω_2` (`sig = 1`) in both, which is right for `Ω_{Ω_2}·2` and wrong for
`Ω_{Ω_Ω}·2`. -/

/-- Replace the misprint `(4,4,1)` at column 16 by `(4,3,1)`. -/
def fix441 (m : List (List Nat)) : List (List Nat) := m.set 16 [4,3,1]

/-- Sheet row 4522, `Ω_{Ω_2}+Ω_3`, as printed. -/
def sheet4522 : List (List Nat) := [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,1],[4,2,0],[2,2,0],[3,3,1],[4,4,1],[5,3,0],[3,3,1],[4,3,1],[5,2,0],[4,3,0],[5,4,1],[6,4,1],[7,3,0],[6,4,0],[7,5,1],[8,5,1],[9,3,0]]
/-- Sheet row 4523, `Ω_{Ω_2}·2`, as printed. -/
def sheet4523 : List (List Nat) := [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,1],[4,2,0],[2,2,0],[3,3,1],[4,4,1],[5,3,0],[3,3,1],[4,3,1],[5,2,0],[4,3,0],[5,4,1],[6,4,1],[7,3,0],[6,4,0],[7,5,1],[8,5,1],[9,3,0],[3,3,1],[4,3,1],[5,2,0]]
/-- Sheet row 4524, `Ω_{Ω_2}·ω`, as printed. -/
def sheet4524 : List (List Nat) := [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,1],[4,2,0],[2,2,0],[3,3,1],[4,4,1],[5,3,0],[3,3,1],[4,3,1],[5,2,0],[4,3,0],[5,4,1],[6,4,1],[7,3,0],[6,4,1]]

#guard ¬ (agreeing.map (·.1)).contains "(W_W_2+W_3)" ∧ ¬ (agreeing.map (·.1)).contains "(W_W_2*2)"
#guard fix441 sheet4522 = ruleOf "(W_W_2+W_3)" ∧ fix441 sheet4523 = ruleOf "(W_W_2*2)" ∧
  fix441 sheet4524 = ruleOf "(W_W_2*w)"
#guard subLaw (ruleOf "(W_W_2+W_3)") = some (ruleOf "(W_W_2*2)")
#guard expandRL 3 1 (ruleOf "(W_W_2*w)") = ruleOf "(W_W_2+W_3)"
#guard ruleOf "(W_W_2*2)" = ruleOf "(W_W_2+W_3)" ++ [[3,3,1],[4,3,1],[5,2,0]]
#guard sig (ruleOf "(W_W_2*2)") = some 1 ∧ sig (ruleOf "(W_W_W*2)") = some 1 ∧ sig sheet4747 = some 0

end Googology.Trans.BMS.TrioConfirm
