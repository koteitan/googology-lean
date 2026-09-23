import Googology.Trans.BMS.TrioRules2

/-!
# Fix E: the printed label of row 3552

Row 3552 of the sheet
([`tools/omega_alpha_rows.tsv`](https://github.com/koteitan/trio/blob/main/tools/omega_alpha_rows.tsv))
is printed `ψ_{Ω_{Ω+1}}(Ω_β)` with `β = ψ_{Ω_{ω+1}}(Ω_{ω+1})`.
[TRIO-SHEET-41.md](TRIO-SHEET-41.md) reads it as a label typo (the row belongs to
`ψ_{Ω_{ω+1}}(Ω_β)`), and records that the rules give a non-standard matrix for the
printed ordinal.  This file finds why, gives the matrix, and adds one correction
(Fix E) to `TrioRules2.lean`.  The explanation is in
[TRIO-SHEET-FIXES.md](TRIO-SHEET-FIXES.md).

Notation: `ψ(w)` is `ψ_{Ω_{Ω+1}}(Ω_w)`, the region between rows 4466 (`w = Ω+1`) and
4468 (`Ω_{Ω+1}`).  `P` is `M(ψ(Ω+1))` without its last column, so it ends in the
lowered leaf `(6,2,0)`.  `P₂ = M(ψ(Ω_2)) = P ++ (7,3,1)(8,3,1)(9,2,0)` (row 4467).

**Why the rules fail.**  Rule 9 writes the argument's level `w` with `writeLevel`,
which copies the tail of `M(w)` past the deepest level column that `M(w)` shares
with the ladders `M(2)`, `M(Ω+1)` and the matrix so far.  For `Ω_ω ≤ w`, `M(w)`
starts `B ++ (1,1,1)` and shares no level column with any ladder, so all of
`M(w)[1:]` is copied, and only the z1 and level columns are lifted (by 2).  The
`Ω` leaf `(3,1,0)` of `B` stays at `y = 1`.  So `ψ(Ω_ω)` gets
`P ++ (7,3,1)(8,3,1)(9,1,0)(7,3,1)`, which is below `P₂ = M(ψ(Ω_2))`, and for
`w = β` the lowered leaf `(5,1,0)` of `M(β)` also stays at `y = 1` while its level
column above it is lifted to `(8,3,0)`: the result
`P ++ (7,3,1)(8,3,1)(9,1,0)(7,3,1)(8,3,0)(9,4,1)(10,4,1)(11,1,0)(12,4,0)` is not
standard (yaBMS `bms -s`) and lies below `P₂`.

**Fix E (rule 9 for `u = Ω+1`, `Ω_ω ≤ w < Ω_{ω+1}`).**  The argument is written as
the argument `Ω_{Ω_2}` (`P₂`), then `M(w)` from its mark `(1,1,1)` on, lifted by one
storey (`x+1`, `y+1` on every column):

  `M(ψ_{Ω_{Ω+1}}(Ω_w)) = P₂ ++ L(M(w)[4:])`.

For `w = Ω_ω` this is `P₂ ++ (2,2,1)`: the leaf `(9,2,0)` naming `Ω_2` upgraded by
the mark `(2,2,1)`, placed where the base `M(Ω_{Ω+1})` already has it (rule 5), as in
row 4457 (`Ω_Ω+Ω_ω = … (8,2,0)(2,2,1)`).  Everything of level `ω` stacks on that
base as it stacks on `M(Ω_ω) = B ++ (1,1,1)` at the top level (rule 2).

Nothing else changes: on every label of the sheet (the 813 rows and the 9 corrected
labels) the new rules give the matrix of `TrioRules2.lean`, except on the printed
label of row 3552 (`TrioRules3Sheet.lean`).

All checks are `#guard`s: a calibration, not a theorem.
-/

namespace Googology.Trans.BMS.TrioRules3

open Googology.Trans.BMS.TrioRules
open Googology.Trans.BMS.TrioRules2
open Googology.Trans.BMS (expandRL)

/-- `ω`. -/
def omega : Od := wpow one

/-- `Ω + 1`. -/
def omegaOnePlusOne : Od := add [(.W one, 1)] one

/-- `Ω_{Ω_2}`, the argument whose matrix `P₂` Fix E starts from. -/
def omOmTwo : Od := [(.W [(.W (nat 2), 1)], 1)]

/-- The first five columns of `M(w)` for `Ω_ω ≤ w < Ω_{ω+1}`: `B ++ (1,1,1)`. -/
def headOmegaOmega : Cols :=
  #[⟨0, 0, false⟩, ⟨1, 1, true⟩, ⟨2, 1, true⟩, ⟨3, 1, false⟩, ⟨1, 1, true⟩]

/-- `Ω_ω ≤ w < Ω_{ω+1}`. -/
def levelOmega (w : Od) : Bool :=
  cmpOrd w [(.W omega, 1)] != .lt && cmpOrd w [(.W (add omega one), 1)] == .lt

section
variable (Mf : Od → Cols)

/-- **Fix E**: rule 9 for `u = Ω+1` and an argument level `w` with
`Ω_ω ≤ w < Ω_{ω+1}`; otherwise `MpsiLevel2`. -/
def MpsiLevel3 (u X : Od) : Cols :=
  let old := MpsiLevel2 Mf u X
  if cmpOrd u omegaOnePlusOne != .eq then old else
  match lvlO X with
  | none => old
  | some w =>
    if !levelOmega w then old else
    let m := Mf w
    if m.extract 0 5 != headOmegaOmega then old else
    MpsiLevel2 Mf u omOmTwo ++
      (m.extract 4 m.size).map fun c => { c with x := c.x + 1, y := c.y + 1 }

/-- One step of the builder: `Mstep2` with Fix E. -/
def Mstep3 (alpha : Od) : Cols :=
  match lvlO alpha, isPsiLevel alpha with
  | some _, some uX => MpsiLevel3 Mf uX.1 uX.2
  | _, _ => Mstep2 Mf alpha

end

/-- The builder with fuel. -/
def Mfuel3 : Nat → Od → Cols
  | 0, _ => #[]
  | n + 1, a => Mstep3 (Mfuel3 n) a

/-- `α ↦` the columns of `ψ_0(Ω_α)`, by rules 1–10 with Fixes A–E. -/
def M3 (alpha : Od) : Cols := Mfuel3 fuel alpha

/-- **The trio matrix of `ψ_0(Ω_α)` with Fixes A–E.** -/
def trioRuleMatrix3 (alpha : Od) : List (List Nat) := toRows (M3 alpha)

/-- The matrix for a label of the sheet. -/
def trioRuleMatrixOf3 (s : String) : Option (List (List Nat)) := do
  let a ← parse s
  if a.isEmpty then none else some (trioRuleMatrix3 a)

/-- **Every column is three rows deep with `z < 2`.** -/
theorem WF3_trioRuleMatrix3 (alpha : Od) : WF3 (trioRuleMatrix3 alpha) := WF3_toRows _

/-- The matrix of a label, `[]` when it does not parse. -/
def ruleOf3 (s : String) : List (List Nat) := (trioRuleMatrixOf3 s).getD []

/-- The matrix of a label under `TrioRules2`. -/
def ruleOf2 (s : String) : List (List Nat) := (trioRuleMatrixOf2 s).getD []

/-- Lift every column by one storey: `(x, y, z) ↦ (x+1, y+1, z)`. -/
def liftRows (l : List (List Nat)) : List (List Nat) :=
  l.map fun c => [c.getD 0 0 + 1, c.getD 1 0 + 1, c.getD 2 0]

/-! ### The printed label of row 3552 -/

/-- The printed label of row 3552. -/
def printed3552 : String := "psi_W_(W+1)(W_psi_W_(w+1)(W_(w+1)))"

-- `TrioRules2` (and rules 1–10) give the non-standard matrix described above.
#guard ruleOf2 printed3552 = [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,1],[4,1,0],[3,2,0],[4,3,1],[5,3,1],[6,2,0],[7,3,1],[8,3,1],[9,1,0],[7,3,1],[8,3,0],[9,4,1],[10,4,1],[11,1,0],[12,4,0]]
#guard ruleOf2 printed3552 = (trioRuleMatrixOf printed3552).getD []
-- It lies below row 4467 `ψ(Ω_2)`, although its label is above it.
#guard ruleOf2 printed3552 < ruleOf2 "psi_W_(W+1)(W_W_2)"
#guard cmpOrd ((parse "psi_W_(W+1)(W_W_2)").getD []) ((parse printed3552).getD []) == .lt

-- Fix E: `P₂ ++ L(M(β)[4:])`.  yaBMS `bms -s` says it is standard.
#guard ruleOf3 printed3552 = [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,1],[4,1,0],[3,2,0],[4,3,1],[5,3,1],[6,2,0],[7,3,1],[8,3,1],[9,2,0],[2,2,1],[3,2,0],[4,3,1],[5,3,1],[6,2,0],[7,3,0]]
#guard ruleOf3 printed3552 =
  ruleOf3 "psi_W_(W+1)(W_W_2)" ++ liftRows ((ruleOf3 "psi_W_(w+1)(W_(w+1))").drop 4)
-- It lies between rows 4467 and 4468, and above the argument `Ω_{Ω_ω}`.
#guard ruleOf3 "psi_W_(W+1)(W_W_2)" < ruleOf3 "psi_W_(W+1)(W_W_w)"
#guard ruleOf3 "psi_W_(W+1)(W_W_w)" < ruleOf3 printed3552
#guard ruleOf3 printed3552 < ruleOf3 "W_(W+1)"

/-! ### The expansion of the new matrix is the lifted expansion of `M(β)`

`M(β)` is row 3546 of the sheet.  For `n = 0, …, 3`, BM4 expansion (`expandRL 3 n`,
proved equal to BM4 on the entries in `EntriesR.lean`) commutes with Fix E:
`(P₂ ++ L(M(β)[4:]))[n] = P₂ ++ L(M(β)[n][4:])`.  So the new matrix has the
fundamental sequence of `β`, carried one storey up. -/

#guard (List.range 4).all fun n =>
  expandRL 3 n (ruleOf3 printed3552) =
    ruleOf3 "psi_W_(W+1)(W_W_2)" ++
      liftRows ((expandRL 3 n (ruleOf3 "psi_W_(w+1)(W_(w+1))")).drop 4)

/-! ### The argument `Ω_{Ω_ω}`

Fix E gives `P₂ ++ (2,2,1)`.  Its expansion `[1]` is `P₂` followed by one lifted
storey whose last leaf is `(10,3,0)`: the argument `Ω_{Ω_3}` spelt by rule 6, one
storey per level.  The old matrix `P ++ (7,3,1)(8,3,1)(9,1,0)(7,3,1)` lies below
`P₂`, the matrix of the smaller argument `Ω_{Ω_2}`. -/

#guard ruleOf3 "psi_W_(W+1)(W_W_w)" = ruleOf3 "psi_W_(W+1)(W_W_2)" ++ [[2,2,1]]
#guard expandRL 3 1 (ruleOf3 "psi_W_(W+1)(W_W_w)") =
  ruleOf3 "psi_W_(W+1)(W_W_2)" ++
    [[2,2,0],[3,3,1],[4,3,1],[5,3,0],[3,3,1],[4,3,1],[5,1,0],[4,3,0],[5,4,1],[6,4,1],[7,3,0],[8,4,1],[9,4,1],[10,3,0]]
#guard ruleOf2 "psi_W_(W+1)(W_W_w)" < ruleOf2 "psi_W_(W+1)(W_W_2)"

/-! ### Why level `ω` cannot hang below the leaf `(9,2,0)`

In the region of `ψ_{Ω_{ω+1}}` (rows 3550–3552), arguments of level `ω` hang below
the leaf `(8,1,0)` that names the argument `Ω_Ω`.  In the region of `ψ_{Ω_{Ω+1}}` the columns below `(9,2,0)` are already taken
by arguments of level `Ω`: expansion `[2]` of row 4468 `M(Ω_{Ω+1})` is `P₂` followed
by `(10,3,1)(11,3,1)`, a nested `ψ_{Ω_{Ω+1}}`, and the rules' matrix of the argument
`Ω_{ψ_{Ω_{Ω+1}}(Ω_{Ω+1})} = Ω_{ε_{Ω_Ω+1}}`, `P₂ ++ (10,3,0)`, has the expansions
`P₂ ++ (10,2,0)(11,2,0)⋯`: towers of the leaf `(9,2,0)` reach `ε_{Ω_Ω+1}`, so that
leaf with children names `Ω_Ω`, not `Ω_ω`. -/

#guard expandRL 3 2 (ruleOf3 "W_(W+1)") = ruleOf3 "psi_W_(W+1)(W_W_2)" ++ [[10,3,1],[11,3,1]]
#guard ruleOf3 "psi_W_(W+1)(W_psi_W_(W+1)(W_(W+1)))" = ruleOf3 "psi_W_(W+1)(W_W_2)" ++ [[10,3,0]]
#guard expandRL 3 2 (ruleOf3 "psi_W_(W+1)(W_psi_W_(W+1)(W_(W+1)))") =
  ruleOf3 "psi_W_(W+1)(W_W_2)" ++ [[10,2,0],[11,2,0]]
#guard ruleOf3 printed3552 < ruleOf3 "psi_W_(W+1)(W_psi_W_(W+1)(W_(W+1)))"

/-! ### Side check: row 3551

Row 3551 is `ψ_{Ω_{ω+1}}(Ω_{Ω_ω})`.  The rules give `… (8,1,0)(6,2,1)`, the sheet
gives `… (8,1,0)(1,1,1)`.  Expansion `[1]` of the rules' matrix adds the unit
`(6,2,0)(7,3,1)(8,3,1)(9,1,0)`, a second leaf naming `Ω`, the shape of the unit the rules
give `Ω_ω+Ω` at the top level; read so, it is the argument `Ω_{Ω·2}`, and `[2]` adds a
third, so the fundamental sequence is `Ω·n` (argument `Ω_{Ω·ω}`).  Expansion `[1]` of
the sheet's matrix is one lifted storey ending in a leaf `(9,2,0)`, the shape of the
argument `Ω_{Ω_2}` in `P₂`.  This is a reading by analogy: the rules' own matrices of
`ψ_{Ω_{ω+1}}(Ω_x)` for `x = Ω+1, Ω·2, Ω·ω, Ω_2` are not standard (yaBMS), and the order
check passes with either matrix for row 3551. -/

/-- The first 12 columns of row 3551: `M(ψ_{Ω_{ω+1}}(Ω_Ω))` (row 3550). -/
def row3550 : List (List Nat) :=
  [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,0],[3,2,1],[4,2,1],[5,1,0],[6,2,1],[7,2,1],[8,1,0]]

#guard ruleOf3 "psi_W_(w+1)(W_W)" = row3550
#guard ruleOf3 "psi_W_(w+1)(W_W_w)" = row3550 ++ [[6,2,1]]
#guard expandRL 3 1 (row3550 ++ [[6,2,1]]) = row3550 ++ [[6,2,0],[7,3,1],[8,3,1],[9,1,0]]
#guard expandRL 3 2 (row3550 ++ [[6,2,1]]) =
  row3550 ++ [[6,2,0],[7,3,1],[8,3,1],[9,1,0],[7,3,0],[8,4,1],[9,4,1],[10,1,0]]
#guard expandRL 3 1 (row3550 ++ [[1,1,1]]) =
  row3550 ++ [[1,1,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,0],[4,3,1],[5,3,1],[6,2,0],[7,3,1],[8,3,1],[9,2,0]]

end Googology.Trans.BMS.TrioRules3
