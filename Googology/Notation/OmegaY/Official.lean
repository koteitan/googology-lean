/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Build.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
The file is moved from `WellOrder/OmegaY/Official/Build.lean` to `Googology/Notation/OmegaY/Official.lean`, beside `Basic.lean`, because it is the definition of the notation; the ported files import it from here. In the module docstring, "`notes/03-official-rule.md` of this repository" is made a link to that file of wy-wo-por at the same revision. The code is unchanged.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.Build

set_option backward.do.legacy false

/-!
# Executable official omega-Y expansion

This is the official omega-Y expansion (Naruyoko's StudyAndExpandSequence,
https://github.com/Naruyoko/StudyAndExpandSequence, `expand` with the default
settings of v1.1), written from the rule in
[`notes/03-official-rule.md`](https://github.com/koteitan/wy-wo-por/blob/7038635644b8d1df3f0f1a80f107210da7e33a94/notes/03-official-rule.md)
of koteitan/wy-wo-por. No code of that program is used; it was only run to compare outputs.

It is a modification of Phyrion's weak-magma rule `OmegaY.Expansion.expandDiagram`
(`OmegaY/Expansion/Build.lean`). It works on the same data: the canonical
mountain `Canonical.build`, cells with ordinal rows and stored left endpoints,
the parent lookup `Expansion.below`, the in-row parent `Expansion.weakParent`,
and the value stage `Expansion.finish`. The parts that differ from the weak rule
(notes/03 §4) are:

* the source is the original mountain `M(s)`, not the mountain of the
  decremented sequence;
* which nodes are lifted is decided per region by the in-row ancestors on the
  reference row (`ascends`), not by markers;
* the lift is the height difference inside a region (`childItems`), not the
  boundary reference;
* the gap is filled by copies of the root row (`Item.clean`), not by `fill`.

## Row convention

Phyrion's mountains keep a phantom cell of row `0` and value `0` at the bottom
of every column. A real node of official row `ρ` (notes/03 §1) is stored at row
`1 + ρ`: the bottom row `0` is stored as `1`, and rows `≥ ω` are unchanged.
`official` and `stored` convert between the two. The rule below is stated in
official rows, as in notes/03.

Every failure is an explicit error. The recursion over regions is structural in
the region level; the ancestor walks carry an explicit column allowance.
This file does not prove totality, canonical reconstruction, or
well-foundedness.
-/

namespace OmegaY.Official

open Canonical

inductive Error where
  | expansion (error : Expansion.Error)
  /-- A clean copy, an offset or a cut bottom reached a region that does not ascend. -/
  | cleanCopyNotAscending
  /-- The node of the copied root row is missing in the source column. -/
  | missingCleanSource
  /-- Counting generations left the root row. -/
  | generationLeavesRow
  /-- A clean copy without a cut bottom found no boundary node or a nonzero offset. -/
  | missingBoundaryNode
  /-- An ancestor walk used up its column allowance. -/
  | searchExhausted
  | nonLeftward
  /-- A parentless node above the bottom row. -/
  | missingParent
  | rowsNotIncreasing
  | emptyColumn
  deriving DecidableEq, Repr

abbrev Result := Except Error

def liftE {α : Type} (r : Expansion.Result α) : Result α := r.mapError Error.expansion

/-! ## Rows -/

/-- The number of stored Cantor coefficients: the degree plus one, and `0` for
the zero row. -/
def len (a : Row) : Nat := a.toList.length

/-- Rows below `ω`. -/
def isFinite (a : Row) : Bool := len a ≤ 1

/-- The official row of a stored real row: `1 + ρ ↦ ρ`. -/
def official (r : Row) : Row := if isFinite r then ((r.coeff 0 - 1 : Nat) : Row) else r

/-- The stored row of an official row: `ρ ↦ 1 + ρ`. -/
def stored (ρ : Row) : Row := if isFinite ρ then ((ρ.coeff 0 + 1 : Nat) : Row) else ρ

/-- `a` and `b` have the same coefficient at every exponent `≥ e`. -/
def agreeFrom (e : Nat) (a b : Row) : Bool :=
  (List.range (max (len a) (len b))).all fun k => decide (k < e) || a.coeff k == b.coeff k

/-! ## Regions (notes/03 §1.3)

A region of level `d ≥ 1` with base `b` is the set of rows `ρ` with
`ρ_k = b_k` for every `k ≥ d - 1`. It is passed as the pair `(d, b)`. -/

def inRegion (d : Nat) (base row : Row) : Bool := agreeFrom (d - 1) row base

/-- The height `h_S(ρ) = ρ_{d-2}` of a row in a region of level `d ≥ 2`. -/
def height (d : Nat) (row : Row) : Nat := row.coeff (d - 2)

/-- The base of slot `S[j]` (level `d - 1`) of a region `S` of level `d ≥ 2`. -/
def slot (d : Nat) (base : Row) (j : Nat) : Row :=
  Row.ofList ((List.range (max (len base) (d - 1))).map fun k =>
    if k + 2 < d then 0 else if k + 2 = d then j else base.coeff k)

/-! ## Queries on a stored mountain, in official rows -/

/-- The real nodes of a column, bottom to top (the phantom is skipped). -/
def realNodes (M : Mountain) (c : Nat) : List (Ref × Cell) :=
  match M[c]? with
  | none => []
  | some col => ((List.range col.size).zip col.toList).drop 1 |>.map fun p => (⟨c, p.1⟩, p.2)

/-- The node of column `c` at official row `ρ`. -/
def nodeAt (M : Mountain) (c : Nat) (ρ : Row) : Option (Ref × Cell) :=
  (realNodes M c).find? fun p => official p.2.row == ρ

/-- `top_S(c)`: the highest node of column `c` whose official row is in `S`. -/
def topIn (M : Mountain) (c d : Nat) (base : Row) : Option (Ref × Cell) :=
  ((realNodes M c).filter fun p => inRegion d base (official p.2.row)).getLast?

def heightOf (d : Nat) (node : Option (Ref × Cell)) : Nat :=
  match node with
  | none => 0
  | some (_, cell) => height d (official cell.row)

def leftColumn (cell : Cell) : Result Nat := do
  let left ← liftE (Expansion.leftOf cell)
  return left.column

/-- The reference row `Z` of a root node row: one less in the finite
coefficient when it is positive, otherwise the row itself. -/
def referenceRow (ρ : Row) : Row :=
  if 0 < ρ.coeff 0 then Row.ofList (ρ.toList.set 0 (ρ.coeff 0 - 1)) else ρ

/-- Follow in-row parents `P` (`Expansion.weakParent`) from `a` until the column
is at most `rootColumn`; report whether that column is exactly `rootColumn`. -/
def reachesRoot (M : Mountain) (rootColumn : Nat) : Nat → Ref → Result Bool
  | 0, _ => throw .searchExhausted
  | fuel + 1, a =>
      if a.column ≤ rootColumn then pure (a.column = rootColumn) else do
        match ← liftE (Expansion.weakParent M a) with
        | none => pure false
        | some p => reachesRoot M rootColumn fuel p

/-- The number of generations `g` of notes/03 §2.4, case 4: steps from column
`c` to the column of the left endpoint of the node `(c, C)`, until the column is
at most `rootColumn`. On the bottom row the stored left endpoint is the phantom
of the previous column, so this gives `x - c_r` there, as in notes/03. -/
def generations (M : Mountain) (rootColumn : Nat) (C : Row) :
    Nat → Ref → Cell → Nat → Result Nat
  | 0, _, _, _ => throw .searchExhausted
  | fuel + 1, ref, cell, g =>
      if ref.column ≤ rootColumn then pure g else do
        let p ← leftColumn cell
        if ¬ p < ref.column then throw .nonLeftward
        match nodeAt M p C with
        | none => throw .generationLeavesRow
        | some (r, c) => generations M rootColumn C fuel r c (g + 1)

/-! ## Items (notes/03 §2.3) -/

/-- An item `(S, T, C, o, b)`. The level is passed separately. -/
structure Item where
  source : Row
  target : Row
  clean : Option Row
  offset : Nat
  cutBottom : Bool

/-- A node to place: official row and the source column of its left endpoint
(`none` for a parentless node). -/
structure Emit where
  row : Row
  leftColumn : Option Nat

/-- The data fixed while one column `X = x + i w` is copied. -/
structure Context where
  /-- The source mountain `M(s)`. -/
  source : Mountain
  /-- The output so far (the columns left of `X`). -/
  result : Mountain
  x : Nat
  block : Nat
  rootColumn : Nat
  width : Nat
  lastColumn : Nat

def Context.boundary (ctx : Context) : Nat := ctx.rootColumn + ctx.width * ctx.block

/-- Whether the column `x` ascends in a region `S` (condition `A(S, x)`). -/
def ascends (ctx : Context) (rho : Option (Ref × Cell)) : Result Bool :=
  match rho with
  | none => pure false
  | some (_, rc) =>
      match nodeAt ctx.source ctx.x (referenceRow (official rc.row)) with
      | none => pure false
      | some (ref, _) => reachesRoot ctx.source ctx.rootColumn (ctx.x + 1) ref

/-- The children of an item of level `d ≥ 2` (notes/03 §2.4, cases 1 to 4). -/
def childItems (ctx : Context) (d : Nat) (it : Item) : Result (List Item) := do
  let M := ctx.source
  let x := ctx.x
  let i := ctx.block
  match topIn M x d it.source with
  | none => return []
  | some (_, aCell) =>
    let hTop := height d (official aCell.row)
    let hCut := heightOf d (topIn M ctx.lastColumn d it.source)
    let rho := topIn M ctx.rootColumn d it.source
    let hRoot := heightOf d rho
    let rhoRow := match rho with | none => (0 : Row) | some (_, c) => official c.row
    let sl := slot d it.source
    let tl := slot d it.target
    let e := if d = 2 then 1 else 0
    let asc ← ascends ctx rho
    if ¬ asc then
      -- case 1
      if it.clean.isSome ∨ it.offset ≠ 0 ∨ it.cutBottom then throw .cleanCopyNotAscending
      return (List.range (hTop + 1)).map fun (j : Nat) => ⟨sl j, tl j, none, 0, false⟩
    match it.clean with
    | none =>
      if ¬ it.cutBottom then
        -- case 2
        let lift : Int := ((hCut : Int) - hRoot) * i
        return (List.range (((hTop : Int) + lift + 1).toNat)).map fun (j : Nat) =>
          if j < hRoot then ⟨sl j, tl j, none, 0, false⟩
          else if (j : Int) < hRoot + lift + e then ⟨sl hRoot, tl j, some rhoRow, 0, decide (hRoot < j)⟩
          else ⟨sl ((j : Int) - lift).toNat, tl j, none, 0, decide (i ≠ 0 ∧ (j : Int) = hRoot + lift)⟩
      else
        -- case 3
        let hB := heightOf d (topIn ctx.result ctx.boundary d it.target)
        let tgt := if i = 0 then hTop else hB + hTop
        return ((List.range (tgt + 1)).filter (hRoot ≤ ·)).map fun (j : Nat) =>
          if j < hB + hRoot + e then ⟨sl hRoot, tl (j - hRoot), some rhoRow, 0, true⟩
          else ⟨sl (j - hB), tl (j - hRoot), none, 0, decide (j = hB + hRoot)⟩
    | some C =>
      -- case 4
      let (csRef, cs) ← match nodeAt M x C with
        | none => throw .missingCleanSource
        | some p => pure p
      let g ← generations M ctx.rootColumn C (x + 1) csRef cs 0
      let b := topIn ctx.result ctx.boundary d it.target
      let hB := heightOf d b
      let tgt : Int := if i = 0 then hTop else (hB : Int) + g - it.offset
      if ¬ it.cutBottom ∧ (b.isNone ∨ it.offset ≠ 0) then throw .missingBoundaryNode
      return (List.range (tgt + 1).toNat).map fun (j : Nat) =>
        let oj := ((j : Int) - hB + it.offset).toNat
        if it.cutBottom then ⟨sl hRoot, tl j, some C, oj, true⟩
        else if j < hRoot then ⟨sl j, tl j, none, 0, false⟩
        else ⟨sl hRoot, tl j, some C, oj, decide (hRoot < j)⟩

/-- A level-1 item emits at most one node (notes/03 §2.3). -/
def levelOne (ctx : Context) (it : Item) : Result (List Emit) := do
  match nodeAt ctx.source ctx.x it.source with
  | none => return []
  | some (_, src) =>
    match it.clean with
    | some C =>
      match nodeAt ctx.source ctx.x C with
      | none => throw .missingCleanSource
      | some (_, cs) => return [⟨it.target, some (← leftColumn cs)⟩]
    | none =>
      if it.source = 0 then return [⟨it.target, none⟩]
      else return [⟨it.target, some (← leftColumn src)⟩]

/-- Process an item of level `d`, depth first. -/
def runItem (ctx : Context) : Nat → Item → Result (List Emit)
  | 0, _ => pure []
  | 1, it => levelOne ctx it
  | d + 2, it => do
      let children ← childItems ctx (d + 2) it
      let outs ← children.mapM (runItem ctx (d + 1))
      return outs.flatten

/-- The first items: the regions `L_{k,j}` below the top row `τ`, in row
order (notes/03 §2.3). Each is paired with its level `k + 1`. -/
def lowerItems (τ : Row) : List (Nat × Item) :=
  (List.range (len τ)).reverse.flatMap fun k =>
    (List.range (τ.coeff k)).map fun (j : Nat) =>
      let b := slot (k + 2) τ j
      (k + 1, ⟨b, b, none, 0, false⟩)

/-- Turn the emitted nodes into cells and finish the values with Phyrion's
`Expansion.finish` (top value 1, then `v(u) = v(u⁺) + v(π(u⁺))`). -/
def assemble (ctx : Context) (emits : List Emit) : Result Column := do
  if emits.isEmpty then throw .emptyColumn
  for pair in emits.zip emits.tail do
    if ¬ pair.1.row < pair.2.row then throw .rowsNotIncreasing
  let X := ctx.result.size
  let cells ← emits.mapM fun em => do
    let row := stored em.row
    match em.leftColumn with
    | some p =>
      let q := if ctx.rootColumn ≤ p then p + ctx.width * ctx.block else p
      let ref ← liftE (Expansion.below ctx.result q row)
      pure (⟨row, 0, some ref⟩ : Cell)
    | none =>
      if em.row = 0 then pure (⟨row, 0, some ⟨X - 1, 0⟩⟩ : Cell)
      else throw .missingParent
  liftE (Expansion.finish ctx.result (phantom :: cells))

/-- Copy the column `x` of `M(s)` into block `i` (notes/03 §2.2 to §2.5). -/
def copyColumn (ctx : Context) (τ : Row) : Result Column := do
  let mut emits : List Emit := []
  for (d, it) in lowerItems τ do
    emits := emits ++ (← runItem ctx d it)
  -- the upper part: rows `≥ τ` are copied without lifting
  let xa := if ctx.x = ctx.lastColumn then ctx.rootColumn else ctx.x
  for (_, cell) in realNodes ctx.source xa do
    if τ ≤ official cell.row then
      emits := emits ++ [⟨official cell.row, some (← leftColumn cell)⟩]
  assemble ctx emits

/-- The source columns of block `i` (notes/03 §2.1). -/
def blockColumns (rootColumn lastColumn copies i : Nat) : List Nat :=
  if i = 0 then [lastColumn]
  else List.range' (rootColumn + 1)
    (if i < copies then lastColumn - rootColumn else lastColumn - rootColumn - 1)

/-- The complete output mountain of `s[n]`, in Phyrion's storage format. -/
def expandDiagram (values : List Nat) (copies : Nat) : Result Mountain := do
  let M ← liftE ((Canonical.build values).mapError Expansion.Error.canonical)
  if values.isEmpty then return M
  let x0 := M.size - 1
  let lastCol ← liftE (Expansion.columnAt M x0)
  let t ← liftE (Expansion.top lastCol)
  let τ := official t.row
  if τ = 0 ∨ copies = 0 then return M.pop
  let root ← liftE (Expansion.leftOf t)
  let cr := root.column
  if ¬ cr < x0 then throw (.expansion .invalidRoot)
  let w := x0 - cr
  let mut R := M.extract 0 x0
  for i in List.range (copies + 1) do
    for x in blockColumns cr x0 copies i do
      if R.size ≠ x + w * i then throw (.expansion .misplacedFill)
      let ctx : Context := ⟨M, R, x, i, cr, w, x0⟩
      let col ← copyColumn ctx τ
      R := R.push col
  return R

def expand (values : List Nat) (copies : Nat) : Result (List Nat) := do
  liftE (Expansion.valuesOf (← expandDiagram values copies))

end OmegaY.Official
