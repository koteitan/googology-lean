/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Reserve.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
The import of `OmegaY.Official.Build` is `Googology.Notation.OmegaY.Official`, where that file is moved.
-/
import Googology.Notation.OmegaY.Official

set_option backward.do.legacy false

/-!
# The leg atoms of a mountain and the splice classification

This file defines, as executable functions, the atom system of
`notes/04-official-design.md` §3 and the classification of §1.2 that Phyrion's
iterated splice theorem (`OmegaY.Splice.iterated_reservoirs`) needs.

* An atom is a pair of columns `parent < child` with a key template. A key template
  lists, for the scales `D, D-1, …, 0`, a column or `none` (the top key entry `⊤`).
* The leg atom of a real node `u` of column `c ≥ 1` goes from the column of the
  stored left endpoint of `u` (the left leg: the parent of the edge into `u`, or the
  phantom of column `c - 1` for a bottom node) to `c`. Its key is the key of a
  hypothetical edge from the row of `u` whose parent is the highest real node of the
  leg column at a row not above the row of `u`.
* `classifiedB s n D` checks, for one expansion `s[n]` of the official rule, that
  every leg atom of the output is classified by the leg atoms of the input as a base,
  reserve or seam atom, with the leg atom of the top node of the last column as
  control. It also checks the shapes the splice theorem needs: the output mountain
  can be built, it has `x₀ + n·w` columns, and every row of both mountains has
  degree at most `D`. That every leg atom is well formed (`wellFormed`), that the
  root is left of the last column and that the control is a leg atom are proved for
  all valid mountains in `ReserveShape.lean`.

Rows here are Phyrion's stored rows (`1 + ρ` for a finite official row `ρ`); the
jump between two stored rows is the jump between the official rows.

Nothing in this file is a theorem about all inputs. `ReserveCheck.lean` evaluates
`classifiedB` on the fixtures of `Check.lean`.
-/

namespace OmegaY.Official.Reserve

open Canonical

/-- A key template: the entries for the scales `D, D-1, …, 0`; `none` is `⊤`. -/
abbrev RawKey := List (Option Nat)

/-- An atom `(parent, child, key)`. -/
structure RawAtom where
  parent : Nat
  child : Nat
  key : RawKey
  deriving DecidableEq, Repr, Inhabited

/-! ## Mountain geometry -/

def cell? (M : Mountain) (r : Ref) : Option Cell := do
  let col ← M[r.column]?
  col[r.index]?

/-- The raw parent of a node: the left endpoint stored on the cell above it. -/
def rawParent (M : Mountain) (r : Ref) : Option Ref := do
  let col ← M[r.column]?
  let up ← col[r.index + 1]?
  up.left

/-- The root of a node at scale `k`: follow raw parents along edges whose jump is at
most `k`. The fuel bounds the number of steps; raw parents lie strictly left. -/
def scaleRoot (M : Mountain) (k : Nat) : Nat → Ref → Ref
  | 0, r => r
  | fuel + 1, r =>
      match rawParent M r, cell? M r with
      | some p, some c =>
          match cell? M p with
          | some cp =>
              if Row.jump c.row cp.row ≤ k ∧ p.column < r.column then scaleRoot M k fuel p
              else r
          | none => r
      | _, _ => r

/-- The key template of an edge from a node at row `row` whose parent is `p`
(Phyrion's `keyTemplate`): scales `D, …, 0`. -/
def keyAt (M : Mountain) (D : Nat) (row : Row) (p : Ref) : RawKey :=
  match cell? M p with
  | none => []
  | some cp =>
      let d := Row.jump row cp.row
      (List.range (D + 1)).reverse.map fun k =>
        if d ≤ k then some (scaleRoot M k (p.column + 1) p).column else none

/-- The highest real node of column `l` whose row is at most `row`. -/
def highestAtMost (M : Mountain) (l : Nat) (row : Row) : Option Ref := do
  let col ← M[l]?
  let j ← ((List.range col.size).filter fun j =>
    0 < j && (match col[j]? with | some c => decide (c.row ≤ row) | none => false)).getLast?
  return ⟨l, j⟩

/-- The leg atom of a real node `u`. -/
def legAtom? (M : Mountain) (D : Nat) (u : Ref) : Option RawAtom := do
  let cu ← cell? M u
  let l ← cu.left
  let p ← highestAtMost M l.column cu.row
  return ⟨l.column, u.column, keyAt M D cu.row p⟩

/-- The leg atoms of all real nodes of the columns `c ≥ 1`. -/
def atoms (M : Mountain) (D : Nat) : List RawAtom :=
  (List.range M.size).flatMap fun c =>
    if c = 0 then []
    else match M[c]? with
      | none => []
      | some col => (List.range col.size).filterMap fun i =>
          if i = 0 then none else legAtom? M D ⟨c, i⟩

/-- The atom system of a sequence (empty when the mountain cannot be built). -/
def atomsOf (s : List Nat) (D : Nat) : List RawAtom :=
  match Canonical.build s with
  | .ok M => atoms M D
  | .error _ => []

/-! ## Keys -/

/-- Strict order of key entries: columns by index, `none` (`⊤`) largest. -/
def entryLt : Option Nat → Option Nat → Bool
  | some a, some b => decide (a < b)
  | some _, none => true
  | none, _ => false

/-- The lexicographic order of key templates of length `m`, written as in
`Pi.Lex`: some index `i` has equal entries before it and a smaller entry at `i`. -/
def keyLt (m : Nat) (a b : RawKey) : Bool :=
  (List.range m).any fun i =>
    (List.range i).all (fun j => a[j]? == b[j]?) && entryLt (a[i]?.getD none) (b[i]?.getD none)

def keyEq (m : Nat) (a b : RawKey) : Bool :=
  (List.range m).all fun j => a[j]? == b[j]?

def keyLe (m : Nat) (a b : RawKey) : Bool := keyEq m a b || keyLt m a b

/-- Apply the column map `μ_b` (`c ↦ c` below the root column, `c ↦ c + sh` from it)
to every entry of a key template. -/
def mapKey (cr sh : Nat) (K : RawKey) : RawKey :=
  K.map (Option.map fun v => if v < cr then v else v + sh)

def mapColumn (cr sh : Nat) (v : Nat) : Nat := if v < cr then v else v + sh

/-! ## Shapes -/

/-- An atom is well formed in a mountain of width `n`: `parent < child < n`, the key
has `D + 1` entries, and every column entry is at most the parent. -/
def wellFormed (D n : Nat) (a : RawAtom) : Bool :=
  decide (a.parent < a.child) && decide (a.child < n) && decide (a.key.length = D + 1) &&
    a.key.all fun e => match e with | some v => decide (v ≤ a.parent) | none => true

/-- Every stored row of the mountain has degree at most `D`. -/
def degreeAtMost (M : Mountain) (D : Nat) : Bool :=
  M.toList.all fun col => col.toList.all fun c => decide (len c.row ≤ D + 1)

/-! ## The classification -/

/-- (base) an input atom with the same endpoints and a key at least as large. -/
def baseOK (D : Nat) (Es : List RawAtom) (e : RawAtom) : Bool :=
  Es.any fun a => a.parent == e.parent && a.child == e.child && keyLe (D + 1) e.key a.key

/-- (reserve) at block `b` with boundary `B`. -/
def reserveOK (D cr w x0 b : Nat) (Es : List RawAtom) (e : RawAtom) : Bool :=
  let B := x0 + b * w
  let src := cr + (e.child - B)
  let pp? : Option Nat :=
    if e.parent < cr then some e.parent
    else if B ≤ e.parent then some (cr + (e.parent - B)) else none
  match pp? with
  | none => false
  | some pp => Es.any fun a => a.child < x0 && a.parent == pp && a.child == src &&
      keyLe (D + 1) e.key (mapKey cr ((b + 1) * w) a.key)

/-- (seam) at block `b`: the child is the boundary `B`, the key is below the mapped
control, and an input atom into `x₀` with the mapped parent covers it. -/
def seamOK (D cr w x0 b : Nat) (Es : List RawAtom) (Kc : RawKey) (e : RawAtom) : Bool :=
  e.child == x0 + b * w && keyLt (D + 1) e.key (mapKey cr (b * w) Kc) &&
    Es.any fun a => a.child == x0 && mapColumn cr (b * w) a.parent == e.parent &&
      keyLe (D + 1) e.key (mapKey cr (b * w) a.key)

/-- The data of a nontrivial expansion: the input mountain, the last column `x₀`,
the root column `cr` and the control key. -/
structure Root where
  x0 : Nat
  cr : Nat
  control : RawKey
  deriving Repr

/-- The root data of an input mountain whose last column has a top above the bottom:
the last column `x₀`, the root column (the column of the left endpoint of the top
node) and the key of the leg atom of the top node (the control). -/
def root? (M : Mountain) (D : Nat) : Option Root :=
  match M[M.size - 1]? with
  | none => none
  | some col =>
    if col.size - 1 ≤ 1 then none
    else match col[col.size - 1]? with
      | none => none
      | some t =>
        match t.left with
        | none => none
        | some r =>
          match legAtom? M D ⟨M.size - 1, col.size - 1⟩ with
          | none => none
          | some a => if r.column = a.parent then some ⟨M.size - 1, r.column, a.key⟩ else none

/-- The classification of one expansion `s[n]` at dimension `D`, for an atom system
`E` and a choice of control `ctl`. It is `true` when the expansion fails (there is
nothing to show). -/
def classifiedWith (E : Mountain → Nat → List RawAtom) (ctl : Mountain → Nat → Option Root)
    (s : List Nat) (n D : Nat) : Bool :=
  match Canonical.build s, Official.expand s n with
  | .ok M, .ok out =>
    match Canonical.build out with
    | .error _ => false
    | .ok MO =>
      let Es := E M D
      let EO := E MO D
      degreeAtMost M D && degreeAtMost MO D &&
      match ctl M D with
      | none =>
          -- the last entry is 1 (or the input is empty): deletion only
          decide (out.length + 1 = s.length) && EO.all (baseOK D Es)
      | some ρ =>
        if n = 0 then decide (out.length + 1 = s.length) && EO.all (baseOK D Es)
        else
          let w := ρ.x0 - ρ.cr
          decide (out.length = ρ.x0 + n * w) &&
          EO.all fun e =>
            if e.child < ρ.x0 then baseOK D Es e
            else
              let b := (e.child - ρ.x0) / w
              reserveOK D ρ.cr w ρ.x0 b Es e || seamOK D ρ.cr w ρ.x0 b Es ρ.control e
  | _, _ => true

/-- The classification for the leg atoms, with the leg atom of the top node of the
last column as control (`notes/04-official-design.md` §3). -/
def classifiedB (s : List Nat) (n D : Nat) : Bool := classifiedWith atoms root? s n D

/-! ## Phyrion's representation, for comparison -/

/-- The real edges with Phyrion's key templates. -/
def edgeAtoms (M : Mountain) (D : Nat) : List RawAtom :=
  (List.range M.size).flatMap fun c =>
    match M[c]? with
    | none => []
    | some col => (List.range col.size).filterMap fun i => do
        if i = 0 then none
        let cu ← cell? M ⟨c, i⟩
        let p ← rawParent M ⟨c, i⟩
        return ⟨p.column, c, keyAt M D cu.row p⟩

/-- The real top edge of the last column as control. -/
def edgeRoot? (M : Mountain) (D : Nat) : Option Root := do
  let x0 := M.size - 1
  let col ← M[x0]?
  let i := col.size - 1
  if i ≤ 1 then none
  let t ← col[i]?
  let lower ← col[i - 1]?
  let r ← t.left
  some ⟨x0, r.column, keyAt M D lower.row r⟩

/-- The classification for Phyrion's representation (real edges only). -/
def classifiedEdgesB (s : List Nat) (n D : Nat) : Bool := classifiedWith edgeAtoms edgeRoot? s n D

/-- The largest degree plus one of a stored row of the mountain of `s`
(`0` if it cannot be built); `dimOf s` is the least `D` with every degree `≤ D`. -/
def dimOf (s : List Nat) : Nat :=
  match Canonical.build s with
  | .ok M => (M.toList.flatMap fun col => col.toList.map fun c => len c.row - 1).foldl max 0
  | .error _ => 0

end OmegaY.Official.Reserve
