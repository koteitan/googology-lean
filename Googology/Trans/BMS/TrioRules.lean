import Googology.Trans.BMS.Trio

/-!
# The trio matrix of `ψ_0(Ω_α)` for `ε₀ ≤ α < Λ`: rules 1–10

`Trio.lean` transcribes the map `ψ_0(Ω_α) ↦ M(α)` of
[koteitan/trio](https://github.com/koteitan/trio) for `α < ε₀`, plus two closed
clauses above it.  This file transcribes the rest of the
[algorithm for `ε₀ ≤ α < Λ`](https://github.com/koteitan/trio/blob/main/ebp2bms/algorithm/2/README-en.md):
the OT embedding `B`, the base `M(Ω_v)` built by insertion, and rules 1–10 for
the arithmetic on `Ω_v` (`Λ` is the least `Ω` fixed point).

The rules on the algorithm page are stated in prose; the page names its reference
implementation,
[`tools/probe_eps_range.py`](https://github.com/koteitan/trio/blob/main/tools/probe_eps_range.py),
and this file is a function-by-function transcription of that program.  The
Python name of each piece is given in its docstring, and the rule it carries:

| rule | where |
|---|---|
| 1 (row 1 repeats row 0; `strip`) | `strip`, `blockF` |
| 2 (`α ≥ Ω_v` stacks on `M(Ω_v)`) | `Mstep`, `placeUnits` |
| 3 (a level is an address) | `writeLevel` (`arg = true`), `isLevel`, `relative` |
| 4 (a unit's leaf is one column) | `writeLevel` (`arg = false`), `leafY` |
| 5 (the upgrade mark) | `suffixOf`, `appendSuffix`, `tailLevel` |
| 6 (storeys) | `storeyOf`, `laySt`, `spent` |
| 7 (the next anchor's `x`) | `lastRoot` |
| 8 (an uncountable subscript copies the base) | `copyStorey` |
| 9 (`ψ_{Ω_u}(X)` raises no unit) | `isPsiLevel`, `MpsiLevel` |
| 10 (ladder coverage) | `writeLevel` (the ladders) |

**Ordinals.**  The input `α` is what the program works on: a Cantor normal form
to base `ω` whose exponents are again normal forms or one of two atoms, `Ω_v`
and `ψ_v(X)`, both fixed points of `x ↦ ω^x` (`Ex`, `Od`).  The sheet's labels
are strings in the program's notation (`W_2+W*w`, `psi_W_(w+1)(W_W_w)`), and
`parse` reads them exactly as the program does, so the table rows are checked
under their own labels.  `ofTerm` reads a term of the extended Buchholz
notation into this form, which is how the map extends `Trio.lean`'s.

**Recursion.**  The program recurses on the nesting of its ordinals, and the
builder `M` calls itself on subscripts.  Every such recursion here carries a
fuel argument (`fuel = 200`), which bounds only the depth of the nesting; on
every input checked here the recursion stops long before the fuel runs out, as
the `#guard`s (which compare with values the program prints) show.

**Columns.**  A column is `Col = (x, y, z)` with `x y : Int` (the program lays
out an anchor at `x = r + 1` from `r = -1`) and `z : Bool`.  Row 2 is a `Bool`
because the program only ever writes `0` and `1` there; that makes the output
well formed by construction, which is `WF3_trioRuleMatrix` below.

**Where the program errs.**  Where the program would raise (a countable
argument of `ψ_{Ω_u}`, an index past the end of a list, the maximum of an
empty list), the transcription returns a default instead (the empty matrix,
the column `(0,0,0)`, index `0`).  None of the checked rows reaches them.

The calibration against the sheet — every row of the table the program is
measured on — is in `TrioRulesSheet.lean`.
-/

namespace Googology.Trans.BMS.TrioRules

open Googology.Notation.ExBuchholz
open Googology.Notation.ExBuchholz.Term

/-! ### Ordinals: normal forms over two families of atoms -/

/-- An exponent of the normal form: a normal form `o a`, or an atom — `W v` is
`Ω_v`, `psi v X` is `ψ_v(X)`.  (Python: an `Ord` tuple or an atom tuple.) -/
inductive Ex where
  | o : List (Ex × Nat) → Ex
  | W : List (Ex × Nat) → Ex
  | psi : List (Ex × Nat) → List (Ex × Nat) → Ex
  deriving BEq, Repr, Inhabited

/-- A normal form `ω^{e_1}·c_1 + ω^{e_2}·c_2 + ⋯`, exponents decreasing. -/
abbrev Od := List (Ex × Nat)

/-- The recursion depth every fuelled function below is given. -/
def fuel : Nat := 200

/-- Python `is_atom`. -/
def Ex.isAtom : Ex → Bool
  | .o _ => false
  | _ => true

/-- Whether an exponent is a `ψ` atom. -/
def Ex.isPsi : Ex → Bool
  | .psi _ _ => true
  | _ => false

/-- Python `ato`: the normal form an exponent denotes (`ω^atom = atom`). -/
def ato : Ex → Od
  | .o a => a
  | x => [(x, 1)]

/-- Python `nat`. -/
def nat (n : Nat) : Od := if n = 0 then [] else [(.o [], n)]

/-- `1`. -/
def one : Od := nat 1

/-- Python `wpow`: `ω^x`. -/
def wpow (x : Od) : Od := [(.o x, 1)]

/-- Python `lvl`: the `Ω` level `v` with `Ω_v ≤ x < Ω_{v+1}`, `none` when `x` is
countable.  A `ψ_{Ω_u}` names the cardinal, so its level is `u`. -/
def lvlF : Nat → Ex → Option Od
  | 0, _ => none
  | _ + 1, .W v => some v
  | _ + 1, .psi v _ =>
      match v with
      | [] => none
      | [(.W u, 1)] => some u
      | _ => some v
  | _ + 1, .o [] => none
  | n + 1, .o ((e, _) :: _) => lvlF n e

/-- Python `lvl` on an exponent. -/
def lvl (x : Ex) : Option Od := lvlF fuel x

/-- Python `lvl` on a normal form. -/
def lvlO (a : Od) : Option Od := lvl (.o a)

/-- Python `is_card_psi`: `ψ_{Ω_u}(X)`, with the cardinal itself as subscript. -/
def isCardPsi : Ex → Bool
  | .psi [(.W _, 1)] _ => true
  | _ => false

/-- The kind of an atom at a fixed level: `ψ_{Ω_u}` just below `Ω_u`, `Ω_u`,
then `ψ_u` just above. -/
def kindA (x : Ex) : Int :=
  match x with
  | .W _ => 0
  | _ => if isCardPsi x then -1 else 1

/-- The argument of a `ψ` atom. -/
def argA : Ex → Od
  | .psi _ X => X
  | _ => []

/-- Python `cmp_atom`, with the comparison of normal forms passed in. -/
def cmpAtomWith (c : Od → Od → Ordering) (x y : Ex) : Ordering :=
  (c ((lvl x).getD []) ((lvl y).getD [])).then <|
    (compare (kindA x) (kindA y)).then <|
      match x with
      | .W _ => .eq
      | _ => c (argA x) (argA y)

/-- Python `cmp_exp`. -/
def cmpExpWith (c : Od → Od → Ordering) (x y : Ex) : Ordering :=
  if x.isAtom && y.isAtom then cmpAtomWith c x y else c (ato x) (ato y)

/-- Python `cmp_ord`: lexicographic on the summands, then the length. -/
def cmpOrdWith (c : Od → Od → Ordering) (a b : Od) : Ordering :=
  ((a.zip b).map fun pq => (cmpExpWith c pq.1.1 pq.2.1).then (compare pq.1.2 pq.2.2)).foldr
    Ordering.then (compare a.length b.length)

/-- The comparison with fuel. -/
def cmpF : Nat → Od → Od → Ordering
  | 0 => fun _ _ => .eq
  | n + 1 => cmpOrdWith (cmpF n)

/-- Python `cmp_ord`. -/
def cmpOrd (a b : Od) : Ordering := cmpF fuel a b

/-- Python `cmp_exp`. -/
def cmpExp (x y : Ex) : Ordering := cmpExpWith (cmpF fuel) x y

/-- Python `add`: ordinal addition of normal forms. -/
def add (a b : Od) : Od :=
  match b with
  | [] => a
  | (lead, cb) :: bt =>
    let keep := a.filter fun t => cmpExp t.1 lead == .gt
    let same := a.filter fun t => cmpExp t.1 lead == .eq
    match same with
    | s :: _ => keep ++ ((lead, s.2 + cb) :: bt)
    | [] => keep ++ b

/-- Python `add_exp`. -/
def addExp (x y : Ex) : Od := add (ato x) (ato y)

/-- Python `mul`: ordinal multiplication of normal forms. -/
def mul (a b : Od) : Od :=
  match a with
  | [] => []
  | (e1, c1) :: ta =>
    if b.isEmpty then []
    else b.foldl (fun out ec =>
      if ec.1 == .o [] then add out ((e1, c1 * ec.2) :: ta)
      else add out [(.o (addExp e1 ec.1), ec.2)]) []

/-- Python `power`: ordinal exponentiation, as far as the notation needs it. -/
def power (a b : Od) : Od :=
  if b.isEmpty then one
  else if a == one then one
  else if b == one then a
  else match b with
    | [(.o [], k)] => (List.range (k - 1)).foldl (fun r _ => mul r a) a
    | _ =>
      match a with
      | [] => []
      | (e1, _) :: _ => if e1 == .o [] then wpow b else wpow (mul (ato e1) b)

/-! ### Reading the sheet's labels (Python `parse`) -/

/-- A token: `psi`, `w`, `W`, a numeral or one of `+ * ^ ( ) _`. -/
inductive Tok where
  | psi | w | W
  | num (n : Nat)
  | sym (c : Char)
  deriving DecidableEq, Repr

/-- Python `canon`: `p(` and `p_` are sugar for `psi(` and `psi_`. -/
def canonGo : Option Char → List Char → List Char
  | _, [] => []
  | prev, c :: rest =>
    let follow := match rest with
      | d :: _ => d == '_' || d == '('
      | [] => false
    if c == 'p' && !((prev.map Char.isAlpha).getD false) && follow then
      'p' :: 's' :: 'i' :: canonGo (some c) rest
    else c :: canonGo (some c) rest

/-- Close a numeral being read. -/
def flushNum : Option Nat → List Tok → List Tok
  | none, ts => ts
  | some n, ts => .num n :: ts

/-- The tokenizer; `none` when a character is not part of a token. -/
def tokGo : Option Nat → List Char → Option (List Tok)
  | acc, [] => some (flushNum acc [])
  | acc, 'p' :: 's' :: 'i' :: r => (tokGo none r).map (flushNum acc [.psi] ++ ·)
  | acc, c :: r =>
    if c.isDigit then tokGo (some (acc.getD 0 * 10 + (c.toNat - '0'.toNat))) r
    else if c == 'w' then (tokGo none r).map (flushNum acc [.w] ++ ·)
    else if c == 'W' then (tokGo none r).map (flushNum acc [.W] ++ ·)
    else if "+*^()_".toList.contains c then (tokGo none r).map (flushNum acc [.sym c] ++ ·)
    else none

mutual
/-- Python `atom` (and `sub`, which is `_` followed by an atom). -/
def pAtom : Nat → List Tok → Option (Od × List Tok)
  | 0, _ => none
  | n + 1, .sym '(' :: r => do
      let (e, r) ← pExpr n r
      match r with
      | .sym ')' :: r => some (e, r)
      | _ => none
  | _ + 1, .w :: r => some (wpow one, r)
  | n + 1, .W :: r =>
      match r with
      | .sym '_' :: r' => do
          let (v, r'') ← pAtom n r'
          some (ato (.W v), r'')
      | _ => some (ato (.W one), r)
  | n + 1, .psi :: r => do
      let (v, r) ← match r with
        | .sym '_' :: r' => pAtom n r'
        | _ => some ([], r)
      match r with
      | .sym '(' :: r => do
          let (x, r) ← pExpr n r
          match r with
          | .sym ')' :: r => some ([(.psi v x, 1)], r)
          | _ => none
      | _ => none
  | _ + 1, .num k :: r => some (nat k, r)
  | _, _ => none

/-- Python `pw`: `^` is right associative. -/
def pPw : Nat → List Tok → Option (Od × List Tok)
  | 0, _ => none
  | n + 1, ts => do
      let (b, r) ← pAtom n ts
      match r with
      | .sym '^' :: r => do
          let (e, r) ← pPw n r
          some (power b e, r)
      | _ => some (b, r)

/-- The loop of Python `term`: `*` or a numeral right after is a product. -/
def pTermLoop : Nat → Od → List Tok → Option (Od × List Tok)
  | 0, _, _ => none
  | n + 1, f, .sym '*' :: r => do
      let (g, r) ← pPw n r
      pTermLoop n (mul f g) r
  | n + 1, f, r@(.num _ :: _) => do
      let (g, r) ← pPw n r
      pTermLoop n (mul f g) r
  | _ + 1, f, r => some (f, r)

/-- Python `term`. -/
def pTerm : Nat → List Tok → Option (Od × List Tok)
  | 0, _ => none
  | n + 1, ts => do
      let (f, r) ← pPw n ts
      pTermLoop n f r

/-- The loop of Python `expr`. -/
def pExprLoop : Nat → Od → List Tok → Option (Od × List Tok)
  | 0, _, _ => none
  | n + 1, e, .sym '+' :: r => do
      let (t, r) ← pTerm n r
      pExprLoop n (add e t) r
  | _ + 1, e, r => some (e, r)

/-- Python `expr`. -/
def pExpr : Nat → List Tok → Option (Od × List Tok)
  | 0, _ => none
  | n + 1, ts => do
      let (t, r) ← pTerm n ts
      pExprLoop n t r
end

/-- Python `parse`: the ordinal a label names, `none` when it does not parse. -/
def parse (s : String) : Option Od := do
  let cs := canonGo none (s.toList.filter (· != ' '))
  let ts ← tokGo none cs
  let (e, r) ← pExpr (4 * ts.length + 16) ts
  if r.isEmpty then some e else none

/-! ### Pieces of the normal form the builder reads -/

/-- Python `units`: the exponents of the summands, each repeated by its
coefficient. -/
def units (a : Od) : List Ex := a.flatMap fun ec => List.replicate ec.2 ec.1

/-- Python `pred_beta`: the `β'` with `1 + β' = β`. -/
def predBeta (beta : Od) : Od :=
  match beta with
  | [] => []
  | (e, k) :: _ => if e == .o [] then nat (k - 1) else beta

/-- **Rule 1**, Python `strip`: what the children of the column of a summand
`ω^δ` spell out.  `ψ_v(X)·c + ρ ↦ X + ψ_v(X)·(c-1) + ρ` (the uncollapse),
`Ω_v·c + ρ ↦ Ω_v·(c-1) + ρ`, anything else is itself. -/
def strip (delta : Ex) : Od :=
  match ato delta with
  | [] => []
  | (h, c) :: dt =>
    let rest := (if c > 1 then [(h, c - 1)] else []) ++ dt
    match h with
    | .psi _ X => add X rest
    | .W _ => rest
    | _ => (h, c) :: dt

/-- Whether the leading exponent is a `ψ` atom. -/
def headIsPsi (a : Od) : Bool :=
  match a with
  | (h, _) :: _ => h.isPsi
  | [] => false

/-! ### Columns -/

/-- A column `(x, y, z)`; row 2 is `0` (`false`) or `1` (`true`). -/
structure Col where
  x : Int
  y : Int
  z : Bool
  deriving DecidableEq, Repr, Inhabited

/-- A matrix under construction. -/
abbrev Cols := Array Col

/-- The column at `i` (`(0,0,0)` past the end). -/
def colAt (cs : Cols) (i : Nat) : Col := cs.getD i default

/-- The last column. -/
def lastC (cs : Cols) : Col := colAt cs (cs.size - 1)

/-- Replace the row-1 value of the last column. -/
def setLastY (cs : Cols) (y : Int) : Cols := cs.modify (cs.size - 1) fun c => { c with y := y }

/-- Python `lift`: `L(x, y, z) = (x+1, y+1, z)`. -/
def liftCols (cs : Cols) : Cols := cs.map fun c => { c with x := c.x + 1, y := c.y + 1 }

/-- **Rule 6**, Python `storey`: the lifted copy, its final leaf naming `y`. -/
def storeyOf (cs : Cols) (y : Int) : Cols := setLastY (liftCols cs) y

/-- Python `_forest`: each column's row-0 parent, the nearest earlier column
with a smaller `x`. -/
def forest (cs : Cols) : Array (Option Nat) :=
  (Array.range cs.size).map fun i =>
    (List.range i).reverse.find? fun j => decide ((colAt cs j).x < (colAt cs i).x)

/-- **Rule 3**, Python `_is_level`: an anchor or a `+1` marker — a `z = 0`
column with `y ≥ 1` whose parent is absent, a `z0` column other than a `ψ_0`
node, or a root. -/
def isLevel (cs : Cols) (par : Array (Option Nat)) (i : Nat) : Bool :=
  let c := colAt cs i
  if c.z || decide (c.y < 1) then false
  else match par.getD i none with
    | none => true
    | some p =>
      let cp := colAt cs p
      if !cp.z then !(p != 0 && cp.y == 0)
      else match par.getD p none with
        | none => true
        | some gp => !(colAt cs gp).z

/-- Python `_relative`: a row-1 value that tracks the unit's level. -/
def relative (cs : Cols) (par : Array (Option Nat)) (i : Nat) : Bool :=
  (colAt cs i).z || isLevel cs par i

/-- The length of the common prefix. -/
def commonPrefix (a b : Cols) : Nat :=
  ((a.toList.zip b.toList).takeWhile fun p => p.1 == p.2).length

/-- The index of the last root: a `z1` column whose parent is absent or `z0`. -/
def lastRootIdx (cs : Cols) : Option Nat :=
  let par := forest cs
  (List.range cs.size).reverse.find? fun j =>
    (colAt cs j).z &&
      match par.getD j none with
      | none => true
      | some p => !(colAt cs p).z

/-- Python `last_root_plain`: `(level, x)` of the last root. -/
def lastRootPlain (cs : Cols) : Int × Int :=
  match lastRootIdx cs with
  | some i => ((colAt cs i).y, (colAt cs i).x)
  | none => (0, 0)

/-- **Rule 7**, Python `last_root`: `(level, anchor x)` for the unit continuing
`cs` — the root's own `x` when a leaf closes `cs`, the next one otherwise. -/
def lastRoot (cs : Cols) : Int × Int :=
  match lastRootIdx cs with
  | some i => ((colAt cs i).y, (colAt cs i).x + (if (lastC cs).z then 1 else 0))
  | none => (0, 0)

/-- Python `Ctx.last_storey`: where the last storey starts. -/
def lastStorey (cs : Cols) : Nat :=
  let par := forest cs
  ((List.range cs.size).filter fun i => i ≥ 1 && isLevel cs par i).getLast?.getD 0

/-- The indices of the `z0` columns. -/
def zIdx (seg : Cols) : List Nat := (List.range seg.size).filter fun j => !(colAt seg j).z

/-- End of a run of `z1` columns with consecutive `x`. -/
def runEnd (cs : Cols) : Nat → Nat → Nat
  | 0, j => j
  | n + 1, j =>
    if j + 1 < cs.size && (colAt cs (j + 1)).z && (colAt cs (j + 1)).x == (colAt cs j).x + 1
    then runEnd cs n (j + 1) else j

/-- Starts of the maximal runs of `z1` columns (the markers). -/
def runsGo (cs : Cols) : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, i =>
    if i ≥ cs.size then []
    else if (colAt cs i).z then i :: runsGo cs n (runEnd cs cs.size i + 1)
    else runsGo cs n (i + 1)

/-- The level named by the last column `block` writes for `gamma` (Python
`_tail_block`). -/
def tailBlockF : Nat → Od → Bool → Option Od
  | 0, _, _ => none
  | n + 1, gamma, arg =>
    match gamma.getLast? with
    | none => none
    | some (e, _) =>
      let rest := strip e
      if !rest.isEmpty then tailBlockF n rest (headIsPsi (ato e))
      else if arg then none else lvl e

/-- Python `_tail_block`. -/
def tailBlock (gamma : Od) (arg : Bool) : Option Od := tailBlockF fuel gamma arg

/-- Python `unit_tail_level`: the level named by the last column of the add unit
`ω^β`. -/
def unitTailLevel (beta : Od) : Option Od :=
  let bp := predBeta beta
  if beta.isEmpty || bp.isEmpty then none
  else match bp.getLast? with
    | some (e, _) => tailBlock (ato e) false
    | none => none

/-- Python `tail_level`: the level named by the last column of `M(α)`. -/
def tailLevel (alpha : Od) : Option Od :=
  match (units alpha).getLast? with
  | none => none
  | some b => unitTailLevel (ato b)

/-- Python `is_psi_level`: `α = ψ_{Ω_u}(X)` gives `(u, X)`. -/
def isPsiLevel (alpha : Od) : Option (Od × Od) :=
  match alpha with
  | [(a@(.psi v X), 1)] =>
    if v.isEmpty then none
    else match lvl a with
      | some u => if cmpOrd u v != .eq then some (u, X) else none
      | none => none
  | _ => none

/-! ### The state of the builder (Python `Ctx`) -/

/-- The matrix being built and what a storey needs. -/
structure Ctx where
  cols : Cols
  st : Nat := 0
  regime : Option Od
  prev : Option Od := none
  storeys : Nat := 0
  level : Int := 0
  tailSub : Option Cols := none
  leafLevel : Option Int := none
  fresh : Bool := false

/-- **Rule 6**, Python `Ctx.lay_storey`: lay a lifted copy of the last storey. -/
def laySt (y : Option Int) : StateM Ctx Unit := modify fun c =>
  let seg := storeyOf (c.cols.extract c.st c.cols.size) (y.getD (lastC c.cols).y)
  { c with st := c.cols.size, cols := c.cols ++ seg, prev := none,
           storeys := c.storeys + 1, fresh := true }

/-- The loop of Python `Ctx.copy_storey`. -/
def copyLoop : Nat → Cols → Int → StateM Ctx Int
  | 0, _, _ => pure 0
  | n + 1, src, ax => do
    let dx := ax - (colAt src 0).x
    let seg := setLastY (src.map fun c => { c with x := c.x + dx, y := c.y + 1 }) (lastC src).y
    modify fun c => { c with st := c.cols.size, cols := c.cols ++ seg,
                             storeys := c.storeys + 1, prev := none }
    let zs := zIdx seg
    if zs.length ≤ 3 then
      let k : Int := (zs.length : Int) - 1
      let isOne := k == 1
      modify fun c => { c with leafLevel := some ((lastC seg).y + (if isOne then 0 else 1)) }
      if !isOne && zs.length ≥ 2 then
        modify fun c => { c with tailSub := some (seg.extract (zs.getD (zs.length - 2) 0 + 1) seg.size) }
      pure k
    else
      let src' := seg.extract 0 (zs.getD (zs.length - 2) 0 + 1)
      let cs := (← get).cols
      copyLoop n src' ((lastRootPlain cs).2 + 1)

/-- **Rule 8**, Python `Ctx.copy_storey`: copies of the last storey, each one
sub-unit shorter, until one sub-unit is left; returns how many are left. -/
def copyStorey (ax : Int) : StateM Ctx Int := do
  let cs := (← get).cols
  let i0 := lastStorey cs
  let z0 := (List.range cs.size).filter fun j => j ≥ i0 && !(colAt cs j).z
  copyLoop fuel (cs.extract i0 (z0.getLast?.getD 0 + 1)) ax

/-! ### The builder, given `M` on smaller subscripts

Every function in this section takes `Mf`, the builder itself one step of fuel
down; `Mfuel` ties the knot. -/

section
variable (Mf : Od → Cols)

/-- **Rule 4**, Python `leaf_y`: the row-1 value of the last column of `M(v)`. -/
def leafY (v : Od) : Int := (lastC (Mf v)).y

/-- **Rule 5**, Python `suffix`: the columns after the last `z0` column of
`M(v)`. -/
def suffixOf (v : Od) : Cols :=
  let cs := Mf v
  match (List.range cs.size).reverse.find? (fun j => !(colAt cs j).z) with
  | some i => cs.extract (i + 1) cs.size
  | none => #[]

/-- **Rules 3, 4 and 10**, Python `write_level`: the columns naming the level
`Ω_v` at `x`, at chain depth `d`.  A unit's leaf is one column; a collapse
argument writes `M(v)` past what the ladders already cover, lifting the
unit-relative row-1 values by the depth the context spent elsewhere. -/
def writeLevel (v : Od) (x d : Int) (arg : Bool) (ladders : List Cols) : Cols :=
  let base := Mf v
  if !arg then #[⟨x, (lastC base).y, false⟩] else
  let par := forest base
  let step (acc : Int × Nat) (lad : Cols) : Int × Nat :=
    (List.range (commonPrefix lad base)).foldl (fun li i =>
      if i ≥ 1 && isLevel base par i && decide ((colAt base i).y ≤ d) && i > li.2
      then ((colAt base i).y, i) else li) acc
  let li := (Mf (nat d.toNat) :: ladders).foldl step (0, 0)
  let tail := base.extract (li.2 + 1) base.size
  if tail.isEmpty then #[⟨x, (lastC base).y, false⟩] else
  let bump := d - li.1
  let dx := x - (colAt tail 0).x
  tail.mapIdx fun i c =>
    ⟨c.x + dx, c.y + (if relative base par (li.2 + 1 + i) then bump else 0), c.z⟩

/-- **Rule 6**, Python `Ctx.spent`: the last leaf used up the regime's own leaf
on a different level. -/
def spent (c : Ctx) : Bool :=
  match c.prev, c.regime with
  | some u, some v =>
    cmpOrd u v != .eq && !(suffixOf Mf v).isEmpty && leafY Mf u == leafY Mf v
  | _, _ => false

/-- **Rule 5**, Python `append_suffix`: the upgrade mark, copied from where the
level is already spelt. -/
def appendSuffix (cols : Cols) (v : Od) (storeys : Nat) (tailSub : Option Cols) : Cols :=
  if (lastC cols).z then cols else
  let suf := suffixOf Mf v
  if suf.isEmpty then
    match tailSub with
    | some ts => if !ts.isEmpty && (lvlO v).isSome then cols ++ ts else cols
    | none => cols
  else
  let n := suf.size
  let dx := suf.toList.map fun c => c.x - (colAt suf 0).x
  let runs := runsGo cols cols.size 0
  let lift0 : Int := max ((lastC cols).y - leafY Mf v) 0
  let ks : List Int :=
    lift0 :: (((List.range (storeys + 1)).reverse.map fun j => (j : Int)).filter (· != lift0))
  let found := ks.findSome? fun k =>
    let pat := suf.toList.map fun c => (c.y + k, c.z)
    runs.reverse.findSome? fun i =>
      let seg := cols.extract i (i + n)
      if seg.size == n && seg.toList.map (fun c => (c.y, c.z)) == pat &&
          seg.toList.map (fun c => c.x - (colAt seg 0).x) == dx
      then some seg else none
  match found with
  | some seg => cols ++ seg
  | none => cols ++ suf

/-- **Rules 1, 3, 4, 6**, Python `block` (with a context): the OT embedding.
One column per summand `ω^δ` of `gamma`, its children spelling `strip δ`; a
countable summand is a `ψ_0` node `(x,0,0)`, an uncountable one names its
level.  A spent ladder is relaid by a storey between summands and between a
column and its children. -/
def blockF : Nat → Od → Int → Int → Bool → Option Od → Int → StateM Ctx Unit
  | 0, _, _, _, _, _, _ => pure ()
  | n + 1, gamma, x0, d0, arg, plvl, py => do
    let mut x := x0
    let mut d := d0
    for ec in gamma do
      let e := ec.1
      let subArg := headIsPsi (ato e)
      for _ in [0:ec.2] do
        if !(← get).fresh && spent Mf (← get) then
          laySt none
          let l := lastC (← get).cols
          x := l.x
          d := l.y
        let ctx ← get
        let v := lvl e
        let run : Cols :=
          match v with
          | none => #[⟨x, 0, false⟩]
          | some v =>
            if !arg && (match plvl with | some p => cmpOrd v p == .eq | none => false) then
              #[⟨x, py, false⟩]
            else if !arg && ctx.storeys != 0 &&
                (match ctx.regime with | some r => cmpOrd v r == .eq | none => false) then
              #[⟨x, (if (ctx.regime.bind lvlO).isNone then ctx.level
                     else ctx.leafLevel.getD 0), false⟩]
            else if !arg && (match ctx.regime with
                | some r => (lvlO r).isSome && leafY Mf v == leafY Mf r && cmpOrd v one != .eq
                | none => false) then
              #[⟨x, leafY Mf v + 1, false⟩]
            else writeLevel Mf v x d arg [ctx.cols]
        modify fun c => { c with cols := c.cols ++ run }
        let sub := strip e
        let mut nx := (lastC run).x + 1
        let mut nd := (lastC run).y
        modify fun c => { c with prev := if arg then none else v }
        if !sub.isEmpty && !(← get).fresh && spent Mf (← get) then
          laySt none
          let l := lastC (← get).cols
          nx := l.x + 1
          nd := l.y
        blockF n sub nx nd subArg v (lastC run).y
        modify fun c => { c with prev := tailBlock (ato e) arg }

/-- **Rules 2 and 6–8**, Python `place_units`: lay `α`'s add units after `cols`,
from the given level and root `x`, relaying the ladder by storeys where it runs
out. -/
def placeUnits (cols : Cols) (alpha : Od) (level0 rootX0 : Int) (regime : Option Od) : Ctx :=
  let act : StateM Ctx Unit := do
    let mut level := level0
    let mut rootX := rootX0
    let mut skip := 0
    if (regime.bind lvlO).isSome then
      let k ← copyStorey (rootX + 1)
      skip := if k == 1 then 1 else 0
      let lr := lastRootPlain (← get).cols
      level := lr.1
      rootX := lr.2
    let mut prev0 := false
    let mut first := true
    for b in (units alpha).drop skip do
      let beta := ato b
      modify fun c => { c with fresh := false }
      let laid := !first && spent Mf (← get)
      if laid then
        laySt none
        let lr := lastRootPlain (← get).cols
        level := lr.1
        rootX := lr.2
        prev0 := false
      if beta.isEmpty && prev0 then
        let t := lastC (← get).cols
        modify fun c => { c with cols := c.cols.push ⟨t.x + 1, t.y + 1, false⟩ }
      else if beta.isEmpty then
        modify fun c => { c with cols := c.cols ++ #[⟨rootX + 1, level, false⟩,
                                                   ⟨rootX + 2, level + 1, false⟩],
                                 prev := none }
      else
        let ax := rootX + 1
        let mut x0 := ax + 1
        let mut y := level + 1
        modify fun c => { c with level := level,
                                 cols := c.cols ++ #[⟨ax, level, false⟩, ⟨x0, y, true⟩] }
        let mut i := 0
        for e in units (predBeta beta) do
          if i != 0 && !(← get).fresh && spent Mf (← get) then
            laySt none
            let lr := lastRootPlain (← get).cols
            y := lr.1
            x0 := lr.2
            modify fun c => { c with level := lr.1 - 1 }
          modify fun c => { c with cols := c.cols.push ⟨x0 + 1, y, true⟩ }
          blockF Mf fuel (ato e) (x0 + 2) (y - 1) false none 0
          i := i + 1
        rootX := x0
      level := level + 1
      prev0 := beta.isEmpty
      if !beta.isEmpty then
        modify fun c => { c with prev := unitTailLevel beta }
      match (← get).prev, regime with
      | some p, some r =>
        if (lvlO r).isNone && !laid && cmpOrd p r == .lt then
          let dy := leafY Mf p - leafY Mf r
          if dy > 0 then
            modify fun c => { c with cols := setLastY c.cols (leafY Mf r) }
            for k in [1:dy.toNat + 1] do
              laySt (some (leafY Mf r + k))
            let lr := lastRootPlain (← get).cols
            level := lr.1
            rootX := lr.2
            prev0 := false
      | _, _ => pure ()
      first := false
  (act.run { cols := cols, regime := regime }).2

/-- The row-0 children of column `i`. -/
def kidsOf (par : Array (Option Nat)) (n i : Nat) : List Nat :=
  (List.range n).filter fun c => par.getD c none == some i

/-- The depth-first walk of Python `M_Omega`. -/
def omegaDfs (cs : Cols) (par : Array (Option Nat)) (drop : Option Nat) :
    Nat → Nat → Int → List Col
  | 0, _, _ => []
  | n + 1, i, d =>
    if drop == some i then [] else
    let c := colAt cs i
    let ins : List Col :=
      if isLevel cs par i || i == 0 then
        [⟨d + 1, c.y + 1, true⟩, ⟨d + 2, c.y + 1, true⟩, ⟨d + 3, c.y + 1, false⟩]
      else []
    (⟨d, c.y, c.z⟩ :: ins) ++ (kidsOf par cs.size i).flatMap fun k => omegaDfs cs par drop n k (d + 1)

/-- **The base**, Python `M_Omega`: `M(Ω_v)` by insertion into `M(v)` — drop a
trailing level column, put the tail `(1,1,1)(2,1,1)(3,1,0)` of
`B = M(Ω_1)` under the root anchor and every level column, and write out
row-0 depth as `x`. -/
def MOmega (v : Od) : Cols :=
  let cs := Mf v
  if cs.isEmpty then #[] else
  let par := forest cs
  let last := cs.size - 1
  let drop := if isLevel cs par last then some last else none
  (omegaDfs cs par drop (cs.size + 1) 0 0).toArray

/-- **Rule 9**, Python `M_psi_level`: `M(ψ_{Ω_u}(X))` is `M(Ω_u)` with its leaf
lowered by one, and the argument's level written below it. -/
def MpsiLevel (u X : Od) : Cols :=
  let base := MOmega Mf u
  let y0 := (lastC base).y
  let cols := setLastY base (y0 - 1)
  let x := (lastC base).x + 1
  match lvlO X with
  | none => #[]
  | some w =>
    if cmpOrd w u == .eq then cols.push ⟨x, y0, false⟩
    else appendSuffix Mf (cols ++ writeLevel Mf w x (y0 - 1) true [Mf u, cols]) w 0 none

/-- The upgrade mark at the end, if a leaf ends the matrix. -/
def finish (alpha : Od) (ctx : Ctx) : Cols :=
  match tailLevel alpha with
  | some t => appendSuffix Mf ctx.cols t ctx.storeys ctx.tailSub
  | none => ctx.cols

/-- One step of Python `M`: below `Ω_1` the add units are laid from `(0,0,0)`;
otherwise on top of `M(Ω_v)` (rule 2), from its last root. -/
def Mstep (alpha : Od) : Cols :=
  match lvlO alpha with
  | none => finish Mf alpha (placeUnits Mf #[] alpha 0 (-1) none)
  | some v =>
    match isPsiLevel alpha with
    | some uX => MpsiLevel Mf uX.1 uX.2
    | none =>
      if alpha == [(.W v, 1)] then MOmega Mf v
      else
        let base := MOmega Mf v
        let ya := lastRoot base
        finish Mf alpha (placeUnits Mf base alpha ya.1 (ya.2 - 1) (some v))

end

/-- The builder with fuel. -/
def Mfuel : Nat → Od → Cols
  | 0, _ => #[]
  | n + 1, a => Mstep (Mfuel n) a

/-- Python `M`: `α ↦` the columns of `ψ_0(Ω_α)`. -/
def M (alpha : Od) : Cols := Mfuel fuel alpha

/-- Columns as the three-row lists `Trio.lean` uses. -/
def toRows (cs : Cols) : List (List Nat) :=
  cs.toList.map fun c => [c.x.toNat, c.y.toNat, if c.z then 1 else 0]

/-- **The trio matrix of `ψ_0(Ω_α)` for `α < Λ`**, by rules 1–10. -/
def trioRuleMatrix (alpha : Od) : List (List Nat) := toRows (M alpha)

/-- Python `Many`: the matrix for a label of the sheet. -/
def trioRuleMatrixOf (s : String) : Option (List (List Nat)) := do
  let a ← parse s
  if a.isEmpty then none else some (trioRuleMatrix a)

/-! ### Reading a term of the extended Buchholz notation

`cons a b t` is `ψ_a(b) + t`.  `ψ_0(0) = 1`; `ψ_0(b) = ω^b` when `b` has no
`Ω` in it (`b < ε₀`); otherwise `ψ_0(b)` is a collapse atom.  `ψ_a(0) = Ω_a`
and `ψ_a(b)` is a collapse atom. -/

/-- No `ψ` with a nonzero subscript anywhere in the term. -/
def omegaFree : Term → Bool
  | nil => true
  | cons a b t => a == nil && omegaFree b && omegaFree t

/-- The normal form of a term. -/
def ofTerm : Term → Od
  | nil => []
  | cons a b t =>
    let s : Od :=
      if a == nil then
        (if b == nil then one else if omegaFree b then wpow (ofTerm b)
         else [(.psi [] (ofTerm b), 1)])
      else if b == nil then [(.W (ofTerm a), 1)]
      else [(.psi (ofTerm a) (ofTerm b), 1)]
    add s (ofTerm t)

/-- **The map on terms**: `trioMatrix` of `Trio.lean`, extended by rules 1–10. -/
def trioMatrixL (α : Term) : List (List Nat) := trioRuleMatrix (ofTerm α)

/-! ### Well formed by construction -/

theorem WF3_toRows (cs : Cols) : WF3 (toRows cs) := by
  intro c hc
  rw [toRows, List.mem_map] at hc
  obtain ⟨a, -, rfl⟩ := hc
  refine ⟨rfl, ?_⟩
  cases a.z <;> simp

/-- **Every column of the rule-built matrix is three rows deep with `z < 2`.** -/
theorem WF3_trioRuleMatrix (alpha : Od) : WF3 (trioRuleMatrix alpha) := WF3_toRows _

/-- **The same for the map on terms.** -/
theorem WF3_trioMatrixL (α : Term) : WF3 (trioMatrixL α) := WF3_trioRuleMatrix _

/-! ### It extends `Trio.lean`'s map

On every term `Trio.lean` checks, the rule-built matrix is `trioMatrix`. -/

open Googology.Trans.BMS (trioMatrix omegaIndexMatrix omegaFinMatrix opowT)

#guard trioMatrixL t1 = trioMatrix t1
#guard trioMatrixL (addT t1 t1) = trioMatrix (addT t1 t1)
#guard trioMatrixL (addT t1 (addT t1 t1)) = trioMatrix (addT t1 (addT t1 t1))
#guard trioMatrixL (opowT t1) = trioMatrix (opowT t1)
#guard trioMatrixL (addT (opowT t1) t1) = trioMatrix (addT (opowT t1) t1)
#guard trioMatrixL (addT (opowT t1) (addT t1 t1)) = trioMatrix (addT (opowT t1) (addT t1 t1))
#guard trioMatrixL (addT (opowT t1) (opowT t1)) = trioMatrix (addT (opowT t1) (opowT t1))
#guard trioMatrixL (addT (opowT t1) (addT (opowT t1) t1))
  = trioMatrix (addT (opowT t1) (addT (opowT t1) t1))
#guard trioMatrixL (addT (opowT t1) (addT (opowT t1) (opowT t1)))
  = trioMatrix (addT (opowT t1) (addT (opowT t1) (opowT t1)))
#guard trioMatrixL (opowT (addT t1 t1)) = trioMatrix (opowT (addT t1 t1))
#guard trioMatrixL (addT (opowT (addT t1 t1)) t1) = trioMatrix (addT (opowT (addT t1 t1)) t1)
#guard trioMatrixL (addT (opowT (addT t1 t1)) (opowT t1))
  = trioMatrix (addT (opowT (addT t1 t1)) (opowT t1))
#guard trioMatrixL (addT (opowT (addT t1 t1)) (opowT (addT t1 t1)))
  = trioMatrix (addT (opowT (addT t1 t1)) (opowT (addT t1 t1)))
#guard trioMatrixL (opowT (addT t1 (addT t1 t1))) = trioMatrix (opowT (addT t1 (addT t1 t1)))
#guard trioMatrixL (opowT (opowT t1)) = trioMatrix (opowT (opowT t1))
#guard trioMatrixL (addT (opowT (opowT t1)) t1) = trioMatrix (addT (opowT (opowT t1)) t1)
#guard trioMatrixL (opowT (addT (opowT t1) t1)) = trioMatrix (opowT (addT (opowT t1) t1))
#guard trioMatrixL (opowT (opowT (opowT t1))) = trioMatrix (opowT (opowT (opowT t1)))
#guard trioMatrixL (opowT (opowT (opowT (opowT t1))))
  = trioMatrix (opowT (opowT (opowT (opowT t1))))
#guard trioMatrixL (opowT (addT (opowT (addT t1 t1)) (opowT (addT t1 t1))))
  = trioMatrix (opowT (addT (opowT (addT t1 t1)) (opowT (addT t1 t1))))
#guard trioMatrixL te0 = trioMatrix te0
#guard trioMatrixL (psi nil (psi (addT t1 t1) nil)) = trioMatrix (psi nil (psi (addT t1 t1) nil))
#guard trioMatrixL (psi nil (psi (opowT t1) nil)) = trioMatrix (psi nil (psi (opowT t1) nil))
#guard trioMatrixL (psi nil (psi (addT (opowT t1) t1) nil))
  = trioMatrix (psi nil (psi (addT (opowT t1) t1) nil))
#guard trioMatrixL (psi nil (psi (addT (opowT t1) (opowT t1)) nil))
  = trioMatrix (psi nil (psi (addT (opowT t1) (opowT t1)) nil))
#guard trioMatrixL (psi nil (psi (opowT (addT t1 t1)) nil))
  = trioMatrix (psi nil (psi (opowT (addT t1 t1)) nil))
#guard trioMatrixL (psi nil (psi (opowT (opowT t1)) nil))
  = trioMatrix (psi nil (psi (opowT (opowT t1)) nil))

/-! ### The base `M(Ω_v)`: insertion agrees with the closed form

The algorithm page states `M(Ω_v) = B ++ L(B) ++ ⋯ ++ L^{v-1}(B)` for finite
`v` and says the insertion was machine-checked against it for `v = 1, …, 6`;
here it is checked against `omegaFinMatrix` of `Trio.lean`. -/

#guard trioRuleMatrix [(.W (nat 1), 1)] = omegaFinMatrix 1
#guard trioRuleMatrix [(.W (nat 2), 1)] = omegaFinMatrix 2
#guard trioRuleMatrix [(.W (nat 3), 1)] = omegaFinMatrix 3
#guard trioRuleMatrix [(.W (nat 4), 1)] = omegaFinMatrix 4
#guard trioRuleMatrix [(.W (nat 5), 1)] = omegaFinMatrix 5
#guard trioRuleMatrix [(.W (nat 6), 1)] = omegaFinMatrix 6

/-! ### Examples from the algorithm page -/

-- Rule 5: `M(Ω_ω) = M(Ω_1) ++ (1,1,1)`.
#guard trioRuleMatrixOf "W_w" = some [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1]]
-- The collapse clause: `M(ω^ω) = (0,0,0)(1,1,1)(2,1,1)(3,0,0)` gives
-- `M(ψ_0(Ω_{ω^ω})) = (0,0,0)(1,1,1)(2,1,1)(3,0,0)(4,1,1)(5,1,1)(6,0,0)`.
#guard trioRuleMatrixOf "w^w" = some [[0,0,0],[1,1,1],[2,1,1],[3,0,0]]
#guard trioRuleMatrixOf "psi(W_(w^w))"
  = some [[0,0,0],[1,1,1],[2,1,1],[3,0,0],[4,1,1],[5,1,1],[6,0,0]]

end Googology.Trans.BMS.TrioRules
