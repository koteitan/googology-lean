import Googology.Trans.BMS.TrioRulesAll

/-!
# Fix G and Fix M: leaves with more after them outside the tower regimes, and marked levels

A patch on top of `TrioRulesAll.lean` (rules 1–10 of
[koteitan/trio](https://github.com/koteitan/trio) with Fixes A–E and N).  The checks
are in `TrioFixNonLastOtherSheet.lean`; they are `#guard`s, a calibration, not a
theorem.  `M(α)` is the matrix of `ψ_0(Ω_α)`, `M[n]` is yaBMS's `[n]` (`expandRL 3 n`).

## The fault

Fix N (`TrioRulesNonLast.lean`) acts only when the regime `r` (the units are laid on
`M(Ω_r)`) is a tower over `1` (`Ω`, `Ω_Ω`, `Ω_{Ω_Ω}`, …).  Outside the towers
(`r = Ω_ω`, `Ω_{ω+1}`, `Ω_2`, `Ω_3`, `Ω+1`, `Ω+2`, …), and at levels with a mark
(`ω`, `ω·2`, `Ω_ω`, …) in any uncountable regime, a leaf with more after it gets the
plain continuation, so different levels get one matrix.  Two more faults in the same
regimes: rule 6's storey (`spent`) is laid after a leaf at `y = 1` (not standard),
and a level `b + n` of a class (below) is named by the leaf of another level
(`Ω_{Ω_ω}+Ω_{ω+1}` and `Ω_{Ω_ω}+Ω_2` get one matrix).  Applying Fix N as it is to
`r = Ω_ω` adds collisions (TRIO-NONLAST-LEAF.md, "Still open" 1).

## Classes and tops

`chainG r = [t_k = r, t_{k-1}, …]` with `t_{i-1} = w` when `t_i = Ω_w`, `t_{i-1} =
t_i - 1` when `t_i` is a successor; the chain stops at a limit or at `0`.  So
`chainG (Ω_Ω) = [Ω_Ω, Ω, 1]` (Fix N's `tops`), `chainG (Ω_ω) = [Ω_ω, ω]`,
`chainG (Ω_2) = [Ω_2, 2, 1]`, `chainG (Ω+1) = [Ω+1, Ω, 1]`.  The `t_i` are the
**tops**.  The **base** of a level `p` is `t + 1` for the greatest top `t < p`, else
`1` (`lvlBase`); `p = base + n` with `1 ≤ n < 64` gives `liftCount r p = n`.

## The change (exactly this, nothing else)

`MstepX Mf α = MstepAll Mf α` except in the sum branch (`α` neither `Ω_v` nor
`ψ_{Ω_u}(X)`), where `placeUnitsX` replaces `placeUnitsN`.  `placeUnitsX`, `blockX`
and `restateX` are `placeUnitsN`, `blockN` and `restate` of `TrioRulesNonLast.lean`
with these four changes.  Write `r` for the regime, `p` for the level the last leaf
names (`prev`), `cap` for the level of the last lifted copy.

1. **No storey for a spent ladder in an uncountable regime.**  Every call of rule 6's
   `spent` is `spentX`, which is `false` when `lvlO r ≠ none` and `spent` otherwise.
2. **Fix G (Fix N outside the towers).**  Where `placeUnitsN` asks `fixNNeeded`, ask
   `fixXNeeded = fixNNeeded ∨ fixGNeeded ∨ fixMNeeded`.  `fixGNeeded`: `r` is
   uncountable and not a tower over `1`, the last column is a leaf (`z = 0`), `p`'s
   chain has no mark (`suffixOf (chainBase p) = []`), `p ∉ chainG r`, `p ≠ cap`,
   `p + 1 ≠ cap`.  When `fixGNeeded` or `fixNNeeded` holds, Fix N's step `fixN` runs
   unchanged (the upgrade, the lifted copy with the leaf kept, `restate` when a
   sub-unit was written).
3. **Fix M (a marked level that is not a top).**  `fixMNeeded`: `r` uncountable (a
   tower or not), the last column is a leaf, `p`'s chain has a mark, `p ∉ chainG r`,
   `p ≠ cap`.  Then `fixM`: the upgrade (`upgradeNF`), the mark (`suffixIn` in the
   last lifted copy, else `appendSuffix`), then Fix N's kept copy (`blift`) of the
   columns up to the last leaf before the mark, from that leaf's row-1 parent, or from
   the previous copy's start when that parent is the previous copy's root (Fix N 2);
   `cap := p`, `capy :=` the kept leaf's value unless a sub-unit was written.  No unit
   is laid again (`fixM` returns `false`).
4. **Lifted leaves (outside the towers).**  In `blockX`, a unit's leaf (not a collapse
   argument, not the level of the column above) naming `p = b + n`, `b = lvlBase r p`,
   `n = liftCount r p ≥ 1`, `p ≠ cap`, `r` uncountable and not a tower: the leaf of `b`
   (`leafNameN`, else `writeLevel`), then `n` lifted copies (`layLifts`).  First
   choice (`liftByMark`): when the class limit `b + ω` has a one-column mark `m`
   (`markCols`) and `leafY (b + ω) ≤` the leaf's row 1, the copies are BMS's own,
   `cols := expandRL 3 n (cols ++ [m])`, i.e. `M(γ + Ω_{b+n}) = M(γ + Ω_{b+ω})[n]`.
   Otherwise `n` copies `bliftL` (Fix N's `blift` with the leaf lifted, not kept),
   each from `copyRootN`.  Fix N's state then records the last copy (`fst`, `fend`)
   and `fs0`.

Nothing else changes: `leafNameNF`, `upgradeNF`, `suffixIn`, `finishN`, `fixN`, Fix D
and rules 1–10 are reused as they are.  The Python reference is the flag set
`nospent, G, lift, captop, liftstate, mark = b, marktower, bymark` of the calibration
script (not published); the Lean builder equals it on 1,924 test labels.

## What the checks show (`TrioFixNonLastOtherSheet.lean`)

* On the 822 sheet labels and Fix N's two families (`familyW`, `family1`) the patched
  matrix is `TrioRulesAll`'s, so every check of `TrioRulesAllSheet.lean` still holds.
* Five families of sums after `Ω_{Ω_ω}`, `Ω_{Ω_{ω+1}}`, `Ω_{Ω_2}` and (marked levels)
  `Ω_{Ω_Ω}`, `Ω_Ω`, 688 labels: order disagreements `8,008 → 5`, colliding pairs
  `490 → 3` (per family in the sheet).  Not standard (yaBMS `bms -s`, outside Lean):
  `143 → 6`.  Three more families (`Ω_{Ω+1}`, `Ω_{Ω+2}`, `Ω_{Ω_3}`, 332 labels,
  Python only): `795 → 0` disagreements, `0` not standard either way.
* BMS expansion: on 27 labels `P + t·ω`, `M(P+t·ω)[1] = M(P+t·2)` and
  `M(P+t·ω)[2] = M(P+t·3)` with the patch (without it `[2]` fails on all 27 and `[1]`
  on 9); and
  `M(Ω_{Ω_ω}+Ω_Ω+Ω_{ω·2})[n] = M(Ω_{Ω_ω}+Ω_Ω+Ω_{ω+n+1})` (`n = 1, 2`), which the
  `bliftL` copies alone do not give.

## Still open

* After two lifted copies, `γ + Ω_2 + Ω_2` and `γ + Ω_2 + Ω` still share a matrix when
  the second copy starts at the first copy's start and its leaf does not ascend
  (`Ω_Ω+Ω_ω+Ω_2+…`, `Ω_{Ω_Ω}+Ω_{Ω_ω}+Ω_2+…`, and Fix N's own
  `Ω_{Ω_Ω}+Ω_{Ω_2}+Ω_2+…`).  BMS expansion confirms the shared matrix as
  `γ + Ω_2·2` (it is `M(γ+Ω_2·ω)[1]`), so `γ + Ω_2 + Ω` needs another matrix; lowering
  every later leaf by one makes it collide with `γ + Ω_2 + ω^ω`, and keeping the
  cap's leaf breaks the `·ω` expansions.  Not solved.  In the regime `Ω_ω`
  (`γ = Ω_{Ω_ω}+Ω_Ω`) the same pair is reversed instead of shared:
  `M(γ+Ω_2+Ω_2) < M(γ+Ω_2+Ω)` (the one disagreement of that family).
* In the regime `Ω_ω`, a Fix G copy whose kept leaf falls to row 1 value `0`
  (`Ω_{Ω_ω}+Ω_Ω+Ω+Ω`) gives the matrix of `Ω_{Ω_ω}+Ω_Ω+Ω+ω^ω`.
* Fix M in a tower regime: `M(Ω_{Ω_Ω}+Ω_{Ω_ω}·ω)[n]` lies above
  `M(Ω_{Ω_Ω}+Ω_{Ω_ω}·(n+2))` (`n = 1, 2, 3`), and 3 pairs of the `Ω_{Ω_Ω}` family
  are out of order.  Without the patch that family has 91 colliding pairs.  Fix M also
  makes 3 matrices of that family not standard that were standard before
  (`Ω_{Ω_Ω}+Ω_{Ω_ω}+Ω_{Ω+1}+Ω_ω`, `Ω_{Ω_Ω}+Ω_{Ω_ω}+Ω_ω+Ω_ω`, `Ω_{Ω_Ω}+Ω_{Ω_ω}+Ω_ω+Ω_2`;
  yaBMS `bms -s`, outside Lean).
* Last leaves naming a level that is not `base + n` (`Ω_{Ω_2}+Ω_{Ω+1}` and
  `Ω_{Ω_2}+Ω_3`): not this item, unchanged.
* Outside the calibrated families the patch puts pairs out of order that were in order
  before (review, Python reference and Lean `#eval`, not in the sheet):
  - Fix M (change 3) in the regimes `Ω_2`, `Ω_3`, `Ω_4`, `Ω+1`, on a leaf of `Ω_ω` with
    more after it: `M(Ω_{Ω_2}+Ω_ω+Ω) < M(Ω_{Ω_2}+Ω+ω)` (also after `Ω_{Ω_3}`, `Ω_{Ω_4}`,
    `Ω_{Ω_{Ω+1}}`), and yaBMS finds the patched matrix not standard; without the patch
    the order is right and the matrix standard.  The family after `Ω_{Ω_2}` above has
    no `Ω_ω` term.  Sums of up to three terms from `1, ω, Ω, Ω_2, Ω_3, Ω_4, Ω_ω,
    Ω_{Ω_2}` after `Ω_{Ω_2}` (165 labels, Python): 278 pairs that the patch puts out
    of order (1,695 that it puts in order), 15 matrices that become not standard.
  - Fix G (change 2) in the regimes `Ω_{ω·2}`, `Ω_{ω+2}`, `Ω_{Ω_ω}`:
    `M(Ω_{Ω_{ω·2}}+Ω_{ω·2}) > M(Ω_{Ω_{ω·2}}+Ω_Ω+Ω)`,
    `M(Ω_{Ω_{ω+2}}+Ω_Ω+Ω) < M(Ω_{Ω_{ω+2}}+Ω_{ω+1}+ω)`,
    `M(Ω_{Ω_{Ω_ω}}+Ω_Ω+Ω) < M(Ω_{Ω_{Ω_ω}}+Ω_ω+1)`.
  - Change 1 in the regime `Ω_{ω^2}`: `M(Ω_{Ω_{ω^2}}+Ω_{ω·2}) < M(Ω_{Ω_{ω^2}}+Ω_ω+Ω)`.
-/

namespace Googology.Trans.BMS.TrioFixNonLastOther

open Googology.Trans.BMS.TrioRules
open Googology.Trans.BMS.TrioRules2
open Googology.Trans.BMS.TrioRules3
open Googology.Trans.BMS.TrioRulesNL
open Googology.Trans.BMS.TrioRulesAll

/-! ### Classes of levels in a regime -/

/-- `r` is a tower over `1` (Fix N's regimes). -/
def isTower (r : Od) : Bool :=
  (lvlO r).isSome && (omArg r).isSome && cmpOrd (chainBase r) one == .eq

/-- An uncountable regime that is not a tower over `1`. -/
def otherRegime (r : Od) : Bool := (lvlO r).isSome && !isTower r

/-- `t - 1` when `t` is a successor ordinal. -/
def predFin (t : Od) : Option Od :=
  match t.getLast? with
  | some (.o [], k) => some (t.dropLast ++ (if k > 1 then [(.o [], k - 1)] else []))
  | _ => none

/-- The generalised tops: `t, w` (for `t = Ω_w`) or `t - 1` (for a successor), … -/
def chainG : Nat → Od → List Od
  | 0, _ => []
  | n + 1, t =>
    if t.isEmpty then [] else
    t :: match omArg t with
      | some w => chainG n w
      | none => match predFin t with
        | some u => chainG n u
        | none => []

/-- The tops of a regime. -/
def topsG (r : Od) : List Od := chainG fuel r

/-- The base of `p`'s class: one above the greatest top below `p`, else `1`. -/
def lvlBase (r p : Od) : Od :=
  match (topsG r).find? (fun t => cmpOrd t p == .lt) with
  | some t => add t one
  | none => one

/-- `n` when `p = base + n` with `1 ≤ n < 64`, else `0`. -/
def liftCount (r p : Od) : Nat :=
  let b := lvlBase r p
  ((List.range 63).map (· + 1)).find? (fun n => cmpOrd (add b (nat n)) p == .eq) |>.getD 0

/-- The class limit `b + ω` of `p = b + n`. -/
def classLim (r p : Od) : Option Od :=
  if !otherRegime r then none else
  let b := lvlBase r p
  if cmpOrd b p == .eq || liftCount r p > 0 then some (add b (wpow one)) else none

/-- Is `p` one of the tops of `r`? -/
def isTop (r p : Od) : Bool := (topsG r).any fun t => cmpOrd p t == .eq

/-- `p` is the cap of the last copy. -/
def isCap (s : CtxN) (p : Od) : Bool :=
  match s.n.cap with
  | some q => cmpOrd p q == .eq
  | none => false

/-! ### Columns -/

/-- `blift` with the last leaf lifted, not kept. -/
def bliftL (cs : Cols) (s0 : Nat) : Cols :=
  let seg := blift cs s0
  setLastY seg ((lastC seg).y + 1)

/-- Rows to columns (the inverse of `toRows` on three-row matrices). -/
def ofRows (l : List (List Nat)) : Cols :=
  (l.map fun r => (⟨(r.getD 0 0 : Int), (r.getD 1 0 : Int), r.getD 2 0 != 0⟩ : TrioRules.Col)).toArray

/-- Fix N's copy root for the leaf at `i`: its row-1 parent, or the start of the
previous copy when that parent is the previous copy's root. -/
def copyRootN (s : CtxN) (cols : Cols) (i : Nat) : Nat :=
  let raw := ((par1 cols).getD i none).getD 0
  match s.n.fst, s.n.fs0 with
  | some f, some q => if q == raw then f else raw
  | _, _ => raw

section
variable (Mf : Od → Cols)

/-- **Change 1**: rule 6's `spent`, never in an uncountable regime. -/
def spentX (c : Ctx) : Bool :=
  if (c.regime.bind lvlO).isSome then false else spent Mf c

/-- **Change 2**: Fix N outside the towers. -/
def fixGNeeded (s : CtxN) : Bool :=
  match s.c.regime, s.c.prev with
  | some r, some p =>
    otherRegime r && !(lastC s.c.cols).z && (suffixOf Mf (chainBase p)).isEmpty &&
      !isTop r p && !isCap s p && !isCap s (add p one)
  | _, _ => false

/-- **Change 3**: a marked level that is not a top, with more after it. -/
def fixMNeeded (s : CtxN) : Bool :=
  match s.c.regime, s.c.prev with
  | some r, some p =>
    (lvlO r).isSome && !(lastC s.c.cols).z && !(suffixOf Mf (chainBase p)).isEmpty &&
      !isTop r p && !isCap s p
  | _, _ => false

/-- Fix N, Fix G or Fix M is needed. -/
def fixXNeeded (s : CtxN) : Bool := fixNNeeded Mf s || fixGNeeded Mf s || fixMNeeded Mf s

/-- The mark the finish writes for a leaf naming `v` at the end of `cols`. -/
def markCols (s : CtxN) (cols : Cols) (v : Od) : Cols :=
  let inCopy : Option Cols :=
    match s.n.fst with
    | some a => if (suffixOf Mf v).isEmpty then none else suffixIn Mf cols v a s.n.fend
    | none => none
  match inCopy with
  | some seg => cols ++ seg
  | none => appendSuffix Mf cols v s.c.storeys none

/-- **Change 3**, `fixM`: the upgrade and the mark, then the kept copy of the columns
up to the last leaf before the mark.  Returns `false` (no unit is laid again). -/
def fixM : StateM CtxN Bool := do
  let s ← get
  let p := s.c.prev.getD []
  let u := upgradeNF Mf fuel s s.c.cols p false
  let used := u.2.2
  let li := u.1.size - 1
  let cols := markCols Mf s u.1 u.2.1
  let s0 := copyRootN s cols li
  let seg := blift (cols.extract 0 (li + 1)) s0
  let cols' := cols ++ seg
  set ({ c := { s.c with cols := cols', st := cols.size, prev := none },
         n := { s.n with cap := s.c.prev, fs0 := some s0, fst := some cols.size,
                         fend := cols'.size, fcount := s.n.fcount + 1,
                         capy := if used then none else some (lastC seg).y } } : CtxN)
  pure false

/-- Fix M, else Fix N (which is also Fix G). -/
def fixX : StateM CtxN Bool := do
  if fixMNeeded Mf (← get) then fixM Mf else fixN Mf

/-- **Change 4**: `n` lifted copies naming `b+1, …, b+n` after the leaf of `b` that
ends `cols`, by BMS expansion of the class limit's mark when there is one. -/
def liftByMark (s : CtxN) (cols : Cols) (b : Od) (n : Nat) : Option Cols :=
  match s.c.regime.bind (fun r => classLim r b) with
  | none => none
  | some lim =>
    if decide (leafY Mf lim > (lastC cols).y) || (suffixOf Mf lim).size != 1 then none else
    let withMark := markCols Mf s cols lim
    if withMark.size != cols.size + 1 then none else
    let e := ofRows (expandRL 3 n (toRows withMark))
    if e.size > cols.size && e.extract 0 cols.size == cols then some (e.extract cols.size e.size)
    else none

/-- **Change 4**: lay the lifted copies after the leaf of `b` (the state's last
column), recording the last copy in Fix N's state. -/
def layLifts (b : Od) (n : Nat) : StateM CtxN Unit := do
  let s ← get
  let cols := s.c.cols
  match liftByMark Mf s cols b n with
  | some segs =>
    let cols' := cols ++ segs
    let len := segs.size / n
    set ({ s with c := { s.c with cols := cols' },
                  n := { s.n with fs0 := (par1 cols').getD (cols'.size - 1) none,
                                  fst := some (cols.size + len * (n - 1)),
                                  fend := cols'.size } } : CtxN)
  | none =>
    for _ in [0:n] do
      let s ← get
      let cols := s.c.cols
      let raw := ((par1 cols).getD (cols.size - 1) none).getD 0
      let s0 := copyRootN s cols (cols.size - 1)
      let seg := bliftL cols s0
      set ({ s with c := { s.c with cols := cols ++ seg },
                    n := { s.n with fs0 := some raw, fst := some cols.size,
                                    fend := cols.size + seg.size } } : CtxN)

/-- The level `p = b + n` of a unit's leaf that change 4 writes by lifted copies:
`some (b, n)`. -/
def liftLeaf (s : CtxN) (v : Od) : Option (Od × Nat) :=
  match s.c.regime with
  | some r =>
    if otherRegime r && !isCap s v then
      let n := liftCount r v
      if n > 0 then some (lvlBase r v, n) else none
    else none
  | none => none

/-- `blockN` with changes 1 and 4. -/
def blockX : Nat → Od → Int → Int → Bool → Option Od → Int → StateM CtxN Unit
  | 0, _, _, _, _, _, _ => pure ()
  | n + 1, gamma, x0, d0, arg, plvl, py => do
    let mut x := x0
    let mut d := d0
    for ec in gamma do
      let e := ec.1
      let subArg := headIsPsi (ato e)
      for _ in [0:ec.2] do
        if !(← get).c.fresh && spentX Mf (← get).c then
          TrioRulesNL.liftC (laySt none)
          let l := lastC (← get).c.cols
          x := l.x
          d := l.y
        let s ← get
        let v := lvl e
        let samePlvl : Bool := match v, plvl with
          | some v, some p => cmpOrd v p == .eq
          | _, _ => false
        let lifted : Option (Od × Nat) :=
          match v with
          | some v => if !arg && !samePlvl then liftLeaf s v else none
          | none => none
        match lifted with
        | some (b, k) =>
          let run : Cols :=
            match leafNameN Mf s b with
            | some y => #[⟨x, y, false⟩]
            | none => writeLevel Mf b x d arg [s.c.cols]
          modify fun s => { s with c := { s.c with cols := s.c.cols ++ run } }
          layLifts Mf b k
        | none =>
          let run : Cols :=
            match v with
            | none => #[⟨x, 0, false⟩]
            | some v =>
              if !arg && samePlvl then
                #[⟨x, py, false⟩]
              else if !arg then
                match leafNameN Mf s v with
                | some y => #[⟨x, y, false⟩]
                | none => writeLevel Mf v x d arg [s.c.cols]
              else writeLevel Mf v x d arg [s.c.cols]
          modify fun s => { s with c := { s.c with cols := s.c.cols ++ run } }
        let lastRun := lastC (← get).c.cols
        let sub := strip e
        let mut nx := lastRun.x + 1
        let mut nd := lastRun.y
        modify fun s => { s with c := { s.c with prev := if arg then none else v } }
        if !sub.isEmpty && !(← get).c.fresh && spentX Mf (← get).c then
          TrioRulesNL.liftC (laySt none)
          let l := lastC (← get).c.cols
          nx := l.x + 1
          nd := l.y
        blockX n sub nx nd subArg v lastRun.y
        modify fun s => { s with c := { s.c with prev := tailBlock (ato e) arg } }

/-- `restate` of Fix N 4 with `blockX`. -/
def restateX (digits : List Ex) : StateM CtxN (Int × Int) := do
  let lr := lastRootPlain (← get).c.cols
  let y := lr.1 + 1
  let x0 := lr.2 + 2
  let two : Cols := #[⟨lr.2 + 1, lr.1, false⟩, ⟨x0, y, true⟩]
  modify fun s => { s with c := { s.c with cols := s.c.cols ++ two, level := y - 1 } }
  for e in digits do
    modify fun s => { s with c := { s.c with cols := s.c.cols.push ⟨x0 + 1, y, true⟩ } }
    blockX Mf fuel (ato e) (x0 + 2) (y - 1) false none 0
  pure (y, x0)

/-- `placeUnitsN` with changes 1–4. -/
def placeUnitsX (cols : Cols) (alpha : Od) (level0 rootX0 : Int) (regime : Option Od) :
    CtxN :=
  let act : StateM CtxN Unit := do
    let mut level := level0
    let mut rootX := rootX0
    let mut skip := 0
    if (regime.bind lvlO).isSome then
      let k ← TrioRulesNL.liftC (copyStorey (rootX + 1))
      skip := if k == 1 then 1 else 0
      let lr := lastRootPlain (← get).c.cols
      level := lr.1
      rootX := lr.2
      if skip == 1 then
        match (units alpha).head? with
        | some b0 =>
          let alld := units (predBeta (ato b0))
          let rest := alld.drop 1
          let mut j := 0
          for e in rest do
            if fixXNeeded Mf (← get) then
              if ← fixX Mf then
                let lr ← restateX Mf (alld.take (j + 1))
                level := lr.1
                rootX := lr.2
              else
                let lr := lastRootPlain (← get).c.cols
                level := lr.1
                rootX := lr.2
            modify fun s => { s with c := { s.c with cols := s.c.cols.push ⟨rootX + 1, level, true⟩ } }
            blockX Mf fuel (ato e) (rootX + 2) (level - 1) false none 0
            j := j + 1
          if !rest.isEmpty then
            modify fun s => { s with c := { s.c with prev := unitTailLevel (ato b0) } }
        | none => pure ()
    let mut prev0 := false
    let mut first := true
    for b in (units alpha).drop skip do
      let beta := ato b
      modify fun s => { s with c := { s.c with fresh := false } }
      let laid := !first && spentX Mf (← get).c
      if laid then
        TrioRulesNL.liftC (laySt none)
        let lr := lastRootPlain (← get).c.cols
        level := lr.1
        rootX := lr.2
        prev0 := false
      else if (!first || skip == 1) && fixXNeeded Mf (← get) then
        let _ ← fixX Mf
        let lr := lastRootPlain (← get).c.cols
        level := lr.1
        rootX := lr.2
        prev0 := false
      if beta.isEmpty && prev0 then
        let t := lastC (← get).c.cols
        modify fun s => { s with c := { s.c with cols := s.c.cols.push ⟨t.x + 1, t.y + 1, false⟩ } }
      else if beta.isEmpty then
        let two : Cols := #[⟨rootX + 1, level, false⟩, ⟨rootX + 2, level + 1, false⟩]
        modify fun s => { s with c := { s.c with cols := s.c.cols ++ two, prev := none } }
      else
        let ax := rootX + 1
        let mut x0 := ax + 1
        let mut y := level + 1
        let two : Cols := #[⟨ax, level, false⟩, ⟨x0, y, true⟩]
        modify fun s => { s with c := { s.c with level := level, cols := s.c.cols ++ two } }
        let digits := units (predBeta beta)
        let mut i := 0
        for e in digits do
          if i != 0 && !(← get).c.fresh && spentX Mf (← get).c then
            TrioRulesNL.liftC (laySt none)
            let lr := lastRootPlain (← get).c.cols
            y := lr.1
            x0 := lr.2
            modify fun s => { s with c := { s.c with level := lr.1 - 1 } }
          else if i != 0 && fixXNeeded Mf (← get) then
            if ← fixX Mf then
              let lr ← restateX Mf (digits.take i)
              y := lr.1
              x0 := lr.2
            else
              let lr := lastRootPlain (← get).c.cols
              y := lr.1
              x0 := lr.2
              modify fun s => { s with c := { s.c with level := lr.1 - 1 } }
          modify fun s => { s with c := { s.c with cols := s.c.cols.push ⟨x0 + 1, y, true⟩ } }
          blockX Mf fuel (ato e) (x0 + 2) (y - 1) false none 0
          -- Fix D: a digit too deep for a countable regime, with digits after it.
          match tailBlock (ato e) false, regime with
          | some p, some r =>
            if i + 1 < digits.length && (lvlO r).isNone && cmpOrd p r == .lt &&
                decide (leafY Mf p > leafY Mf r) then
              modify fun s => { s with c := { s.c with cols := setLastY s.c.cols (leafY Mf r) } }
              for k in [1:(leafY Mf p - leafY Mf r).toNat + 1] do
                TrioRulesNL.liftC (laySt (some (leafY Mf r + k)))
              TrioRulesNL.liftC (laySt none)
              let lr := lastRootPlain (← get).c.cols
              y := lr.1
              x0 := lr.2
              modify fun s => { s with c := { s.c with level := lr.1 - 1 } }
          | _, _ => pure ()
          i := i + 1
        rootX := x0
      level := level + 1
      prev0 := beta.isEmpty
      if !beta.isEmpty then
        modify fun s => { s with c := { s.c with prev := unitTailLevel beta } }
      match (← get).c.prev, regime with
      | some p, some r =>
        if (lvlO r).isNone && !laid && cmpOrd p r == .lt then
          let dy := leafY Mf p - leafY Mf r
          if dy > 0 then
            modify fun s => { s with c := { s.c with cols := setLastY s.c.cols (leafY Mf r) } }
            for k in [1:dy.toNat + 1] do
              TrioRulesNL.liftC (laySt (some (leafY Mf r + k)))
            let lr := lastRootPlain (← get).c.cols
            level := lr.1
            rootX := lr.2
            prev0 := false
      | _, _ => pure ()
      first := false
  (act.run { c := { cols := cols, regime := regime } }).2

/-- **One step of the patched builder**: `MstepAll` with `placeUnitsX` in the sum
branch. -/
def MstepX (alpha : Od) : Cols :=
  match lvlO alpha with
  | none => finishN Mf alpha (placeUnitsX Mf #[] alpha 0 (-1) none)
  | some v =>
    match isPsiLevel alpha with
    | some uX => MpsiLevel3 Mf uX.1 uX.2
    | none =>
      if alpha == [(.W v, 1)] then MOmega2 Mf v
      else
        let base := MOmega2 Mf v
        let ya := lastRoot base
        finishN Mf alpha (placeUnitsX Mf base alpha ya.1 (ya.2 - 1) (some v))

end

/-- The patched builder with fuel. -/
def MfuelX : Nat → Od → Cols
  | 0, _ => #[]
  | n + 1, a => MstepX (MfuelX n) a

/-- `α ↦` the columns of `ψ_0(Ω_α)`, by the rules with Fixes A–E, N, G and M (changes 1–4). -/
def MX (alpha : Od) : Cols := MfuelX fuel alpha

/-- **The trio matrix of `ψ_0(Ω_α)` with Fixes A–E, N, G and M (changes 1–4).** -/
def trioRuleMatrixX (alpha : Od) : List (List Nat) := toRows (MX alpha)

/-- The matrix for a label of the sheet. -/
def trioRuleMatrixOfX (s : String) : Option (List (List Nat)) := do
  let a ← parse s
  if a.isEmpty then none else some (trioRuleMatrixX a)

/-- The matrix of a label, `[]` when it does not parse. -/
def xOf (s : String) : List (List Nat) := (trioRuleMatrixOfX s).getD []

/-- **Every column is three rows deep with `z < 2`.** -/
theorem WF3_trioRuleMatrixX (alpha : Od) : WF3 (trioRuleMatrixX alpha) := WF3_toRows _

/-! ### The patch against `TrioRulesAll`: the branches it does not touch -/

section
variable (Mf : Od → Cols)

/-- The change is only in `placeUnitsX`, which the step on `α = ψ_{Ω_u}(X)` does not
call, so that step is `MstepAll`'s. -/
theorem MstepX_psi (alpha v : Od) (uX : Od × Od)
    (hv : lvlO alpha = some v) (hp : isPsiLevel alpha = some uX) :
    MstepX Mf alpha = MstepAll Mf alpha := by
  simp [MstepX, MstepAll, hv, hp]

/-- On `α = Ω_v` the step is `MstepAll`'s. -/
theorem MstepX_omega (alpha v : Od) (hv : lvlO alpha = some v)
    (hp : isPsiLevel alpha = none) (he : (alpha == [(.W v, 1)]) = true) :
    MstepX Mf alpha = MstepAll Mf alpha := by
  simp [MstepX, MstepAll, hv, hp, he]

end


/-! ### Where the changes cannot act -/

section
variable (Mf : Od → Cols)

/-- **Change 1** acts only in an uncountable regime. -/
theorem spentX_eq_spent (c : Ctx) (h : c.regime.bind lvlO = none) :
    spentX Mf c = spent Mf c := by
  simp [spentX, h]

/-- In a countable regime (`none`) no fix of this file or of Fix N fires. -/
theorem fixXNeeded_countable (s : CtxN) (h : s.c.regime = none) :
    fixXNeeded Mf s = false := by
  simp [fixXNeeded, fixNNeeded, fixGNeeded, fixMNeeded, h]

/-- **Fix G** never fires in a tower regime (there Fix N decides). -/
theorem fixGNeeded_tower (s : CtxN) (r : Od) (h : s.c.regime = some r)
    (ht : isTower r = true) : fixGNeeded Mf s = false := by
  unfold fixGNeeded
  rw [h]
  cases s.c.prev <;> simp [otherRegime, ht]

/-- **Fix M** never fires on a leaf whose level has no mark. -/
theorem fixMNeeded_plain (s : CtxN) (p : Od) (hp : s.c.prev = some p)
    (hm : (suffixOf Mf (chainBase p)).isEmpty = true) : fixMNeeded Mf s = false := by
  unfold fixMNeeded
  rw [hp]
  cases s.c.regime <;> simp [hm]

/-- So in a tower regime, on a leaf whose level has no mark, the patched test is
Fix N's. -/
theorem fixXNeeded_tower_plain (s : CtxN) (r p : Od) (h : s.c.regime = some r)
    (ht : isTower r = true) (hp : s.c.prev = some p)
    (hm : (suffixOf Mf (chainBase p)).isEmpty = true) :
    fixXNeeded Mf s = fixNNeeded Mf s := by
  simp [fixXNeeded, fixGNeeded_tower Mf s r h ht, fixMNeeded_plain Mf s p hp hm]

end

/-- **Change 4** never acts in a tower regime. -/
theorem liftLeaf_tower (s : CtxN) (r v : Od) (h : s.c.regime = some r)
    (ht : isTower r = true) : liftLeaf s v = none := by
  simp [liftLeaf, h, otherRegime, ht]

/-- **Change 4** never acts in a countable regime. -/
theorem liftLeaf_countable (s : CtxN) (v : Od) (h : s.c.regime = none) :
    liftLeaf s v = none := by
  simp [liftLeaf, h]

end Googology.Trans.BMS.TrioFixNonLastOther
