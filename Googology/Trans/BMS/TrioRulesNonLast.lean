import Googology.Trans.BMS.TrioRules2

/-!
# Fix N: a leaf with more after it, in an uncountable regime

`TrioRules2.lean` (rules 1–10 of
[koteitan/trio](https://github.com/koteitan/trio) with Fixes A–D) names the
level of a unit's leaf only at the end of the matrix: a final leaf gets its
upgrade (Fix B 3), a leaf with more after it gets nothing.  So under an
uncountable regime a leaf that is not the last column reads as its plain
row-1 value, and different levels collide:

* `Ω_{Ω_Ω}+Ω_{Ω_2}+1`, `Ω_{Ω_Ω}+Ω_{Ω+1}+1` and `Ω_{Ω_Ω}·2+1` get one matrix,
  which lies above `M(Ω_{Ω_Ω}·2)`;
* `Ω_Ω+Ω_2+1` and `Ω_Ω·2+1` get one matrix.

The matrix is the same because the continuation after the leaf is written the
same way.  BMS itself reads that plain continuation as the **top** level of the
leaf's row-1 value: the sheet's own rows `M(Ω_Ω·ω)` (row 4460) and
`M(Ω_{Ω_Ω}·ω)` (row 4748) expand to `M(Ω_Ω·ω)[n] = M(Ω_Ω·n + Ω_2)` and
`M(Ω_{Ω_Ω}·ω)[n] = M(Ω_{Ω_Ω}·n + Ω_{Ω+1})` (`TrioRulesNonLastSheet.lean`), whose leaves before
the last one are plain.  So the plain continuation must stay with the top level,
and every other level needs a different continuation.

Notation: `r` is the regime (the units are laid on `M(Ω_r)`); `tops(r) = [r, w, w', …]` with `r = Ω_w`, `w = Ω_{w'}`, … (the levels
whose leaf is the largest name of its row-1 value); `P₁(i)` is the row-1 parent
of column `i` (the nearest row-0 ancestor with a smaller row-1 value).

**Fix N.**  Let `r` be a tower `Ω_{Ω_{…_1}}` (so `r ∈ {Ω, Ω_Ω, Ω_{Ω_Ω}, …}`).
When the last leaf names a level `p ∉ tops(r)` whose `Ω`-chain ends in a level
without a mark (`1`, `2`, …, not `ω`), and another add unit or another digit
follows:

1. the leaf gets its upgrade now (Fix B 3), as if it were last;
2. a **lifted copy** is laid: the columns from `s₀ = P₁(leaf)` to the end, each
   one `x + 1`, and `y + 1` exactly when its row-1 ancestry reaches `s₀` (BMS
   ascension), with the final leaf one below its lifted value (the leaf is
   kept).  If `s₀` is the root of the previous lifted copy, the previous copy
   itself is lifted (`s₀` := its start);
3. after that copy: the level `p` becomes the cap (a later leaf naming `p` is
   top); a leaf naming `r` is one higher per copy; a leaf naming `p` takes the
   copy's final value when step 1 wrote no sub-unit; the first sub-unit of an
   upgrade, and a mark, are taken from the copy;
4. the next add unit continues from the last root; the next digit too, except
   when step 1 wrote a sub-unit — then the unit is laid again (anchor and root
   under the sub-unit's root, and its digits so far) and the digit continues on
   that root.

The lifted copy is what BMS writes itself: `blift` reproduces
`M(Ω_{Ω_Ω}+Ω_{Ω_ω})[1] = M(Ω_{Ω_Ω}+Ω_{Ω_2}) ++ (lifted copy)` exactly
(`TrioRulesNonLastSheet.lean`), and with the leaf kept it gives
`M(Ω_{Ω_Ω}+Ω_{Ω_2}+1)` below `M(Ω_{Ω_Ω}·2)`.

Fix N changes no label of the sheet: on all 813 rows and the 9 corrected labels
the new rules give the matrix of `TrioRules2.lean`.  The checks are in
`TrioRulesNonLastSheet.lean`; the explanation is in
[TRIO-NONLAST-LEAF.md](TRIO-NONLAST-LEAF.md).  All checks are `#guard`s: a
calibration, not a theorem.
-/

namespace Googology.Trans.BMS.TrioRulesNL

open Googology.Trans.BMS.TrioRules
open Googology.Trans.BMS.TrioRules2

/-! ### Row-1 parents and the lifted copy -/

/-- The proper row-0 ancestors of column `i`, nearest first. -/
def ancestors (par : Array (Option Nat)) : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, i =>
    match par.getD i none with
    | some p => p :: ancestors par n p
    | none => []

/-- The row-1 parent of each column (Python `_par1`). -/
def par1 (cs : Cols) : Array (Option Nat) :=
  let par := forest cs
  (Array.range cs.size).map fun i =>
    (ancestors par cs.size i).find? fun j => decide ((colAt cs j).y < (colAt cs i).y)

/-- Does the row-1 ancestry of `i` reach `s0` (walking while above `s0`)? -/
def reaches (p1 : Array (Option Nat)) (s0 : Nat) : Nat → Nat → Bool
  | 0, _ => false
  | n + 1, j =>
    if j == s0 then true
    else if j < s0 then false
    else match p1.getD j none with
      | some k => reaches p1 s0 n k
      | none => false

/-- **Fix N 2** (Python `blift`): the lifted copy of `cs[s0:]`; the final leaf
one below its lift. -/
def blift (cs : Cols) (s0 : Nat) : Cols :=
  let p1 := par1 cs
  let seg := ((List.range cs.size).filter (· ≥ s0)).toArray.map fun i =>
    let c := colAt cs i
    { c with x := c.x + 1, y := c.y + (if reaches p1 s0 (cs.size + 1) i then 1 else 0) }
  setLastY seg ((lastC seg).y - 1)

/-- The last sub-unit `(c,L,1)(c+1,L,1)(c+2,y2,0)` inside `cs[a:b]`, any `L`. -/
def findSubIn (cs : Cols) (a b : Nat) (y2 : Int) : Option Cols :=
  ((List.range cs.size).reverse.find? fun i =>
    let c := colAt cs i
    a ≤ i && i + 3 ≤ b && c.z &&
      colAt cs (i + 1) == ⟨c.x + 1, c.y, true⟩ && colAt cs (i + 2) == ⟨c.x + 2, y2, false⟩).map
    fun i => cs.extract i (i + 3)

/-- `v, w, w', …` while `v = Ω_w`, `w = Ω_{w'}`, … -/
def omChain : Nat → Od → List Od
  | 0, _ => []
  | n + 1, v => v :: match omArg v with
    | some w => omChain n w
    | none => []

/-- The end of the `Ω`-chain of `v`. -/
def chainBase (v : Od) : Od := (omChain fuel v).getLast?.getD v

/-! ### The state -/

/-- What Fix N remembers across the build. -/
structure NState where
  cap : Option Od := none
  fst : Option Nat := none
  fend : Nat := 0
  fcount : Nat := 0
  fs0 : Option Nat := none
  capy : Option Int := none

/-- The builder's state with Fix N's. -/
structure CtxN where
  c : Ctx
  n : NState := {}

/-- Run a step of `TrioRules` on the inner state. -/
def liftC {α : Type} (act : StateM Ctx α) : StateM CtxN α := fun s =>
  let r := act.run s.c
  (r.1, { s with c := r.2 })

section
variable (Mf : Od → Cols)

/-- **Fix N 3** (Python `leaf_name` over `leaf_name0`): Fix B's leaf name, with
the regime one higher per lifted copy and the cap named by the copy's leaf. -/
def leafNameNF : Nat → CtxN → Od → Option Int
  | 0, _, _ => none
  | n + 1, s, v =>
    let base : Option Int :=
      match s.c.regime with
      | none => none
      | some r =>
        let unc := (lvlO r).isSome
        match omArg v with
        | some w =>
          if unc then some ((leafNameNF n s w).getD (leafY Mf w) + 1)
          else leafNameF.rest Mf s.c v r unc
        | none => leafNameF.rest Mf s.c v r unc
    let isR : Bool := match s.c.regime with
      | some r => (lvlO r).isSome && cmpOrd v r == .eq
      | none => false
    let isCap : Bool := match s.n.cap with
      | some p => cmpOrd v p == .eq
      | none => false
    if isR && s.n.cap.isSome then base.map (· + (s.n.fcount : Int))
    else match s.n.capy with
      | some y => if isCap then some y else base
      | none => base

/-- `N(v)`. -/
def leafNameN (s : CtxN) (v : Od) : Option Int := leafNameNF Mf fuel s v

/-- `N(v)`, falling back to `leafY v`. -/
def leafNameOrYN (s : CtxN) (v : Od) : Int := (leafNameN Mf s v).getD (leafY Mf v)

/-- Fix B 3 with Fix N 3: while `t = Ω_w`, append a sub-unit whose leaf names
`w`; after a lifted copy the first one is the copy's own.  Returns the columns,
the `t` left, and whether a sub-unit was written. -/
def upgradeNF : Nat → CtxN → Cols → Od → Bool → Cols × Od × Bool
  | 0, _, cs, t, used => (cs, t, used)
  | n + 1, s, cs, t, used =>
    match s.c.regime, omArg t with
    | some r, some w =>
      if (lvlO r).isSome && !(lastC cs).z then
        let y2 := leafNameOrYN Mf s w
        let inCopy : Option Cols :=
          if used then none else
          match s.n.fst with
          | some a => findSubIn cs a s.n.fend y2
          | none => none
        match inCopy.orElse fun _ => findSub cs (lastC cs).y y2 with
        | some sub => upgradeNF n s (cs ++ sub) w true
        | none => (cs, t, used)
      else (cs, t, used)
    | _, _ => (cs, t, used)

/-- **Fix N 3** (Python `suffix_in`): the mark naming `v` inside the lifted copy
`cs[a:b]`, one level above where the leaf just written would put it. -/
def suffixIn (cs : Cols) (v : Od) (a b : Nat) : Option Cols :=
  if (lastC cs).z then none else
  let suf := suffixOf Mf v
  let n := suf.size
  let k : Int := max ((lastC cs).y - leafY Mf v) 0 + 1
  let pat := suf.toList.map fun c => (c.y + k, c.z)
  let dx := suf.toList.map fun c => c.x - (colAt suf 0).x
  ((List.range cs.size).reverse.find? fun i =>
    a ≤ i && i + n ≤ b &&
      (let seg := cs.extract i (i + n)
       seg.toList.map (fun c => (c.y, c.z)) == pat &&
         seg.toList.map (fun c => c.x - (colAt seg 0).x) == dx) &&
      (i == 0 || !(colAt cs (i - 1)).z || (colAt cs (i - 1)).x != (colAt cs i).x - 1)).map
    fun i => cs.extract i (i + n)

/-- Python `fixF_needed`: the last leaf names a level that is not a top, with
no mark in its chain, under a regime that is a tower over `1`. -/
def fixNNeeded (s : CtxN) : Bool :=
  match s.c.regime, s.c.prev with
  | some r, some p =>
    (lvlO r).isSome && (omArg r).isSome && cmpOrd (chainBase r) one == .eq &&
      !(lastC s.c.cols).z && (suffixOf Mf (chainBase p)).isEmpty &&
      !((omChain fuel r).any fun t => cmpOrd p t == .eq) &&
      !(match s.n.cap with | some q => cmpOrd p q == .eq | none => false)
  | _, _ => false

/-- **Fix N 1–2** (Python `fixF`): the upgrade, then the lifted copy with the
leaf kept.  Returns whether a sub-unit was written. -/
def fixN : StateM CtxN Bool := do
  let s ← get
  let p := s.c.prev.getD []
  let u := upgradeNF Mf fuel s s.c.cols p false
  let cols := u.1
  let used := u.2.2
  let s0a := ((par1 cols).getD (cols.size - 1) none).getD 0
  let s0 := match s.n.fst, s.n.fs0 with
    | some f, some q => if q == s0a then f else s0a
    | _, _ => s0a
  let seg := blift cols s0
  let cols' := cols ++ seg
  set ({ c := { s.c with cols := cols', st := cols.size, prev := none },
         n := { s.n with cap := s.c.prev, fs0 := some s0, fst := some cols.size,
                         fend := cols'.size, fcount := s.n.fcount + 1,
                         capy := if used then none else some (lastC cols').y } } : CtxN)
  pure used

/-- The OT embedding `blockF2` with Fix N's leaf name. -/
def blockN : Nat → Od → Int → Int → Bool → Option Od → Int → StateM CtxN Unit
  | 0, _, _, _, _, _, _ => pure ()
  | n + 1, gamma, x0, d0, arg, plvl, py => do
    let mut x := x0
    let mut d := d0
    for ec in gamma do
      let e := ec.1
      let subArg := headIsPsi (ato e)
      for _ in [0:ec.2] do
        if !(← get).c.fresh && spent Mf (← get).c then
          liftC (laySt none)
          let l := lastC (← get).c.cols
          x := l.x
          d := l.y
        let s ← get
        let v := lvl e
        let run : Cols :=
          match v with
          | none => #[⟨x, 0, false⟩]
          | some v =>
            if !arg && (match plvl with | some p => cmpOrd v p == .eq | none => false) then
              #[⟨x, py, false⟩]
            else if !arg then
              match leafNameN Mf s v with
              | some y => #[⟨x, y, false⟩]
              | none => writeLevel Mf v x d arg [s.c.cols]
            else writeLevel Mf v x d arg [s.c.cols]
        modify fun s => { s with c := { s.c with cols := s.c.cols ++ run } }
        let sub := strip e
        let mut nx := (lastC run).x + 1
        let mut nd := (lastC run).y
        modify fun s => { s with c := { s.c with prev := if arg then none else v } }
        if !sub.isEmpty && !(← get).c.fresh && spent Mf (← get).c then
          liftC (laySt none)
          let l := lastC (← get).c.cols
          nx := l.x + 1
          nd := l.y
        blockN n sub nx nd subArg v (lastC run).y
        modify fun s => { s with c := { s.c with prev := tailBlock (ato e) arg } }

/-- **Fix N 4** (Python `restate`): the unit laid again under the sub-unit's
root, with the digits so far; returns `(level, root x)`. -/
def restate (digits : List Ex) : StateM CtxN (Int × Int) := do
  let lr := lastRootPlain (← get).c.cols
  let y := lr.1 + 1
  let x0 := lr.2 + 2
  let two : Cols := #[⟨lr.2 + 1, lr.1, false⟩, ⟨x0, y, true⟩]
  modify fun s => { s with c := { s.c with cols := s.c.cols ++ two, level := y - 1 } }
  for e in digits do
    modify fun s => { s with c := { s.c with cols := s.c.cols.push ⟨x0 + 1, y, true⟩ } }
    blockN Mf fuel (ato e) (x0 + 2) (y - 1) false none 0
  pure (y, x0)

/-- `placeUnits2` with Fix N. -/
def placeUnitsN (cols : Cols) (alpha : Od) (level0 rootX0 : Int) (regime : Option Od) :
    CtxN :=
  let act : StateM CtxN Unit := do
    let mut level := level0
    let mut rootX := rootX0
    let mut skip := 0
    if (regime.bind lvlO).isSome then
      let k ← liftC (copyStorey (rootX + 1))
      skip := if k == 1 then 1 else 0
      let lr := lastRootPlain (← get).c.cols
      level := lr.1
      rootX := lr.2
      -- Fix C: the copy is the first unit's first digit; lay its other digits.
      if skip == 1 then
        match (units alpha).head? with
        | some b0 =>
          let alld := units (predBeta (ato b0))
          let rest := alld.drop 1
          let mut j := 0
          for e in rest do
            if fixNNeeded Mf (← get) then
              if ← fixN Mf then
                let lr ← restate Mf (alld.take (j + 1))
                level := lr.1
                rootX := lr.2
              else
                let lr := lastRootPlain (← get).c.cols
                level := lr.1
                rootX := lr.2
            modify fun s => { s with c := { s.c with cols := s.c.cols.push ⟨rootX + 1, level, true⟩ } }
            blockN Mf fuel (ato e) (rootX + 2) (level - 1) false none 0
            j := j + 1
          if !rest.isEmpty then
            modify fun s => { s with c := { s.c with prev := unitTailLevel (ato b0) } }
        | none => pure ()
    let mut prev0 := false
    let mut first := true
    for b in (units alpha).drop skip do
      let beta := ato b
      modify fun s => { s with c := { s.c with fresh := false } }
      let laid := !first && spent Mf (← get).c
      if laid then
        liftC (laySt none)
        let lr := lastRootPlain (← get).c.cols
        level := lr.1
        rootX := lr.2
        prev0 := false
      else if (!first || skip == 1) && fixNNeeded Mf (← get) then
        let _ ← fixN Mf
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
          if i != 0 && !(← get).c.fresh && spent Mf (← get).c then
            liftC (laySt none)
            let lr := lastRootPlain (← get).c.cols
            y := lr.1
            x0 := lr.2
            modify fun s => { s with c := { s.c with level := lr.1 - 1 } }
          else if i != 0 && fixNNeeded Mf (← get) then
            if ← fixN Mf then
              let lr ← restate Mf (digits.take i)
              y := lr.1
              x0 := lr.2
            else
              let lr := lastRootPlain (← get).c.cols
              y := lr.1
              x0 := lr.2
              modify fun s => { s with c := { s.c with level := lr.1 - 1 } }
          modify fun s => { s with c := { s.c with cols := s.c.cols.push ⟨x0 + 1, y, true⟩ } }
          blockN Mf fuel (ato e) (x0 + 2) (y - 1) false none 0
          -- Fix D: a digit too deep for a countable regime, with digits after it.
          match tailBlock (ato e) false, regime with
          | some p, some r =>
            if i + 1 < digits.length && (lvlO r).isNone && cmpOrd p r == .lt &&
                decide (leafY Mf p > leafY Mf r) then
              modify fun s => { s with c := { s.c with cols := setLastY s.c.cols (leafY Mf r) } }
              for k in [1:(leafY Mf p - leafY Mf r).toNat + 1] do
                liftC (laySt (some (leafY Mf r + k)))
              liftC (laySt none)
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
              liftC (laySt (some (leafY Mf r + k)))
            let lr := lastRootPlain (← get).c.cols
            level := lr.1
            rootX := lr.2
            prev0 := false
      | _, _ => pure ()
      first := false
  (act.run { c := { cols := cols, regime := regime } }).2

/-- The upgrade at the end: Fix B 3 (with Fix N 3), then the mark — from the
lifted copy if there is one, else by `appendSuffix`. -/
def finishN (alpha : Od) (s : CtxN) : Cols :=
  match tailLevel alpha with
  | some t =>
    let u := upgradeNF Mf fuel s s.c.cols t false
    let inCopy : Option Cols :=
      match s.n.fst with
      | some a => if (suffixOf Mf u.2.1).isEmpty then none else suffixIn Mf u.1 u.2.1 a s.n.fend
      | none => none
    match inCopy with
    | some seg => u.1 ++ seg
    | none => appendSuffix Mf u.1 u.2.1 s.c.storeys none
  | none => s.c.cols

/-- One step of the builder with Fix N. -/
def MstepN (alpha : Od) : Cols :=
  match lvlO alpha with
  | none => finishN Mf alpha (placeUnitsN Mf #[] alpha 0 (-1) none)
  | some v =>
    match isPsiLevel alpha with
    | some uX => MpsiLevel2 Mf uX.1 uX.2
    | none =>
      if alpha == [(.W v, 1)] then MOmega2 Mf v
      else
        let base := MOmega2 Mf v
        let ya := lastRoot base
        finishN Mf alpha (placeUnitsN Mf base alpha ya.1 (ya.2 - 1) (some v))

end

/-- The builder with Fix N, with fuel. -/
def MfuelN : Nat → Od → Cols
  | 0, _ => #[]
  | n + 1, a => MstepN (MfuelN n) a

/-- `α ↦` the columns of `ψ_0(Ω_α)`, by the rules with Fix N. -/
def MN (alpha : Od) : Cols := MfuelN fuel alpha

/-- **The trio matrix of `ψ_0(Ω_α)` by the rules with Fix N.** -/
def trioRuleMatrixN (alpha : Od) : List (List Nat) := toRows (MN alpha)

/-- The matrix for a label of the sheet. -/
def trioRuleMatrixOfN (s : String) : Option (List (List Nat)) := do
  let a ← parse s
  if a.isEmpty then none else some (trioRuleMatrixN a)

/-- **Every column is three rows deep with `z < 2`.** -/
theorem WF3_trioRuleMatrixN (alpha : Od) : WF3 (trioRuleMatrixN alpha) := WF3_toRows _

end Googology.Trans.BMS.TrioRulesNL
