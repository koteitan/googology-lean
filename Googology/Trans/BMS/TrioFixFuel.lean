import Googology.Trans.BMS.TrioRulesAll
import Googology.Trans.BMS.TrioRulesFuel

/-!
# Fix Fuel: the merged rules with a fuel that grows with the term

`TrioRulesAll.lean` (rules 1–10 of [koteitan/trio](https://github.com/koteitan/trio)
with Fixes A–E and N) runs every recursion of the program on one fixed fuel,
`TrioRules.fuel = 200`.  When a recursion needs more than `200` steps it stops
early, and the output is wrong: `TrioTree.lean` shows two different standard
terms, `ψ_0(Ω + T_205)` and `ψ_0(Ω + T_206)` (`T_n` a tower of `n` copies of
`ψ_0`, nesting depths `206` and `207`), that get the same matrix.

## The change (for the lead, to merge)

**Only the fuel changes; no rule changes.**  Every definition of
`TrioRulesAll.lean` and of the files it builds on that reads `fuel` is copied
here with a parameter `F : Nat` in place of `fuel` (`200`):

| here, with `F` | the fuel-200 original |
|---|---|
| `TrioFuel.lvl F`, `lvlO F`, `cmpOrd F`, `strip F`, `tailBlock F`, `unitTailLevel F`, `tailLevel F`, `isPsiLevel F`, `copyStorey F`, `spent F`, `appendSuffix F`, `ofTerm F` (from `TrioRulesFuel.lean`) | the `TrioRules` functions of the same name |
| `MpsiLevel2`, `leafRest` | `TrioRules2.MpsiLevel2`, `TrioRules2.leafNameF.rest` |
| `levelOmega`, `MpsiLevel3` | `TrioRules3.levelOmega`, `TrioRules3.MpsiLevel3` |
| `chainBase`, `leafNameNF`, `leafNameN`, `leafNameOrYN`, `upgradeNF`, `fixNNeeded`, `fixN`, `blockN`, `restate`, `placeUnitsN`, `finishN` | the `TrioRulesNL` functions of the same name |
| `MstepAll`, `MfuelAll`, `MF` | `TrioRulesAll.MstepAll`, `MfuelAll`, `MAll` |

The bodies are the originals with `fuel` replaced by `F` and each fuel-reading
callee replaced by its `F` copy; nothing else is edited.  Two fuel-200 reads stay,
neither of which depends on the input's depth: `TrioRules.lvl` inside
`TrioRules.cmpAtomWith` (only on atoms, one step; `lvl_atom`) and `TrioRules.cmpExp`
inside `TrioRules.add` (only on the constants `ω + 1`, `Ω + 1`).  The constants
`omega`, `omegaOnePlusOne`, `omOmTwo`, `headOmegaOmega` of `TrioRules3` and
the fuel-free pieces (`MOmega2`, `writeLevel`, `blift`, `suffixIn`, …) are
reused as they are.

The map then takes its fuel from the term:

  `fuelOf α = max 200 (odDep α)`,   `MD α = MF (fuelOf α) α`,

`odDep` the nesting depth of the normal form (`odDep (ω^{e₁}·c₁ + ⋯) = max exDep eᵢ`,
`exDep (ω^a) = odDep a + 1`, `exDep (Ω_v) = odDep v + 1`,
`exDep (ψ_v(X)) = max (odDep v) (odDep X) + 1`).  Terms of the notation `Term`
use one fuel for the reading and the builder:

  `fuelT α = max 200 (tDep α)`,
  `trioMatrixLD α = toRows (MF (fuelT α) (ofTerm (fuelT α) α))`,

`tDep` the nesting depth of the term, subscripts included.  (Coefficients are
not counted: fuel `200` is enough on labels with coefficient `300`, checked
while writing this file.)  The `max 200` makes the patched map **equal** to the
old one up to depth `200`.

**The same patch in one line, for the lead:** replace `fuel` by a parameter `F`
in every definition that reads it (the table above), then call the builder with
`F = max 200 (depth of α)`.

## What is proved

* `MF_200 : MF 200 = TrioRulesAll.MAll`: at fuel `200` the copies are the
  original program (every `*_200` lemma below is one of the copies).
* `MD_eq_MAll : odDep α ≤ 200 → MD α = MAll α`, and the same for the matrices
  (`trioRuleMatrixD_eq`), for labels (`trioRuleMatrixOfD_eq`) and for terms
  (`trioMatrixLD_eq : tDep α ≤ 200 → trioMatrixLD α = trioMatrixLAll α`).
* `WF3_trioRuleMatrixD`: every column is three rows deep with `z < 2`.
* In `TrioFixFuelE0.lean`: below `ε₀` the patched map is `trioMatrix` at every
  depth, so it keeps the order and is injective there
  (`trioMatrixLD_eq_trioMatrix`, `trioMatrixLD_lt_iff`, `trioMatrixLD_injective`),
  and the merged step is rules 1–10's step on every countable `α`
  (`MstepAll_countable`, `MstepAll_countable_200`).

## What is checked, not proved (`TrioFixFuelSheet.lean`)

All checks of `TrioRulesAllSheet.lean` for the patched map, with the same
numbers; the depth-206/207 collision gone (and the patched map equal to the
fuel-free `TrioTree.trioE` on that family up to depth `301`); an uncountable
family past depth `200`; fuel `odDep α` giving the same matrix as more fuel on
every label.  That `fuelOf α` is enough for **every** `α` above `ε₀` (so that
more fuel changes nothing) is not proved.
-/

namespace Googology.Trans.BMS.TrioFixFuel

open Googology.Notation.ExBuchholz
open Googology.Notation.ExBuchholz.Term
open Googology.Trans.BMS.TrioRules (Ex Od ato nat one wpow Col Cols colAt lastC setLastY forest
  isLevel lastRootPlain lastRoot Ctx laySt leafY suffixOf writeLevel units predBeta headIsPsi
  toRows parse fuel WF3_toRows)
open Googology.Trans.BMS.TrioFuel (lvl lvlO cmpOrd strip tailBlock unitTailLevel tailLevel
  isPsiLevel copyStorey spent appendSuffix)
open Googology.Trans.BMS.TrioRules2 (omArg findSub MOmega2)
open Googology.Trans.BMS.TrioRules3 (omega omegaOnePlusOne omOmTwo headOmegaOmega)
open Googology.Trans.BMS.TrioRulesNL (par1 blift findSubIn omChain NState CtxN suffixIn)

/-! ### The size of a normal form -/

mutual
/-- The nesting depth of an exponent. -/
def exDep : Ex → Nat
  | .o a => odDep a + 1
  | .W v => odDep v + 1
  | .psi v X => max (odDep v) (odDep X) + 1
/-- The nesting depth of a normal form: the largest depth of its exponents. -/
def odDep : List (Ex × Nat) → Nat
  | [] => 0
  | p :: t => max (exDep p.1) (odDep t)
end

/-- **The fuel of `α`**: `200`, or the depth of `α` when it is larger. -/
def fuelOf (alpha : Od) : Nat := max fuel (odDep alpha)

/-- The nesting depth of a term, subscripts included:
`tDep (ψ_a(b) + t) = max (max (tDep a) (tDep b) + 1) (tDep t)`. -/
def tDep : Term → Nat
  | nil => 0
  | cons a b t => max (max (tDep a) (tDep b) + 1) (tDep t)

/-- The fuel of a term: `200`, or its depth when it is larger. -/
def fuelT (α : Term) : Nat := max fuel (tDep α)

/-! ### The program with fuel `F` -/

section
variable (F : Nat)

section
variable (Mf : Od → Cols)

/-- `TrioRules2.MpsiLevel2` with fuel `F`. -/
def MpsiLevel2 (u X : Od) : Cols :=
  let base := MOmega2 Mf u
  let y0 := (lastC base).y
  let cols := setLastY base (y0 - 1)
  let x := (lastC base).x + 1
  match lvlO F X with
  | none => #[]
  | some w =>
    if cmpOrd F w u == .eq then cols.push ⟨x, y0, false⟩
    else appendSuffix F Mf (cols ++ writeLevel Mf w x (y0 - 1) true [Mf u, cols]) w 0 none

/-- `TrioRules2.leafNameF.rest` with fuel `F`. -/
def leafRest (c : Ctx) (v r : Od) (unc : Bool) : Option Int :=
  if c.storeys != 0 && cmpOrd F v r == .eq then
    some (if !unc then c.level else c.leafLevel.getD 0)
  else if unc && leafY Mf v == leafY Mf r && cmpOrd F v one != .eq &&
      !(match omArg r with | some u => cmpOrd F u v == .eq | none => false) then
    some (leafY Mf v + 1)
  else none

end

/-- `TrioRules3.levelOmega` with fuel `F`. -/
def levelOmega (w : Od) : Bool :=
  cmpOrd F w [(.W omega, 1)] != .lt && cmpOrd F w [(.W (TrioRules.add omega one), 1)] == .lt

/-- `TrioRulesNL.chainBase` with fuel `F`. -/
def chainBase (v : Od) : Od := (omChain F v).getLast?.getD v

section
variable (Mf : Od → Cols)

/-- `TrioRules3.MpsiLevel3` with fuel `F`. -/
def MpsiLevel3 (u X : Od) : Cols :=
  let old := MpsiLevel2 F Mf u X
  if cmpOrd F u omegaOnePlusOne != .eq then old else
  match lvlO F X with
  | none => old
  | some w =>
    if !levelOmega F w then old else
    let m := Mf w
    if m.extract 0 5 != headOmegaOmega then old else
    MpsiLevel2 F Mf u omOmTwo ++
      (m.extract 4 m.size).map fun c => { c with x := c.x + 1, y := c.y + 1 }

/-- `TrioRulesNL.leafNameNF` with fuel `F` in the pieces it calls. -/
def leafNameNF : Nat → CtxN → Od → Option Int
  | 0, _, _ => none
  | n + 1, s, v =>
    let base : Option Int :=
      match s.c.regime with
      | none => none
      | some r =>
        let unc := (lvlO F r).isSome
        match omArg v with
        | some w =>
          if unc then some ((leafNameNF n s w).getD (leafY Mf w) + 1)
          else leafRest F Mf s.c v r unc
        | none => leafRest F Mf s.c v r unc
    let isR : Bool := match s.c.regime with
      | some r => (lvlO F r).isSome && cmpOrd F v r == .eq
      | none => false
    let isCap : Bool := match s.n.cap with
      | some p => cmpOrd F v p == .eq
      | none => false
    if isR && s.n.cap.isSome then base.map (· + (s.n.fcount : Int))
    else match s.n.capy with
      | some y => if isCap then some y else base
      | none => base

/-- `TrioRulesNL.leafNameN` with fuel `F`. -/
def leafNameN (s : CtxN) (v : Od) : Option Int := leafNameNF F Mf F s v

/-- `TrioRulesNL.leafNameOrYN` with fuel `F`. -/
def leafNameOrYN (s : CtxN) (v : Od) : Int := (leafNameN F Mf s v).getD (leafY Mf v)

/-- `TrioRulesNL.upgradeNF` with fuel `F` in the pieces it calls. -/
def upgradeNF : Nat → CtxN → Cols → Od → Bool → Cols × Od × Bool
  | 0, _, cs, t, used => (cs, t, used)
  | n + 1, s, cs, t, used =>
    match s.c.regime, omArg t with
    | some r, some w =>
      if (lvlO F r).isSome && !(lastC cs).z then
        let y2 := leafNameOrYN F Mf s w
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

/-- `TrioRulesNL.fixNNeeded` with fuel `F`. -/
def fixNNeeded (s : CtxN) : Bool :=
  match s.c.regime, s.c.prev with
  | some r, some p =>
    (lvlO F r).isSome && (omArg r).isSome && cmpOrd F (chainBase F r) one == .eq &&
      !(lastC s.c.cols).z && (suffixOf Mf (chainBase F p)).isEmpty &&
      !((omChain F r).any fun t => cmpOrd F p t == .eq) &&
      !(match s.n.cap with | some q => cmpOrd F p q == .eq | none => false)
  | _, _ => false

/-- `TrioRulesNL.fixN` with fuel `F`. -/
def fixN : StateM CtxN Bool := do
  let s ← get
  let p := s.c.prev.getD []
  let u := upgradeNF F Mf F s s.c.cols p false
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

/-- `TrioRulesNL.blockN` with fuel `F` in the pieces it calls. -/
def blockN : Nat → Od → Int → Int → Bool → Option Od → Int → StateM CtxN Unit
  | 0, _, _, _, _, _, _ => pure ()
  | n + 1, gamma, x0, d0, arg, plvl, py => do
    let mut x := x0
    let mut d := d0
    for ec in gamma do
      let e := ec.1
      let subArg := headIsPsi (ato e)
      for _ in [0:ec.2] do
        if !(← get).c.fresh && spent F Mf (← get).c then
          TrioRulesNL.liftC (laySt none)
          let l := lastC (← get).c.cols
          x := l.x
          d := l.y
        let s ← get
        let v := lvl F e
        let run : Cols :=
          match v with
          | none => #[⟨x, 0, false⟩]
          | some v =>
            if !arg && (match plvl with | some p => cmpOrd F v p == .eq | none => false) then
              #[⟨x, py, false⟩]
            else if !arg then
              match leafNameN F Mf s v with
              | some y => #[⟨x, y, false⟩]
              | none => writeLevel Mf v x d arg [s.c.cols]
            else writeLevel Mf v x d arg [s.c.cols]
        modify fun s => { s with c := { s.c with cols := s.c.cols ++ run } }
        let sub := strip F e
        let mut nx := (lastC run).x + 1
        let mut nd := (lastC run).y
        modify fun s => { s with c := { s.c with prev := if arg then none else v } }
        if !sub.isEmpty && !(← get).c.fresh && spent F Mf (← get).c then
          TrioRulesNL.liftC (laySt none)
          let l := lastC (← get).c.cols
          nx := l.x + 1
          nd := l.y
        blockN n sub nx nd subArg v (lastC run).y
        modify fun s => { s with c := { s.c with prev := tailBlock F (ato e) arg } }

/-- `TrioRulesNL.restate` with fuel `F`. -/
def restate (digits : List Ex) : StateM CtxN (Int × Int) := do
  let lr := lastRootPlain (← get).c.cols
  let y := lr.1 + 1
  let x0 := lr.2 + 2
  let two : Cols := #[⟨lr.2 + 1, lr.1, false⟩, ⟨x0, y, true⟩]
  modify fun s => { s with c := { s.c with cols := s.c.cols ++ two, level := y - 1 } }
  for e in digits do
    modify fun s => { s with c := { s.c with cols := s.c.cols.push ⟨x0 + 1, y, true⟩ } }
    blockN F Mf F (ato e) (x0 + 2) (y - 1) false none 0
  pure (y, x0)

/-- `TrioRulesNL.placeUnitsN` with fuel `F`. -/
def placeUnitsN (cols : Cols) (alpha : Od) (level0 rootX0 : Int) (regime : Option Od) :
    CtxN :=
  let act : StateM CtxN Unit := do
    let mut level := level0
    let mut rootX := rootX0
    let mut skip := 0
    if (regime.bind (lvlO F)).isSome then
      let k ← TrioRulesNL.liftC (copyStorey F (rootX + 1))
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
            if fixNNeeded F Mf (← get) then
              if ← fixN F Mf then
                let lr ← restate F Mf (alld.take (j + 1))
                level := lr.1
                rootX := lr.2
              else
                let lr := lastRootPlain (← get).c.cols
                level := lr.1
                rootX := lr.2
            modify fun s => { s with c := { s.c with cols := s.c.cols.push ⟨rootX + 1, level, true⟩ } }
            blockN F Mf F (ato e) (rootX + 2) (level - 1) false none 0
            j := j + 1
          if !rest.isEmpty then
            modify fun s => { s with c := { s.c with prev := unitTailLevel F (ato b0) } }
        | none => pure ()
    let mut prev0 := false
    let mut first := true
    for b in (units alpha).drop skip do
      let beta := ato b
      modify fun s => { s with c := { s.c with fresh := false } }
      let laid := !first && spent F Mf (← get).c
      if laid then
        TrioRulesNL.liftC (laySt none)
        let lr := lastRootPlain (← get).c.cols
        level := lr.1
        rootX := lr.2
        prev0 := false
      else if (!first || skip == 1) && fixNNeeded F Mf (← get) then
        let _ ← fixN F Mf
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
          if i != 0 && !(← get).c.fresh && spent F Mf (← get).c then
            TrioRulesNL.liftC (laySt none)
            let lr := lastRootPlain (← get).c.cols
            y := lr.1
            x0 := lr.2
            modify fun s => { s with c := { s.c with level := lr.1 - 1 } }
          else if i != 0 && fixNNeeded F Mf (← get) then
            if ← fixN F Mf then
              let lr ← restate F Mf (digits.take i)
              y := lr.1
              x0 := lr.2
            else
              let lr := lastRootPlain (← get).c.cols
              y := lr.1
              x0 := lr.2
              modify fun s => { s with c := { s.c with level := lr.1 - 1 } }
          modify fun s => { s with c := { s.c with cols := s.c.cols.push ⟨x0 + 1, y, true⟩ } }
          blockN F Mf F (ato e) (x0 + 2) (y - 1) false none 0
          -- Fix D: a digit too deep for a countable regime, with digits after it.
          match tailBlock F (ato e) false, regime with
          | some p, some r =>
            if i + 1 < digits.length && (lvlO F r).isNone && cmpOrd F p r == .lt &&
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
        modify fun s => { s with c := { s.c with prev := unitTailLevel F beta } }
      match (← get).c.prev, regime with
      | some p, some r =>
        if (lvlO F r).isNone && !laid && cmpOrd F p r == .lt then
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

/-- `TrioRulesNL.finishN` with fuel `F`. -/
def finishN (alpha : Od) (s : CtxN) : Cols :=
  match tailLevel F alpha with
  | some t =>
    let u := upgradeNF F Mf F s s.c.cols t false
    let inCopy : Option Cols :=
      match s.n.fst with
      | some a => if (suffixOf Mf u.2.1).isEmpty then none else suffixIn Mf u.1 u.2.1 a s.n.fend
      | none => none
    match inCopy with
    | some seg => u.1 ++ seg
    | none => appendSuffix F Mf u.1 u.2.1 s.c.storeys none
  | none => s.c.cols

/-- `TrioRulesAll.MstepAll` with fuel `F`. -/
def MstepAll (alpha : Od) : Cols :=
  match lvlO F alpha with
  | none => finishN F Mf alpha (placeUnitsN F Mf #[] alpha 0 (-1) none)
  | some v =>
    match isPsiLevel F alpha with
    | some uX => MpsiLevel3 F Mf uX.1 uX.2
    | none =>
      if alpha == [(.W v, 1)] then MOmega2 Mf v
      else
        let base := MOmega2 Mf v
        let ya := lastRoot base
        finishN F Mf alpha (placeUnitsN F Mf base alpha ya.1 (ya.2 - 1) (some v))

end

/-- `TrioRulesAll.MfuelAll` with fuel `F` in every step. -/
def MfuelAll : Nat → Od → Cols
  | 0, _ => #[]
  | n + 1, a => MstepAll F (MfuelAll n) a

/-- `TrioRulesAll.MAll` with fuel `F`. -/
def MF (alpha : Od) : Cols := MfuelAll F F alpha

end

/-! ### The map with the fuel of the term -/

/-- **`α ↦` the columns of `ψ_0(Ω_α)`, by the merged rules with fuel `fuelOf α`.** -/
def MD (alpha : Od) : Cols := MF (fuelOf alpha) alpha

/-- **The trio matrix of `ψ_0(Ω_α)`, merged rules, fuel from the term.** -/
def trioRuleMatrixD (alpha : Od) : List (List Nat) := toRows (MD alpha)

/-- The matrix for a label of the sheet. -/
def trioRuleMatrixOfD (s : String) : Option (List (List Nat)) := do
  let a ← parse s
  if a.isEmpty then none else some (trioRuleMatrixD a)

/-- The matrix of a label, `[]` when it does not parse. -/
def fxOf (s : String) : List (List Nat) := (trioRuleMatrixOfD s).getD []

/-- A term read as a normal form, with fuel `fuelT α`. -/
def ofTermD (α : Term) : Od := TrioFuel.ofTerm (fuelT α) α

/-- **The map on terms**: the merged rules on `ofTermD α`, both with fuel `fuelT α`. -/
def trioMatrixLD (α : Term) : List (List Nat) := toRows (MF (fuelT α) (ofTermD α))

/-- The merged rules at fuel `200` on terms (`TrioRules.ofTerm`, `MAll`): the map
whose collision at depths 206/207 this file removes. -/
def trioMatrixLAll (α : Term) : List (List Nat) :=
  TrioRulesAll.trioRuleMatrixAll (TrioRules.ofTerm α)

/-- **Every column is three rows deep with `z < 2`.** -/
theorem WF3_trioRuleMatrixD (alpha : Od) : WF3 (trioRuleMatrixD alpha) := WF3_toRows _

/-! ### At fuel `200` the copies are the original program -/

open Googology.Trans.BMS.TrioFuel (lvlO_200 cmpOrd_200 appendSuffix_200 strip_200 tailBlock_200
  lvl_200 spent_200 copyStorey_200 unitTailLevel_200 tailLevel_200 isPsiLevel_200 ofTerm_200)

theorem MpsiLevel2_200 : MpsiLevel2 200 = TrioRules2.MpsiLevel2 := by
  funext Mf u X
  unfold MpsiLevel2 TrioRules2.MpsiLevel2
  rw [lvlO_200, cmpOrd_200, appendSuffix_200]
  rfl

theorem leafRest_200 : leafRest 200 = TrioRules2.leafNameF.rest := by
  funext Mf c v r unc
  unfold leafRest TrioRules2.leafNameF.rest
  rw [cmpOrd_200]
  rfl

theorem levelOmega_200 : levelOmega 200 = TrioRules3.levelOmega := by
  funext w
  unfold levelOmega TrioRules3.levelOmega
  rw [cmpOrd_200]

theorem chainBase_200 : chainBase 200 = TrioRulesNL.chainBase := rfl

theorem MpsiLevel3_200 : MpsiLevel3 200 = TrioRules3.MpsiLevel3 := by
  funext Mf u X
  unfold MpsiLevel3 TrioRules3.MpsiLevel3
  rw [MpsiLevel2_200, cmpOrd_200, lvlO_200, levelOmega_200]
  rfl

theorem leafNameNF_200 (Mf : Od → Cols) :
    ∀ n, leafNameNF 200 Mf n = TrioRulesNL.leafNameNF Mf n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    funext s v
    simp only [leafNameNF, TrioRulesNL.leafNameNF, ih, lvlO_200, cmpOrd_200, leafRest_200]
    rfl

theorem leafNameN_200 : leafNameN 200 = TrioRulesNL.leafNameN := by
  funext Mf s v
  simp only [leafNameN, TrioRulesNL.leafNameN, leafNameNF_200]; rfl

theorem leafNameOrYN_200 : leafNameOrYN 200 = TrioRulesNL.leafNameOrYN := by
  funext Mf s v
  simp only [leafNameOrYN, TrioRulesNL.leafNameOrYN, leafNameN_200]

theorem upgradeNF_200 (Mf : Od → Cols) :
    ∀ n, upgradeNF 200 Mf n = TrioRulesNL.upgradeNF Mf n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    funext s cs t used
    simp only [upgradeNF, TrioRulesNL.upgradeNF, ih, lvlO_200, leafNameOrYN_200]
    rfl

theorem fixNNeeded_200 : fixNNeeded 200 = TrioRulesNL.fixNNeeded := by
  funext Mf s
  simp only [fixNNeeded, TrioRulesNL.fixNNeeded, lvlO_200, cmpOrd_200, chainBase_200]; rfl

theorem fixN_200 : fixN 200 = TrioRulesNL.fixN := by
  funext Mf
  simp only [fixN, TrioRulesNL.fixN, upgradeNF_200]; rfl

theorem blockN_200 (Mf : Od → Cols) : ∀ n, blockN 200 Mf n = TrioRulesNL.blockN Mf n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    funext g x d arg plvl py
    simp only [blockN, TrioRulesNL.blockN, ih, spent_200, lvl_200, cmpOrd_200, leafNameN_200,
      strip_200, tailBlock_200]
    rfl

theorem restate_200 : restate 200 = TrioRulesNL.restate := by
  funext Mf ds
  simp only [restate, TrioRulesNL.restate, blockN_200]; rfl

theorem placeUnitsN_200 : placeUnitsN 200 = TrioRulesNL.placeUnitsN := by
  funext Mf cols alpha l r reg
  simp only [placeUnitsN, TrioRulesNL.placeUnitsN, blockN_200, spent_200, lvlO_200, cmpOrd_200,
    copyStorey_200, unitTailLevel_200, fixNNeeded_200, fixN_200, restate_200, tailBlock_200]
  rfl

theorem finishN_200 : finishN 200 = TrioRulesNL.finishN := by
  funext Mf a s
  simp only [finishN, TrioRulesNL.finishN, tailLevel_200, upgradeNF_200, appendSuffix_200]; rfl

theorem MstepAll_200 : MstepAll 200 = TrioRulesAll.MstepAll := by
  funext Mf a
  simp only [MstepAll, TrioRulesAll.MstepAll, lvlO_200, isPsiLevel_200, MpsiLevel3_200,
    finishN_200, placeUnitsN_200]
  rfl

theorem MfuelAll_200 : ∀ n, MfuelAll 200 n = TrioRulesAll.MfuelAll n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => funext a; simp only [MfuelAll, TrioRulesAll.MfuelAll, ih, MstepAll_200]

/-- **At fuel `200` the patched builder is `TrioRulesAll.MAll`.** -/
theorem MF_200 : MF 200 = TrioRulesAll.MAll := by
  funext a; simp only [MF, TrioRulesAll.MAll, MfuelAll_200]; rfl

/-! ### Up to depth `200` nothing changes -/

theorem fuelOf_of_le {alpha : Od} (h : odDep alpha ≤ 200) : fuelOf alpha = 200 := by
  simp only [fuelOf, fuel]; omega

/-- **Up to depth `200` the patched builder is `TrioRulesAll.MAll`.** -/
theorem MD_eq_MAll {alpha : Od} (h : odDep alpha ≤ 200) : MD alpha = TrioRulesAll.MAll alpha := by
  rw [MD, fuelOf_of_le h, MF_200]

theorem trioRuleMatrixD_eq {alpha : Od} (h : odDep alpha ≤ 200) :
    trioRuleMatrixD alpha = TrioRulesAll.trioRuleMatrixAll alpha := by
  rw [trioRuleMatrixD, MD_eq_MAll h]; rfl

/-- **On a label whose normal form has depth at most `200`, the patched matrix is
`TrioRulesAll`'s.** -/
theorem trioRuleMatrixOfD_eq (s : String) (h : ∀ a, parse s = some a → odDep a ≤ 200) :
    trioRuleMatrixOfD s = TrioRulesAll.trioRuleMatrixOfAll s := by
  unfold trioRuleMatrixOfD TrioRulesAll.trioRuleMatrixOfAll
  cases hp : parse s with
  | none => rfl
  | some a =>
    simp only [Option.bind_eq_bind, Option.bind_some]
    rw [trioRuleMatrixD_eq (h a hp)]

theorem fuelT_of_le {α : Term} (h : tDep α ≤ 200) : fuelT α = 200 := by
  simp only [fuelT, fuel]; omega

theorem ofTermD_eq {α : Term} (h : tDep α ≤ 200) : ofTermD α = TrioRules.ofTerm α := by
  rw [ofTermD, fuelT_of_le h, ofTerm_200]

/-- **On a term of depth at most `200` the patched map is the fuel-200 map.** -/
theorem trioMatrixLD_eq {α : Term} (h : tDep α ≤ 200) : trioMatrixLD α = trioMatrixLAll α := by
  rw [trioMatrixLD, ofTermD_eq h, fuelT_of_le h, MF_200]; rfl

/-! ### The two fuel-200 reads that stay

Two definitions under `MF F` still read `TrioRules.fuel`: `TrioRules.cmpAtomWith`
(inside every comparison `cmpF F`) calls `TrioRules.lvl`, and `TrioRules.add`
calls `TrioRules.cmpExp`.  Neither depends on the depth of the input:
`cmpAtomWith` is only called on atoms (`Ω_v`, `ψ_v(X)`; `cmpExpWith` tests
`isAtom`), where `lvl` stops after one step (`lvl_atom` below), and `add` is only
called on the constants `ω + 1` (`levelOmega`) and `Ω + 1`
(`TrioRules3.omegaOnePlusOne`). -/

/-- On an atom, `lvl` at fuel `200` is `lvl` at every fuel `F ≥ 1`. -/
theorem lvl_atom {F : Nat} (hF : 1 ≤ F) (x : Ex) (hx : x.isAtom = true) :
    TrioRules.lvl x = TrioFuel.lvl F x := by
  obtain ⟨k, rfl⟩ : ∃ k, F = k + 1 := ⟨F - 1, by omega⟩
  cases x with
  | o a => simp [Ex.isAtom] at hx
  | W v => rfl
  | psi v X => rfl

end Googology.Trans.BMS.TrioFixFuel
