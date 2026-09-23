import Googology.Trans.BMS.TrioFixOfTerm

/-!
# Patch "strip": rule 1 uncollapses an exponent whose head is not an atom

A patch on top of `TrioFixOfTerm.lean` (the reading `ofTermFix`) and
`TrioRulesAll.lean` (rules 1–10 of [koteitan/trio](https://github.com/koteitan/trio)
with Fixes A–E and N).  It changes **one function of rule 1**, `strip`, and the flag
that says whether the children `strip` gives start with an argument.

## The defect

A summand `ω^δ` of a sum the builder lays out (`blockF` / `blockN`) is a column whose
children spell `strip δ`: the argument `Y` with `ω^δ = ψ_v(Y)`, the `ψ_v` of the
column.  `TrioRules.strip` has three cases on the head `h·c` of `δ = h·c + ρ`:

* `h = ψ_v(X)`: `ω^δ = ψ_v(X + ψ_v(X)·(c-1) + ρ)`, children `X + ψ_v(X)·(c-1) + ρ`;
* `h = Ω_v`: `ω^δ = ψ_v(Ω_v·(c-1) + ρ)`, children `Ω_v·(c-1) + ρ`;
* otherwise (`h = ω^{e}`, not an atom): children `δ` itself.

The third case is right when `δ < ε₀` (`ψ_0(δ) = ω^δ`) and when the leading exponent
chain of `δ` (`δ = ω^{e₁}·c + ⋯`, `e₁ = ω^{e₂}·c' + ⋯`, …) ends in `Ω_v`
(`ψ_v(δ) = ω^{Ω_v + δ} = ω^δ`).  It is wrong when that chain ends in a `ψ` atom
`A = ψ_v(X)`: then `A ≤ δ < ` the next fixed point of `ω^·` after `A`, and
`ψ_v(δ)` is not `ω^δ` (for `v = 0`, `ψ_0(δ) = ψ_0(ψ_0(X)·ω) = ψ_0(X)`, since
`ψ_0` is constant from `ψ_0(X)` up to `Ω`: the tree of a non-standard term).  With
the reading `ofTermFix` this case is reached: `ψ_0(Ω + ψ_0(Ω+1)) = ω^{ε₀ + ε₀·ω} =
ω^{ε₀·ω}`, and `ε₀·ω = ω^{ε₀+1}` has the head `ω^{ε₀+1}`, whose chain ends in
`ε₀ = ψ_0(Ω)`.  The builder wrote its children as `ε₀·ω`, the tree of
`ψ_0(ψ_0(Ω+1))`, instead of `Ω + ε₀·ω`, the tree of `ψ_0(Ω + ψ_0(Ω+1))`.  This is
what broke the order in `TrioFixOfTerm.trioMatrixLFix_order_fails`.

## The change, for merging

Let `chainAtom h` be the atom at the end of the leading-exponent chain of the head
`h` (`none` if the chain ends in `0`, i.e. `h < ε₀`-like finite towers).  Then

* `stripSt δ` (in place of `TrioRules.strip δ`): the first two cases unchanged; in
  the third case, if `chainAtom h = ψ_v(X)` (any subscript `v`, as the first case
  treats every `ψ` atom), the children are `X + δ` (`add X (ato δ)`); otherwise `δ`
  as before.  Here `ψ_v(X + δ) = ω^{ψ_v(X) + δ} = ω^δ` since `ψ_v(X) < ω^{e₁}`.
* `uncollapses e` (in place of `headIsPsi (ato e)`): `chainAtom` of the head of `e`
  is a `ψ` atom.  For a head that is a `ψ` atom this is `headIsPsi`; it is `true` in
  the new case as well, because the children `X + δ` start with the argument `X`
  just as in the first case.  It is used as the `arg` flag of the children
  (`blockN`'s `subArg`, `tailBlockF`'s recursion).

`strip` is called in `blockN` (Fix N's copy of `blockF`) and in `tailBlockF`; the
flag in the same two places.  The patch copies, with `stripSt` / `uncollapses` in
place of `strip` / `headIsPsi ∘ ato` and no other change: `tailBlockF`,
`tailBlock`, `unitTailLevel`, `tailLevel` (no `Mf`), and `blockN`, `restate`,
`placeUnitsN`, `finishN`, `MstepAll` (`Mf`-parametric), then ties the knot
(`MfuelSt`, `MSt`).  Every other function (`writeLevel`, `leafY`, `suffixOf`,
`MOmega2`, `MpsiLevel3`, Fix N's `fixN`, …) is used as it is.  A merge replaces
the body of `TrioRules.strip` by `stripSt` and each `headIsPsi (ato e)` by
`uncollapses e` (in `blockF`, `blockF2`, `blockN`, and the copies in the other
patches); nothing else.

`stripSt_eq_strip`: the two agree unless the head of `δ` is not an atom and its
chain ends in a `ψ` atom; `uncollapses_eq` likewise for the flag.  Below `ε₀` no
`ψ` atom occurs, so the builder is unchanged there.

The checks are in `TrioFixStripSheet.lean`.
-/

namespace Googology.Trans.BMS.TrioFixStrip

open Googology.Notation.ExBuchholz
open Googology.Notation.ExBuchholz.Term
open Googology.Trans.BMS.TrioRules
open Googology.Trans.BMS.TrioRules2
open Googology.Trans.BMS.TrioRules3
open Googology.Trans.BMS.TrioRulesNL
open Googology.Trans.BMS.TrioRulesAll
open Googology.Trans.BMS.TrioFixOfTerm (ofTermFix)

/-! ### Rule 1, corrected -/

/-- The atom at the end of the leading-exponent chain: `x` itself for an atom,
`chainAtom e₁` for `ω^{e₁}·c + ⋯`, `none` for `ω^0` (a finite tower). -/
def chainAtomF : Nat → Ex → Option Ex
  | 0, _ => none
  | _ + 1, .o [] => none
  | n + 1, .o ((e, _) :: _) => chainAtomF n e
  | _ + 1, .W v => some (.W v)
  | _ + 1, .psi v X => some (.psi v X)

/-- `chainAtomF` with the builder's fuel. -/
def chainAtom (x : Ex) : Option Ex := chainAtomF fuel x

/-- The argument `X` when the chain ends in a `ψ` atom `ψ_v(X)`. -/
def chainArg (x : Ex) : Option Od :=
  match chainAtom x with
  | some (.psi _ X) => some X
  | _ => none

/-- **Rule 1, corrected** (`TrioRules.strip` with a third case): what the children
of the column of a summand `ω^δ` spell.  `ψ_v(X)·c + ρ ↦ X + ψ_v(X)·(c-1) + ρ`,
`Ω_v·c + ρ ↦ Ω_v·(c-1) + ρ` (as before); a head `ω^{e}` whose chain ends in
`ψ_v(X)` gives `X + δ` (**new**); anything else is itself. -/
def stripSt (delta : Ex) : Od :=
  match ato delta with
  | [] => []
  | (h, c) :: dt =>
    let rest := (if c > 1 then [(h, c - 1)] else []) ++ dt
    match h with
    | .psi _ X => add X rest
    | .W _ => rest
    | _ =>
      match chainArg h with
      | some X => add X ((h, c) :: dt)
      | none => (h, c) :: dt

/-- **The flag of the children** (in place of `headIsPsi (ato e)`): the children
`stripSt e` start with the argument of a `ψ` atom. -/
def uncollapses (e : Ex) : Bool :=
  match ato e with
  | (h, _) :: _ => (chainArg h).isSome
  | [] => false

/-- **Where the two rules 1 agree**: unless the head `h` of `δ` is not an atom and
its chain ends in a `ψ` atom. -/
theorem stripSt_eq_strip (delta : Ex)
    (h : ∀ h c dt, ato delta = (h, c) :: dt → h.isAtom = false → chainArg h = none) :
    stripSt delta = strip delta := by
  unfold stripSt strip
  cases hd : ato delta with
  | nil => rfl
  | cons p dt =>
    obtain ⟨hh, c⟩ := p
    cases hh with
    | psi v X => rfl
    | W v => rfl
    | o a => simp [h _ _ _ hd rfl]

theorem chainAtom_psi (v X : Od) : chainAtom (.psi v X) = some (.psi v X) := by
  simp [chainAtom, fuel, chainAtomF]

theorem chainAtom_W (v : Od) : chainAtom (.W v) = some (.W v) := by
  simp [chainAtom, fuel, chainAtomF]

/-- The flag agrees with `headIsPsi` on a head that is an atom. -/
theorem uncollapses_eq (e : Ex)
    (h : ∀ h c dt, ato e = (h, c) :: dt → h.isAtom = false → chainArg h = none) :
    uncollapses e = headIsPsi (ato e) := by
  unfold uncollapses headIsPsi
  cases hd : ato e with
  | nil => rfl
  | cons p dt =>
    obtain ⟨hh, c⟩ := p
    cases hh with
    | psi v X => simp [chainArg, chainAtom_psi, Ex.isPsi]
    | W v => simp [chainArg, chainAtom_W, Ex.isPsi]
    | o a => simp [h _ _ _ hd rfl, Ex.isPsi]

/-! ### The builder with the corrected rule 1

Copies of `TrioRules.tailBlockF` … `TrioRulesAll.MstepAll` with `stripSt` and
`uncollapses`; no other change. -/

/-- `TrioRules.tailBlockF` with `stripSt`. -/
def tailBlockFSt : Nat → Od → Bool → Option Od
  | 0, _, _ => none
  | n + 1, gamma, arg =>
    match gamma.getLast? with
    | none => none
    | some (e, _) =>
      let rest := stripSt e
      if !rest.isEmpty then tailBlockFSt n rest (uncollapses e)
      else if arg then none else lvl e

/-- `TrioRules.tailBlock` with `stripSt`. -/
def tailBlockSt (gamma : Od) (arg : Bool) : Option Od := tailBlockFSt fuel gamma arg

/-- `TrioRules.unitTailLevel` with `stripSt`. -/
def unitTailLevelSt (beta : Od) : Option Od :=
  let bp := predBeta beta
  if beta.isEmpty || bp.isEmpty then none
  else match bp.getLast? with
    | some (e, _) => tailBlockSt (ato e) false
    | none => none

/-- `TrioRules.tailLevel` with `stripSt`. -/
def tailLevelSt (alpha : Od) : Option Od :=
  match (units alpha).getLast? with
  | none => none
  | some b => unitTailLevelSt (ato b)

section
variable (Mf : Od → Cols)

/-- `TrioRulesNL.blockN` with `stripSt` and `uncollapses`. -/
def blockNSt : Nat → Od → Int → Int → Bool → Option Od → Int → StateM CtxN Unit
  | 0, _, _, _, _, _, _ => pure ()
  | n + 1, gamma, x0, d0, arg, plvl, py => do
    let mut x := x0
    let mut d := d0
    for ec in gamma do
      let e := ec.1
      let subArg := uncollapses e
      for _ in [0:ec.2] do
        if !(← get).c.fresh && spent Mf (← get).c then
          TrioRulesNL.liftC (laySt none)
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
        let sub := stripSt e
        let mut nx := (lastC run).x + 1
        let mut nd := (lastC run).y
        modify fun s => { s with c := { s.c with prev := if arg then none else v } }
        if !sub.isEmpty && !(← get).c.fresh && spent Mf (← get).c then
          TrioRulesNL.liftC (laySt none)
          let l := lastC (← get).c.cols
          nx := l.x + 1
          nd := l.y
        blockNSt n sub nx nd subArg v (lastC run).y
        modify fun s => { s with c := { s.c with prev := tailBlockSt (ato e) arg } }

/-- `TrioRulesNL.restate` with `blockNSt`. -/
def restateSt (digits : List Ex) : StateM CtxN (Int × Int) := do
  let lr := lastRootPlain (← get).c.cols
  let y := lr.1 + 1
  let x0 := lr.2 + 2
  let two : Cols := #[⟨lr.2 + 1, lr.1, false⟩, ⟨x0, y, true⟩]
  modify fun s => { s with c := { s.c with cols := s.c.cols ++ two, level := y - 1 } }
  for e in digits do
    modify fun s => { s with c := { s.c with cols := s.c.cols.push ⟨x0 + 1, y, true⟩ } }
    blockNSt Mf fuel (ato e) (x0 + 2) (y - 1) false none 0
  pure (y, x0)

/-- `TrioRulesNL.placeUnitsN` with `blockNSt`, `restateSt`, `tailBlockSt`,
`unitTailLevelSt`. -/
def placeUnitsNSt (cols : Cols) (alpha : Od) (level0 rootX0 : Int) (regime : Option Od) :
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
                let lr ← restateSt Mf (alld.take (j + 1))
                level := lr.1
                rootX := lr.2
              else
                let lr := lastRootPlain (← get).c.cols
                level := lr.1
                rootX := lr.2
            modify fun s => { s with c := { s.c with cols := s.c.cols.push ⟨rootX + 1, level, true⟩ } }
            blockNSt Mf fuel (ato e) (rootX + 2) (level - 1) false none 0
            j := j + 1
          if !rest.isEmpty then
            modify fun s => { s with c := { s.c with prev := unitTailLevelSt (ato b0) } }
        | none => pure ()
    let mut prev0 := false
    let mut first := true
    for b in (units alpha).drop skip do
      let beta := ato b
      modify fun s => { s with c := { s.c with fresh := false } }
      let laid := !first && spent Mf (← get).c
      if laid then
        TrioRulesNL.liftC (laySt none)
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
            TrioRulesNL.liftC (laySt none)
            let lr := lastRootPlain (← get).c.cols
            y := lr.1
            x0 := lr.2
            modify fun s => { s with c := { s.c with level := lr.1 - 1 } }
          else if i != 0 && fixNNeeded Mf (← get) then
            if ← fixN Mf then
              let lr ← restateSt Mf (digits.take i)
              y := lr.1
              x0 := lr.2
            else
              let lr := lastRootPlain (← get).c.cols
              y := lr.1
              x0 := lr.2
              modify fun s => { s with c := { s.c with level := lr.1 - 1 } }
          modify fun s => { s with c := { s.c with cols := s.c.cols.push ⟨x0 + 1, y, true⟩ } }
          blockNSt Mf fuel (ato e) (x0 + 2) (y - 1) false none 0
          -- Fix D: a digit too deep for a countable regime, with digits after it.
          match tailBlockSt (ato e) false, regime with
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
        modify fun s => { s with c := { s.c with prev := unitTailLevelSt beta } }
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

/-- `TrioRulesNL.finishN` with `tailLevelSt`. -/
def finishNSt (alpha : Od) (s : CtxN) : Cols :=
  match tailLevelSt alpha with
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

/-- **One step of the builder**: `TrioRulesAll.MstepAll` with `placeUnitsNSt` and
`finishNSt`. -/
def MstepSt (alpha : Od) : Cols :=
  match lvlO alpha with
  | none => finishNSt Mf alpha (placeUnitsNSt Mf #[] alpha 0 (-1) none)
  | some v =>
    match isPsiLevel alpha with
    | some uX => MpsiLevel3 Mf uX.1 uX.2
    | none =>
      if alpha == [(.W v, 1)] then MOmega2 Mf v
      else
        let base := MOmega2 Mf v
        let ya := lastRoot base
        finishNSt Mf alpha (placeUnitsNSt Mf base alpha ya.1 (ya.2 - 1) (some v))

end

/-- The builder with the corrected rule 1, with fuel. -/
def MfuelSt : Nat → Od → Cols
  | 0, _ => #[]
  | n + 1, a => MstepSt (MfuelSt n) a

/-- `α ↦` the columns of `ψ_0(Ω_α)`, by rules 1–10 with Fixes A–E, N and the
corrected rule 1. -/
def MSt (alpha : Od) : Cols := MfuelSt fuel alpha

/-- **The trio matrix of `ψ_0(Ω_α)`** with the corrected rule 1. -/
def trioRuleMatrixSt (alpha : Od) : List (List Nat) := toRows (MSt alpha)

/-- The matrix for a label of the sheet. -/
def trioRuleMatrixOfSt (s : String) : Option (List (List Nat)) := do
  let a ← parse s
  if a.isEmpty then none else some (trioRuleMatrixSt a)

/-- The matrix of a label, `[]` when it does not parse. -/
def stOf (s : String) : List (List Nat) := (trioRuleMatrixOfSt s).getD []

/-- **The trio matrix of a term**: the reading `ofTermFix`, then the builder with
the corrected rule 1. -/
def trioMatrixLSt (α : Term) : List (List Nat) := trioRuleMatrixSt (ofTermFix α)

/-- Every column is three rows deep with `z < 2`. -/
theorem WF3_trioRuleMatrixSt (alpha : Od) : Googology.Trans.BMS.WF3 (trioRuleMatrixSt alpha) := WF3_toRows _

theorem WF3_trioMatrixLSt (α : Term) : Googology.Trans.BMS.WF3 (trioMatrixLSt α) := WF3_toRows _

/-- On `α = ψ_{Ω_u}(X)` and on `α = Ω_v` the step is `MstepAll`'s (the patch only
touches the branch through `placeUnits`). -/
theorem MstepSt_eq_MstepAll_of_ne (Mf : Od → Cols) (alpha v : Od) (hv : lvlO alpha = some v)
    (h : isPsiLevel alpha ≠ none ∨ alpha == [(.W v, 1)]) :
    MstepSt Mf alpha = MstepAll Mf alpha := by
  cases hp : isPsiLevel alpha with
  | some uX => simp [MstepSt, MstepAll, hv, hp]
  | none =>
    have he : (alpha == [(.W v, 1)]) = true := by
      rcases h with h | h
      · exact absurd hp h
      · exact h
    simp [MstepSt, MstepAll, hv, hp, he]

/-! ### The case of `TrioFixOfTerm.trioMatrixLFix_order_fails` -/

/-- `ε₀·ω = ω^{ε₀+1}`, the exponent of `ψ_0(Ω + ψ_0(Ω+1)) = ω^{ε₀·ω}`. -/
def e0w : Ex := .o [(.psi [] [(.W one, 1)], 1), (.o [], 1)]

/-- The old rule 1 writes it as itself, the tree of `ψ_0(ψ_0(Ω+1))`. -/
theorem strip_e0w : strip (.o [(e0w, 1)]) = [(e0w, 1)] := rfl

/-- The corrected rule 1 writes it as `Ω + ε₀·ω`, the tree of `ψ_0(Ω + ψ_0(Ω+1))`. -/
theorem stripSt_e0w : stripSt (.o [(e0w, 1)]) = [(.W one, 1), (e0w, 1)] := rfl

open Googology.Trans.BMS.TrioFixOfTerm (tα tβ) in
/-- With it, `β = ψ_0(ψ_1(ψ_0(Ω + ψ_0(Ω+1))))` gets the tree of the term (the old
map's matrix), which lies above that of `α = ε_{ε₀}`. -/
theorem trioMatrixLSt_tβ : trioMatrixLSt tβ =
    [[0,0,0],[1,1,1],[2,1,1],[3,0,0],[4,1,0],[5,0,0],[6,1,0],[6,0,0],[7,1,0],[7,0,0]] := by
  decide +kernel

open Googology.Trans.BMS.TrioFixOfTerm (tα tβ) in
theorem trioMatrixLSt_tα : trioMatrixLSt tα =
    [[0,0,0],[1,1,1],[2,1,1],[3,0,0],[4,1,0],[5,0,0],[6,1,0]] := by
  decide +kernel

open Googology.Trans.BMS.TrioFixOfTerm (tα tβ) in
/-- **The counterexample is gone**: `tα < tβ` and now `M(tα) < M(tβ)`. -/
theorem trioMatrixLSt_tα_lt_tβ : trioMatrixLSt tα < trioMatrixLSt tβ := by
  rw [trioMatrixLSt_tα, trioMatrixLSt_tβ]; decide

end Googology.Trans.BMS.TrioFixStrip
