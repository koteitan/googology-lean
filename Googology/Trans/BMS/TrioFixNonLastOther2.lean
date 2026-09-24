import Googology.Trans.BMS.TrioFixNonLastOther

/-!
# Fix G, Fix M and change 1 of `TrioFixNonLastOther`, narrowed

A patch on top of `TrioFixNonLastOther.lean` (rules 1–10 of
[koteitan/trio](https://github.com/koteitan/trio) with Fixes A–E, N, G, M and changes 1–4).
It narrows where Fix M (change 3), Fix G (change 2) and change 1 act, so that pairs that
were in order before `TrioFixNonLastOther` stay in order.  Change 4 (lifted leaves) is
not touched.  The checks are in `TrioFixNonLastOther2Sheet.lean` (and the heavy sheets
`TrioFixNonLastOther2SheetHeavy1`, `…Heavy2`); they are `#guard`s, a
calibration, not a theorem.

## Notation

`r` is the regime (`α ∈ [Ω_r, Ω_{r+1})`), `p` the level the last leaf names (`prev`),
`tops r = chainG r` (`TrioFixNonLastOther`), `N_s(v) = leafNameOrYN s v` the row-1 entry
of a leaf naming `v` in the current state `s` (Fix N's leaf name, else `leafY v`).
A level `u` is *marked* when `suffixOf (chainBase u) ≠ []`.

## The change (exactly this, nothing else)

`MstepX2 Mf α = MstepX Mf α` except in the sum branch, where `placeUnitsX2` replaces
`placeUnitsX`; `placeUnitsX2`, `blockX2`, `restateX2` are `placeUnitsX`, `blockX`,
`restateX` with `spentX2`, `fixXNeeded2`, `fixX2` in place of `spentX`, `fixXNeeded`,
`fixX`.  Everything else (`fixM`, `fixN`, `layLifts`, `liftLeaf`, `markCols`, …) is
reused unchanged.

1. **Change 1′** (`spentX2`).  In an uncountable regime rule 6's `spent` is switched
   off only when `keepSpent` fails, where
   `keepSpent ⇔ leafY r ≠ 1 ∨ (p marked ∧ p ∉ tops r)`.
   (`spentX` switched it off in every uncountable regime.)  So rule 6 is back in
   `r = Ω_{ω·2}`, `Ω_{ω·3}` (`leafY r = 2, 3`), and in `r = Ω_{ω^2}` after a marked
   level that is not a top (`p = ω`).  In `r = Ω_ω`, `Ω_{Ω_ω}` (`leafY r = 1`, marked
   levels there are tops) nothing changes.
2. **Fix G′** (`fixGNeeded2`) `= fixGNeeded ∧ leafApart ∧ upgradeFull`:
   * `leafApart s r p ⇔ ∀ t ∈ tops r, t < p → N_s(t) ≠ N_s(p)`: the leaf of `p` is
     not the leaf of a lower top (e.g. `p = Ω` has `N = 2` like the top `ω+1` of
     `r = Ω_{ω+2}` and the top `ω` of `r = Ω_{Ω_ω}`, and like the top `ω·2` of
     `r = Ω_{ω·2}`);
   * `upgradeFull s p ⇔ omArg (upgradeNF s cols p).t = none`: the upgrade of the last
     leaf spells `p`'s `Ω`-chain to its end (for `p = Ω` in `r = Ω_{ω·2}`,
     `Ω_{ω·3}`, `Ω_{ω+2}` no sub-unit names `1`, so the leaf of `Ω` stays the leaf of
     a lower level with a mark, `ω·2` in `r = Ω_{ω·3}`).
3. **Fix M′** (`fixMNeeded2`) `= fixMNeeded ∧ (isTower r ∨ leafApart s r p)`: in a
   tower regime Fix M is unchanged; outside the towers it needs the leaf of `p` apart
   from the lower tops (`p = ω` has `N = 1` like the top `1` in `r = Ω+1` and the tops
   `1` of `r = Ω_2, Ω_3, Ω_4`; in `r = Ω_ω` the level `ω·2` has `N = 2`, the top `ω`
   has `N = 1`, so Fix M stays there).
4. `fixX2`: Fix M′ when `fixMNeeded2`, else Fix N (which is also Fix G′), as `fixX`.

The Python reference is the calibration script of `TrioFixNonLastOther` with three
predicates added (not published); the Lean builder equals it on 3,345 of the 3,387
labels below (`#eval`, outside the sheets; the other 42 have 138–656 columns and take
minutes each in Lean).

## What the calibration shows (Python reference, yaBMS `bms -s` for standardness)

On 3,387 labels in 25 families (the five calibrated families of `TrioFixNonLastOther`,
its three Python-only ones, and 17 more: sums of up to three terms after `Ω_r` for the
regimes `r = Ω_2, Ω_3, Ω_4, Ω+1, Ω_{Ω+1}, Ω_{ω·2}, Ω_{ω·3}, Ω_{ω+1}, Ω_{ω+2}, Ω_{ω^2},
Ω_{ω^2+1}, Ω_{Ω_ω}, Ω_{Ω_2}, Ω_{Ω_2+1}`, and wider ones for `Ω_ω` (two) and `Ω_Ω`):

* The five calibrated families, the families after `Ω_{Ω+1}`, `Ω_{Ω+2}`, `Ω_{Ω_3}`, and
  the 27 expansions `M(P+t·ω)[n] = M(P+t·(n+1))`: every matrix is `TrioFixNonLastOther`'s.
* The nine pairs of the review are in order again (`TrioFixNonLastOther2Sheet.lean`).
* Against `TrioRulesAll` (before `TrioFixNonLastOther`), pairs put out of order /
  in order: after `Ω_{Ω_2}` (the review's 165-label family plus two products)
  `278/1,695 → 0/1,695`; after `Ω_{Ω_3}`, `Ω_{Ω_4}`, `Ω_{Ω+1}`, `Ω_{Ω_{Ω+1}}`
  `276, 276, 144, 153 → 0`; after `Ω_{Ω_{ω·2}}` `1,679 → 0`; after `Ω_{Ω_{ω·3}}`
  `526 → 0`; matrices that become not standard: `15 → 0` after `Ω_{Ω_2}` (and `0` in
  every family).

## Still open

* Some pairs that `TrioRulesAll` had in order are still out of order (Python):
  after `Ω_{Ω_{ω+2}}` 52 (of 1,161 put in order), after `Ω_{Ω_{Ω_ω}}` 24 (of 960),
  after `Ω_{Ω_{ω^2+1}}` 22 (of 904), after `Ω_{Ω_{ω^2}}` 8 (of 1,652), after
  `Ω_{Ω_{ω+1}}` 6 (of 108), after `Ω_{Ω_ω}` 2 and 11 (families with `Ω_{ω·2}`; these
  are `TrioFixNonLastOther`'s own).  The ones after `Ω_{Ω_{ω+1}}`, `Ω_{Ω_{ω+2}}`,
  `Ω_{Ω_{Ω_ω}}`, `Ω_{Ω_{ω^2+1}}` follow a leaf whose level shares its
  leaf with a lower top (`γ+Ω_Ω+…` against `γ+Ω_{ω+1}+…` when `r = Ω_{ω+1}`, `Ω_{ω+2}`;
  `γ+Ω_Ω+Ω_2` against `γ+Ω_ω+Ω_ω` when `r = Ω_{Ω_ω}`): Fix G′ leaves that leaf alone,
  and a later Fix G′ copy or lifted leaf (change 4) puts the pair out of order.  Turning
  off every later fix after such a leaf gives `52, 6, 24 → 0, 0, 13` but raises the
  disagreements after `Ω_{Ω_{ω·2}}` (`2,626 → 2,781`); not done.
* After `Ω_{Ω_{ω^2}}`, `M(γ+Ω_ω) > M(γ+Ω_ω+x)` (`γ = Ω_Ω`, `Ω_{ω^2}`): the last-leaf
  version carries the mark `(3,2,1)`, the storey that rule 6 lays is below it.
* Where rule 6 is back after `Ω_{Ω_{ω·2}}`, its storeys and change 4's lifted copies give
  matrices of up to 656 columns; 117 of the 221 are not standard (`TrioRulesAll`: 124, at
  most 74 columns; `TrioFixNonLastOther`: 20); none of the 117 was standard under
  `TrioRulesAll`.
* The last leaves behind all this are not this item: `M(γ+Ω_Ω) = M(γ+Ω_{ω+1})` for
  `γ = Ω_{Ω_{ω+1}}`, `Ω_{Ω_{ω+2}}`; `M(γ+Ω_ω) = M(γ+Ω_{ω·2})` for `γ = Ω_{Ω_{ω^2}}`
  (all under `TrioRulesAll` already); and after `Ω_{Ω_2}` the leaf of `Ω_ω` is the leaf
  of `Ω` with the mark `(1,1,1)`, not standard.
* The "Still open" list of `TrioFixNonLastOther` stands, except its last item (the
  review's regressions), which this patch answers.
-/

namespace Googology.Trans.BMS.TrioFixNonLastOther2

open Googology.Trans.BMS.TrioRules
open Googology.Trans.BMS.TrioRules2
open Googology.Trans.BMS.TrioRules3
open Googology.Trans.BMS.TrioRulesNL
open Googology.Trans.BMS.TrioRulesAll
open Googology.Trans.BMS.TrioFixNonLastOther

section
variable (Mf : Od → Cols)

/-- `u`'s chain has a mark (`suffixOf (chainBase u) ≠ []`). -/
def markedLvl (u : Od) : Bool := !(suffixOf Mf (chainBase u)).isEmpty

/-- **Change 1′**: rule 6's storey stays off in an uncountable regime `r` only when
`leafY r = 1` and the last leaf's level `u` is not a marked level outside the tops. -/
def keepSpent (c : Ctx) : Bool :=
  match c.regime, c.prev with
  | some r, some u => leafY Mf r != 1 || (markedLvl Mf u && !isTop r u)
  | _, _ => false

/-- **Change 1′**: rule 6's `spent`, except in an uncountable regime where
`keepSpent` fails. -/
def spentX2 (c : Ctx) : Bool :=
  if (c.regime.bind lvlO).isSome && !keepSpent Mf c then false else spent Mf c

/-- No top `t < p` of `r` has the leaf name of `p` (`leafNameOrYN`, in the current
state). -/
def leafApart (s : CtxN) (r p : Od) : Bool :=
  (topsG r).all fun t => cmpOrd t p != .lt || leafNameOrYN Mf s t != leafNameOrYN Mf s p

/-- The upgrade of the last leaf (`upgradeNF`) reaches the end of `p`'s `Ω`-chain. -/
def upgradeFull (s : CtxN) (p : Od) : Bool :=
  (omArg (upgradeNF Mf fuel s s.c.cols p false).2.1).isNone

/-- **Fix G′**: Fix G when the leaf of `p` is apart from the lower tops and its
upgrade is full. -/
def fixGNeeded2 (s : CtxN) : Bool :=
  fixGNeeded Mf s &&
    match s.c.regime, s.c.prev with
    | some r, some p => leafApart Mf s r p && upgradeFull Mf s p
    | _, _ => false

/-- **Fix M′**: Fix M in a tower regime, and outside the towers when the leaf of `p`
is apart from the lower tops. -/
def fixMNeeded2 (s : CtxN) : Bool :=
  fixMNeeded Mf s &&
    match s.c.regime, s.c.prev with
    | some r, some p => isTower r || leafApart Mf s r p
    | _, _ => false

/-- Fix N, Fix G′ or Fix M′ is needed. -/
def fixXNeeded2 (s : CtxN) : Bool := fixNNeeded Mf s || fixGNeeded2 Mf s || fixMNeeded2 Mf s

/-- Fix M′, else Fix N (which is also Fix G′). -/
def fixX2 : StateM CtxN Bool := do
  if fixMNeeded2 Mf (← get) then fixM Mf else fixN Mf

/-- `blockX` with `spentX2` in place of `spentX`. -/
def blockX2 : Nat → Od → Int → Int → Bool → Option Od → Int → StateM CtxN Unit
  | 0, _, _, _, _, _, _ => pure ()
  | n + 1, gamma, x0, d0, arg, plvl, py => do
    let mut x := x0
    let mut d := d0
    for ec in gamma do
      let e := ec.1
      let subArg := headIsPsi (ato e)
      for _ in [0:ec.2] do
        if !(← get).c.fresh && spentX2 Mf (← get).c then
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
        if !sub.isEmpty && !(← get).c.fresh && spentX2 Mf (← get).c then
          TrioRulesNL.liftC (laySt none)
          let l := lastC (← get).c.cols
          nx := l.x + 1
          nd := l.y
        blockX2 n sub nx nd subArg v lastRun.y
        modify fun s => { s with c := { s.c with prev := tailBlock (ato e) arg } }

/-- `restateX` with `blockX2`. -/
def restateX2 (digits : List Ex) : StateM CtxN (Int × Int) := do
  let lr := lastRootPlain (← get).c.cols
  let y := lr.1 + 1
  let x0 := lr.2 + 2
  let two : Cols := #[⟨lr.2 + 1, lr.1, false⟩, ⟨x0, y, true⟩]
  modify fun s => { s with c := { s.c with cols := s.c.cols ++ two, level := y - 1 } }
  for e in digits do
    modify fun s => { s with c := { s.c with cols := s.c.cols.push ⟨x0 + 1, y, true⟩ } }
    blockX2 Mf fuel (ato e) (x0 + 2) (y - 1) false none 0
  pure (y, x0)

/-- `placeUnitsX` with `spentX2`, `fixXNeeded2` and `fixX2` in place of `spentX`,
`fixXNeeded` and `fixX`. -/
def placeUnitsX2 (cols : Cols) (alpha : Od) (level0 rootX0 : Int) (regime : Option Od) :
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
            if fixXNeeded2 Mf (← get) then
              if ← fixX2 Mf then
                let lr ← restateX2 Mf (alld.take (j + 1))
                level := lr.1
                rootX := lr.2
              else
                let lr := lastRootPlain (← get).c.cols
                level := lr.1
                rootX := lr.2
            modify fun s => { s with c := { s.c with cols := s.c.cols.push ⟨rootX + 1, level, true⟩ } }
            blockX2 Mf fuel (ato e) (rootX + 2) (level - 1) false none 0
            j := j + 1
          if !rest.isEmpty then
            modify fun s => { s with c := { s.c with prev := unitTailLevel (ato b0) } }
        | none => pure ()
    let mut prev0 := false
    let mut first := true
    for b in (units alpha).drop skip do
      let beta := ato b
      modify fun s => { s with c := { s.c with fresh := false } }
      let laid := !first && spentX2 Mf (← get).c
      if laid then
        TrioRulesNL.liftC (laySt none)
        let lr := lastRootPlain (← get).c.cols
        level := lr.1
        rootX := lr.2
        prev0 := false
      else if (!first || skip == 1) && fixXNeeded2 Mf (← get) then
        let _ ← fixX2 Mf
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
          if i != 0 && !(← get).c.fresh && spentX2 Mf (← get).c then
            TrioRulesNL.liftC (laySt none)
            let lr := lastRootPlain (← get).c.cols
            y := lr.1
            x0 := lr.2
            modify fun s => { s with c := { s.c with level := lr.1 - 1 } }
          else if i != 0 && fixXNeeded2 Mf (← get) then
            if ← fixX2 Mf then
              let lr ← restateX2 Mf (digits.take i)
              y := lr.1
              x0 := lr.2
            else
              let lr := lastRootPlain (← get).c.cols
              y := lr.1
              x0 := lr.2
              modify fun s => { s with c := { s.c with level := lr.1 - 1 } }
          modify fun s => { s with c := { s.c with cols := s.c.cols.push ⟨x0 + 1, y, true⟩ } }
          blockX2 Mf fuel (ato e) (x0 + 2) (y - 1) false none 0
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

/-- **One step of the patched builder**: `MstepX` with `placeUnitsX2` in the sum branch. -/
def MstepX2 (alpha : Od) : Cols :=
  match lvlO alpha with
  | none => finishN Mf alpha (placeUnitsX2 Mf #[] alpha 0 (-1) none)
  | some v =>
    match isPsiLevel alpha with
    | some uX => MpsiLevel3 Mf uX.1 uX.2
    | none =>
      if alpha == [(.W v, 1)] then MOmega2 Mf v
      else
        let base := MOmega2 Mf v
        let ya := lastRoot base
        finishN Mf alpha (placeUnitsX2 Mf base alpha ya.1 (ya.2 - 1) (some v))

end

/-- The patched builder with fuel. -/
def MfuelX2 : Nat → Od → Cols
  | 0, _ => #[]
  | n + 1, a => MstepX2 (MfuelX2 n) a

/-- `α ↦` the columns of `ψ_0(Ω_α)`, by the rules with Fixes A–E, N, G and M, narrowed. -/
def MX2 (alpha : Od) : Cols := MfuelX2 fuel alpha

/-- **The trio matrix of `ψ_0(Ω_α)` with Fixes A–E, N, G and M, narrowed.** -/
def trioRuleMatrixX2 (alpha : Od) : List (List Nat) := toRows (MX2 alpha)

/-- The matrix for a label of the sheet. -/
def trioRuleMatrixOfX2 (s : String) : Option (List (List Nat)) := do
  let a ← parse s
  if a.isEmpty then none else some (trioRuleMatrixX2 a)

/-- The matrix of a label, `[]` when it does not parse. -/
def x2Of (s : String) : List (List Nat) := (trioRuleMatrixOfX2 s).getD []


/-- **Every column is three rows deep with `z < 2`.** -/
theorem WF3_trioRuleMatrixX2 (alpha : Od) : WF3 (trioRuleMatrixX2 alpha) := WF3_toRows _

/-! ### Where the narrowing cannot act -/

section
variable (Mf : Od → Cols)

/-- The step on `α = ψ_{Ω_u}(X)` is `MstepX`'s. -/
theorem MstepX2_psi (alpha v : Od) (uX : Od × Od)
    (hv : lvlO alpha = some v) (hp : isPsiLevel alpha = some uX) :
    MstepX2 Mf alpha = MstepX Mf alpha := by
  simp [MstepX2, MstepX, hv, hp]

/-- On `α = Ω_v` the step is `MstepX`'s. -/
theorem MstepX2_omega (alpha v : Od) (hv : lvlO alpha = some v)
    (hp : isPsiLevel alpha = none) (he : (alpha == [(.W v, 1)]) = true) :
    MstepX2 Mf alpha = MstepX Mf alpha := by
  simp [MstepX2, MstepX, hv, hp, he]

/-- In a countable regime `spentX2` is rule 6's `spent`, as `spentX` is. -/
theorem spentX2_countable (c : Ctx) (h : c.regime.bind lvlO = none) :
    spentX2 Mf c = spentX Mf c := by
  simp [spentX2, spentX, h]

/-- Where `keepSpent` fails, `spentX2` is `spentX` (both `false` in an uncountable
regime). -/
theorem spentX2_of_not_keep (c : Ctx) (hk : keepSpent Mf c = false) :
    spentX2 Mf c = spentX Mf c := by
  unfold spentX2 spentX
  cases h : (c.regime.bind lvlO).isSome <;> simp_all

/-- `spentX2` never fires where `spentX` fires and `spent` does not. -/
theorem spentX2_le_spent (c : Ctx) (h : spentX2 Mf c = true) : spent Mf c = true := by
  unfold spentX2 at h
  split at h
  · exact absurd h (by simp)
  · exact h

/-- **Fix G′** implies Fix G. -/
theorem fixGNeeded2_imp (s : CtxN) (h : fixGNeeded2 Mf s = true) : fixGNeeded Mf s = true := by
  unfold fixGNeeded2 at h
  simp only [Bool.and_eq_true] at h
  exact h.1

/-- **Fix M′** implies Fix M. -/
theorem fixMNeeded2_imp (s : CtxN) (h : fixMNeeded2 Mf s = true) : fixMNeeded Mf s = true := by
  unfold fixMNeeded2 at h
  simp only [Bool.and_eq_true] at h
  exact h.1

/-- In a tower regime Fix M′ is Fix M. -/
theorem fixMNeeded2_tower (s : CtxN) (r : Od) (h : s.c.regime = some r)
    (ht : isTower r = true) : fixMNeeded2 Mf s = fixMNeeded Mf s := by
  unfold fixMNeeded2 fixMNeeded
  rw [h]
  cases s.c.prev <;> simp [ht]

/-- In a countable regime no fix fires. -/
theorem fixXNeeded2_countable (s : CtxN) (h : s.c.regime = none) :
    fixXNeeded2 Mf s = false := by
  simp [fixXNeeded2, fixNNeeded, fixGNeeded2, fixMNeeded2, fixGNeeded, fixMNeeded, h]

end

end Googology.Trans.BMS.TrioFixNonLastOther2
