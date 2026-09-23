import Googology.Trans.BMS.TrioRulesAll

/-!
# Fix S: the stretch from `Ω_ω·Ω+Ω_2` to `Ω_ω·Ω·2`

A separate patch on top of `TrioRulesAll.lean` (rules 1–10 of
[koteitan/trio](https://github.com/koteitan/trio) with Fixes A–E and N).
[TRIO-ROW-3480.md](TRIO-ROW-3480.md) shows that the rules are wrong on the whole
stretch from `β+Ω_2` to `β·2`, `β = Ω_ω·Ω`.  With this patch the builder gives
the matrices that note asks for:

* `M(β+Ω_3) = c2` (row 3480; `c2` is proved standard in `TrioRow3480.lean`);
* `M(β+Ω_ω) = lM = w2 ++ (2,2,1)` (row 3481) and `M(β+Ω_{n+2}) = lM[n]`;
* `M(β·2) = b1 = w2 ++ (7,4,1)(8,1,0)` (row 3482), `M(β+Ω_ω·ω) = t2 = w2 ++ (7,4,1)`;
* `β+Ω_2+1`, `β+Ω_2·ω`, `β+Ω_2·Ω`, `β+Ω_2^2` are written on the lifted copy of
  `w2`'s storey, between `w2` and `c2`.

## Where the stretch lives in the builder

`α = β + …` has the countable regime `r = ω` (`α ≥ Ω_ω`, `lvlO r = none`).  The unit
after `β` is **laid**: `β`'s tail leaf `(8,1,0)` names `Ω` and `leafY 1 = leafY ω`,
so `spent` holds and the unit starts with `laySt none`, the storey `(1,1,0)…(6,1,0)`
of `w1 = M(β+Ω)`.  Inside that storey the leaf value `L = leafY r + 1 = 2` does what
the value `1` does on the base `M(Ω_ω)`: it names `Ω_2`, and with the mark `(2,2,1)`
it names `Ω_ω`.  `Ω_3, Ω_4, …` need one more storey each.  That storey is BMS's own
ascension of the old one (`blift` of `TrioRulesNonLast.lean`), not the plain lift
`laySt`: the plain lift turns `(6,1,0)` into `(7,2,0)`, which is not standard.

## The change (Fix S)

Notation: `r` is the regime.  Fix S acts only when `r` is **countable**
(`lvlO r = none`).  `L = leafY r + 1`.  A unit is *laid* when the builder laid a storey
for it at its start (`laid := !first && spent`, as in `placeUnits`).  A unit is
*in the storey* (`laidS` in the code) when it is laid, or when an earlier unit of the
same `α` was laid, or when a Fix S copy (S3) was laid before it.  Everything below
applies only to units in the storey under a countable regime.  Every other path is
`TrioRulesAll`'s, unchanged.

* **S1 (leaf name, `leafNameS`, used by `blockS`).**  A unit leaf (`arg = false`,
  not the `plvl` case) naming `v` gets the row-1 value `L` when `v = r` (was
  `Ctx.level`, the unit's anchor level, from `leafNameF.rest`), or when `v < r` and
  `leafY v > L` (was `leafY v`).  Exception: when `v` is the cap of a Fix N/S copy
  with a recorded value, `leafNameN` is used (the copy's value).  Otherwise
  `leafNameN`, as before.
* **S2 (storeys for a deep level, `deepStoreys`, after each digit).**  After a digit
  whose last column is a leaf of value `L` naming `p` (`p = tailBlock (ato e) false`),
  with `p < r` and `leafY p > L`: append `leafY p - L` lifted copies, one after the
  other.  Each copy is `blift cs s₀` from the row-1 parent `s₀` of the current last
  leaf, with the leaf lifted instead of kept (`bliftUpS`).  So
  `M(β+Ω_{2+k}) = w2` followed by `k` lifted copies.
* **S3 (a leaf with more after it, `fixSNeeded`).**  At three places: before the
  next digit, before the next unit (when the unit before was in the storey and the
  next unit is not laid), and inside `blockS` before a sibling summand (`!arg`).
  S3 fires when the last column is a leaf of value `> leafY r` naming `p < r`, `p` is
  not the cap of an earlier copy, and `M(chainBase p)` has no mark.  It runs Fix N's
  `fixN`.  Under a countable regime `fixN` writes no sub-unit.  It lays the lifted
  copy with the leaf kept, and makes `p` the cap.  The next digit, unit or summand
  continues from the copy (its last root, or the copy's leaf `x` for a summand), as
  in Fix N.
* **S5 (no second storey inside the storey).**  In a unit in the storey, `spent`
  does not lay a storey (in `blockS`, between digits, and at the start of the next
  unit).  BMS agrees: `M(β+Ω·ω)[1] = w1 ++ (7,4,0)(8,5,1)(9,5,1)(10,1,0)` and
  `M(β·ω)[2] = b1 ++ (7,4,0)(8,5,1)(9,5,1)(10,2,0)(9,5,1)(10,1,0)` continue in the
  same storey.
* **Fix D and the end-of-unit storeys are not used in a unit in the storey.**  S1–S3
  replace them there.  Outside the storey both are unchanged; row 3492 `Ω_ω·Ω_2·ω`
  is not in a storey.

For the merge: this patch replaces `placeUnitsN` by `placeUnitsS` and `blockN` by
`blockS` in the non-`ψ` branches of `MstepAll` (`MstepS`).  `placeUnitsS` is
`placeUnitsN` with the lines marked `-- Fix S`, and `blockS` is `blockN` with the
lines marked `-- Fix S`.  `MOmega2`, `MpsiLevel3` (Fixes A, E), `finishN`, `fixN`,
`restate` and Fix N's trigger `fixNNeeded` are reused as they are.
`MstepS_eq_MstepAll_of_ne` states that the `ψ` and `Ω_v` branches are unchanged.

The checks are in `TrioFixStretchSheet.lean`; the explanation is in
[TRIO-FIX-STRETCH.md](TRIO-FIX-STRETCH.md).  All checks are `#guard`s: a
calibration, not a theorem.
-/
namespace Googology.Trans.BMS.TrioFixStretch

open Googology.Trans.BMS.TrioRules
open Googology.Trans.BMS.TrioRules2
open Googology.Trans.BMS.TrioRules3
open Googology.Trans.BMS.TrioRulesNL
open Googology.Trans.BMS.TrioRulesAll

/-- `blift` with the leaf lifted instead of kept (BMS ascension of `cs[s0:]`). -/
def bliftUpS (cs : Cols) (s0 : Nat) : Cols :=
  let seg := blift cs s0
  setLastY seg ((lastC seg).y + 1)

/-- The row-1 parent of the last column (`0` when there is none). -/
def lastPar1 (cs : Cols) : Nat := ((par1 cs).getD (cs.size - 1) none).getD 0

/-- `k` lifted copies, one after the other, each from the row-1 parent of the
current last leaf. -/
def bliftUpN : Nat → Cols → Cols
  | 0, cs => cs
  | k + 1, cs => bliftUpN k (cs ++ bliftUpS cs (lastPar1 cs))

section
variable (Mf : Od → Cols)

/-- The countable regime `r` (`none` when the regime is absent or uncountable). -/
def countableRegime (c : Ctx) : Option Od :=
  match c.regime with
  | some r => if (lvlO r).isNone then some r else none
  | none => none

/-- `L = leafY r + 1`, the leaf value of the storey of a laid unit. -/
def storeyLeaf (r : Od) : Int := leafY Mf r + 1

/-- **Fix S 1**: the leaf name in a laid unit under a countable regime. -/
def leafNameS (laid : Bool) (s : CtxN) (v : Od) : Option Int :=
  match (if laid then countableRegime s.c else none) with
  | some r =>
    let isCap := match s.n.cap with | some q => cmpOrd v q == .eq | none => false
    if isCap && s.n.capy.isSome then leafNameN Mf s v else
    if cmpOrd v r == .eq ||
        (cmpOrd v r == .lt && decide (leafY Mf v > storeyLeaf Mf r)) then
      some (storeyLeaf Mf r)
    else leafNameN Mf s v
  | none => leafNameN Mf s v

/-- **Fix S 3**: the last leaf names a level below a countable regime, with a
value above the regime's own leaf, and no mark in its chain. -/
def fixSNeeded (s : CtxN) : Bool :=
  match countableRegime s.c, s.c.prev with
  | some r, some p =>
    cmpOrd p r == .lt && !(lastC s.c.cols).z &&
      decide ((lastC s.c.cols).y > leafY Mf r) &&
      (suffixOf Mf (chainBase p)).isEmpty &&
      !(match s.n.cap with | some q => cmpOrd p q == .eq | none => false)
  | _, _ => false

/-- `blockN` with Fix S 1's leaf name (`laid`: the unit was laid). -/
def blockS (laid : Bool) : Nat → Od → Int → Int → Bool → Option Od → Int → StateM CtxN Unit
  | 0, _, _, _, _, _, _ => pure ()
  | n + 1, gamma, x0, d0, arg, plvl, py => do
    let mut x := x0
    let mut d := d0
    let mut firstS := true  -- Fix S 3
    for ec in gamma do
      let e := ec.1
      let subArg := headIsPsi (ato e)
      for _ in [0:ec.2] do
        -- Fix S 3: a leaf with a sibling summand after it, in a laid unit.
        if laid && !arg && !firstS && fixSNeeded Mf (← get) then
          let _ ← fixN Mf
          let l := lastC (← get).c.cols
          x := l.x
          d := l.y
        firstS := false
        if !(laid && (countableRegime (← get).c).isSome) &&  -- Fix S 5
            !(← get).c.fresh && spent Mf (← get).c then
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
              match leafNameS Mf laid s v with   -- Fix S 1
              | some y => #[⟨x, y, false⟩]
              | none => writeLevel Mf v x d arg [s.c.cols]
            else writeLevel Mf v x d arg [s.c.cols]
        modify fun s => { s with c := { s.c with cols := s.c.cols ++ run } }
        let sub := strip e
        let mut nx := (lastC run).x + 1
        let mut nd := (lastC run).y
        modify fun s => { s with c := { s.c with prev := if arg then none else v } }
        if !(laid && (countableRegime (← get).c).isSome) &&  -- Fix S 5
            !sub.isEmpty && !(← get).c.fresh && spent Mf (← get).c then
          TrioRulesNL.liftC (laySt none)
          let l := lastC (← get).c.cols
          nx := l.x + 1
          nd := l.y
        blockS laid n sub nx nd subArg v (lastC run).y
        modify fun s => { s with c := { s.c with prev := tailBlock (ato e) arg } }

/-- **Fix S 2**: after a digit of a laid unit whose leaf of value `L` names `p < r`
with `leafY p > L`, the `leafY p - L` lifted copies. -/
def deepStoreys (laid : Bool) (e : Ex) : StateM CtxN Unit := do
  let s ← get
  match (if laid then countableRegime s.c else none), tailBlock (ato e) false with
  | some r, some p =>
    let L := storeyLeaf Mf r
    let cs := s.c.cols
    if cmpOrd p r == .lt && decide (leafY Mf p > L) && !(lastC cs).z && (lastC cs).y == L then
      let cs' := bliftUpN (leafY Mf p - L).toNat cs
      set ({ s with c := { s.c with cols := cs', st := cs.size } } : CtxN)
  | _, _ => pure ()

/-- `placeUnitsN` with Fix S (the changed lines are marked `-- Fix S`). -/
def placeUnitsS (cols : Cols) (alpha : Od) (level0 rootX0 : Int) (regime : Option Od) :
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
                let lr ← restate Mf (alld.take (j + 1))
                level := lr.1
                rootX := lr.2
              else
                let lr := lastRootPlain (← get).c.cols
                level := lr.1
                rootX := lr.2
            modify fun s => { s with c := { s.c with cols := s.c.cols.push ⟨rootX + 1, level, true⟩ } }
            blockS Mf false fuel (ato e) (rootX + 2) (level - 1) false none 0
            j := j + 1
          if !rest.isEmpty then
            modify fun s => { s with c := { s.c with prev := unitTailLevel (ato b0) } }
        | none => pure ()
    let mut prev0 := false
    let mut first := true
    let mut prevLaid := false  -- Fix S
    let mut inS := false  -- Fix S: a Fix S copy has been laid
    for b in (units alpha).drop skip do
      let beta := ato b
      modify fun s => { s with c := { s.c with fresh := false } }
      let laid := !first && !inS && spent Mf (← get).c  -- Fix S 5: `!inS`
      if laid then
        TrioRulesNL.liftC (laySt none)
        let lr := lastRootPlain (← get).c.cols
        level := lr.1
        rootX := lr.2
        prev0 := false
      else if (!first || skip == 1) &&
          (fixNNeeded Mf (← get) || (prevLaid && fixSNeeded Mf (← get))) then  -- Fix S 3
        if prevLaid && fixSNeeded Mf (← get) then inS := true  -- Fix S
        let _ ← fixN Mf
        let lr := lastRootPlain (← get).c.cols
        level := lr.1
        rootX := lr.2
        prev0 := false
      if laid && (regime.bind lvlO).isNone then inS := true  -- Fix S: the storey stays
      let laidS := laid || inS  -- Fix S: laid, or after a laid unit / a Fix S copy
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
          if i != 0 && !laidS && !(← get).c.fresh && spent Mf (← get).c then  -- Fix S 5
            TrioRulesNL.liftC (laySt none)
            let lr := lastRootPlain (← get).c.cols
            y := lr.1
            x0 := lr.2
            modify fun s => { s with c := { s.c with level := lr.1 - 1 } }
          else if i != 0 &&
              (fixNNeeded Mf (← get) || (laidS && fixSNeeded Mf (← get))) then  -- Fix S 3
            if laidS && fixSNeeded Mf (← get) then inS := true  -- Fix S
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
          blockS Mf laidS fuel (ato e) (x0 + 2) (y - 1) false none 0  -- Fix S 1
          deepStoreys Mf laidS e  -- Fix S 2
          -- Fix D: a digit too deep for a countable regime, with digits after it.
          match tailBlock (ato e) false, regime with
          | some p, some r =>
            if !laidS &&  -- Fix S: not in a laid unit
                i + 1 < digits.length && (lvlO r).isNone && cmpOrd p r == .lt &&
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
      prevLaid := laidS  -- Fix S
      if !beta.isEmpty then
        modify fun s => { s with c := { s.c with prev := unitTailLevel beta } }
      match (← get).c.prev, regime with
      | some p, some r =>
        if (lvlO r).isNone && !laidS && cmpOrd p r == .lt then  -- Fix S: `laidS` (was `laid`)
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

/-- One step of the builder: `MstepAll` with `placeUnitsS` in place of
`placeUnitsN`. -/
def MstepS (alpha : Od) : Cols :=
  match lvlO alpha with
  | none => finishN Mf alpha (placeUnitsS Mf #[] alpha 0 (-1) none)
  | some v =>
    match isPsiLevel alpha with
    | some uX => MpsiLevel3 Mf uX.1 uX.2
    | none =>
      if alpha == [(.W v, 1)] then MOmega2 Mf v
      else
        let base := MOmega2 Mf v
        let ya := lastRoot base
        finishN Mf alpha (placeUnitsS Mf base alpha ya.1 (ya.2 - 1) (some v))

end

/-- The builder with Fix S, with fuel. -/
def MfuelS : Nat → Od → Cols
  | 0, _ => #[]
  | n + 1, a => MstepS (MfuelS n) a

/-- `α ↦` the columns of `ψ_0(Ω_α)`, by rules 1–10 with Fixes A–E, N and S. -/
def MS (alpha : Od) : Cols := MfuelS fuel alpha

/-- **The trio matrix of `ψ_0(Ω_α)` with Fixes A–E, N and S.** -/
def trioRuleMatrixS (alpha : Od) : List (List Nat) := toRows (MS alpha)

/-- The matrix for a label of the sheet. -/
def trioRuleMatrixOfS (s : String) : Option (List (List Nat)) := do
  let a ← parse s
  if a.isEmpty then none else some (trioRuleMatrixS a)

/-- The matrix of a label, `[]` when it does not parse. -/
def sOf (s : String) : List (List Nat) := (trioRuleMatrixOfS s).getD []

/-- **Every column is three rows deep with `z < 2`.** -/
theorem WF3_trioRuleMatrixS (alpha : Od) : WF3 (trioRuleMatrixS alpha) := WF3_toRows _

/-- On `α = ψ_{Ω_u}(X)` and on `α = Ω_v` the step is `MstepAll`'s (Fix S only
touches `placeUnits`). -/
theorem MstepS_eq_MstepAll_of_ne (Mf : Od → Cols) (alpha v : Od) (hv : lvlO alpha = some v)
    (h : isPsiLevel alpha ≠ none ∨ alpha == [(.W v, 1)]) :
    MstepS Mf alpha = MstepAll Mf alpha := by
  cases hp : isPsiLevel alpha with
  | some uX => simp [MstepS, MstepAll, hv, hp]
  | none =>
    have he : (alpha == [(.W v, 1)]) = true := by
      rcases h with h | h
      · exact absurd hp h
      · exact h
    simp [MstepS, MstepAll, hv, hp, he]

end Googology.Trans.BMS.TrioFixStretch
