import Googology.Trans.BMS.TrioRules

/-!
# Rules 1–10, corrected on the 22 rows where the sheet is right

`TrioRules.lean` transcribes rules 1–10 of
[koteitan/trio](https://github.com/koteitan/trio)
([algorithm page](https://github.com/koteitan/trio/blob/main/ebp2bms/algorithm/2/README-en.md)).
[TRIO-SHEET-41.md](TRIO-SHEET-41.md) decides the 41 rows of the sheet where those
rules and the sheet disagree: the sheet is right on 22 of them (12 order errors
`S-o` and 10 collisions `S-c`).  This file is `TrioRules.lean` with four
corrections, which give the sheet's matrix on exactly those 22 rows and change
nothing else on the 785 standard rows (of the 28 non-standard rows, only row
4533 changes, by Fix A).  Everything not listed below is reused from
`TrioRules.lean` unchanged.

Notation: a column is `(x, y, z)`; "the leaf naming `Ω_v`" is the `z = 0` column
a unit writes for a summand of level `v`; `r` is the regime (`α = Ω_r·… `, the
subscript of `M(Ω_r)`, the base the units are laid on); `N(v)` is the row-1
entry the rules give a leaf naming `Ω_v`.

* **Fix A (the base `M(Ω_v)`, `MOmega2`).**  `M(Ω_v)` drops the last column of
  `M(v)` when that column is a level column.  Corrected: it is dropped only when
  its parent is a level column or the root; a level column whose parent is a
  leaf (the column `(x+1, y, 0)` that ends `M(ψ_{Ω_u}(Ω_u))` and `M(ψ_1(Ω_2))`)
  is kept, as it is, with no copy of `B`'s tail inserted after it.
  Rows 4508, 4628, 4674, 4762, 4769.
* **Fix B (rules 4–6 under an uncountable regime, `leafName`, `upgrade`).**
  Let `lvl r ≠ none`.
  1. A leaf naming `Ω_v` with `v = Ω_w` (a single `Ω` atom) has
     `N(Ω_w) = N(w) + 1`.
  2. The rule "`N(v) = leafY v + 1` when `leafY v = leafY r`, `v ≠ 1`" is not
     used when `r = Ω_v`.
  3. The upgrade of a final leaf naming `Ω_t`: while `t = Ω_w`, append a copy of
     the last sub-unit `(a,L,1)(a+1,L,1)(a+2,N(w),0)` already in the matrix,
     `L` the row-1 entry of the current last column; then `t := w`.  After
     that, the old upgrade (the suffix of `M(t)`), without the old `tail_sub`
     (which was the one-step case of 3).
  Rows 4488, 4609, 4613, 4618, 4667, 4744–4747, 4750–4753.
* **Fix C (rules 2 and 8, `placeUnits2`).**  When the copy of the base's last
  storey is down to one sub-unit, it stands for the first add unit's first digit
  `Ω_r` only; the other digits of that unit's `β'` are laid on the copy's root.
  (The old rules dropped them.)  Rows 4490, 4491, 4497.
* **Fix D (rule 6 under a countable regime, `placeUnits2`).**  When a digit that
  is not the last of its add unit names `Ω_p` with `p < r` and
  `leafY p > leafY r`, its leaf is lowered to `leafY r`, storeys with leaves
  `leafY r + 1, …, leafY p` are laid (as the old rules do after a whole unit),
  and one more storey is laid for the next digit.  Row 3492.

The calibration against every row of the sheet, the verdicts of
`TrioSheet41.lean`, and the order check are in `TrioRules2Sheet.lean`.
-/

namespace Googology.Trans.BMS.TrioRules2

open Googology.Trans.BMS.TrioRules

/-- `w` when `v = Ω_w` is a single `Ω` atom. -/
def omArg (v : Od) : Option Od :=
  match v with
  | [(.W w, 1)] => some w
  | _ => none

/-- The last sub-unit `(a,L,1)(a+1,L,1)(a+2,y2,0)` of `cs`. -/
def findSub (cs : Cols) (L y2 : Int) : Option Cols :=
  ((List.range cs.size).reverse.find? fun i =>
    let c := colAt cs i
    i + 2 < cs.size && c.z && c.y == L &&
      colAt cs (i + 1) == ⟨c.x + 1, L, true⟩ && colAt cs (i + 2) == ⟨c.x + 2, y2, false⟩).map
    fun i => cs.extract i (i + 3)

/-- The depth-first walk of `MOmega2`: `omegaDfs`, except that the column
`plain` takes no copy of `B`'s tail. -/
def omegaDfs2 (cs : Cols) (par : Array (Option Nat)) (drop plain : Option Nat) :
    Nat → Nat → Int → List TrioRules.Col
  | 0, _, _ => []
  | n + 1, i, d =>
    if drop == some i then [] else
    let c := colAt cs i
    let ins : List TrioRules.Col :=
      if (isLevel cs par i && plain != some i) || i == 0 then
        [⟨d + 1, c.y + 1, true⟩, ⟨d + 2, c.y + 1, true⟩, ⟨d + 3, c.y + 1, false⟩]
      else []
    (⟨d, c.y, c.z⟩ :: ins) ++
      (kidsOf par cs.size i).flatMap fun k => omegaDfs2 cs par drop plain n k (d + 1)

section
variable (Mf : Od → Cols)

/-- **Fix A**: `M(Ω_v)` by insertion; a trailing level column is dropped only
when its parent is a level column or the root, and kept plain otherwise. -/
def MOmega2 (v : Od) : Cols :=
  let cs := Mf v
  if cs.isEmpty then #[] else
  let par := forest cs
  let last := cs.size - 1
  let lastLev := isLevel cs par last
  let parLev := match par.getD last none with
    | some p => isLevel cs par p || p == 0
    | none => false
  let drop := if lastLev && parLev then some last else none
  let plain := if lastLev && !parLev then some last else none
  (omegaDfs2 cs par drop plain (cs.size + 1) 0 0).toArray

/-- Rule 9 on the corrected base. -/
def MpsiLevel2 (u X : Od) : Cols :=
  let base := MOmega2 Mf u
  let y0 := (lastC base).y
  let cols := setLastY base (y0 - 1)
  let x := (lastC base).x + 1
  match lvlO X with
  | none => #[]
  | some w =>
    if cmpOrd w u == .eq then cols.push ⟨x, y0, false⟩
    else appendSuffix Mf (cols ++ writeLevel Mf w x (y0 - 1) true [Mf u, cols]) w 0 none

/-- **Fix B 1–2**: the row-1 entry of a unit's leaf naming `Ω_v`, when a
regime rule sets it (`none`: `writeLevel`'s, i.e. `leafY v`). -/
def leafNameF : Nat → Ctx → Od → Option Int
  | 0, _, _ => none
  | n + 1, c, v =>
    match c.regime with
    | none => none
    | some r =>
      let unc := (lvlO r).isSome
      match omArg v with
      | some w =>
        if unc then some ((leafNameF n c w).getD (leafY Mf w) + 1) else rest c v r unc
      | none => rest c v r unc
where
  /-- The old branches: the regime itself past a storey, and one slot deeper. -/
  rest (c : Ctx) (v r : Od) (unc : Bool) : Option Int :=
    if c.storeys != 0 && cmpOrd v r == .eq then
      some (if !unc then c.level else c.leafLevel.getD 0)
    else if unc && leafY Mf v == leafY Mf r && cmpOrd v one != .eq &&
        !(match omArg r with | some u => cmpOrd u v == .eq | none => false) then
      some (leafY Mf v + 1)
    else none

/-- `N(v)`. -/
def leafName (c : Ctx) (v : Od) : Option Int := leafNameF Mf fuel c v

/-- `N(v)`, falling back to `leafY v`. -/
def leafNameOrY (c : Ctx) (v : Od) : Int := (leafName Mf c v).getD (leafY Mf v)

/-- **Fix B 3**: the upgrade of a final leaf naming `Ω_t` while `t = Ω_w`;
returns the columns and the `t` left for `appendSuffix`. -/
def upgradeF : Nat → Ctx → Cols → Od → Cols × Od
  | 0, _, cs, t => (cs, t)
  | n + 1, c, cs, t =>
    match c.regime, omArg t with
    | some r, some w =>
      if (lvlO r).isSome && !(lastC cs).z then
        match findSub cs (lastC cs).y (leafNameOrY Mf c w) with
        | some sub => upgradeF n c (cs ++ sub) w
        | none => (cs, t)
      else (cs, t)
    | _, _ => (cs, t)

/-- The OT embedding `blockF` with Fix B's leaf. -/
def blockF2 : Nat → Od → Int → Int → Bool → Option Od → Int → StateM Ctx Unit
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
            else if !arg then
              match leafName Mf ctx v with
              | some y => #[⟨x, y, false⟩]
              | none => writeLevel Mf v x d arg [ctx.cols]
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
        blockF2 n sub nx nd subArg v (lastC run).y
        modify fun c => { c with prev := tailBlock (ato e) arg }

/-- `placeUnits` with Fixes C and D. -/
def placeUnits2 (cols : Cols) (alpha : Od) (level0 rootX0 : Int) (regime : Option Od) : Ctx :=
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
      -- Fix C: the copy is the first unit's first digit; lay its other digits.
      if skip == 1 then
        match (units alpha).head? with
        | some b0 =>
          let rest := (units (predBeta (ato b0))).drop 1
          for e in rest do
            modify fun c => { c with cols := c.cols.push ⟨rootX + 1, level, true⟩ }
            blockF2 Mf fuel (ato e) (rootX + 2) (level - 1) false none 0
          if !rest.isEmpty then
            modify fun c => { c with prev := unitTailLevel (ato b0) }
        | none => pure ()
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
        let digits := units (predBeta beta)
        let mut i := 0
        for e in digits do
          if i != 0 && !(← get).fresh && spent Mf (← get) then
            laySt none
            let lr := lastRootPlain (← get).cols
            y := lr.1
            x0 := lr.2
            modify fun c => { c with level := lr.1 - 1 }
          modify fun c => { c with cols := c.cols.push ⟨x0 + 1, y, true⟩ }
          blockF2 Mf fuel (ato e) (x0 + 2) (y - 1) false none 0
          -- Fix D: a digit too deep for a countable regime, with digits after it.
          match tailBlock (ato e) false, regime with
          | some p, some r =>
            if i + 1 < digits.length && (lvlO r).isNone && cmpOrd p r == .lt &&
                decide (leafY Mf p > leafY Mf r) then
              modify fun c => { c with cols := setLastY c.cols (leafY Mf r) }
              for k in [1:(leafY Mf p - leafY Mf r).toNat + 1] do
                laySt (some (leafY Mf r + k))
              laySt none
              let lr := lastRootPlain (← get).cols
              y := lr.1
              x0 := lr.2
              modify fun c => { c with level := lr.1 - 1 }
          | _, _ => pure ()
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

/-- The upgrade at the end: Fix B 3, then the suffix of `M(t)`. -/
def finish2 (alpha : Od) (ctx : Ctx) : Cols :=
  match tailLevel alpha with
  | some t =>
    let ct := upgradeF Mf fuel ctx ctx.cols t
    appendSuffix Mf ct.1 ct.2 ctx.storeys none
  | none => ctx.cols

/-- One step of the corrected builder. -/
def Mstep2 (alpha : Od) : Cols :=
  match lvlO alpha with
  | none => finish2 Mf alpha (placeUnits2 Mf #[] alpha 0 (-1) none)
  | some v =>
    match isPsiLevel alpha with
    | some uX => MpsiLevel2 Mf uX.1 uX.2
    | none =>
      if alpha == [(.W v, 1)] then MOmega2 Mf v
      else
        let base := MOmega2 Mf v
        let ya := lastRoot base
        finish2 Mf alpha (placeUnits2 Mf base alpha ya.1 (ya.2 - 1) (some v))

end

/-- The corrected builder with fuel. -/
def Mfuel2 : Nat → Od → Cols
  | 0, _ => #[]
  | n + 1, a => Mstep2 (Mfuel2 n) a

/-- `α ↦` the columns of `ψ_0(Ω_α)`, by the corrected rules. -/
def M2 (alpha : Od) : Cols := Mfuel2 fuel alpha

/-- **The trio matrix of `ψ_0(Ω_α)` by the corrected rules.** -/
def trioRuleMatrix2 (alpha : Od) : List (List Nat) := toRows (M2 alpha)

/-- The corrected matrix for a label of the sheet. -/
def trioRuleMatrixOf2 (s : String) : Option (List (List Nat)) := do
  let a ← parse s
  if a.isEmpty then none else some (trioRuleMatrix2 a)

/-- **Every column is three rows deep with `z < 2`.** -/
theorem WF3_trioRuleMatrix2 (alpha : Od) : WF3 (trioRuleMatrix2 alpha) := WF3_toRows _

/-! ### The four fixes on one row each -/

-- Fix A, row 4508 `Ω_{ψ_1(Ω_2)}`: the kept column `(5,2,0)`.
#guard trioRuleMatrixOf2 "W_psi_1(W_2)" = some [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,1],[4,1,0],[5,2,0]]
-- Fix B, row 4747 `Ω_{Ω_Ω}·2`: leaf 3, then the sub-units at heights 3 and 2.
#guard trioRuleMatrixOf2 "(W_W_W*2)" = some [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,1],[4,1,0],[3,2,0],[4,3,1],[5,3,1],[6,3,0],[4,3,1],[5,3,1],[6,2,0],[5,3,0],[6,4,1],[7,4,1],[8,3,0],[7,4,0],[8,5,1],[9,5,1],[10,3,0],[4,3,1],[5,3,1],[6,2,0],[2,2,1],[3,2,1],[4,1,0]]
-- Fix C, row 4490 `Ω_{Ω+1}·ω`: the digit `(6,4,1)` of `+1`.
#guard trioRuleMatrixOf2 "(W_(W+1)*w)" = some [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,1],[3,1,0],[1,1,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,1],[4,1,0],[3,2,0],[4,3,1],[5,3,1],[6,3,0],[4,3,0],[5,4,1],[6,4,1],[7,3,0],[6,4,1]]
-- Fix D, row 3492 `Ω_ω·Ω_2·ω`: two storeys, then the digit.
#guard trioRuleMatrixOf2 "(W_w*W_2*w)" = some [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[1,1,1],[2,1,0],[3,2,1],[4,2,1],[5,1,0],[4,2,1],[5,1,0],[1,1,0],[2,2,1],[3,2,1],[4,2,0],[2,2,1],[3,2,0],[4,3,1],[5,3,1],[6,2,0],[5,3,1],[6,2,0],[2,2,0],[3,3,1],[4,3,1],[5,3,0],[3,3,1],[4,3,0],[5,4,1],[6,4,1],[7,3,0],[6,4,1],[7,2,0],[6,4,1]]

end Googology.Trans.BMS.TrioRules2
