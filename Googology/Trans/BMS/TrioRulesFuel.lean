import Googology.Trans.BMS.TrioRulesE0

/-!
# Rules 1–10 with the fuel taken from the depth

`TrioRules.lean` runs every recursion of the transcribed program on one fixed
fuel, `TrioRules.fuel = 200`, and `TrioRulesE0.lean` shows that this is enough
below `ε₀` exactly when the nesting depth is at most `201` (the tower of depth
`203` comes out one column short).  Here the fuel is a parameter:

* `TrioFuel.M F`, `TrioFuel.ofTerm F`, `TrioFuel.trioMatrixF F` are the
  definitions of `TrioRules.lean` with every use of `fuel` replaced by `F`.
  At `F = 200` they are `TrioRules`' own functions (`M_200`, `ofTerm_200`,
  `trioMatrixF_200`), so this is the same program, not a variant.
* `trioMatrixD α := trioMatrixF (dep α + 1) α`: the fuel grows with the term.

The main theorem is

  `trioMatrixD α = trioMatrix α`   for every `α : exbE0.State`
  (`trioMatrixD_eq_trioMatrix`),

with no depth bound and no hypothesis, and more generally
`trioMatrixF F α = trioMatrix α` whenever `1 ≤ F` and `dep α ≤ F + 1`
(`trioMatrixF_eq_trioMatrix`).  The proof is `TrioRulesE0.lean`'s with `200`
replaced by `F`; the lemmas there that do not mention the fuel are reused.
-/

namespace Googology.Trans.BMS.TrioFuel

open Googology.Notation.ExBuchholz
open Googology.Notation.ExBuchholz.Term
open Googology.Trans.BMS.TrioRules (Ex Od ato nat one wpow lvlF cmpExpWith cmpOrdWith cmpF units
  predBeta headIsPsi Col Cols colAt lastC setLastY forest isLevel lastRootPlain lastRoot lastStorey
  zIdx runsGo Ctx laySt copyLoop leafY suffixOf writeLevel MOmega toRows omegaFree)

/-! ### The program, with the fuel as a parameter -/

section
variable (F : Nat)

/-- `TrioRules.lvl` with fuel `F`. -/
def lvl (x : Ex) : Option Od := lvlF F x

/-- `TrioRules.lvlO` with fuel `F`. -/
def lvlO (a : Od) : Option Od := lvl F (.o a)

/-- `TrioRules.cmpOrd` with fuel `F`. -/
def cmpOrd (a b : Od) : Ordering := cmpF F a b

/-- `TrioRules.cmpExp` with fuel `F`. -/
def cmpExp (x y : Ex) : Ordering := cmpExpWith (cmpF F) x y

/-- `TrioRules.add` with fuel `F`. -/
def add (a b : Od) : Od :=
  match b with
  | [] => a
  | (lead, cb) :: bt =>
    let keep := a.filter fun t => cmpExp F t.1 lead == .gt
    let same := a.filter fun t => cmpExp F t.1 lead == .eq
    match same with
    | s :: _ => keep ++ ((lead, s.2 + cb) :: bt)
    | [] => keep ++ b

/-- `TrioRules.strip` with fuel `F`. -/
def strip (delta : Ex) : Od :=
  match ato delta with
  | [] => []
  | (h, c) :: dt =>
    let rest := (if c > 1 then [(h, c - 1)] else []) ++ dt
    match h with
    | .psi _ X => add F X rest
    | .W _ => rest
    | _ => (h, c) :: dt

/-- `TrioRules.tailBlockF` with fuel `F` inside. -/
def tailBlockF : Nat → Od → Bool → Option Od
  | 0, _, _ => none
  | n + 1, gamma, arg =>
    match gamma.getLast? with
    | none => none
    | some (e, _) =>
      let rest := strip F e
      if !rest.isEmpty then tailBlockF n rest (headIsPsi (ato e))
      else if arg then none else lvl F e

/-- `TrioRules.tailBlock` with fuel `F`. -/
def tailBlock (gamma : Od) (arg : Bool) : Option Od := tailBlockF F F gamma arg

/-- `TrioRules.unitTailLevel` with fuel `F`. -/
def unitTailLevel (beta : Od) : Option Od :=
  let bp := predBeta beta
  if beta.isEmpty || bp.isEmpty then none
  else match bp.getLast? with
    | some (e, _) => tailBlock F (ato e) false
    | none => none

/-- `TrioRules.tailLevel` with fuel `F`. -/
def tailLevel (alpha : Od) : Option Od :=
  match (units alpha).getLast? with
  | none => none
  | some b => unitTailLevel F (ato b)

/-- `TrioRules.isPsiLevel` with fuel `F`. -/
def isPsiLevel (alpha : Od) : Option (Od × Od) :=
  match alpha with
  | [(a@(.psi v X), 1)] =>
    if v.isEmpty then none
    else match lvl F a with
      | some u => if cmpOrd F u v != .eq then some (u, X) else none
      | none => none
  | _ => none

/-- `TrioRules.copyStorey` with fuel `F`. -/
def copyStorey (ax : Int) : StateM Ctx Int := do
  let cs := (← get).cols
  let i0 := lastStorey cs
  let z0 := (List.range cs.size).filter fun j => j ≥ i0 && !(colAt cs j).z
  copyLoop F (cs.extract i0 (z0.getLast?.getD 0 + 1)) ax

section
variable (Mf : Od → Cols)

/-- `TrioRules.spent` with fuel `F`. -/
def spent (c : Ctx) : Bool :=
  match c.prev, c.regime with
  | some u, some v =>
    cmpOrd F u v != .eq && !(suffixOf Mf v).isEmpty && leafY Mf u == leafY Mf v
  | _, _ => false

/-- `TrioRules.appendSuffix` with fuel `F`. -/
def appendSuffix (cols : Cols) (v : Od) (storeys : Nat) (tailSub : Option Cols) : Cols :=
  if (lastC cols).z then cols else
  let suf := suffixOf Mf v
  if suf.isEmpty then
    match tailSub with
    | some ts => if !ts.isEmpty && (lvlO F v).isSome then cols ++ ts else cols
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

/-- `TrioRules.blockF` with fuel `F` in the pieces it calls. -/
def blockF : Nat → Od → Int → Int → Bool → Option Od → Int → StateM Ctx Unit
  | 0, _, _, _, _, _, _ => pure ()
  | n + 1, gamma, x0, d0, arg, plvl, py => do
    let mut x := x0
    let mut d := d0
    for ec in gamma do
      let e := ec.1
      let subArg := headIsPsi (ato e)
      for _ in [0:ec.2] do
        if !(← get).fresh && spent F Mf (← get) then
          laySt none
          let l := lastC (← get).cols
          x := l.x
          d := l.y
        let ctx ← get
        let v := lvl F e
        let run : Cols :=
          match v with
          | none => #[⟨x, 0, false⟩]
          | some v =>
            if !arg && (match plvl with | some p => cmpOrd F v p == .eq | none => false) then
              #[⟨x, py, false⟩]
            else if !arg && ctx.storeys != 0 &&
                (match ctx.regime with | some r => cmpOrd F v r == .eq | none => false) then
              #[⟨x, (if (ctx.regime.bind (lvlO F)).isNone then ctx.level
                     else ctx.leafLevel.getD 0), false⟩]
            else if !arg && (match ctx.regime with
                | some r => (lvlO F r).isSome && leafY Mf v == leafY Mf r && cmpOrd F v one != .eq
                | none => false) then
              #[⟨x, leafY Mf v + 1, false⟩]
            else writeLevel Mf v x d arg [ctx.cols]
        modify fun c => { c with cols := c.cols ++ run }
        let sub := strip F e
        let mut nx := (lastC run).x + 1
        let mut nd := (lastC run).y
        modify fun c => { c with prev := if arg then none else v }
        if !sub.isEmpty && !(← get).fresh && spent F Mf (← get) then
          laySt none
          let l := lastC (← get).cols
          nx := l.x + 1
          nd := l.y
        blockF n sub nx nd subArg v (lastC run).y
        modify fun c => { c with prev := tailBlock F (ato e) arg }

/-- `TrioRules.placeUnits` with fuel `F`. -/
def placeUnits (cols : Cols) (alpha : Od) (level0 rootX0 : Int) (regime : Option Od) : Ctx :=
  let act : StateM Ctx Unit := do
    let mut level := level0
    let mut rootX := rootX0
    let mut skip := 0
    if (regime.bind (lvlO F)).isSome then
      let k ← copyStorey F (rootX + 1)
      skip := if k == 1 then 1 else 0
      let lr := lastRootPlain (← get).cols
      level := lr.1
      rootX := lr.2
    let mut prev0 := false
    let mut first := true
    for b in (units alpha).drop skip do
      let beta := ato b
      modify fun c => { c with fresh := false }
      let laid := !first && spent F Mf (← get)
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
          if i != 0 && !(← get).fresh && spent F Mf (← get) then
            laySt none
            let lr := lastRootPlain (← get).cols
            y := lr.1
            x0 := lr.2
            modify fun c => { c with level := lr.1 - 1 }
          modify fun c => { c with cols := c.cols.push ⟨x0 + 1, y, true⟩ }
          blockF F Mf F (ato e) (x0 + 2) (y - 1) false none 0
          i := i + 1
        rootX := x0
      level := level + 1
      prev0 := beta.isEmpty
      if !beta.isEmpty then
        modify fun c => { c with prev := unitTailLevel F beta }
      match (← get).prev, regime with
      | some p, some r =>
        if (lvlO F r).isNone && !laid && cmpOrd F p r == .lt then
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

/-- `TrioRules.MpsiLevel` with fuel `F`. -/
def MpsiLevel (u X : Od) : Cols :=
  let base := MOmega Mf u
  let y0 := (lastC base).y
  let cols := setLastY base (y0 - 1)
  let x := (lastC base).x + 1
  match lvlO F X with
  | none => #[]
  | some w =>
    if cmpOrd F w u == .eq then cols.push ⟨x, y0, false⟩
    else appendSuffix F Mf (cols ++ writeLevel Mf w x (y0 - 1) true [Mf u, cols]) w 0 none

/-- `TrioRules.finish` with fuel `F`. -/
def finish (alpha : Od) (ctx : Ctx) : Cols :=
  match tailLevel F alpha with
  | some t => appendSuffix F Mf ctx.cols t ctx.storeys ctx.tailSub
  | none => ctx.cols

/-- `TrioRules.Mstep` with fuel `F`. -/
def Mstep (alpha : Od) : Cols :=
  match lvlO F alpha with
  | none => finish F Mf alpha (placeUnits F Mf #[] alpha 0 (-1) none)
  | some v =>
    match isPsiLevel F alpha with
    | some uX => MpsiLevel F Mf uX.1 uX.2
    | none =>
      if alpha == [(.W v, 1)] then MOmega Mf v
      else
        let base := MOmega Mf v
        let ya := lastRoot base
        finish F Mf alpha (placeUnits F Mf base alpha ya.1 (ya.2 - 1) (some v))

end

/-- `TrioRules.Mfuel` with fuel `F` in every step. -/
def Mfuel : Nat → Od → Cols
  | 0, _ => #[]
  | n + 1, a => Mstep F (Mfuel n) a

/-- `TrioRules.M` with fuel `F`. -/
def M (alpha : Od) : Cols := Mfuel F F alpha

/-- `TrioRules.ofTerm` with fuel `F` (in the `add` that groups the summands). -/
def ofTerm : Term → Od
  | nil => []
  | cons a b t =>
    let s : Od :=
      if a == nil then
        (if b == nil then one else if omegaFree b then wpow (ofTerm b)
         else [(.psi [] (ofTerm b), 1)])
      else if b == nil then [(.W (ofTerm a), 1)]
      else [(.psi (ofTerm a) (ofTerm b), 1)]
    add F s (ofTerm t)

/-- **Rules 1–10 with fuel `F`**: `TrioRules.trioMatrixL` with `F` for `200`. -/
def trioMatrixF (α : Term) : List (List Nat) := toRows (M F (ofTerm F α))

end

open Googology.Trans.BMS.TrioRulesE0 (dep)

/-- **Rules 1–10 with the fuel taken from the depth**: fuel `dep α + 1`. -/
def trioMatrixD (α : Term) : List (List Nat) := trioMatrixF (dep α + 1) α

/-! ### At fuel `200` it is `TrioRules`' program -/

theorem lvl_200 : lvl 200 = TrioRules.lvl := rfl
theorem lvlO_200 : lvlO 200 = TrioRules.lvlO := rfl
theorem cmpOrd_200 : cmpOrd 200 = TrioRules.cmpOrd := rfl
theorem cmpExp_200 : cmpExp 200 = TrioRules.cmpExp := rfl

theorem add_200 : add 200 = TrioRules.add := rfl
theorem strip_200 : strip 200 = TrioRules.strip := rfl

theorem tailBlockF_200 : ∀ n, tailBlockF 200 n = TrioRules.tailBlockF n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    funext g arg
    simp only [tailBlockF, TrioRules.tailBlockF, ih, strip_200, lvl_200]
    rfl

theorem tailBlock_200 : tailBlock 200 = TrioRules.tailBlock := by
  funext g arg
  simp only [tailBlock, TrioRules.tailBlock, tailBlockF_200]; rfl

theorem unitTailLevel_200 : unitTailLevel 200 = TrioRules.unitTailLevel := by
  funext b; simp only [unitTailLevel, TrioRules.unitTailLevel, tailBlock_200]; rfl

theorem tailLevel_200 : tailLevel 200 = TrioRules.tailLevel := by
  funext a; simp only [tailLevel, TrioRules.tailLevel, unitTailLevel_200]; rfl

theorem isPsiLevel_200 : isPsiLevel 200 = TrioRules.isPsiLevel := rfl
theorem copyStorey_200 : copyStorey 200 = TrioRules.copyStorey := rfl
theorem spent_200 : spent 200 = TrioRules.spent := rfl
theorem appendSuffix_200 : appendSuffix 200 = TrioRules.appendSuffix := rfl

theorem blockF_200 (Mf : Od → Cols) : ∀ n, blockF 200 Mf n = TrioRules.blockF Mf n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    funext g x d arg plvl py
    simp only [blockF, TrioRules.blockF, ih, spent_200, lvl_200, cmpOrd_200, lvlO_200, strip_200,
      tailBlock_200]
    rfl

theorem placeUnits_200 : placeUnits 200 = TrioRules.placeUnits := by
  funext Mf cols alpha l r reg
  simp only [placeUnits, TrioRules.placeUnits, blockF_200, spent_200, lvlO_200, cmpOrd_200,
    copyStorey_200, unitTailLevel_200]
  rfl

theorem MpsiLevel_200 : MpsiLevel 200 = TrioRules.MpsiLevel := by
  funext Mf u X
  unfold MpsiLevel TrioRules.MpsiLevel
  rw [lvlO_200, cmpOrd_200, appendSuffix_200]
  cases TrioRules.lvlO X with
  | none => rfl
  | some w => rfl

theorem finish_200 : finish 200 = TrioRules.finish := by
  funext Mf a c; simp only [finish, TrioRules.finish, tailLevel_200, appendSuffix_200]; rfl

theorem Mstep_200 : Mstep 200 = TrioRules.Mstep := by
  funext Mf a
  simp only [Mstep, TrioRules.Mstep, lvlO_200, isPsiLevel_200, MpsiLevel_200, finish_200,
    placeUnits_200]
  rfl

theorem Mfuel_200 : ∀ n, Mfuel 200 n = TrioRules.Mfuel n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => funext a; simp only [Mfuel, TrioRules.Mfuel, ih, Mstep_200]

/-- **At fuel `200` the builder is `TrioRules.M`.** -/
theorem M_200 : M 200 = TrioRules.M := by
  funext a; simp only [M, TrioRules.M, Mfuel_200]; rfl

/-- **At fuel `200` the reading of terms is `TrioRules.ofTerm`.** -/
theorem ofTerm_200 : ∀ α, ofTerm 200 α = TrioRules.ofTerm α := by
  intro α
  induction α with
  | nil => rfl
  | cons a b t iha ihb iht => simp only [ofTerm, TrioRules.ofTerm, iha, ihb, iht, add_200]

/-- **At fuel `200` the map is `TrioRules.trioMatrixL`.** -/
theorem trioMatrixF_200 : trioMatrixF 200 = TrioRules.trioMatrixL := by
  funext α
  simp only [trioMatrixF, TrioRules.trioMatrixL, TrioRules.trioRuleMatrix, M_200, ofTerm_200]

/-! ### Below `ε₀`, with fuel `F`

The proof of `TrioRulesE0.lean` with `200` replaced by `F` and `201` by
`F + 1`.  The lemmas there that do not read the fuel (the order on terms, the
state-monad calculus `Spec`, the columns `prO` and the add units) are used as
they are. -/

open Googology.Trans.BMS (AllNil DescAll trioMatrix omegaIndexMatrix)
open Googology.Trans.BMS (unread unread_nil unread_cons prSS mulUnits addUnits bodyU peelOne
  isFiniteT dropLastT WF3 WF3_omegaIndexMatrix)
open Googology.Trans.BMS.TrioRulesE0 (exps expandG GDesc H lexc omegaFree_of_allNil cmp_allNil
  cmpOrdWith_nil_nil cmpOrdWith_nil_cons cmpOrdWith_cons_nil cmpOrdWith_cons GDesc_tail GDesc_pos
  GDesc_head_pos GDesc_next mem_expandG lexc_rep mem_exps H_tail dep_eq_zero cmpF_nil_nil
  cmp_le_of_desc GDesc_bump Spec spec_pure spec_mono spec_bind spec_get_bind spec_forIn prO
  spec_pure_bind spec_modify0_bind spec_modify_bind spec_bind_last spec_push_bind unread_shift
  unread_exps flatMap_range'_const isFiniteT_eq exps_dropLastT cmp_nil_ne_lt units_nat predBetaSpec
  toCol colsOf toRows_colsOf nrp nlx addUnits_split Tup run_bind' run_modify_bind run_get_bind
  run_pure_bind run_pure' lastC_push lastC_append_two hf_of_spec mulUnits_exps)

section
variable (F : Nat)

/-- An exponent read with fuel `F`. -/
def ex (b : Term) : Ex := .o (ofTerm F b)

/-- Grouped exponents as a normal form, read with fuel `F`. -/
def grp (L : List (Term × Nat)) : Od := L.map (fun p => (ex F p.1, p.2))

/-- `ofTerm F x` lists the exponents of `x` with their multiplicities, strictly
decreasing. -/
def Inv (x : Term) : Prop := ∃ L, GDesc L ∧ ofTerm F x = grp F L ∧ expandG L = exps x

/-- Standard, of depth at most `F + 1`. -/
def Good (x : Term) : Prop := H x ∧ dep x ≤ F + 1

end

section
variable {F : Nat}

theorem ofTerm_cons (b t : Term) (hb : AllNil b) :
    ofTerm F (cons nil b t) = add F [(ex F b, 1)] (ofTerm F t) := by
  by_cases h : b = nil
  · subst h; simp [ofTerm, one, nat, ex]
  · simp [ofTerm, h, omegaFree_of_allNil b hb, wpow, ex]

theorem cmpExpWith_ex (c : Od → Od → Ordering) (p q : Term) :
    cmpExpWith c (ex F p) (ex F q) = c (ofTerm F p) (ofTerm F q) := rfl

theorem lexc_grp (c : Od → Od → Ordering) :
    ∀ L1 L2 : List (Term × Nat), GDesc L1 → GDesc L2 →
      (∀ p ∈ L1, ∀ q ∈ L2, c (ofTerm F p.1) (ofTerm F q.1) = Term.cmp p.1 q.1) →
      cmpOrdWith c (grp F L1) (grp F L2) = lexc (expandG L1) (expandG L2) := by
  intro L1
  induction L1 with
  | nil =>
    intro L2 _ h2 _
    cases L2 with
    | nil => simp [grp, expandG, cmpOrdWith_nil_nil, lexc]
    | cons q r =>
      have hq := GDesc_head_pos h2
      obtain ⟨k, hk⟩ : ∃ k, q.2 = k + 1 := ⟨q.2 - 1, by omega⟩
      simp [grp, expandG, cmpOrdWith_nil_cons, hk, List.replicate_succ, lexc]
  | cons p r ih =>
    intro L2 h1 h2 hc
    cases L2 with
    | nil =>
      have hp := GDesc_head_pos h1
      obtain ⟨k, hk⟩ : ∃ k, p.2 = k + 1 := ⟨p.2 - 1, by omega⟩
      simp [grp, expandG, cmpOrdWith_cons_nil, hk, List.replicate_succ, lexc]
    | cons q s =>
      have ihr := ih s (GDesc_tail h1) (GDesc_tail h2)
        (fun p' hp' q' hq' => hc p' (List.mem_cons_of_mem _ hp') q' (List.mem_cons_of_mem _ hq'))
      have hpq := hc p List.mem_cons_self q List.mem_cons_self
      have e1 : grp F (p :: r) = (ex F p.1, p.2) :: grp F r := rfl
      have e2 : grp F (q :: s) = (ex F q.1, q.2) :: grp F s := rfl
      have f1 : expandG (p :: r) = List.replicate p.2 p.1 ++ expandG r := by
        simp [expandG]
      have f2 : expandG (q :: s) = List.replicate q.2 q.1 ++ expandG s := by
        simp [expandG]
      rw [e1, e2, cmpOrdWith_cons, cmpExpWith_ex, hpq, ihr, f1, f2]
      have hp := GDesc_head_pos h1
      have hq := GDesc_head_pos h2
      obtain ⟨k, hk⟩ : ∃ k, p.2 = k + 1 := ⟨p.2 - 1, by omega⟩
      obtain ⟨k', hk'⟩ : ∃ k, q.2 = k + 1 := ⟨q.2 - 1, by omega⟩
      cases hcm : Term.cmp p.1 q.1 with
      | lt =>
        simp [hk, hk', List.replicate_succ, lexc, hcm, Ordering.then]
      | gt =>
        simp [hk, hk', List.replicate_succ, lexc, hcm, Ordering.then]
      | eq =>
        have he : p.1 = q.1 := cmp_eq_iff.mp hcm
        rw [he, lexc_rep q.1 (expandG r) (expandG s) (he ▸ GDesc_next h1) (GDesc_next h2)]
        rfl

/-- **`cmpF` is the term order**, on the grouped normal forms, with enough fuel. -/
theorem cmpF_ofTerm : ∀ m n : Nat, m ≤ n → (∀ x, H x → dep x ≤ m → Inv F x) →
    ∀ a b : Term, H a → H b → dep a ≤ m → dep b ≤ m →
      cmpF n (ofTerm F a) (ofTerm F b) = Term.cmp a b := by
  intro m
  induction m with
  | zero =>
    intro n _ _ a b _ _ ha hb
    rw [dep_eq_zero (Nat.le_zero.mp ha), dep_eq_zero (Nat.le_zero.mp hb)]
    exact cmpF_nil_nil n
  | succ m ih =>
    intro n hmn hinv a b hHa hHb ha hb
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    obtain ⟨L1, hG1, hO1, hE1⟩ := hinv a hHa ha
    obtain ⟨L2, hG2, hO2, hE2⟩ := hinv b hHb hb
    show cmpOrdWith (cmpF n') (ofTerm F a) (ofTerm F b) = _
    rw [hO1, hO2, lexc_grp _ L1 L2 hG1 hG2, hE1, hE2, cmp_allNil a b hHa.1 hHb.1]
    intro p hp q hq
    have hp' := mem_exps a p.1 (hE1 ▸ mem_expandG hG1 hp) hHa
    have hq' := mem_exps b q.1 (hE2 ▸ mem_expandG hG2 hq) hHb
    exact ih n' (by omega) (fun x hx hd => hinv x hx (by omega)) p.1 q.1 hp'.1 hq'.1
      (by omega) (by omega)

theorem add_gt {x lead : Ex} {cb : Nat} {bt : Od} (h : cmpExp F x lead = .gt) :
    add F [(x, 1)] ((lead, cb) :: bt) = (x, 1) :: (lead, cb) :: bt := by
  simp [add, h]

theorem add_eq {x lead : Ex} {cb : Nat} {bt : Od} (h : cmpExp F x lead = .eq) :
    add F [(x, 1)] ((lead, cb) :: bt) = (lead, 1 + cb) :: bt := by
  simp [add, h]

/-- **`ofTerm F` groups the summands** on a standard term of depth at most
`F + 1`. -/
theorem inv_all : ∀ m : Nat, m ≤ F + 1 → ∀ x, H x → dep x ≤ m → Inv F x := by
  intro m
  induction m with
  | zero =>
    intro _ x _ hx
    rw [dep_eq_zero (Nat.le_zero.mp hx)]
    exact ⟨[], trivial, rfl, rfl⟩
  | succ m ih =>
    intro hm x
    have hQ := ih (by omega)
    induction x with
    | nil => intro _ _; exact ⟨[], trivial, rfl, rfl⟩
    | cons a b t _ _ iht =>
      intro hH hd
      obtain ⟨⟨ha, hAb, hAt⟩, hDb, hDt, _⟩ := hH
      subst ha
      have hdt : dep t ≤ m + 1 := by simp only [dep] at hd; omega
      have hdb : dep b ≤ m := by simp only [dep] at hd; omega
      obtain ⟨Lt, hGt, hOt, hEt⟩ := iht ⟨hAt, hDt⟩ hdt
      unfold Inv
      rw [ofTerm_cons b t hAb, hOt]
      cases Lt with
      | nil =>
        refine ⟨[(b, 1)], by simp [GDesc], rfl, ?_⟩
        simp [expandG, exps] at hEt ⊢
        exact hEt
      | cons p L' =>
        obtain ⟨d, k⟩ := p
        have hk : 0 < k := GDesc_head_pos hGt
        obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        cases t with
        | nil => simp [expandG, exps, List.replicate_succ] at hEt
        | cons a' d' t' =>
          have hd' : d' = d := by
            simp [expandG, exps, List.replicate_succ] at hEt; exact hEt.1.symm
          subst hd'
          have ha' : a' = nil := hAt.1
          subst ha'
          have hle : Term.cmp d' b ≠ .gt := cmp_le_of_desc ⟨hDb, hDt, ‹_›⟩
          have hdd : dep d' ≤ m := by simp only [dep] at hdt; omega
          have hc : cmpExp F (ex F b) (ex F d') = Term.cmp b d' :=
            cmpF_ofTerm m F (by omega) hQ b d' ⟨hAb, hDb⟩
              ⟨hAt.2.1, hDt.1⟩ hdb hdd
          have hsw := cmp_swap b d'
          cases hbd : Term.cmp b d' with
          | lt => rw [hbd] at hsw; exact absurd hsw.symm hle
          | gt =>
            rw [hbd] at hc hsw
            refine ⟨(b, 1) :: (d', k' + 1) :: L', ⟨by omega, hsw.symm, hGt⟩, ?_, ?_⟩
            · exact add_gt hc
            · simp only [expandG, List.flatMap_cons, exps] at hEt ⊢
              rw [hEt]; rfl
          | eq =>
            rw [hbd] at hc
            have hb : b = d' := cmp_eq_iff.mp hbd
            subst hb
            refine ⟨(b, 1 + (k' + 1)) :: L', GDesc_bump hGt, add_eq hc, ?_⟩
            simp only [expandG, List.flatMap_cons, exps] at hEt ⊢
            rw [show 1 + (k' + 1) = (k' + 1) + 1 by omega, List.replicate_succ, List.cons_append,
              hEt]

theorem Good.inv {x : Term} (h : Good F x) : Inv F x := inv_all (F + 1) (le_refl _) x h.1 h.2

theorem Good.of_mem {x p : Term} (h : Good F x) (hp : p ∈ exps x) : Good F p :=
  let h' := mem_exps x p hp h.1
  ⟨h'.1, by have := h.2; omega⟩

theorem Good.mem_grp {x : Term} {L : List (Term × Nat)} (h : Good F x) (hG : GDesc L)
    (hE : expandG L = exps x) {p : Term × Nat} (hp : p ∈ L) : Good F p.1 :=
  h.of_mem (hE ▸ mem_expandG hG hp)

theorem lvlF_ex : ∀ (n : Nat) (x : Term), Good F x → lvlF n (ex F x) = none := by
  intro n
  induction n with
  | zero => intro _ _; rfl
  | succ n ih =>
    intro x hx
    obtain ⟨L, hG, hO, hE⟩ := hx.inv
    show lvlF (n + 1) (.o (ofTerm F x)) = none
    rw [hO]
    cases L with
    | nil => rfl
    | cons p L' =>
      show lvlF n (ex F p.1) = none
      exact ih p.1 (hx.mem_grp hG hE List.mem_cons_self)

theorem lvl_ex {G : Nat} {x : Term} (hx : Good F x) : lvl G (ex F x) = none := lvlF_ex _ x hx

theorem ato_ex (x : Term) : ato (ex F x) = ofTerm F x := rfl

theorem strip_ex {G : Nat} {x : Term} (hx : Good F x) : strip G (ex F x) = ofTerm F x := by
  obtain ⟨L, hG, hO, hE⟩ := hx.inv
  unfold strip
  rw [ato_ex, hO]
  cases L with
  | nil => rfl
  | cons p L' => rfl

theorem spent_none (Mf : Od → Cols) (c : Ctx) (h : c.regime = none) : spent F Mf c = false := by
  unfold spent; rw [h]; split <;> simp_all

theorem blockF_spec (Mf : Od → Cols) : ∀ (n : Nat) (g : Term) (x d : Int) (arg : Bool)
    (plvl : Option Od) (py : Int), Good F g →
    Spec (blockF F Mf n (ofTerm F g) x d arg plvl py) (fun _ => True)
      (prO n x (ofTerm F g)).toArray := by
  intro n
  induction n with
  | zero => intro g x d arg plvl py _; simpa [blockF, prO] using spec_pure (Q := fun _ : Unit => True) trivial
  | succ n ih =>
    intro g x d arg plvl py hg
    obtain ⟨L, hG, hO, hE⟩ := hg.inv
    simp only [blockF]
    refine spec_bind (spec_mono (spec_forIn (ofTerm F g) _ (fun r : MProd Int Int => r = ⟨d, x⟩)
      (fun ec => (List.range' 0 ec.2).flatMap fun _ => ⟨x, 0, false⟩ :: prO n (x + 1) (ato ec.1))
      ?_ (⟨d, x⟩ : MProd Int Int) rfl) (fun _ _ => trivial)) (fun _ _ => spec_pure trivial) (by simp [prO])
    intro ec hec b hb
    subst hb
    rw [hO] at hec
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hec
    have hgp := hg.mem_grp hG hE hp
    simp only [lvl_ex hgp, strip_ex hgp, ato_ex]
    rw [Std.Legacy.Range.forIn_eq_forIn_range']
    refine spec_bind (w2 := #[]) (spec_forIn _ _ (fun r : MProd Int Int => r = ⟨d, x⟩)
      (fun _ => ⟨x, 0, false⟩ :: prO n (x + 1) (ofTerm F p.1)) ?_ (⟨d, x⟩ : MProd Int Int) rfl)
      (fun r hr => ?_) ?_
    · intro i _ b hb
      subst hb
      refine spec_get_bind fun s1 _ => spec_get_bind fun s2 hs2 => ?_
      rw [spent_none Mf s2 hs2]
      simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      rw [show (({ x := x, y := 0, z := false } :: prO n (x + 1) (ofTerm F p.1)).toArray :
          Array TrioRules.Col) = #[⟨x, 0, false⟩] ++ (prO n (x + 1) (ofTerm F p.1)).toArray by simp]
      repeat trioE0_step
      rw [spent_none Mf _ ‹_›]
      simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      repeat trioE0_step
      refine spec_bind_last (ih p.1 _ _ _ _ _ hgp) (fun _ _ => ?_)
      repeat trioE0_step
    · subst hr
      repeat trioE0_step
    · simp [Std.Legacy.Range.size]

theorem grp_flatMap {β : Type} (G : Od → List β) : ∀ L : List (Term × Nat),
    (grp F L).flatMap (fun ec => (List.range' 0 ec.2).flatMap (fun _ => G (ato ec.1))) =
      (expandG L).flatMap (fun b => G (ofTerm F b)) := by
  intro L
  induction L with
  | nil => rfl
  | cons p L ih =>
    simp only [grp, List.map_cons] at ih ⊢
    rw [List.flatMap_cons, ih, flatMap_range'_const]
    simp only [expandG, List.flatMap_cons, List.flatMap_append]
    congr 1
    simp only [ato_ex]
    generalize p.2 = k
    induction k with
    | zero => rfl
    | succ k ihk => simp [List.replicate_succ, List.flatMap_cons, ihk]

/-- **`blockF` writes the one-row matrix of the exponent** when the fuel covers
the depth. -/
theorem prO_ofTerm : ∀ (n : Nat) (g : Term) (x : Int), Good F g → dep g ≤ n →
    prO n x (ofTerm F g) =
      (unread 0 g).map (fun e : Nat => (⟨x + (e : Int), 0, false⟩ : TrioRules.Col)) := by
  intro n
  induction n with
  | zero =>
    intro g x _ hd
    rw [dep_eq_zero (Nat.le_zero.mp hd)]; rfl
  | succ n ih =>
    intro g x hg hd
    obtain ⟨L, hG, hO, hE⟩ := hg.inv
    show (ofTerm F g).flatMap _ = _
    rw [hO, grp_flatMap (fun A => (⟨x, 0, false⟩ : TrioRules.Col) :: prO n (x + 1) A) L, hE,
      unread_exps g 0, List.map_flatMap]
    apply List.flatMap_congr
    intro b hb
    have hb' := mem_exps g b hb hg.1
    rw [ih b (x + 1) (hg.of_mem hb) (by omega), unread_shift b 1, List.map_cons, List.map_map]
    simp only [Nat.cast_zero, add_zero, Function.comp_def, Nat.cast_add, Nat.cast_one]
    congr 1
    apply List.map_congr_left
    intro e _
    congr 1
    omega

theorem units_grp (L : List (Term × Nat)) : units (grp F L) = (expandG L).map (ex F) := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    simp only [units, grp, List.map_cons, List.flatMap_cons, expandG, List.map_append,
      List.map_replicate] at ih ⊢
    rw [ih]

theorem units_ofTerm {x : Term} (hx : Good F x) : units (ofTerm F x) = (exps x).map (ex F) := by
  obtain ⟨L, _, hO, hE⟩ := hx.inv
  rw [hO, units_grp, hE]

theorem ofTerm_eq_nil_iff {x : Term} (hx : Good F x) : ofTerm F x = [] ↔ x = nil := by
  obtain ⟨L, hG, hO, hE⟩ := hx.inv
  constructor
  · intro h
    rw [hO] at h
    have hL : L = [] := List.map_eq_nil_iff.mp h
    subst hL
    cases x with
    | nil => rfl
    | cons _ _ _ => simp [expandG, exps] at hE
  · rintro rfl; rfl

theorem predBeta_ofTerm {e : Term} (he : Good F e) (hne : e ≠ nil) :
    units (predBeta (ofTerm F e)) = (exps (peelOne e)).map (ex F) ∧
      (∀ g ∈ exps (peelOne e), Good F g) ∧
      (∀ q ∈ (predBeta (ofTerm F e)).getLast?, ∃ g, Good F g ∧ q.1 = ex F g) := by
  obtain ⟨L, hG, hO, hE⟩ := he.inv
  cases L with
  | nil =>
    exfalso; apply hne
    cases e with
    | nil => rfl
    | cons _ _ _ => simp [expandG, exps] at hE
  | cons p L' =>
    obtain ⟨b0, k⟩ := p
    have hb0 : Good F b0 := he.mem_grp hG hE List.mem_cons_self
    rw [hO]
    show units (predBeta ((.o (ofTerm F b0), k) :: grp F L')) = _ ∧ _ ∧
      ∀ q ∈ (predBeta ((.o (ofTerm F b0), k) :: grp F L')).getLast?, _
    rw [predBetaSpec]
    by_cases hb : b0 = nil
    · subst hb
      have hL' : L' = [] := by
        cases L' with
        | nil => rfl
        | cons q r => exact absurd hG.2.1 (cmp_nil_ne_lt _)
      subst hL'
      have hex : exps e = List.replicate k nil := by
        rw [← hE]; simp [expandG]
      have hfin : isFiniteT e = true := by
        rw [isFiniteT_eq, hex]; simp
      have hpe : exps (peelOne e) = List.replicate (k - 1) nil := by
        rw [peelOne, hfin, if_pos rfl, exps_dropLastT, hex]
        simp
      simp only [ofTerm, List.isEmpty_nil, ↓reduceIte, hpe]
      refine ⟨by rw [units_nat, List.map_replicate]; rfl, ?_, ?_⟩
      · intro g hg
        rw [(List.mem_replicate.mp hg).2]
        exact ⟨⟨trivial, trivial⟩, by simp [dep]⟩
      · intro q hq
        refine ⟨nil, ⟨⟨trivial, trivial⟩, by simp [dep]⟩, ?_⟩
        unfold nat at hq
        split at hq
        · simp at hq
        · simp at hq; rw [← hq]; rfl
    · have hne' : (ofTerm F b0).isEmpty = false := by
        cases h : ofTerm F b0 with
        | nil => exact absurd ((ofTerm_eq_nil_iff hb0).mp h) hb
        | cons _ _ => rfl
      have hfin : isFiniteT e = false := by
        have hk := GDesc_head_pos hG
        obtain ⟨k', hk'⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp at hk; omega⟩
        rw [isFiniteT_eq, ← hE, hk']
        simp [expandG, List.replicate_succ, hb]
      have hpe : peelOne e = e := by rw [peelOne, hfin]; rfl
      simp only [hne', Bool.false_eq_true, ↓reduceIte, hpe]
      have h1 : ((Ex.o (ofTerm F b0), k) :: grp F L') = grp F ((b0, k) :: L') := rfl
      rw [h1, units_grp, hE]
      refine ⟨rfl, fun g hg => he.of_mem hg, ?_⟩
      intro q hq
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (List.mem_of_getLast? hq)
      exact ⟨p.1, he.mem_grp hG hE hp, rfl⟩

theorem tailBlockF_ofTerm {G : Nat} : ∀ (n : Nat) (g : Term) (arg : Bool), Good F g →
    tailBlockF G n (ofTerm F g) arg = none := by
  intro n
  induction n with
  | zero => intro _ _ _; rfl
  | succ n ih =>
    intro g arg hg
    obtain ⟨L, hG, hO, hE⟩ := hg.inv
    unfold tailBlockF
    split
    · rfl
    · rename_i e c hlast
      rw [hO] at hlast
      obtain ⟨p, hp, hpe⟩ := List.mem_map.mp (List.mem_of_getLast? hlast)
      have hgp := hg.mem_grp hG hE hp
      simp only [Prod.mk.injEq] at hpe
      rw [← hpe.1, strip_ex hgp]
      dsimp only
      by_cases hr : (ofTerm F p.1).isEmpty = true
      · simp only [hr, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        split
        · rfl
        · exact lvl_ex hgp
      · simp only [hr, Bool.not_false, ↓reduceIte]
        exact ih _ _ hgp

theorem tailLevel_ofTerm {α : Term} (hα : Good F α) : tailLevel F (ofTerm F α) = none := by
  unfold tailLevel
  rw [units_ofTerm hα]
  split
  · rfl
  · rename_i b hb
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp (List.mem_of_getLast? hb)
    have hge := hα.of_mem he
    unfold unitTailLevel
    rw [ato_ex]
    by_cases hn : e = nil
    · subst hn; rfl
    · have hne : (ofTerm F e).isEmpty = false := by
        cases h : ofTerm F e with
        | nil => exact absurd ((ofTerm_eq_nil_iff hge).mp h) hn
        | cons _ _ => rfl
      obtain ⟨_, _, hlast⟩ := predBeta_ofTerm hge hn
      simp only [hne, Bool.false_or]
      split
      · rfl
      · split
        · rename_i e' c' hl
          obtain ⟨g, hg, hq⟩ := hlast _ hl
          simp only at hq
          rw [hq, ato_ex]
          exact tailBlockF_ofTerm _ g false hg
        · rfl

theorem loop_units (f : Ex → Tup → StateM Ctx (ForInStep Tup))
    (hf : ∀ e, Good F e → dep e ≤ F → ∀ (first : Bool) (rp1 lastX : Nat) (pz : Bool) (i : Nat) (s : Ctx),
      1 ≤ i → s.regime = none → (pz = true → lastC s.cols = ⟨lastX, (i : Int) - 1, false⟩) →
      ∃ s', (f (ex F e) ⟨first, (i : Int) - 1, pz, (rp1 : Int) - 1⟩).run s =
          (.yield ⟨false, ((i + 1 : Nat) : Int) - 1, e == nil, ((nrp e rp1 : Nat) : Int) - 1⟩, s') ∧
        s'.cols = s.cols ++ (colsOf (addUnits rp1 lastX pz i (cons nil e nil))).toArray ∧
        s'.regime = none ∧
        (e = nil → lastC s'.cols = ⟨nlx e rp1 lastX pz, ((i + 1 : Nat) : Int) - 1, false⟩)) :
    ∀ t : Term, Good F t → ∀ (first : Bool) (rp1 lastX : Nat) (pz : Bool) (i : Nat) (s : Ctx),
      1 ≤ i → s.regime = none → (pz = true → lastC s.cols = ⟨lastX, (i : Int) - 1, false⟩) →
      ∃ r s', (forIn ((exps t).map (ex F)) (⟨first, (i : Int) - 1, pz, (rp1 : Int) - 1⟩ : Tup) f).run s
          = (r, s') ∧
        s'.cols = s.cols ++ (colsOf (addUnits rp1 lastX pz i t)).toArray ∧ s'.regime = none := by
  intro t
  induction t with
  | nil =>
    intro _ first rp1 lastX pz i s _ hs _
    exact ⟨_, s, rfl, by simp [addUnits, colsOf], hs⟩
  | cons a e t _ _ iht =>
    intro hg first rp1 lastX pz i s hi hs hl
    have ha : a = nil := hg.1.1.1
    subst ha
    have hge : Good F e := hg.of_mem (List.mem_cons_self)
    have hgt : Good F t := ⟨H_tail hg.1, by have := hg.2; simp only [dep] at this; omega⟩
    have hde : dep e ≤ F := by have := hg.2; simp only [dep] at this; omega
    obtain ⟨s1, h1, hc1, hr1, hl1⟩ := hf e hge hde first rp1 lastX pz i s hi hs hl
    obtain ⟨r, s2, h2, hc2, hr2⟩ := iht hgt false (nrp e rp1) (nlx e rp1 lastX pz) (e == nil) (i + 1)
      s1 (by omega) hr1 (fun h => hl1 (by simpa using h))
    refine ⟨r, s2, ?_, ?_, hr2⟩
    · simp only [exps, List.map_cons, List.forIn_cons]
      rw [run_bind', h1]
      push_cast at h2 ⊢
      exact h2
    · rw [hc2, hc1, addUnits_split rp1 lastX pz i nil e t]
      simp [colsOf, Array.append_assoc]

theorem colsOf_prSS (x : Nat) (g : Term) (hg : Good F g) (hd : dep g ≤ F) :
    colsOf (prSS x g) = prO F (x : Int) (ofTerm F g) := by
  rw [prO_ofTerm F g x hg hd, colsOf, prSS, List.map_map]
  apply List.map_congr_left
  intro e _
  simp [toCol]

theorem run_loop (α : Term) (hα : Good F α) (f : Ex → Tup → StateM Ctx (ForInStep Tup))
    (hf : ∀ e, Good F e → dep e ≤ F → ∀ (first : Bool) (rp1 lastX : Nat) (pz : Bool) (i : Nat) (s : Ctx),
      1 ≤ i → s.regime = none → (pz = true → lastC s.cols = ⟨lastX, (i : Int) - 1, false⟩) →
      ∃ s', (f (ex F e) ⟨first, (i : Int) - 1, pz, (rp1 : Int) - 1⟩).run s =
          (.yield ⟨false, ((i + 1 : Nat) : Int) - 1, e == nil, ((nrp e rp1 : Nat) : Int) - 1⟩, s') ∧
        s'.cols = s.cols ++ (colsOf (addUnits rp1 lastX pz i (cons nil e nil))).toArray ∧
        s'.regime = none ∧
        (e = nil → lastC s'.cols = ⟨nlx e rp1 lastX pz, ((i + 1 : Nat) : Int) - 1, false⟩))
    (S : Ctx) (hS : S.regime = none) (hS0 : S.cols = #[]) :
    (StateT.run (pure PUnit.unit >>= fun _ =>
        forIn ((exps α).map (ex F)) (⟨true, 0, false, -1⟩ : Tup) f >>= fun _ => pure PUnit.unit) S).2.cols =
      (colsOf (addUnits 0 0 false 1 α)).toArray := by
  obtain ⟨r, s', hrun, hc, -⟩ := loop_units f hf α hα true 0 0 false 1 S le_rfl hS (by simp)
  have e1 : (⟨true, 0, false, -1⟩ : Tup) = ⟨true, ((1 : Nat) : Int) - 1, false, ((0 : Nat) : Int) - 1⟩ := rfl
  have key : (StateT.run (pure PUnit.unit >>= fun _ =>
        forIn ((exps α).map (ex F)) (⟨true, 0, false, -1⟩ : Tup) f >>= fun _ => pure PUnit.unit) S) =
      (PUnit.unit, s') := by
    rw [run_bind']
    show (forIn ((exps α).map (ex F)) (⟨true, 0, false, -1⟩ : Tup) f >>= fun _ => pure PUnit.unit).run S = _
    rw [run_bind', e1, hrun]
    rfl
  rw [key]
  show s'.cols = _
  rw [hc, hS0]; simp

theorem placeUnits_ofTerm (Mf : Od → Cols) (α : Term) (hα : Good F α) :
    (placeUnits F Mf #[] (ofTerm F α) 0 (-1) none).cols = (colsOf (addUnits 0 0 false 1 α)).toArray := by
  unfold placeUnits
  simp only [Option.bind_none, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, List.drop_zero,
    units_ofTerm hα]
  refine run_loop α hα _ ?_ _ rfl rfl
  intro e he hde first rp1 lastX pz i s hi hs hl
  have hsp : ∀ c : Ctx, c.regime = s.regime → spent F Mf c = false := fun c hc =>
    spent_none Mf c (hc.trans hs)
  by_cases he0 : e = nil
  · subst he0
    cases pz
    · simp (disch := exact rfl) only [run_modify_bind, run_get_bind, run_pure_bind, ato_ex, ofTerm,
        List.isEmpty_nil, hsp, Bool.and_false, Bool.false_eq_true, ↓reduceIte, Bool.not_true]
      rw [run_pure']
      refine ⟨_, Prod.ext ?_ rfl, ?_, hs, ?_⟩
      · simp only [nrp, beq_self_eq_true, ↓reduceIte, ForInStep.yield.injEq, MProd.mk.injEq, true_and, and_true]
        omega
      · simp [addUnits, colsOf, toCol]
        push_cast [Nat.cast_sub hi]
        ring_nf
      · intro _
        rw [lastC_append_two]
        simp [nlx]
        ring
    · have hl' := hl rfl
      simp (disch := exact rfl) only [run_modify_bind, run_get_bind, run_pure_bind, ato_ex, ofTerm,
        List.isEmpty_nil, hsp, Bool.and_false, Bool.false_eq_true, ↓reduceIte, Bool.not_true,
        Bool.and_self, hl']
      split
      · next p r h1 h2 => simp at h2
      simp only [run_pure_bind, run_pure']
      refine ⟨_, Prod.ext ?_ rfl, ?_, hs, ?_⟩
      · simp only [nrp, beq_self_eq_true, ↓reduceIte, ForInStep.yield.injEq, MProd.mk.injEq, true_and,
          and_true]
        omega
      · simp [addUnits, colsOf, toCol]
      · intro _
        rw [lastC_push]
        simp [nlx]
  · have hE : (ofTerm F e).isEmpty = false := by
      cases h : ofTerm F e with
      | nil => exact absurd ((ofTerm_eq_nil_iff he).mp h) he0
      | cons _ _ => rfl
    obtain ⟨hunits, hgood, -⟩ := predBeta_ofTerm he he0
    have hsub : ∀ g ∈ exps (peelOne e), g ∈ exps e := by
      intro g hg
      unfold peelOne at hg
      split at hg
      · rw [exps_dropLastT] at hg; exact List.mem_of_mem_dropLast hg
      · exact hg
    have hdep : ∀ g ∈ exps (peelOne e), dep g ≤ F := by
      intro g hg
      have := (mem_exps e g (hsub g hg) he.1).2
      omega
    let w : Ex → List TrioRules.Col := fun a =>
      ⟨(rp1 : Int) - 1 + 1 + 1 + 1, (i : Int) - 1 + 1, true⟩ ::
        prO F ((rp1 : Int) - 1 + 1 + 1 + 2) (ato a)
    have hW : (colsOf (addUnits rp1 lastX pz i (cons nil e nil))).toArray =
        #[⟨(rp1 : Int) - 1 + 1, (i : Int) - 1, false⟩, ⟨(rp1 : Int) - 1 + 1 + 1, (i : Int) - 1 + 1, true⟩] ++
          (((exps (peelOne e)).map (ex F)).flatMap w).toArray := by
      have hb : (e == nil) = false := by simp [he0]
      simp only [addUnits, hb, Bool.false_eq_true, ↓reduceIte, bodyU, mulUnits_exps, List.append_nil]
      simp only [colsOf, List.map_cons, List.map_flatMap, List.flatMap_map]
      have hfl : (exps (peelOne e)).flatMap
            (fun a => toCol [rp1 + 1 + 1, i, 1] :: List.map toCol (prSS (rp1 + 1 + 2) a)) =
          (exps (peelOne e)).flatMap (fun a => w (ex F a)) := by
        apply List.flatMap_congr
        intro g hg
        rw [show List.map toCol (prSS (rp1 + 1 + 2) g) = colsOf (prSS (rp1 + 1 + 2) g) from rfl,
          colsOf_prSS _ g (hgood g hg) (hdep g hg)]
        simp only [w, ato_ex, toCol, List.getD_cons_zero, List.getD_cons_succ, beq_self_eq_true]
        congr 2
        · push_cast; ring
        · ring
        · push_cast; ring
      rw [hfl]
      apply Array.ext'
      simp [toCol]
      omega
    refine hf_of_spec ?_ hs (fun _ h => absurd h he0)
    rw [hW]
    trioE0_step
    refine spec_get_bind fun s1 hs1 => ?_
    simp only [spent_none Mf s1 hs1, Bool.and_false, Bool.false_eq_true, ↓reduceIte, ato_ex, hE,
      Bool.false_and]
    repeat trioE0_step
    rw [hunits]
    refine spec_bind_last (spec_forIn _ _
      (fun r : MProd Nat (MProd Int Int) => r.snd = ⟨(rp1 : Int) - 1 + 1 + 1, (i : Int) - 1 + 1⟩) w
      ?_ _ rfl) (fun r hr => ?_)
    · intro a ha b hb
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp ha
      obtain ⟨j, x0', y'⟩ := b
      simp only [MProd.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      refine spec_get_bind fun s2 _ => spec_get_bind fun s3 hs3 => ?_
      simp only [spent_none Mf s3 hs3, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      show Spec _ _ (List.toArray (_ :: _))
      rw [List.toArray_cons]
      repeat trioE0_step
      refine spec_bind_last (blockF_spec Mf F g _ _ _ _ _ (hgood g hg)) (fun _ _ => ?_)
      repeat trioE0_step
    · obtain ⟨j, x0', y'⟩ := r
      simp only [MProd.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      simp only [Bool.not_false, ↓reduceIte]
      repeat trioE0_step
      split
      · next p r h1 h2 => simp at h2
      repeat trioE0_step
      refine spec_pure ?_
      have hb : (e == nil) = false := by simp [he0]
      simp only [nrp, he0, ↓reduceIte, hb, ForInStep.yield.injEq, MProd.mk.injEq, true_and]
      omega

theorem M_ofTerm (hF : 1 ≤ F) (α : Term) (hα : Good F α) :
    M F (ofTerm F α) = (colsOf (omegaIndexMatrix α)).toArray := by
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  show Mfuel (F' + 1) (F' + 1) (ofTerm (F' + 1) α) = _
  rw [Mfuel]
  unfold Mstep
  have hl : lvlO (F' + 1) (ofTerm (F' + 1) α) = none := lvl_ex hα
  rw [hl]
  dsimp only
  unfold finish
  rw [tailLevel_ofTerm hα]
  dsimp only
  exact placeUnits_ofTerm _ α hα

/-- **Rules 1–10 with fuel `F` agree with `Trio.lean` below `ε₀`** on every
term with all subscripts `0` and descending principal terms, of depth at most
`F + 1`. -/
theorem trioMatrixF_eq_of_good (hF : 1 ≤ F) (α : Term) (hA : AllNil α) (hD : DescAll α)
    (hd : dep α ≤ F + 1) : trioMatrixF F α = trioMatrix α := by
  rw [Googology.Trans.BMS.TrioStd.trioMatrix_allNil α hA]
  unfold trioMatrixF
  rw [M_ofTerm hF α ⟨⟨hA, hD⟩, hd⟩]
  exact toRows_colsOf _ (WF3_omegaIndexMatrix α)

/-- **The same for every standard form below `ε₀`** of depth at most `F + 1`. -/
theorem trioMatrixF_eq_trioMatrix (hF : 1 ≤ F) (α : Googology.Trans.BMS.exbE0.State)
    (hd : dep α.1 ≤ F + 1) : trioMatrixF F α.1 = trioMatrix α.1 :=
  trioMatrixF_eq_of_good hF α.1 (Googology.Trans.BMS.allNil_of_state α)
    (Googology.Trans.BMS.descAll_of_OT α.1 α.2.1 (Googology.Trans.BMS.allNil_of_state α)) hd

end

/-- **Rules 1–10, fuelled by the depth, agree with `Trio.lean` on every term
with all subscripts `0` and descending principal terms.** -/
theorem trioMatrixD_eq_of_good (α : Term) (hA : AllNil α) (hD : DescAll α) :
    trioMatrixD α = trioMatrix α :=
  trioMatrixF_eq_of_good (by omega) α hA hD (by omega)

/-- **Rules 1–10, fuelled by the depth, agree with `trioMatrix` on every
standard `α < ε₀`**: no depth bound, no hypothesis. -/
theorem trioMatrixD_eq_trioMatrix (α : Googology.Trans.BMS.exbE0.State) :
    trioMatrixD α.1 = trioMatrix α.1 :=
  trioMatrixF_eq_trioMatrix (by omega) α (by omega)

/-! ### Calibration

`TrioRulesE0.lean`'s towers: at depth `203` fuel `200` is one column short,
the depth fuel is not.  These are `#guard`s, checks of the compiled program. -/

open Googology.Trans.BMS.TrioRulesE0 (towerT)

#guard trioMatrixF 200 (towerT 202) ≠ trioMatrix (towerT 202)
#guard trioMatrixD (towerT 202) = trioMatrix (towerT 202)
#guard trioMatrixD (towerT 260) = trioMatrix (towerT 260)

end Googology.Trans.BMS.TrioFuel
