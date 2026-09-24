import Googology.Trans.BMS.TrioFixStrip
import Googology.Trans.BMS.TrioFixFuelE0

/-!
# The patched builder with no regime is a plain builder

`TrioFixStrip.MstepSt` is the merged builder (`TrioRulesAll`: Fixes A–E and N, state
`CtxN`) with the corrected rule 1 (`stripSt`, `uncollapses`).  On a countable `α`
(`lvlO α = none`) there is no regime, and Fixes B–D and N never act.  This file writes the
plain builder that remains, `blockFSt` / `placeUnitsSt` / `finishSt` (copies of
`TrioRules.blockF` / `placeUnits` / `finish` on the state `Ctx`, with `stripSt`,
`uncollapses`, `tailBlockSt`, `unitTailLevelSt` in place of `strip`, `headIsPsi ∘ ato`,
`tailBlock`, `unitTailLevel`), and proves

  `MstepSt_countable`: `lvlO α = none → MstepSt Mf α = finishSt Mf α (placeUnitsSt Mf #[] α 0 (-1) none)`.

The proof is `TrioFixFuelE0.lean`'s simulation (`Sim`), step by step.
-/

namespace Googology.Trans.BMS.TrioFixStripCalib

open Googology.Trans.BMS.TrioRules
open Googology.Trans.BMS.TrioRulesNL (CtxN NState)
open Googology.Trans.BMS.TrioFixStrip
open Googology.Trans.BMS.TrioFixFuelE0 (P SimAt sim_pure sim_bind sim_get_bind sim_get_bind_left
  sim_modify sim_liftC sim_forIn sim_forIn_range sim_ite laySt_pres sim_to_at sim_pure_bind_left
  sim_pure_bind_right run_tail_of_sim)

/-! ### The plain builder with the corrected rule 1 -/

section
variable (Mf : Od → Cols)

/-- `TrioRules.blockF` with `stripSt`, `uncollapses` and `tailBlockSt`. -/
def blockFSt : Nat → Od → Int → Int → Bool → Option Od → Int → StateM Ctx Unit
  | 0, _, _, _, _, _, _ => pure ()
  | n + 1, gamma, x0, d0, arg, plvl, py => do
    let mut x := x0
    let mut d := d0
    for ec in gamma do
      let e := ec.1
      let subArg := uncollapses e
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
            else writeLevel Mf v x d arg [ctx.cols]
        modify fun c => { c with cols := c.cols ++ run }
        let sub := stripSt e
        let mut nx := (lastC run).x + 1
        let mut nd := (lastC run).y
        modify fun c => { c with prev := if arg then none else v }
        if !sub.isEmpty && !(← get).fresh && spent Mf (← get) then
          laySt none
          let l := lastC (← get).cols
          nx := l.x + 1
          nd := l.y
        blockFSt n sub nx nd subArg v (lastC run).y
        modify fun c => { c with prev := tailBlockSt (ato e) arg }

/-- `TrioRules.placeUnits` with `blockFSt` and `unitTailLevelSt`. -/
def placeUnitsSt (cols : Cols) (alpha : Od) (level0 rootX0 : Int) (regime : Option Od) : Ctx :=
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
          blockFSt Mf fuel (ato e) (x0 + 2) (y - 1) false none 0
          i := i + 1
        rootX := x0
      level := level + 1
      prev0 := beta.isEmpty
      if !beta.isEmpty then
        modify fun c => { c with prev := unitTailLevelSt beta }
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

/-- `TrioRules.finish` with `tailLevelSt`. -/
def finishSt (alpha : Od) (ctx : Ctx) : Cols :=
  match tailLevelSt alpha with
  | some t => appendSuffix Mf ctx.cols t ctx.storeys ctx.tailSub
  | none => ctx.cols

end

/-! ### The simulation -/

local notation "SimF" => Googology.Trans.BMS.TrioFixFuelE0.Sim


theorem leafNameNF_none (Mf : Od → Cols) (s : CtxN) (hs : P s) :
    ∀ n v, TrioRulesNL.leafNameNF Mf n s v = none := by
  intro n v
  cases n with
  | zero => rfl
  | succ n => simp [TrioRulesNL.leafNameNF, hs.1, hs.2]

theorem leafNameN_none (Mf : Od → Cols) (s : CtxN) (hs : P s) (v : Od) :
    TrioRulesNL.leafNameN Mf s v = none := leafNameNF_none Mf s hs _ v

theorem fixNNeeded_none (Mf : Od → Cols) (s : CtxN) (hs : P s) :
    TrioRulesNL.fixNNeeded Mf s = false := by
  simp [TrioRulesNL.fixNNeeded, hs.1]

theorem spent_none' (Mf : Od → Cols) (c : Ctx) (h : c.regime = none) : spent Mf c = false := by
  unfold spent; rw [h]; split <;> simp_all

macro "st_sim_step" : tactic => `(tactic| first
  | with_reducible refine sim_bind (sim_forIn _ _ fun _ _ => ?_) fun _ => ?_
  | with_reducible refine sim_bind (sim_forIn_range _ _ fun _ _ => ?_) fun _ => ?_
  | ((with_reducible refine sim_get_bind fun s hs => ?_)
     dsimp only
     try simp only [leafNameN_none _ s hs, hs.1, Bool.and_false, Bool.false_eq_true,
       ↓reduceIte, ite_self]
     refine sim_to_at ?_ hs)
  | with_reducible refine sim_bind (sim_liftC (laySt_pres _)) fun _ => ?_
  | ((with_reducible refine sim_bind (sim_modify ?_) fun _ => ?_)
     intro _ _
     exact ⟨rfl, rfl, rfl⟩)
  | with_reducible refine sim_bind (sim_pure _) fun _ => ?_
  | with_reducible refine sim_ite _ (fun _ => ?_) (fun _ => ?_)
  | with_reducible exact sim_pure _)

/-- **`blockNSt` runs as `blockFSt`** with no regime. -/
theorem sim_blockNSt (Mf : Od → Cols) : ∀ n g x d arg plvl py,
    SimF (blockNSt Mf n g x d arg plvl py) (blockFSt Mf n g x d arg plvl py) := by
  intro n
  induction n with
  | zero => intro g x d arg plvl py; exact sim_pure _
  | succ n ih =>
    intro g x d arg plvl py
    rw [blockNSt, blockFSt]
    dsimp only
    repeat (first | st_sim_step | refine sim_bind (ih _ _ _ _ _ _) fun _ => ?_)

macro "st_sim_get_left" : tactic => `(tactic|
  ((with_reducible refine sim_get_bind_left fun s hs => ?_)
   dsimp only
   simp only [fixNNeeded_none _ s hs, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
   refine sim_to_at ?_ hs))

/-- **`placeUnitsNSt` with no regime is `placeUnitsSt`**, with Fix N's state untouched. -/
theorem placeUnitsNSt_none (Mf : Od → Cols) (cols : Cols) (alpha : Od) (l r : Int) :
    placeUnitsNSt Mf cols alpha l r none = { c := placeUnitsSt Mf cols alpha l r none, n := {} } ∧
    (placeUnitsSt Mf cols alpha l r none).tailSub = none ∧
    (placeUnitsSt Mf cols alpha l r none).regime = none := by
  unfold placeUnitsNSt placeUnitsSt
  dsimp only
  have key : ∀ (pN : StateM CtxN Unit) (pF : StateM Ctx Unit), SimF pN pF →
      (pN.run { c := { cols := cols, regime := none } }).2 =
          { c := (pF.run { cols := cols, regime := none }).2, n := {} } ∧
        (pF.run { cols := cols, regime := none }).2.tailSub = none ∧
        (pF.run { cols := cols, regime := none }).2.regime = none :=
    fun pN pF h => run_tail_of_sim h _ ⟨rfl, rfl⟩ rfl
  refine key _ _ ?_
  simp only [Option.bind_none, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  repeat
    first
    | st_sim_step
    | (with_reducible refine sim_bind (sim_blockNSt Mf _ _ _ _ _ _ _) fun _ => ?_)
    | st_sim_get_left
    | with_reducible_and_instances exact sim_pure _
    | (with_reducible refine sim_pure_bind_left ?_)
    | (with_reducible refine sim_pure_bind_right ?_)
    | (split <;> try contradiction)

theorem upgradeNF_none (Mf : Od → Cols) (s : CtxN) (hs : s.c.regime = none) :
    ∀ n cs t used, TrioRulesNL.upgradeNF Mf n s cs t used = (cs, t, used) := by
  intro n cs t used
  cases n with
  | zero => rfl
  | succ n => simp [TrioRulesNL.upgradeNF, hs]

/-- **The countable step of the patched builder** is the plain builder with the
corrected rule 1. -/
theorem MstepSt_countable (Mf : Od → Cols) (alpha : Od) (h : lvlO alpha = none) :
    MstepSt Mf alpha = finishSt Mf alpha (placeUnitsSt Mf #[] alpha 0 (-1) none) := by
  obtain ⟨h1, h2, h3⟩ := placeUnitsNSt_none Mf #[] alpha 0 (-1)
  unfold MstepSt
  rw [h]
  dsimp only
  rw [h1]
  unfold finishNSt finishSt
  cases tailLevelSt alpha with
  | none => rfl
  | some t =>
    dsimp only
    rw [upgradeNF_none Mf _ h3, h2]

end Googology.Trans.BMS.TrioFixStripCalib
