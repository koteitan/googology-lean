import Googology.Trans.BMS.TrioFixFuel
import Googology.Trans.BMS.TrioMono

/-!
# Fix Fuel below `ε₀`: injective at every depth

`TrioFixFuel.lean` gives the merged rules (`TrioRulesAll`, Fixes A–E and N) a fuel
that grows with the term.  This file proves, for that patched map on terms
(`TrioFixFuel.trioMatrixLD`, fuel `max 200 (tDep α)`):

  `trioMatrixLD α = trioMatrix α`  for every standard `α < ε₀`
  (`trioMatrixLD_eq_trioMatrix`), with no depth bound,

so below `ε₀` it keeps and reflects the order and is injective at every depth
(`trioMatrixLD_lt_iff`, `trioMatrixLD_injective`).  `TrioRulesFuel.lean` proved
the same for rules 1–10 (`TrioRules.lean`); what is new is the step

  `MstepAll_countable`: on a countable `α` (`lvlO F α = none`) the merged step
  `TrioFixFuel.MstepAll F Mf α` **is** rules 1–10's step `TrioFuel.Mstep F Mf α`,
  for every fuel `F` and every `Mf`,

and at fuel `200` (`MstepAll_countable_200`) this is the statement
`TrioRulesAll.lean` lists as not proved ("it would need a simulation of
`placeUnitsN`'s nested loops against `placeUnits`'s").

**How.**  With no regime, Fixes B–D and N never act: `leafNameN` is `none`,
`fixNNeeded` is `false`, Fix C and Fix D need a regime, `upgradeNF` does nothing,
and `tailSub` stays `none` (only `copyStorey` sets it).  `Sim p q` says that the
Fix N program `p` (state `CtxN`) runs as the plain program `q` (state `Ctx`) on the
inner state, leaves Fix N's own state alone, and keeps the regime and `tailSub`,
from every state with no regime and no cap value.  `Sim` goes through `bind`,
`get`, `modify`, `forIn` and `if` (`sim_*`), so the two do-blocks are matched step
by step (`fixfuel_sim_step`): `sim_blockN` for `blockN` against `blockF`,
`placeUnitsN_none` for `placeUnitsN` against `placeUnits`.  The extra `get`s and
branches of Fix N are removed with `sim_get_bind_left` and `fixNNeeded_none`.
-/

namespace Googology.Trans.BMS.TrioFixFuelE0
open Googology.Trans.BMS.TrioRules (Ex Od Col Cols Ctx laySt)
open Googology.Trans.BMS.TrioRulesNL (CtxN NState)

/-- The invariant: no regime, no cap value. -/
def P (s : CtxN) : Prop := s.c.regime = none ∧ s.n.capy = none

/-- `p` runs as `q` from `s`: same result, `q`'s state as the inner state, Fix N's
state unchanged, regime and `tailSub` kept. -/
def SimAt {α : Type} (s : CtxN) (p : StateM CtxN α) (q : StateM Ctx α) : Prop :=
  p.run s = ((q.run s.c).1, { s with c := (q.run s.c).2 }) ∧
    (q.run s.c).2.regime = s.c.regime ∧ (q.run s.c).2.tailSub = s.c.tailSub

/-- `p` runs as `q` from every state with no regime and no cap value. -/
def Sim {α : Type} (p : StateM CtxN α) (q : StateM Ctx α) : Prop := ∀ s, P s → SimAt s p q

theorem sim_pure {α : Type} (a : α) : Sim (pure a) (pure a) := by
  intro s _; exact ⟨rfl, rfl, rfl⟩

theorem sim_bind {α β : Type} {p : StateM CtxN α} {q : StateM Ctx α} {f : α → StateM CtxN β}
    {g : α → StateM Ctx β} (hp : Sim p q) (hf : ∀ a, Sim (f a) (g a)) : Sim (p >>= f) (q >>= g) := by
  intro s hs
  obtain ⟨h1, h2, h3⟩ := hp s hs
  have hs' : P { s with c := (q.run s.c).2 } := ⟨by simpa [hs.1] using h2, hs.2⟩
  obtain ⟨k1, k2, k3⟩ := hf (q.run s.c).1 _ hs'
  refine ⟨?_, ?_, ?_⟩
  · show (f (p.run s).1).run (p.run s).2 = _
    rw [h1]; exact k1
  · show ((g (q.run s.c).1).run (q.run s.c).2).2.regime = _
    rw [k2, h2]
  · show ((g (q.run s.c).1).run (q.run s.c).2).2.tailSub = _
    rw [k3, h3]

theorem sim_get_bind {β : Type} {f : CtxN → StateM CtxN β} {g : Ctx → StateM Ctx β}
    (h : ∀ s, P s → SimAt s (f s) (g s.c)) : Sim (get >>= f) (get >>= g) := by
  intro s hs; exact h s hs

theorem sim_get_bind_left {β : Type} {f : CtxN → StateM CtxN β} {q : StateM Ctx β}
    (h : ∀ s, P s → SimAt s (f s) q) : Sim (get >>= f) q := by
  intro s hs; exact h s hs

theorem sim_modify {f : CtxN → CtxN} {g : Ctx → Ctx}
    (h : ∀ s, P s → f s = { s with c := g s.c } ∧ (g s.c).regime = s.c.regime ∧
      (g s.c).tailSub = s.c.tailSub) : Sim (modify f) (modify g) := by
  intro s hs
  obtain ⟨h1, h2, h3⟩ := h s hs
  exact ⟨by show (PUnit.unit, f s) = _; rw [h1]; rfl, h2, h3⟩

theorem sim_liftC {α : Type} {q : StateM Ctx α}
    (h : ∀ c, (q.run c).2.regime = c.regime ∧ (q.run c).2.tailSub = c.tailSub) :
    Sim (Googology.Trans.BMS.TrioRulesNL.liftC q) q := by
  intro s _; exact ⟨rfl, h s.c⟩

theorem sim_forIn {ρ β : Type} (l : List ρ) : ∀ (b : β) {f : ρ → β → StateM CtxN (ForInStep β)}
    {g : ρ → β → StateM Ctx (ForInStep β)}, (∀ x b, Sim (f x b) (g x b)) →
    Sim (forIn l b f) (forIn l b g) := by
  induction l with
  | nil => intro b f g _; exact sim_pure b
  | cons x xs ih =>
    intro b f g h
    simp only [List.forIn_cons]
    refine sim_bind (h x b) fun r => ?_
    cases r with
    | done b' => exact sim_pure b'
    | yield b' => exact ih b' h

theorem sim_forIn_range {β : Type} (r : Std.Legacy.Range) (b : β) {f : Nat → β → StateM CtxN (ForInStep β)}
    {g : Nat → β → StateM Ctx (ForInStep β)} (h : ∀ x b, Sim (f x b) (g x b)) :
    Sim (forIn r b f) (forIn r b g) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.forIn_eq_forIn_range']
  exact sim_forIn _ b h

theorem sim_ite {α : Type} (c : Prop) [Decidable c] {p p' : StateM CtxN α} {q q' : StateM Ctx α}
    (h : c → Sim p q) (h' : ¬c → Sim p' q') : Sim (if c then p else p') (if c then q else q') := by
  by_cases hc : c
  · simp only [hc, ↓reduceIte]; exact h hc
  · simp only [hc, ↓reduceIte]; exact h' hc

theorem laySt_pres (y : Option Int) (c : Ctx) :
    ((laySt y).run c).2.regime = c.regime ∧ ((laySt y).run c).2.tailSub = c.tailSub := ⟨rfl, rfl⟩

theorem sim_to_at {α : Type} {s : CtxN} {p : StateM CtxN α} {q : StateM Ctx α}
    (h : Sim p q) (hs : P s) : SimAt s p q := h s hs

theorem leafNameNF_none (F : Nat) (Mf : Od → Cols) (s : CtxN) (hs : P s) :
    ∀ n v, TrioFixFuel.leafNameNF F Mf n s v = none := by
  intro n v
  cases n with
  | zero => rfl
  | succ n => simp [TrioFixFuel.leafNameNF, hs.1, hs.2]

theorem leafNameN_none (F : Nat) (Mf : Od → Cols) (s : CtxN) (hs : P s) (v : Od) :
    TrioFixFuel.leafNameN F Mf s v = none := leafNameNF_none F Mf s hs F v

macro "fixfuel_sim_step" : tactic => `(tactic| first
  | with_reducible refine sim_bind (sim_forIn _ _ fun _ _ => ?_) fun _ => ?_
  | with_reducible refine sim_bind (sim_forIn_range _ _ fun _ _ => ?_) fun _ => ?_
  | ((with_reducible refine sim_get_bind fun s hs => ?_)
     dsimp only
     try simp only [leafNameN_none _ _ s hs, hs.1, Bool.and_false, Bool.false_eq_true,
       ↓reduceIte, ite_self]
     refine sim_to_at ?_ hs)
  | with_reducible refine sim_bind (sim_liftC (laySt_pres _)) fun _ => ?_
  | ((with_reducible refine sim_bind (sim_modify ?_) fun _ => ?_)
     intro _ _
     exact ⟨rfl, rfl, rfl⟩)
  | with_reducible refine sim_bind (sim_pure _) fun _ => ?_
  | with_reducible refine sim_ite _ (fun _ => ?_) (fun _ => ?_)
  | with_reducible exact sim_pure _)

open Googology.Trans.BMS.TrioFixFuel in
/-- **`blockN` runs as `blockF`** with no regime. -/
theorem sim_blockN (F : Nat) (Mf : Od → Cols) : ∀ n g x d arg plvl py,
    Sim (blockN F Mf n g x d arg plvl py) (TrioFuel.blockF F Mf n g x d arg plvl py) := by
  intro n
  induction n with
  | zero => intro g x d arg plvl py; exact sim_pure _
  | succ n ih =>
    intro g x d arg plvl py
    rw [blockN, TrioFuel.blockF]
    dsimp only
    repeat (first | fixfuel_sim_step | refine sim_bind (ih _ _ _ _ _ _) fun _ => ?_)
theorem sim_pure_bind_left {α β : Type} {a : α} {f : α → StateM CtxN β} {q : StateM Ctx β}
    (h : Sim (f a) q) : Sim (pure a >>= f) q := h

theorem sim_pure_bind_right {α β : Type} {a : α} {p : StateM CtxN β} {g : α → StateM Ctx β}
    (h : Sim p (g a)) : Sim p (pure a >>= g) := h

theorem run_of_sim {α : Type} {p : StateM CtxN α} {q : StateM Ctx α} (h : Sim p q) (s : CtxN)
    (hs : P s) : (p.run s).2 = { s with c := (q.run s.c).2 } := by
  rw [(h s hs).1]

theorem run_tail_of_sim {α : Type} {p : StateM CtxN α} {q : StateM Ctx α} (h : Sim p q)
    (s : CtxN) (hs : P s) (ht : s.c.tailSub = none) :
    (p.run s).2 = { s with c := (q.run s.c).2 } ∧ (q.run s.c).2.tailSub = none ∧
      (q.run s.c).2.regime = none := by
  obtain ⟨h1, h2, h3⟩ := h s hs
  exact ⟨by rw [h1], h3.trans ht, h2.trans hs.1⟩

theorem fixNNeeded_none (F : Nat) (Mf : Od → Cols) (s : CtxN) (hs : P s) :
    TrioFixFuel.fixNNeeded F Mf s = false := by
  simp [TrioFixFuel.fixNNeeded, hs.1]

macro "fixfuel_sim_get_left" : tactic => `(tactic|
  ((with_reducible refine sim_get_bind_left fun s hs => ?_)
   dsimp only
   simp only [fixNNeeded_none _ _ s hs, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
   refine sim_to_at ?_ hs))

open Googology.Trans.BMS.TrioFixFuel in
/-- **`placeUnitsN` with no regime is `placeUnits`**, with Fix N's state untouched;
`tailSub` stays `none` and the regime `none`. -/
theorem placeUnitsN_none (F : Nat) (Mf : Od → Cols) (cols : Cols) (alpha : Od) (l r : Int) :
    placeUnitsN F Mf cols alpha l r none =
      { c := TrioFuel.placeUnits F Mf cols alpha l r none, n := {} } ∧
    (TrioFuel.placeUnits F Mf cols alpha l r none).tailSub = none ∧
    (TrioFuel.placeUnits F Mf cols alpha l r none).regime = none := by
  unfold placeUnitsN TrioFuel.placeUnits
  dsimp only
  have key : ∀ (pN : StateM CtxN Unit) (pF : StateM Ctx Unit), Sim pN pF →
      (pN.run { c := { cols := cols, regime := none } }).2 =
          { c := (pF.run { cols := cols, regime := none }).2, n := {} } ∧
        (pF.run { cols := cols, regime := none }).2.tailSub = none ∧
        (pF.run { cols := cols, regime := none }).2.regime = none :=
    fun pN pF h => run_tail_of_sim h _ ⟨rfl, rfl⟩ rfl
  refine key _ _ ?_
  simp only [Option.bind_none, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  repeat
    first
    | fixfuel_sim_step
    | (with_reducible refine sim_bind (sim_blockN F Mf _ _ _ _ _ _ _) fun _ => ?_)
    | fixfuel_sim_get_left
    | with_reducible_and_instances exact sim_pure _
    | (with_reducible refine sim_pure_bind_left ?_)
    | (with_reducible refine sim_pure_bind_right ?_)
    | (split <;> try contradiction)
/-! ### The countable step -/

theorem upgradeNF_none (F : Nat) (Mf : Od → Cols) (s : CtxN) (hs : s.c.regime = none) :
    ∀ n cs t used, TrioFixFuel.upgradeNF F Mf n s cs t used = (cs, t, used) := by
  intro n cs t used
  cases n with
  | zero => rfl
  | succ n => simp [TrioFixFuel.upgradeNF, hs]

/-- **The countable step**: on a countable `α` the merged step (Fixes A–E, N) is
rules 1–10's step, for the same `Mf` and the same fuel. -/
theorem MstepAll_countable (F : Nat) (Mf : Od → Cols) (alpha : Od)
    (h : TrioFuel.lvlO F alpha = none) :
    TrioFixFuel.MstepAll F Mf alpha = TrioFuel.Mstep F Mf alpha := by
  obtain ⟨h1, h2, h3⟩ := placeUnitsN_none F Mf #[] alpha 0 (-1)
  unfold TrioFixFuel.MstepAll TrioFuel.Mstep
  rw [h]
  dsimp only
  rw [h1]
  unfold TrioFixFuel.finishN TrioFuel.finish
  cases TrioFuel.tailLevel F alpha with
  | none => rfl
  | some t =>
    dsimp only
    rw [upgradeNF_none F Mf _ h3, h2]

/-- **The countable step at fuel `200`**: `TrioRulesAll`'s merged step is rules
1–10's step on every countable `α`, for the same `Mf`. -/
theorem MstepAll_countable_200 (Mf : Od → Cols) (alpha : Od)
    (h : TrioRules.lvlO alpha = none) :
    TrioRulesAll.MstepAll Mf alpha = TrioRules.Mstep Mf alpha := by
  rw [← TrioFixFuel.MstepAll_200, ← TrioFuel.Mstep_200]
  exact MstepAll_countable 200 Mf alpha h

open Googology.Notation.ExBuchholz
open Googology.Notation.ExBuchholz.Term
open Googology.Trans.BMS (trioMatrix omegaIndexMatrix)
open Googology.Trans.BMS.TrioRulesE0 (dep colsOf toRows_colsOf)

/-- The builder with fuel `F` on `ofTerm F α`, below `ε₀`: the columns of
`omegaIndexMatrix α` (`TrioFuel.M_ofTerm` for the merged rules). -/
theorem MF_ofTerm (F : Nat) (hF : 1 ≤ F) (α : Term) (hα : TrioFuel.Good F α) :
    TrioFixFuel.MF F (TrioFuel.ofTerm F α) = (colsOf (omegaIndexMatrix α)).toArray := by
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  show TrioFixFuel.MfuelAll (F' + 1) (F' + 1) (TrioFuel.ofTerm (F' + 1) α) = _
  have hl : TrioFuel.lvlO (F' + 1) (TrioFuel.ofTerm (F' + 1) α) = none := TrioFuel.lvl_ex hα
  rw [TrioFixFuel.MfuelAll, MstepAll_countable _ _ _ hl]
  unfold TrioFuel.Mstep
  rw [hl]
  dsimp only
  unfold TrioFuel.finish
  rw [TrioFuel.tailLevel_ofTerm hα]
  dsimp only
  exact TrioFuel.placeUnits_ofTerm _ α hα

theorem dep_le_tDep : ∀ α : Term, dep α ≤ TrioFixFuel.tDep α := by
  intro α
  induction α with
  | nil => simp [dep, TrioFixFuel.tDep]
  | cons a b t _ hb ht => simp only [dep, TrioFixFuel.tDep]; omega

/-- **The patched map on terms is `trioMatrix` below `ε₀`**, at every depth, for
every term with all subscripts `0` and descending principal terms. -/
theorem trioMatrixLD_eq_of_good (α : Term) (hA : AllNil α) (hD : DescAll α) :
    TrioFixFuel.trioMatrixLD α = trioMatrix α := by
  rw [Googology.Trans.BMS.TrioStd.trioMatrix_allNil α hA]
  have hF : 1 ≤ TrioFixFuel.fuelT α := by
    simp only [TrioFixFuel.fuelT, TrioRules.fuel]; omega
  have hd : dep α ≤ TrioFixFuel.fuelT α + 1 := by
    have := dep_le_tDep α
    simp only [TrioFixFuel.fuelT, TrioRules.fuel]; omega
  unfold TrioFixFuel.trioMatrixLD TrioFixFuel.ofTermD
  rw [MF_ofTerm _ hF α ⟨⟨hA, hD⟩, hd⟩]
  exact toRows_colsOf _ (Googology.Trans.BMS.WF3_omegaIndexMatrix α)

/-- **The same for every standard form below `ε₀`**: no depth bound. -/
theorem trioMatrixLD_eq_trioMatrix (α : Googology.Trans.BMS.exbE0.State) :
    TrioFixFuel.trioMatrixLD α.1 = trioMatrix α.1 :=
  trioMatrixLD_eq_of_good α.1 (Googology.Trans.BMS.allNil_of_state α)
    (Googology.Trans.BMS.descAll_of_OT α.1 α.2.1 (Googology.Trans.BMS.allNil_of_state α))

/-- **So below `ε₀` the patched map keeps and reflects the order at every depth.** -/
theorem trioMatrixLD_lt_iff (α β : Googology.Trans.BMS.exbE0.State) :
    TrioFixFuel.trioMatrixLD α.1 < TrioFixFuel.trioMatrixLD β.1 ↔ α.1 < β.1 := by
  rw [trioMatrixLD_eq_trioMatrix, trioMatrixLD_eq_trioMatrix,
    Googology.Trans.BMS.TrioStd.trioMatrix_allNil _ (Googology.Trans.BMS.allNil_of_state α),
    Googology.Trans.BMS.TrioStd.trioMatrix_allNil _ (Googology.Trans.BMS.allNil_of_state β)]
  exact Googology.Trans.BMS.omegaIndexMatrix_lt_iff α β

/-- **And it is injective below `ε₀`, at every depth.** -/
theorem trioMatrixLD_injective {α β : Googology.Trans.BMS.exbE0.State}
    (h : TrioFixFuel.trioMatrixLD α.1 = TrioFixFuel.trioMatrixLD β.1) : α = β := by
  rw [trioMatrixLD_eq_trioMatrix, trioMatrixLD_eq_trioMatrix,
    Googology.Trans.BMS.TrioStd.trioMatrix_allNil _ (Googology.Trans.BMS.allNil_of_state α),
    Googology.Trans.BMS.TrioStd.trioMatrix_allNil _ (Googology.Trans.BMS.allNil_of_state β)] at h
  exact Googology.Trans.BMS.omegaIndexMatrix_injective h

end Googology.Trans.BMS.TrioFixFuelE0
