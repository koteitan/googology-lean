import Googology.Trans.BMS.TrioRules3
import Googology.Trans.BMS.TrioRulesNonLast

/-!
# Rules 1–10 with all the fixes: A, B, C, D, E and N

Four versions of rules 1–10 of [koteitan/trio](https://github.com/koteitan/trio)
exist side by side:

* `TrioRules.lean`: the transcription of rules 1–10;
* `TrioRules2.lean`: Fixes A–D ([TRIO-SHEET-41.md](TRIO-SHEET-41.md));
* `TrioRules3.lean`: Fix E on top of `TrioRules2` ([TRIO-SHEET-FIXES.md](TRIO-SHEET-FIXES.md));
* `TrioRulesNonLast.lean`: Fix N on top of `TrioRules2` ([TRIO-NONLAST-LEAF.md](TRIO-NONLAST-LEAF.md)).

This file has one builder with all six fixes.  The two top fixes touch different
branches of one step of the builder:

* Fix E changes only rule 9 (`α = ψ_{Ω_u}(X)`): `MpsiLevel3` in place of `MpsiLevel2`;
* Fix N changes only `placeUnits` and the final upgrade (every other `α`):
  `placeUnitsN`, `finishN` in place of `placeUnits2`, `finish2`.

So the merged step `MstepAll` is `MstepN` of `TrioRulesNonLast.lean` with
`MpsiLevel2` replaced by `MpsiLevel3` (as TRIO-NONLAST-LEAF.md says), and every
definition below it is reused unchanged.  `MstepAll_psi` and `MstepAll_notPsi`
state this: on a `ψ`-level `α` the merged step is `Mstep3`'s, on every other `α`
it is `MstepN`'s, for the same `Mf`.  The two fixes still meet through the
recursion (`Mf` is the merged builder in both branches); the checks in
`TrioRulesAllSheet.lean` look for that.

**Against `TrioRules.lean`.**  For one step with the same `Mf`:

* `MOmega2_eq_MOmega`: Fix A's base equals rule 2's base unless Fix A fires
  (`fixAFires`: the last column of `M(v)` is a level column whose parent is a leaf);
* `MpsiLevel3_eq_MpsiLevel2`: Fix E's rule 9 equals `TrioRules2`'s unless Fix E fires
  (`fixEFires`: `u = Ω+1`, `Ω_ω ≤ w < Ω_{ω+1}` and `M(w)` starts `B ++ (1,1,1)`);
* `MstepAll_eq_Mstep_psi`, `MstepAll_eq_Mstep_omega`: so on `α = ψ_{Ω_u}(X)` and on
  `α = Ω_v` the merged step is rule 9 / rule 2 of `TrioRules.lean` when neither fix
  fires.

The remaining branch (`α` a sum or product, laid by `placeUnits`) is not proved
equal; the points where it differs are listed at the end of this file.
-/

namespace Googology.Trans.BMS.TrioRulesAll

open Googology.Trans.BMS.TrioRules
open Googology.Trans.BMS.TrioRules2
open Googology.Trans.BMS.TrioRules3
open Googology.Trans.BMS.TrioRulesNL

section
variable (Mf : Od → Cols)

/-- **One step of the merged builder**: `MstepN` (Fixes A–D and N) with rule 9 by
`MpsiLevel3` (Fix E). -/
def MstepAll (alpha : Od) : Cols :=
  match lvlO alpha with
  | none => finishN Mf alpha (placeUnitsN Mf #[] alpha 0 (-1) none)
  | some v =>
    match isPsiLevel alpha with
    | some uX => MpsiLevel3 Mf uX.1 uX.2
    | none =>
      if alpha == [(.W v, 1)] then MOmega2 Mf v
      else
        let base := MOmega2 Mf v
        let ya := lastRoot base
        finishN Mf alpha (placeUnitsN Mf base alpha ya.1 (ya.2 - 1) (some v))

end

/-- The merged builder with fuel. -/
def MfuelAll : Nat → Od → Cols
  | 0, _ => #[]
  | n + 1, a => MstepAll (MfuelAll n) a

/-- `α ↦` the columns of `ψ_0(Ω_α)`, by rules 1–10 with Fixes A–E and N. -/
def MAll (alpha : Od) : Cols := MfuelAll fuel alpha

/-- **The trio matrix of `ψ_0(Ω_α)` with Fixes A–E and N.** -/
def trioRuleMatrixAll (alpha : Od) : List (List Nat) := toRows (MAll alpha)

/-- The matrix for a label of the sheet. -/
def trioRuleMatrixOfAll (s : String) : Option (List (List Nat)) := do
  let a ← parse s
  if a.isEmpty then none else some (trioRuleMatrixAll a)

/-- The matrix of a label, `[]` when it does not parse. -/
def allOf (s : String) : List (List Nat) := (trioRuleMatrixOfAll s).getD []

/-- **Every column is three rows deep with `z < 2`.** -/
theorem WF3_trioRuleMatrixAll (alpha : Od) : WF3 (trioRuleMatrixAll alpha) := WF3_toRows _

/-! ### The merge: each branch is one of the two versions -/

section
variable (Mf : Od → Cols)

/-- On `α = ψ_{Ω_u}(X)` the merged step is `TrioRules3`'s step (Fix E). -/
theorem MstepAll_psi (alpha : Od) (v : Od) (uX : Od × Od)
    (hv : lvlO alpha = some v) (hp : isPsiLevel alpha = some uX) :
    MstepAll Mf alpha = Mstep3 Mf alpha ∧ MstepAll Mf alpha = MpsiLevel3 Mf uX.1 uX.2 := by
  refine ⟨?_, ?_⟩ <;> simp [MstepAll, Mstep3, hv, hp]

/-- On every other `α` the merged step is `TrioRulesNonLast`'s step (Fix N). -/
theorem MstepAll_notPsi (alpha : Od) (h : lvlO alpha = none ∨ isPsiLevel alpha = none) :
    MstepAll Mf alpha = MstepN Mf alpha := by
  rcases h with h | h
  · simp [MstepAll, MstepN, h]
  · cases hv : lvlO alpha <;> simp [MstepAll, MstepN, hv, h]

/-! ### Against `TrioRules.lean`: Fix A -/

/-- **Fix A fires on `v`**: the last column of `M(v)` is a level column whose parent
is neither a level column nor the root. -/
def fixAFires (v : Od) : Bool :=
  let cs := Mf v
  let par := forest cs
  let last := cs.size - 1
  let parLev := match par.getD last none with
    | some p => isLevel cs par p || p == 0
    | none => false
  !cs.isEmpty && isLevel cs par last && !parLev

/-- With no column kept plain, Fix A's walk is rule 2's walk. -/
theorem omegaDfs2_none (cs : Cols) (par : Array (Option Nat)) (drop : Option Nat) :
    ∀ (n i : Nat) (d : Int), omegaDfs2 cs par drop none n i d = omegaDfs cs par drop n i d := by
  intro n
  induction n with
  | zero => intro i d; rfl
  | succ n ih =>
    intro i d
    simp only [omegaDfs2, omegaDfs, ih]
    split <;> simp

/-- The two walks, for each value of "the last column is a level column" (`l`) and
"its parent is a level column or the root" (`b`), when Fix A does not fire. -/
theorem omegaDfs2_key (cs : Cols) (par : Array (Option Nat)) (last n : Nat) (l b : Bool)
    (h : (l && !b) = false) :
    omegaDfs2 cs par (if l && b then some last else none) (if l && !b then some last else none) n 0 0 =
      omegaDfs cs par (if l then some last else none) n 0 0 := by
  cases l <;> cases b <;> simp_all [omegaDfs2_none]

/-- **Fix A**: when it does not fire, `M(Ω_v)` is rule 2's. -/
theorem MOmega2_eq_MOmega (v : Od) (h : fixAFires Mf v = false) :
    MOmega2 Mf v = MOmega Mf v := by
  unfold MOmega2 MOmega
  unfold fixAFires at h
  dsimp only at h ⊢
  split
  · rfl
  · rename_i he
    simp only [he, Bool.not_false, Bool.true_and] at h
    exact congrArg List.toArray (omegaDfs2_key _ _ _ _ _ _ h)

/-- Rule 9 on Fix A's base is rule 9 when Fix A does not fire on `u`. -/
theorem MpsiLevel2_eq_MpsiLevel (u X : Od) (h : fixAFires Mf u = false) :
    MpsiLevel2 Mf u X = MpsiLevel Mf u X := by
  unfold MpsiLevel2 MpsiLevel
  rw [MOmega2_eq_MOmega Mf u h]
  rfl

/-! ### Against `TrioRules2.lean`: Fix E -/

/-- **Fix E fires on `ψ_{Ω_u}(X)`**: `u = Ω+1`, the argument's level `w` has
`Ω_ω ≤ w < Ω_{ω+1}`, and `M(w)` starts `B ++ (1,1,1)`. -/
def fixEFires (u X : Od) : Bool :=
  cmpOrd u omegaOnePlusOne == .eq &&
    match lvlO X with
    | none => false
    | some w => levelOmega w && (Mf w).extract 0 5 == headOmegaOmega

/-- **Fix E**: when it does not fire, rule 9 is `TrioRules2`'s. -/
theorem MpsiLevel3_eq_MpsiLevel2 (u X : Od) (h : fixEFires Mf u X = false) :
    MpsiLevel3 Mf u X = MpsiLevel2 Mf u X := by
  unfold fixEFires at h
  unfold MpsiLevel3
  cases hc : cmpOrd u omegaOnePlusOne <;> simp only [hc] at h ⊢ <;> try rfl
  cases hx : lvlO X with
  | none => rfl
  | some w =>
    simp only [hx] at h ⊢
    cases hw : levelOmega w <;> simp only [hw] at h ⊢ <;> try rfl
    simp at h
    simp [h]

/-! ### Against `TrioRules.lean`: the two branches without `placeUnits` -/

/-- **Rule 9**: on `α = ψ_{Ω_u}(X)` the merged step is `TrioRules`'s when neither
Fix A (on `u`) nor Fix E fires. -/
theorem MstepAll_eq_Mstep_psi (alpha v : Od) (uX : Od × Od)
    (hv : lvlO alpha = some v) (hp : isPsiLevel alpha = some uX)
    (hA : fixAFires Mf uX.1 = false) (hE : fixEFires Mf uX.1 uX.2 = false) :
    MstepAll Mf alpha = Mstep Mf alpha := by
  rw [(MstepAll_psi Mf alpha v uX hv hp).2, MpsiLevel3_eq_MpsiLevel2 Mf _ _ hE,
    MpsiLevel2_eq_MpsiLevel Mf _ _ hA]
  simp [Mstep, hv, hp]

/-- **Rule 2**: on `α = Ω_v` the merged step is `TrioRules`'s when Fix A does not
fire on `v`. -/
theorem MstepAll_eq_Mstep_omega (alpha v : Od) (hv : lvlO alpha = some v)
    (hp : isPsiLevel alpha = none) (he : (alpha == [(.W v, 1)]) = true)
    (hA : fixAFires Mf v = false) :
    MstepAll Mf alpha = Mstep Mf alpha := by
  simp [MstepAll, Mstep, hv, hp, he, MOmega2_eq_MOmega Mf v hA]

end

/-! ### Where the merged builder differs from `TrioRules.lean`

Besides the two proved branches above, the merged step differs from `Mstep` of
`TrioRules.lean` only in the `placeUnits` branch (`α` neither `Ω_v` nor
`ψ_{Ω_u}(X)`), at exactly these points of the code (`r` the regime):

1. the base `MOmega2` in place of `MOmega` (Fix A; `MOmega2_eq_MOmega`);
2. a unit's leaf naming `Ω_v`: `leafNameNF` in place of `blockF`'s two regime
   branches.  With no lifted copy yet (`cap = none`) this is Fix B's `leafNameF`,
   which differs from `blockF` only when `r` is uncountable and `v = Ω_w`
   (Fix B 1: `N(w) + 1`), or when `r = Ω_v` (Fix B 2: the `leafY v + 1` branch is
   skipped);
3. the final upgrade: `upgradeNF` (Fix B 3, the copied sub-units while `t = Ω_w`,
   uncountable `r`) then `appendSuffix … none`, in place of
   `appendSuffix … tailSub` (rule 8's `tailSub` is dropped);
4. Fix C: after `copyStorey` returns one sub-unit, the other digits of the first
   add unit are laid (rules 1–10 drop them);
5. Fix D: a non-last digit naming `Ω_p`, `p < r`, `leafY p > leafY r`, countable `r`;
6. Fix N: `fixNNeeded` (a tower regime `r`, a non-last leaf naming `p ∉ tops(r)`
   with a plain chain) — the upgrade, the lifted copy, `restate`, and after a copy
   the changed leaf names (`leafNameNF` with `cap`) and `suffixIn`.

For a countable `α` (`lvlO α = none`, regime `none`) none of points 2–6 can act,
by reading the code: `leafNameNF` is `none` (so `writeLevel` is used, as in
`blockF`), `upgradeNF` is the identity, `tailSub` is never set (no `copyStorey`),
and Fix D and Fix N need a regime.  This is **not proved** here (it would need a
simulation of `placeUnitsN`'s nested loops against `placeUnits`'s).
`TrioRulesAllSheet.lean`, Part 7, checks it with the same `Mf` on the 171
countable labels used there, and checks that the `ψ` and `Ω_v` steps differ
exactly when `fixAFires` / `fixEFires` hold.

**Why there is no theorem at fuel 200.**  Fixes B, C, D and N are decided inside
the loops of `placeUnits`, from the state built so far (the regime, the last
leaf, the storeys, the lifted copy).  So "no fix fires on `α`" is not a
condition on `α` alone, and it has to hold again at every recursive call
(`writeLevel`, `leafY`, `suffixOf`, `MOmega` call `Mf` on the levels of `α`).
A fuel-200 statement would need a copy of `placeUnits` that records whether a
fix fired, and a proof that the two copies run the same way.  What is proved is
the step-level part above, for the two branches without `placeUnits`. -/

end Googology.Trans.BMS.TrioRulesAll
