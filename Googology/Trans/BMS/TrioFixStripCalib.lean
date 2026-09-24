import Googology.Trans.BMS.TrioFixStripCalibUnits

/-!
# The patched trio map computes `trioE2` on the fragment, within the fuel

`TrioFixStrip.trioMatrixLSt` is the trio map of [koteitan/trio](https://github.com/koteitan/trio)
(rules 1–10 of `ebp2bms/algorithm/2`, with the merged Fixes A–E, N, the reading `ofTermFix`
and the corrected rule 1 `stripSt`).  `TrioFixStripTree.trioE2` is the same map written as
a structural recursion, with order (`trioE2_lt_iff`) and standard forms (`trioE2_std`)
proved there.  This file proves

  `trioMatrixLSt_eq_trioE2`: for standard `α < Ω` with every subscript `0` or `1` and
  `rdT α ≤ 100`, `trioMatrixLSt α = trioE2 α`,

and so, for those `α`, **the order** (`trioMatrixLSt_lt_iff`, `trioMatrixLSt_injective`) and
**the standard forms** (`trioMatrixLSt_std`) of the patched map.

## Why a depth bound

`TrioFixStripTree.CalibSt`, the same statement with no bound, is **false**
(`TrioFixStripCalibNo.not_calibSt`): every recursion of the program carries a fuel of `200`,
and the towers `T_202 ≠ T_203` (`ψ_0` applied `202` / `203` times to `0`) get one matrix.
The bound used here is `rdT α ≤ 100`, where `rdT` (`TrioFixStripCalibRead.lean`) bounds the
nesting depth of the reading from above (`odDep_read_le`): the proof pays the comparison of
two readings with the sum of their depths as fuel.  `rdT α` is at most twice the nesting
depth `dep α` of the term, so every term with `dep α ≤ 50` is covered.  The bound is
sufficient, not sharp: numerically the program first fails at `rdT = 201`
(`TrioFixStripCalibNo.CalibRd200`, open).

## How the proof goes

* `TrioFixStripCalibSim`: with no regime, the patched builder `MstepSt` is the plain
  builder `placeUnitsSt` / `blockFSt` / `finishSt` (Fixes B–D and N never act).
* `TrioFixStripCalibRead`: on the fragment the reading groups the summands, compares
  them as the terms do, and writes the summand `ψ_a(b)` as `ω^{sx a b}` with
  `ato (sx 0 b)` the reading of `expoT b` (the exponent of `ψ_0(b) = ω^{expoT b}`).
* `TrioFixStripCalibEx`: what the builder reads off `sx a b`: the level (`lvl_sx`), the
  children (`stripSt_sx`: the reading of `b`), the flag (`uncollapses_sx`).
* `TrioFixStripCalibBlock`: so `blockFSt` writes the tree of the term.
* `TrioFixStripCalibUnits`: so `placeUnitsSt` lays `trioE2`'s add units.
* Here: the level the matrix ends on is `none` or `Ω_1`, and `M(1) = (0,0,0)(1,1,0)` has no
  suffix, so `finishSt` appends nothing.
-/

namespace Googology.Trans.BMS.TrioFixStripCalib

open Googology.Notation.ExBuchholz
open Googology.Notation.ExBuchholz.Term
open Googology.Trans.BMS (AllNil WF3)
open Googology.Trans.BMS.TrioRules
open Googology.Trans.BMS.TrioFixOfTerm (ofTermFix)
open Googology.Trans.BMS.TrioTree (Sub01 TopNil topNil_of_lt_tW mulUnitsE)
open Googology.Trans.BMS.TrioFixStripTree (expoT topNil_expoT addUnitsE2 bodyE2 trioE2
  trioE2_lt_iff trioE2_injective trioE2_std CalibSt)
open Googology.Trans.BMS.TrioTreeRules (sums B2 WF3_mulUnitsE)
open Googology.Trans.BMS.TrioRulesE0 (colsOf toRows_colsOf)
open Googology.Trans.BMS.TrioFixStrip (stripSt uncollapses tailBlockFSt tailBlockSt
  unitTailLevelSt tailLevelSt MstepSt MfuelSt MSt trioRuleMatrixSt trioMatrixLSt)

/-! ### The level the matrix ends on -/

theorem tailBlockFSt_read : ∀ (n : Nat) (γ : Term) (arg : Bool), Rd γ →
    tailBlockFSt n (ofTermFix γ) arg = none ∨ tailBlockFSt n (ofTermFix γ) arg = some one := by
  intro n
  induction n with
  | zero => intro _ _ _; left; rfl
  | succ n ih =>
    intro γ arg hR
    unfold tailBlockFSt
    split
    · left; rfl
    · rename_i e k hlast
      obtain ⟨p, hp, he, _⟩ := mem_read hR (List.mem_of_getLast? hlast)
      simp only at he
      subst he
      have hpp := rd_of_mem_sums hp hR
      simp only [stripSt_sx hpp, uncollapses_sx hpp]
      split
      · exact ih _ _ (rd_arg hpp)
      · split
        · left; rfl
        · rw [lvl_sx hpp]; split <;> simp

theorem tailLevelSt_read {α : Term} (hR : Rd α) (hT : TopNil α) :
    tailLevelSt (ofTermFix α) = none ∨ tailLevelSt (ofTermFix α) = some one := by
  unfold tailLevelSt
  rw [units_read hR hT]
  split
  · left; rfl
  · rename_i b hb
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp (List.mem_of_getLast? hb)
    have hU : Rd (psi nil e) := rd_of_mem_sums (mem_sums_of_mem_exps' α hT e he) hR
    unfold unitTailLevelSt
    simp only
    split
    · left; rfl
    · split
      · rename_i e' c' hl
        rcases mem_predBeta (List.mem_of_getLast? hl) with hq | hq
        · rw [ato_sx_nil hU] at hq
          obtain ⟨p, hp, hq1, _⟩ := mem_read (rd_expoT hU) hq
          have hp1 : p.1 = nil :=
            sums_nil_of_topNil (topNil_expoT ((sumF_of_rd hU).good rfl)) p hp
          have hpp : Rd (psi nil p.2) := by
            have := rd_of_mem_sums hp (rd_expoT hU); rwa [hp1] at this
          simp only at hq1
          rw [hq1, hp1]
          unfold tailBlockSt
          rw [ato_sx_nil hpp]
          exact tailBlockFSt_read _ _ _ (rd_expoT hpp)
        · simp only at hq
          rw [hq]
          left; rfl
      · left; rfl

theorem lvlO_read {α : Term} (hR : Rd α) (hT : TopNil α) : lvlO (ofTermFix α) = none := by
  cases α with
  | nil => rfl
  | cons a e t =>
    obtain ⟨rfl, _⟩ := hT
    obtain ⟨k, L', _, hL⟩ := read_head hR
    have hU : Rd (psi nil e) :=
      rd_of_mem_sums (x := cons nil e t) (p := (nil, e)) List.mem_cons_self hR
    show lvlF (199 + 1) (.o (ofTermFix (cons nil e t))) = none
    rw [hL]
    show lvlF 199 (sx nil e) = none
    rw [lvlF_sx 199 nil e hU (by have := exDep_sx_le100 hU; omega)]
    rfl

/-! ### The builder -/

/-- `M(1) = (0,0,0)(1,1,0)` for the patched builder, at the fuel the collapse arguments use. -/
theorem MfuelSt_one : MfuelSt 199 one = B2 := by
  decide +kernel

theorem suffixOf_one (Mf : Od → Cols) (h1 : Mf one = B2) : suffixOf Mf one = #[] := by
  unfold suffixOf; rw [h1]; rfl

theorem finishSt_read (Mf : Od → Cols) (h1 : Mf one = B2) {α : Term} (hR : Rd α)
    (hT : TopNil α) (ctx : Ctx) (hts : ctx.tailSub = none) :
    finishSt Mf (ofTermFix α) ctx = ctx.cols := by
  unfold finishSt
  rcases tailLevelSt_read hR hT with h | h <;> rw [h]
  rw [hts]
  unfold appendSuffix
  simp [suffixOf_one Mf h1]

/-- **The patched builder on the reading of `α`**. -/
theorem MSt_read (α : Term) (hR : Rd α) (hT : TopNil α) :
    MSt (ofTermFix α) = (colsOf (trioE2 α)).toArray := by
  show MstepSt (MfuelSt 199) (ofTermFix α) = _
  rw [MstepSt_countable _ _ (lvlO_read hR hT)]
  obtain ⟨-, h2, -⟩ := placeUnitsNSt_none (MfuelSt 199) #[] (ofTermFix α) 0 (-1)
  rw [finishSt_read _ MfuelSt_one hR hT _ h2]
  exact placeUnitsSt_read _ MfuelSt_one α hR hT

theorem WF3_addUnitsE2 : ∀ (α : Term) (rp1 lastX : Nat) (pz : Bool) (i : Nat),
    WF3 (addUnitsE2 rp1 lastX pz i α) := by
  intro α
  induction α with
  | nil => intro _ _ _ _; exact Googology.Trans.BMS.WF3_nil
  | cons _ b t _ _ iht =>
    intro rp1 lastX pz i
    rw [addUnitsE2]
    split
    · split
      · exact Googology.Trans.BMS.WF3_cons ⟨rfl, by simp⟩ (iht _ _ _ _)
      · exact Googology.Trans.BMS.WF3_cons ⟨rfl, by simp⟩
          (Googology.Trans.BMS.WF3_cons ⟨rfl, by simp⟩ (iht _ _ _ _))
    · exact Googology.Trans.BMS.WF3_append (Googology.Trans.BMS.WF3_cons ⟨rfl, by simp⟩
        (Googology.Trans.BMS.WF3_cons ⟨rfl, by simp⟩ (WF3_mulUnitsE _ _ _))) (iht _ _ _ _)

/-! ### The theorem -/

/-- **The patched trio map computes `trioE2`** on every standard countable term whose
subscripts are `0` or `1` and whose reading is at most `100` deep (`rdT α ≤ 100`; every
term of nesting depth `dep α ≤ 50` is one). -/
theorem trioMatrixLSt_eq_trioE2 {α : Term} (hOT : OT α) (hc : α < tW) (hS : Sub01 α)
    (hd : rdT α ≤ 100) : trioMatrixLSt α = trioE2 α := by
  unfold trioMatrixLSt trioRuleMatrixSt
  rw [MSt_read α ⟨hOT, hS, hd⟩ (topNil_of_lt_tW hOT hc)]
  exact toRows_colsOf _ (WF3_addUnitsE2 α 0 0 false 1)

/-- `CalibSt` with the depth bound: proved. -/
def CalibRd : Prop :=
  ∀ α : Term, OT α → α < tW → Sub01 α → rdT α ≤ 100 → trioMatrixLSt α = trioE2 α

theorem calibRd : CalibRd := fun _ hOT hc hS hd => trioMatrixLSt_eq_trioE2 hOT hc hS hd

/-- **Order of the patched map** on the fragment within the fuel. -/
theorem trioMatrixLSt_lt_iff {α β : Term} (hα : OT α) (hβ : OT β) (hαc : α < tW)
    (hβc : β < tW) (sα : Sub01 α) (sβ : Sub01 β) (dα : rdT α ≤ 100) (dβ : rdT β ≤ 100) :
    trioMatrixLSt α < trioMatrixLSt β ↔ α < β := by
  rw [trioMatrixLSt_eq_trioE2 hα hαc sα dα, trioMatrixLSt_eq_trioE2 hβ hβc sβ dβ]
  exact trioE2_lt_iff hα hβ hαc hβc sα sβ

/-- **So it is injective there.** -/
theorem trioMatrixLSt_injective {α β : Term} (hα : OT α) (hβ : OT β) (hαc : α < tW)
    (hβc : β < tW) (sα : Sub01 α) (sβ : Sub01 β) (dα : rdT α ≤ 100) (dβ : rdT β ≤ 100)
    (h : trioMatrixLSt α = trioMatrixLSt β) : α = β := by
  rw [trioMatrixLSt_eq_trioE2 hα hαc sα dα, trioMatrixLSt_eq_trioE2 hβ hβc sβ dβ] at h
  exact trioE2_injective hα hβ hαc hβc sα sβ h

/-- **Standard forms of the patched map** on the fragment within the fuel. -/
theorem trioMatrixLSt_std {α : Term} (hOT : OT α) (hc : α < tW) (hS : Sub01 α)
    (hd : rdT α ≤ 100) :
    ∃ A : BM4.Arr 3, Pat.Std 3 A ∧ Googology.Trans.BMS.entriesR A = trioMatrixLSt α := by
  rw [trioMatrixLSt_eq_trioE2 hOT hc hS hd]
  exact trioE2_std hOT hc hS

/-- `rdT` is at most twice the nesting depth. -/
theorem rdT_le_two_dep : ∀ x : Term, Sub01 x → rdT x ≤ 2 * TrioRulesE0.dep x
  | nil, _ => le_rfl
  | cons a b t, hS => by
    have h1 := rdT_le_two_dep b hS.2.1
    have h2 := rdT_le_two_dep t hS.2.2
    rw [rdT_cons]
    simp only [TrioRulesE0.dep]
    unfold rsT
    split
    · split <;> omega
    · split
      · rename_i hb; subst hb; simp [TrioRulesE0.dep]; omega
      · rename_i hb
        have : 1 ≤ TrioRulesE0.dep b := by
          cases b with
          | nil => exact absurd rfl hb
          | cons _ _ _ => simp only [TrioRulesE0.dep]; omega
        omega

/-- **The same with the nesting depth**: `dep α ≤ 50` is enough. -/
theorem trioMatrixLSt_eq_trioE2_of_dep {α : Term} (hOT : OT α) (hc : α < tW) (hS : Sub01 α)
    (hd : TrioRulesE0.dep α ≤ 50) : trioMatrixLSt α = trioE2 α :=
  trioMatrixLSt_eq_trioE2 hOT hc hS (by have := rdT_le_two_dep α hS; omega)

#print axioms trioMatrixLSt_eq_trioE2
#print axioms calibRd
#print axioms trioMatrixLSt_lt_iff
#print axioms trioMatrixLSt_injective
#print axioms trioMatrixLSt_std
#print axioms trioMatrixLSt_eq_trioE2_of_dep

end Googology.Trans.BMS.TrioFixStripCalib
