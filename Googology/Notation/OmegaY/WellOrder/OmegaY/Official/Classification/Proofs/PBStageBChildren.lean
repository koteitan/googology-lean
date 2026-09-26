/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/PBStageBChildren.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.PBStageBLift
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.ChainCorrCopyMono

set_option backward.do.legacy false

/-!
# The children of an item, spelled out (stage B tools)

`childItems_cases`: the list of children of an item of level `d + 2` is one of the five forms of
the rule (notes/03 §2.4): no top of the column in the source region (no children), case 1 (the
column does not ascend), and, when it ascends at the root top `ρ`, cases 2, 3, 4 with the
children `ChainCorr.c2`, `ChainCorr.c3`, `ChainCorr.c4` of `ChainCorrCopyMono.lean`.
-/

namespace OmegaY.Official.Classification.Proofs.CopyShape.PBStageB

open Canonical Reserve Official Descent Classification Proofs
open ChainCorr ChainCorr.CopyMonoProof

/-- The children of an item of level `d + 2`, case by case. -/
inductive ChildCase (ctx : Context) (d : Nat) (it : Item) : List Item → Prop
  | none (h : topIn ctx.source ctx.x (d + 2) it.source = none) : ChildCase ctx d it []
  | case1 (a : Ref × Cell) (ha : topIn ctx.source ctx.x (d + 2) it.source = some a)
      (hasc : ascends ctx (topIn ctx.source ctx.rootColumn (d + 2) it.source) = .ok false)
      (hcl : it.clean = none) (hoff : it.offset = 0) (hcb : it.cutBottom = false) :
      ChildCase ctx d it ((List.range (height (d + 2) (official a.2.row) + 1)).map
        fun j => (⟨slot (d + 2) it.source j, slot (d + 2) it.target j, none, 0, false⟩ : Item))
  | case2 (a : Ref × Cell) (ha : topIn ctx.source ctx.x (d + 2) it.source = some a)
      (ρr : Ref) (ρc : Cell)
      (hρ : topIn ctx.source ctx.rootColumn (d + 2) it.source = some (ρr, ρc))
      (hasc : ascends ctx (some (ρr, ρc)) = .ok true)
      (hcl : it.clean = none) (hcb : it.cutBottom = false) (L e : Int)
      (hL : L = ((heightOf (d + 2) (topIn ctx.source ctx.lastColumn (d + 2) it.source) : Int) -
        (height (d + 2) (official ρc.row) : Int)) * (ctx.block : Int))
      (he : e = if d + 2 = 2 then 1 else 0) :
      ChildCase ctx d it ((List.range (((height (d + 2) (official a.2.row) : Int) + L + 1).toNat)).map
        (c2 it.source it.target (official ρc.row) d (height (d + 2) (official ρc.row)) L e
          ctx.block))
  | case3 (a : Ref × Cell) (ha : topIn ctx.source ctx.x (d + 2) it.source = some a)
      (ρr : Ref) (ρc : Cell)
      (hρ : topIn ctx.source ctx.rootColumn (d + 2) it.source = some (ρr, ρc))
      (hasc : ascends ctx (some (ρr, ρc)) = .ok true)
      (hcl : it.clean = none) (hcb : it.cutBottom = true) (e : Int)
      (he : e = if d + 2 = 2 then 1 else 0) :
      ChildCase ctx d it
        (((List.range ((if ctx.block = 0 then height (d + 2) (official a.2.row) else
            heightOf (d + 2) (topIn ctx.result ctx.boundary (d + 2) it.target) +
              height (d + 2) (official a.2.row)) + 1)).filter
            (fun x => decide (height (d + 2) (official ρc.row) ≤ x))).map
          (c3 it.source it.target (official ρc.row) d (height (d + 2) (official ρc.row))
            (heightOf (d + 2) (topIn ctx.result ctx.boundary (d + 2) it.target)) e))
  | case4 (a : Ref × Cell) (ha : topIn ctx.source ctx.x (d + 2) it.source = some a)
      (ρr : Ref) (ρc : Cell)
      (hρ : topIn ctx.source ctx.rootColumn (d + 2) it.source = some (ρr, ρc))
      (hasc : ascends ctx (some (ρr, ρc)) = .ok true)
      (C : Row) (hcl : it.clean = some C) (csRef : Ref) (cs : Cell)
      (hcs : nodeAt ctx.source ctx.x C = some (csRef, cs)) (g : Nat)
      (hg : generations ctx.source ctx.rootColumn C (ctx.x + 1) csRef cs 0 = .ok g)
      (hbnd : ¬ (¬ it.cutBottom = true ∧
        ((topIn ctx.result ctx.boundary (d + 2) it.target).isNone = true ∨ it.offset ≠ 0))) :
      ChildCase ctx d it
        ((List.range ((if ctx.block = 0 then (height (d + 2) (official a.2.row) : Int) else
            (heightOf (d + 2) (topIn ctx.result ctx.boundary (d + 2) it.target) : Int) + g -
              it.offset) + 1).toNat).map
          (c4 it.source it.target C d (height (d + 2) (official ρc.row))
            (heightOf (d + 2) (topIn ctx.result ctx.boundary (d + 2) it.target)) it.offset
            it.cutBottom))

theorem childItems_cases {ctx : Context} {d : Nat} {it : Item} {cs : List Item}
    (h : childItems ctx (d + 2) it = .ok cs) : ChildCase ctx d it cs := by
  unfold childItems at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  cases hx : topIn ctx.source ctx.x (d + 2) it.source with
  | none =>
      rw [hx] at h
      obtain rfl := Except.ok.inj h
      exact ChildCase.none hx
  | some a =>
      obtain ⟨aRef, aCell⟩ := a
      rw [hx] at h
      simp only at h
      cases hρ : topIn ctx.source ctx.rootColumn (d + 2) it.source with
      | none =>
          rw [hρ] at h
          have hasc : ascends ctx none = .ok false := rfl
          simp only [hasc, Bool.false_eq_true, not_false_eq_true, if_true] at h
          split at h
          · simp [throw, throwThe, MonadExceptOf.throw] at h
          · rename_i hflags
            obtain rfl := Except.ok.inj h
            have hcl : it.clean = none := by
              cases hc : it.clean with
              | none => rfl
              | some _ => exact absurd (Or.inl (by simp [hc])) hflags
            have hoff : it.offset = 0 := by
              by_contra hne
              exact hflags (Or.inr (Or.inl hne))
            have hcb : it.cutBottom = false := by
              cases hb : it.cutBottom with
              | false => rfl
              | true => exact absurd (Or.inr (Or.inr hb)) hflags
            refine ChildCase.case1 (aRef, aCell) hx ?_ hcl hoff hcb
            rw [hρ]; rfl
      | some ρ =>
          obtain ⟨ρr, ρc⟩ := ρ
          rw [hρ] at h
          cases hasc : ascends ctx (some (ρr, ρc)) with
          | error err =>
              rw [hasc] at h
              cases h
          | ok asc =>
              rw [hasc] at h
              simp only at h
              cases asc with
              | false =>
                  simp only [Bool.false_eq_true, not_false_eq_true, if_true] at h
                  split at h
                  · simp [throw, throwThe, MonadExceptOf.throw] at h
                  · rename_i hflags
                    obtain rfl := Except.ok.inj h
                    have hcl : it.clean = none := by
                      cases hc : it.clean with
                      | none => rfl
                      | some _ => exact absurd (Or.inl (by simp [hc])) hflags
                    have hoff : it.offset = 0 := by
                      by_contra hne
                      exact hflags (Or.inr (Or.inl hne))
                    have hcb : it.cutBottom = false := by
                      cases hb : it.cutBottom with
                      | false => rfl
                      | true => exact absurd (Or.inr (Or.inr hb)) hflags
                    refine ChildCase.case1 (aRef, aCell) hx ?_ hcl hoff hcb
                    rw [hρ]; exact hasc
              | true =>
                  simp only [not_true_eq_false, if_false] at h
                  split at h
                  · rename_i hcl
                    split at h
                    · rename_i hcb
                      have hcb' : it.cutBottom = false := by simpa using hcb
                      obtain rfl := Except.ok.inj h
                      exact ChildCase.case2 (aRef, aCell) hx ρr ρc hρ hasc hcl hcb' _ _ rfl rfl
                    · rename_i hcb
                      have hcb' : it.cutBottom = true := by simpa using hcb
                      obtain rfl := Except.ok.inj h
                      exact ChildCase.case3 (aRef, aCell) hx ρr ρc hρ hasc hcl hcb' _ rfl
                  · rename_i C hcl
                    split at h
                    · simp [throw, throwThe, MonadExceptOf.throw] at h
                    · rename_i p hp
                      obtain ⟨csRef, cs0⟩ := p
                      split at h
                      · cases h
                      · rename_i g hg
                        split at h
                        · simp [throw, throwThe, MonadExceptOf.throw] at h
                        · rename_i hbnd
                          obtain rfl := Except.ok.inj h
                          exact ChildCase.case4 (aRef, aCell) hx ρr ρc hρ hasc C hcl csRef cs0 hp g
                            hg hbnd

end OmegaY.Official.Classification.Proofs.CopyShape.PBStageB

#print axioms OmegaY.Official.Classification.Proofs.CopyShape.PBStageB.childItems_cases
