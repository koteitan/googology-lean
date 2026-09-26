/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/LRCKids.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.LRCSet

set_option backward.do.legacy false

/-!
# The children of an item, indexed

For a successful call of `childItems` on an item whose source region has a node of the source
column, the four cases of the rule as a length and a formula for the `j`-th child.
-/

namespace OmegaY.Official.Recon.LRC

open Canonical Expansion Dimension RowLaw JumpLaw JumpLawLower
open Classification Classification.Proofs.ChainCorr

/-- The plain child of case 1. -/
def k1 (d : Nat) (S T : Row) (j : Nat) : Item := ⟨slot d S j, slot d T j, none, 0, false⟩

theorem getElem_range_map {α : Type} (n : Nat) (f : Nat → α) (j : Nat)
    (hj : j < ((List.range n).map f).length) : ((List.range n).map f)[j] = f j := by
  simp

/-- An item that copies a root row or has a cut bottom needs an ascending column. -/
theorem asc_true_of_kind {ctx : Context} {d : Nat} {A : Item} {cs : List Item}
    (h : childItems ctx d A = .ok cs) {a : Ref × Cell}
    (hx : topIn ctx.source ctx.x d A.source = some a)
    (hk : A.clean ≠ none ∨ A.cutBottom = true) :
    ascends ctx (topIn ctx.source ctx.rootColumn d A.source) = .ok true := by
  obtain ⟨b, hb⟩ := childItems_asc h hx
  cases b with
  | true => exact hb
  | false =>
    obtain ⟨h1, h2, _⟩ := childItems_case1 h hx hb
    rcases hk with hk | hk
    · exact absurd h1 hk
    · rw [h2] at hk; cases hk

/-- **Case 1.** -/
theorem kids1 {ctx : Context} {d : Nat} {A : Item} {cs : List Item}
    (h : childItems ctx d A = .ok cs) {a : Ref × Cell}
    (hx : topIn ctx.source ctx.x d A.source = some a)
    (hasc : ascends ctx (topIn ctx.source ctx.rootColumn d A.source) = .ok false) :
    A.clean = none ∧ A.cutBottom = false ∧ cs.length = height d (official a.2.row) + 1 ∧
      ∀ j (hj : j < cs.length), cs[j] = k1 d A.source A.target j := by
  obtain ⟨h1, h2, _⟩ := childItems_case1 h hx hasc
  have hl := LowerLeftProof.case1_list h hx hasc
  subst hl
  refine ⟨h1, h2, by simp, fun j hj => ?_⟩
  simp [k1]

/-- **Case 2.** -/
theorem kids2 {ctx : Context} {d : Nat} {A : Item} {cs : List Item}
    (h : childItems ctx d A = .ok cs) (hcl : A.clean = none) (hcb : A.cutBottom = false)
    {a : Ref × Cell} (hx : topIn ctx.source ctx.x d A.source = some a)
    {r : Ref} {cl : Cell} (hrho : topIn ctx.source ctx.rootColumn d A.source = some (r, cl))
    (hasc : ascends ctx (some (r, cl)) = .ok true) :
    cs.length = (((height d (official a.2.row) : Nat) : Int) +
        (((heightOf d (topIn ctx.source ctx.lastColumn d A.source) : Nat) : Int) -
          ((height d (official cl.row) : Nat) : Int)) * (ctx.block : Int) + 1).toNat ∧
      ∀ j (hj : j < cs.length), cs[j] = c2 d A.source A.target ctx.block
        (height d (official cl.row))
        ((((heightOf d (topIn ctx.source ctx.lastColumn d A.source) : Nat) : Int) -
          ((height d (official cl.row) : Nat) : Int)) * (ctx.block : Int)) (official cl.row) j := by
  have hl := childItems_case2 h hcl hcb hx hrho hasc
  subst hl
  exact ⟨by simp, fun j hj => by simp⟩

/-- **Case 3** (block `≠ 0`). -/
theorem kids3 {ctx : Context} {d : Nat} {A : Item} {cs : List Item}
    (h : childItems ctx d A = .ok cs) (hcl : A.clean = none) (hcb : A.cutBottom = true)
    (hblk : ctx.block ≠ 0)
    {a : Ref × Cell} (hx : topIn ctx.source ctx.x d A.source = some a)
    {r : Ref} {cl : Cell} (hrho : topIn ctx.source ctx.rootColumn d A.source = some (r, cl))
    (hasc : ascends ctx (some (r, cl)) = .ok true) :
    cs.length = heightOf d (topIn ctx.result ctx.boundary d A.target) +
        height d (official a.2.row) + 1 - height d (official cl.row) ∧
      ∀ t (ht : t < cs.length), cs[t] = c3 d A.source A.target (height d (official cl.row))
        (heightOf d (topIn ctx.result ctx.boundary d A.target)) (official cl.row)
        (t + height d (official cl.row)) := by
  have hl := childItems_case3 h hcl hcb hx hrho hasc
  rw [if_neg hblk, range_filter_ge, List.map_map] at hl
  subst hl
  exact ⟨by simp, fun t ht => by simp⟩

/-- **Case 4** (block `≠ 0`). -/
theorem kids4 {ctx : Context} {d : Nat} {A : Item} {cs : List Item} {C : Row}
    (h : childItems ctx d A = .ok cs) (hcl : A.clean = some C) (hblk : ctx.block ≠ 0)
    {a : Ref × Cell} (hx : topIn ctx.source ctx.x d A.source = some a)
    {r : Ref} {cl : Cell} (hrho : topIn ctx.source ctx.rootColumn d A.source = some (r, cl))
    (hasc : ascends ctx (some (r, cl)) = .ok true) :
    ∃ csRef csc g, nodeAt ctx.source ctx.x C = some (csRef, csc) ∧
      generations ctx.source ctx.rootColumn C (ctx.x + 1) csRef csc 0 = .ok g ∧
      (A.cutBottom = false →
        (topIn ctx.result ctx.boundary d A.target).isSome ∧ A.offset = 0) ∧
      cs.length = (((heightOf d (topIn ctx.result ctx.boundary d A.target) : Nat) : Int) +
        (g : Int) - (A.offset : Int) + 1).toNat ∧
      ∀ j (hj : j < cs.length), cs[j] = c4 d A.source A.target (height d (official cl.row))
        (heightOf d (topIn ctx.result ctx.boundary d A.target)) A.offset A.cutBottom C j := by
  obtain ⟨csRef, csc, g, hn, hg, hb, hl⟩ := childItems_case4 h hcl hx hrho hasc
  rw [if_neg hblk] at hl
  subst hl
  exact ⟨csRef, csc, g, hn, hg, hb, by simp, fun j hj => by simp⟩

end OmegaY.Official.Recon.LRC
