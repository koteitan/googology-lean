/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/CutPredShape.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.CutPredBase

set_option backward.do.legacy false

/-!
# The children of an item, case by case

`Official.childItems` (notes/03-official-rule.md §2.4) written out in the four cases of the
rule: no node of column `x` in the region (`childItems_none`), case 1 (`childItems_case1`,
no ascension: all children plain), case 2 (`c2`, lifting), case 3 (`c3`, cut bottom) and
case 4 (`c4`, copies of the root row). Each lemma reads the list of children off a
successful call.
-/

namespace OmegaY.Official.Recon
open Canonical Official Classification

/-- A child of case 2 (lifting): `j < hρ` plain, `hρ ≤ j < hρ + Δ + e` a copy of the root
row (cut when `j > hρ`), above it the lifted slots (cut bottom when `i ≠ 0`, `j = hρ + Δ`). -/
def c2 (d : Nat) (S T : Row) (i hR : Nat) (lift : Int) (C : Row) (j : Nat) : Item :=
  if j < hR then ⟨slot d S j, slot d T j, none, 0, false⟩
  else if (j : Int) < hR + lift + (if d = 2 then 1 else 0) then
    ⟨slot d S hR, slot d T j, some C, 0, decide (hR < j)⟩
  else ⟨slot d S ((j : Int) - lift).toNat, slot d T j, none, 0, decide (i ≠ 0 ∧ (j : Int) = hR + lift)⟩

/-- A child of case 3 (cut bottom). -/def c3 (d : Nat) (S T : Row) (hR hB : Nat) (C : Row) (j : Nat) : Item :=
  if (j : Int) < (hB : Int) + (hR : Int) + (if d = 2 then 1 else 0) then
    ⟨slot d S hR, slot d T (j - hR), some C, 0, true⟩
  else ⟨slot d S (j - hB), slot d T (j - hR), none, 0, decide (j = hB + hR)⟩

/-- A child of case 4 (copy of the root row `C`). -/
def c4 (d : Nat) (S T : Row) (hR hB off : Nat) (cb : Bool) (C : Row) (j : Nat) : Item :=
  if cb then ⟨slot d S hR, slot d T j, some C, ((j : Int) - hB + off).toNat, true⟩
  else if j < hR then ⟨slot d S j, slot d T j, none, 0, false⟩
  else ⟨slot d S hR, slot d T j, some C, ((j : Int) - hB + off).toNat, decide (hR < j)⟩

theorem childItems_none {ctx : Context} {d : Nat} {it : Item} {cs : List Item}
    (h : childItems ctx d it = .ok cs) (hx : topIn ctx.source ctx.x d it.source = none) :
    cs = [] := by
  unfold childItems at h
  simp only [hx, pure, Except.pure] at h
  exact (Except.ok.inj h).symm

theorem childItems_asc {ctx : Context} {d : Nat} {it : Item} {cs : List Item}
    (h : childItems ctx d it = .ok cs) {a : Ref × Cell}
    (hx : topIn ctx.source ctx.x d it.source = some a) :
    ∃ b, ascends ctx (topIn ctx.source ctx.rootColumn d it.source) = .ok b := by
  unfold childItems at h
  simp only [hx, bind, Except.bind] at h
  cases hasc : ascends ctx (topIn ctx.source ctx.rootColumn d it.source) with
  | error e => rw [hasc] at h; cases h
  | ok b => exact ⟨b, rfl⟩

theorem childItems_case1 {ctx : Context} {d : Nat} {it : Item} {cs : List Item}
    (h : childItems ctx d it = .ok cs) {a : Ref × Cell}
    (hx : topIn ctx.source ctx.x d it.source = some a)
    (hasc : ascends ctx (topIn ctx.source ctx.rootColumn d it.source) = .ok false) :
    it.clean = none ∧ it.cutBottom = false ∧ ∀ c ∈ cs, c.clean = none ∧ c.cutBottom = false := by
  unfold childItems at h
  simp only [hx, hasc, bind, Except.bind, pure, Except.pure] at h
  simp only [Bool.false_eq_true, not_false_eq_true, if_true] at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  · rename_i hc
    refine ⟨?_, ?_, ?_⟩
    · cases hcl : it.clean with
      | none => rfl
      | some _ => simp [hcl] at hc
    · cases hcb : it.cutBottom with
      | false => rfl
      | true => simp [hcb] at hc
    · obtain rfl := (Except.ok.inj h).symm
      intro c hc'
      simp only [List.mem_map] at hc'
      obtain ⟨j, _, rfl⟩ := hc'
      exact ⟨rfl, rfl⟩

theorem childItems_case2 {ctx : Context} {d : Nat} {it : Item} {cs : List Item}
    (h : childItems ctx d it = .ok cs) (hcl : it.clean = none) (hcb : it.cutBottom = false)
    {a : Ref × Cell} (hx : topIn ctx.source ctx.x d it.source = some a)
    {r : Ref} {cl : Cell} (hrho : topIn ctx.source ctx.rootColumn d it.source = some (r, cl))
    (hasc : ascends ctx (some (r, cl)) = .ok true) :
    cs = (List.range (((height d (official a.2.row) : Nat) : Int) +
        (((heightOf d (topIn ctx.source ctx.lastColumn d it.source) : Nat) : Int) -
          ((height d (official cl.row) : Nat) : Int)) * (ctx.block : Int) + 1).toNat).map
      (c2 d it.source it.target ctx.block (height d (official cl.row))
        ((((heightOf d (topIn ctx.source ctx.lastColumn d it.source) : Nat) : Int) -
          ((height d (official cl.row) : Nat) : Int)) * (ctx.block : Int)) (official cl.row)) := by
  unfold childItems at h
  simp only [hx, hrho, hasc, hcl, hcb, bind, Except.bind, pure, Except.pure] at h
  simp only [not_true_eq_false, if_false, Bool.false_eq_true, not_false_eq_true, if_true] at h
  exact (Except.ok.inj h).symm

theorem childItems_case3 {ctx : Context} {d : Nat} {it : Item} {cs : List Item}
    (h : childItems ctx d it = .ok cs) (hcl : it.clean = none) (hcb : it.cutBottom = true)
    {a : Ref × Cell} (hx : topIn ctx.source ctx.x d it.source = some a)
    {r : Ref} {cl : Cell} (hrho : topIn ctx.source ctx.rootColumn d it.source = some (r, cl))
    (hasc : ascends ctx (some (r, cl)) = .ok true) :
    cs = ((List.range ((if ctx.block = 0 then height d (official a.2.row)
        else heightOf d (topIn ctx.result ctx.boundary d it.target) + height d (official a.2.row))
          + 1)).filter (fun j => decide (height d (official cl.row) ≤ j))).map
      (c3 d it.source it.target (height d (official cl.row))
        (heightOf d (topIn ctx.result ctx.boundary d it.target)) (official cl.row)) := by
  unfold childItems at h
  simp only [hx, hrho, hasc, hcl, hcb, bind, Except.bind, pure, Except.pure] at h
  simp only [not_true_eq_false, if_false] at h
  exact (Except.ok.inj h).symm

theorem childItems_case4 {ctx : Context} {d : Nat} {it : Item} {cs : List Item} {C : Row}
    (h : childItems ctx d it = .ok cs) (hcl : it.clean = some C)
    {a : Ref × Cell} (hx : topIn ctx.source ctx.x d it.source = some a)
    {r : Ref} {cl : Cell} (hrho : topIn ctx.source ctx.rootColumn d it.source = some (r, cl))
    (hasc : ascends ctx (some (r, cl)) = .ok true) :
    ∃ csRef csc g, nodeAt ctx.source ctx.x C = some (csRef, csc) ∧
      generations ctx.source ctx.rootColumn C (ctx.x + 1) csRef csc 0 = .ok g ∧
      (it.cutBottom = false → (topIn ctx.result ctx.boundary d it.target).isSome ∧ it.offset = 0) ∧
      cs = (List.range ((if ctx.block = 0 then ((height d (official a.2.row) : Nat) : Int)
          else ((heightOf d (topIn ctx.result ctx.boundary d it.target) : Nat) : Int) + (g : Int)
            - (it.offset : Int)) + 1).toNat).map
        (c4 d it.source it.target (height d (official cl.row))
          (heightOf d (topIn ctx.result ctx.boundary d it.target)) it.offset it.cutBottom C) := by
  unfold childItems at h
  simp only [hx, hrho, hasc, hcl, bind, Except.bind, pure, Except.pure] at h
  simp only [not_true_eq_false, if_false] at h
  cases hcs : nodeAt ctx.source ctx.x C with
  | none => simp [hcs, throw, throwThe, MonadExceptOf.throw] at h
  | some q =>
    obtain ⟨csRef, csc⟩ := q
    simp only [hcs] at h
    cases hg : generations ctx.source ctx.rootColumn C (ctx.x + 1) csRef csc 0 with
    | error e => simp [hg] at h
    | ok g =>
      simp only [hg] at h
      split at h
      · simp [throw, throwThe, MonadExceptOf.throw] at h
      · rename_i hthrow
        refine ⟨csRef, csc, g, rfl, hg, ?_, (Except.ok.inj h).symm⟩
        intro hcb
        simp only [hcb, Bool.false_eq_true, not_false_eq_true, true_and, not_or,
          Option.isNone_iff_eq_none] at hthrow
        refine ⟨?_, by simpa using hthrow.2⟩
        cases hb : topIn ctx.result ctx.boundary d it.target with
        | none => exact absurd hb hthrow.1
        | some _ => rfl
end OmegaY.Official.Recon
