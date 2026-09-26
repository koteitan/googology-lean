/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/CutPredMain.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.CutPredItems

set_option backward.do.legacy false

/-!
# `CutPredHolds` from two facts about the run

`CutPredItems.lean` shows, by induction on the level, that the output of every first item of
the rule satisfies `CutSeq p out` for every `p` (a first item is plain: `C = ⊥`, `b = 0`),
provided the context satisfies `LiftPos` and `CleanGap`. The upper part emits no cut node.
So the whole emitted list satisfies `CutPred` (`cutPred_of_ctx`), and `CutPredHolds` follows
from the two facts for the contexts of the run (`cutPredHolds_of_facts`).

* `LiftPosHolds` (fact MD, proved in `CutPredLift.lean`): a statement about the source
  mountain `M(s)` alone. In a region
  of level `d ≥ 3` below `τ`, if an inner column `x` (`c_r < x ≤ x₀`) ascends and has a node
  on the row of `ρ = top_S(c_r)`, then `h_ρ < h_κ` (`κ = top_S(x₀)`): the lift `Δ` of case 2
  is never `0` for `i ≠ 0`.
* `CleanGapHolds` (proved in `CutPredBoundary.lean`): for a reached clean item of level `≥ 2`
  with `i ≠ 0` that reaches case 4, `h_ρ ≤ h_B + g`.

The unconditional `CutPredHolds` is `CutPredMD.cutPredHolds` (`CutPredBoundary.lean`).

## Numerical check

`reference/official/cut-pred.cjs` tests `CutPred` on every copied column, `LiftPos` on every
lower region of level `≥ 3` that has a node of column `c_r` (not only the reached ones), and
`CleanGap` on every reached clean item. No failure:

| sample | cut emits | `LiftPos` | `CleanGap` |
|---|---:|---:|---:|
| standard S1–S3, S6, `n = 1,2,3` | 925614 | 26334 | 26334 |
| legal, length ≤ 6, entries ≤ 6 | 225731 | 17394 | 17394 |
| legal, length ≤ 5, entries ≤ 8 | 467536 | 21867 | 21867 |
| random legal (`--random 20000,10,10,7`) | 3941178 | 93114 | 93114 |

In every tested case `CleanGap` is strict (`h_ρ < h_B + g`).
-/

namespace OmegaY.Official.Recon
open Canonical Official Classification

/-! ## The first items and the upper part -/

theorem lowerItems_plain {τ : Row} {d : Nat} {it : Item} (h : (d, it) ∈ lowerItems τ) :
    it.clean = none ∧ it.cutBottom = false := by
  simp only [lowerItems, List.mem_flatMap, List.mem_reverse, List.mem_range,
    List.mem_map] at h
  obtain ⟨k, _, j, _, he⟩ := h
  obtain ⟨-, rfl⟩ := Prod.mk.inj he.symm
  exact ⟨rfl, rfl⟩

theorem upperT_noCut {ctx : Context} {τ : Row} {u : List EO} (h : upperT ctx τ = .ok u) :
    ∀ e ∈ u, ∀ r, e.2 ≠ .clean r true := by
  unfold upperT at h
  have hF := forall₂_of_mapM h
  intro e he r hr
  obtain ⟨p, _, hp⟩ := forall₂_mem_right hF e he
  simp only [bind, Except.bind, pure, Except.pure] at hp
  cases hl : leftColumn p.2 with
  | error _ => rw [hl] at hp; cases hp
  | ok lc =>
    rw [hl] at hp
    simp only [Except.ok.injEq] at hp
    rw [← hp] at hr
    cases hr

theorem emitsT_parts {ctx : Context} {τ : Row} {es : List EO} (h : emitsT ctx τ = .ok es) :
    ∃ outs u, List.Forall₂ (fun p o => runItemT ctx p.1 p.2 = .ok o) (lowerItems τ) outs ∧
      upperT ctx τ = .ok u ∧ es = outs.flatten ++ u := by
  simp only [emitsT, lowerT, bind, Except.bind, pure, Except.pure] at h
  cases hl : (lowerItems τ).mapM (fun p => runItemT ctx p.1 p.2) with
  | error _ => rw [hl] at h; cases h
  | ok outs =>
    rw [hl] at h
    simp only at h
    cases hu : upperT ctx τ with
    | error _ => rw [hu] at h; cases h
    | ok u =>
      rw [hu] at h
      simp only [Except.ok.injEq] at h
      exact ⟨outs, u, forall₂_of_mapM hl, rfl, h.symm⟩

/-- **`CutPred` for one context.** -/
theorem cutPred_of_ctx {ctx : Context} {τ : Row} (H1 : CleanGap ctx τ) (H2 : LiftPos ctx τ)
    {es : List EO} (h : emitsT ctx τ = .ok es) : CutPred es := by
  obtain ⟨outs, u, hF, hu, rfl⟩ := emitsT_parts h
  apply cutPred_of_cutSeq
  rw [cutSeq_append]
  refine ⟨?_, cutSeq_of_noCut _ u (upperT_noCut hu)⟩
  apply cutSeq_flatten_all
  intro o ho p
  obtain ⟨⟨d, it⟩, hmem, hrun⟩ := forall₂_mem_right hF o ho
  obtain ⟨hcl, hcb⟩ := lowerItems_plain hmem
  exact (spec_all H1 H2 d it o (Reached.root hmem) hrun).plain hcl hcb p

/-! ## The two facts for the run -/

/-- **Fact MD** (proved: `CutPredMD.liftPosHolds`). A statement about the source mountain alone: for every context whose
source is `M(s)`, with root column `c_r`, last column `x₀` and a column `c_r < x ≤ x₀`,
`LiftPos` holds. -/
def LiftPosHolds : Prop :=
  ∀ (s : List Nat) (M : Mountain) (col : Column) (t : Cell) (root : Ref),
    Canonical.build s = .ok M → M[M.size - 1]? = some col → col.back? = some t →
    t.left = some root → root.column < M.size - 1 →
    ∀ ctx : Context, ctx.source = M → ctx.rootColumn = root.column →
      ctx.lastColumn = M.size - 1 → root.column < ctx.x → ctx.x ≤ M.size - 1 →
      LiftPos ctx (official t.row)

/-- `CleanGap` for the contexts of the copied columns of every run (proved:
`CutPredMD.cleanGapHolds`). -/
def CleanGapHolds : Prop :=
  ∀ (s : List Nat) (n : Nat) (R : Mountain), Official.expandDiagram s n = .ok R →
    ∀ (M : Mountain) (col : Column) (t : Cell) (root : Ref) (x i : Nat),
      Canonical.build s = .ok M → M[M.size - 1]? = some col → col.back? = some t →
      t.left = some root → root.column < M.size - 1 →
      x ∈ blockColumns root.column (M.size - 1) n i →
      CleanGap (ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1)
        (x + (M.size - 1 - root.column) * i)) (official t.row)

/-- **`CutPredHolds` from the two facts.** -/
theorem cutPredHolds_of_facts (hL : LiftPosHolds) (hC : CleanGapHolds) : CutPredHolds := by
  intro s n R hrun M col t root x i es hM hcol ht hroot hcr hxb hes
  obtain ⟨h1, h2⟩ := mem_blockColumns hcr hxb
  exact cutPred_of_ctx (hC s n R hrun M col t root x i hM hcol ht hroot hcr hxb)
    (hL s M col t root hM hcol ht hroot hcr _ rfl rfl rfl h1 h2) hes

/-- **`CrossChainHolds` from `ParentBelowHolds`, the two facts and three kinds.** -/
theorem crossChainHolds_of_facts (hPB : ParentBelowHolds) (hP : CrossLexFor IsPlain)
    (hCl : CrossLexFor IsClean) (hL : LiftPosHolds) (hG : CleanGapHolds)
    (hU : CrossLexFor IsUpper) : CrossChainHolds :=
  crossChainHolds_of_three hPB hP hCl (cutPredHolds_of_facts hL hG) hU

end OmegaY.Official.Recon

#print axioms OmegaY.Official.Recon.cutPred_of_ctx
#print axioms OmegaY.Official.Recon.cutPredHolds_of_facts
#print axioms OmegaY.Official.Recon.crossChainHolds_of_facts
