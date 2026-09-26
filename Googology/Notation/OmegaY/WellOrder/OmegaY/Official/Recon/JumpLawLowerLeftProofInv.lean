/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/JumpLawLowerLeftProofInv.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.LowerLeftBase
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.ChainCorrLegLeftItems

set_option backward.do.legacy false

/-!
# Aligned or right-legged items

For `LowerPairsLeft` (`JumpLawLowerLeft.lean`) we need to know which items of the lower tree of a
copied column can emit a node whose leg is left of `c_r`. This file proves, from the fact
`LiftLegRight` about `M(s)` alone (`ChainCorrLegLeftItems.lean`), that every item of the tree is

* *aligned*: no cut bottom and source region = target region; or
* *right-legged*: every node of the column `x` in its source region has its leg at or right of
  `c_r` (`Items.RightLegs`).

This is the invariant `Items.Inv` of `ChainCorrLegLeftItems.lean` without its third case (cut
and clean): a cut clean item is right-legged, because its source is the slot `S[h_ρ]` of the
root row, and `LiftLegRight` covers the slots `S[k]`, `k ≥ h_ρ`, of an ascending region.

Results:

* `childItems_alignedOrRight`: the invariant passes to the children.
* `inTree_alignedOrRight`: every item of the lower tree satisfies it (first items are aligned).
* `liftCtx_of_lift`: `LiftLegRight` gives the lift fact `Items.LiftCtx` of a new column.
* `aligned_of_leftLeg`: an item whose source region contains a node of `x` with its leg left of
  `c_r` is aligned.
-/

namespace OmegaY.Official.Recon.LowerLeftProof

open Canonical Expansion Dimension RowLaw JumpLaw JumpLawLower
open Classification.Proofs.ChainCorr.LegLeft.Items (RightLegs LiftCtx rightLegs_slot)

/-- An item is aligned (no cut bottom, source = target) or right-legged. -/
def AlignedOrRight (ctx : Context) (d : Nat) (it : Item) : Prop :=
  (it.cutBottom = false ∧ it.source = it.target) ∨ RightLegs ctx d it.source

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
set_option linter.unnecessarySeqFocus false in
set_option maxHeartbeats 400000 in
/-- **The invariant passes to the children.** -/
theorem childItems_alignedOrRight {ctx : Context} {d : Nat} {it : Item} {cs : List Item}
    (h : childItems ctx (d + 2) it = .ok cs) (hit : AlignedOrRight ctx (d + 2) it)
    (hlift : ∀ r cl, topIn ctx.source ctx.rootColumn (d + 2) it.source = some (r, cl) →
      ascends ctx (some (r, cl)) = .ok true →
      ∀ k, (official cl.row).coeff d ≤ k → RightLegs ctx (d + 1) (slot (d + 2) it.source k)) :
    ∀ c ∈ cs, AlignedOrRight ctx (d + 1) c := by
  rcases hit with ⟨hcb, hst⟩ | hright
  swap
  · intro c hc
    obtain ⟨j, hj⟩ := Classification.Proofs.ChainCorr.LegJump.childItems_source h c hc
    refine Or.inr ?_
    rw [hj]
    exact rightLegs_slot hright j
  unfold childItems at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  generalize hrho : topIn ctx.source ctx.rootColumn (d + 2) it.source = rho at h
  split at h
  · obtain rfl := Except.ok.inj h
    simp
  · split at h
    · cases h
    · rename_i v hv
      split at h
      · -- case 1: not ascending
        split at h
        · simp [throw, throwThe, MonadExceptOf.throw] at h
        · obtain rfl := Except.ok.inj h
          intro c hc
          simp only [List.mem_map, List.mem_range] at hc
          obtain ⟨j, _, rfl⟩ := hc
          exact Or.inl ⟨rfl, by simp [hst]⟩
      · rename_i hasc
        have hvt : v = true := by simpa using hasc
        subst hvt
        have hsome : ∃ r cl, rho = some (r, cl) := by
          cases rho with
          | none => simp [ascends, pure, Except.pure] at hv
          | some p => exact ⟨p.1, p.2, rfl⟩
        obtain ⟨r, cl, rfl⟩ := hsome
        have hL := hlift r cl hrho hv
        generalize heightOf (d + 2) (topIn ctx.source ctx.lastColumn (d + 2) it.source) = hK at h
        generalize heightOf (d + 2) (topIn ctx.result ctx.boundary (d + 2) it.target) = hB at h
        simp only [heightOf, Recon.RowLaw.height_eq] at h
        generalize (official cl.row).coeff d = hR at h hL
        split at h
        · rename_i hclean
          split at h
          · -- case 2
            obtain rfl := Except.ok.inj h
            generalize hedef : (if d + 2 = 2 then 1 else 0 : Int) = e
            have he : 0 ≤ e := by rw [← hedef]; split <;> omega
            intro c hc
            simp only [List.mem_map, List.mem_range] at hc
            obtain ⟨j, _, rfl⟩ := hc
            by_cases h1 : j < hR
            · simp only [h1, if_true]
              exact Or.inl ⟨rfl, by simp [hst]⟩
            · simp only [h1, if_false]
              by_cases h2 : (j : Int) < hR + ((hK : Int) - hR) * ctx.block + e
              · simp only [h2, if_true]
                exact Or.inr (hL _ le_rfl)
              · simp only [h2, if_false]
                exact Or.inr (hL _ (by omega))
          · -- case 3: a cut item is not aligned
            rename_i hcut
            exfalso
            simp [hcb] at hcut
        · -- case 4
          rename_i C hC
          split at h
          · simp [throw, throwThe, MonadExceptOf.throw] at h
          · split at h
            · cases h
            · split at h
              · simp [throw, throwThe, MonadExceptOf.throw] at h
              · obtain rfl := Except.ok.inj h
                intro c hc
                simp only [List.mem_map, List.mem_range] at hc
                obtain ⟨j, _, rfl⟩ := hc
                simp only [hcb, Bool.false_eq_true, if_false]
                by_cases h1 : j < hR
                · simp only [h1, if_true]
                  exact Or.inl ⟨rfl, by simp [hst]⟩
                · simp only [h1, if_false]
                  exact Or.inr (hL _ le_rfl)

/-- **Along a descent the invariant is kept** (the regions stay below `τ`). -/
theorem desc_alignedOrRight {ctx : Context} {τ : Row} (hLL : LiftCtx ctx τ) {d : Nat} {A : Item}
    {d' : Nat} {B : Item} (hD : Desc ctx d A d' B) :
    (∀ r, inRegion d A.source r = true → r < τ) → AlignedOrRight ctx d A →
      AlignedOrRight ctx d' B := by
  induction hD with
  | refl => exact fun _ h => h
  | @step d A cs c d' B hcs hc _ ih =>
    intro hbel hA
    have hci := childItems_alignedOrRight hcs hA
      (fun r cl hr hv k hk => hLL d A.source r cl hbel hr hv k hk)
    apply ih _ (hci c hc)
    obtain ⟨j, hj⟩ := Classification.Proofs.ChainCorr.LegJump.childItems_source hcs c hc
    intro r hr
    rw [hj] at hr
    exact hbel r (inRegion_of_slot hr)

/-- **Every item of the lower tree is aligned or right-legged.** -/
theorem inTree_alignedOrRight {ctx : Context} {τ : Row} (hLL : LiftCtx ctx τ) {d : Nat}
    {B : Item} (hB : InTree ctx τ d B) : AlignedOrRight ctx d B := by
  obtain ⟨F, hF, hD⟩ := hB
  have hbel := (lower_itemOK (ctx := ctx) hF).1.below
  obtain ⟨k, j, _, _, hFeq⟩ := mem_lowerItems hF
  apply desc_alignedOrRight hLL hD hbel
  rw [hFeq]
  exact Or.inl ⟨rfl, rfl⟩

/-- **`LiftLegRight` gives the lift fact of a new column.** -/
theorem liftCtx_of_lift (hLift : Classification.Proofs.ChainCorr.LegLeft.LiftLegRight)
    {s : List Nat} {ctx : Context} {t : Cell} {root : Ref} (hctx : RunCtx s ctx t root) :
    LiftCtx ctx (official t.row) := by
  intro d S r cl hbel htop hasc k hk q hq hin l hl
  have h := hLift s ctx.source t root hctx.top ctx rfl hctx.rootc
    (by rw [← hctx.rootc]; exact hctx.xgt) (by rw [← hctx.last]; exact hctx.xle) d S r cl hbel
    (by rw [← hctx.rootc]; exact htop) hasc k hk q hq hin l hl
  rw [hctx.rootc]
  exact h

/-- **An item whose source region holds a node of `x` with its leg left of `c_r` is aligned.** -/
theorem aligned_of_leftLeg {ctx : Context} {d : Nat} {B : Item} (hB : AlignedOrRight ctx d B)
    {u : Ref × Cell} (hu : u ∈ realNodes ctx.source ctx.x)
    (hin : inRegion d B.source (official u.2.row) = true) {l : Nat}
    (hul : leftColumn u.2 = .ok l) (hlt : l < ctx.rootColumn) :
    B.cutBottom = false ∧ B.source = B.target := by
  rcases hB with h | h
  · exact h
  · exfalso
    obtain ⟨ref, href, hrefc⟩ := Classification.leftColumn_ok hul
    have := h u hu hin ref href
    omega

end OmegaY.Official.Recon.LowerLeftProof

#print axioms OmegaY.Official.Recon.LowerLeftProof.childItems_alignedOrRight
#print axioms OmegaY.Official.Recon.LowerLeftProof.inTree_alignedOrRight
#print axioms OmegaY.Official.Recon.LowerLeftProof.liftCtx_of_lift
#print axioms OmegaY.Official.Recon.LowerLeftProof.aligned_of_leftLeg
