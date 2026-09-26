/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/JumpLawLowerLeftProofParts.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.JumpLawLowerLeftProofInv

set_option backward.do.legacy false

/-!
# Parts of the proof of `LowerPairsLeft`

* `slot_inj`: slots of one region with different indices differ.
* `prev_of_aligned`: in the children of an aligned item of block `i ≥ 1`, the child before an
  aligned child is a plain aligned child `(S[j], S[j], ⊥, 0, 0)`. (Case 2 lifts by at least one
  slot, so no lifted child is aligned; the aligned copies of the root row sit at `j = h_ρ`; case
  3 needs a cut bottom; case 4 without a cut bottom copies the slots below `h_ρ` plainly.)
* `desc_trans`: descents compose.
* `theta_item`: every node of the lower part is emitted by an item of level one of the tree.
* `theta_source`: (from `LiftLegRight`) a node of the lower part whose leg is left of `c_r` is
  emitted by an aligned item of level one, i.e. it keeps the row of its source node `u`, and
  the leg of `u` is its leg.
-/

namespace OmegaY.Official.Recon.LowerLeftProof

open Canonical Expansion Dimension RowLaw JumpLaw JumpLawLower

/-- Slots of one region with different indices differ. -/
theorem slot_inj {d : Nat} {S : Row} {a b : Nat} (h : slot (d + 2) S a = slot (d + 2) S b) :
    a = b := by
  have ha := (inRegion_slot_iff.mp (self_inRegion (d + 1) (slot (d + 2) S a))).2
  have hb := (inRegion_slot_iff.mp (self_inRegion (d + 1) (slot (d + 2) S b))).2
  rw [h] at ha
  omega

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
set_option linter.unnecessarySeqFocus false in
set_option maxHeartbeats 800000 in
/-- **The child before an aligned child of an aligned item is plain and aligned.** Here `hmd`
is (MD) at the top: the root column is lower than the last column in the region (`md_top`), so
case 2 lifts by at least one slot in a block `i ≥ 1`. -/
theorem prev_of_aligned {ctx : Context} {d : Nat} {it : Item} {cs : List Item}
    (h : childItems ctx (d + 2) it = .ok cs) (hcb : it.cutBottom = false)
    (hst : it.source = it.target)
    (hmd : ∀ r cl, topIn ctx.source ctx.rootColumn (d + 2) it.source = some (r, cl) →
      (official cl.row).coeff d <
        heightOf (d + 2) (topIn ctx.source ctx.lastColumn (d + 2) it.source))
    (hi : 1 ≤ ctx.block) {j : Nat} (hj : j + 1 < cs.length)
    (hal : cs[j + 1].source = cs[j + 1].target) :
    cs[j] = ⟨slot (d + 2) it.source j, slot (d + 2) it.target j, none, 0, false⟩ := by
  unfold childItems at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  generalize hrho : topIn ctx.source ctx.rootColumn (d + 2) it.source = rho at h
  split at h
  · obtain rfl := Except.ok.inj h
    simp at hj
  · split at h
    · cases h
    · rename_i v hv
      split at h
      · -- case 1: not ascending
        split at h
        · simp [throw, throwThe, MonadExceptOf.throw] at h
        · obtain rfl := Except.ok.inj h
          simp only [List.getElem_map, List.getElem_range]
      · rename_i hasc
        have hvt : v = true := by simpa using hasc
        subst hvt
        have hsome : ∃ r cl, rho = some (r, cl) := by
          cases rho with
          | none => simp [ascends, pure, Except.pure] at hv
          | some p => exact ⟨p.1, p.2, rfl⟩
        obtain ⟨r, cl, rfl⟩ := hsome
        have hlt := hmd r cl hrho
        generalize heightOf (d + 2) (topIn ctx.source ctx.lastColumn (d + 2) it.source) = hK
          at h hlt
        generalize heightOf (d + 2) (topIn ctx.result ctx.boundary (d + 2) it.target) = hB at h
        simp only [heightOf, Recon.RowLaw.height_eq] at h
        generalize (official cl.row).coeff d = hR at h hlt
        split at h
        · rename_i hclean
          split at h
          · -- case 2
            obtain rfl := Except.ok.inj h
            have hlift : (1 : Int) ≤ ((hK : Int) - hR) * ctx.block := by
              have h1 : (1 : Int) ≤ (hK : Int) - hR := by omega
              have h2 : (1 : Int) ≤ (ctx.block : Int) := by omega
              have := Int.mul_le_mul h1 h2 (by omega) (by omega)
              simpa using this
            simp only [List.getElem_map, List.getElem_range] at hal ⊢
            have hjR : j < hR := by
              by_contra hjR
              have h1 : ¬ j + 1 < hR := by omega
              simp only [h1, if_false] at hal
              have key : ∀ a b : Nat, slot (d + 2) it.source a = slot (d + 2) it.target b → a = b :=
                fun a b hab => slot_inj (by rw [hst] at hab; exact hab)
              split at hal <;> split at hal <;> (dsimp only at hal; have := key _ _ hal; omega)
            simp only [hjR, if_true]
          · -- case 3 needs a cut bottom
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
                simp only [List.getElem_map, List.getElem_range] at hal ⊢
                simp only [hcb, Bool.false_eq_true, if_false] at hal ⊢
                have hjR : j < hR := by
                  by_contra hjR
                  have h1 : ¬ j + 1 < hR := by omega
                  simp only [h1, if_false] at hal
                  rw [hst] at hal
                  have := slot_inj hal
                  omega
                simp only [hjR, if_true]

/-- Descents compose. -/
theorem desc_trans {ctx : Context} {d : Nat} {A : Item} {d' : Nat} {B : Item} {d'' : Nat}
    {C : Item} (h1 : Desc ctx d A d' B) (h2 : Desc ctx d' B d'' C) : Desc ctx d A d'' C := by
  induction h1 with
  | refl => exact h2
  | step hcs hc _ ih => exact .step hcs hc (ih h2)

/-- **Every node of the lower part is emitted by an item of level one.** -/
theorem theta_item {s : List Nat} {ctx : Context} {t : Cell} {root : Ref}
    (hctx : RunCtx s ctx t root) {vs : List (List Emit)}
    (hvs : LowerRun ctx (official t.row) vs) {em : Emit} (hem : em ∈ vs.flatten) :
    ∃ J1 L1, InTree ctx (official t.row) 1 J1 ∧ runItem ctx 1 J1 = .ok L1 ∧ em ∈ L1 := by
  obtain ⟨F, hF, hin⟩ := JumpLaw.lowerItems_cover (official t.row) (lower_lt hctx hvs em hem)
  obtain ⟨LF, hLF, hemF, _⟩ := mem_first_output hctx hvs hF hem hin
  obtain ⟨hFOK, _, hF1, _⟩ := lower_itemOK (ctx := ctx) hF
  obtain ⟨m, hm⟩ : ∃ m, F.1 = 0 + 1 + m := ⟨F.1 - 1, by omega⟩
  have hFOK' := hFOK
  rw [hm] at hFOK' hLF
  obtain ⟨J, LJ, hD, hLJ, hemJ⟩ := descend_to hctx 0 m F.2 LF em hFOK' hLF hemF
  have hD' : Desc ctx F.1 F.2 1 J := by rw [hm]; exact hD
  exact ⟨J, LJ, ⟨F, hF, hD'⟩, hLJ, hemJ⟩

/-- The items of the lower tree satisfy the item hypotheses. -/
theorem inTree_itemOK {s : List Nat} {ctx : Context} {t : Cell} {root : Ref}
    (hctx : RunCtx s ctx t root) {d : Nat} {B : Item} (hB : InTree ctx (official t.row) d B) :
    1 ≤ d ∧ ItemOK ctx (official t.row) d B := by
  obtain ⟨F, hF, hD⟩ := hB
  obtain ⟨hFOK, _, hF1, _⟩ := lower_itemOK (ctx := ctx) hF
  obtain ⟨hd1, _, hBOK, _⟩ := desc_facts hctx hD hF1 hFOK
  exact ⟨hd1, hBOK⟩

/-- **A node with its leg left of `c_r` keeps the row of its source node** (from `LiftLegRight`).
Its item of level one is aligned (not cut, source = target), and the source node `u` of the
column `x` has the row of the node and the leg of the node. -/
theorem theta_source (hLift : Classification.Proofs.ChainCorr.LegLeft.LiftLegRight)
    {s : List Nat} {ctx : Context} {t : Cell} {root : Ref} (hctx : RunCtx s ctx t root)
    {J1 : Item} (hJ1 : InTree ctx (official t.row) 1 J1) {L1 : List Emit}
    (hL1 : runItem ctx 1 J1 = .ok L1) {em : Emit} (hem : em ∈ L1) {l : Nat}
    (hleft : em.leftColumn = some l) (hlt : l < ctx.rootColumn) :
    J1.cutBottom = false ∧ J1.source = em.row ∧
      ∃ u ∈ realNodes ctx.source ctx.x, official u.2.row = em.row ∧ leftColumn u.2 = .ok l := by
  obtain ⟨u, hu, hurow, hul⟩ := levelOne_leg hJ1 hL1 hem hleft
  have hinv := inTree_alignedOrRight (liftCtx_of_lift hLift hctx) hJ1
  have hin : inRegion 1 J1.source (official u.2.row) = true := by
    rw [hurow]; exact self_inRegion 1 J1.source
  obtain ⟨hcb, hst⟩ := aligned_of_leftLeg hinv hu hin hul hlt
  obtain ⟨_, hJ1OK⟩ := inTree_itemOK hctx hJ1
  have hgood := runItem_good hctx 1 le_rfl J1 hJ1OK L1 hL1
  have hrow : em.row = J1.target := inRegion_one_iff.mp (hgood.1.2.1 em hem)
  refine ⟨hcb, by rw [hst, hrow], u, hu, by rw [hurow, hst, hrow], hul⟩

end OmegaY.Official.Recon.LowerLeftProof

#print axioms OmegaY.Official.Recon.LowerLeftProof.prev_of_aligned
#print axioms OmegaY.Official.Recon.LowerLeftProof.theta_source
