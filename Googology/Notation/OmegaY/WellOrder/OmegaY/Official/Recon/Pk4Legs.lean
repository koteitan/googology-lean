/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/Pk4Legs.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.CrossPlainPosColumn
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CopyShapeCutForm
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.LiftLegRightProof

set_option backward.do.legacy false

/-!
# Legs and rows of the lower copies of one column

Facts about the traced copy of one column `x` (`c_r < x ≤ x₀`) of a block `i ≥ 1`, for any
context with the source `M(s)`, used by `PairOld` and `PairAbove` (`Pk4Pair.lean`).

* `emitsT_cleanAsc`: the origin row of a clean emit (cut or not) is the row of the root-column
  top of a region where the column ascends (`ProfileLeg.AscRow`). (`runItemT_asc` of
  `CopyShapeCutForm.lean` states this for gap copies only; the proof is the same.)
* `emitsT_cleanLeg`: the origin of a clean emit has its leg at or right of `c_r`
  (`LiftLegPf.ascLegs`: every node of an ascending column in the region has its leg at or right
  of `c_r`).
* `emitsT_plainLeft`: a plain emit whose origin has its leg left of `c_r` has the row of its
  origin (`LegLeft.Items.emitsT_legLeft` with `LiftLegPf.liftLegRight_holds`).
-/

namespace OmegaY.Official.Recon.Pk4

open Canonical Reserve Official Descent Classification Proofs
open OmegaY.Official.Classification.Proofs.CopyShape.ProfileLeg (AscRow ItemInvA childItems_invA)
open OmegaY.Official.Classification.Proofs.ChainCorr.Inner (isCleanO)

/-! ## The origin row of a clean emit -/

theorem levelOneT_ascC {ctx : Context} {it : Item} {ps : List (Emit × Origin)}
    (h : levelOneT ctx it = .ok ps) (hA : ItemInvA ctx it) :
    ∀ p ∈ ps, isCleanO p.2 = true → ∀ c0, cell? ctx.source p.2.src = some c0 →
      AscRow ctx (official c0.row) := by
  unfold levelOneT at h
  cases hsrc : nodeAt ctx.source ctx.x it.source with
  | none =>
      simp [hsrc, pure, Except.pure] at h
      subst h
      simp
  | some q =>
      obtain ⟨srcRef, src⟩ := q
      simp only [hsrc] at h
      cases hC : it.clean with
      | some C =>
          simp only [hC] at h
          cases hcs : nodeAt ctx.source ctx.x C with
          | none => simp [hcs, throw, throwThe, MonadExceptOf.throw] at h
          | some q' =>
              obtain ⟨csRef, cs⟩ := q'
              obtain ⟨_, _, hccell, hcrow⟩ := nodeAt_spec hcs
              simp only [hcs, bind, Except.bind, pure, Except.pure] at h
              split at h
              · cases h
              · cases h
                intro p hp _ c0 hc0
                simp only [List.mem_singleton] at hp
                subst hp
                have hcc : c0 = cs := by
                  simp only [Origin.src] at hc0
                  exact Option.some.inj (hc0.symm.trans hccell)
                subst hcc
                rw [hcrow]
                exact hA C hC
      | none =>
          simp only [hC] at h
          split at h
          · simp only [pure, Except.pure, Except.ok.injEq] at h
            subst h
            intro p hp hk
            simp only [List.mem_singleton] at hp
            subst hp
            simp [isCleanO] at hk
          · simp only [bind, Except.bind, pure, Except.pure] at h
            split at h
            · cases h
            · cases h
              intro p hp hk
              simp only [List.mem_singleton] at hp
              subst hp
              simp [isCleanO] at hk

theorem runItemT_ascC (ctx : Context) :
    ∀ (d : Nat) (it : Item) (ps : List (Emit × Origin)), runItemT ctx (d + 1) it = .ok ps →
      ItemInvA ctx it → ∀ p ∈ ps, isCleanO p.2 = true →
        ∀ c0, cell? ctx.source p.2.src = some c0 → AscRow ctx (official c0.row)
  | 0, it, ps, h, hA => levelOneT_ascC (by simpa [runItemT] using h) hA
  | d + 1, it, ps, h, hA => by
      simp only [runItemT, bind, Except.bind, pure, Except.pure] at h
      split at h
      · cases h
      · rename_i children hch
        split at h
        · cases h
        · rename_i outs houts
          cases h
          obtain ⟨hlen, hall⟩ := mapM_except_spec _ _ _ houts
          intro p hp
          obtain ⟨l, hl, hpl⟩ := List.mem_flatten.mp hp
          obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hl
          have hmem : children[a]'(by omega) ∈ children := List.getElem_mem _
          exact runItemT_ascC ctx d _ _ (hall a (by omega) ha) (childItems_invA hch hA _ hmem) p hpl

/-- **The origin row of a clean emit is an ascending root top.** -/
theorem emitsT_cleanAsc {ctx : Context} {τ : Row} {es : List (Emit × Origin)}
    (h : emitsT ctx τ = .ok es) :
    ∀ p ∈ es, isCleanO p.2 = true → ∀ c0, cell? ctx.source p.2.src = some c0 →
      AscRow ctx (official c0.row) := by
  obtain ⟨lo, us, hlo, hus, rfl⟩ := CrossPlain.emitsT_parts h
  intro p hp hcl c0 hc0
  rcases List.mem_append.mp hp with hp | hp
  · obtain ⟨q, hq, out, hout, hpo⟩ := Recon.LowerPB.lowerT_mem hlo hp
    obtain ⟨k, j, _, _, rfl⟩ := Recon.RowLaw.mem_lowerItems hq
    exact runItemT_ascC ctx k _ out hout (fun C hC => by cases hC) p hpo hcl c0 hc0
  · have hu := CrossPlain.upperT_isUpper hus p hp
    cases ho : p.2 with
    | plain r => rw [ho] at hu; cases hu
    | clean r b => rw [ho] at hu; cases hu
    | upper r => rw [ho] at hcl; cases hcl

/-- **The origin of a clean emit has its leg at or right of `c_r`.** -/
theorem emitsT_cleanLeg {s : List Nat} {M : Mountain} {t : Cell} {root : Ref}
    (hTop : Recon.Top s M t root) {ctx : Context} (hsrc : ctx.source = M)
    (hroot : ctx.rootColumn = root.column) (hcx : root.column < ctx.x) {τ : Row}
    {es : List (Emit × Origin)} (h : emitsT ctx τ = .ok es) :
    ∀ p ∈ es, isCleanO p.2 = true → ∀ c0, cell? M p.2.src = some c0 →
      ∀ l, c0.left = some l → root.column ≤ l.column := by
  intro p hp hcl c0 hc0 l hl
  have hnu : p.2.isUpper = false := by
    cases ho : p.2 with
    | plain r => rfl
    | clean r b => rfl
    | upper r => rw [ho] at hcl; cases hcl
  obtain ⟨hcol, hidx, _⟩ := emitsT_good h p hp
  simp only [hnu, Bool.false_eq_true, if_false] at hcol
  obtain ⟨d, S, ⟨ρr, ρc⟩, hρ, hrow, hasc⟩ :=
    emitsT_cleanAsc h p hp hcl c0 (by rw [hsrc]; exact hc0)
  obtain ⟨aref, acl, hna, hra⟩ := ChainCorr.ascClean_of_ascends hasc
  rw [hsrc] at hna hρ
  rw [hsrc, hroot] at hra
  rw [hroot] at hρ
  obtain ⟨_, hρreg, _⟩ := Recon.RowLaw.topIn_spec hρ
  simp only at hrow hρreg
  have hc : cell? M ⟨ctx.x, p.2.src.index⟩ = some c0 := by
    rw [← hcol]; exact hc0
  exact Recon.LowerPB.LiftLegPf.ascLegs hTop.build hcx hρ hna hra hidx hc
    (by rw [← hrow]; exact hρreg) hl

/-- **A plain emit whose origin has its leg left of `c_r` has the row of its origin.** -/
theorem emitsT_plainLeft {s : List Nat} {M : Mountain} {t : Cell} {root : Ref}
    (hTop : Recon.Top s M t root) {ctx : Context} (hsrc : ctx.source = M)
    (hroot : ctx.rootColumn = root.column) (hcx : root.column < ctx.x)
    (hxx : ctx.x ≤ M.size - 1) {es : List (Emit × Origin)}
    (h : emitsT ctx (official t.row) = .ok es) :
    ∀ p ∈ es, ∀ r, p.2 = .plain r → ∀ c, cell? M r = some c → ∀ l, c.left = some l →
      l.column < root.column → p.1.row = official c.row := by
  have hLL : ChainCorr.LegLeft.Items.LiftCtx ctx (official t.row) := by
    intro d S r' cl hbel htop hasc k hk q hq hin l' hl'
    have := Recon.LowerPB.LiftLegPf.liftLegRight_holds s M t root hTop ctx hsrc hroot hcx hxx
      d S r' cl hbel (by rw [← hroot, ← hsrc]; exact htop) hasc k hk q (by rw [← hsrc]; exact hq)
      hin l' hl'
    rw [hroot]; exact this
  intro p hp r hr c hc l hl hlt
  exact ChainCorr.LegLeft.Items.emitsT_legLeft hLL h p hp r hr c (by rw [hsrc]; exact hc) l hl
    (by rw [hroot]; exact hlt)

end OmegaY.Official.Recon.Pk4

#print axioms OmegaY.Official.Recon.Pk4.emitsT_cleanLeg
#print axioms OmegaY.Official.Recon.Pk4.emitsT_plainLeft
