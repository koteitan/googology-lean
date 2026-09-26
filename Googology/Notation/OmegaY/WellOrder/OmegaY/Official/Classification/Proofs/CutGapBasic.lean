/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/CutGapBasic.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CutGapLeg

set_option backward.do.legacy false

/-!
# Small facts about emits (`CutGap`)

* `emitOK_reg`, `emitOK_clean`: read off `ChainCorr.Inner.EmitOK`.
* `cut_le_rootTop`: the origin row of a gap copy is at most the row of the top of the root
  column in every region that contains it (its origin row is the row of a node of the root
  column, `CleanTopP`). This replaces (MA), which is false (`CopyShapeMAFalse.lean`).
-/

namespace OmegaY.Official.Classification.Proofs.CutGap

open Canonical Reserve Official Descent Classification Proofs CopyShape

/-- The origin of an emit lies in the source region of its item. -/
theorem emitOK_reg {M : Mountain} {cr d : Nat} {it : Item} {p : Emit × Origin}
    (hk : ChainCorr.Inner.EmitOK M cr d it p) {c0 : Cell} (hc0 : cell? M p.2.src = some c0) :
    inRegion d it.source (official c0.row) = true := by
  obtain ⟨_, c, hc, hreg, _⟩ := hk
  rw [hc0] at hc
  cases hc
  exact hreg

/-- A clean item with `b = 0` copies rows at or below its row `C`. -/
theorem emitOK_clean {M : Mountain} {cr d : Nat} {S T C : Row} {o : Nat} {p : Emit × Origin}
    (hk : ChainCorr.Inner.EmitOK M cr d ⟨S, T, some C, o, false⟩ p) {c0 : Cell}
    (hc0 : cell? M p.2.src = some c0) : official c0.row ≤ C := by
  obtain ⟨_, c, hc, _, h1, _⟩ := hk
  rw [hc0] at hc
  cases hc
  exact (h1 C rfl rfl).1

/-- **The origin row of a gap copy is at most the row of the root top of every region that
contains it** (the replacement of (MA) in case 1). -/
theorem cut_le_rootTop {M : Mountain} (hV : MountainValid M) {cr d : Nat} {S : Row}
    {p : Emit × Origin} (hct : CleanTopP M cr p) (hcut : ChainCorr.cutOrigin p.2 = true)
    {c0 : Cell} (hc0 : cell? M p.2.src = some c0) (hin : inRegion d S (official c0.row) = true)
    {ρr : Ref} {ρc : Cell} (hρ : topIn M cr d S = some (ρr, ρc)) :
    official c0.row ≤ official ρc.row := by
  have ho : ∃ r, p.2 = .clean r true := by
    generalize p.2 = o at hcut
    cases o with
    | clean r b => cases b <;> simp_all [ChainCorr.cutOrigin]
    | plain r => simp [ChainCorr.cutOrigin] at hcut
    | upper r => simp [ChainCorr.cutOrigin] at hcut
  obtain ⟨r0, hpo⟩ := ho
  have hsrc : p.2.src = r0 := by rw [hpo]; rfl
  obtain ⟨ρr', ρc', hρ', hρrow'⟩ := hct r0 true hpo c0 (by rw [← hsrc]; exact hc0)
  obtain ⟨hmem', _, _⟩ := Recon.RowLaw.topIn_spec hρ'
  obtain ⟨hcol', hidx', hcell'⟩ := Classification.mem_realNodes hmem'
  have := le_top_of_node hV hcol' hidx' hcell' (by rw [hρrow']; exact hin) hρ
  rw [hρrow'] at this
  exact this

end OmegaY.Official.Classification.Proofs.CutGap

#print axioms OmegaY.Official.Classification.Proofs.CutGap.cut_le_rootTop
