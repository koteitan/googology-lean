/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/CutGapFG.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CopyShapeMH
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CutGapFirst

set_option backward.do.legacy false

/-!
# `FactFG` holds (`CutGap`)

`FGHolds` (`CutGapFirst.lean`): a reached level-2 clean item with `b = 0` in a copied column of
a block `i ≥ 1` makes the child `h_ρ + 1`: `h_ρ + 1 ≤ h_q + g`.

* `mhStrong`: `h_ρ ≤ h_q` for every reached clean item with `b = 0`. This is the argument of
  `CopyShape.MHProof.mhHolds` (`CopyShapeMH.lean`), which proves this strong form inside its
  proof but states only `h_ρ ≤ h_q + g`; it is repeated here with the strong conclusion.
* `generations_pos`: `g ≥ 1`, since the column `y > c_r` is itself counted.
-/

set_option linter.unusedSimpArgs false

namespace OmegaY.Official.Classification.Proofs.CutGap

open Canonical Reserve Official Descent Classification Proofs CopyShape CopyShape.MHProof

/-- (MH) in its strong form `h_ρ ≤ h_q`. -/
theorem mhStrong : ∀ s n D M out ρ R t, ChainCorr.SpliceData s n D M out ρ R t →
    ∀ i, 0 < i → i < n + 1 → ∀ y, y ∈ blockColumns ρ.cr ρ.x0 n i →
    ∀ d it C, Reach (ctxAt M R y i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 (y + (ρ.x0 - ρ.cr) * i)) (official t.row)
      (d + 2) it → it.clean = some C → it.cutBottom = false →
      heightOf (d + 2) (topIn M ρ.cr (d + 2) it.source) ≤
        heightOf (d + 2) (topIn (ctxAt M R y i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 (y + (ρ.x0 - ρ.cr) * i)).result
          (ctxAt M R y i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 (y + (ρ.x0 - ρ.cr) * i)).boundary (d + 2) it.target) := by
  intro s n D M out ρ R t hS i hi0 hi y hy d it C hRe hC hcb
  have hV := build_valid_of_success hS.splice.build
  have hVR := build_valid_of_success hS.canon
  obtain ⟨hcy, _⟩ := ChainCorr.mem_blockColumns_pos hy hi0
  have hst := reach_clean_eq (ctx := ctxAt M R y i ρ.cr (ρ.x0 - ρ.cr) ρ.x0
    (y + (ρ.x0 - ρ.cr) * i)) hV hi0 hRe hC hcb
  have hbel := (reach_below hRe).1
  -- the context, read off
  show heightOf (d + 2) (topIn M ρ.cr (d + 2) it.source) ≤
    heightOf (d + 2) (topIn (R.extract 0 (y + (ρ.x0 - ρ.cr) * i))
      (ρ.cr + (ρ.x0 - ρ.cr) * i) (d + 2) it.target)
  rw [topIn_extract' (by omega)]
  cases hρ : topIn M ρ.cr (d + 2) it.source with
  | none => exact Nat.zero_le _
  | some p =>
      obtain ⟨ρr, ρc⟩ := p
      obtain ⟨hρmem, hρreg, _⟩ := Recon.RowLaw.topIn_spec hρ
      have hlt : official ρc.row < official t.row := hbel _ hρreg
      obtain ⟨col, root, hcol, ht, htl, _, hcr, hx0⟩ := splice_root hS
      have hcx : root.column < M.size - 1 := by
        rw [← hcr, ← hx0]
        exact lt_of_lt_of_le hcy ‹y ≤ ρ.x0›
      have hRs : R.size = ρ.x0 + n * (ρ.x0 - ρ.cr) := by
        rw [build_size hS.canon]
        exact Reconstruction.expand_length_splice hS.splice.build hS.splice.run
          hS.splice.root hS.splice.copies
      have hBR := Recon.CutPredMD.boundaryRootRowsHolds s n R hS.run M col t root
        hS.splice.build hcol ht htl hcx i hi0
      have hBlt : root.column + (M.size - 1 - root.column) * i < R.size := by
        rw [← hcr, ← hx0, hRs]
        have hwi : (ρ.x0 - ρ.cr) * i ≤ n * (ρ.x0 - ρ.cr) := by
          rw [Nat.mul_comm n]; exact Nat.mul_le_mul_left _ (by omega)
        omega
      have hρmem' : (ρr, ρc) ∈ realNodes M root.column := by rw [← hcr]; exact hρmem
      obtain ⟨q0, hq0, hq0row⟩ := hBR hBlt (ρr, ρc) hρmem' hlt
      rw [← hcr, ← hx0] at hq0
      -- `q0` is a node of the boundary column in `T = S`
      have hq0reg : inRegion (d + 2) it.target (official q0.2.row) = true := by
        rw [← hst, hq0row]; exact hρreg
      cases hq : topIn R (ρ.cr + (ρ.x0 - ρ.cr) * i) (d + 2) it.target with
      | none =>
          have := Recon.RowLaw.topIn_none hq q0 hq0
          rw [hq0reg] at this
          cases this
      | some qq =>
          obtain ⟨hqmem, hqreg, hqmax⟩ := Recon.RowLaw.topIn_spec hq
          have hidx := hqmax q0 hq0 hq0reg
          have hle : q0.2.row ≤ qq.2.row := row_le_of_index hVR hq0 hqmem hidx
          obtain ⟨_, hq01, hq0cell⟩ := Classification.mem_realNodes hq0
          have h1 : (1 : Row) ≤ q0.2.row := one_le_row hVR hq0cell hq01
          have hco := Recon.RowLaw.coeff_le_of_inRegion hq0reg hqreg (Recon.official_mono h1 hle)
          rw [hq0row] at hco
          obtain ⟨qr, qc⟩ := qq
          show (official ρc.row).coeff d ≤ (official qc.row).coeff d
          exact hco


theorem generations_ge {M : Mountain} {cr : Nat} {C : Row} :
    ∀ (fuel : Nat) (ref : Ref) (cell : Cell) (g0 g : Nat),
      generations M cr C fuel ref cell g0 = .ok g → g0 ≤ g
  | 0, _, _, _, _, h => by simp [generations, throw, throwThe, MonadExceptOf.throw] at h
  | fuel + 1, ref, cell, g0, g, h => by
      unfold generations at h
      split at h
      · simp only [pure, Except.pure, Except.ok.injEq] at h
        omega
      · simp only [bind, Except.bind] at h
        split at h
        · cases h
        · rename_i p _
          split at h
          · cases h
          · split at h
            · cases h
            · rename_i r c _
              have := generations_ge fuel r c (g0 + 1) g h
              omega

theorem generations_pos {M : Mountain} {cr : Nat} {C : Row} {fuel : Nat} {ref : Ref} {cell : Cell}
    {g : Nat} (hc : cr < ref.column) (h : generations M cr C (fuel + 1) ref cell 0 = .ok g) :
    1 ≤ g := by
  unfold generations at h
  split at h
  · omega
  · simp only [bind, Except.bind] at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · rename_i r c _
          exact generations_ge fuel r c 1 g h

/-- **`FactFG` holds.** -/
theorem fgHolds : FGHolds := by
  intro s n D M out ρ R t hS i hi0 hi y hy it C hRe hC hcb csRef cs g hnd hgen
  have h1 := mhStrong s n D M out ρ R t hS i hi0 hi y hy 0 it C hRe hC hcb
  obtain ⟨hcy, _⟩ := ChainCorr.mem_blockColumns_pos hy hi0
  obtain ⟨hcol, _, _, _⟩ := Classification.nodeAt_spec hnd
  change csRef.column = y at hcol
  have hlt : ρ.cr < csRef.column := by omega
  have h2 := generations_pos hlt hgen
  exact Nat.add_le_add h1 h2

end OmegaY.Official.Classification.Proofs.CutGap

#print axioms OmegaY.Official.Classification.Proofs.CutGap.mhStrong
#print axioms OmegaY.Official.Classification.Proofs.CutGap.fgHolds
