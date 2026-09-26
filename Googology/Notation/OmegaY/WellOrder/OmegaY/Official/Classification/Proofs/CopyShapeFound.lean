/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/CopyShapeFound.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CopyShapeNoMA
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.ParentBelowLowerProfile
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.ChainSplit

set_option backward.do.legacy false

/-!
# The shape of copied columns: the foundation statements

This file closes `Recon.LowerPB.Emitted` (`ParentBelowLowerProfile.lean`) without hypothesis,
and collects the proved statements about the copied columns of a block `i ≥ 1` that the
reconstruction leaves and the chain leaves may use.

## How `Emitted` is proved

`Emitted` is about any context `ctx` of a block `1 ≤ i ≤ n` (`LowerPB.BCtx`), not only the
contexts of the splice data (`ChainCorr.SpliceData`) for which (MD) and (MH) were first proved.
So the two facts are proved again for these contexts:

* (MD) for a block context (`factMD_of_bctx`): the source form `CopyShape.md_source`;
* (MH) for a block context (`factMH_of_bctx`): as `CopyShape.MHProof.mhHolds`. A reached clean
  item with `b = 0` has equal source and target (`reach_clean_eq`), the output boundary column
  `c_r + w·i` has every row `< τ` of the root column (`CutPredMD.boundaryRootRowsHolds`), and a
  block context reads that column of the output (`BCtx.bnd`); the column exists
  (`boundary_lt`, from the size `x₀ + n·w` of the output, `run_size`).

Then the covering part of `NoMA.runItemT_shapeW` (which needs no (MA)) says every node of the
column in the region of a top item of the lower part is the origin of a non-cut emit, and
every node below `τ` lies in the region of one top item (`JumpLaw.lowerItems_cover`).

(MA) is not used; it is false (`CopyShapeMAFalse.lean`).
-/

namespace OmegaY.Official.Classification.Proofs.CopyShape.Found

open Canonical Reserve Official Descent Classification Proofs
open Recon

/-! ## The output of a run -/

theorem topIn_congr {M N : Mountain} {c d : Nat} {S : Row} (h : M[c]? = N[c]?) :
    topIn M c d S = topIn N c d S := by
  unfold topIn realNodes
  rw [h]

/-- The number of columns of a splice run: `x₀ + n·w`. -/
theorem run_size {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}
    (hrun : Official.expandDiagram s n = .ok R) (hTop : Recon.Top s M t root) (hn : n ≠ 0) :
    R.size = (M.size - 1) + n * (M.size - 1 - root.column) := by
  obtain ⟨M', hM', hcases⟩ := Reconstruction.expandDiagram_cases hrun
  have hMM : M' = M := Except.ok.inj (hM'.symm.trans hTop.build)
  subst hMM
  have hlt := hTop.lt
  rcases hcases with ⟨hs, _⟩ | ⟨_, col, t', hcol, ht', hbr⟩
  · subst hs
    have h' : Canonical.build ([] : List Nat) = .ok #[] := rfl
    rw [h'] at hM'
    have hM0 : M' = #[] := (Except.ok.inj hM').symm
    subst hM0
    simp at hlt
  · have htt : t' = t := by
      have h := hTop.top
      rw [hcol] at h
      simp only [Option.bind_some] at h
      exact Option.some.inj (ht'.symm.trans h)
    subst htt
    rcases hbr with ⟨hτ, _⟩ | ⟨_, _, root', hroot', hcr, hsize, _⟩
    · rcases hτ with h0 | h0
      · exact absurd h0 hTop.real
      · exact absurd h0 hn
    · have hrr : root' = root := Option.some.inj (hroot'.symm.trans hTop.left)
      subst hrr
      rw [hsize, Reconstruction.sum_blocks hcr hn]

/-- The boundary column `c_r + w·i` of a block `1 ≤ i ≤ n` is a column of the output. -/
theorem boundary_lt {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}
    (hrun : Official.expandDiagram s n = .ok R) (hTop : Recon.Top s M t root) {i : Nat}
    (hi1 : 1 ≤ i) (hin : i ≤ n) :
    root.column + (M.size - 1 - root.column) * i < R.size := by
  rw [run_size hrun hTop (by omega)]
  have hlt := hTop.lt
  have hwi : (M.size - 1 - root.column) * i ≤ n * (M.size - 1 - root.column) := by
    rw [Nat.mul_comm n]
    exact Nat.mul_le_mul_left _ hin
  omega

theorem top_col {s : List Nat} {M : Mountain} {t : Cell} {root : Ref}
    (hTop : Recon.Top s M t root) : ∃ col, M[M.size - 1]? = some col ∧ col.back? = some t := by
  have h := hTop.top
  cases hcol : M[M.size - 1]? with
  | none => rw [hcol] at h; cases h
  | some col => rw [hcol] at h; exact ⟨col, rfl, h⟩

/-! ## (MD) and (MH) for the contexts of a block -/

/-- **(MD) for every context of a block.** -/
theorem factMD_of_bctx {s : List Nat} {R M : Mountain} {t : Cell} {root : Ref}
    (hTop : Recon.Top s M t root) {i : Nat} {ctx : Context}
    (hB : LowerPB.BCtx M R root.column (M.size - 1) i ctx) : FactMD ctx (official t.row) := by
  intro d it hRe ρr ρc hρ _
  have hbel := (reach_below hRe).1
  obtain ⟨col, hcol, htc⟩ := top_col hTop
  rw [hB.source, hB.root] at hρ
  have := md_source s M hTop.build col t hcol htc root hTop.left hTop.real d it.source hbel ρr ρc
    hρ
  rw [hB.source, hB.last]
  exact this

/-- **(MH) for every context of a block `1 ≤ i ≤ n`**, in the strong form `h_ρ ≤ h_q`. -/
theorem factMH_of_bctx {s : List Nat} {n : Nat} {R : Mountain}
    (hrun : Official.expandDiagram s n = .ok R) {M : Mountain} {t : Cell} {root : Ref}
    (hTop : Recon.Top s M t root) {i : Nat} (hi1 : 1 ≤ i) (hin : i ≤ n) {ctx : Context}
    (hB : LowerPB.BCtx M R root.column (M.size - 1) i ctx) : FactMH ctx (official t.row) := by
  intro d it C hRe hC hcb csRef cs g _ _
  have hblk : 1 ≤ ctx.block := by rw [hB.block]; exact hi1
  have hV : MountainValid ctx.source := by
    rw [hB.source]; exact build_valid_of_success hTop.build
  obtain ⟨_, _, _, _, hBasic⟩ := Recon.run_basic hrun
  have hVR : MountainValid R := hBasic.valid
  have hst := MHProof.reach_clean_eq hV hblk hRe hC hcb
  have hbel := (reach_below hRe).1
  have hbd : ctx.boundary = root.column + (M.size - 1 - root.column) * i := by
    unfold Context.boundary
    rw [hB.root, hB.width, hB.block]
  show heightOf (d + 2) (topIn ctx.source ctx.rootColumn (d + 2) it.source) ≤
    heightOf (d + 2) (topIn ctx.result ctx.boundary (d + 2) it.target) + g
  rw [hbd, topIn_congr hB.bnd, hB.source, hB.root]
  cases hρ : topIn M root.column (d + 2) it.source with
  | none => exact Nat.zero_le _
  | some p =>
      obtain ⟨ρr, ρc⟩ := p
      obtain ⟨hρmem, hρreg, _⟩ := Recon.RowLaw.topIn_spec hρ
      have hlt : official ρc.row < official t.row := hbel _ hρreg
      obtain ⟨col, hcol, htc⟩ := top_col hTop
      have hBR := Recon.CutPredMD.boundaryRootRowsHolds s n R hrun M col t root hTop.build hcol
        htc hTop.left hTop.lt i hi1
      obtain ⟨q0, hq0, hq0row⟩ := hBR (boundary_lt hrun hTop hi1 hin) (ρr, ρc) hρmem hlt
      have hq0reg : inRegion (d + 2) it.target (official q0.2.row) = true := by
        rw [← hst, hq0row]; exact hρreg
      cases hq : topIn R (root.column + (M.size - 1 - root.column) * i) (d + 2) it.target with
      | none =>
          have := Recon.RowLaw.topIn_none hq q0 hq0
          rw [hq0reg] at this
          cases this
      | some qq =>
          obtain ⟨hqmem, hqreg, hqmax⟩ := Recon.RowLaw.topIn_spec hq
          have hidx := hqmax q0 hq0 hq0reg
          have hle : q0.2.row ≤ qq.2.row := MHProof.row_le_of_index hVR hq0 hqmem hidx
          obtain ⟨_, hq01, hq0cell⟩ := Classification.mem_realNodes hq0
          have h1 : (1 : Row) ≤ q0.2.row := Classification.one_le_row hVR hq0cell hq01
          have hco := Recon.RowLaw.coeff_le_of_inRegion hq0reg hqreg (Recon.official_mono h1 hle)
          rw [hq0row] at hco
          obtain ⟨qr, qc⟩ := qq
          show (official ρc.row).coeff d ≤ (official qc.row).coeff d + g
          have : (official ρc.row).coeff d ≤ (official qc.row).coeff d := hco
          omega

/-- **MH for the contexts of a block** (the statement `LowerPB.RuleFix.MHB` of
`ParentBelowLowerFixCover.lean`, written out). -/
theorem mhBlock : ∀ s n R, Official.expandDiagram s n = .ok R → ∀ M t root, Recon.Top s M t root →
    ∀ i, 1 ≤ i → i ≤ n → ∀ ctx, LowerPB.BCtx M R root.column (M.size - 1) i ctx →
      root.column < ctx.x → FactMH ctx (official t.row) :=
  fun _ _ _ hrun _ _ _ hTop _ hi1 hin _ hB _ => factMH_of_bctx hrun hTop hi1 hin hB

/-! ## `Emitted` -/

/-- **The lower part of a block context covers the column.** In a context of a block
`1 ≤ i ≤ n`, every node of the column `ctx.x` below `τ` is the origin of a non-cut emit of the
lower part. (No condition on `ctx.x` beyond `BCtx`.) -/
theorem lowerT_covers {s : List Nat} {n : Nat} {R : Mountain}
    (hrun : Official.expandDiagram s n = .ok R) {M : Mountain} {t : Cell} {root : Ref}
    (hTop : Recon.Top s M t root) {i : Nat} (hi1 : 1 ≤ i) (hin : i ≤ n) {ctx : Context}
    (hB : LowerPB.BCtx M R root.column (M.size - 1) i ctx) {es : List (Emit × Origin)}
    (hes : lowerT ctx (official t.row) = .ok es) {k : Nat} {c : Cell} (hk : 1 ≤ k)
    (hc : cell? M ⟨ctx.x, k⟩ = some c) (hτ : official c.row < official t.row) :
    ∃ e ∈ es, ChainCorr.cutOrigin e.2 = false ∧ e.2.src = ⟨ctx.x, k⟩ := by
  have hblk : 1 ≤ ctx.block := by rw [hB.block]; exact hi1
  have hV : MountainValid ctx.source := by
    rw [hB.source]; exact build_valid_of_success hTop.build
  have hMD := factMD_of_bctx hTop hB
  have hMH := factMH_of_bctx hrun hTop hi1 hin hB
  obtain ⟨P, hP, hPin⟩ := Recon.JumpLaw.lowerItems_cover (official t.row) hτ
  unfold lowerT at hes
  simp only [bind, Except.bind, pure, Except.pure] at hes
  split at hes
  · cases hes
  · rename_i outs houts
    cases hes
    obtain ⟨out, hout, hPo⟩ := exists_of_mapM houts P hP
    obtain ⟨kk, j, _, _, rfl⟩ := Recon.RowLaw.mem_lowerItems hP
    have hsh := NoMA.runItemT_shapeW ctx (official t.row) ctx.result ctx.boundary hV hblk
      (fun _ _ => rfl) hMD hMH kk _ out hPo (Reach.top hP) (fun C hC => by cases hC)
    have hcr : CovRow (Env.ofCtx ctx ctx.result ctx.boundary) (kk + 1)
        ⟨slot (kk + 2) (official t.row) j, slot (kk + 2) (official t.row) j, none, 0, false⟩
        (official c.row) := by
      refine ⟨hPin, ?_, ?_⟩
      · intro C hC; cases hC
      · intro _ hb; cases hb
    obtain ⟨q, hq, hqs, hqc⟩ := hsh.2.2 ⟨ctx.x, k⟩ c rfl hk
      (by rw [Env.ofCtx_M, hB.source]; exact hc) hcr
    exact ⟨q, List.mem_flatten.mpr ⟨out, hout, hq⟩, hqc, hqs⟩

theorem cutO_eq (o : Origin) : LowerPB.cutO o = ChainCorr.cutOrigin o := by
  cases o with
  | clean src b => cases b <;> rfl
  | _ => rfl

/-- **`LowerPB.Emitted` holds** (no hypothesis). -/
theorem emitted : Recon.LowerPB.Emitted := by
  intro s n R hrun M t root hTop i hi1 hin ctx hB _ es hes k c hk hc hτ
  obtain ⟨e, he, hcut, hsrc⟩ := lowerT_covers hrun hTop hi1 hin hB hes hk hc hτ
  exact ⟨e, he, by rw [cutO_eq]; exact hcut, hsrc⟩

end OmegaY.Official.Classification.Proofs.CopyShape.Found

#print axioms OmegaY.Official.Classification.Proofs.CopyShape.Found.factMD_of_bctx
#print axioms OmegaY.Official.Classification.Proofs.CopyShape.Found.factMH_of_bctx
#print axioms OmegaY.Official.Classification.Proofs.CopyShape.Found.mhBlock
#print axioms OmegaY.Official.Classification.Proofs.CopyShape.Found.lowerT_covers
#print axioms OmegaY.Official.Classification.Proofs.CopyShape.Found.emitted
