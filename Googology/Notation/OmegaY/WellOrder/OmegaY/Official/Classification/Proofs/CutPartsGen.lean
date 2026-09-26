/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/CutPartsGen.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CutPartsStep
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CutPartsPaRow

set_option backward.do.legacy false

/-!
# `CutGenReach` and the remaining gap-copy statements

`CutGenReach` (`CutPartsStep.lean`) says: for a gap copy with origin `o`, leg `l` and
`pa` the highest node of the column `l` at or below the row of `o`, the scale-`k` chain of
`M(s)` from `pa` reaches the raw parent `m'` of `o` when `o → m'` is a scale-`k` step.

This holds for every real node of a canonical mountain (`rawParent_reach_hAM`): the parent
search for the node above `o` starts at `pa` (`ControlProof.Q_of_highestAtMost`) and the node it
finds, `m'`, is reached from `pa` by numerical parents (`Frame.Hit.parentPath`), which are raw
parents. Along this path the rows lie between `row m'` and `row o`, so every step has a jump at
most `jump(row o, row m') ≤ k` (`Row.jump_le_between`).

With `CutPaRow` (`CutPartsPaRow.lean`) and `CutGenReach` proved, `StepCut` needs only
`StepInner`, the three start statements and `CutTopLookup` (`stepCut_of_rest`), and the four
gap-copy statements of `ChainCorrCut.lean` follow from `StepInner`, `CopyOrder`, `CopyFirst`,
`BoundaryChain` and five open statements (`cut_statements_of_rest`,
`wellFounded_of_cut_rest`).
-/

namespace OmegaY.Official.Classification.Proofs.ChainCorr.CutParts

open Canonical Reserve Official Descent Classification Proofs

section Frames

open Geometry

theorem parentPath_height_le {F : Frame} (hF : F.Ordered) {u p : F.Node}
    (h : Frame.ParentPath F u p) : F.height p ≤ F.height u := by
  induction h with
  | refl _ => exact le_rfl
  | cons hp _ ih => exact ih.trans (Frame.P_height_le hF hp)

/-- A numerical parent in a canonical mountain is the raw parent. -/
theorem rawParent_of_P {s : List Nat} {M : Mountain} (hb : Canonical.build s = .ok M)
    {u q : (Frame.ofMountain M).Node} (hP : (Frame.ofMountain M).P u = some q) :
    Reserve.rawParent M (Frame.ref u) = some (Frame.ref q) := by
  have hF := build_normal_of_success hb
  obtain ⟨v, hv⟩ := hF.upper_of_parent hP
  have hvals := Frame.P_value hF.toOrdered hP
  have hReal : Frame.Real u := Frame.real_of_value_pos hF.toOrdered (by omega)
  obtain ⟨p, hp, _, _, hleft⟩ := hF.upper_step u v hReal hv
  have hpq : p = q := Option.some.inj (hp.symm.trans hP)
  subst hpq
  rw [ControlProof.rawParent_ref (M := M) u, hv, Option.bind_some, hleft]

/-- A path of numerical parents whose rows stay in an interval of jump at most `k` is a
scale-`k` chain. -/
theorem path_reach {s : List Nat} {M : Mountain} (hb : Canonical.build s = .ok M) {k : Nat}
    {H : Row} {u p : (Frame.ofMountain M).Node} (h : Frame.ParentPath (Frame.ofMountain M) u p) :
    Row.jump ((Frame.ofMountain M).height p) H ≤ k → (Frame.ofMountain M).height u ≤ H →
      ScaleReach M k (Frame.ref u) (Frame.ref p) := by
  have hO := (build_normal_of_success hb).toOrdered
  induction h with
  | refl u => intro _ _; exact ScaleReach.refl _
  | @cons u q p hP rest ih =>
      intro hpH hu
      have hq := Frame.P_height_le hO hP
      have hpq := parentPath_height_le hO rest
      have hr := ih hpH (le_trans hq hu)
      have h1 := (Row.jump_le_between hpq (le_trans hq hu) hpH).2
      have h2 := (Row.jump_le_between hq hu h1).1
      rw [Row.jump_comm] at h2
      exact ScaleReach.step (rawParent_of_P hb hP) (ControlProof.cell?_ref (M := M) u)
        (ControlProof.cell?_ref (M := M) q) h2 (Frame.P_column_lt hO hP) hr

/-- **In a canonical mountain the scale-`k` chain from the highest node `pa` of the leg column
of `u` at or below the row of `u` reaches the raw parent of `u`, if `u` steps to it at
scale `k`.** -/
theorem rawParent_reach_hAM {s : List Nat} {M : Mountain} (hb : Canonical.build s = .ok M)
    {u q l pa : Ref} {cu cq : Cell} (hcu : cell? M u = some cu) (hu : 0 < u.index)
    (hl : cu.left = some l) (hpa : highestAtMost M l.column cu.row = some pa)
    (hraw : Reserve.rawParent M u = some q) (hcq : cell? M q = some cq) {k : Nat}
    (hk : Row.jump cu.row cq.row ≤ k) : ScaleReach M k pa q := by
  have hF := build_normal_of_success hb
  have hO := hF.toOrdered
  obtain ⟨nu, hnu, hcell⟩ := ControlProof.node_of_cell? hcu
  have h1 := ControlProof.rawParent_ref (M := M) nu
  rw [hnu, hraw] at h1
  cases hup : (Frame.ofMountain M).upper nu with
  | none => rw [hup] at h1; cases h1
  | some v =>
    rw [hup, Option.bind_some] at h1
    obtain ⟨np, hlk, _, _⟩ := hO.stored_valid v q h1.symm
    have hnp : Frame.ref np = q := Frame.lookup_spec hlk
    have hleft' : ((Frame.ofMountain M).cell v).left = some (Frame.ref np) := by
      rw [hnp]
      exact h1.symm
    have hrawF := Frame.rawParent_eq_of_upper_left hup hleft'
    have hReal : Frame.Real nu := by
      show 0 < nu.2.val
      have : u.index = nu.2.val := by rw [← hnu]; rfl
      omega
    have hP : (Frame.ofMountain M).P nu = some np :=
      (hF.rawParent_eq_P hReal).symm.trans hrawF
    obtain ⟨qq, hQ, hit⟩ := (Frame.P_iff hO).mp hP
    have hl' : ((Frame.ofMountain M).cell nu).left = some l := by rw [hcell]; exact hl
    have hpa' : highestAtMost M l.column ((Frame.ofMountain M).height nu) = some pa := by
      simp only [Frame.height, hcell]
      exact hpa
    obtain ⟨q', hQ', hq'⟩ := ControlProof.Q_of_highestAtMost hO hl' hpa'
    have hqq : qq = q' := Option.some.inj (hQ.symm.trans hQ')
    subst hqq
    -- `pa` is a real node
    have hpa0 : 0 < pa.index := (highestAtMost_spec hpa).2.1
    have hqqReal : Frame.Real qq := by
      show 0 < qq.2.val
      have : pa.index = qq.2.val := by rw [← hq']; rfl
      omega
    have hpos := hO.real_positive qq hqqReal
    have hpath := Frame.Hit.parentPath hO hpos hit
    have hcpa := ControlProof.cell?_ref (M := M) qq
    rw [hq'] at hcpa
    have hH : (Frame.ofMountain M).height qq ≤ cu.row :=
      hAM_row_le hpa (by simpa [Frame.height] using hcpa)
    have hcnp := ControlProof.cell?_ref (M := M) np
    rw [hnp, hcq] at hcnp
    have hnpH : Row.jump ((Frame.ofMountain M).height np) cu.row ≤ k := by
      simp only [Frame.height]
      rw [← Option.some.inj hcnp, Row.jump_comm]
      exact hk
    have := path_reach hb hpath hnpH hH
    rw [hq', hnp] at this
    exact this

end Frames

/-- **`CutGenReach` holds.** -/
theorem cutGenReach : CutGenReach := by
  intro s n D M out ρ R t X x i es hS _ j hj _ cu cv ref l pe pa cpe cpa hL k m' _ hst
  obtain ⟨hpar, cm, cm', hcm, hcm', hjk, _⟩ := hst
  have hcmv : cm = cv := Option.some.inj (hcm.symm.trans hL.hcv)
  subst hcmv
  obtain ⟨_, hidx, _⟩ := emitsT_good hS.emits es[j] (List.getElem_mem hj)
  exact rawParent_reach_hAM hS.splice.build hL.hcv (by omega) hL.hl hL.hpa hpar hcm' hjk

/-! ## What is left -/

/-- **`StepCut` from `StepInner`, the three start statements and `CutTopLookup`.** -/
theorem stepCut_of_rest (hStep : StepInner) (hCopy : CutStartCopy) (hRoot : CutStartRoot)
    (hJump : CutJump) (hTop : CutTopLookup) : StepCut :=
  stepCut_of_parts hStep hCopy hRoot hJump cutPaRow cutGenReach hTop

/-- **The four gap-copy statements of `ChainCorrCut.lean`** from `StepInner`, the block profile
(`CopyOrder`, `CopyFirst`), `BoundaryChain` and five open statements. -/
theorem cut_statements_of_rest (hStep : StepInner) (hA : CopyOrder) (hC2 : CopyFirst)
    (hBC : BoundaryChain) (hTop : CutTopLookup) (hLow : CutRunLow) (hHigh : CutRunHigh)
    (hOR : CutOriginReach) (hJT : CutJumpTop) :
    StepCut ∧ CutJump ∧ CutStartCopy ∧ CutStartRoot :=
  cut_statements hStep hA hC2 hBC cutPaRow cutGenReach hTop hLow hHigh hOR hJT

/-- **Well-foundedness of the official expansion** from the reconstruction, the five
statements of `ChainCorrRegions.lean`, the block profile, `BoundaryChain` and the five open
gap-copy statements. -/
theorem wellFounded_of_cut_rest (hrec : Dimension.BlockReconstruction) (hStep : StepInner)
    (hLeg : StartLeg) (hJ : StartJump) (hCopy : StartCopy) (hRoot : StartRoot)
    (hA : CopyOrder) (hC2 : CopyFirst) (hBC : BoundaryChain) (hTop : CutTopLookup)
    (hLow : CutRunLow) (hHigh : CutRunHigh) (hOR : CutOriginReach) (hJT : CutJumpTop) :
    WellFounded Step :=
  wellFounded_of_cut_parts hrec hStep hLeg hJ hCopy hRoot hA hC2 hBC cutPaRow cutGenReach hTop
    hLow hHigh hOR hJT

end OmegaY.Official.Classification.Proofs.ChainCorr.CutParts

#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.CutParts.rawParent_reach_hAM
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.CutParts.cutGenReach
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.CutParts.stepCut_of_rest
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.CutParts.cut_statements_of_rest
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.CutParts.wellFounded_of_cut_rest
