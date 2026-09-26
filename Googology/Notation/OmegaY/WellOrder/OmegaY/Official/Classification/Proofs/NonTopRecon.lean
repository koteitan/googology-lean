/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/NonTopRecon.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.NonTopMain

set_option backward.do.legacy false

/-!
# `NonTopStep` from the canonical reconstruction (`NonTopRecon.lean`)

`LowerChain.NonTopStep` assumes only a successful run `expandDiagram s n = .ok R` and
`Recon.Top s M t root`; it does not assume that `R` is the canonical mountain of the output
values. `NonTopMain.nonTopStepS` proves the same statement over `Setting`, which includes that
fact. Here the setting is built from a run and `Recon.Top` (the output values exist, a degree
bound, the root of the splice), with the canonical output taken from
`Dimension.BlockReconstruction`:

* **`nonTopStep_of_reconstruction : Dimension.BlockReconstruction → NonTopStep`**.

So `NonTopStep` holds as soon as the reconstruction does; the well-foundedness theorem
`LowerChain.wellFounded_of_lower_main` then needs neither `NonTopStep`, `StartRelNT` nor
`StartRootNT` (`wellFounded_of_lower_rec`).

All declarations are in the namespace `ChainCorr.NonTop`.
-/

namespace OmegaY.Official.Classification.Proofs.ChainCorr.NonTop

open Canonical Reserve Official Descent Classification Proofs
open ChainCorr.Inner ChainCorr.LowerChain

/-! ## The output values of a run exist -/

theorem finish_size {m : Mountain} {cells : List Cell} {col : Column}
    (h : Expansion.finish m (phantom :: cells) = .ok col) : 1 < col.size := by
  cases cells with
  | nil =>
      exfalso
      unfold Expansion.finish at h
      simp only [List.mergeSort_singleton] at h
      unfold Expansion.finishSorted at h
      simp [phantom, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
      revert h
      unfold Expansion.validateColumnRows
      simp [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
  | cons c cs =>
      obtain ⟨hshape, _⟩ := Expansion.finish_success_spec h
      have hlen := congrArg List.length hshape.1
      simp only [List.length_map, List.length_mergeSort, List.length_cons, Array.length_toList]
        at hlen
      omega

theorem mapM_bottom_ok (cols : List Column) (h : ∀ col ∈ cols, 1 < col.size) :
    ∃ out, cols.mapM (fun column => match column[1]? with
      | some bottom => (Except.ok bottom.value : Expansion.Result Nat)
      | none => .error .missingNode) = .ok out := by
  induction cols with
  | nil => exact ⟨[], rfl⟩
  | cons col cols ih =>
      obtain ⟨out, hout⟩ := ih (fun c hc => h c (List.mem_cons_of_mem _ hc))
      have h1 := h col List.mem_cons_self
      refine ⟨col[1].value :: out, ?_⟩
      rw [List.mapM_cons, hout]
      simp [Array.getElem?_eq_getElem h1]

/-- **The output values of a run exist.** -/
theorem valuesOf_of_run {s : List Nat} {n : Nat} {M R : Mountain}
    (hb : Canonical.build s = .ok M) (hrun : Official.expandDiagram s n = .ok R) :
    ∃ out, Expansion.valuesOf R = .ok out := by
  have hV := build_valid_of_success hb
  have hI : Recon.Inv M (M.size - 1) R := Recon.expandDiagram_inv hb n R hrun
  obtain ⟨_, hpre, hnew⟩ := hI
  have hcol : ∀ c (hc : c < R.size), 1 < R[c].size := by
    intro c hc
    by_cases hx : c < M.size - 1
    · have h1 := hpre c hx
      have hcM : c < M.size := by omega
      rw [Array.getElem?_eq_getElem hc, Array.getElem?_eq_getElem hcM] at h1
      have e := Option.some.inj h1
      rw [e]
      have := (hV c hcM).size_ge_two
      omega
    · obtain ⟨_, cells, hfin, _⟩ := hnew c hc (by omega)
      exact finish_size hfin
  unfold Expansion.valuesOf
  apply mapM_bottom_ok
  intro col hmem
  obtain ⟨c, hc, rfl⟩ := Array.getElem_of_mem (Array.mem_toList_iff.mp hmem)
  exact hcol c hc

/-! ## A degree bound -/

theorem le_sum_of_mem' {l : List Nat} {a : Nat} (h : a ∈ l) : a ≤ l.sum := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
      simp only [List.sum_cons]
      rcases List.mem_cons.mp h with rfl | h'
      · omega
      · have := ih h'; omega

theorem exists_degreeAtMost (M : Mountain) : ∃ D, degreeAtMost M D = true := by
  refine ⟨((M.toList.flatMap fun col => col.toList).map fun c => len c.row).sum, ?_⟩
  unfold degreeAtMost
  simp only [List.all_eq_true, decide_eq_true_eq]
  intro col hcol c hc
  have hmem : len c.row ∈ (M.toList.flatMap fun col => col.toList).map fun c => len c.row :=
    List.mem_map.mpr ⟨c, List.mem_flatMap.mpr ⟨col, hcol, hc⟩, rfl⟩
  have := le_sum_of_mem' hmem
  omega

/-! ## The setting of a run -/

/-- **The setting of `NonTopMain` from a run, `Recon.Top` and the reconstruction.** -/
theorem setting_of_run (hrec : Dimension.BlockReconstruction) {s : List Nat} {n : Nat}
    {R M : Mountain} {t : Cell} {root : Ref} (hrun : Official.expandDiagram s n = .ok R)
    (hTop : Recon.Top s M t root) (hn : n ≠ 0) :
    ∃ D out ρ col, Setting s n D M out ρ R col t ∧ ρ.cr = root.column ∧ ρ.x0 = M.size - 1 := by
  have hb := hTop.build
  have hV := build_valid_of_success hb
  obtain ⟨out, hvals⟩ := valuesOf_of_run hb hrun
  obtain ⟨D, hD⟩ := exists_degreeAtMost M
  obtain ⟨col, hcol, ht⟩ : ∃ col, M[M.size - 1]? = some col ∧ col.back? = some t := by
    have h := hTop.top
    cases hc : M[M.size - 1]? with
    | none => rw [hc] at h; cases h
    | some col => rw [hc] at h; exact ⟨col, rfl, h⟩
  obtain ⟨ρ, hρ, hx0, hcr⟩ := root?_of_official_ne_zero hV D hcol ht hTop.real hTop.left
  obtain ⟨middle, last, hs, hlast, _⟩ := hTop.preparation
  have hns : ¬ (s = [] ∨ n = 0 ∨ s.getLast? = some 1) := by
    rintro (h | h | h)
    · rw [hs] at h; simp at h
    · exact hn h
    · rw [hs, List.getLast?_append] at h
      simp only [List.getLast?_singleton, Option.some_or, Option.some.injEq] at h
      omega
  have hcanon := hrec s n R out hns hrun hvals
  have hexp : Official.expand s n = .ok out := by
    unfold Official.expand
    rw [hrun]
    simp [bind, Except.bind, liftE, Except.mapError, hvals]
  have hdeg : DegreeOK s D := by
    intro M' hM'
    rw [hb] at hM'
    cases hM'
    exact hD
  exact ⟨D, out, ρ, col, ⟨⟨hb, hexp, hρ, hn⟩, hdeg, hrun, hcanon, hcol, ht⟩, hcr, hx0⟩

/-- **`NonTopStep` from the canonical reconstruction.** -/
theorem nonTopStep_of_reconstruction (hrec : Dimension.BlockReconstruction) : NonTopStep := by
  intro s n R M t root i hrun hTop hi0 hi v m hc hnt k m' hst
  obtain ⟨D, out, ρ, col, hS, hcr, hx0⟩ := setting_of_run hrec hrun hTop (by omega)
  rw [← hcr, ← hx0] at hc hnt ⊢
  exact nonTopStepS s n D M out ρ R col t hS i hi0 (by omega) v m hc hnt k m' hst

/-- **Well-foundedness of the official expansion** from the reconstruction, `TopStep`,
`TopStart` and the gap-copy statements, through `LowerChain.wellFounded_of_lower_main`. -/
theorem wellFounded_of_lower_rec (hrec : Dimension.BlockReconstruction) (hTS : TopStep)
    (hTSt : TopStart) (hCut : StepCut) (hCJump : CutJump) (hCCopy : CutStartCopyNT)
    (hCRoot : CutStartRootNT) : WellFounded Step :=
  wellFounded_of_lower_main hrec hTS hTSt (nonTopStep_of_reconstruction hrec) startRelNT
    startRootNT hCut hCJump hCCopy hCRoot

end OmegaY.Official.Classification.Proofs.ChainCorr.NonTop

#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.NonTop.valuesOf_of_run
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.NonTop.nonTopStep_of_reconstruction
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.NonTop.wellFounded_of_lower_rec
