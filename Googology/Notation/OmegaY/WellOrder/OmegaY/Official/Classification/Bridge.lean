/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Bridge.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Control
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Reconstruction
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Dimension

set_option backward.do.legacy false

/-!
# Connection to `Reconstruction.lean` and `Dimension.lean`

`Reconstruction.wellFounded_of_parts` needs `Reconstruction.DegreeAndAtomsHold`: the
degree check (item 2, `Dimension.output_degree` from `Dimension.BlockReconstruction`)
and the atom classification `Reconstruction.atomsClassified` (item 4). This file
proves `atomsClassified` from the open statements of this directory
(`atomsClassified_of_open`) and assembles the well-foundedness from
`Dimension.BlockReconstruction`, `ControlDominates` and `KeyLeRest`
(`wellFounded_of_block`).
-/

namespace OmegaY.Official.Classification

open Canonical Reserve Official Descent

theorem spliceCase_not_delete {s out : List Nat} {n D : Nat} {M : Mountain} {ρ : Root}
    (hc : SpliceCase s n D M out ρ) : ¬ (s = [] ∨ n = 0 ∨ s.getLast? = some 1) := by
  have hV := build_valid_of_success hc.build
  have hsz := build_size hc.build
  have hx := (root?_spec hV hc.root).1
  rintro (h | h | h)
  · subst h; simp only [List.length_nil] at hsz; omega
  · exact hc.copies h
  · have hs : s = s.dropLast ++ [1] := by
      rw [← List.dropLast_append_getLast? 1 h]
      simp [List.dropLast_append_getLast? 1 h]
    have hb := hc.build
    rw [hs] at hb
    obtain ⟨col, hcol, htop⟩ := Dimension.last_column_one hb
    have hb' : Canonical.build s = .ok M := hc.build
    have hcolM : M[M.size - 1]? = some col := by
      have := build_size hb
      exact hcol
    obtain ⟨hcs, hcolEq⟩ := column_of_getElem? hcolM
    have hCV := hV (M.size - 1) hcs
    rw [hcolEq] at hCV
    have h2 := hCV.size_ge_two
    have ht : col.back? = some col[col.size - 1] := by
      simp [Array.back?, Array.getElem?_eq_getElem (show col.size - 1 < col.size by omega)]
    have hrow := htop _ ht
    have h0 : official col[col.size - 1].row = 0 := by rw [hrow]; exact official_one
    have hr := hc.root
    rw [root?_none_of_official_zero hV D hcolM ht h0] at hr
    cases hr

theorem reconstructs_of_block (h : Dimension.BlockReconstruction) : Reconstructs := by
  intro s n D M out ρ R hc hR
  obtain ⟨R', hR', hv⟩ := expand_spec hc.run
  have hRR : R' = R := Except.ok.inj (hR'.symm.trans hR)
  subst hRR
  exact h s n R' out (spliceCase_not_delete hc) hR' hv

theorem reconstructs_of_holds (h : Reconstruction.ReconstructionHolds) : Reconstructs := by
  intro s n D M out ρ R hc hR
  obtain ⟨R', hR', hv⟩ := expand_spec hc.run
  have hRR : R' = R := Except.ok.inj (hR'.symm.trans hR)
  subst hRR
  exact h s n R' out hR' hv

/-- **Item 4 (`Reconstruction.atomsClassified`) from the open statements.** -/
theorem atomsClassified_of_open (h1 : Reconstructs) (h4 : ControlDominates) (h5 : KeyLeRest)
    {s out : List Nat} {n D : Nat} {M MO : Mountain} (hs : s ≠ []) (hdeg : DegreeOK s D)
    (hM : Canonical.build s = .ok M) (hrun : Official.expand s n = .ok out)
    (hMO : Canonical.build out = .ok MO) : Reconstruction.atomsClassified M MO n D = true := by
  obtain ⟨R, hR, hv⟩ := expand_spec hrun
  obtain ⟨M', hM', hcases⟩ := expandDiagram_spec hR
  rw [hM] at hM'
  cases hM'
  have hV := build_valid_of_success hM
  -- the deletion branch
  have hdel : R = M.pop → ∀ e ∈ atoms MO D, baseOK D (atoms M D) e = true := by
    intro hRp
    subst hRp
    obtain ⟨MO', hMO', _, _, hbase⟩ := deletion_facts hs hM hv hdeg
    have : MO' = MO := Except.ok.inj (hMO'.symm.trans hMO)
    subst this
    exact hbase
  unfold Reconstruction.atomsClassified
  cases hr : root? M D with
  | none =>
      simp only
      rcases hcases with ⟨he, _⟩ | ⟨col, t, hcol, ht, hbr⟩
      · exact absurd (List.isEmpty_iff.mp he) hs
      · rcases hbr with ⟨_, hRp⟩ | ⟨hsp, root, htl, _, _, _⟩
        · exact List.all_eq_true.mpr (hdel hRp)
        · obtain ⟨ρ, hρ, _, _⟩ :=
            root?_of_official_ne_zero hV D hcol ht (fun h0 => hsp (Or.inl h0)) htl
          rw [hρ] at hr
          cases hr
  | some ρ =>
      simp only
      by_cases hn : n = 0
      · rw [if_pos hn]
        rcases hcases with ⟨he, _⟩ | ⟨col, t, hcol, ht, hbr⟩
        · exact absurd (List.isEmpty_iff.mp he) hs
        · rcases hbr with ⟨_, hRp⟩ | ⟨hsp, _⟩
          · exact List.all_eq_true.mpr (hdel hRp)
          · exact absurd (Or.inr hn) hsp
      · rw [if_neg hn]
        have hc : SpliceCase s n D M out ρ := ⟨hM, hrun, hr, hn⟩
        have hsplice := spliceAtomsClassified_of_witness h1
          (witnessHolds_of_keys (keyWitnessHolds_of_rest (keyWitnessRest_of h4 h5)))
        apply List.all_eq_true.mpr
        intro e he
        split
        · rename_i hlt
          exact splice_base hc hMO e he hlt
        · exact hsplice s n D M out ρ MO hc hdeg hMO e he (by omega)

theorem degreeAndAtomsHold_of_open (hrec : Dimension.BlockReconstruction)
    (h4 : ControlDominates) (h5 : KeyLeRest) : Reconstruction.DegreeAndAtomsHold := by
  intro s n D M MO out hs hdeg hM hrun hMO
  exact ⟨Dimension.output_degree hrec hM (hdeg M hM) hrun hMO,
    atomsClassified_of_open (reconstructs_of_block hrec) h4 h5 hs hdeg hM hrun hMO⟩

/-- **Well-foundedness of the official expansion from the three open statements**:
canonical reconstruction for block-adding expansions, control dominance (input
mountain only) and the key bounds of the canonical witness. -/
theorem wellFounded_of_block (hrec : Dimension.BlockReconstruction) (h4 : ControlDominates)
    (h5 : KeyLeRest) : WellFounded Step :=
  Reconstruction.wellFounded_of_parts (degreeAndAtomsHold_of_open hrec h4 h5)

end OmegaY.Official.Classification

#print axioms OmegaY.Official.Classification.atomsClassified_of_open
#print axioms OmegaY.Official.Classification.wellFounded_of_block
