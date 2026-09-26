/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/TopChainBase.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.LowerChainRecon
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.JumpLawSeam
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.ParentBelowLowerCols
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.JumpLawLowerLeftDone

set_option backward.do.legacy false

set_option autoImplicit false

/-!
# The top chain: the jump law at an upper node (proved)

`upperJump`: in a new column of the output `R` of a splice run, for two consecutive cells
`lower`, `upper` with `upper.row = bump lower.row e`, `upper.row ≥ row t` (the node `upper` is
in the upper part), and the cell `parent` at the stored left end of `upper`:
`jump lower.row parent.row = e`. This is the part of `RowLaw.JumpLawHolds` that is already
proved (`colJump_block0`, `colJump_upper` with the proved `seamTauHolds`); the proof follows
`jumpLawHolds_of_col`.
-/

namespace OmegaY.Official.Recon.JumpLaw.TopChainU

open Canonical Expansion Dimension RowLaw

theorem tau_gt_one' {s : List Nat} {M : Mountain} {t : Cell} {root : Ref}
    (hTop : Top s M t root) : (1 : Row) < t.row := CrossUpperSim.tau_gt_one hTop

/-- `ColJump` for the pairs whose upper node is at a row `≥ θ`. -/
def ColJumpU (θ : Row) (ctx : Context) (R : Mountain) (emits : List Emit) : Prop :=
  ∀ k (hk : k + 1 < emits.length) (l e : Nat) (p : Row),
    θ ≤ stored emits[k + 1].row →
    emits[k + 1].leftColumn = some l →
    emits[k + 1].row = Row.bump emits[k].row e →
    HighestBelow (rowsOf R (legCol ctx l)) emits[k + 1].row p →
    Row.jump emits[k].row p = e

/-- **The jump law at a node of the upper part of a new column.** -/
theorem upperJump {s : List Nat} {n : Nat} {R : Mountain}
    (hrun : Official.expandDiagram s n = .ok R) {M0 : Mountain} {t0 : Cell} {root0 : Ref}
    (hTop0 : Top s M0 t0 root0) {c : Nat} (hc : c < R.size) (hx : s.length - 1 ≤ c)
    {index : Nat} {lower upper parent : Cell} {ref : Ref} {e : Nat}
    (hl : R[c][index]? = some lower) (hu : R[c][index + 1]? = some upper) (hi : 0 < index)
    (hleft : upper.left = some ref) (hcell : cellAt R ref = .ok parent)
    (hbump : upper.row = Row.bump lower.row e) (hup : t0.row ≤ upper.row) :
    Row.jump lower.row parent.row = e := by
  obtain ⟨M, hM, hcases⟩ := Reconstruction.expandDiagram_cases hrun
  have hMs := Canonical.build_size hM
  rcases hcases with ⟨rfl, rfl⟩ | ⟨_, col, t, hcol, ht, hcases⟩
  · simp only [List.length_nil] at hMs
    omega
  rcases hcases with ⟨_, rfl⟩ | ⟨hτ, hn, root, hroot, hcr, _, _⟩
  · simp at hc
    omega
  obtain ⟨_, hinv⟩ := Classification.expandDiagram_splice hrun hM hcol ht
    (by rintro (h1 | h1) <;> contradiction) hroot
  obtain ⟨i, x, hi', hxm, hX, hcopy⟩ := hinv.2.2 c hc (by omega)
  have hTop : Top s M t root := ⟨hM, by rw [hcol]; exact ht, hτ, hroot, hcr⟩
  subst hX
  have hNC : NewColumn s n R M t root i x :=
    ⟨hrun, hTop, hn, hinv, hi', hxm, hc,
      ⟨_, Array.getElem?_eq_getElem hc, hcopy⟩⟩
  obtain ⟨vs, us, hvs, hus, hasm⟩ := copyColumn_parts hcopy
  have hCJ : ColJumpU t.row (colCtx M R root i x) R (vs.flatten ++ us) := by
    intro k hk l e p hθk hleft' hθ' hHB'
    rcases Nat.eq_zero_or_pos i with hi0 | hi0
    · subst hi0
      exact colJump_block0 hNC hvs hus hasm k hk l e p hleft' hθ' hHB'
    · refine colJump_upper seamTauHolds hNC hi0 hvs hus hasm k hk l e p ?_ hleft' hθ' hHB'
      by_contra hlt
      have hmem : (vs.flatten ++ us)[k + 1] ∈ vs.flatten := by
        rw [List.getElem_append_left (by omega)]
        exact List.getElem_mem _
      have h1 := lower_lt hNC.runCtx hvs _ hmem
      have h2 := stored_strictMono h1
      rw [Classification.stored_official (le_of_lt (tau_gt_one' hTop))] at h2
      exact absurd (lt_of_lt_of_le h2 hθk) (lt_irrefl _)
  replace hasm : assemble (colCtx M R root i x) (vs.flatten ++ us) =
      .ok R[x + (M.size - 1 - root.column) * i] := hasm
  generalize hctx : colCtx M R root i x = ctx at hCJ hasm
  generalize hemits : vs.flatten ++ us = emits at hCJ hasm
  -- the two cells
  obtain ⟨k, rfl⟩ : ∃ k, index = k + 1 := ⟨index - 1, by omega⟩
  obtain ⟨hsize, hcells⟩ := assemble_below hasm
  have hk1 : k + 1 < emits.length := by
    have := (Array.getElem?_eq_some_iff.mp hu).1
    omega
  obtain ⟨cl, hcl, hclrow, _, _⟩ := hcells k (by omega)
  obtain ⟨cu, hcu, hcurow, hcunone, hcusome⟩ := hcells (k + 1) hk1
  have hcl' : cl = lower := Option.some.inj (hcl.symm.trans hl)
  have hcu' : cu = upper := Option.some.inj (hcu.symm.trans hu)
  subst hcl' hcu'
  -- the new row is above the bottom
  have hθ : emits[k + 1].row = Row.bump emits[k].row e := by
    apply stored_inj
    rw [stored_bump, ← hcurow, ← hclrow, hbump]
  have hθpos : emits[k].row < emits[k + 1].row := by
    rw [hθ]; exact Row.lt_bump _ _
  obtain ⟨l, hlsome⟩ : ∃ l, emits[k + 1].leftColumn = some l := by
    cases hlc : emits[k + 1].leftColumn with
    | some l => exact ⟨l, rfl⟩
    | none =>
      have h0 := hcunone hlc
      rw [h0] at hθpos
      exact absurd hθpos (not_lt.mpr (Row.zero_le _))
  obtain ⟨ref', href', hbelow⟩ := hcusome l hlsome
  have hrr : ref' = ref := Option.some.inj (href'.symm.trans hleft)
  subst hrr
  -- the output is valid
  have hI := expandDiagram_inv hM n R hrun
  have hB := basic_of_inv hM hI (fun c hc hx => bottomHolds s n R hrun c hc (by omega))
  have hV := hB.valid
  -- the column read
  have hres : ctx.result = R.extract 0 (x + (M.size - 1 - root.column) * i) := by
    rw [← hctx]; rfl
  obtain ⟨nodes, hnodes⟩ := below_nodes hbelow
  have hq : legCol ctx l < x + (M.size - 1 - root.column) * i := by
    have := (Array.getElem?_eq_some_iff.mp hnodes).1
    rw [hres] at this
    simp only [Array.size_extract] at this
    omega
  have hnodesR : R[legCol ctx l]? = some nodes := by
    rw [← hnodes, hres]
    exact (getElem?_extract_lt hq).symm
  obtain ⟨hrefc, pc, hpc, hpcrow⟩ := Expansion.below_result hnodes hbelow
  have hpar : pc = parent := by
    obtain ⟨col', hcol', hcell'⟩ := cellAt_ok_iff.mp hcell
    rw [hrefc, hnodesR] at hcol'
    obtain rfl := Option.some.inj hcol'
    exact Option.some.inj (hpc.symm.trans hcell')
  subst hpar
  have hqs : legCol ctx l < R.size := (Array.getElem?_eq_some_iff.mp hnodesR).1
  have hCV : ColumnValid R (legCol ctx l) nodes := by
    have := hV _ hqs
    rwa [(Array.getElem?_eq_some_iff.mp hnodesR).2] at this
  -- the parent is real
  obtain ⟨b1, hb1⟩ : ∃ b1, nodes[1]? = some b1 :=
    ⟨nodes[1]'(by have := hCV.size_ge_two; omega),
      Array.getElem?_eq_getElem (by have := hCV.size_ge_two; omega)⟩
  have hθ1 : (1 : Row) < stored emits[k + 1].row := by
    have := stored_strictMono (lt_of_le_of_lt (Row.zero_le _) hθpos)
    rwa [stored_zero] at this
  have hidx : 1 ≤ ref'.index :=
    Expansion.below_max_index hnodes hbelow hb1 (by rw [hCV.bottom_row b1 hb1]; exact hθ1)
  have hpc1 : (1 : Row) ≤ pc.row :=
    row_one_le_of_ne_zero (ne_of_gt (hCV.rows_strict 0 ref'.index phantom pc hCV.phantom hpc
      (by omega)))
  -- the highest row below
  have hHB : HighestBelow (rowsOf R (legCol ctx l)) emits[k + 1].row (official pc.row) := by
    refine ⟨?_, ?_, ?_⟩
    · refine List.mem_map.mpr ⟨(⟨legCol ctx l, ref'.index⟩, pc), ?_, rfl⟩
      refine mem_realNodes_iff.mpr ⟨nodes, ref'.index - 1, hnodesR, ?_, ?_⟩
      · rw [show ref'.index - 1 + 1 = ref'.index by omega]; exact hpc
      · simp only [Ref.mk.injEq, true_and]; omega
    · have := official_strictMono hpc1 hpcrow
      rwa [official_stored] at this
    · intro r hr hrθ
      obtain ⟨q, hqm, rfl⟩ := List.mem_map.mp hr
      obtain ⟨col', j, hcol', hcellj, hq1⟩ := mem_realNodes_iff.mp hqm
      rw [hnodesR] at hcol'
      obtain rfl := Option.some.inj hcol'
      have hq1r : (1 : Row) ≤ q.2.row := realNodes_row_one_le hV hqm
      have hlt : q.2.row < stored emits[k + 1].row := by
        have := stored_strictMono hrθ
        rwa [Classification.stored_official hq1r] at this
      have hj := Expansion.below_max_index hnodes hbelow hcellj hlt
      apply official_mono hq1r
      rcases Nat.eq_or_lt_of_le hj with he | hlt'
      · rw [he] at hcellj
        rw [Option.some.inj (hcellj.symm.trans hpc)]
      · exact (hCV.rows_strict _ _ _ _ hcellj hpc hlt').le
  have hθk : t.row ≤ stored emits[k + 1].row := by
    obtain ⟨rfl, rfl, rfl⟩ := CrossUpperSim.top_unique hTop0 hTop
    rw [← hcurow]; exact hup
  have hj := hCJ k hk1 l e (official pc.row) hθk hlsome hθ hHB
  rw [hclrow, ← Classification.stored_official hpc1, jump_stored]
  exact hj


/-- `ColJump` for the lower pairs whose leg column is left of `cr`. -/
def ColJumpL (θ : Row) (cr : Nat) (ctx : Context) (R : Mountain) (emits : List Emit) : Prop :=
  ∀ k (hk : k + 1 < emits.length) (l e : Nat) (p : Row),
    stored emits[k + 1].row < θ → legCol ctx l < cr →
    emits[k + 1].leftColumn = some l →
    emits[k + 1].row = Row.bump emits[k].row e →
    HighestBelow (rowsOf R (legCol ctx l)) emits[k + 1].row p →
    Row.jump emits[k].row p = e

/-- **The jump law at a node of the lower part of a new column whose parent is left of `c_r`**
(from the proved `LowerPairsLeft`). -/
theorem leftJump {s : List Nat} {n : Nat} {R : Mountain}
    (hrun : Official.expandDiagram s n = .ok R) {M0 : Mountain} {t0 : Cell} {root0 : Ref}
    (hTop0 : Top s M0 t0 root0) {c : Nat} (hc : c < R.size) (hx : s.length - 1 ≤ c)
    {index : Nat} {lower upper parent : Cell} {ref : Ref} {e : Nat}
    (hl : R[c][index]? = some lower) (hu : R[c][index + 1]? = some upper) (hi : 0 < index)
    (hleft : upper.left = some ref) (hcell : cellAt R ref = .ok parent)
    (hbump : upper.row = Row.bump lower.row e) (hlow : upper.row < t0.row)
    (hleg : ref.column < root0.column) :
    Row.jump lower.row parent.row = e := by
  obtain ⟨M, hM, hcases⟩ := Reconstruction.expandDiagram_cases hrun
  have hMs := Canonical.build_size hM
  rcases hcases with ⟨rfl, rfl⟩ | ⟨_, col, t, hcol, ht, hcases⟩
  · simp only [List.length_nil] at hMs
    omega
  rcases hcases with ⟨_, rfl⟩ | ⟨hτ, hn, root, hroot, hcr, _, _⟩
  · simp at hc
    omega
  obtain ⟨_, hinv⟩ := Classification.expandDiagram_splice hrun hM hcol ht
    (by rintro (h1 | h1) <;> contradiction) hroot
  obtain ⟨i, x, hi', hxm, hX, hcopy⟩ := hinv.2.2 c hc (by omega)
  have hTop : Top s M t root := ⟨hM, by rw [hcol]; exact ht, hτ, hroot, hcr⟩
  subst hX
  have hNC : NewColumn s n R M t root i x :=
    ⟨hrun, hTop, hn, hinv, hi', hxm, hc,
      ⟨_, Array.getElem?_eq_getElem hc, hcopy⟩⟩
  obtain ⟨vs, us, hvs, hus, hasm⟩ := copyColumn_parts hcopy
  have hCJ : ColJumpL t.row root.column (colCtx M R root i x) R (vs.flatten ++ us) := by
    intro k hk l e p hθk hlc hleft' hθ' hHB'
    have hl : l < root.column := by
      by_contra hn
      have : legCol (colCtx M R root i x) l = l + (M.size - 1 - root.column) * i := by
        unfold legCol colCtx Classification.ctxAt
        simp [show root.column ≤ l by omega]
      omega
    rcases Nat.eq_zero_or_pos i with hi0 | hi0
    · subst hi0
      exact colJump_block0 hNC hvs hus hasm k hk l e p hleft' hθ' hHB'
    · refine LowerLeftDone.lowerPairsLeft_holds s n R M t root i x hNC hi0 vs us hvs hus _ hasm
        k hk l e p ?_ hleft' hθ' hHB' hl
      by_contra hge
      have hmem : (vs.flatten ++ us)[k + 1] ∈ us := by
        rw [List.getElem_append_right (by omega)]
        exact List.getElem_mem _
      obtain ⟨_, _, _, hτ, _⟩ := (upper_facts hus).1 _ hmem
      have h2 := CrossUpper.stored_mono hτ
      rw [Classification.stored_official (le_of_lt (tau_gt_one' hTop))] at h2
      exact absurd (lt_of_le_of_lt h2 hθk) (lt_irrefl _)
  replace hasm : assemble (colCtx M R root i x) (vs.flatten ++ us) =
      .ok R[x + (M.size - 1 - root.column) * i] := hasm
  generalize hctx : colCtx M R root i x = ctx at hCJ hasm
  generalize hemits : vs.flatten ++ us = emits at hCJ hasm
  -- the two cells
  obtain ⟨k, rfl⟩ : ∃ k, index = k + 1 := ⟨index - 1, by omega⟩
  obtain ⟨hsize, hcells⟩ := assemble_below hasm
  have hk1 : k + 1 < emits.length := by
    have := (Array.getElem?_eq_some_iff.mp hu).1
    omega
  obtain ⟨cl, hcl, hclrow, _, _⟩ := hcells k (by omega)
  obtain ⟨cu, hcu, hcurow, hcunone, hcusome⟩ := hcells (k + 1) hk1
  have hcl' : cl = lower := Option.some.inj (hcl.symm.trans hl)
  have hcu' : cu = upper := Option.some.inj (hcu.symm.trans hu)
  subst hcl' hcu'
  -- the new row is above the bottom
  have hθ : emits[k + 1].row = Row.bump emits[k].row e := by
    apply stored_inj
    rw [stored_bump, ← hcurow, ← hclrow, hbump]
  have hθpos : emits[k].row < emits[k + 1].row := by
    rw [hθ]; exact Row.lt_bump _ _
  obtain ⟨l, hlsome⟩ : ∃ l, emits[k + 1].leftColumn = some l := by
    cases hlc : emits[k + 1].leftColumn with
    | some l => exact ⟨l, rfl⟩
    | none =>
      have h0 := hcunone hlc
      rw [h0] at hθpos
      exact absurd hθpos (not_lt.mpr (Row.zero_le _))
  obtain ⟨ref', href', hbelow⟩ := hcusome l hlsome
  have hrr : ref' = ref := Option.some.inj (href'.symm.trans hleft)
  subst hrr
  -- the output is valid
  have hI := expandDiagram_inv hM n R hrun
  have hB := basic_of_inv hM hI (fun c hc hx => bottomHolds s n R hrun c hc (by omega))
  have hV := hB.valid
  -- the column read
  have hres : ctx.result = R.extract 0 (x + (M.size - 1 - root.column) * i) := by
    rw [← hctx]; rfl
  obtain ⟨nodes, hnodes⟩ := below_nodes hbelow
  have hq : legCol ctx l < x + (M.size - 1 - root.column) * i := by
    have := (Array.getElem?_eq_some_iff.mp hnodes).1
    rw [hres] at this
    simp only [Array.size_extract] at this
    omega
  have hnodesR : R[legCol ctx l]? = some nodes := by
    rw [← hnodes, hres]
    exact (getElem?_extract_lt hq).symm
  obtain ⟨hrefc, pc, hpc, hpcrow⟩ := Expansion.below_result hnodes hbelow
  have hpar : pc = parent := by
    obtain ⟨col', hcol', hcell'⟩ := cellAt_ok_iff.mp hcell
    rw [hrefc, hnodesR] at hcol'
    obtain rfl := Option.some.inj hcol'
    exact Option.some.inj (hpc.symm.trans hcell')
  subst hpar
  have hqs : legCol ctx l < R.size := (Array.getElem?_eq_some_iff.mp hnodesR).1
  have hCV : ColumnValid R (legCol ctx l) nodes := by
    have := hV _ hqs
    rwa [(Array.getElem?_eq_some_iff.mp hnodesR).2] at this
  -- the parent is real
  obtain ⟨b1, hb1⟩ : ∃ b1, nodes[1]? = some b1 :=
    ⟨nodes[1]'(by have := hCV.size_ge_two; omega),
      Array.getElem?_eq_getElem (by have := hCV.size_ge_two; omega)⟩
  have hθ1 : (1 : Row) < stored emits[k + 1].row := by
    have := stored_strictMono (lt_of_le_of_lt (Row.zero_le _) hθpos)
    rwa [stored_zero] at this
  have hidx : 1 ≤ ref'.index :=
    Expansion.below_max_index hnodes hbelow hb1 (by rw [hCV.bottom_row b1 hb1]; exact hθ1)
  have hpc1 : (1 : Row) ≤ pc.row :=
    row_one_le_of_ne_zero (ne_of_gt (hCV.rows_strict 0 ref'.index phantom pc hCV.phantom hpc
      (by omega)))
  -- the highest row below
  have hHB : HighestBelow (rowsOf R (legCol ctx l)) emits[k + 1].row (official pc.row) := by
    refine ⟨?_, ?_, ?_⟩
    · refine List.mem_map.mpr ⟨(⟨legCol ctx l, ref'.index⟩, pc), ?_, rfl⟩
      refine mem_realNodes_iff.mpr ⟨nodes, ref'.index - 1, hnodesR, ?_, ?_⟩
      · rw [show ref'.index - 1 + 1 = ref'.index by omega]; exact hpc
      · simp only [Ref.mk.injEq, true_and]; omega
    · have := official_strictMono hpc1 hpcrow
      rwa [official_stored] at this
    · intro r hr hrθ
      obtain ⟨q, hqm, rfl⟩ := List.mem_map.mp hr
      obtain ⟨col', j, hcol', hcellj, hq1⟩ := mem_realNodes_iff.mp hqm
      rw [hnodesR] at hcol'
      obtain rfl := Option.some.inj hcol'
      have hq1r : (1 : Row) ≤ q.2.row := realNodes_row_one_le hV hqm
      have hlt : q.2.row < stored emits[k + 1].row := by
        have := stored_strictMono hrθ
        rwa [Classification.stored_official hq1r] at this
      have hj := Expansion.below_max_index hnodes hbelow hcellj hlt
      apply official_mono hq1r
      rcases Nat.eq_or_lt_of_le hj with he | hlt'
      · rw [he] at hcellj
        rw [Option.some.inj (hcellj.symm.trans hpc)]
      · exact (hCV.rows_strict _ _ _ _ hcellj hpc hlt').le
  obtain ⟨rfl, rfl, rfl⟩ := CrossUpperSim.top_unique hTop0 hTop
  have hθk : stored emits[k + 1].row < t0.row := by
    rw [← hcurow]; exact hlow
  have hlc : legCol ctx l < root0.column := by rw [← hrefc]; exact hleg
  have hj := hCJ k hk1 l e (official pc.row) hθk hlc hlsome hθ hHB
  rw [hclrow, ← Classification.stored_official hpc1, jump_stored]
  exact hj


#print axioms OmegaY.Official.Recon.JumpLaw.jumpLawHolds_of_col


end OmegaY.Official.Recon.JumpLaw.TopChainU
