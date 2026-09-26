/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/SeamClean.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.SeamX0

set_option backward.do.legacy false

set_option autoImplicit false

/-!
# Clean copies in the diagram (the base of `StepCleanNT`)

`NonTopBase.lean` studies a clean copy (`b = 0`) `v` of `a = (y, C)` in a copied column of a
block `i ≥ 1` when the output is the canonical mountain of `s[n]` (`Setting`). Here the same
facts are proved for the diagram `R = expandDiagram s n` of a run (`Env`):

* `copyAtX_cellD`, `copyAtX_leftD`: the cell of a traced node and its left end;
* `factsXD`: `Inner.Clean.Facts` for the context of a copied column (the boundary rows from
  `CutPredMD.boundaryRootRowsHolds`);
* `cleanX_parent_rowD`: the raw parent of `v` is on the row of `v` (the jump law of the output,
  `LRC.jumpLawHolds`, in place of the row law of a canonical mountain).

All declarations are in the namespace `ChainCorr.NonTop.SeamD`.
-/

namespace OmegaY.Official.Classification.Proofs.ChainCorr.NonTop.SeamD

open Canonical Reserve Official Descent Classification Proofs
open Recon Recon.RowLaw
open ChainCorr.Inner ChainCorr.Inner.Clean ChainCorr.Inner.CleanRoot
open Geometry

section Run

variable {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}

/-- The size of the output of a run with `n ≥ 1`. -/
theorem size_of_run (hrun : Official.expandDiagram s n = .ok R) (hTop : Recon.Top s M t root)
    (hn : n ≠ 0) : R.size = (M.size - 1) + n * (M.size - 1 - root.column) :=
  CopyShape.Found.run_size hrun hTop hn

/-- **The cell of a traced node** (diagram form of `copyAtX_cell`). -/
theorem copyAtX_cellD (E : CrossUpperSim.Env s n R M t root) {i : Nat} (hi0 : 0 < i)
    (hi : i < n + 1) {v : Ref} {o : Origin}
    (h : CopyAtX M R n root.column (M.size - 1) (official t.row) i v o) :
    ∃ y es j, ∃ hj : j < es.length, es[j].2 = o ∧
      (v.column = y + (M.size - 1 - root.column) * i ∧ root.column < y ∧ y ≤ M.size - 1 ∧
        v.column < R.size) ∧
      y ∈ blockColumns root.column (M.size - 1) n i ∧ v.index = j + 1 ∧
      emitsT (ctxAt M R y i root.column (M.size - 1 - root.column) (M.size - 1) v.column)
        (official t.row) = .ok es ∧
      ∃ cv, cell? R v = some cv ∧ cv.row = stored es[j].1.row ∧ ∃ ref : Ref, cv.left = some ref ∧
        ref.column = legColumn (ctxAt M R y i root.column (M.size - 1 - root.column) (M.size - 1)
          v.column) es[j].1 := by
  obtain ⟨y, es, j, hcy, hyx, hyb, hvc, hvi, hes, hj, ho⟩ := h
  have hinv := E.CI
  have hcrx := E.top.lt
  have hRs := size_of_run E.run E.top (by omega)
  have hw1 : M.size - 1 - root.column ≤ (M.size - 1 - root.column) * i :=
    Nat.le_mul_of_pos_right _ hi0
  have hXR : v.column < R.size := by
    rw [hRs, hvc]
    unfold blockColumns at hyb
    rw [if_neg (by omega)] at hyb
    simp only [List.mem_range'_1] at hyb
    by_cases hin : i < n
    · rw [if_pos hin] at hyb
      have : (M.size - 1 - root.column) * i + (M.size - 1 - root.column) ≤
          n * (M.size - 1 - root.column) := by
        rw [Nat.mul_comm n, ← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hin
      omega
    · rw [if_neg hin] at hyb
      have hin' : i = n := by omega
      subst hin'
      rw [Nat.mul_comm]
      omega
  have hX0 : M.size - 1 ≤ v.column := by omega
  obtain ⟨i', x', _, hx', hXeq, hcopy⟩ := hinv.2.2 v.column hXR hX0
  obtain ⟨hii, hxx⟩ := blockX_unique hcrx hcy hyx hx' (hvc.symm.trans hXeq) hi0
  subst hii
  subst hxx
  obtain ⟨es', hes', hasm⟩ := copyColumn_emitsT hcopy
  have hee : es' = es := Except.ok.inj (hes'.symm.trans hes)
  subst hee
  obtain ⟨_, hcells⟩ := assemble_spec hasm
  obtain ⟨cell, hcellX, hrow, ref, hrefl, hrefc⟩ := hcells j (by simpa using hj)
  simp only [List.getElem_map] at hrow hrefc
  refine ⟨x', es', j, hj, ho, ⟨hvc, hcy, hyx, hXR⟩, hyb, hvi, hes, cell, ?_, hrow, ref, hrefl,
    hrefc⟩
  simp only [cell?, Array.getElem?_eq_getElem hXR, Option.bind_eq_bind, Option.bind_some, hvi]
  exact hcellX

/-- The diagram of a run is a valid mountain. -/
theorem validR (hrun : Official.expandDiagram s n = .ok R) : MountainValid R := by
  obtain ⟨_, _, _, _, hB⟩ := run_basic hrun
  exact hB.valid

/-- **The left end of a traced node** (diagram form of `copyAtX_left`). -/
theorem copyAtX_leftD (E : CrossUpperSim.Env s n R M t root) {i : Nat} (hi0 : 0 < i)
    (hi : i < n + 1) {u : Ref} {o : Origin}
    (h : CopyAtX M R n root.column (M.size - 1) (official t.row) i u o) :
    ∃ (cu : Cell) (ref : Ref) (co : Cell) (l : Ref), cell? R u = some cu ∧ cu.left = some ref ∧
      cell? M o.src = some co ∧ co.left = some l ∧
      ref.column = mapColumn root.column ((M.size - 1 - root.column) * i) l.column := by
  have hV := build_valid_of_success E.top.build
  obtain ⟨y, es, j, hj, ho, ⟨hvc, hcy, hyx, hXR⟩, _, hvi, hes, cu, hcu, _, ref, hrefl, hrefc⟩ :=
    copyAtX_cellD E hi0 hi h
  obtain ⟨hsc, hsi, co, hco, hleft⟩ := emitsT_good hes es[j] (List.getElem_mem hj)
  rw [ho] at hsc hsi hco hleft
  rcases hleft with ⟨l, hl, hlc⟩ | ⟨hnone, h0, hnu⟩
  · refine ⟨cu, ref, co, l, hcu, hrefl, hco, hl, ?_⟩
    rw [hrefc]
    simp only [legColumn, hlc, ctxAt, mapColumn]
    by_cases hh : root.column ≤ l.column
    · simp [hh, show ¬ l.column < root.column by omega]
    · simp [hh, show l.column < root.column by omega]
  · rw [hnu] at hsc
    simp only [Bool.false_eq_true, if_false, ctxAt] at hsc
    have hi1 := index_one_of_official_zero hV hco hsi h0
    have hbl := bottom_left E.top.build hco hi1 (by omega)
    refine ⟨cu, ref, co, ⟨o.src.column - 1, 0⟩, hcu, hrefl, hco, hbl, ?_⟩
    rw [hrefc]
    simp only [legColumn, hnone, ctxAt, Array.size_extract]
    rw [hsc, mapColumn_of_ge (by omega), hvc]
    have hXR' : y + (M.size - 1 - root.column) * i ≤ R.size := by omega
    omega

/-- **`Facts` in every copied column of a block `i ≥ 1`** (diagram form of `factsX`). -/
theorem factsXD (E : CrossUpperSim.Env s n R M t root) {i : Nat} (hi0 : 0 < i) (hi : i < n + 1)
    {y : Nat} (hcy : root.column < y) :
    Facts (ctxAt M R y i root.column (M.size - 1 - root.column) (M.size - 1)
      (y + (M.size - 1 - root.column) * i)) (official t.row) := by
  have hTop := E.top
  have hVR := validR E.run
  refine ⟨⟨s, hTop.build⟩, by simp [ctxAt]; omega, by simp [ctxAt]; exact hcy, ?_, ?_⟩
  · intro S ρ' hbelow hρ'
    simp only [ctxAt] at hρ' ⊢
    obtain ⟨κ, hκ, hlt⟩ := liftTwo hTop hbelow hρ'
    rw [hκ]
    exact hlt
  · intro S ρ' hbelow hρ'
    simp only [ctxAt, Context.boundary] at hρ' ⊢
    have hbc : root.column + (M.size - 1 - root.column) * i <
        y + (M.size - 1 - root.column) * i := by omega
    rw [topIn_extract hbc]
    obtain ⟨hρmem, hρin, _⟩ := topIn_spec hρ'
    obtain ⟨col, hcol, htc⟩ := CopyShape.Found.top_col hTop
    have hBR := CopyShape.Found.boundary_lt E.run hTop (i := i) hi0 (by omega)
    obtain ⟨q, hqmem, hqrow⟩ := CutPredMD.boundaryRootRowsHolds s n R E.run M col t root
      hTop.build hcol htc hTop.left hTop.lt i hi0 hBR ρ' hρmem (hbelow _ hρin)
    have hqin : inRegion 2 S (official q.2.row) = true := by rw [hqrow]; exact hρin
    obtain ⟨b, hb⟩ := filter_last_exists (P := fun p => inRegion 2 S (official p.2.row)) hqmem hqin
    have hb' : topIn R (root.column + (M.size - 1 - root.column) * i) 2 S = some b := hb
    rw [hb']
    have hle := LRC.topIn_row_max' hVR hb' hqmem hqin
    have := coeff_le_of_inRegion (d := 0) hqin (topIn_spec hb').2.1 hle
    rw [hqrow] at this
    exact this

/-- **The raw parent of a clean copy is on the row of the copy** (diagram form of
`cleanX_parent_row`, by the jump law of the output). -/
theorem cleanX_parent_rowD (E : CrossUpperSim.Env s n R M t root) {i : Nat} (hi0 : 0 < i)
    (hi : i < n + 1) {v a : Ref}
    (hva : CopyAtX M R n root.column (M.size - 1) (official t.row) i v (.clean a false)) :
    ∃ (ca : Cell) (l : Ref) (cv : Cell) (v1 : Ref) (c1 : Cell), cell? M a = some ca ∧
      ca.left = some l ∧ cell? R v = some cv ∧ rawParent R v = some v1 ∧
      cell? R v1 = some c1 ∧ c1.row = cv.row ∧
      highestAtMost R (mapColumn root.column ((M.size - 1 - root.column) * i) l.column) cv.row =
        some v1 := by
  have hva' := hva
  obtain ⟨y, es, j, hcy, hyx, hyb, hvc, hvi, hes, hj, ho⟩ := hva'
  have hes' : emitsT (ctxAt M R y i root.column (M.size - 1 - root.column) (M.size - 1)
      (y + (M.size - 1 - root.column) * i)) (official t.row) = .ok es := by rw [← hvc]; exact hes
  have hF := factsXD E hi0 hi hcy
  obtain ⟨hj1, hnext, hrow⟩ := emitsT_follow hF hes' j hj a ho
  have hup : CopyAtX M R n root.column (M.size - 1) (official t.row) i (up v) (.clean a true) :=
    ⟨y, es, j + 1, hcy, hyx, hyb, by simp only [up]; exact hvc, by simp only [up]; omega,
      by simp only [up]; exact hes, hj1, hnext⟩
  have hcellrow : ∀ {u : Ref} {k : Nat} (hk : k < es.length), u.column = v.column →
      u.index = k + 1 → ∃ cu, cell? R u = some cu ∧ cu.row = stored es[k].1.row := by
    intro u k hk hu1 hu2
    have hcu : CopyAtX M R n root.column (M.size - 1) (official t.row) i u es[k].2 :=
      ⟨y, es, k, hcy, hyx, hyb, by rw [hu1]; exact hvc, hu2, by rw [hu1]; exact hes, hk, rfl⟩
    obtain ⟨y', es', k', hk', _, ⟨hyc', hcy', hyx', _⟩, _, hki, hes2, cu, hcu', hcurow, _⟩ :=
      copyAtX_cellD E hi0 hi hcu
    have hyy : y' = y := by
      have hcrx : root.column < M.size - 1 := by omega
      have := blockX_unique (x' := y) (i' := i) hcrx hcy' hyx' hyb
        (by rw [← hyc', hu1, hvc]) hi0
      exact this.2.symm
    subst hyy
    have hee : es' = es := by
      have hux : u.column = y' + (M.size - 1 - root.column) * i := by rw [hu1, hvc]
      rw [hux, hes'] at hes2
      exact (Except.ok.inj hes2).symm
    subst hee
    have hkk : k' = k := by omega
    subst hkk
    exact ⟨cu, hcu', hcurow⟩
  obtain ⟨cv, hcv, hcvrow⟩ := hcellrow hj rfl hvi
  obtain ⟨cu, hcu, hcurow⟩ := hcellrow hj1 (u := up v) (by simp [up]) (by simp [up]; omega)
  have hbump : cu.row = Row.bump cv.row 0 := by
    rw [hcurow, hcvrow, hrow, stored_bump]
  obtain ⟨cu', ref, co, l, hcu', hrefl, hco, hl, hrefc⟩ := copyAtX_leftD E hi0 hi hup
  have hcc : cu' = cu := Option.some.inj (hcu'.symm.trans hcu)
  subst hcc
  have hraw : rawParent R v = some ref := rawParent_eq_some.mpr ⟨cu', hcu', hrefl⟩
  have hv0 : 0 < v.index := by omega
  -- the jump law of the output
  have hVR := validR E.run
  obtain ⟨cq, hcq, hqlt⟩ := left_cell hVR hcu' hrefl
  have hXR : v.column < R.size := by
    obtain ⟨col, hcol, _⟩ := cell?_column hcv
    exact (Array.getElem?_eq_some_iff.mp hcol).1
  have hl' : R[v.column][v.index]? = some cv := by
    have := hcv; simp only [cell?, Array.getElem?_eq_getElem hXR, Option.bind_eq_bind,
      Option.bind_some] at this; exact this
  have hu' : R[v.column][v.index + 1]? = some cu' := by
    have := hcu'; simp only [cell?, up, Array.getElem?_eq_getElem hXR, Option.bind_eq_bind,
      Option.bind_some] at this; exact this
  have hx : s.length - 1 ≤ v.column := by
    rw [← E.Ms, hvc]
    have := Nat.le_mul_of_pos_right (M.size - 1 - root.column) hi0
    omega
  have hcell : cellAt R ref = .ok cq := by
    rw [cellAt_ok_iff]
    unfold cell? at hcq
    cases hcol : R[ref.column]? with
    | none => rw [hcol] at hcq; cases hcq
    | some col =>
      rw [hcol] at hcq
      exact ⟨col, rfl, by simpa using hcq⟩
  have hj0 := LRC.jumpLawHolds s n R E.run v.column hXR hx v.index _ _ _ _ 0 hl' hu' hv0 hrefl
    hcell hbump
  have hcqrow : cq.row = cv.row := (Row.jump_eq_zero.mp hj0).symm
  -- `ref` is the highest node of its column at or below the row of `v`
  have hham : highestAtMost R ref.column cv.row = some ref := by
    obtain ⟨vN, hvN, hvNc⟩ := LowerChainRecon.node_of_cell hcv
    obtain ⟨uN, huN, huNc⟩ := LowerChainRecon.node_of_cell hcu'
    obtain ⟨qN, hqN, hqNc⟩ := LowerChainRecon.node_of_cell hcq
    have hu1 : uN.1 = vN.1 := Fin.ext (by
      have h1 := congrArg Ref.column huN; have h2 := congrArg Ref.column hvN
      simp [Frame.ref, up] at h1 h2; omega)
    have huu : (Frame.ofMountain R).upper vN = some uN :=
      ControlProof.upper_eq_of_index hu1.symm (by
        have h1 := congrArg Ref.index huN; have h2 := congrArg Ref.index hvN
        simp [Frame.ref, up] at h1 h2; omega)
    have hvr : Frame.Real vN := by
      show 0 < vN.2.val
      have := congrArg Ref.index hvN; simp [Frame.ref] at this; omega
    have hqraw : (Frame.ofMountain R).rawParent vN = some qN :=
      Geometry.Frame.rawParent_eq_of_upper_left huu (by rw [huNc, hqN]; exact hrefl)
    have hH := CrossUpperSim.highestIn_of_hb (E.HB vN hvr) huu hqraw
    have hhu : (Frame.ofMountain R).height uN = Row.bump cv.row 0 := by
      change ((Frame.ofMountain R).cell uN).row = _; rw [huNc, hbump]
    rw [hhu] at hH
    have hH' : CrossUpperSim.HighestIn (Frame.ofMountain R) (· ≤ cv.row) qN :=
      ⟨CopyShape.ProfileLeg.le_of_lt_bump0 hH.1, fun w hw hle =>
        hH.2 w hw (lt_of_le_of_lt hle (Row.lt_bump _ _))⟩
    have hqr : Frame.Real qN := by
      apply CrossUpper.real_of_one_le (validR E.run).toOrdered
      change (1 : Row) ≤ ((Frame.ofMountain R).cell qN).row
      rw [hqNc, hcqrow]
      exact Classification.one_le_row hVR hcv hv0
    have := LowerChainRecon.highestAtMost_of_highestIn hqr hH'
    rw [hqN] at this
    have hqc : qN.1.val = ref.column := by
      have := congrArg Ref.column hqN; simpa [Frame.ref] using this
    rw [hqc] at this
    exact this
  rw [hrefc] at hham
  exact ⟨co, l, cv, ref, cq, hco, hl, hcv, hraw, hcq, hcqrow, hham⟩

end Run

open Geometry.Frame in
/-- **The first step of the generation chain of a clean copy** (`chainX_first_step` with the
top data in place of `Setting`). -/
theorem chainX_first_stepD {s : List Nat} {M : Mountain} {t : Cell} {root : Ref}
    (hTop : Recon.Top s M t root) {n : Nat} {R : Mountain} {i : Nat}
    {v a : Ref} (hva : CopyAtX M R n root.column (M.size - 1) (official t.row) i v (.clean a false)) :
    ∃ b, GenStep M root.column a b ∧ root.column ≤ b.column := by
  obtain ⟨y, es, j, hcy, hyx, hyb, hvc, hvi, hes, hj, ho⟩ := hva
  have hes' : emitsT (ctxAt M R y i root.column ((M.size - 1) - root.column) (M.size - 1) (y + ((M.size - 1) - root.column) * i))
      (official t.row) = .ok es := by rw [← hvc]; exact hes
  obtain ⟨C, cs, hcs, ⟨ref, cl, hn, hr⟩, hroot⟩ :=
    emitsT_cleanRoot hes' es[j] (List.getElem_mem hj) a false ho
  simp only [ctxAt] at hcs hn hr hroot
  have hb := hTop.build
  have hN := build_normal_of_success hb
  have hO := hN.toOrdered
  obtain ⟨hac, ha1, hacell, harow⟩ := Classification.nodeAt_spec hcs
  simp only at hac ha1 hacell harow
  by_cases h0 : 0 < C.coeff 0
  · have hZC := Recon.RowLaw.referenceRow_bump h0
    obtain ⟨hrc, hr1, hrcell, hrrow⟩ := Classification.nodeAt_spec hn
    simp only at hrc hr1 hrcell hrrow
    obtain ⟨cu, hcu, hofu, g, hg, hgc⟩ :=
      chain_to_root hb hZC hroot (y + 1) ref cl hrcell hr1 hrrow (by rw [hrc]; exact hcy) hr
    have hupa : up ref = a := by
      obtain ⟨hmem, _⟩ := Recon.RowLaw.nodeAt_spec hcs
      have hupmem : (up ref, cu) ∈ realNodes M y := by
        rw [mem_realNodes_iff]
        unfold cell? at hcu
        cases hcolr : M[ref.column]? with
        | none => simp [up, hcolr] at hcu
        | some colr =>
            simp only [up, hcolr, Option.bind_eq_bind, Option.bind_some] at hcu
            refine ⟨colr, ref.index, by rw [← hrc]; exact hcolr, hcu, ?_⟩
            simp [up, hrc]
      have := ChainCorr.realNodes_eq_of_official (build_valid_of_success hb) hupmem hmem
        (by simp only; rw [hofu, harow])
      exact congrArg Prod.fst this
    rw [hupa] at hg
    exact first_step_of_chain hg (le_of_eq hgc.symm)
  · have hZ : referenceRow C = C := by
      unfold referenceRow
      rw [if_neg h0]
    rw [hZ, hcs] at hn
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hn)
    obtain ⟨q, hw, hqcr⟩ := ChainCorr.weakParent_of_reachesRoot (by rw [hac]; exact hcy) hr
    obtain ⟨col', cell, upper, parentCell, hcol, hcell, hup, hleft, hpc, hprow⟩ :=
      Recon.RowLaw.weakParent_some hw
    have hraw : Reserve.rawParent M a = some q := by
      simp only [Reserve.rawParent, hcol, Option.bind_eq_bind, Option.bind_some, hup, hleft]
    have hcellr : cell? M a = some cell := by simp [cell?, hcol, hcell]
    have hcc : cell = cs := Option.some.inj (hcellr.symm.trans hacell)
    subst hcc
    have hqc : cell? M q = some parentCell := by
      obtain ⟨column, h1, h2⟩ := cellAt_ok_iff.mp hpc
      simp [cell?, h1, h2]
    obtain ⟨na, hna, hnacell⟩ := ControlProof.node_of_cell? hacell
    have hareal : Frame.Real na := by
      show 0 < na.2.val
      have : na.2.val = a.index := by rw [← hna]; rfl
      omega
    obtain ⟨nq, hPa, hnq⟩ := P_of_rawParent hN hareal (hna ▸ hraw)
    obtain ⟨q0, hQ0, hit0⟩ := (P_iff hO).mp hPa
    have hnqcell : (Frame.ofMountain M).cell nq = parentCell := by
      have := ControlProof.cell?_ref nq
      rw [hnq, hqc] at this
      exact (Option.some.inj this).symm
    have hh : (Frame.ofMountain M).height nq = (Frame.ofMountain M).height na := by
      show ((Frame.ofMountain M).cell nq).row = ((Frame.ofMountain M).cell na).row
      rw [hnqcell, hnacell, hprow]
    have hc : root.column ≤ nq.1.val := by
      have : nq.1.val = q.column := by rw [← hnq]; rfl
      omega
    have hch := inrow_hit (cr := root.column) hO hit0 na hareal hQ0 hh hc
    rw [hna] at hch
    exact first_step_of_chain hch hc

open CutGap in
/-- **`LookupInner` in every copied column** (diagram form of `lookupInnerX`). -/
theorem lookupInnerXD {s : List Nat} {n : Nat} {M : Mountain} {R : Mountain} {t : Cell}
    {root : Ref} (E : CrossUpperSim.Env s n R M t root) {i : Nat} (hi0 : 0 < i) (hi : i < n + 1)
    {v a : Ref} (hva : CopyAtX M R n root.column (M.size - 1) (official t.row) i v (.clean a false))
    {b : Ref} (hab : GenStep M root.column a b) (hlb : root.column < b.column) {v1 : Ref}
    (hraw : rawParent R v = some v1) :
    CopyAt M R n root.column (M.size - 1) (official t.row) i v1 (.clean b false) := by
  have hb := E.top.build
  have hV := build_valid_of_success hb
  have hVR := validR E.run
  have hva' := hva
  obtain ⟨y, es, j, hcy, hyx, hyb, hvc, hvi, hes, hj, ho⟩ := hva'
  have hes' : emitsT (ctxAt M R y i root.column ((M.size - 1) - root.column) (M.size - 1) (y + ((M.size - 1) - root.column) * i))
      (official t.row) = .ok es := by rw [← hvc]; exact hes
  -- the step `a → b`
  obtain ⟨_, hb1, ca, cb, l, hca, hl, hbl, hcb, hbrow⟩ := hab
  have hlcr : root.column < l.column := by rw [← hbl]; exact hlb
  -- the copied row `C` of `v`: the row of `a`, ascension test of `y`
  obtain ⟨C, cs, hcs, ⟨refx, clx, hnx, hrx⟩, hroot⟩ :=
    emitsT_cleanRoot hes' es[j] (List.getElem_mem hj) a false ho
  simp only [ctxAt] at hcs hnx hrx hroot
  obtain ⟨hac, ha1, hacell, harow⟩ := Classification.nodeAt_spec hcs
  simp only at hac ha1 hacell harow
  have hcsa : cs = ca := Option.some.inj (hacell.symm.trans hca)
  subst hcsa
  -- `C` is the row of the root top of its level-2 region, in a first item of level `≥ 2`
  obtain ⟨⟨qx, hqx, hqx2, hqxin⟩, ρr, ρc, hρ, hρrow⟩ :=
    emitsT_cleanTop hes' es[j] (List.getElem_mem hj) a false ho cs hacell
  simp only [ctxAt] at hρ
  -- the leg column ascends at `ρ`
  have hyl : l.column < y := by
    have := left_lt_of_valid hV hacell hl
    rw [hac] at this
    exact this
  obtain ⟨refl, cll, hnl, hrl⟩ := ascLeg hb hcy (by rw [← harow] at hnx; exact hnx) hrx
    (by rw [← harow] at hcs; exact hcs) hl hlcr
  have hascl : ascends (ctxAt M R l.column i root.column ((M.size - 1) - root.column) (M.size - 1)
      (l.column + ((M.size - 1) - root.column) * i)) (some (ρr, ρc)) = .ok true := by
    apply ascends_of_reach (ref := refl) (cl := cll)
    · simp only [ctxAt]
      rw [hρrow]
      exact hnl
    · simpa [ctxAt] using hrl
  -- the emits of the column `l`
  have hlx : l.column < M.size - 1 := by omega
  have hlmem : l.column ∈ blockColumns root.column (M.size - 1) n i :=
    CrossUpperSim.mem_blockColumns_of_inner hi0 hi hlcr hlx
  obtain ⟨_, _, _, _, hq0, ⟨hvc0, _, _, hXRv⟩, _, _, _, _⟩ := copyAtX_cellD E hi0 hi hva
  have hXRl : l.column + (M.size - 1 - root.column) * i < R.size := by omega
  obtain ⟨lol, usl, hDl⟩ := Recon.TopChain.colData_block E hi0 (by omega) hlmem hXRl
  have hXRy : y + (M.size - 1 - root.column) * i < R.size := by omega
  obtain ⟨loy, usy, hDy⟩ := Recon.TopChain.colData_block E hi0 (by omega) hyb hXRy
  have hesl := hDl.emitsT
  -- the non-cut emit of `b` in the column `l`
  obtain ⟨k0, hk0, hk0src, hk0nc⟩ : ∃ k0, ∃ hk0 : k0 < (lol ++ usl).length, (lol ++ usl)[k0].2.src = b ∧
      cutOrigin (lol ++ usl)[k0].2 = false := by
    have hCτ0 : official cs.row < official t.row :=
      (lowerItems_below (official t.row) _ hqx).1 _ hqxin
    have hbcell : cell? M ⟨(ctxAt M R l.column i root.column (M.size - 1 - root.column)
        (M.size - 1) (l.column + (M.size - 1 - root.column) * i)).x, b.index⟩ = some cb := by
      simp only [ctxAt]; rw [← hbl]; exact hcb
    obtain ⟨e, he, hecut, hesrc⟩ := CopyShape.Final.emitted s n R E.run M t root E.top i hi0
      (by omega) _ hDl.bctx hDl.xgt lol hDl.hlo b.index cb hb1 hbcell
      (by rw [hbrow]; exact hCτ0)
    obtain ⟨m, hm, hme⟩ := List.getElem_of_mem he
    refine ⟨m, by rw [List.length_append]; omega, ?_, ?_⟩
    · rw [List.getElem_append_left hm, hme, hesrc]
      simp only [ctxAt]; rw [← hbl]
    · rw [List.getElem_append_left hm, hme, ← CopyShape.Found.cutO_eq]; exact hecut
  have hCτ : official cs.row < official t.row :=
    (lowerItems_below (official t.row) _ hqx).1 _ hqxin
  have hbC : official cb.row = official cs.row := by rw [hbrow]
  have hclean : (lol ++ usl)[k0].2 = .clean b false := by
    have hlowl := emitsT_plainAsc (ctx := ctxAt M R l.column i root.column ((M.size - 1) - root.column) (M.size - 1)
      (l.column + ((M.size - 1) - root.column) * i)) (τ := official t.row) hesl
    have hupl := emitsT_upperRow (ctx := ctxAt M R l.column i root.column ((M.size - 1) - root.column) (M.size - 1)
      (l.column + ((M.size - 1) - root.column) * i)) (τ := official t.row) hesl
    generalize hE : (lol ++ usl)[k0].2 = o at hk0src hk0nc
    cases o with
    | clean r' bb =>
        cases bb
        · have : r' = b := hk0src
          rw [this]
        · simp [cutOrigin] at hk0nc
    | upper r' =>
        exfalso
        have hr' : r' = b := hk0src
        rw [hr'] at hE
        have := hupl (lol ++ usl)[k0] (List.getElem_mem hk0) b hE cb hcb
        rw [hbC] at this
        exact absurd hCτ (not_lt.mpr this)
    | plain r' =>
        exfalso
        have hr' : r' = b := hk0src
        rw [hr'] at hE
        rcases hlowl (lol ++ usl)[k0] (List.getElem_mem hk0) b hE cb hcb with
          ⟨q1, hq1, hq11, hq1in⟩ | hP
        · have hq1in' : inRegion q1.1 q1.2.source (official cs.row) = true := by
            rw [← hbC]; exact hq1in
          have := Recon.JumpLaw.lowerItems_eq_of_common hqx hq1 hqxin hq1in'
          rw [this] at hqx2
          omega
        · have hρ' : topIn M root.column 2 (official cb.row) = some (ρr, ρc) := by
            rw [hbC]; exact hρ
          have hρrow' : official ρc.row = official cb.row := by rw [hbC]; exact hρrow
          have hf : ascends (ctxAt M R l.column i root.column ((M.size - 1) - root.column) (M.size - 1)
              (l.column + ((M.size - 1) - root.column) * i)) (some (ρr, ρc)) = .ok false :=
            hP b hE cb hcb ρr ρc hρ' hρrow'
          rw [hascl] at hf
          cases hf
  -- the copy node of `b`
  let v2 : Ref := ⟨l.column + ((M.size - 1) - root.column) * i, k0 + 1⟩
  have hv2 : CopyAt M R n root.column (M.size - 1) (official t.row) i v2 (.clean b false) :=
    ⟨l.column, (lol ++ usl), k0, hlcr, by omega, hlmem, rfl, rfl, hesl, hk0, hclean⟩
  -- both copies keep the row `C`
  have hRR : ChainCorr.SRCmp.RootRow M root.column (official cs.row) :=
    ⟨(ρr, ρc), (topIn_spec hρ).1, hρrow⟩
  have hrowv : es[j].1.row = official cs.row := by
    have hee : es = loy ++ usy := Except.ok.inj (hes'.symm.trans hDy.emitsT)
    have hmemj : es[j] ∈ loy ++ usy := by rw [← hee]; exact List.getElem_mem hj
    have hcmp := Recon.TopChain.Seam.ecmp_of_colData hDy es[j] hmemj cs
      (by rw [ho]; exact hacell) (official cs.row) hRR
    rw [ho] at hcmp
    exact (hcmp.1 rfl).2.1 rfl
  have hrowv2 : (lol ++ usl)[k0].1.row = official cs.row := by
    have hcmp := Recon.TopChain.Seam.ecmp_of_colData hDl (lol ++ usl)[k0] (List.getElem_mem hk0) cb
      (by rw [hclean]; exact hcb) (official cs.row) hRR
    rw [hclean] at hcmp
    exact ((hcmp.1 rfl).2.1 hbC.symm)
  -- the cells in the output
  obtain ⟨y1, es1, j1, hj1, ho1, ⟨hvc1, hcy1, hyx1, _⟩, _, hvi1, hes1, cv, hcv, hcvrow, _⟩ :=
    copyAtX_cellD E hi0 hi hva
  obtain ⟨y2, es2, j2, hj2, ho2, ⟨hvc2, hcy2, hyx2, _⟩, _, hvi2, hes2, cv2, hcv2, hcv2row, _⟩ :=
    copyAtX_cellD E hi0 hi (copyAtX_of_copyAt hv2)
  have hy1 : y1 = y := by
    have := blockX_unique (x' := y) (i' := i) (by omega) hcy1 hyx1 hyb (by rw [← hvc1, hvc]) hi0
    exact this.2.symm
  subst hy1
  have he1 : es1 = es := by
    rw [hvc, hes'] at hes1
    exact (Except.ok.inj hes1).symm
  subst he1
  have hjj : j1 = j := by omega
  subst hjj
  have hy2 : y2 = l.column := by
    have := blockX_unique (x' := l.column) (i' := i) (by omega) hcy2 hyx2 hlmem (by rw [← hvc2]) hi0
    exact this.2.symm
  subst hy2
  have he2 : es2 = (lol ++ usl) := by
    have e : v2.column = l.column + ((M.size - 1) - root.column) * i := rfl
    rw [e, hesl] at hes2
    exact (Except.ok.inj hes2).symm
  subst he2
  have hkk : j2 = k0 := by simp [v2] at hvi2; omega
  subst hkk
  -- the raw parent of `v` is the node of `φ(l)` at the row of `v`
  obtain ⟨ca', l', cv', v1', c1, hca', hl', hcv', hraw', hc1, hrow1, hham⟩ :=
    cleanX_parent_rowD E hi0 hi hva
  have e1 : v1' = v1 := Option.some.inj (hraw'.symm.trans hraw)
  subst e1
  have e2 : cv' = cv := Option.some.inj (hcv'.symm.trans hcv)
  subst e2
  have e3 : ca' = cs := Option.some.inj (hca'.symm.trans hacell)
  subst e3
  have e4 : l' = l := Option.some.inj (hl'.symm.trans hl)
  subst e4
  have hv1col : v1'.column = l'.column + ((M.size - 1) - root.column) * i := by
    have := highestAtMost_column hham
    rw [this, mapColumn_of_ge (le_of_lt hlcr)]
  have hrows : c1.row = cv2.row := by
    rw [hrow1, hcvrow, hcv2row, hrowv, hrowv2]
  have hv1 : v1' = v2 := cell?_eq_of_index hVR (by rw [hv1col]) hc1 hcv2 hrows
  rw [hv1]
  exact hv2

/-- **One output step from a clean copy** (diagram form of `cleanStepX`). -/
theorem cleanStepXD {s : List Nat} {n : Nat} {M : Mountain} {R : Mountain} {t : Cell}
    {root : Ref} (E : CrossUpperSim.Env s n R M t root) {i : Nat} (hi0 : 0 < i) (hi : i < n + 1)
    {v a : Ref} (hva : CopyAtX M R n root.column (M.size - 1) (official t.row) i v (.clean a false)) :
    ∃ (b v1 : Ref) (cv c1 : Cell), GenStep M root.column a b ∧ root.column ≤ b.column ∧
      rawParent R v = some v1 ∧ cell? R v = some cv ∧ cell? R v1 = some c1 ∧ c1.row = cv.row ∧
      v1.column < v.column ∧
      (root.column < b.column → CopyAt M R n root.column (M.size - 1) (official t.row) i v1 (.clean b false)) ∧
      (b.column = root.column → v1.column = root.column + ((M.size - 1) - root.column) * i) := by
  have hVR := validR E.run
  obtain ⟨b, hab, hb⟩ := chainX_first_stepD E.top hva
  obtain ⟨ca, l, cv, v1, c1, hca, hl, hcv, hraw, hc1, hrow, hham⟩ := cleanX_parent_rowD E hi0 hi hva
  have hlt := (rawParent_cells hVR hraw).2.2
  have hab' := hab
  obtain ⟨_, _, ca', cb, l', hca', hl', hbl, _, _⟩ := hab'
  have e1 : ca' = ca := Option.some.inj (hca'.symm.trans hca)
  subst e1
  have e2 : l' = l := Option.some.inj (hl'.symm.trans hl)
  subst e2
  have hv1c : v1.column = mapColumn root.column (((M.size - 1) - root.column) * i) l'.column := highestAtMost_column hham
  refine ⟨b, v1, cv, c1, hab, hb, hraw, hcv, hc1, hrow, hlt,
    fun h => lookupInnerXD E hi0 hi hva hab h hraw, fun h => ?_⟩
  rw [hv1c, ← hbl, h, mapColumn_of_ge (le_refl _)]

/-- **The walk from a clean copy** (diagram form of `walkX`). -/
theorem walkXD {s : List Nat} {n : Nat} {M : Mountain} {R : Mountain} {t : Cell}
    {root : Ref} (E : CrossUpperSim.Env s n R M t root) {i : Nat} (hi0 : 0 < i) (hi : i < n + 1) :
    ∀ (x : Nat) (v a : Ref), a.column = x →
      CopyAtX M R n root.column (M.size - 1) (official t.row) i v (.clean a false) →
      ∃ cv, cell? R v = some cv ∧
        (∃ g, Relation.TransGen (GenStep M root.column) a g ∧ g.column = root.column) ∧
        ∀ g', Relation.ReflTransGen (GenStep M root.column) a g' → root.column ≤ g'.column ∧
          (root.column < g'.column → ∃ v', ScaleReach R 0 v v' ∧
            CopyAtX M R n root.column (M.size - 1) (official t.row) i v' (.clean g' false)) ∧
          (g'.column = root.column → ∃ (P : Ref) (cP : Cell), ScaleReach R 0 v P ∧
            P.column = root.column + ((M.size - 1) - root.column) * i ∧ cell? R P = some cP ∧ cP.row = cv.row) := by
  have hV := build_valid_of_success E.top.build
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
  intro v a hax hva
  obtain ⟨hacr, _, _⟩ := cleanX_src hva
  obtain ⟨b, v1, cv, c1, hab, hbcr, hraw, hcv, hc1, hrow, hlt, hin, hbd⟩ := cleanStepXD E hi0 hi hva
  have hstep : ScaleReach R 0 v v1 :=
    ScaleReach.step hraw hcv hc1 (by rw [hrow, Row.jump_self]) hlt (ScaleReach.refl v1)
  have hba : b.column < a.column := by
    obtain ⟨_, _, ca, cb, l, hca, hl, hbl, _, _⟩ := hab
    rw [hbl]; exact left_lt_of_valid hV hca hl
  -- the node `a` itself
  have hself : root.column ≤ a.column ∧
      (root.column < a.column → ∃ v', ScaleReach R 0 v v' ∧
        CopyAtX M R n root.column (M.size - 1) (official t.row) i v' (.clean a false)) ∧
      (a.column = root.column → ∃ (P : Ref) (cP : Cell), ScaleReach R 0 v P ∧
        P.column = root.column + ((M.size - 1) - root.column) * i ∧ cell? R P = some cP ∧ cP.row = cv.row) :=
    ⟨le_of_lt hacr, fun _ => ⟨v, ScaleReach.refl v, hva⟩, fun h => absurd h (by omega)⟩
  rcases Nat.lt_or_eq_of_le hbcr with hbgt | hbeq
  · -- the next generation is right of `c_r`: continue from its clean copy
    have hv1 := copyAtX_of_copyAt (hin hbgt)
    obtain ⟨cv1, hcv1, ⟨g, hbg, hgc⟩, hall⟩ := ih b.column (by omega) v1 b rfl hv1
    have e : cv1 = c1 := Option.some.inj (hcv1.symm.trans hc1)
    subst e
    refine ⟨cv, hcv, ⟨g, Relation.TransGen.head hab hbg, hgc⟩, fun g' hg' => ?_⟩
    rcases Relation.ReflTransGen.cases_head hg' with rfl | ⟨b', hab', hb'g'⟩
    · exact hself
    · have e2 : b' = b := GenStep.unique hV hab' hab
      subst e2
      obtain ⟨h1, h2, h3⟩ := hall g' hb'g'
      refine ⟨h1, fun h => ?_, fun h => ?_⟩
      · obtain ⟨v', hr, hc⟩ := h2 h
        exact ⟨v', ScaleReach.trans hstep hr, hc⟩
      · obtain ⟨P, cP, hr, hPc, hcP, hProw⟩ := h3 h
        exact ⟨P, cP, ScaleReach.trans hstep hr, hPc, hcP, by rw [hProw, hrow]⟩
  · -- the next generation is in the root column: `v₁` is the boundary node
    refine ⟨cv, hcv, ⟨b, Relation.TransGen.single hab, hbeq.symm⟩, fun g' hg' => ?_⟩
    rcases Relation.ReflTransGen.cases_head hg' with rfl | ⟨b', hab', hb'g'⟩
    · exact hself
    · have e2 : b' = b := GenStep.unique hV hab' hab
      subst e2
      have e3 := genChain_stop (le_of_eq hbeq.symm) hb'g'
      subst e3
      refine ⟨le_of_eq hbeq, fun h => absurd h (by omega), fun _ => ?_⟩
      exact ⟨v1, c1, hstep, hbd hbeq.symm, hc1, hrow⟩

open Geometry.Frame in
/-- **The step of `M(s)` from the origin of a clean copy** (`cleanParentReach` for every copied
column, with the top data in place of `Setting`). -/
theorem cleanParentReachD {s : List Nat} {M : Mountain} {t : Cell} {root : Ref}
    (hTop : Recon.Top s M t root) {n : Nat} {R : Mountain} {i : Nat} {v a : Ref}
    (hva : CopyAtX M R n root.column (M.size - 1) (official t.row) i v (.clean a false))
    {k : Nat} {m' : Ref} (hst : MStep M k a m') :
    Relation.TransGen (GenStep M root.column) a m' ∨
      ∃ g g1, Relation.TransGen (GenStep M root.column) a g ∧ g.column = root.column ∧
        MStep M k g g1 ∧ ScaleReach M k g1 m' := by
  have hva' := hva
  obtain ⟨y, es, j, hcy, hyx, hyb, hvc, hvi, hes, hj, ho⟩ := hva'
  have hes' : emitsT (ctxAt M R y i root.column ((M.size - 1) - root.column) (M.size - 1) (y + ((M.size - 1) - root.column) * i))
      (official t.row) = .ok es := by rw [← hvc]; exact hes
  obtain ⟨C, cs, hcs, ⟨ref, cl, hn, hr⟩, hroot⟩ :=
    emitsT_cleanRoot hes' es[j] (List.getElem_mem hj) a false ho
  simp only [ctxAt] at hcs hn hr hroot
  have hb := hTop.build
  have hN := build_normal_of_success hb
  have hO := hN.toOrdered
  obtain ⟨hac, ha1, hacell, harow⟩ := Classification.nodeAt_spec hcs
  simp only at hac ha1 hacell harow
  obtain ⟨na, hna, hnacell⟩ := ControlProof.node_of_cell? hacell
  have hareal : Frame.Real na := by
    show 0 < na.2.val
    have : na.2.val = a.index := by rw [← hna]; rfl
    omega
  have hst' := hst
  obtain ⟨hpar, cm, cm', hcm, hcm', hjk, hlt⟩ := hst'
  obtain ⟨nm', hPa, hnm'⟩ := P_of_rawParent hN hareal (hna ▸ hpar)
  obtain ⟨q0, hQ0, hit0⟩ := (P_iff hO).mp hPa
  by_cases h0 : 0 < C.coeff 0
  · -- `C₀ > 0`: the chain reaches the root column
    have hZC := Recon.RowLaw.referenceRow_bump h0
    obtain ⟨hrc, hr1, hrcell, hrrow⟩ := Classification.nodeAt_spec hn
    simp only at hrc hr1 hrcell hrrow
    obtain ⟨cu, hcu, hofu, g, hg, hgc⟩ :=
      chain_to_root hb hZC hroot (y + 1) ref cl hrcell hr1 hrrow (by rw [hrc]; exact hcy) hr
    -- the node above `ref` is `a`
    have hupa : up ref = a := by
      obtain ⟨hmem, _⟩ := Recon.RowLaw.nodeAt_spec hcs
      have hupmem : (up ref, cu) ∈ realNodes M y := by
        rw [mem_realNodes_iff]
        unfold cell? at hcu
        cases hcolr : M[ref.column]? with
        | none => simp [up, hcolr] at hcu
        | some colr =>
            simp only [up, hcolr, Option.bind_eq_bind, Option.bind_some] at hcu
            refine ⟨colr, ref.index, by rw [← hrc]; exact hcolr, hcu, ?_⟩
            simp [up, hrc]
      have := ChainCorr.realNodes_eq_of_official (build_valid_of_success hb) hupmem hmem
        (by simp only; rw [hofu, harow])
      exact congrArg Prod.fst this
    rw [hupa] at hg
    rcases walk hO hg na hna q0 nm' hQ0 hit0 with hon | ⟨ng, hng, hrej, q', hQ', hit'⟩
    · exact Or.inl (hnm' ▸ hon)
    · -- the search passes `g`: it continues along the numerical parents of `g`
      right
      have hgreal : Frame.Real ng := by
        have hgi : ∀ {x z : Ref}, Relation.TransGen (GenStep M root.column) x z → 1 ≤ z.index := by
          intro x z hxz
          induction hxz with
          | single h => exact h.2.1
          | tail _ h _ => exact h.2.1
        show 0 < ng.2.val
        have : ng.2.val = g.index := by rw [← hng]; rfl
        have := hgi hg
        omega
      have hvpos : 0 < (Frame.ofMountain M).value ng := hO.real_positive ng hgreal
      have hvge : (Frame.ofMountain M).value na ≤ (Frame.ofMountain M).value ng := by
        by_contra hn'
        exact hrej ⟨hvpos, lt_of_not_ge hn'⟩
      obtain ⟨va, hvaU⟩ := hN.upper_of_parent hPa
      have hva1 := hN.upper_nontrivial na va hareal hvaU
      obtain ⟨vg, hvg⟩ := hN.upper_exists ng hgreal (by omega)
      obtain ⟨pg, hPg, _, _, _⟩ := hN.upper_step ng vg hgreal hvg
      have hrawg := rawParent_of_P hN hgreal hPg
      rw [hng] at hrawg
      -- the rows
      obtain ⟨cg, hcg, hcgrow⟩ := chain_row hg cs hacell
      have hcgF : (Frame.ofMountain M).cell ng = cg := by
        have := ControlProof.cell?_ref ng
        rw [hng, hcg] at this
        exact (Option.some.inj this).symm
      have hcma : cm = cs := Option.some.inj (hcm.symm.trans hacell)
      subst hcma
      have hm'F : (Frame.ofMountain M).cell nm' = cm' := by
        have := ControlProof.cell?_ref nm'
        rw [hnm', hcm'] at this
        exact (Option.some.inj this).symm
      -- the search from the candidate of `g` with the threshold `v(a)` passes `P(g)`
      obtain ⟨r0, hwide, htail⟩ := hit'.loosen hvge
      have hPg' : (Frame.ofMountain M).P ng = some r0 := (P_iff hO).mpr ⟨q', hQ', hwide⟩
      have hr0 : r0 = pg := Option.some.inj (hPg'.symm.trans hPg)
      subst hr0
      have hpgpos := (P_value hO hPg).1
      have hpgreal : Frame.Real r0 := Frame.real_of_value_pos hO hpgpos
      have hchain := hit_pchain hO r0.1.val r0 nm' rfl hpgpos htail
      -- heights: `row m' ≤ row π(g) ≤ row g = C`
      have hpg_le : (Frame.ofMountain M).height r0 ≤ cm.row := by
        have := P_height_le hO hPg
        have e : (Frame.ofMountain M).height ng = cm.row := by
          show ((Frame.ofMountain M).cell ng).row = cm.row
          rw [hcgF, hcgrow]
        exact this.trans e.le
      have hm'_le : cm'.row ≤ (Frame.ofMountain M).height r0 := by
        have := pchain_height hO hchain
        have e : (Frame.ofMountain M).height nm' = cm'.row := by
          show ((Frame.ofMountain M).cell nm').row = cm'.row
          rw [hm'F]
        exact e.symm.le.trans this
      have hreach : ScaleReach M k (Frame.ref r0) (Frame.ref nm') :=
        pchain_reach hN hjk hchain hpgreal hpg_le (by
          show cm'.row ≤ ((Frame.ofMountain M).cell nm').row
          rw [hm'F])
      rw [hnm'] at hreach
      refine ⟨g, Frame.ref r0, hg, hgc, ⟨hrawg, cg, (Frame.ofMountain M).cell r0, hcg,
        ControlProof.cell?_ref r0, ?_, ?_⟩, hreach⟩
      · rw [hcgrow, Row.jump_comm]
        have hzw : Row.jump cm'.row cm.row ≤ k := by rw [Row.jump_comm]; exact hjk
        exact (Row.jump_le_between (d := k) hm'_le hpg_le hzw).2
      · have := P_column_lt hO hPg
        show r0.1.val < g.column
        rw [← hng]
        exact this
  · -- `C₀ = 0`: the raw parent of `a` is its in-row parent, on the chain
    left
    have hZ : referenceRow C = C := by
      unfold referenceRow
      rw [if_neg h0]
    rw [hZ, hcs] at hn
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hn)
    obtain ⟨q, hw, hqcr⟩ := ChainCorr.weakParent_of_reachesRoot (by rw [hac]; exact hcy) hr
    obtain ⟨col', cell, upper, parentCell, hcol, hcell, hup, hleft, hpc, hprow⟩ :=
      Recon.RowLaw.weakParent_some hw
    have hraw : Reserve.rawParent M a = some q := by
      simp only [Reserve.rawParent, hcol, Option.bind_eq_bind, Option.bind_some, hup, hleft]
    have hqm : q = m' := Option.some.inj (hraw.symm.trans hpar)
    subst hqm
    have hcellr : cell? M a = some cell := by simp [cell?, hcol, hcell]
    have hcc : cell = cs := Option.some.inj (hcellr.symm.trans hacell)
    subst hcc
    have hqc : cell? M q = some parentCell := by
      obtain ⟨column, h1, h2⟩ := cellAt_ok_iff.mp hpc
      simp [cell?, h1, h2]
    have hnm'cell : (Frame.ofMountain M).cell nm' = parentCell := by
      have := ControlProof.cell?_ref nm'
      rw [hnm', hqc] at this
      exact (Option.some.inj this).symm
    have hh : (Frame.ofMountain M).height nm' = (Frame.ofMountain M).height na := by
      show ((Frame.ofMountain M).cell nm').row = ((Frame.ofMountain M).cell na).row
      rw [hnm'cell, hnacell, hprow]
    have hc : root.column ≤ nm'.1.val := by
      have : nm'.1.val = q.column := by rw [← hnm']; rfl
      omega
    have := inrow_hit (cr := root.column) hO hit0 na hareal hQ0 hh hc
    rw [hna, hnm'] at this
    exact this

open Geometry.Frame in
/-- `cleanParentReachD` for a clean copy with any flag `b` (a gap copy included). -/
theorem cleanParentReachD' {s : List Nat} {M : Mountain} {t : Cell} {root : Ref}
    (hTop : Recon.Top s M t root) {n : Nat} {R : Mountain} {i : Nat} {v a : Ref} {bb : Bool}
    (hva : CopyAtX M R n root.column (M.size - 1) (official t.row) i v (.clean a bb))
    {k : Nat} {m' : Ref} (hst : MStep M k a m') :
    Relation.TransGen (GenStep M root.column) a m' ∨
      ∃ g g1, Relation.TransGen (GenStep M root.column) a g ∧ g.column = root.column ∧
        MStep M k g g1 ∧ ScaleReach M k g1 m' := by
  have hva' := hva
  obtain ⟨y, es, j, hcy, hyx, hyb, hvc, hvi, hes, hj, ho⟩ := hva'
  have hes' : emitsT (ctxAt M R y i root.column ((M.size - 1) - root.column) (M.size - 1) (y + ((M.size - 1) - root.column) * i))
      (official t.row) = .ok es := by rw [← hvc]; exact hes
  obtain ⟨C, cs, hcs, ⟨ref, cl, hn, hr⟩, hroot⟩ :=
    emitsT_cleanRoot hes' es[j] (List.getElem_mem hj) a bb ho
  simp only [ctxAt] at hcs hn hr hroot
  have hb := hTop.build
  have hN := build_normal_of_success hb
  have hO := hN.toOrdered
  obtain ⟨hac, ha1, hacell, harow⟩ := Classification.nodeAt_spec hcs
  simp only at hac ha1 hacell harow
  obtain ⟨na, hna, hnacell⟩ := ControlProof.node_of_cell? hacell
  have hareal : Frame.Real na := by
    show 0 < na.2.val
    have : na.2.val = a.index := by rw [← hna]; rfl
    omega
  have hst' := hst
  obtain ⟨hpar, cm, cm', hcm, hcm', hjk, hlt⟩ := hst'
  obtain ⟨nm', hPa, hnm'⟩ := P_of_rawParent hN hareal (hna ▸ hpar)
  obtain ⟨q0, hQ0, hit0⟩ := (P_iff hO).mp hPa
  by_cases h0 : 0 < C.coeff 0
  · -- `C₀ > 0`: the chain reaches the root column
    have hZC := Recon.RowLaw.referenceRow_bump h0
    obtain ⟨hrc, hr1, hrcell, hrrow⟩ := Classification.nodeAt_spec hn
    simp only at hrc hr1 hrcell hrrow
    obtain ⟨cu, hcu, hofu, g, hg, hgc⟩ :=
      chain_to_root hb hZC hroot (y + 1) ref cl hrcell hr1 hrrow (by rw [hrc]; exact hcy) hr
    -- the node above `ref` is `a`
    have hupa : up ref = a := by
      obtain ⟨hmem, _⟩ := Recon.RowLaw.nodeAt_spec hcs
      have hupmem : (up ref, cu) ∈ realNodes M y := by
        rw [mem_realNodes_iff]
        unfold cell? at hcu
        cases hcolr : M[ref.column]? with
        | none => simp [up, hcolr] at hcu
        | some colr =>
            simp only [up, hcolr, Option.bind_eq_bind, Option.bind_some] at hcu
            refine ⟨colr, ref.index, by rw [← hrc]; exact hcolr, hcu, ?_⟩
            simp [up, hrc]
      have := ChainCorr.realNodes_eq_of_official (build_valid_of_success hb) hupmem hmem
        (by simp only; rw [hofu, harow])
      exact congrArg Prod.fst this
    rw [hupa] at hg
    rcases walk hO hg na hna q0 nm' hQ0 hit0 with hon | ⟨ng, hng, hrej, q', hQ', hit'⟩
    · exact Or.inl (hnm' ▸ hon)
    · -- the search passes `g`: it continues along the numerical parents of `g`
      right
      have hgreal : Frame.Real ng := by
        have hgi : ∀ {x z : Ref}, Relation.TransGen (GenStep M root.column) x z → 1 ≤ z.index := by
          intro x z hxz
          induction hxz with
          | single h => exact h.2.1
          | tail _ h _ => exact h.2.1
        show 0 < ng.2.val
        have : ng.2.val = g.index := by rw [← hng]; rfl
        have := hgi hg
        omega
      have hvpos : 0 < (Frame.ofMountain M).value ng := hO.real_positive ng hgreal
      have hvge : (Frame.ofMountain M).value na ≤ (Frame.ofMountain M).value ng := by
        by_contra hn'
        exact hrej ⟨hvpos, lt_of_not_ge hn'⟩
      obtain ⟨va, hvaU⟩ := hN.upper_of_parent hPa
      have hva1 := hN.upper_nontrivial na va hareal hvaU
      obtain ⟨vg, hvg⟩ := hN.upper_exists ng hgreal (by omega)
      obtain ⟨pg, hPg, _, _, _⟩ := hN.upper_step ng vg hgreal hvg
      have hrawg := rawParent_of_P hN hgreal hPg
      rw [hng] at hrawg
      -- the rows
      obtain ⟨cg, hcg, hcgrow⟩ := chain_row hg cs hacell
      have hcgF : (Frame.ofMountain M).cell ng = cg := by
        have := ControlProof.cell?_ref ng
        rw [hng, hcg] at this
        exact (Option.some.inj this).symm
      have hcma : cm = cs := Option.some.inj (hcm.symm.trans hacell)
      subst hcma
      have hm'F : (Frame.ofMountain M).cell nm' = cm' := by
        have := ControlProof.cell?_ref nm'
        rw [hnm', hcm'] at this
        exact (Option.some.inj this).symm
      -- the search from the candidate of `g` with the threshold `v(a)` passes `P(g)`
      obtain ⟨r0, hwide, htail⟩ := hit'.loosen hvge
      have hPg' : (Frame.ofMountain M).P ng = some r0 := (P_iff hO).mpr ⟨q', hQ', hwide⟩
      have hr0 : r0 = pg := Option.some.inj (hPg'.symm.trans hPg)
      subst hr0
      have hpgpos := (P_value hO hPg).1
      have hpgreal : Frame.Real r0 := Frame.real_of_value_pos hO hpgpos
      have hchain := hit_pchain hO r0.1.val r0 nm' rfl hpgpos htail
      -- heights: `row m' ≤ row π(g) ≤ row g = C`
      have hpg_le : (Frame.ofMountain M).height r0 ≤ cm.row := by
        have := P_height_le hO hPg
        have e : (Frame.ofMountain M).height ng = cm.row := by
          show ((Frame.ofMountain M).cell ng).row = cm.row
          rw [hcgF, hcgrow]
        exact this.trans e.le
      have hm'_le : cm'.row ≤ (Frame.ofMountain M).height r0 := by
        have := pchain_height hO hchain
        have e : (Frame.ofMountain M).height nm' = cm'.row := by
          show ((Frame.ofMountain M).cell nm').row = cm'.row
          rw [hm'F]
        exact e.symm.le.trans this
      have hreach : ScaleReach M k (Frame.ref r0) (Frame.ref nm') :=
        pchain_reach hN hjk hchain hpgreal hpg_le (by
          show cm'.row ≤ ((Frame.ofMountain M).cell nm').row
          rw [hm'F])
      rw [hnm'] at hreach
      refine ⟨g, Frame.ref r0, hg, hgc, ⟨hrawg, cg, (Frame.ofMountain M).cell r0, hcg,
        ControlProof.cell?_ref r0, ?_, ?_⟩, hreach⟩
      · rw [hcgrow, Row.jump_comm]
        have hzw : Row.jump cm'.row cm.row ≤ k := by rw [Row.jump_comm]; exact hjk
        exact (Row.jump_le_between (d := k) hm'_le hpg_le hzw).2
      · have := P_column_lt hO hPg
        show r0.1.val < g.column
        rw [← hng]
        exact this
  · -- `C₀ = 0`: the raw parent of `a` is its in-row parent, on the chain
    left
    have hZ : referenceRow C = C := by
      unfold referenceRow
      rw [if_neg h0]
    rw [hZ, hcs] at hn
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hn)
    obtain ⟨q, hw, hqcr⟩ := ChainCorr.weakParent_of_reachesRoot (by rw [hac]; exact hcy) hr
    obtain ⟨col', cell, upper, parentCell, hcol, hcell, hup, hleft, hpc, hprow⟩ :=
      Recon.RowLaw.weakParent_some hw
    have hraw : Reserve.rawParent M a = some q := by
      simp only [Reserve.rawParent, hcol, Option.bind_eq_bind, Option.bind_some, hup, hleft]
    have hqm : q = m' := Option.some.inj (hraw.symm.trans hpar)
    subst hqm
    have hcellr : cell? M a = some cell := by simp [cell?, hcol, hcell]
    have hcc : cell = cs := Option.some.inj (hcellr.symm.trans hacell)
    subst hcc
    have hqc : cell? M q = some parentCell := by
      obtain ⟨column, h1, h2⟩ := cellAt_ok_iff.mp hpc
      simp [cell?, h1, h2]
    have hnm'cell : (Frame.ofMountain M).cell nm' = parentCell := by
      have := ControlProof.cell?_ref nm'
      rw [hnm', hqc] at this
      exact (Option.some.inj this).symm
    have hh : (Frame.ofMountain M).height nm' = (Frame.ofMountain M).height na := by
      show ((Frame.ofMountain M).cell nm').row = ((Frame.ofMountain M).cell na).row
      rw [hnm'cell, hnacell, hprow]
    have hc : root.column ≤ nm'.1.val := by
      have : nm'.1.val = q.column := by rw [← hnm']; rfl
      omega
    have := inrow_hit (cr := root.column) hO hit0 na hareal hQ0 hh hc
    rw [hna, hnm'] at this
    exact this

end OmegaY.Official.Classification.Proofs.ChainCorr.NonTop.SeamD
