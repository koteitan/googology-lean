/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/PBStageBRoot.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.PBStageBMain
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.PBStageBBoundaryFalse
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.PBStageBCutLegMain

set_option backward.do.legacy false

/-!
# `LowerParentBelowHolds` without `Boundary` (stage B)

`Boundary` is false for the root column `0` (`PBStageBBoundaryFalse.lean`), so the reduction of
`PBStageBMain.lean` (`lowerParentBelowHolds_of_cutLeg_boundary`) has a false hypothesis. `Boundary`
is used only when the leg column of the copied node is the root column `c_r` itself: then the
parent column is the boundary column `B = c_r + w·i` of the output. This file replaces that use by
one statement about the output (`RootShadowOut`, new; proved in `PBStageBBndSim.lean`):

* `RootShadowOut`: in a new column `X` of a block `i ≥ 1`, let `e` be an emitted node whose leg
  column is `c_r` (the left end of its origin is in the root column). Every row below `τ` of the
  boundary column `B` that is below `e` is the row of a lower copy of `X`.

With it, `LowerParentBelowHolds` follows from `CutLeg` and `RootShadowOut`
(`lowerParentBelowHolds_of_rootShadow`), hence from `GenLeg` and `RootShadowOut`
(`lowerParentBelowHolds_of_genLeg`). For `c_r ≥ 1`, `RootShadowOut` follows from `CutLeg` and the
positive-root form `BoundaryPos` of `Boundary` (`rootShadowOut_of_boundaryPos`); the case `c_r = 0`
is `RootShadowZero`. All three are proved: `genLeg` (`PBStageBGenLeg.lean`), `rootShadowZero`
(`PBStageBRootZero.lean`), `boundaryPos` (`PBStageBBndSim.lean`).

## Numerical evidence

`RootShadowOut` (scratch harness `rootshadow.cjs`, same rule as `omegay-trace.cjs`): every emitted
node `e` of a block `i ≥ 1` with leg column `c_r` (plain, clean, gap and upper copies), every node
of `B` below `τ` and below `e`: all legal inputs of length `≤ 5` with entries `≤ 9`, `n = 1,2,3`
(outputs of at most 600 nodes): 3.2 million checks, no failure (1.0 million with `c_r = 0`).
-/

namespace OmegaY.Official.Recon.LowerPB.StageB

open Canonical Expansion Geometry Frame Classification Reserve
open Classification.Proofs Classification.Proofs.CopyShape.ProfileLeg

variable {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}
  {X i x : Nat} {lo us : List (Emit × Origin)}

/-- (new; proved: `rootShadowOut`, `PBStageBBndSim.lean`) **The boundary column below a copy
whose leg is the root column.** -/
def RootShadowOut : Prop :=
  ∀ (s : List Nat) (n : Nat) (R M : Mountain) (t : Cell) (root : Ref) (X i x : Nat)
    (lo us : List (Emit × Origin)), ColData s n R M t root X i x lo us → 1 ≤ i →
    ∀ e ∈ lo ++ us, e.1.leftColumn = some root.column →
      ∀ (q : Nat), q = root.column + (M.size - 1 - root.column) * i → ∀ (hqR : q < R.size)
        (kz : Nat) (hkz : kz < (R[q]'hqR).size), 1 ≤ kz →
        official ((R[q]'hqR)[kz]'hkz).row < official t.row →
        official ((R[q]'hqR)[kz]'hkz).row < e.1.row →
        ∃ f ∈ lo, f.1.row = official ((R[q]'hqR)[kz]'hkz).row

/-- (new; proved: `rootShadowZero`, `PBStageBRootZero.lean`) `RootShadowOut` for the root
column `0`. -/
def RootShadowZero : Prop :=
  ∀ (s : List Nat) (n : Nat) (R M : Mountain) (t : Cell) (root : Ref) (X i x : Nat)
    (lo us : List (Emit × Origin)), ColData s n R M t root X i x lo us → 1 ≤ i →
    root.column = 0 →
    ∀ e ∈ lo ++ us, e.1.leftColumn = some root.column →
      ∀ (q : Nat), q = root.column + (M.size - 1 - root.column) * i → ∀ (hqR : q < R.size)
        (kz : Nat) (hkz : kz < (R[q]'hqR).size), 1 ≤ kz →
        official ((R[q]'hqR)[kz]'hkz).row < official t.row →
        official ((R[q]'hqR)[kz]'hkz).row < e.1.row →
        ∃ f ∈ lo, f.1.row = official ((R[q]'hqR)[kz]'hkz).row

/-- (new; proved: `boundaryPos`, `PBStageBBndSim.lean`) `Boundary` for a root column `c_r ≥ 1`
(`Boundary` itself is false for `c_r = 0`, `PBStageBBoundaryFalse.lean`). -/
def BoundaryPos : Prop :=
  ∀ s n R, Official.expandDiagram s n = .ok R → ∀ M t root, Top s M t root → 1 ≤ root.column →
    ∀ i, 1 ≤ i → i ≤ n →
      ∃ es, lowerT ⟨M, R, root.column, i, root.column, M.size - 1 - root.column, M.size - 1⟩
          (official t.row) = .ok es ∧
        ∀ (hB : root.column + (M.size - 1 - root.column) * i < R.size) k
          (hk : k < R[root.column + (M.size - 1 - root.column) * i].size), 1 ≤ k →
          official R[root.column + (M.size - 1 - root.column) * i][k].row < official t.row →
          ∃ e ∈ es, e.1.row = official R[root.column + (M.size - 1 - root.column) * i][k].row

theorem boundaryPos_of_boundary (h : Boundary) : BoundaryPos :=
  fun s n R hrun M t root hTop _ i hi1 hin => h s n R hrun M t root hTop i hi1 hin

/-- `legRows` for a leg column right of `c_r` (no hypothesis). -/
theorem legRowsGt {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell}
    {root : Ref} (hrun : Official.expandDiagram s n = .ok R) (hTop : Top s M t root)
    (hCI : ColumnsInv M n root.column (M.size - 1 - root.column) (M.size - 1)
      (official t.row) R)
    (hI : Inv M (M.size - 1) R) {i ℓ : Nat} (hi1 : 1 ≤ i)
    (hgt : root.column < ℓ) (hℓ2 : ℓ < M.size - 1)
    (hq : ℓ + (M.size - 1 - root.column) * i < R.size) {kz : Nat}
    (hkz : kz < R[ℓ + (M.size - 1 - root.column) * i].size) (hkz1 : 1 ≤ kz)
    (hlt : official R[ℓ + (M.size - 1 - root.column) * i][kz].row < official t.row) :
    ∃ ctx' es' e', BCtx M R root.column (M.size - 1) i ctx' ∧ ctx'.x = ℓ ∧
      lowerT ctx' (official t.row) = .ok es' ∧ e' ∈ es' ∧
      e'.1.row = official R[ℓ + (M.size - 1 - root.column) * i][kz].row := by
  obtain ⟨i', y, lo, us, hD, _, hyi⟩ := legView hrun hTop hCI hI hi1 (le_of_lt hgt) hℓ2 hq
  obtain ⟨hy, hi'⟩ := hyi hgt
  subst hy
  subst hi'
  obtain ⟨hk', hrow, _⟩ := hD.node hkz hkz1
  have hrow' : official R[y + (M.size - 1 - root.column) * i'][kz].row =
      (lo ++ us)[kz - 1].1.row := by
    rw [hrow, official_stored']
  have hlo : kz - 1 < lo.length := by
    by_contra hn
    have hmem : (lo ++ us)[kz - 1] ∈ us := by
      rw [List.getElem_append_right (by omega)]
      exact List.getElem_mem _
    have := hD.us_ge _ hmem
    rw [← hrow'] at this
    exact absurd hlt (not_lt.mpr this)
  refine ⟨_, lo, (lo ++ us)[kz - 1], hD.bctx, rfl, hD.hlo, ?_, hrow'.symm⟩
  rw [List.getElem_append_left hlo]
  exact List.getElem_mem _

/-- **The copy of `u⁺` is a lower copy.** -/
theorem caseLowerR (hCL : CutLeg) (hRS : RootShadowOut) (hD : ColData s n R M t root X i x lo us)
    {eu : Emit × Origin} (heu : eu ∈ lo) {q kz : Nat} (hqR : q < R.size)
    (hkz : kz < (R[q]'hqR).size) (hkz1 : 1 ≤ kz)
    (hq : q = legColumn (ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1) X)
      eu.1)
    (hlt : official ((R[q]'hqR)[kz]'hkz).row < eu.1.row)
    (hkey : ∀ e ∈ lo, official ((R[q]'hqR)[kz]'hkz).row ≤ e.1.row → e.1.row < eu.1.row →
      False) : False := by
  have hVM := build_valid_of_success hD.top.build
  have hcr := hD.top.lt
  have hxg := hD.xgt
  have hxl := hD.xle
  obtain ⟨k, co, hsrc, hk, hco, hleft⟩ := lowerT_src hD.hlo heu
  change cell? M ⟨x, k⟩ = some co at hco
  have hpos : eu.1.row ≠ 0 := ne_of_gt (lt_of_le_of_lt (Row.zero_le _) hlt)
  obtain ⟨l, hl, hlc⟩ : ∃ l : Ref, co.left = some l ∧ eu.1.leftColumn = some l.column := by
    rcases hleft with h | ⟨hn, _⟩
    · exact h
    · exact absurd (assemble_none_row hD.asm eu.1
        (List.mem_map.mpr ⟨eu, List.mem_append_left _ heu, rfl⟩) hn) hpos
  have hlx : l.column < x := left_lt hVM hco hl
  have hqv := legColumn_eq M R x i root.column (M.size - 1 - root.column) (M.size - 1) X hlc
  rw [hqv] at hq
  have hcoe : cell? M eu.2.src = some co := by rw [hsrc]; exact hco
  rcases Nat.eq_zero_or_pos i with hi | hi1
  · -- block `0`: the identity
    have hx0 := block0_x hD hi
    have hql : q = l.column := by
      rw [hq, hi]
      split <;> simp
    subst hql
    have hcz := origCell hD.inv (by omega) hqR hkz
    have hrow := hD.block0_row hi heu hcoe
    have hwlt : ((R[l.column]'hqR)[kz]'hkz).row < co.row :=
      row_lt_of_official (cell_row_one_le hVM hco hk) (by rw [hrow]; exact hlt)
    obtain ⟨k'', cv, hk'', hcv, hrv⟩ := shadow hD.top.build hk hco hl hkz1 hcz (le_of_lt hwlt)
    have hτ : official cv.row < official t.row := by
      rw [hrv]; exact lt_trans hlt (hD.lo_lt eu heu)
    obtain ⟨f, hf, hfsrc⟩ := hD.emitted0 hi hk'' hcv hτ
    have hfc : cell? M f.2.src = some cv := by rw [hfsrc]; exact hcv
    have hfrow := hD.block0_row hi hf hfc
    exact hkey f hf (le_of_eq (by rw [← hfrow, hrv])) (by rw [← hfrow, hrv]; exact hlt)
  · by_cases hlr : root.column ≤ l.column
    · -- `ℓ ≥ c_r`: the copy of `ℓ` in block `i`
      have hql : q = l.column + (M.size - 1 - root.column) * i := by
        rw [hq, if_pos hlr]
      subst hql
      rcases eq_or_lt_of_le hlr with hre | hgt
      · have hlc' : eu.1.leftColumn = some root.column := by rw [hlc, hre]
        obtain ⟨f, hf, hfr⟩ := hRS s n R M t root X i x lo us hD hi1 eu
          (List.mem_append_left _ heu) hlc' _ (by rw [hre]) hqR kz hkz hkz1
          (lt_trans hlt (hD.lo_lt eu heu)) hlt
        exact hkey f hf (le_of_eq hfr.symm) (by rw [hfr]; exact hlt)
      obtain ⟨ctx', es', e', hB', hx', hes', he', hrow'⟩ := legRowsGt hD.run hD.top hD.ci
        hD.inv hi1 hgt (by omega) hqR hkz hkz1 (lt_trans hlt (hD.lo_lt eu heu))
      obtain ⟨c', hc', _⟩ := lowerT_below hes' e' he'
      rw [hB'.source] at hc'
      have hle := legOrderLeg nonCutOrderLeg cutBetweenLeg CopyShape.PBStageB.cutOrder hD.run
        hD.top hi1 hD.iln hD.bctx hB' hxg hD.hlo hes' heu hk hsrc hco hl hx'.symm he' hc'
        (by rw [hrow']; exact hlt)
      obtain ⟨e, he, hrow⟩ := sameRowLeg nonCutOrderLeg hCL hD.run hD.top hi1 hD.iln hD.bctx hB'
        hxg hk hco hl hx'.symm hD.hlo hes' he' hc' hle
      have her := hrow.trans hrow'
      exact hkey e he (le_of_eq her.symm) (by rw [her]; exact hlt)
    · -- `ℓ < c_r`: the column `q = ℓ` of `M(s)`; the copy keeps the row of its origin
      have hlr' : l.column < root.column := lt_of_not_ge hlr
      have hql : q = l.column := by rw [hq, if_neg hlr]
      subst hql
      obtain ⟨hcut, heur⟩ := legLeft_plain hD hi1 heu hsrc hco hl hlr'
      have hcz := origCell hD.inv (by omega) hqR hkz
      have hwlt : ((R[l.column]'hqR)[kz]'hkz).row < co.row :=
        row_lt_of_official (cell_row_one_le hVM hco hk) (by rw [← heur]; exact hlt)
      obtain ⟨k'', cv, hk'', hcv, hrv⟩ := shadow hD.top.build hk hco hl hkz1 hcz (le_of_lt hwlt)
      have hτ : official cv.row < official t.row := by
        rw [hrv]; exact lt_trans hlt (hD.lo_lt eu heu)
      obtain ⟨f, hf, hfcut, hfsrc⟩ := CopyShape.Found.emitted s n R hD.run M t root hD.top i hi1
        hD.iln _ hD.bctx hxg lo hD.hlo k'' cv hk'' hcv hτ
      have hfc : cell? M f.2.src = some cv := by rw [hfsrc]; exact hcv
      have hfl := CopyShape.PBStageB.lift s n R hD.run M t root hD.top i hi1 hD.iln _ hD.bctx lo
        hD.hlo f hf hfcut cv hfc
      have hflt := CopyShape.PBStageB.sameCol_lt hD.run hD.top hi1 hD.iln hD.bctx hD.hlo hf heu
        hfcut hcut hfc hcoe (by rw [hrv]; exact hwlt)
      rw [hrv] at hfl
      exact hkey f hf hfl hflt

/-- **The copy of `u⁺` is an upper copy.** -/
theorem caseUpperR (hCL : CutLeg) (hRS : RootShadowOut) (hD : ColData s n R M t root X i x lo us)
    {eu : Emit × Origin} (heu : eu ∈ us) {q kz : Nat} (hqR : q < R.size)
    (hkz : kz < (R[q]'hqR).size) (hkz1 : 1 ≤ kz)
    (hq : q = legColumn (ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1) X)
      eu.1)
    (hlt : official ((R[q]'hqR)[kz]'hkz).row < eu.1.row)
    (hkey : ∀ e ∈ lo ++ us, official ((R[q]'hqR)[kz]'hkz).row ≤ e.1.row →
      e.1.row < eu.1.row → False) : False := by
  have hVM := build_valid_of_success hD.top.build
  have hcr := hD.top.lt
  have hxg := hD.xgt
  have hxl := hD.xle
  have ht1 := hD.top.row_one_le
  obtain ⟨k, c, hk, hc, _, hrow, hτc, l, hl, hlc⟩ := (upperT_spec hD.hus).1 eu heu
  rw [upperColumn_ctxAt] at hc
  have hlx : l.column < if x = M.size - 1 then root.column else x := left_lt hVM hc hl
  have hqv := legColumn_eq M R x i root.column (M.size - 1 - root.column) (M.size - 1) X hlc
  rw [hqv] at hq
  have hc1 := cell_row_one_le hVM hc hk
  have hwlt : ∀ cw : Cell, official cw.row = official ((R[q]'hqR)[kz]'hkz).row →
      cw.row < c.row := fun cw hcw =>
    row_lt_of_official hc1 (by rw [hcw, ← hrow]; exact hlt)
  have hright : root.column ≤ l.column → x ≠ M.size - 1 ∧ 1 ≤ i := by
    intro hlr
    have hxx : x ≠ M.size - 1 := by
      intro he
      rw [if_pos he] at hlx
      omega
    refine ⟨hxx, ?_⟩
    rcases Nat.eq_zero_or_pos i with hi | hi
    · exact absurd (block0_x hD hi) hxx
    · exact hi
  by_cases hge : official t.row ≤ official ((R[q]'hqR)[kz]'hkz).row
  · have hw : ∃ kw cw, 1 ≤ kw ∧ cell? M ⟨l.column, kw⟩ = some cw ∧
        official cw.row = official ((R[q]'hqR)[kz]'hkz).row := by
      by_cases hlr : root.column ≤ l.column
      · obtain ⟨hxx, hi1⟩ := hright hlr
        rw [if_neg hxx] at hlx
        have hql : q = l.column + (M.size - 1 - root.column) * i := by rw [hq, if_pos hlr]
        subst hql
        exact legUpper hD.run hD.top hD.ci hD.inv hi1 hlr (by omega) hqR hkz hkz1 hge
      · have hql : q = l.column := by rw [hq, if_neg hlr]
        subst hql
        exact ⟨kz, _, hkz1, origCell hD.inv (by omega) hqR hkz, rfl⟩
    obtain ⟨kw, cw, hkw, hcw, hrw⟩ := hw
    obtain ⟨k'', cv, hk'', hcv, hrv⟩ :=
      shadow hD.top.build hk hc hl hkw hcw (le_of_lt (hwlt cw hrw))
    have hcv' : cell? M ⟨upperColumn (ctxAt M R x i root.column (M.size - 1 - root.column)
        (M.size - 1) X), k''⟩ = some cv := by rw [upperColumn_ctxAt]; exact hcv
    obtain ⟨e, he, her⟩ := (upperT_spec hD.hus).2 k'' cv hk'' hcv' (by rw [hrv, hrw]; exact hge)
    have her' : e.1.row = official ((R[q]'hqR)[kz]'hkz).row := by rw [her, hrv, hrw]
    exact hkey e (List.mem_append_right _ he) (le_of_eq her'.symm) (by rw [her']; exact hlt)
  · have hlτ := lt_of_not_ge hge
    by_cases hlr : root.column ≤ l.column
    · obtain ⟨hxx, hi1⟩ := hright hlr
      rw [if_neg hxx] at hlx hc
      have hql : q = l.column + (M.size - 1 - root.column) * i := by rw [hq, if_pos hlr]
      subst hql
      rcases eq_or_lt_of_le hlr with hre | hgt
      · have hlc' : eu.1.leftColumn = some root.column := by rw [hlc, hre]
        obtain ⟨f, hf, hfr⟩ := hRS s n R M t root X i x lo us hD hi1 eu
          (List.mem_append_right _ heu) hlc' _ (by rw [hre]) hqR kz hkz hkz1 hlτ hlt
        exact hkey f (List.mem_append_left _ hf) (le_of_eq hfr.symm) (by rw [hfr]; exact hlt)
      obtain ⟨ctx', es', e', hB', hx', hes', he', hrow'⟩ := legRowsGt hD.run hD.top hD.ci
        hD.inv hi1 hgt (by omega) hqR hkz hkz1 hlτ
      obtain ⟨c', hc', hc'τ⟩ := lowerT_below hes' e' he'
      rw [hB'.source] at hc'
      have hcc : c'.row < c.row := row_lt_of_official hc1 (lt_of_lt_of_le hc'τ hτc)
      obtain ⟨e, he, her⟩ := sameRowLeg nonCutOrderLeg hCL hD.run hD.top hi1 hD.iln hD.bctx hB'
        hxg hk hc hl hx'.symm hD.hlo hes' he' hc' (Or.inl hcc)
      have her' := her.trans hrow'
      exact hkey e (List.mem_append_left _ he) (le_of_eq her'.symm) (by rw [her']; exact hlt)
    · have hql : q = l.column := by rw [hq, if_neg hlr]
      subst hql
      have hcz := origCell hD.inv (by omega) hqR hkz
      obtain ⟨k'', cv, hk'', hcv, hrv⟩ :=
        shadow hD.top.build hk hc hl hkz1 hcz (le_of_lt (hwlt _ rfl))
      have hcvτ : official cv.row < official t.row := by rw [hrv]; exact hlτ
      have hv : ∃ k3 cv3, 1 ≤ k3 ∧ cell? M ⟨x, k3⟩ = some cv3 ∧ cv3.row = cv.row := by
        by_cases hxx : x = M.size - 1
        · rw [if_pos hxx] at hcv
          obtain ⟨v, hv, hvr⟩ := hD.top.root_rows (mem_realNodes_of_cell hcv hk'')
            (row_lt_of_official ht1 hcvτ)
          obtain ⟨hv1, hv2, hv3⟩ := Classification.mem_realNodes hv
          refine ⟨v.1.index, v.2, hv2, ?_, hvr⟩
          rw [hxx, ← hv1]
          exact hv3
        · rw [if_neg hxx] at hcv
          exact ⟨k'', cv, hk'', hcv, rfl⟩
      obtain ⟨k3, cv3, hk3, hcv3, hr3⟩ := hv
      obtain ⟨f, hf, _, hfl⟩ := emittedLiftB hD hk3 hcv3 (by rw [hr3]; exact hcvτ)
      rw [hr3, hrv] at hfl
      exact hkey f (List.mem_append_left _ hf) hfl
        (lt_of_lt_of_le (hD.lo_lt f hf) (by rw [hrow]; exact hτc))

/-- **The gap at one pair of consecutive nodes.** -/
theorem gapAtR (hCL : CutLeg) (hRS : RootShadowOut) (hD : ColData s n R M t root X i x lo us)
    {a : Nat} (ha1 : 1 ≤ a) (ha : a + 1 < (R[X]'hD.XR).size)
    (hτ : ((R[X]'hD.XR)[a]'(by omega)).row < t.row)
    {ref : Ref} (hleft : ((R[X]'hD.XR)[a + 1]'ha).left = some ref) (hqR : ref.column < R.size)
    {kz : Nat} (hkz : kz < (R[ref.column]'hqR).size)
    (hz1 : ((R[X]'hD.XR)[a]'(by omega)).row < ((R[ref.column]'hqR)[kz]'hkz).row)
    (hz2 : ((R[ref.column]'hqR)[kz]'hkz).row < ((R[X]'hD.XR)[a + 1]'ha).row) : False := by
  obtain ⟨_, _, _, _, hB⟩ := run_basic hD.run
  have ht1 := hD.top.row_one_le
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  have hkz1 : 1 ≤ kz := by
    by_contra h0
    have h0' : kz = 0 := by omega
    subst h0'
    have hph := (hB.valid ref.column hqR).phantom
    rw [Array.getElem?_eq_getElem hkz] at hph
    have hz0 : ((R[ref.column]'hqR)[0]'hkz).row = 0 := by rw [Option.some.inj hph]; rfl
    rw [hz0] at hz1
    exact absurd hz1 (not_lt.mpr (Row.zero_le _))
  have hzpos : (1 : Row) ≤ ((R[ref.column]'hqR)[kz]'hkz).row :=
    row_one_le_of_ne_zero (ne_of_gt (lt_of_le_of_lt (Row.zero_le _) hz1))
  obtain ⟨hka, hra, _⟩ := hD.node (k := a' + 1) (by omega) (by omega)
  obtain ⟨hka1, hra1, ref', hl', hrc'⟩ := hD.node (k := a' + 1 + 1) ha (by omega)
  simp only [Nat.add_sub_cancel] at hra hra1 hrc' hka hka1
  have href : ref' = ref := Option.some.inj (hl'.symm.trans hleft)
  subst href
  rw [hra] at hz1 hτ
  rw [hra1] at hz2
  have h1 : (lo ++ us)[a'].1.row < official ((R[ref'.column]'hqR)[kz]'hkz).row :=
    official_lt_of_stored_lt hz1 hzpos
  have h2 : official ((R[ref'.column]'hqR)[kz]'hkz).row < (lo ++ us)[a' + 1].1.row :=
    lt_official_of_lt_stored hz2 hzpos
  have hτ' : (lo ++ us)[a'].1.row < official t.row := official_lt_of_stored_lt hτ ht1
  have hkey : ∀ e ∈ lo ++ us, official ((R[ref'.column]'hqR)[kz]'hkz).row ≤ e.1.row →
      e.1.row < (lo ++ us)[a' + 1].1.row → False := by
    intro e he hle hlt
    have hmem : e.1 ∈ (lo ++ us).map Prod.fst := List.mem_map.mpr ⟨e, he, rfl⟩
    have hle' := JumpLaw.le_of_consecutive hD.sorted (k := a') (by simpa using hka1) hmem
      (by rw [List.getElem_map]; exact hlt)
    simp only [List.getElem_map] at hle'
    exact absurd (lt_of_lt_of_le h1 (hle.trans hle')) (lt_irrefl _)
  have hua : a' < lo.length := by
    by_contra hn
    have hmem : (lo ++ us)[a'] ∈ us := by
      rw [List.getElem_append_right (by omega)]
      exact List.getElem_mem _
    exact absurd (hD.us_ge _ hmem) (not_le.mpr hτ')
  by_cases hlow : a' + 1 < lo.length
  · have hmem : (lo ++ us)[a' + 1] ∈ lo := by
      rw [List.getElem_append_left hlow]
      exact List.getElem_mem _
    exact caseLowerR hCL hRS hD hmem hqR hkz hkz1 hrc' h2
      (fun e he hle hlt => hkey e (List.mem_append_left _ he) hle hlt)
  · have hmem : (lo ++ us)[a' + 1] ∈ us := by
      rw [List.getElem_append_right (by omega)]
      exact List.getElem_mem _
    exact caseUpperR hCL hRS hD hmem hqR hkz hkz1 hrc' h2 hkey

/-- **`LowerParentBelowHolds` from `CutLeg` and `RootShadowOut`.** -/
theorem lowerParentBelowHolds_of_rootShadow (hCL : CutLeg) (hRS : RootShadowOut) :
    LowerParentBelowHolds := by
  intro s n R hrun M col t hM hcol ht u p up hx hu hraw hUp hlt _
  obtain ⟨M1, col1, t1, root, hM1, hcol1, ht1', hTop, hCI, hI⟩ := run_new_column hrun u.1.isLt hx
  have hMM : M = M1 := Except.ok.inj (hM.symm.trans hM1)
  subst hMM
  have hcc : col = col1 := Option.some.inj (hcol.symm.trans hcol1)
  subst hcc
  have htt : t = t1 := Option.some.inj (ht.symm.trans ht1')
  subst htt
  have hMs := Canonical.build_size hM
  obtain ⟨up', hUp', hLeft⟩ := rawParent_spec hraw
  have hee : up' = up := Option.some.inj (hUp'.symm.trans hUp)
  subst hee
  obtain ⟨hc1, hc2⟩ := upper_spec hUp
  refine parentBelow_of_gap hrun hx hu hraw hUp ?_
  intro z hz hzu
  by_contra hzup
  have hzup' := lt_of_not_ge hzup
  obtain ⟨i, x, lo, us, hD⟩ := colData hrun hTop hCI hI u.1.isLt (by omega)
  obtain ⟨uc, ui⟩ := u
  obtain ⟨vc, vi⟩ := up'
  obtain ⟨pc, pi⟩ := p
  obtain ⟨zc, zi⟩ := z
  simp only at hc1 hc2 hz hx
  subst vc
  subst hz
  have hu1 : 1 ≤ ui.val := hu
  have ha : ui.val + 1 < (R[uc.val]'hD.XR).size := by
    have := vi.isLt
    change vi.val < R[uc.val].size at this
    omega
  have hvi : vi = ⟨ui.val + 1, ha⟩ := Fin.ext hc2
  subst hvi
  exact gapAtR hCL hRS hD hu1 ha hlt hLeft zc.isLt zi.isLt hzu hzup'

/-- **`ParentBelowHolds` from `CutLeg` and `RootShadowOut`.** -/
theorem parentBelowHolds_of_rootShadow (hCL : CutLeg) (hRS : RootShadowOut) :
    ParentBelowHolds :=
  parentBelowHolds_of_lower (lowerParentBelowHolds_of_rootShadow hCL hRS)


/-- **`LowerParentBelowHolds` from `GenLeg` and `RootShadowOut`.** -/
theorem lowerParentBelowHolds_of_genLeg (hG : CopyShape.PBStageB.GenLeg)
    (hRS : RootShadowOut) : LowerParentBelowHolds :=
  lowerParentBelowHolds_of_rootShadow (CopyShape.PBStageB.cutLeg_of_genLeg hG) hRS

/-- **`ParentBelowHolds` from `GenLeg` and `RootShadowOut`.** -/
theorem parentBelowHolds_of_genLeg (hG : CopyShape.PBStageB.GenLeg) (hRS : RootShadowOut) :
    ParentBelowHolds :=
  parentBelowHolds_of_lower (lowerParentBelowHolds_of_genLeg hG hRS)

end OmegaY.Official.Recon.LowerPB.StageB

#print axioms OmegaY.Official.Recon.LowerPB.StageB.lowerParentBelowHolds_of_rootShadow
#print axioms OmegaY.Official.Recon.LowerPB.StageB.lowerParentBelowHolds_of_genLeg
#print axioms OmegaY.Official.Recon.LowerPB.StageB.parentBelowHolds_of_genLeg
