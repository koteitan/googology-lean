/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/SeamLookup.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.SeamReduce
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.StartRootFixCmp
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.CutPredBoundary

set_option backward.do.legacy false

set_option autoImplicit false

/-!
# The lookups of the seam (`StepRootLookup`, `StartRootLookup`)

The argument of `SRFixPa.paLookup`, for the diagram of a run: the copies keep their place among
the rows of the root column (`SRCmp.emitsT_cmp`, with (MD) for the contexts of a block,
`CopyShape.Found.factMD_of_bctx`), and the boundary column `B_i` has every row of the root column
below `τ` (`CutPredMD.boundaryRootRowsHolds`).

* `rows_core_le`, `rows_core_lt`: the order argument on rows alone.
* `colData_x0`: the column data of the copy of `x₀` in a block `m < n` (block `0` included).
-/

namespace OmegaY.Official.Recon.TopChain.Seam

open Canonical Expansion Geometry Frame Classification
open CrossUpperSim CrossUpper
open Classification.Proofs.ChainCorr (MStep cutOrigin blockEmits)
open Classification.Proofs (ScaleReach)
open Classification.Proofs.ChainCorr.LowerChain (CopyOf TopNode Stand TopStep TopStart above
  IsTopAt)
open Classification.ControlProof (height_le_of_index height_lt_of_index node_eq_of_index)
open LowerChainRecon (node_of_cell ref_inj reserve_rawParent_of_frame frame_rawParent_of_reserve)

/-! ## The order argument -/

/-- Rows: the lookup at or below. -/
theorem rows_core_le {RR : Row → Prop} {τ σ ρu σν ρpe : Row} (hσ : σ < τ)
    (hU : ∀ r, RR r → (r ≤ σ → r ≤ ρu) ∧ (σ < r → ρu < r))
    (hP : ∀ r, RR r → (r ≤ σν → r ≤ ρpe) ∧ (σν < r → ρpe < r))
    (hle : ρpe ≤ ρu) (hB : ∀ r, RR r → r < τ → r ≤ ρu → r ≤ ρpe) :
    ∀ r, RR r → (r ≤ σν ↔ r ≤ σ) := by
  intro r hr
  constructor
  · intro h
    have h1 := (hP r hr).1 h
    by_contra hn
    have := (hU r hr).2 (lt_of_not_ge hn)
    exact absurd (lt_of_le_of_lt (le_trans h1 hle) this) (lt_irrefl _)
  · intro h
    have h1 := hB r hr (lt_of_le_of_lt h hσ) ((hU r hr).1 h)
    by_contra hn
    have := (hP r hr).2 (lt_of_not_ge hn)
    exact absurd (lt_of_le_of_lt h1 this) (lt_irrefl _)

/-- Rows: the lookup strictly below. -/
theorem rows_core_lt {RR : Row → Prop} {τ σ ρu σν ρpe : Row} (hσ : σ < τ)
    (hU : ∀ r, RR r → (r < σ → r < ρu) ∧ (σ ≤ r → ρu ≤ r))
    (hP : ∀ r, RR r → (r ≤ σν → r ≤ ρpe) ∧ (σν < r → ρpe < r))
    (hlt : ρpe < ρu) (hB : ∀ r, RR r → r < τ → r < ρu → r ≤ ρpe) :
    ∀ r, RR r → (r ≤ σν ↔ r < σ) := by
  intro r hr
  constructor
  · intro h
    have h1 := (hP r hr).1 h
    by_contra hn
    have := (hU r hr).2 (le_of_not_gt hn)
    exact absurd (lt_of_le_of_lt h1 (lt_of_lt_of_le hlt this)) (lt_irrefl _)
  · intro h
    have h1 := hB r hr (lt_trans h hσ) ((hU r hr).1 h)
    by_contra hn
    have := (hP r hr).2 (lt_of_not_ge hn)
    exact absurd (lt_of_le_of_lt h1 this) (lt_irrefl _)

/-- The comparison of an emit with the root rows, in the two forms used above. -/
theorem ecmp_le {M : Mountain} {cr : Nat} {p : Emit × Origin}
    (h : Classification.Proofs.ChainCorr.SRCmp.ECmp M cr p) {c : Cell}
    (hc : Reserve.cell? M p.2.src = some c) :
    ∀ r, Classification.Proofs.ChainCorr.SRCmp.RootRow M cr r →
      (r ≤ official c.row → r ≤ p.1.row) ∧ (official c.row < r → p.1.row < r) := by
  intro r hr
  have H := h c hc r hr
  cases hcut : cutOrigin p.2
  · obtain ⟨h1, h2, h3⟩ := H.1 hcut
    refine ⟨fun hle => ?_, h3⟩
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact (h1 hlt).le
    · exact le_of_eq (h2 heq).symm
  · obtain ⟨h1, h2⟩ := H.2 hcut
    exact ⟨fun hle => (h1 hle).le, h2⟩

theorem ecmp_lt {M : Mountain} {cr : Nat} {p : Emit × Origin}
    (h : Classification.Proofs.ChainCorr.SRCmp.ECmp M cr p) (hcut : cutOrigin p.2 = false)
    {c : Cell} (hc : Reserve.cell? M p.2.src = some c) :
    ∀ r, Classification.Proofs.ChainCorr.SRCmp.RootRow M cr r →
      (r < official c.row → r < p.1.row) ∧ (official c.row ≤ r → p.1.row ≤ r) := by
  intro r hr
  obtain ⟨h1, h2, h3⟩ := (h c hc r hr).1 hcut
  refine ⟨h1, fun hle => ?_⟩
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact (h3 hlt).le
  · exact le_of_eq (h2 heq.symm)

section Run

variable {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}

/-- The column data of the copy of `x₀` in a block `m < n` (block `0` included). -/
theorem colData_x0 (E : Env s n R M t root) {m : Nat} (hm : m < n) :
    ∃ lo us, LowerPB.ColData s n R M t root (M.size - 1 + (M.size - 1 - root.column) * m) m
      (M.size - 1) lo us := by
  have hcr := E.top.lt
  obtain ⟨M', hM', _, hI, _⟩ := run_basic E.run
  obtain rfl : M = M' := Except.ok.inj (E.top.build.symm.trans hM')
  have hXR : M.size - 1 + (M.size - 1 - root.column) * m < R.size := by
    rw [Proofs.CopyShape.Found.run_size E.run E.top (by omega)]
    have : (M.size - 1 - root.column) * m < n * (M.size - 1 - root.column) := by
      rw [Nat.mul_comm n]; exact Nat.mul_lt_mul_of_pos_left hm (by omega)
    omega
  obtain ⟨i', x', lo, us, hD⟩ := LowerPB.colData E.run E.top E.CI hI hXR (by omega)
  have hXX := hD.Xeq
  obtain ⟨hii, hxx⟩ := Classification.Proofs.ChainCorr.block_unique_boundary hcr hD.xb hXX
  subst hii hxx
  exact ⟨lo, us, hD⟩

end Run

/-- The emits of a column compare with the root rows as their origins. -/
theorem ecmp_of_colData {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}
    {X i x : Nat} {lo us : List (Emit × Origin)}
    (hD : LowerPB.ColData s n R M t root X i x lo us) :
    ∀ p ∈ lo ++ us, Classification.Proofs.ChainCorr.SRCmp.ECmp M root.column p := by
  have h := Classification.Proofs.ChainCorr.SRCmp.emitsT_cmp
    (ctx := ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1) X)
    (τ := official t.row) hD.top.build
    (fun _ => Proofs.CopyShape.Found.factMD_of_bctx hD.top hD.bctx) hD.emitsT
  simpa [ctxAt] using h

end OmegaY.Official.Recon.TopChain.Seam

namespace OmegaY.Official.Recon.TopChain.Seam

open Canonical Expansion Geometry Frame Classification
open CrossUpperSim CrossUpper
open Classification.Proofs.ChainCorr (MStep cutOrigin blockEmits)
open Classification.Proofs (ScaleReach)
open Classification.Proofs.ChainCorr.LowerChain (CopyOf TopNode Stand TopStep TopStart above
  IsTopAt)
open Classification.ControlProof (height_le_of_index height_lt_of_index node_eq_of_index)
open LowerChainRecon (node_of_cell ref_inj reserve_rawParent_of_frame frame_rawParent_of_reserve)

section Run

variable {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}

/-- The boundary column `B_i` has a node at every root row below `τ`. -/
theorem bnd_node (E : Env s n R M t root) {i : Nat} (hi1 : 1 ≤ i) (hin : i ≤ n)
    {p : Ref × Cell} (hp : p ∈ realNodes M root.column) (hpτ : official p.2.row < official t.row) :
    ∃ G : (Frame.ofMountain R).Node, G.1.val = root.column + (M.size - 1 - root.column) * i ∧
      Real G ∧ official ((Frame.ofMountain R).height G) = official p.2.row := by
  obtain ⟨col, hcol, htc⟩ := Proofs.CopyShape.Found.top_col E.top
  have h := CutPredMD.boundaryRootRowsHolds s n R E.run M col t root E.top.build hcol htc
    E.top.left E.top.lt i hi1 (Proofs.CopyShape.Found.boundary_lt E.run E.top hi1 hin) p hp hpτ
  obtain ⟨q, hq, hqrow⟩ := h
  obtain ⟨G, hGc, hGr, _, hGcell⟩ := frameNode_of_realNodes hq
  refine ⟨G, hGc, hGr, ?_⟩
  change official ((Frame.ofMountain R).cell G).row = _
  rw [hGcell, hqrow]

/-- A root row as a `RootRow`. -/
theorem rootRow_of_cell {c : Ref} {cc : Cell} (hcc : Reserve.cell? M c = some cc)
    (hc1 : 1 ≤ c.index) (hcc' : c.column = root.column) :
    Classification.Proofs.ChainCorr.SRCmp.RootRow M root.column (official cc.row) := by
  refine ⟨(c, cc), ?_, rfl⟩
  have := Proofs.CopyShape.mem_realNodes_of_cell' hcc hc1
  rwa [hcc'] at this

end Run

/-- **`StepRootLookup` holds.** -/
theorem stepRootLookup : StepRootLookup := by
  intro s n R M t root i hrun hTop hi0 hin Z z hTN a cz ca hraw hcz hca hlo he A' hA'
  have hi1 : 1 ≤ i := hi0
  obtain ⟨ZN, VN, A, zN, z'N, aN, lo, us, jz, hZ, hz, ha, C⟩ :=
    lo_core hrun hTop hi1 hin hTN hraw hcz hca hlo
  subst hZ hz ha
  have hAA : A' = Frame.ref A :=
    Option.some.inj (hA'.symm.trans (reserve_rawParent_of_frame C.Araw))
  subst hAA
  have E := C.E
  have hG := E.G
  have hF := E.FR
  have hVM := build_valid_of_success hTop.build
  have hcr := hTop.lt
  have hac : aN.1.val = root.column := he
  obtain ⟨loB, usB, hDB⟩ := colData_x0 E (m := i - 1) (by omega)
  have hBeq := Classification.Proofs.ChainCorr.boundary_eq hcr hi0
  have hAc : A.1.val = M.size - 1 + (M.size - 1 - root.column) * (i - 1) := by
    rw [C.Ac, shiftCol_of_le (le_of_eq hac.symm), hac, hBeq]
  -- the emit and the rows of `V`
  have hVmem : lo[jz + 1]'C.jzl ∈ lo ++ us := List.mem_append_left _ (List.getElem_mem _)
  have hVc : Reserve.cell? M (lo[jz + 1]'C.jzl).2.src = some ((Frame.ofMountain M).cell z'N) := by
    rw [C.Vsrc]; exact LowerChainRecon.cell?_ref z'N
  have hCV := ecmp_lt (ecmp_of_colData C.D _ hVmem) C.Vcut hVc
  set ρu := (lo[jz + 1]'C.jzl).1.row with hρu
  set σ := official ((Frame.ofMountain M).cell z'N).row with hσdef
  have hz'1 : (1 : Row) ≤ (Frame.ofMountain M).height z'N := by
    obtain ⟨h1, h2⟩ := upper_spec C.zu
    exact one_le_height hG (show 0 < z'N.2.val by omega)
  have hσ : σ < official t.row := official_strictMono hz'1 C.z'lt
  have hVrow : (Frame.ofMountain R).height VN = stored ρu := C.Vrow
  -- boundary nodes below `V` are at or below `A`
  have hbnd : ∀ p ∈ realNodes M root.column, official p.2.row < official t.row →
      official p.2.row < ρu → ∃ G : (Frame.ofMountain R).Node, G.1 = A.1 ∧ Real G ∧
        official ((Frame.ofMountain R).height G) = official p.2.row ∧ G.2.val ≤ A.2.val := by
    intro p hp hpτ hpu
    obtain ⟨G, hGc, hGr, hGrow⟩ := bnd_node E hi1 hin hp hpτ
    have hGA : G.1 = A.1 := Fin.ext (by rw [hGc, hAc, hBeq])
    refine ⟨G, hGA, hGr, hGrow, C.AH.2 G hGA ?_⟩
    rw [hVrow]
    apply row_lt_of_official (JumpLaw.one_le_stored _)
    rw [JumpLaw.official_stored, hGrow]
    exact hpu
  -- `a` is a root row below `V`
  have har1 : 1 ≤ (Frame.ref aN).index := C.ar
  have hamem : (Frame.ref aN, (Frame.ofMountain M).cell aN) ∈ realNodes M root.column := by
    have := Proofs.CopyShape.mem_realNodes_of_cell' (LowerChainRecon.cell?_ref aN) har1
    rwa [show (Frame.ref aN).column = root.column from hac] at this
  have ha1 : (1 : Row) ≤ (Frame.ofMountain M).height aN := one_le_height hG C.ar
  have haσ : official ((Frame.ofMountain M).cell aN).row < σ :=
    official_strictMono ha1 C.aH.1
  have hRa := rootRow_of_cell (root := root) (LowerChainRecon.cell?_ref aN) har1 hac
  have hau : official ((Frame.ofMountain M).cell aN).row < ρu := (hCV _ hRa).1 haσ
  obtain ⟨G0, _, hG0r, _, hG0A⟩ := hbnd _ hamem (lt_trans haσ hσ) hau
  have hA1 : 1 ≤ A.2.val := le_trans hG0r hG0A
  -- the emit of `A`
  obtain ⟨hAk, hArow⟩ := node_row hDB hAc hA1
  have hAV : (Frame.ofMountain R).height A < (Frame.ofMountain R).height VN := C.AH.1
  have hAlt : ((loB ++ usB)[A.2.val - 1]).1.row < ρu := by
    have := hAV
    rw [hArow, hVrow] at this
    exact LowerPB.lt_of_stored_lt this
  have hVlt : ρu < official t.row := C.D.lo_lt _ (List.getElem_mem _)
  have hAlo : A.2.val - 1 < loB.length := lower_of_row hDB hAk (lt_trans hAlt hVlt)
  have hfe : (loB ++ usB)[A.2.val - 1] = loB[A.2.val - 1] := List.getElem_append_left hAlo
  have hfmem : loB[A.2.val - 1] ∈ loB := List.getElem_mem _
  obtain ⟨⟨_, _, _, _, _⟩, hfup⟩ := LowerPB.lowerT_good hDB.hlo _ hfmem
  obtain ⟨km, cν, hfsrc, hkm1, hcν, _⟩ := LowerPB.lowerT_src hDB.hlo hfmem
  have hfsrc' : ((loB ++ usB)[A.2.val - 1]).2.src = ⟨M.size - 1, km⟩ := by
    rw [hfe, hfsrc]; rfl
  have hcν' : Reserve.cell? M ((loB ++ usB)[A.2.val - 1]).2.src = some cν := by
    rw [hfsrc']; exact hcν
  have hcν1 : (1 : Row) ≤ cν.row := LowerPB.cell_row_one_le hVM hcν hkm1
  -- the origin of `A` is below `τ`
  have hντ : official cν.row < official t.row := by
    have hes := hDB.emitsT
    obtain ⟨c', hc', hlt'⟩ := Classification.Proofs.ChainCorr.SRParts.lower_src_lt hes hAk
      (by rw [hfe]; exact hfup)
    have : c' = cν := by
      have h2 : Reserve.cell? M ((loB ++ usB)[A.2.val - 1]).2.src = some c' := by
        simpa [ctxAt] using hc'
      exact Option.some.inj (h2.symm.trans hcν')
    rw [← this]; exact hlt'
  -- the comparison of `A` with the root rows
  have hCA := ecmp_le (ecmp_of_colData hDB _ (List.getElem_mem hAk)) hcν'
  have hkey := rows_core_lt (RR := Classification.Proofs.ChainCorr.SRCmp.RootRow M root.column)
    (τ := official t.row) (σ := σ) (ρu := ρu) (σν := official cν.row)
    (ρpe := ((loB ++ usB)[A.2.val - 1]).1.row) hσ hCV hCA hAlt (by
      intro r hr hrτ hru
      obtain ⟨p, hp, rfl⟩ := hr
      obtain ⟨G, hGA, hGr, hGrow, hGle⟩ := hbnd p hp hrτ hru
      rw [← hGrow, ← JumpLaw.official_stored ((loB ++ usB)[A.2.val - 1]).1.row, ← hArow]
      exact official_mono (one_le_height hF hGr) (height_le_of_index hF hGA hGle))
  -- the lookup
  refine ⟨loB ++ usB, A.2.val - 1, hAk, ?_, ?_, cν, hcν', ?_, ?_, ?_, ?_⟩
  · show emitsT _ _ = _
    have := hDB.emitsT
    rw [← hAc] at this ⊢
    exact this
  · simp only [Frame.ref, hAc]
    congr 1
    omega
  · rw [hfsrc']
  · rw [hfsrc']; exact hkm1
  · exact row_lt_of_official hTop.row_one_le hντ
  · refine Classification.Proofs.ChainCorr.Inner.highestAtMost_of_max (by exact hac) C.ar
      (LowerChainRecon.cell?_ref aN) ?_ ?_
    · exact le_of_official_le hcν1 ((hkey _ hRa).mpr haσ)
    · intro jj cc hcc hjj hccle
      have hcc1 : (1 : Row) ≤ cc.row := LowerPB.cell_row_one_le hVM hcc hjj
      have hRc := rootRow_of_cell (root := root) hcc hjj rfl
      have hlt := (hkey _ hRc).mp (official_mono hcc1 hccle)
      obtain ⟨cN, hcN, hcNc⟩ := node_of_cell hcc
      have hcN1 : cN.1 = aN.1 := Fin.ext (by
        have := congrArg Ref.column hcN; simp [Frame.ref] at this; omega)
      have hcNj : cN.2.val = jj := by
        have := congrArg Ref.index hcN; simpa [Frame.ref] using this
      have hh : (Frame.ofMountain M).height cN < (Frame.ofMountain M).height z'N := by
        apply row_lt_of_official hz'1
        change official ((Frame.ofMountain M).cell cN).row < σ
        rw [hcNc]; exact hlt
      have := C.aH.2 cN hcN1 hh
      show jj ≤ aN.2.val
      omega

end OmegaY.Official.Recon.TopChain.Seam

#print axioms OmegaY.Official.Recon.TopChain.Seam.stepRootLookup

namespace OmegaY.Official.Recon.TopChain.Seam

open Canonical Expansion Geometry Frame Classification
open CrossUpperSim CrossUpper
open Classification.Proofs.ChainCorr (MStep cutOrigin blockEmits)
open Classification.Proofs (ScaleReach)
open Classification.Proofs.ChainCorr.LowerChain (CopyOf TopNode Stand TopStep TopStart above
  IsTopAt)
open Classification.ControlProof (height_le_of_index height_lt_of_index node_eq_of_index)
open LowerChainRecon (node_of_cell ref_inj reserve_rawParent_of_frame frame_rawParent_of_reserve)

/-- **`StartRootLookup` holds** (the argument of `SRFixPa.paLookup`, for any kind of `u`). -/
theorem startRootLookup : StartRootLookup := by
  intro s n R M t root i x hrun hTop hi0 hin hx es hes j hj _ cu cv l pe pa hcu hcv hl hpa hpe
    hlo he
  have hi1 : 1 ≤ i := hi0
  have hcr := hTop.lt
  have hVM := build_valid_of_success hTop.build
  have hwi : M.size - 1 - root.column ≤ (M.size - 1 - root.column) * i :=
    Nat.le_mul_of_pos_right _ hi1
  obtain ⟨hxg, hxl⟩ := mem_blockColumns hcr hx
  -- the column of `u`
  obtain ⟨UN, hUr, hUc⟩ := node_of_cell hcu
  have hXR : x + (M.size - 1 - root.column) * i < R.size := by
    have : UN.1.val < R.size := UN.1.isLt
    have h2 : UN.1.val = x + (M.size - 1 - root.column) * i := congrArg Ref.column hUr
    omega
  have E := env_of hrun hTop hXR (by omega)
  have hG := E.G
  have hF := E.FR
  obtain ⟨lo, us, hD⟩ := colData_block E hi1 hin hx hXR
  have hee : es = lo ++ us := Except.ok.inj (hes.symm.trans hD.emitsT)
  subst hee
  have hUc' : UN.1.val = x + (M.size - 1 - root.column) * i := congrArg Ref.column hUr
  have hUi : UN.2.val = j + 1 := congrArg Ref.index hUr
  obtain ⟨hUk, hUrow⟩ := node_row hD hUc' (by omega)
  have hUe : (lo ++ us)[UN.2.val - 1] = (lo ++ us)[j] := by simp only [hUi, Nat.add_sub_cancel]
  rw [hUe] at hUrow
  have hcuR : cu.row = stored ((lo ++ us)[j]).1.row := by
    rw [← hUrow, ← hUc]; rfl
  set ρu := ((lo ++ us)[j]).1.row with hρu
  set σ := official cv.row with hσdef
  obtain ⟨_, hsrc1, _⟩ := emitsT_good hes (lo ++ us)[j] (List.getElem_mem hj)
  have hcv1 : (1 : Row) ≤ cv.row := Classification.one_le_row hVM hcv hsrc1
  have hσ : σ < official t.row := official_strictMono hcv1 hlo
  -- `u` is a lower emit
  have hjlo : j < lo.length := by
    by_contra hn
    have hmem : (lo ++ us)[j] ∈ us := by
      rw [List.getElem_append_right (by omega)]
      exact List.getElem_mem _
    obtain ⟨k2, c2, _, hc2, hup2, _, hτ2, _⟩ := (LowerPB.upperT_spec hD.hus).1 _ hmem
    have h2 : ((lo ++ us)[j]).2.src = ⟨upperColumn (ctxAt M R x i root.column
        (M.size - 1 - root.column) (M.size - 1) (x + (M.size - 1 - root.column) * i)), k2⟩ := by
      rw [hup2]; rfl
    rw [h2] at hcv
    have hcc : c2 = cv := Option.some.inj (hc2.symm.trans hcv)
    rw [hcc] at hτ2
    exact absurd (lt_of_lt_of_le hσ hτ2) (lt_irrefl _)
  have hult : ρu < official t.row := hD.lo_lt _ (by
    rw [List.getElem_append_left hjlo]; exact List.getElem_mem _)
  have hCU := ecmp_le (ecmp_of_colData hD _ (List.getElem_mem hj)) hcv
  -- `pe` in the boundary column
  have hBeq := Classification.Proofs.ChainCorr.boundary_eq hcr hi0
  obtain ⟨hpecol, hpe0, _⟩ := Classification.Proofs.ChainCorr.highestAtMost_spec hpe
  rw [he, Classification.Proofs.ChainCorr.mapColumn_of_ge (le_refl _)] at hpecol hpe
  obtain ⟨loB, usB, hDB⟩ := colData_x0 E (m := i - 1) (by omega)
  obtain ⟨cpe, hcpe⟩ : ∃ cpe, Reserve.cell? R pe = some cpe := by
    obtain ⟨_, _, col, hcol, hp, _, _⟩ := Classification.Proofs.ChainCorr.highestAtMost_spec hpe
    refine ⟨col[pe.index], ?_⟩
    simp only [Reserve.cell?, hpecol, hcol, Option.bind_eq_bind, Option.bind_some]
    exact Array.getElem?_eq_getElem hp
  obtain ⟨PE, hPEr, hPEc⟩ := node_of_cell hcpe
  have hPEcol : PE.1.val = M.size - 1 + (M.size - 1 - root.column) * (i - 1) := by
    have := congrArg Ref.column hPEr
    simp only [Frame.ref] at this
    rw [this, hpecol, hBeq]
  have hPEi : PE.2.val = pe.index := congrArg Ref.index hPEr
  obtain ⟨hPk, hProw⟩ := node_row hDB hPEcol (by omega)
  have hpele : cpe.row ≤ cu.row := Classification.Proofs.ChainCorr.SRParts.hAM_le hpe hcpe
  have hle : ((loB ++ usB)[PE.2.val - 1]).1.row ≤ ρu := by
    have h1 : (Frame.ofMountain R).height PE = cpe.row := by
      change ((Frame.ofMountain R).cell PE).row = _; rw [hPEc]
    rw [hProw] at h1
    rw [← h1, hcuR] at hpele
    exact Classification.Proofs.ChainCorr.stored_le_iff.mp hpele
  have hPlo : PE.2.val - 1 < loB.length := lower_of_row hDB hPk (lt_of_le_of_lt hle hult)
  have hfe : (loB ++ usB)[PE.2.val - 1] = loB[PE.2.val - 1] := List.getElem_append_left hPlo
  have hfmem : loB[PE.2.val - 1] ∈ loB := List.getElem_mem _
  obtain ⟨⟨_, _, _, _, _⟩, hfup⟩ := LowerPB.lowerT_good hDB.hlo _ hfmem
  obtain ⟨km, cν, hfsrc, hkm1, hcν, _⟩ := LowerPB.lowerT_src hDB.hlo hfmem
  have hfsrc' : ((loB ++ usB)[PE.2.val - 1]).2.src = ⟨M.size - 1, km⟩ := by
    rw [hfe, hfsrc]; rfl
  have hcν' : Reserve.cell? M ((loB ++ usB)[PE.2.val - 1]).2.src = some cν := by
    rw [hfsrc']; exact hcν
  have hcν1 : (1 : Row) ≤ cν.row := LowerPB.cell_row_one_le hVM hcν hkm1
  have hντ : official cν.row < official t.row := by
    obtain ⟨c', hc', hlt'⟩ := Classification.Proofs.ChainCorr.SRParts.lower_src_lt hDB.emitsT hPk
      (by rw [hfe]; exact hfup)
    have : c' = cν := by
      have h2 : Reserve.cell? M ((loB ++ usB)[PE.2.val - 1]).2.src = some c' := by
        simpa [ctxAt] using hc'
      exact Option.some.inj (h2.symm.trans hcν')
    rw [← this]; exact hlt'
  have hCP := ecmp_le (ecmp_of_colData hDB _ (List.getElem_mem hPk)) hcν'
  have hkey := rows_core_le (RR := Classification.Proofs.ChainCorr.SRCmp.RootRow M root.column)
    (τ := official t.row) (σ := σ) (ρu := ρu) (σν := official cν.row)
    (ρpe := ((loB ++ usB)[PE.2.val - 1]).1.row) hσ hCU hCP hle (by
      intro r hr hrτ hru
      obtain ⟨p, hp, rfl⟩ := hr
      obtain ⟨G, hGc, hGr, hGrow⟩ := bnd_node E hi1 hin hp hrτ
      have hGle : Reserve.cell? R (Frame.ref G) = some ((Frame.ofMountain R).cell G) :=
        LowerChainRecon.cell?_ref G
      have hGrow' : ((Frame.ofMountain R).cell G).row ≤ cu.row := by
        rw [hcuR]
        apply le_of_official_le (JumpLaw.one_le_stored _)
        rw [JumpLaw.official_stored]
        change official ((Frame.ofMountain R).height G) ≤ ρu
        rw [hGrow]; exact hru
      have hidx := Classification.Proofs.ChainCorr.SRParts.hAM_max hpe (q := Frame.ref G)
        (by simp only [Frame.ref]; rw [hGc]) hGr hGle hGrow'
      have hGA : G.1 = PE.1 := Fin.ext (by rw [hGc, hPEcol, hBeq])
      have hGi : G.2.val ≤ PE.2.val := by simp only [Frame.ref] at hidx; omega
      rw [← hGrow, ← JumpLaw.official_stored ((loB ++ usB)[PE.2.val - 1]).1.row, ← hProw]
      exact official_mono (one_le_height hF hGr) (height_le_of_index hF hGA hGi))
  -- the lookup
  have hpeq : pe = ⟨M.size - 1 + (M.size - 1 - root.column) * (i - 1), PE.2.val - 1 + 1⟩ := by
    rw [← hPEr]; simp only [Frame.ref, hPEcol]; congr 1; omega
  obtain ⟨hpacol, hpa0, _⟩ := Classification.Proofs.ChainCorr.highestAtMost_spec hpa
  rw [he] at hpacol hpa
  obtain ⟨cpa, hcpa⟩ : ∃ cpa, Reserve.cell? M pa = some cpa := by
    obtain ⟨_, _, col, hcol, hp, _, _⟩ := Classification.Proofs.ChainCorr.highestAtMost_spec hpa
    refine ⟨col[pa.index], ?_⟩
    simp only [Reserve.cell?, hpacol, hcol, Option.bind_eq_bind, Option.bind_some]
    exact Array.getElem?_eq_getElem hp
  have hcpa1 : (1 : Row) ≤ cpa.row := Classification.one_le_row hVM hcpa hpa0
  have hRpa := rootRow_of_cell (root := root) hcpa hpa0 hpacol
  have hpale := Classification.Proofs.ChainCorr.SRParts.hAM_le hpa hcpa
  refine ⟨loB ++ usB, PE.2.val - 1, hPk, ?_, hpeq, cν, hcν', ?_, ?_, ?_, ?_⟩
  · show emitsT _ _ = _
    have := hDB.emitsT
    exact this
  · rw [hfsrc']
  · rw [hfsrc']; exact hkm1
  · exact row_lt_of_official hTop.row_one_le hντ
  · refine Classification.Proofs.ChainCorr.Inner.highestAtMost_of_max hpacol hpa0 hcpa ?_ ?_
    · exact le_of_official_le hcν1 ((hkey _ hRpa).mpr (official_mono hcpa1 hpale))
    · intro jj cc hcc hjj hccle
      have hcc1 : (1 : Row) ≤ cc.row := LowerPB.cell_row_one_le hVM hcc hjj
      have hRc := rootRow_of_cell (root := root) hcc hjj rfl
      have hle2 := (hkey _ hRc).mp (official_mono hcc1 hccle)
      exact Classification.Proofs.ChainCorr.SRParts.hAM_max hpa (q := ⟨root.column, jj⟩) rfl hjj
        hcc (le_of_official_le hcv1 hle2)

end OmegaY.Official.Recon.TopChain.Seam

#print axioms OmegaY.Official.Recon.TopChain.Seam.startRootLookup
