/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/NonTopBase.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.StepInnerCleanRootLookup
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.LowerChain

set_option backward.do.legacy false

/-!
# Clean copies in every copied column of a block (the base of `NonTop*.lean`)

`StepInnerCleanLookup.lean` and `StepInnerCleanRootLookup.lean` study a clean copy (`b = 0`) `v`
of a node `a = (y, C)` in an **inner** column `y + w·i` (`c_r < y < x₀`) of a block `i ≥ 1`:
its raw parent in the output is on its row (`clean_parent_row`), and when the leg of `a` is
right of `c_r` it is the clean copy of the next generation (`lookupInner`).

The statements of `LowerChain.lean` about the nodes that are not top copies (`StartRelNT`,
`StartRootNT`) are about every copied column of a block, including the copy `x₀ + w·i` of the
last column. This file proves the same facts for a column `y` with `c_r < y ≤ x₀`
(`CopyAtX`): `copyAtX_cell`, `copyAtX_left`, `factsX`, `cleanX_parent_row`,
`chainX_first_step`, `lookupInnerX`, collected in **`cleanStepX`**: from a clean copy `v` of `a`
one output step at the row of `v` reaches the node of the image of the leg column at that row,
which is the clean copy of the next generation `b` of `a` when `b` is right of `c_r`.

All declarations are in the namespace `ChainCorr.NonTop`.
-/

namespace OmegaY.Official.Classification.Proofs.ChainCorr.NonTop

open Canonical Reserve Official Descent Classification Proofs
open Recon Recon.RowLaw
open ChainCorr.Inner ChainCorr.Inner.Clean ChainCorr.Inner.CleanRoot

/-! ## Copies in every column of a block -/

/-- `v` is the node of the copy `y + w·i` of a column `y` (`c_r < y ≤ x₀`) of block `i`,
emitted with origin `o`. -/
def CopyAtX (M R : Mountain) (n cr x0 : Nat) (τ : Row) (i : Nat) (v : Ref) (o : Origin) :
    Prop :=
  ∃ y es j, cr < y ∧ y ≤ x0 ∧ y ∈ blockColumns cr x0 n i ∧ v.column = y + (x0 - cr) * i ∧
    v.index = j + 1 ∧ emitsT (ctxAt M R y i cr (x0 - cr) x0 v.column) τ = .ok es ∧
    ∃ hj : j < es.length, es[j].2 = o

theorem copyAtX_of_copyAt {M R : Mountain} {n cr x0 : Nat} {τ : Row} {i : Nat} {v : Ref}
    {o : Origin} (h : CopyAt M R n cr x0 τ i v o) : CopyAtX M R n cr x0 τ i v o := by
  obtain ⟨y, es, j, h1, h2, h3, h4, h5, h6, hj, ho⟩ := h
  exact ⟨y, es, j, h1, le_of_lt h2, h3, h4, h5, h6, hj, ho⟩

theorem copyAt_of_copyAtX {M R : Mountain} {n cr x0 : Nat} {τ : Row} {i : Nat} {v : Ref}
    {o : Origin} (h : CopyAtX M R n cr x0 τ i v o) (hx : v.column < x0 + (x0 - cr) * i) :
    CopyAt M R n cr x0 τ i v o := by
  obtain ⟨y, es, j, h1, h2, h3, h4, h5, h6, hj, ho⟩ := h
  exact ⟨y, es, j, h1, by omega, h3, h4, h5, h6, hj, ho⟩

/-- The block and the source column of a copied column of a block `i ≥ 1` are unique. -/
theorem blockX_unique {cr x0 n i i' y x' : Nat} (hcr : cr < x0) (hy : cr < y) (hyx : y ≤ x0)
    (hx' : x' ∈ blockColumns cr x0 n i') (heq : y + (x0 - cr) * i = x' + (x0 - cr) * i')
    (hi : 0 < i) : i' = i ∧ x' = y := by
  have hw : 0 < x0 - cr := by omega
  have hwi : x0 - cr ≤ (x0 - cr) * i := Nat.le_mul_of_pos_right _ hi
  rcases Nat.eq_zero_or_pos i' with h0 | hpos
  · subst h0
    simp [blockColumns] at hx'
    omega
  · obtain ⟨hcx, hxx⟩ := mem_blockColumns_pos hx' hpos
    rcases Nat.lt_trichotomy i i' with hlt | heq' | hlt
    · have : (x0 - cr) * i + (x0 - cr) ≤ (x0 - cr) * i' := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hlt
      omega
    · subst heq'
      exact ⟨rfl, by omega⟩
    · have : (x0 - cr) * i' + (x0 - cr) ≤ (x0 - cr) * i := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hlt
      omega

/-- The cell of an output node with a traced origin (any copied column of a block `i ≥ 1`). -/
theorem copyAtX_cell {s : List Nat} {n D : Nat} {M : Mountain} {out : List Nat} {ρ : Root}
    {R : Mountain} {col : Column} {t : Cell} (hS : Setting s n D M out ρ R col t) {i : Nat}
    (hi0 : 0 < i) (hi : i < n + 1) {v : Ref} {o : Origin}
    (h : CopyAtX M R n ρ.cr ρ.x0 (official t.row) i v o) :
    ∃ y es j, ∃ hj : j < es.length, es[j].2 = o ∧
      (v.column = y + (ρ.x0 - ρ.cr) * i ∧ ρ.cr < y ∧ y ≤ ρ.x0 ∧ v.column < R.size) ∧
      y ∈ blockColumns ρ.cr ρ.x0 n i ∧ v.index = j + 1 ∧
      emitsT (ctxAt M R y i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 v.column) (official t.row) = .ok es ∧
      ∃ cv, cell? R v = some cv ∧ cv.row = stored es[j].1.row ∧ ∃ ref : Ref, cv.left = some ref ∧
        ref.column = legColumn (ctxAt M R y i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 v.column) es[j].1 := by
  obtain ⟨y, es, j, hcy, hyx, hyb, hvc, hvi, hes, hj, ho⟩ := h
  obtain ⟨col', t', hcol', ht', _, hcrx, hinv⟩ := spliceCase_data hS.splice hS.run
  have hcc : col' = col := Option.some.inj (hcol'.symm.trans hS.hcol)
  subst hcc
  have htt : t' = t := Option.some.inj (ht'.symm.trans hS.ht)
  subst htt
  have hRs : R.size = ρ.x0 + n * (ρ.x0 - ρ.cr) := by
    rw [build_size hS.canon]
    exact Reconstruction.expand_length_splice hS.splice.build hS.splice.run hS.splice.root
      hS.splice.copies
  have hw1 : ρ.x0 - ρ.cr ≤ (ρ.x0 - ρ.cr) * i := Nat.le_mul_of_pos_right _ hi0
  -- the column is in range
  have hXR : v.column < R.size := by
    rw [hRs, hvc]
    unfold blockColumns at hyb
    rw [if_neg (by omega)] at hyb
    simp only [List.mem_range'_1] at hyb
    by_cases hin : i < n
    · rw [if_pos hin] at hyb
      have : (ρ.x0 - ρ.cr) * i + (ρ.x0 - ρ.cr) ≤ n * (ρ.x0 - ρ.cr) := by
        rw [Nat.mul_comm n, ← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hin
      omega
    · rw [if_neg hin] at hyb
      have hin' : i = n := by omega
      subst hin'
      rw [Nat.mul_comm]
      omega
  have hX0 : ρ.x0 ≤ v.column := by omega
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

/-- The left end of a copied node is in the image of the leg column of its origin. -/
theorem copyAtX_left {s : List Nat} {n D : Nat} {M : Mountain} {out : List Nat} {ρ : Root}
    {R : Mountain} {col : Column} {t : Cell} (hS : Setting s n D M out ρ R col t) {i : Nat}
    (hi0 : 0 < i) (hi : i < n + 1) {u : Ref} {o : Origin}
    (h : CopyAtX M R n ρ.cr ρ.x0 (official t.row) i u o) :
    ∃ (cu : Cell) (ref : Ref) (co : Cell) (l : Ref), cell? R u = some cu ∧ cu.left = some ref ∧
      cell? M o.src = some co ∧ co.left = some l ∧
      ref.column = mapColumn ρ.cr ((ρ.x0 - ρ.cr) * i) l.column := by
  have hV := build_valid_of_success hS.splice.build
  obtain ⟨y, es, j, hj, ho, ⟨hvc, hcy, hyx, hXR⟩, _, hvi, hes, cu, hcu, _, ref, hrefl, hrefc⟩ :=
    copyAtX_cell hS hi0 hi h
  obtain ⟨hsc, hsi, co, hco, hleft⟩ := emitsT_good hes es[j] (List.getElem_mem hj)
  rw [ho] at hsc hsi hco hleft
  rcases hleft with ⟨l, hl, hlc⟩ | ⟨hnone, h0, hnu⟩
  · refine ⟨cu, ref, co, l, hcu, hrefl, hco, hl, ?_⟩
    rw [hrefc]
    simp only [legColumn, hlc, ctxAt, mapColumn]
    by_cases hh : ρ.cr ≤ l.column
    · simp [hh, show ¬ l.column < ρ.cr by omega]
    · simp [hh, show l.column < ρ.cr by omega]
  · -- a bottom node: its leg is the phantom of the previous column
    rw [hnu] at hsc
    simp only [Bool.false_eq_true, if_false, ctxAt] at hsc
    have hi1 := index_one_of_official_zero hV hco hsi h0
    have hbl := bottom_left hS.splice.build hco hi1 (by omega)
    refine ⟨cu, ref, co, ⟨o.src.column - 1, 0⟩, hcu, hrefl, hco, hbl, ?_⟩
    rw [hrefc]
    simp only [legColumn, hnone, ctxAt, Array.size_extract]
    rw [hsc, mapColumn_of_ge (by omega), hvc]
    have hXR' : y + (ρ.x0 - ρ.cr) * i ≤ R.size := by omega
    omega

/-- `Facts` (`StepInnerCleanNext.lean`) in every copied column `y` (`c_r < y ≤ x₀`) of a block
`i ≥ 1`. -/
theorem factsX {s : List Nat} {n D : Nat} {M : Mountain}
    {out : List Nat} {ρ : Root} {R : Mountain} {col : Column} {t : Cell}
    (hS : Setting s n D M out ρ R col t) {i : Nat} (hi0 : 0 < i) (hi : i < n + 1) {y : Nat}
    (hcy : ρ.cr < y) :
    Facts (ctxAt M R y i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 (y + (ρ.x0 - ρ.cr) * i)) (official t.row) := by
  obtain ⟨root, hTop, hroot, hx0⟩ := top_of_setting hS
  refine ⟨⟨s, hS.splice.build⟩, by simp [ctxAt]; omega, by simp [ctxAt]; exact hcy, ?_, ?_⟩
  · intro S ρ' hbelow hρ'
    simp only [ctxAt] at hρ' ⊢
    rw [← hroot] at hρ'
    obtain ⟨κ, hκ, hlt⟩ := liftTwo hTop hbelow hρ'
    rw [hx0, hκ]
    exact hlt
  · intro S ρ' hbelow hρ'
    simp only [ctxAt, Context.boundary] at hρ' ⊢
    have hbc : ρ.cr + (ρ.x0 - ρ.cr) * i < y + (ρ.x0 - ρ.cr) * i := by omega
    rw [topIn_extract hbc]
    obtain ⟨hρmem, hρin, _⟩ := topIn_spec hρ'
    obtain ⟨q, hqmem, hqrow⟩ := boundaryRows s n D M out ρ R col t hS i hi0 hi ρ' hρmem
      (hbelow _ hρin)
    have hqin : inRegion 2 S (official q.2.row) = true := by rw [hqrow]; exact hρin
    obtain ⟨b, hb⟩ := filter_last_exists (P := fun p => inRegion 2 S (official p.2.row)) hqmem hqin
    have hb' : topIn R (ρ.cr + (ρ.x0 - ρ.cr) * i) 2 S = some b := hb
    rw [hb']
    have hle := topIn_row_max hS.canon hb' hqmem hqin
    have := coeff_le_of_inRegion (d := 0) hqin (topIn_spec hb').2.1 hle
    rw [hqrow] at this
    exact this

/-- **The raw parent of a clean copy in the output is on the row of the copy**, and it is the
highest node of the image of the leg column at or below that row (every copied column). -/
theorem cleanX_parent_row {s : List Nat} {n D : Nat} {M : Mountain}
    {out : List Nat} {ρ : Root} {R : Mountain} {col : Column} {t : Cell}
    (hS : Setting s n D M out ρ R col t) {i : Nat} (hi0 : 0 < i) (hi : i < n + 1)
    {v a : Ref} (hva : CopyAtX M R n ρ.cr ρ.x0 (official t.row) i v (.clean a false)) :
    ∃ (ca : Cell) (l : Ref) (cv : Cell) (v1 : Ref) (c1 : Cell), cell? M a = some ca ∧
      ca.left = some l ∧ cell? R v = some cv ∧ rawParent R v = some v1 ∧
      cell? R v1 = some c1 ∧ c1.row = cv.row ∧
      highestAtMost R (mapColumn ρ.cr ((ρ.x0 - ρ.cr) * i) l.column) cv.row = some v1 := by
  have hva' := hva
  obtain ⟨y, es, j, hcy, hyx, hyb, hvc, hvi, hes, hj, ho⟩ := hva'
  have hes' : emitsT (ctxAt M R y i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 (y + (ρ.x0 - ρ.cr) * i))
      (official t.row) = .ok es := by rw [← hvc]; exact hes
  have hF := factsX hS hi0 hi hcy
  obtain ⟨hj1, hnext, hrow⟩ := emitsT_follow hF hes' j hj a ho
  have hup : CopyAtX M R n ρ.cr ρ.x0 (official t.row) i (up v) (.clean a true) :=
    ⟨y, es, j + 1, hcy, hyx, hyb, by simp only [up]; exact hvc, by simp only [up]; omega,
      by simp only [up]; exact hes, hj1, hnext⟩
  -- the rows of `v` and `v⁺`
  have hcellrow : ∀ {u : Ref} {k : Nat} (hk : k < es.length), u.column = v.column →
      u.index = k + 1 → ∃ cu, cell? R u = some cu ∧ cu.row = stored es[k].1.row := by
    intro u k hk hu1 hu2
    have hcu : CopyAtX M R n ρ.cr ρ.x0 (official t.row) i u es[k].2 :=
      ⟨y, es, k, hcy, hyx, hyb, by rw [hu1]; exact hvc, hu2, by rw [hu1]; exact hes, hk, rfl⟩
    obtain ⟨y', es', k', hk', _, ⟨hyc', hcy', hyx', _⟩, _, hki, hes2, cu, hcu', hcurow, _⟩ :=
      copyAtX_cell hS hi0 hi hcu
    have hyy : y' = y := by
      have hcrx : ρ.cr < ρ.x0 := by omega
      have := blockX_unique (x' := y) (i' := i) hcrx hcy' hyx' hyb
        (by rw [← hyc', hu1, hvc]) hi0
      exact this.2.symm
    subst hyy
    have hee : es' = es := by
      have hux : u.column = y' + (ρ.x0 - ρ.cr) * i := by rw [hu1, hvc]
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
  -- the leg of `v⁺`
  obtain ⟨cu', ref, co, l, hcu', hrefl, hco, hl, hrefc⟩ := copyAtX_left hS hi0 hi hup
  have hcc : cu' = cu := Option.some.inj (hcu'.symm.trans hcu)
  subst hcc
  have hraw : rawParent R v = some ref := rawParent_eq_some.mpr ⟨cu', hcu', hrefl⟩
  have hv0 : 0 < v.index := by omega
  -- the row law of the output
  obtain ⟨q, cq, hql, hcq, hBrow, _, _⟩ := Inner.Clean.upper_row hS.canon hcv (by omega) hcu'
  rw [hrefl] at hql
  obtain rfl := Option.some.inj hql
  have hjump : Row.jump cv.row cq.row = 0 := by
    rw [hbump, Row.B] at hBrow
    exact ((Row.bump_strictMono_exponent cv.row).injective hBrow).symm
  have hcqrow : cq.row = cv.row := (Row.jump_eq_zero.mp hjump).symm
  have hham := canon_rawParent_hAM hS.canon hv0 hcv hraw
  rw [hrefc] at hham
  exact ⟨co, l, cv, ref, cq, hco, hl, hcv, hraw, hcq, hcqrow, hham⟩

/-! ## The generation chain -/

open Geometry Geometry.Frame in
/-- **The first step of the generation chain of a clean copy.** -/
theorem chainX_first_step {s : List Nat} {n D : Nat} {M : Mountain} {out : List Nat} {ρ : Root}
    {R : Mountain} {col : Column} {t : Cell} (hS : Setting s n D M out ρ R col t) {i : Nat}
    {v a : Ref} (hva : CopyAtX M R n ρ.cr ρ.x0 (official t.row) i v (.clean a false)) :
    ∃ b, GenStep M ρ.cr a b ∧ ρ.cr ≤ b.column := by
  obtain ⟨y, es, j, hcy, hyx, hyb, hvc, hvi, hes, hj, ho⟩ := hva
  have hes' : emitsT (ctxAt M R y i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 (y + (ρ.x0 - ρ.cr) * i))
      (official t.row) = .ok es := by rw [← hvc]; exact hes
  obtain ⟨C, cs, hcs, ⟨ref, cl, hn, hr⟩, hroot⟩ :=
    emitsT_cleanRoot hes' es[j] (List.getElem_mem hj) a false ho
  simp only [ctxAt] at hcs hn hr hroot
  have hb := hS.splice.build
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
    have hc : ρ.cr ≤ nq.1.val := by
      have : nq.1.val = q.column := by rw [← hnq]; rfl
      omega
    have hch := inrow_hit (cr := ρ.cr) hO hit0 na hareal hQ0 hh hc
    rw [hna] at hch
    exact first_step_of_chain hch hc


/-! ## `LookupInner` in every copied column -/

open CutGap in
/-- **`LookupInner` in every copied column** (`lookupInner` with `y ≤ x₀`). -/
theorem lookupInnerX {s : List Nat} {n D : Nat} {M : Mountain}
    {out : List Nat} {ρ : Root} {R : Mountain} {col : Column} {t : Cell}
    (hS : Setting s n D M out ρ R col t) {i : Nat} (hi0 : 0 < i) (hi : i < n + 1)
    {v a : Ref} (hva : CopyAtX M R n ρ.cr ρ.x0 (official t.row) i v (.clean a false))
    {b : Ref} (hab : GenStep M ρ.cr a b) (hlb : ρ.cr < b.column) {v1 : Ref}
    (hraw : rawParent R v = some v1) :
    CopyAt M R n ρ.cr ρ.x0 (official t.row) i v1 (.clean b false) := by
  have hb := hS.splice.build
  have hV := build_valid_of_success hb
  have hVR := build_valid_of_success hS.canon
  have hdat : ChainCorr.SpliceData s n D M out ρ R t := CopyShape.spliceData_of_setting hS
  have hva' := hva
  obtain ⟨y, es, j, hcy, hyx, hyb, hvc, hvi, hes, hj, ho⟩ := hva'
  have hes' : emitsT (ctxAt M R y i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 (y + (ρ.x0 - ρ.cr) * i))
      (official t.row) = .ok es := by rw [← hvc]; exact hes
  -- the step `a → b`
  obtain ⟨_, hb1, ca, cb, l, hca, hl, hbl, hcb, hbrow⟩ := hab
  have hlcr : ρ.cr < l.column := by rw [← hbl]; exact hlb
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
  have hascl : ascends (ctxAt M R l.column i ρ.cr (ρ.x0 - ρ.cr) ρ.x0
      (l.column + (ρ.x0 - ρ.cr) * i)) (some (ρr, ρc)) = .ok true := by
    apply ascends_of_reach (ref := refl) (cl := cll)
    · simp only [ctxAt]
      rw [hρrow]
      exact hnl
    · simpa [ctxAt] using hrl
  -- the emits of the column `l`
  obtain ⟨hlmem, esl, hesl⟩ := inner_emits hS hi0 hi hlcr (by omega)
  -- the non-cut emit of `b` in the column `l`
  obtain ⟨k0, hk0, hk0src, hk0nc⟩ := CopyShape.NoMA.inner_copyEmitted s n D M out ρ R col t hS
    i hi0 hi l.column esl hlcr (by omega) hesl b cb hbl hb1 hcb
  have hCτ : official cs.row < official t.row :=
    (lowerItems_below (official t.row) _ hqx).1 _ hqxin
  have hbC : official cb.row = official cs.row := by rw [hbrow]
  have hclean : esl[k0].2 = .clean b false := by
    have hlowl := emitsT_plainAsc (ctx := ctxAt M R l.column i ρ.cr (ρ.x0 - ρ.cr) ρ.x0
      (l.column + (ρ.x0 - ρ.cr) * i)) (τ := official t.row) hesl
    have hupl := emitsT_upperRow (ctx := ctxAt M R l.column i ρ.cr (ρ.x0 - ρ.cr) ρ.x0
      (l.column + (ρ.x0 - ρ.cr) * i)) (τ := official t.row) hesl
    generalize hE : esl[k0].2 = o at hk0src hk0nc
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
        have := hupl esl[k0] (List.getElem_mem hk0) b hE cb hcb
        rw [hbC] at this
        exact absurd hCτ (not_lt.mpr this)
    | plain r' =>
        exfalso
        have hr' : r' = b := hk0src
        rw [hr'] at hE
        rcases hlowl esl[k0] (List.getElem_mem hk0) b hE cb hcb with
          ⟨q1, hq1, hq11, hq1in⟩ | hP
        · have hq1in' : inRegion q1.1 q1.2.source (official cs.row) = true := by
            rw [← hbC]; exact hq1in
          have := Recon.JumpLaw.lowerItems_eq_of_common hqx hq1 hqxin hq1in'
          rw [this] at hqx2
          omega
        · have hρ' : topIn M ρ.cr 2 (official cb.row) = some (ρr, ρc) := by
            rw [hbC]; exact hρ
          have hρrow' : official ρc.row = official cb.row := by rw [hbC]; exact hρrow
          have hf : ascends (ctxAt M R l.column i ρ.cr (ρ.x0 - ρ.cr) ρ.x0
              (l.column + (ρ.x0 - ρ.cr) * i)) (some (ρr, ρc)) = .ok false :=
            hP b hE cb hcb ρr ρc hρ' hρrow'
          rw [hascl] at hf
          cases hf
  -- the copy node of `b`
  let v2 : Ref := ⟨l.column + (ρ.x0 - ρ.cr) * i, k0 + 1⟩
  have hv2 : CopyAt M R n ρ.cr ρ.x0 (official t.row) i v2 (.clean b false) :=
    ⟨l.column, esl, k0, hlcr, by omega, hlmem, rfl, rfl, hesl, hk0, hclean⟩
  -- both copies keep the row `C`
  have hRR : ChainCorr.SRCmp.RootRow M ρ.cr (official cs.row) :=
    ⟨(ρr, ρc), (topIn_spec hρ).1, hρrow⟩
  have hrowv : es[j].1.row = official cs.row := by
    have hcmp := ChainCorr.SRCmp.rootCmp s n D M out ρ R t hdat i hi y hyb es hes' es[j]
      (List.getElem_mem hj) cs (by rw [ho]; exact hacell) (official cs.row) hRR
    rw [ho] at hcmp
    exact (hcmp.1 rfl).2.1 rfl
  have hrowv2 : esl[k0].1.row = official cs.row := by
    have hcmp := ChainCorr.SRCmp.rootCmp s n D M out ρ R t hdat i hi l.column hlmem esl hesl
      esl[k0] (List.getElem_mem hk0) cb (by rw [hclean]; exact hcb) (official cs.row) hRR
    rw [hclean] at hcmp
    exact ((hcmp.1 rfl).2.1 hbC.symm)
  -- the cells in the output
  obtain ⟨y1, es1, j1, hj1, ho1, ⟨hvc1, hcy1, hyx1, _⟩, _, hvi1, hes1, cv, hcv, hcvrow, _⟩ :=
    copyAtX_cell hS hi0 hi hva
  obtain ⟨y2, es2, j2, hj2, ho2, ⟨hvc2, hcy2, hyx2, _⟩, _, hvi2, hes2, cv2, hcv2, hcv2row, _⟩ :=
    copyAtX_cell hS hi0 hi (copyAtX_of_copyAt hv2)
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
  have he2 : es2 = esl := by
    have e : v2.column = l.column + (ρ.x0 - ρ.cr) * i := rfl
    rw [e, hesl] at hes2
    exact (Except.ok.inj hes2).symm
  subst he2
  have hkk : j2 = k0 := by simp [v2] at hvi2; omega
  subst hkk
  -- the raw parent of `v` is the node of `φ(l)` at the row of `v`
  obtain ⟨ca', l', cv', v1', c1, hca', hl', hcv', hraw', hc1, hrow1, hham⟩ :=
    cleanX_parent_row hS hi0 hi hva
  have e1 : v1' = v1 := Option.some.inj (hraw'.symm.trans hraw)
  subst e1
  have e2 : cv' = cv := Option.some.inj (hcv'.symm.trans hcv)
  subst e2
  have e3 : ca' = cs := Option.some.inj (hca'.symm.trans hacell)
  subst e3
  have e4 : l' = l := Option.some.inj (hl'.symm.trans hl)
  subst e4
  have hv1col : v1'.column = l'.column + (ρ.x0 - ρ.cr) * i := by
    have := highestAtMost_column hham
    rw [this, mapColumn_of_ge (le_of_lt hlcr)]
  have hrows : c1.row = cv2.row := by
    rw [hrow1, hcvrow, hcv2row, hrowv, hrowv2]
  have hv1 : v1' = v2 := cell?_eq_of_index hVR (by rw [hv1col]) hc1 hcv2 hrows
  rw [hv1]
  exact hv2


/-! ## One step from a clean copy -/

/-- **One output step from a clean copy** (`b = 0`) of `a` in any copied column of a block
`i ≥ 1`: the raw parent `v₁` of `v` is on the row of `v` and left of `v`; with the next
generation `b` of `a` (`c_r ≤ col b`), `v₁` is the clean copy of `b` when `b` is right of `c_r`,
and `v₁` is in the boundary column `c_r + w·i` when `b` is in the root column. -/
theorem cleanStepX {s : List Nat} {n D : Nat} {M : Mountain}
    {out : List Nat} {ρ : Root} {R : Mountain} {col : Column} {t : Cell}
    (hS : Setting s n D M out ρ R col t) {i : Nat} (hi0 : 0 < i) (hi : i < n + 1)
    {v a : Ref} (hva : CopyAtX M R n ρ.cr ρ.x0 (official t.row) i v (.clean a false)) :
    ∃ (b v1 : Ref) (cv c1 : Cell), GenStep M ρ.cr a b ∧ ρ.cr ≤ b.column ∧
      rawParent R v = some v1 ∧ cell? R v = some cv ∧ cell? R v1 = some c1 ∧ c1.row = cv.row ∧
      v1.column < v.column ∧
      (ρ.cr < b.column → CopyAt M R n ρ.cr ρ.x0 (official t.row) i v1 (.clean b false)) ∧
      (b.column = ρ.cr → v1.column = ρ.cr + (ρ.x0 - ρ.cr) * i) := by
  have hVR := build_valid_of_success hS.canon
  obtain ⟨b, hab, hb⟩ := chainX_first_step hS hva
  obtain ⟨ca, l, cv, v1, c1, hca, hl, hcv, hraw, hc1, hrow, hham⟩ := cleanX_parent_row hS hi0 hi hva
  have hlt := (rawParent_cells hVR hraw).2.2
  have hab' := hab
  obtain ⟨_, _, ca', cb, l', hca', hl', hbl, _, _⟩ := hab'
  have e1 : ca' = ca := Option.some.inj (hca'.symm.trans hca)
  subst e1
  have e2 : l' = l := Option.some.inj (hl'.symm.trans hl)
  subst e2
  have hv1c : v1.column = mapColumn ρ.cr ((ρ.x0 - ρ.cr) * i) l'.column := highestAtMost_column hham
  refine ⟨b, v1, cv, c1, hab, hb, hraw, hcv, hc1, hrow, hlt,
    fun h => lookupInnerX hS hi0 hi hva hab h hraw, fun h => ?_⟩
  rw [hv1c, ← hbl, h, mapColumn_of_ge (le_refl _)]

end OmegaY.Official.Classification.Proofs.ChainCorr.NonTop

#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.NonTop.cleanX_parent_row
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.NonTop.chainX_first_step
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.NonTop.lookupInnerX
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.NonTop.cleanStepX
