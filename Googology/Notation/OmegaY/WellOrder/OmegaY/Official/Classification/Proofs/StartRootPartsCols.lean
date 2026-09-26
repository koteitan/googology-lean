/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/StartRootPartsCols.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.StartRootPartsBase

set_option backward.do.legacy false

/-!
# The copies of the column `x₀`

The block `m` (with `m < n`) copies the column `x₀` of `M(s)` to the column
`X = x₀ + w·m` of the output (`w = x₀ - cr`); for `m ≥ 1` this is the boundary column
`cr + w·(m + 1)` of the block `m + 1`. This file collects the cells of these columns
(`bcol`) and proves the step of the chain from a node of the upper part (`upper_parent`):
the upper part of a copy of `x₀` is the upper part (rows `≥ τ`) of the root column `cr`, with
the same rows and legs left of `cr`, so a node of the upper part has the raw parent of its
origin.
-/

namespace OmegaY.Official.Classification.Proofs.ChainCorr.SRParts

open Canonical Reserve Official Descent Classification Proofs
open ChainCorr.Inner

/-- The splice data fix the top `t` of the last column. -/
theorem spliceData_facts {s : List Nat} {n D : Nat} {M : Mountain} {out : List Nat}
    {ρ : Root} {R : Mountain} {t : Cell} (hd : SpliceData s n D M out ρ R t) :
    ρ.x0 = M.size - 1 ∧ ρ.cr < ρ.x0 ∧
      ColumnsInv M n ρ.cr (ρ.x0 - ρ.cr) ρ.x0 (official t.row) R ∧
      R.size = ρ.x0 + n * (ρ.x0 - ρ.cr) := by
  obtain ⟨col', t', hcol', ht', hx0, hcrx, hinv⟩ := spliceCase_data hd.splice hd.run
  have htt : t' = t := by
    obtain ⟨col, hcol, ht⟩ := hd.last
    have : col' = col := Option.some.inj (hcol'.symm.trans hcol)
    subst this
    exact Option.some.inj (ht'.symm.trans ht)
  subst t'
  refine ⟨hx0, hcrx, hinv, ?_⟩
  rw [build_size hd.canon]
  exact Reconstruction.expand_length_splice hd.splice.build hd.splice.run hd.splice.root
    hd.splice.copies

/-- The context of the copy of `x₀` in block `m`. -/
abbrev bctx (M R : Mountain) (cr x0 m : Nat) : Context :=
  ctxAt M R x0 m cr (x0 - cr) x0 (x0 + (x0 - cr) * m)

/-- **The cells of a copy of `x₀`.** -/
theorem bcol {s : List Nat} {n D : Nat} {M : Mountain} {out : List Nat} {ρ : Root}
    {R : Mountain} {t : Cell} (hd : SpliceData s n D M out ρ R t) {m : Nat} (hm : m < n)
    {esB : List (Emit × Origin)}
    (hes : blockEmits M R ρ.cr ρ.x0 (official t.row) m ρ.x0 = .ok esB) :
    ρ.x0 + (ρ.x0 - ρ.cr) * m < R.size ∧
    ∃ c, R[ρ.x0 + (ρ.x0 - ρ.cr) * m]? = some c ∧
      copyColumn (bctx M R ρ.cr ρ.x0 m) (official t.row) = .ok c ∧
      c.size = esB.length + 1 ∧
      ∀ k (hk : k < esB.length), ∃ cell : Cell,
        cell? R ⟨ρ.x0 + (ρ.x0 - ρ.cr) * m, k + 1⟩ = some cell ∧
        cell.row = stored esB[k].1.row ∧ ∃ ref : Ref, cell.left = some ref ∧
          ref.column = legColumn (bctx M R ρ.cr ρ.x0 m) esB[k].1 := by
  obtain ⟨_, hcrx, hinv, hRs⟩ := spliceData_facts hd
  have hXR : ρ.x0 + (ρ.x0 - ρ.cr) * m < R.size := by
    rw [hRs]
    have : (ρ.x0 - ρ.cr) * m < n * (ρ.x0 - ρ.cr) := by
      rw [Nat.mul_comm n]; exact Nat.mul_lt_mul_of_pos_left hm (by omega)
    omega
  refine ⟨hXR, ?_⟩
  obtain ⟨i', x', _, hx', hXeq, hcopy⟩ := hinv.2.2 _ hXR (by omega)
  obtain ⟨hii, hxx⟩ := block_unique_boundary hcrx hx' hXeq
  subst hii
  subst hxx
  have hR : R[ρ.x0 + (ρ.x0 - ρ.cr) * i']? = some R[ρ.x0 + (ρ.x0 - ρ.cr) * i'] :=
    Array.getElem?_eq_getElem hXR
  have hes' : emitsT (bctx M R ρ.cr ρ.x0 i') (official t.row) = .ok esB := hes
  obtain ⟨hsz, hcells⟩ := cells_of_copy hR hcopy hes'
  refine ⟨_, hR, hcopy, hsz, fun k hk => ?_⟩
  obtain ⟨es', hes'', hasm⟩ := copyColumn_emitsT hcopy
  have hee : es' = esB := Except.ok.inj (hes''.symm.trans hes')
  subst hee
  obtain ⟨_, hc⟩ := assemble_spec hasm
  obtain ⟨cell, hcell, hrow, ref, hl, hlc⟩ := hc k (by simpa using hk)
  simp only [List.getElem_map] at hrow hlc
  refine ⟨cell, ?_, hrow, ref, hl, hlc⟩
  simp [cell?, hR, hcell]

/-- The emits of a copy of `x₀` satisfy `Good` (`emitsT_good`); the source column of an
upper emit is `cr`, of a lower emit `x₀`. -/
theorem bsrc {M R : Mountain} {cr x0 m : Nat} {τ : Row} {esB : List (Emit × Origin)}
    (hes : blockEmits M R cr x0 τ m x0 = .ok esB) {k : Nat} (hk : k < esB.length) :
    esB[k].2.src.column = (if esB[k].2.isUpper then cr else x0) ∧ 1 ≤ esB[k].2.src.index ∧
      ∃ cv, cell? M esB[k].2.src = some cv ∧
        ((∃ l : Ref, cv.left = some l ∧ esB[k].1.leftColumn = some l.column) ∨
          (esB[k].1.leftColumn = none ∧ official cv.row = 0 ∧ esB[k].2.isUpper = false)) := by
  obtain ⟨h1, h2, cv, h3, h4⟩ := emitsT_good hes esB[k] (List.getElem_mem hk)
  refine ⟨?_, h2, cv, h3, h4⟩
  rw [h1]
  split <;> simp [upperColumn, ctxAt]

/-- **The raw parent of a node of the upper part of a copy of `x₀`** is the raw parent of its
origin, and the two nodes have the same row. -/
theorem upper_parent {s : List Nat} {n D : Nat} {M : Mountain} {out : List Nat} {ρ : Root}
    {R : Mountain} {t : Cell} (hd : SpliceData s n D M out ρ R t) {m : Nat} (hm : m < n)
    {esB : List (Emit × Origin)}
    (hes : blockEmits M R ρ.cr ρ.x0 (official t.row) m ρ.x0 = .ok esB) {k : Nat}
    (hk : k < esB.length) {ν : Ref} (hν : esB[k].2 = .upper ν) {m' : Ref}
    (hpar : rawParent M ν = some m') :
    rawParent R ⟨ρ.x0 + (ρ.x0 - ρ.cr) * m, k + 1⟩ = some m' ∧
      ∃ cb cν, cell? R ⟨ρ.x0 + (ρ.x0 - ρ.cr) * m, k + 1⟩ = some cb ∧
        cell? M ν = some cν ∧ cb.row = cν.row := by
  have hV := build_valid_of_success hd.splice.build
  obtain ⟨_, hcrx, hinv, _⟩ := spliceData_facts hd
  obtain ⟨_, c, _, _, _, hcells⟩ := bcol hd hm hes
  have hes' : emitsT (bctx M R ρ.cr ρ.x0 m) (official t.row) = .ok esB := hes
  -- the row of an upper node is the row of its origin
  have hrow : ∀ j (hj : j < esB.length) (μ : Ref), esB[j].2 = .upper μ →
      ∃ cb cμ, cell? R ⟨ρ.x0 + (ρ.x0 - ρ.cr) * m, j + 1⟩ = some cb ∧ cell? M μ = some cμ ∧
        cb.row = cμ.row ∧ ∃ ref : Ref, cb.left = some ref ∧
          ref.column = legColumn (bctx M R ρ.cr ρ.x0 m) esB[j].1 := by
    intro j hj μ hμ
    obtain ⟨cb, hcb, hcbrow, ref, hl, hlc⟩ := hcells j hj
    obtain ⟨cμ, hcμ, hr⟩ := emitsT_upper_row hes' esB[j] (List.getElem_mem hj)
      (by rw [hμ]; rfl)
    rw [hμ] at hcμ
    obtain ⟨_, hidx, _⟩ := bsrc hes hj
    rw [hμ] at hidx
    refine ⟨cb, cμ, hcb, hcμ, ?_, ref, hl, hlc⟩
    rw [hcbrow, hr, stored_official (one_le_row hV hcμ hidx)]
  obtain ⟨cb, cν, hcb, hcν, hbrow, _⟩ := hrow k hk ν hν
  refine ⟨?_, cb, cν, hcb, hcν, hbrow⟩
  -- the next emit is the upper copy of `up ν`
  obtain ⟨cu, hcu, hlu⟩ := rawParent_eq_some.mp hpar
  obtain ⟨hk1, hnext⟩ := emitsT_upper_next (ctx := bctx M R ρ.cr ρ.x0 m) hV hes' hk hν hcu
  obtain ⟨cb', cu', hcb', hcu', hrow', ref, hl, hlc⟩ := hrow (k + 1) hk1 (up ν) hnext
  rw [hcu] at hcu'
  cases hcu'
  -- the leg column of the next emit is the column of `m'`, left of `cr`
  obtain ⟨hsc, _, cv, hcv, hleft⟩ := bsrc hes hk1
  rw [hnext] at hsc hcv hleft
  simp only [Origin.isUpper, if_true, Origin.src] at hsc hcv hleft
  rw [hcu] at hcv
  cases hcv
  have hm'lt : m'.column < ρ.cr := by
    have := left_lt_of_valid hV hcu hlu
    simpa [up, ← hsc] using this
  have hlc' : ref.column = m'.column := by
    rw [hlc]
    rcases hleft with ⟨l, hl', hlcol⟩ | ⟨_, _, hf⟩
    · rw [hlu] at hl'
      cases hl'
      simp only [legColumn, hlcol, ctxAt]
      rw [if_neg (by omega)]
    · simp at hf
  have hraw : rawParent R ⟨ρ.x0 + (ρ.x0 - ρ.cr) * m, k + 1⟩ = some ref :=
    rawParent_of_up (u := ⟨ρ.x0 + (ρ.x0 - ρ.cr) * m, k + 1⟩) hcb' hl
  have heq := left_match (a := ν) (b := ⟨ρ.x0 + (ρ.x0 - ρ.cr) * m, k + 1⟩)
    hd.splice.build hd.canon hinv.1 hcu hcb' hlu hl hrow'.symm
    hlc'.symm (by omega)
  rw [hraw, heq]

/-- An upper node of a copy of `x₀` has the step of its origin in its chain. -/
theorem upper_reach {s : List Nat} {n D : Nat} {M : Mountain} {out : List Nat} {ρ : Root}
    {R : Mountain} {t : Cell} (hd : SpliceData s n D M out ρ R t) {m : Nat} (hm : m < n)
    {esB : List (Emit × Origin)}
    (hes : blockEmits M R ρ.cr ρ.x0 (official t.row) m ρ.x0 = .ok esB) {k : Nat}
    (hk : k < esB.length) {ν : Ref} (hν : esB[k].2 = .upper ν) {kk : Nat} {m' : Ref}
    (hst : MStep M kk ν m') :
    ScaleReach R kk ⟨ρ.x0 + (ρ.x0 - ρ.cr) * m, k + 1⟩ m' := by
  have hVR := build_valid_of_success hd.canon
  obtain ⟨_, hcrx, hinv, _⟩ := spliceData_facts hd
  obtain ⟨hpar, cν, cm', hcν, hcm', hj, _⟩ := hst
  obtain ⟨hraw, cb, cν', hcb, hcν', hrow⟩ := upper_parent hd hm hes hk hν hpar
  rw [hcν] at hcν'
  cases hcν'
  have hV := build_valid_of_success hd.splice.build
  have hm'x : m'.column < ρ.x0 := by
    have hνc : ν.column = ρ.cr := by
      have := (bsrc hes hk).1
      rw [hν] at this
      simpa [Origin.isUpper, Origin.src] using this
    have := (ChainCorr.Inner.rawParent_cells hV hpar).2.2
    omega
  have hcm'R : cell? R m' = some cm' := by rw [← cell?_congr hinv.1 hm'x]; exact hcm'
  exact reach_one hVR hraw hcb hcm'R (by rw [hrow]; exact hj)

end OmegaY.Official.Classification.Proofs.ChainCorr.SRParts
