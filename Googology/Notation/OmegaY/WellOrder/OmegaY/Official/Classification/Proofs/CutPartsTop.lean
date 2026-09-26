/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/CutPartsTop.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CutPartsGen

set_option backward.do.legacy false

/-!
# `CutTopLookup` from the block profile, a row statement and a lookup

`CutTopLookup` (`CutPartsStep.lean`) is about a gap copy `v = (X, j + 1)` of `m` in an inner
column at the top of its run (the emit `j + 1` is not again a gap copy of `m`), when `m` has a
raw parent `m'`. This file splits it as `StepInner` splits `LeftCopy` and `JumpCopy`
(`ChainCorrStepInner.lean`):

* **The next emit** (`topNext`, proved from `CopyOrder`, `CopyEmitted`, `CopyFirst` and the
  proved `CopyMono`): the emit `j + 1` exists and is the non-cut copy of the node `m⁺` above
  `m`. So the raw parent of `v` is the left end of `v⁺`, in the column `φ(leg m⁺) = φ(m')`,
  and it is the highest node of that column at or below the row of `v` (the output is
  canonical).
* `CutBump` (open): `jump(row v, row v⁺) ≤ jump(row m, row m⁺)`. By the row law of both
  canonical mountains this is the jump condition of `CutTopLookup`.
* `CutLegLookup` (open): the highest node `pe` of `φ(m')` at or below the row of `v` is `m'`
  (left of `cr`), follows the chain of `m'` (in `cr`), or is a copy or gap copy of `m'` (right of
  `cr`). This is `LegLookup` of `StepInner` for a gap copy `v`.

`cutTopLookup_of_parts` proves `CutTopLookup` from these, and `wellFounded_of_cut_final`
states well-foundedness with the remaining open statements.

## Numerical tests (`reference/official/cut-parts.cjs`)

Counts: gap copies at the top of their run. No failure.

| sample | `CutTopNext` (proved here) | `CutBump` | `CutLegLookup` (`m'` `<`/`=`/`>` `cr`) |
|---|---:|---:|---:|
| standard S1–S3, S6, `n = 1,2,3` | 77316 | 77316 | 0 / 36504 / 40812 |
| legal, length ≤ 6, entries ≤ 6 | 25782 | 25782 | 0 / 19476 / 6306 |
| legal, length ≤ 5, entries ≤ 8 | 19686 | 19686 | 0 / 14946 / 4740 |
| random legal (`--random 20000,10,10,7`) | 80160 | 80160 | 24 / 51624 / 28512 |

With `--extraD 1` (standard samples) the counts of the other statements change only by the
extra scale; no failure either.
-/

namespace OmegaY.Official.Classification.Proofs.ChainCorr.CutParts

open Canonical Reserve Official Descent Classification Proofs

/-! ## The statements -/

/-- (open) At the top of a run of gap copies of `m` in an inner column, followed by the copy of
the node above `m`, the output column does not jump more than the source column. -/
def CutBump : Prop :=
  ∀ s n D M out ρ R t X x i es, Site s n D M out ρ R t X x i es → x < ρ.x0 →
    ∀ j (hj : j < es.length), cutOrigin es[j].2 = true →
    ∀ (hj1 : j + 1 < es.length), es[j + 1].2.src = Inner.up es[j].2.src →
      cutOrigin es[j + 1].2 = false →
    ∀ cv cv' cm cm' : Cell, cell? R ⟨X, j + 1⟩ = some cv → cell? R ⟨X, j + 1 + 1⟩ = some cv' →
      cell? M es[j].2.src = some cm → cell? M (Inner.up es[j].2.src) = some cm' →
      Row.jump cv.row cv'.row ≤ Row.jump cm.row cm'.row

/-- (open) At the top of a run of gap copies of `m` in an inner column, followed by the copy of
the node above `m`, the highest node of the image of the column of the raw parent `m'` of `m`
at or below the row of the gap copy matches `m'`. -/
def CutLegLookup : Prop :=
  ∀ s n D M out ρ R t X x i es, Site s n D M out ρ R t X x i es → x < ρ.x0 →
    ∀ j (hj : j < es.length), cutOrigin es[j].2 = true →
    ∀ (hj1 : j + 1 < es.length), es[j + 1].2.src = Inner.up es[j].2.src →
      cutOrigin es[j + 1].2 = false →
    ∀ m', rawParent M es[j].2.src = some m' → ∀ cv, cell? R ⟨X, j + 1⟩ = some cv →
    ∃ pe, highestAtMost R (mapColumn ρ.cr ((ρ.x0 - ρ.cr) * i) m'.column) cv.row = some pe ∧
      (m'.column < ρ.cr → pe = m') ∧
      (m'.column = ρ.cr → ∀ k m'', k ≤ D → MStep M k es[j].2.src m' → MStep M k m' m'' →
        ScaleReach R k pe m'') ∧
      (ρ.cr < m'.column → CutRel M R n ρ.cr ρ.x0 (official t.row) i pe m')

/-! ## The emit after a run -/

theorem setting_of_site {s : List Nat} {n D : Nat} {M : Mountain} {out : List Nat} {ρ : Root}
    {R : Mountain} {t : Cell} {X x i : Nat} {es : List (Emit × Origin)}
    (hS : Site s n D M out ρ R t X x i es) :
    ∃ col, Inner.Setting s n D M out ρ R col t := by
  obtain ⟨col, hcol, ht⟩ := hS.last
  exact ⟨col, hS.splice, hS.deg, hS.run, hS.canon, hcol, ht⟩

/-- **After the run of gap copies of `m` comes the non-cut copy of the node above `m`.** -/
theorem topNext (hA : CopyOrder) (hB : CopyEmitted) (hC2 : CopyFirst)
    {s : List Nat} {n D : Nat} {M : Mountain} {out : List Nat} {ρ : Root}
    {R : Mountain} {t : Cell} {X x i : Nat} {es : List (Emit × Origin)}
    (hS : Site s n D M out ρ R t X x i es) (hx : x < ρ.x0) {j : Nat} (hj : j < es.length)
    (hcut : cutOrigin es[j].2 = true)
    (hnot : ∀ hj' : j + 1 < es.length, es[j + 1].2 ≠ es[j].2)
    {c : Cell} (hc : cell? M (Inner.up es[j].2.src) = some c) :
    ∃ hj1 : j + 1 < es.length, es[j + 1].2.src = Inner.up es[j].2.src ∧
      cutOrigin es[j + 1].2 = false := by
  have hdat := hS.data
  have hV := build_valid_of_success hS.splice.build
  have hVR := build_valid_of_success hS.canon
  obtain ⟨hcx, _⟩ := mem_blockColumns_pos hS.xMem hS.iPos
  have hipos := hS.iPos
  have hbl : blockEmits M R ρ.cr ρ.x0 (official t.row) i x = .ok es := by
    simp only [blockEmits, ← hS.Xeq]
    exact hS.emits
  obtain ⟨cX, hRX, hcopyX⟩ := hS.copy
  obtain ⟨_, hcellsX⟩ := cells_of_copy hRX hcopyX hS.emits
  have hstrict : ∀ k k' (hk : k < es.length) (hk' : k' < es.length), k < k' →
      es[k].1.row < es[k'].1.row := by
    intro k k' hk hk' hkk
    obtain ⟨c1, hc1, hr1⟩ := hcellsX k hk
    obtain ⟨c2, hc2, hr2⟩ := hcellsX k' hk'
    have := cell_row_lt hVR hc1 hc2 (by omega)
    rw [hr1, hr2] at this
    exact stored_lt_iff.mp this
  -- the origin of the gap copy
  obtain ⟨hoc, ho1, cm, hcm⟩ := src_of_inner (ne_of_lt hx) hbl j hj
  set o := es[j].2.src with ho
  have hup : (Inner.up o).column = x := by simp [Inner.up, hoc]
  have hlt_row : cm.row < c.row := by
    have h1 : cell? M ⟨x, o.index⟩ = some cm := by rw [← hoc]; exact hcm
    have h2 : cell? M ⟨x, o.index + 1⟩ = some c := by rw [← hoc]; exact hc
    exact cell_row_lt hV h1 h2 (by omega)
  -- the non-cut copy of `m⁺`
  obtain ⟨k', hk', hk'src, hk'nc⟩ := hB s n D M out ρ R t hdat i hipos hS.iLt x es hcx hx hbl
    (Inner.up o) c hup (by simp [Inner.up]) hc
  have hck' : cell? M es[k'].2.src = some c := by rw [hk'src]; exact hc
  have hjk : j < k' := by
    by_contra hn
    have := copyMono s n D M out ρ R t hdat i hipos hS.iLt x es hcx hx hbl k' j hk' hj (by omega)
      c cm hck' hcm
    exact absurd hlt_row (not_lt.mpr this)
  have hj1 : j + 1 < es.length := by omega
  -- the origin `ν` of the emit `j + 1`
  obtain ⟨hνc, hν1, cν, hcν⟩ := src_of_inner (ne_of_lt hx) hbl (j + 1) hj1
  have hm1 := copyMono s n D M out ρ R t hdat i hipos hS.iLt x es hcx hx hbl j (j + 1) hj hj1
    (by omega) cm cν hcm hcν
  have hm2 := copyMono s n D M out ρ R t hdat i hipos hS.iLt x es hcx hx hbl (j + 1) k' hj1 hk'
    (by omega) cν c hcν hck'
  have hν' : cell? M ⟨x, es[j + 1].2.src.index⟩ = some cν := by rw [← hνc]; exact hcν
  have ho' : cell? M ⟨x, o.index⟩ = some cm := by rw [← hoc]; exact hcm
  have hu' : cell? M ⟨x, o.index + 1⟩ = some c := by rw [← hoc]; exact hc
  have hi1 := cell_index_le hV ho' hν' hm1
  have hi2 := cell_index_le hV hν' hu' hm2
  -- the first emit of an origin is non-cut
  have first : ∀ k (hk : k < es.length), ∃ k0, ∃ hk0 : k0 < es.length, k0 ≤ k ∧
      es[k0].2.src = es[k].2.src ∧ cutOrigin es[k0].2 = false := by
    intro k hk
    classical
    have hex : ∃ k1, ∃ hk1 : k1 < es.length, es[k1].2.src = es[k].2.src := ⟨k, hk, rfl⟩
    obtain ⟨hk0l, hk0src⟩ := Nat.find_spec hex
    have hmin : ∀ k1 (hk1 : k1 < es.length), k1 < Nat.find hex →
        es[k1].2.src ≠ es[Nat.find hex].2.src := by
      intro k1 hk1 hlt' heq'
      exact Nat.find_min hex hlt' ⟨hk1, heq'.trans hk0src⟩
    refine ⟨Nat.find hex, hk0l, ?_, hk0src, ?_⟩
    · by_contra hn
      exact Nat.find_min hex (by omega : k < Nat.find hex) ⟨hk, rfl⟩
    · exact hC2 s n D M out ρ R t hdat i hipos hS.iLt x es hcx hx hbl (Nat.find hex) hk0l hmin
  rcases Nat.lt_or_eq_of_le hi1 with hlt | heq
  · -- the origin of the emit `j + 1` is `m⁺`
    have hidx : es[j + 1].2.src.index = o.index + 1 := by omega
    have hνu : es[j + 1].2.src = Inner.up o :=
      ref_eq_of (by rw [hνc, hup]) (by simp [Inner.up, hidx])
    refine ⟨hj1, hνu, ?_⟩
    -- it is the first emit of `m⁺`
    obtain ⟨k0, hk0, hk0le, hk0src, hk0nc⟩ := first (j + 1) hj1
    rcases Nat.lt_or_eq_of_le hk0le with hlt0 | heq0
    · exfalso
      have hc0 : cell? M es[k0].2.src = some c := by rw [hk0src, hνu]; exact hc
      have := copyMono s n D M out ρ R t hdat i hipos hS.iLt x es hcx hx hbl k0 j hk0 hj
        (by omega) c cm hc0 hcm
      exact absurd hlt_row (not_lt.mpr this)
    · subst heq0
      exact hk0nc
  · -- the origin of the emit `j + 1` would be `m`: impossible
    exfalso
    have hνo : es[j + 1].2.src = o := ref_eq_of (by rw [hνc, hoc]) heq.symm
    have hne := hnot hj1
    have hnc : cutOrigin es[j + 1].2 = false := by
      cases hcj : cutOrigin es[j + 1].2
      · rfl
      · exfalso
        apply hne
        have h1 : ∃ r, es[j + 1].2 = .clean r true := by
          generalize es[j + 1].2 = o' at hcj
          cases o' with
          | clean r b => cases b <;> simp_all [cutOrigin]
          | plain r => simp [cutOrigin] at hcj
          | upper r => simp [cutOrigin] at hcj
        have h2 : ∃ r, es[j].2 = .clean r true := by
          generalize es[j].2 = o' at hcut
          cases o' with
          | clean r b => cases b <;> simp_all [cutOrigin]
          | plain r => simp [cutOrigin] at hcut
          | upper r => simp [cutOrigin] at hcut
        obtain ⟨r1, h1⟩ := h1
        obtain ⟨r2, h2⟩ := h2
        have hr1 : es[j + 1].2.src = r1 := by rw [h1]; rfl
        have hr2 : es[j].2.src = r2 := by rw [h2]; rfl
        rw [h1, h2]
        have : r1 = r2 := by rw [← hr1, ← hr2, hνo]
        rw [this]
    obtain ⟨k0, hk0, hk0le, hk0src, hk0nc⟩ := first j hj
    have hc0 : cell? M es[k0].2.src = some cm := by rw [hk0src]; exact hcm
    have hc1 : cell? M es[j + 1].2.src = some cm := by rw [hνo]; exact hcm
    have hA' := hA s n D M out ρ R t hdat i hipos hS.iLt x x es es hS.xMem hS.xMem hbl hbl k0 hk0
      (j + 1) hj1 hk0nc hnc cm cm hc0 hc1
    have := hstrict k0 (j + 1) hk0 hj1 (by omega)
    rw [hA'.2 rfl] at this
    exact lt_irrefl _ this

/-! ## The reduction -/

/-- **`CutTopLookup` from the block profile, `CutBump` and `CutLegLookup`.** -/
theorem cutTopLookup_of_parts (hA : CopyOrder) (hB : CopyEmitted) (hC2 : CopyFirst)
    (hBump : CutBump) (hLeg : CutLegLookup) : CutTopLookup := by
  intro s n D M out ρ R t X x i es hS hx j hj hcut hnot m' hm'
  have hV := build_valid_of_success hS.splice.build
  have hVR := build_valid_of_success hS.canon
  obtain ⟨col, hSet⟩ := setting_of_site hS
  obtain ⟨hcx, _⟩ := mem_blockColumns_pos hS.xMem hS.iPos
  obtain ⟨c, hc, hcl⟩ := Inner.rawParent_eq_some.mp hm'
  obtain ⟨hj1, hsrc1, hnc1⟩ := topNext hA hB hC2 hS hx hj hcut hnot hc
  -- the node above the gap copy is a copy of `m⁺`
  have hupat : Inner.CopyAt M R n ρ.cr ρ.x0 (official t.row) i ⟨X, j + 1 + 1⟩ es[j + 1].2 :=
    ⟨x, es, j + 1, hcx, hx, hS.xMem, hS.Xeq, rfl, hS.emits, hj1, rfl⟩
  obtain ⟨cu', ref', co, l', hcu', href', hco, hl', hrefc'⟩ :=
    Inner.copyAt_left hSet hS.iPos hS.iLt hupat
  rw [hsrc1] at hco
  have hcoc : co = c := Option.some.inj (hco.symm.trans hc)
  subst co
  have hll : l' = m' := Option.some.inj (hl'.symm.trans hcl)
  subst l'
  have hraw : rawParent R ⟨X, j + 1⟩ = some ref' :=
    Inner.rawParent_eq_some.mpr ⟨cu', hcu', href'⟩
  obtain ⟨⟨cv, hcv⟩, ⟨cpe, hcpe⟩, _⟩ := Inner.rawParent_cells hVR hraw
  have hham := Inner.canon_rawParent_hAM hS.canon (by simp) hcv hraw
  rw [hrefc'] at hham
  obtain ⟨pe, hpe, hlow, hroot, hcopy⟩ :=
    hLeg s n D M out ρ R t X x i es hS hx j hj hcut hj1 hsrc1 hnc1 m' hm' cv hcv
  have hpr : pe = ref' := Option.some.inj (hpe.symm.trans hham)
  subst pe
  refine ⟨ref', hraw, ?_, hlow, fun h => ⟨?_, hroot h⟩, hcopy⟩
  · -- the jump, by the row law of both mountains
    intro cu cm cpe' cm' hcu hcm hcpe' hcm'
    have hcuv : cu = cv := Option.some.inj (hcu.symm.trans hcv)
    subst cu
    have hcp : cpe' = cpe := Option.some.inj (hcpe'.symm.trans hcpe)
    subst cpe'
    obtain ⟨_, ho1, _⟩ := emitsT_good hS.emits es[j] (List.getElem_mem hj)
    have hb := hBump s n D M out ρ R t X x i es hS hx j hj hcut hj1 hsrc1 hnc1 cv cu' cm c hcv
      hcu' hcm hc
    have hR := Inner.jump_up_of_rowLaw hS.canon (r := ⟨X, j + 1⟩) (by simp) hcv hcu' href' hcpe
    have hM := Inner.jump_up_of_rowLaw hS.splice.build (by omega) hcm hc hcl hcm'
    omega
  · rw [Inner.highestAtMost_column hham, h, mapColumn_of_ge (le_refl _)]

/-! ## What is left -/

/-- **The four gap-copy statements of `ChainCorrCut.lean`** from `StepInner`, the block profile
(`CopyOrder`, `CopyEmitted`, `CopyFirst`), `BoundaryChain` and six open statements. -/
theorem cut_statements_final (hStep : StepInner) (hA : CopyOrder) (hB : CopyEmitted)
    (hC2 : CopyFirst) (hBC : BoundaryChain) (hBump : CutBump) (hLeg : CutLegLookup)
    (hLow : CutRunLow) (hHigh : CutRunHigh) (hOR : CutOriginReach) (hJT : CutJumpTop) :
    StepCut ∧ CutJump ∧ CutStartCopy ∧ CutStartRoot :=
  cut_statements_of_rest hStep hA hC2 hBC (cutTopLookup_of_parts hA hB hC2 hBump hLeg) hLow hHigh
    hOR hJT

/-- **Well-foundedness of the official expansion** from the reconstruction, the five
statements of `ChainCorrRegions.lean`, the block profile, `BoundaryChain` and the six open
gap-copy statements. -/
theorem wellFounded_of_cut_final (hrec : Dimension.BlockReconstruction) (hStep : StepInner)
    (hLeg0 : StartLeg) (hJ : StartJump) (hCopy : StartCopy) (hRoot : StartRoot)
    (hA : CopyOrder) (hB : CopyEmitted) (hC2 : CopyFirst) (hBC : BoundaryChain)
    (hBump : CutBump) (hLeg : CutLegLookup) (hLow : CutRunLow) (hHigh : CutRunHigh)
    (hOR : CutOriginReach) (hJT : CutJumpTop) : WellFounded Step :=
  wellFounded_of_cut_rest hrec hStep hLeg0 hJ hCopy hRoot hA hC2 hBC
    (cutTopLookup_of_parts hA hB hC2 hBump hLeg) hLow hHigh hOR hJT

end OmegaY.Official.Classification.Proofs.ChainCorr.CutParts

#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.CutParts.topNext
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.CutParts.cutTopLookup_of_parts
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.CutParts.cut_statements_final
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.CutParts.wellFounded_of_cut_final
