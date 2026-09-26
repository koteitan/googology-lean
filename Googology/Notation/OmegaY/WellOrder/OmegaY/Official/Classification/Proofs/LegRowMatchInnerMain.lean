/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/LegRowMatchInnerMain.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.LegRowMatchInnerRun
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.LegRowMatchInnerAsc
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.ChainCorrLegLeftJump

set_option backward.do.legacy false

/-!
# `LegRowMatchInner` holds

`LegRowMatchInner` (`ChainCorrLegLeftJump.lean`): for a region node `u = (X, j + 1)` of block
`i ≥ 1` whose origin `o` (in `M(s)`) is not a gap copy and has its leg `l` right of `c_r`, if the
column `l` of `M(s)` has a real node at the row of `o`, the output column `l + w·i` has a real
node at the row of `u`.

The proof of `LegJump.legRowMatch_inner` used the false block profile `CopyOrder` for one
comparison: the copy of `o` (column `x`) and the copy of the node `o'` of `l` at the row
`r = row o` (column `l`) get the same row. Here this comparison is proved directly:

* both rows are given by the row formula `RowΨ` (`blockRowΨ`, `LegRowMatchInnerRun.lean`):
  `Ψ E (topA ctx_x) false (k + 1) L L r` and `Ψ E (topA ctx_l) false (k + 1) L L r` for the
  same first item `(k + 1, L)` of `r` (lower part), or `r` for both (upper part);
* `Ψ E top r` reads `top` only on the regions `S ∋ r` whose root top `ρ` is below `r`
  (`Ψ_congr`); there `topA ctx_x S = topA ctx_l S`, because `x` ascends in `S` iff `l` does
  (`ascAgree`, `LegRowMatchInnerAsc.lean`: `o` is a node of `x` above `ρ` whose leg is `l`).

The node `o'` has a non-cut copy (`NoMA.copyEmitted`, proved).

Main results:

* `copyRowLeg`: the rows of the non-cut copies of `o` and `o'` are equal (the equal part of
  `NoMA.CopyOrderLeg`).
* `legRowMatchInner : ChainCorr.LegLeft.LegRowMatchInner` (no hypothesis).
* `startJumpGe : ChainCorr.LegLeft.StartJumpGe` and `startJump : ChainCorr.StartJump`
  (with `LiftLegRight` from `LiftLegRightProof.lean`).
-/

namespace OmegaY.Official.Classification.Proofs.CopyShape.InnerRow

open Canonical Reserve Official Descent Classification Proofs
open ChainCorr ChainCorr.LegJump

/-- Two rows given by `RowΨ` for the same origin row are equal when the two root-top functions
agree on the regions that `Ψ` reads (only needed in the lower part). -/
theorem rowΨ_eq {E : Env} {top₁ top₂ : Nat → Row → Option (Ref × Cell)} {τ : Row}
    {x₁ x₂ : Nat} {src₁ src₂ : Ref} {row₁ row₂ r : Row}
    (h₁ : RowΨ E top₁ τ x₁ src₁ row₁ r) (h₂ : RowΨ E top₂ τ x₂ src₂ row₂ r)
    (ht₁ : ∀ d S, top₁ d S = none ∨ top₁ d S = topIn E.M E.cr d S)
    (ht₂ : ∀ d S, top₂ d S = none ∨ top₂ d S = topIn E.M E.cr d S)
    (hag : r < τ → ∀ d S ρ, inRegion (d + 2) S r = true → topIn E.M E.cr (d + 2) S = some ρ →
      official ρ.2.row < r → top₁ (d + 2) S = top₂ (d + 2) S) : row₁ = row₂ := by
  rcases h₁ with ⟨hr, _, q, hq, hin, hrow⟩ | ⟨hr, hrow⟩ <;>
    rcases h₂ with ⟨hr', _, q', hq', hin', hrow'⟩ | ⟨hr', hrow'⟩
  · have hqq := Recon.JumpLaw.lowerItems_eq_of_common hq hq' hin hin'
    subst hqq
    obtain ⟨k, j, _, _, hk⟩ := Recon.RowLaw.mem_lowerItems hq
    rw [hrow, hrow', hk]
    rw [hk] at hin
    exact Ψ_congr E top₁ top₂ r ht₁ ht₂ (hag hr) k false _ _ hin (fun h => by cases h)
  · exact absurd hr (not_lt.mpr hr')
  · exact absurd hr' (not_lt.mpr hr)
  · rw [hrow, hrow']

theorem topA_congr {ctx ctx' : Context} {d : Nat} {S : Row} {ρ : Ref × Cell}
    (h : topIn ctx.source ctx.rootColumn d S = some ρ)
    (h' : topIn ctx'.source ctx'.rootColumn d S = some ρ) (hb : ascB ctx ρ = ascB ctx' ρ) :
    topA ctx d S = topA ctx' d S := by
  unfold topA
  rw [h, h']
  simp only [hb]

/-- **The copies of a node and of the node of its leg column at the same row have the same
row** (the equal part of `NoMA.CopyOrderLeg`, for a leg right of `c_r`). -/
theorem copyRowLeg {s : List Nat} {n D : Nat} {M : Mountain} {out : List Nat} {ρ : Root}
    {R : Mountain} {t : Cell} (hS : SpliceData s n D M out ρ R t) {i : Nat} (hi0 : 0 < i)
    (hi : i < n + 1) {y y' : Nat} (hy : y ∈ blockColumns ρ.cr ρ.x0 n i)
    (hy' : y' ∈ blockColumns ρ.cr ρ.x0 n i) {es es' : List (Emit × Origin)}
    (hes : blockEmits M R ρ.cr ρ.x0 (official t.row) i y = .ok es)
    (hes' : blockEmits M R ρ.cr ρ.x0 (official t.row) i y' = .ok es')
    {k : Nat} (hk : k < es.length) {k' : Nat} (hk' : k' < es'.length)
    (hnc : cutOrigin es[k].2 = false) (hnc' : cutOrigin es'[k'].2 = false)
    {c c' : Cell} {lr : Ref} (hc : cell? M es[k].2.src = some c)
    (hc' : cell? M es'[k'].2.src = some c') (hl : c.left = some lr) (hlr : lr.column = y')
    (hcr : ρ.cr < y') (hrow : c.row = c'.row) : es[k].1.row = es'[k'].1.row := by
  obtain ⟨hcy, _⟩ := mem_blockColumns_pos hy hi0
  have hΨ := blockRowΨ hS hi0 hi hy hes es[k] (List.getElem_mem hk) hnc c hc
  have hΨ' := blockRowΨ hS hi0 hi hy' hes' es'[k'] (List.getElem_mem hk') hnc' c' hc'
  rw [← hrow] at hΨ'
  refine rowΨ_eq hΨ hΨ' (topA_cases _) (topA_cases _) ?_
  intro hτ d S ρ' hin hρ' hlt
  -- the origin is in the column `y`
  have hcol : es[k].2.src.column = y := by
    rcases hΨ with ⟨_, hcol, _⟩ | ⟨hτ', _⟩
    · exact hcol
    · exact absurd hτ (not_lt.mpr hτ')
  obtain ⟨ρr, ρc⟩ := ρ'
  have hb := hS.splice.build
  have hV := build_valid_of_success hb
  have hidx : 1 ≤ es[k].2.src.index := by
    have hpos := one_le_row hV hc
    by_contra hn
    have h0 : es[k].2.src.index = 0 := by omega
    obtain ⟨_, hidx, _⟩ := emitsT_good (τ := official t.row)
      (ctx := ctxAt M R y i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 (y + (ρ.x0 - ρ.cr) * i)) hes _
      (List.getElem_mem hk)
    omega
  have hcell : cell? M ⟨y, es[k].2.src.index⟩ = some c := by
    rw [← hcol]; exact hc
  have hρ'' : topIn M ρ.cr (d + 2) S = some (ρr, ρc) := hρ'
  have hiff := ascAgree hb hcy hidx hcell hl (by rw [hlr]; exact hcr) hρ'' hin hlt
    (ctxAt M R y i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 (y + (ρ.x0 - ρ.cr) * i))
    (ctxAt M R y' i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 (y' + (ρ.x0 - ρ.cr) * i)) rfl rfl rfl rfl rfl
    (by rw [hlr]; rfl)
  have hbb : ascB (ctxAt M R y i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 (y + (ρ.x0 - ρ.cr) * i)) (ρr, ρc) =
      ascB (ctxAt M R y' i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 (y' + (ρ.x0 - ρ.cr) * i)) (ρr, ρc) := by
    apply Bool.eq_iff_iff.mpr
    rw [ascB_iff, ascB_iff]
    exact hiff
  exact topA_congr hρ'' hρ'' hbb

/-- **`LegRowMatchInner` holds** (no hypothesis). The proof of `LegJump.legRowMatch_inner`, with
`CopyEmitted` from `NoMA.copyEmitted` and the comparison of the rows from `copyRowLeg` instead of
the false `CopyOrder`. -/
theorem legRowMatchInner : ChainCorr.LegLeft.LegRowMatchInner := by
  intro s n D M out ρ R t X x i es hS j hj hnc cu cv ref l pe pa cpe cpa hL hlt hsm
  obtain ⟨jn, cn, hjn0, hcn, hcnrow⟩ := hsm
  have hdat := hS.data
  have hV := build_valid_of_success hS.splice.build
  obtain ⟨col', t', hcol', ht', _, hcrx, hinv⟩ := spliceCase_data hS.splice hS.run
  have htt : t' = t := by
    obtain ⟨col, hcol, ht⟩ := hS.last
    have : col' = col := Option.some.inj (hcol'.symm.trans hcol)
    subst this
    exact Option.some.inj (ht'.symm.trans ht)
  subst t'
  obtain ⟨hcx, hxx⟩ := mem_blockColumns_pos hS.xMem hS.iPos
  have hipos := hS.iPos
  have hblx : blockEmits M R ρ.cr ρ.x0 (official t.row) i x = .ok es := by
    simp only [blockEmits, ← hS.Xeq]
    exact hS.emits
  have himg := leg_image hS hj hL
  rw [mapColumn_of_ge (le_of_lt hlt)] at himg
  obtain ⟨hsrc, _, _, _, _⟩ := emitsT_good hS.emits es[j] (List.getElem_mem hj)
  have hly : l.column < es[j].2.src.column := left_lt_of_valid hV hL.hcv hL.hl
  have hsrcle : es[j].2.src.column ≤ ρ.x0 := by
    rw [hsrc]
    split
    · exact upperColumn_le hcrx.le hxx
    · exact hxx
  have hyx : l.column < ρ.x0 := by omega
  have hymem : l.column ∈ blockColumns ρ.cr ρ.x0 n i := by
    unfold blockColumns
    rw [if_neg (by omega)]
    simp only [List.mem_range'_1]
    split <;> omega
  -- the output column `l + w·i`
  obtain ⟨_, _, colL, hcolL, _, _, _⟩ := highestAtMost_spec hL.hpe
  have hL0 : ρ.x0 ≤ ref.column := by
    rw [himg]
    have : ρ.x0 - ρ.cr ≤ (ρ.x0 - ρ.cr) * i := Nat.le_mul_of_pos_right _ hipos
    omega
  obtain ⟨hLsz, _⟩ := column_of_getElem? hcolL
  obtain ⟨i', x', _, hx', hLeq, hcopyL⟩ := hinv.2.2 ref.column hLsz hL0
  obtain ⟨hii, hxy⟩ := blockCol_unique_inner hcrx hlt hyx hipos hx' (by rw [← himg]; exact hLeq)
  subst i' x'
  have hcolL' : R[ref.column]? = some R[ref.column] := Array.getElem?_eq_getElem hLsz
  obtain ⟨esl, hesl, _⟩ := copyColumn_emitsT hcopyL
  obtain ⟨_, hcellsL⟩ := cells_of_copy hcolL' hcopyL hesl
  have hbl : blockEmits M R ρ.cr ρ.x0 (official t.row) i l.column = .ok esl := by
    have h' : l.column + (ρ.x0 - ρ.cr) * i = ref.column := himg.symm
    simp only [blockEmits, h']
    exact hesl
  -- the row of `u`
  obtain ⟨cX, hRX, hcopyX⟩ := hS.copy
  obtain ⟨_, hcellsX⟩ := cells_of_copy hRX hcopyX hS.emits
  obtain ⟨cellu, hcellu, hrowu⟩ := hcellsX j hj
  have hrowcu : cu.row = stored es[j].1.row := by
    rw [Option.some.inj (hL.hcu.symm.trans hcellu)]
    exact hrowu
  -- the non-cut copy of the node `(l, σ)`
  obtain ⟨k, hk, hksrc, hknc⟩ := NoMA.copyEmitted s n D M out ρ R t hdat i hipos hS.iLt l.column
    esl hlt hyx hbl ⟨l.column, jn⟩ cn rfl hjn0 hcn
  have hcnk : cell? M esl[k].2.src = some cn := by rw [hksrc]; exact hcn
  have hrowe := copyRowLeg hdat hipos hS.iLt hS.xMem hymem hblx hbl hj hk hnc hknc hL.hcv hcnk
    hL.hl rfl hlt hcnrow.symm
  obtain ⟨cell, hcell, hrow⟩ := hcellsL k hk
  exact ⟨k + 1, cell, by omega, hcell, by rw [hrow, hrowcu, hrowe]⟩

/-- **`StartJumpGe` holds** (no hypothesis). -/
theorem startJumpGe : ChainCorr.LegLeft.StartJumpGe :=
  ChainCorr.LegLeft.startJumpGe_of_inner legRowMatchInner

/-- **`StartJump` holds** (no hypothesis): `LiftLegRight` (`LiftLegRightProof.lean`) gives
`PlainLegLeftRow`, and `LegRowMatchInner` is proved above. -/
theorem startJump : ChainCorr.StartJump :=
  ChainCorr.LegLeft.startJump_of_inner Recon.LowerPB.LiftLegPf.plainLegLeftRow legRowMatchInner

end OmegaY.Official.Classification.Proofs.CopyShape.InnerRow

#print axioms OmegaY.Official.Classification.Proofs.CopyShape.InnerRow.copyRowLeg
#print axioms OmegaY.Official.Classification.Proofs.CopyShape.InnerRow.legRowMatchInner
#print axioms OmegaY.Official.Classification.Proofs.CopyShape.InnerRow.startJumpGe
#print axioms OmegaY.Official.Classification.Proofs.CopyShape.InnerRow.startJump
#print axioms OmegaY.Official.Recon.LowerPB.LiftLegPf.liftLegRight
