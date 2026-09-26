/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/CopyShape.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CopyShapeRun

set_option backward.do.legacy false

/-!
# `CopyOrder`, `CopyEmitted`, `CopyFirst` from MA, MD, MH

The three column-shape statements of `ChainCorrStartCopy.lean` (and the two of
`ChainCorrStepInner.lean`, `ChainCorr.Inner.CopyEmitted` and `ChainCorr.Inner.CopyFirst`)
follow from three facts about the items reached by the rule in the copied columns of the
blocks `i ≥ 1` (`MAHolds`, `MDHolds`, `MHHolds`, see `CopyShapeItems.lean`):

* `copyOrder_of_facts`: every non-cut emit of block `i` has the row `Φ(σ)` of its origin row
  `σ` (lower part) or `σ` itself (upper part), with one strictly increasing map `Φ` for the
  whole block (`CopyShapeMaps.lean`);
* `copyEmitted_of_facts`: every node of an inner column is the origin of a non-cut emit;
* `copyFirst_of_facts`: no gap copy comes before the non-cut emit of the same origin.

## Numerical tests

`reference/official/copy-shape.cjs` checks MA, MD, MH on every reached item of level `≥ 2`
of the blocks `i ≥ 1`, and the row formula (`RowOK`) on every non-cut emit:

| sample | MA | MD | MH | formula | failures |
|---|---:|---:|---:|---:|---:|
| standard S1–S3, S6, `n = 1,2,3` | 48 | 270272 | 26334 | 858387 | 0 |
| legal, length ≤ 6, entries ≤ 6 | 0 | 121151 | 17394 | 266796 | 0 |
| legal, length ≤ 5, entries ≤ 8 | 0 | 257275 | 21867 | 176334 | 0 |
| random legal (`--random 20000,10,10,7`) | 6 | 2015617 | 93114 | 767328 | 0 |

In all tests MH even holds without the generations: `h_ρ ≤ h_q`.

MD is proved in `CopyShapeMD.lean` (`mdHolds`), so the three statements follow from MA and MH
alone (`copyOrder_of_MA_MH`, `copyEmitted_of_MA_MH`, `copyFirst_of_MA_MH` there). MA and MH
remain open.
-/

namespace OmegaY.Official.Classification.Proofs.CopyShape

open Canonical Reserve Official Descent Classification Proofs

/-! ## The facts, for every copied column of a block `i ≥ 1` -/

/-- A fact about the context of every copied column of every block `i ≥ 1`. -/
def BlockFact (P : Context → Row → Prop) : Prop :=
  ∀ s n D M out ρ R t, ChainCorr.SpliceData s n D M out ρ R t → ∀ i, 0 < i → i < n + 1 →
    ∀ y, y ∈ blockColumns ρ.cr ρ.x0 n i →
      P (ctxAt M R y i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 (y + (ρ.x0 - ρ.cr) * i)) (official t.row)

/-- (MA, open) -/
def MAHolds : Prop := BlockFact FactMA
/-- (MD, proved: `mdHolds` in `CopyShapeMD.lean`) -/
def MDHolds : Prop := BlockFact FactMD
/-- (MH, open) -/
def MHHolds : Prop := BlockFact FactMH

/-! ## Tools -/

theorem realNodes_extract' {R : Mountain} {X c : Nat} (hc : c < X) :
    realNodes (R.extract 0 X) c = realNodes R c := by
  have h : (R.extract 0 X)[c]? = R[c]? := by
    simp only [Array.getElem?_extract]
    by_cases hs : c < R.size
    · simp [hc, hs]
    · rw [Array.getElem?_eq_none (by omega)]
      simp [hc]
      omega
  unfold realNodes
  rw [h]

theorem topIn_extract' {R : Mountain} {X c d : Nat} {S : Row} (hc : c < X) :
    topIn (R.extract 0 X) c d S = topIn R c d S := by
  unfold topIn
  rw [realNodes_extract' hc]

/-- The shape of the copied column `y` of block `i ≥ 1`. -/
theorem column_shape (hMA : MAHolds) (hMD : MDHolds) (hMH : MHHolds) {s : List Nat} {n D : Nat}
    {M : Mountain} {out : List Nat} {ρ : Root} {R : Mountain} {t : Cell}
    (hS : ChainCorr.SpliceData s n D M out ρ R t) {i : Nat} (hi0 : 0 < i) (hi : i < n + 1)
    {y : Nat} (hy : y ∈ blockColumns ρ.cr ρ.x0 n i) {es : List (Emit × Origin)}
    (hes : ChainCorr.blockEmits M R ρ.cr ρ.x0 (official t.row) i y = .ok es) :
    (∀ p ∈ es, ChainCorr.cutOrigin p.2 = false → ∀ c, cell? M p.2.src = some c →
      RowOK ⟨M, R, ρ.cr, ρ.x0, ρ.cr + (ρ.x0 - ρ.cr) * i, i⟩ (official t.row) p.1.row
        (official c.row)) ∧
    es.Pairwise NCB ∧
    (y ≠ ρ.x0 → ∀ (p : Ref) (c : Cell), p.column = y → 1 ≤ p.index → cell? M p = some c →
        ∃ q ∈ es, q.2.src = p ∧ ChainCorr.cutOrigin q.2 = false) := by
  have hV := build_valid_of_success hS.splice.build
  obtain ⟨hcy, _⟩ := ChainCorr.mem_blockColumns_pos hy hi0
  have hbnd : ∀ d T, topIn (ctxAt M R y i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 (y + (ρ.x0 - ρ.cr) * i)).result
      (ctxAt M R y i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 (y + (ρ.x0 - ρ.cr) * i)).boundary d T =
      topIn R (ρ.cr + (ρ.x0 - ρ.cr) * i) d T := by
    intro d T
    exact topIn_extract' (by show ρ.cr + (ρ.x0 - ρ.cr) * i < y + (ρ.x0 - ρ.cr) * i; omega)
  obtain ⟨h1, h2, h3⟩ := emitsT_shape (ctxAt M R y i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 (y + (ρ.x0 - ρ.cr) * i))
    (official t.row) R (ρ.cr + (ρ.x0 - ρ.cr) * i) hV (show 1 ≤ i from hi0) hbnd
    (hMA s n D M out ρ R t hS i hi0 hi y hy) (hMD s n D M out ρ R t hS i hi0 hi y hy)
    (hMH s n D M out ρ R t hS i hi0 hi y hy) hes
  refine ⟨h1, h2, ?_⟩
  intro hyx p c hpc hp1 hc
  exact h3 p c hpc hp1 hc (Or.inr (by simp [upperColumn, ctxAt, hyx]))

/-! ## Comparing two non-cut emits of a block -/

theorem rowOK_cmp {E : Env} {τ row row' r r' : Row} (h : RowOK E τ row r)
    (h' : RowOK E τ row' r') : (r < r' → row < row') ∧ (r = r' → row = row') := by
  rcases h with ⟨hr, q, hq, hin, hrow⟩ | ⟨hr, hrow⟩ <;>
    rcases h' with ⟨hr', q', hq', hin', hrow'⟩ | ⟨hr', hrow'⟩
  · obtain ⟨k, j, _, _, rfl⟩ := Recon.RowLaw.mem_lowerItems hq
    obtain ⟨k', j', _, _, rfl⟩ := Recon.RowLaw.mem_lowerItems hq'
    simp only at hin hin' hrow hrow'
    refine ⟨fun hlt => ?_, fun heq => ?_⟩
    · by_cases hqq : k = k' ∧ j = j'
      · obtain ⟨rfl, rfl⟩ := hqq
        rw [hrow, hrow']
        exact (Φ_strictMono E k _ _ _ _ hin hin' hlt).1
      · obtain ⟨a, ha, hqa⟩ := List.getElem_of_mem hq
        obtain ⟨b, hb, hqb⟩ := List.getElem_of_mem hq'
        have hsep := ChainCorr.Inner.lowerItems_sep τ
        rcases Nat.lt_trichotomy a b with hab | hab | hab
        · have := List.pairwise_iff_getElem.mp hsep a b ha hb hab
          rw [hqa, hqb] at this
          rw [hrow, hrow']
          exact this _ _ (Φ_mem E k false _ _ r) (Φ_mem E k' false _ _ r')
        · subst hab
          rw [hqa] at hqb
          simp only [Prod.mk.injEq, Item.mk.injEq] at hqb
          exfalso
          apply hqq
          refine ⟨by omega, ?_⟩
          have h1 := hqb.2.1
          have h2 := congrArg (fun T => T.coeff k) h1
          simp only [Recon.RowLaw.slot_coeff_at] at h2
          have hk : k = k' := by omega
          subst hk
          simpa [Recon.RowLaw.slot_coeff_at] using h2
        · have := List.pairwise_iff_getElem.mp hsep b a hb ha hab
          rw [hqa, hqb] at this
          exact absurd (this _ _ hin' hin) (not_lt.mpr hlt.le)
    · subst heq
      have := Recon.JumpLaw.lowerItems_eq_of_common hq hq' hin hin'
      simp only [Prod.mk.injEq, Item.mk.injEq] at this
      obtain ⟨hk, hS, -⟩ := this
      have hk' : k = k' := by omega
      subst hk'
      rw [hrow, hrow', hS]
  · have hlow : row < τ := by
      rw [hrow]
      exact (lowerItems_below τ _ hq).1 _ (by
        obtain ⟨k, j, _, _, rfl⟩ := Recon.RowLaw.mem_lowerItems hq
        exact Φ_mem E k false _ _ r)
    refine ⟨fun _ => by rw [hrow']; exact lt_of_lt_of_le hlow hr', fun heq => ?_⟩
    rw [heq] at hr
    exact absurd hr (not_lt.mpr hr')
  · refine ⟨fun hlt => ?_, fun heq => ?_⟩
    · exact absurd (lt_of_lt_of_le hr' hr) (not_lt.mpr hlt.le)
    · rw [heq] at hr
      exact absurd hr' (not_lt.mpr hr)
  · rw [hrow, hrow']
    exact ⟨id, id⟩

/-! ## The three statements -/

/-- **`CopyOrder` from MA, MD, MH.** -/
theorem copyOrder_of_facts (hMA : MAHolds) (hMD : MDHolds) (hMH : MHHolds) :
    ChainCorr.CopyOrder := by
  intro s n D M out ρ R t hS i hi0 hi y y' es es' hy hy' hes hes' k hk k' hk' hnc hnc' c c' hc hc'
  have hV := build_valid_of_success hS.splice.build
  have hA := (column_shape hMA hMD hMH hS hi0 hi hy hes).1 _ (List.getElem_mem hk) hnc c hc
  have hA' := (column_shape hMA hMD hMH hS hi0 hi hy' hes').1 _ (List.getElem_mem hk') hnc' c' hc'
  obtain ⟨hlt, heq⟩ := rowOK_cmp hA hA'
  refine ⟨fun h => hlt ?_, fun h => heq (by rw [h])⟩
  exact Recon.official_strictMono (one_le_row hV hc (emitsT_good (τ := official t.row)
    (ctx := ctxAt M R y i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 (y + (ρ.x0 - ρ.cr) * i)) hes _
    (List.getElem_mem hk)).2.1) h

theorem mem_blockColumns_inner {cr x0 n i y : Nat} (hi0 : 0 < i) (hi : i < n + 1)
    (hcy : cr < y) (hyx : y < x0) : y ∈ blockColumns cr x0 n i := by
  unfold blockColumns
  rw [if_neg (by omega)]
  simp only [List.mem_range'_1]
  split <;> omega

/-- **`CopyEmitted` from MA, MD, MH.** -/
theorem copyEmitted_of_facts (hMA : MAHolds) (hMD : MDHolds) (hMH : MHHolds) :
    ChainCorr.CopyEmitted := by
  intro s n D M out ρ R t hS i hi0 hi y es hcy hyx hes p c hpc hp1 hc
  obtain ⟨q, hq, hqs, hqc⟩ := (column_shape hMA hMD hMH hS hi0 hi
    (mem_blockColumns_inner hi0 hi hcy hyx) hes).2.2 (ne_of_lt hyx) p c hpc hp1 hc
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hq
  exact ⟨k, hk, hqs, hqc⟩

/-- **`CopyFirst` from MA, MD, MH.** -/
theorem copyFirst_of_facts (hMA : MAHolds) (hMD : MDHolds) (hMH : MHHolds) :
    ChainCorr.CopyFirst := by
  intro s n D M out ρ R t hS i hi0 hi y es hcy hyx hes k hk hfirst
  have hsh := column_shape hMA hMD hMH hS hi0 hi (mem_blockColumns_inner hi0 hi hcy hyx) hes
  by_contra hcut
  have hcut' : ChainCorr.cutOrigin es[k].2 = true := by simpa using hcut
  obtain ⟨hcol, hidx, c, hc⟩ := ChainCorr.src_of_inner (ne_of_lt hyx) hes k hk
  obtain ⟨q, hq, hqs, hqc⟩ := hsh.2.2 (ne_of_lt hyx) _ c hcol hidx hc
  obtain ⟨k', hk', rfl⟩ := List.getElem_of_mem hq
  rcases Nat.lt_trichotomy k' k with hlt | heq | hgt
  · exact hfirst k' hk' hlt hqs
  · subst heq
    rw [hcut'] at hqc
    cases hqc
  · exact List.pairwise_iff_getElem.mp hsh.2.1 k k' hk hk' hgt hcut' hqc hqs.symm

/-! ## The statements of `ChainCorrStepInner.lean` -/

theorem spliceData_of_setting {s : List Nat} {n D : Nat} {M : Mountain} {out : List Nat}
    {ρ : Root} {R : Mountain} {col : Column} {t : Cell}
    (hS : ChainCorr.Inner.Setting s n D M out ρ R col t) : ChainCorr.SpliceData s n D M out ρ R t :=
  ⟨hS.splice, hS.deg, hS.run, hS.canon, ⟨col, hS.hcol, hS.ht⟩⟩

/-- **`ChainCorr.Inner.CopyEmitted` from MA, MD, MH.** -/
theorem inner_copyEmitted_of_facts (hMA : MAHolds) (hMD : MDHolds) (hMH : MHHolds) :
    ChainCorr.Inner.CopyEmitted := by
  intro s n D M out ρ R col t hS i hi0 hi y es hcy hyx hes
  exact copyEmitted_of_facts hMA hMD hMH s n D M out ρ R t (spliceData_of_setting hS) i hi0 hi y
    es hcy hyx hes

/-- **`ChainCorr.Inner.CopyFirst` from MA, MD, MH.** -/
theorem inner_copyFirst_of_facts (hMA : MAHolds) (hMD : MDHolds) (hMH : MHHolds) :
    ChainCorr.Inner.CopyFirst := by
  intro s n D M out ρ R col t hS i hi0 hi y es hcy hyx hes
  exact copyFirst_of_facts hMA hMD hMH s n D M out ρ R t (spliceData_of_setting hS) i hi0 hi y
    es hcy hyx hes

end OmegaY.Official.Classification.Proofs.CopyShape

#print axioms OmegaY.Official.Classification.Proofs.CopyShape.copyOrder_of_facts
#print axioms OmegaY.Official.Classification.Proofs.CopyShape.copyEmitted_of_facts
#print axioms OmegaY.Official.Classification.Proofs.CopyShape.copyFirst_of_facts
#print axioms OmegaY.Official.Classification.Proofs.CopyShape.inner_copyEmitted_of_facts
#print axioms OmegaY.Official.Classification.Proofs.CopyShape.inner_copyFirst_of_facts
