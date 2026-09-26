/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/StepInnerLookupLeg.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.StepInnerLookupBump
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.ChainCorrStartRoot

set_option backward.do.legacy false

/-!
# `LegLookup` (`ChainCorrStepInner.lean`) from the block profile

`ChainCorr.Inner.LegLookup` asks, for two consecutive copy pairs `(v, m)` and `(v⁺, m⁺)` of
a block `i ≥ 1` and the raw parent `pa = left(m⁺)` of `m`: the highest node `pe` of the
output column `φ(col pa)` at or below the row of `v` is

* `pa` itself when `pa` is left of `cr`;
* a node whose scale-`k` chain reaches `m''` for every pair of `M(s)` steps
  `m → pa → m''` at scale `k`, when `pa` is in the root column;
* a copy node of `pa` when `pa` is right of `cr`.

Common part (`legLookup_common`, proved): the output mountain is canonical, so `pe` is the
raw parent `left(v⁺)` of `v`, and its column is `φ(col pa)` (`copyAt_left`).

## `pa` left of `cr` (`legLookup_left`, proved from `LegBelowTop`)

The leg of `m⁺` is left of `cr`, so the emit of `v⁺` is an upper origin: a copy of the root
row has its leg at or right of `cr` (`leg_of_ascension`), and a plain origin is below the top
row `τ` (`emitsT_plainBelow`), where `LegJump.LegBelowTop` (open, another agent's statement)
puts the leg at or right of `cr`. An upper copy has the row of its origin (`upper_row`), so
`row v⁺ = row m⁺`. In both canonical mountains the raw parent is the highest node of its
column strictly below the upper node (`canonical_rawParent_highest_below`), and the columns
left of `x₀` are shared (`AgreeBelow`): `left(v⁺) = left(m⁺) = pa`.

## `pa` right of `cr` (`legLookup_inner`)

The argument of `startCopy_of_parts` (`ChainCorrStartCopy.lean`) at the row of `v` instead
of the row of a single copied node: `pa` is the highest node of `col pa` at or below
`row m` (`canon_rawParent_hAM`), it has a non-cut copy (`CopyEmitted`), rows of non-cut copies
follow the rows of their origins (`CopyOrder`), origin rows do not decrease
(`copyMono_holds`), and the first emit of an origin is not a gap copy (`CopyFirst`); so the
emit at `pe` has the origin `pa`. It is a gap copy only if `pa` has no raw parent:

* `LegGapTop` (open, new): a gap copy of `pa` in the column `φ(col pa)` at or below the row
  of `v` occurs only when `pa` is the top of its column.

## `pa` in the root column (`legLookup_root`)

`pe` is a node of the boundary column `cr + w·i = x₀ + w·(i - 1)` (block `i - 1`). By
`BoundaryChain` (open, another agent's statement, `ChainCorrStartRoot.lean`) it suffices that
the chain of `M(s)` from the origin of `pe` reaches `m''`:

* `LegOriginReach` (open, new): for `M(s)` steps `m → pa → m''` at scale `k`, the scale-`k`
  chain of `M(s)` from the origin of `pe = left(v⁺)` reaches `m''`.

## Result

* **`legLookup_of_parts : CopyOrder → CopyEmitted → CopyFirst → LegBelowTop → LegGapTop →
  BoundaryChain → LegOriginReach → LegLookup`**.
* **`stepInner_of_open`**: `StepInner` from these and the three clean statements
  `CleanNext`, `CleanLookup`, `CleanParent` (`BumpCopyLower` is `bumpCopyLower_of_copyFirst`).

## Numerical tests (JS reference of this repository, the rule of `omegay-trace.cjs`)

Counts: consecutive copy pairs in the case of the statement. No failure.

| statement | standard S1–S3, S6 | legal ≤ 6, ≤ 6 | legal ≤ 5, ≤ 8 | random `20000,10,10,7` |
|---|---:|---:|---:|---:|
| `LegGapTop` (`pa > cr`) | 176094 | 16314 | 6750 | 62406 |
| `LegOriginReach` (`pa = cr`, `pa` has a raw parent) | 117960 | 11052 | 5220 | 29634 |
| `pe = pa` (`pa < cr`, proved here) | 4338 | 834 | 816 | 4332 |

The general form "a gap copy of `p` lies above every non-cut copy (same block) of an origin
of row in `[row p, row p⁺)`" fails on 40 gap copies of the random sample (for example
`(1,9,5,6,3,8,10,8)[1]`), so `LegGapTop` is stated only for the lookup of `LegLookup`.
-/

namespace OmegaY.Official.Classification.Proofs.ChainCorr.InnerLookup

open Canonical Reserve Official Descent Classification Proofs
open ChainCorr.Inner

/-! ## The open statements -/

/-- (open) A gap copy of the raw parent `pa` of `m` in the column `φ(col pa)` at or below the
row of the copy `v` of `m` occurs only when `pa` is the top of its column. -/
def LegGapTop : Prop :=
  ∀ s n D M out ρ R (col : Column) (t : Cell), Setting s n D M out ρ R col t →
    ∀ i, 0 < i → i < n + 1 → ∀ v m,
      CopyNode M R n ρ.cr ρ.x0 (official t.row) i v m →
      CopyNode M R n ρ.cr ρ.x0 (official t.row) i (up v) (up m) →
      ∀ pa, rawParent M m = some pa → ρ.cr < pa.column →
      ∀ esl, emitsT (ctxAt M R pa.column i ρ.cr (ρ.x0 - ρ.cr) ρ.x0
          (pa.column + (ρ.x0 - ρ.cr) * i)) (official t.row) = .ok esl →
      ∀ k (hk : k < esl.length), cutOrigin esl[k].2 = true → esl[k].2.src = pa →
      ∀ cv, cell? R v = some cv → stored esl[k].1.row ≤ cv.row → rawParent M pa = none

/-- (open) For a raw parent `pa` of `m` in the root column, the chain of `M(s)` from the
origin of `pe = left(v⁺)` (a node of the boundary column) reaches the next node `m''` of the
chain of `pa`. -/
def LegOriginReach : Prop :=
  ∀ s n D M out ρ R (col : Column) (t : Cell), Setting s n D M out ρ R col t →
    ∀ i, 0 < i → i < n + 1 → ∀ v m,
      CopyNode M R n ρ.cr ρ.x0 (official t.row) i v m →
      CopyNode M R n ρ.cr ρ.x0 (official t.row) i (up v) (up m) →
      ∀ pa, rawParent M m = some pa → pa.column = ρ.cr →
      ∀ pe, rawParent R v = some pe →
      ∀ esB, blockEmits M R ρ.cr ρ.x0 (official t.row) (i - 1) ρ.x0 = .ok esB →
      ∀ k (hk : k < esB.length), pe.index = k + 1 →
      ∀ kk m'', MStep M kk m pa → MStep M kk pa m'' → ScaleReach M kk esB[k].2.src m''

/-! ## The common part -/

/-- The lookup of `LegLookup` is the raw parent of `v`. -/
theorem legLookup_common {s : List Nat} {n D : Nat} {M : Mountain} {out : List Nat} {ρ : Root}
    {R : Mountain} {col : Column} {t : Cell} (hS : Setting s n D M out ρ R col t) {i : Nat}
    (hi0 : 0 < i) (hi : i < n + 1) {v m : Ref}
    (hvm : CopyNode M R n ρ.cr ρ.x0 (official t.row) i v m)
    (hup : CopyNode M R n ρ.cr ρ.x0 (official t.row) i (up v) (up m))
    {pa : Ref} (hpa : rawParent M m = some pa) {cv : Cell} (hcv : cell? R v = some cv) :
    ∃ pe, rawParent R v = some pe ∧
      pe.column = mapColumn ρ.cr ((ρ.x0 - ρ.cr) * i) pa.column ∧
      highestAtMost R (mapColumn ρ.cr ((ρ.x0 - ρ.cr) * i) pa.column) cv.row = some pe := by
  obtain ⟨o', hvo', hsrc', _⟩ := copyAt_of_copyNode hup
  obtain ⟨cu, ref, co, l, hcu, hrefl, hco, hl, hrefc⟩ := copyAt_left hS hi0 hi hvo'
  rw [hsrc'] at hco
  obtain ⟨c, hc, hcl⟩ := rawParent_eq_some.mp hpa
  have hcc : c = co := Option.some.inj (hc.symm.trans hco)
  subst hcc
  have hll : pa = l := Option.some.inj (hcl.symm.trans hl)
  subst hll
  have hraw : rawParent R v = some ref := rawParent_eq_some.mpr ⟨cu, hcu, hrefl⟩
  have hv0 := (copyNode_index_pos hvm).1
  have hham := canon_rawParent_hAM hS.canon hv0 hcv hraw
  rw [hrefc] at hham
  exact ⟨ref, hraw, hrefc, hham⟩

/-- Mountains that agree below `B` have the same cells there. -/
theorem cell?_agree {M R : Mountain} {B : Nat} (hA : AgreeBelow M R B) {r : Ref}
    (hr : r.column < B) : cell? R r = cell? M r := by
  unfold cell?
  rw [hA r.column hr]

/-! ## `pa` left of the root column -/

/-- **`pa` left of `cr`: the raw parent of `v` is `pa`.** -/
theorem legLookup_left (hT : LegJump.LegBelowTop) {s : List Nat} {n D : Nat} {M : Mountain}
    {out : List Nat} {ρ : Root} {R : Mountain} {col : Column} {t : Cell}
    (hS : Setting s n D M out ρ R col t) {i : Nat} (hi0 : 0 < i) (hi : i < n + 1) {v m : Ref}
    (hup : CopyNode M R n ρ.cr ρ.x0 (official t.row) i (up v) (up m))
    {pa : Ref} (hpa : rawParent M m = some pa) (hlt : pa.column < ρ.cr) :
    rawParent R v = some pa := by
  obtain ⟨_, _, _, _, _, hcrx, hinv⟩ := spliceCase_data hS.splice hS.run
  obtain ⟨o', hvo', hsrc', _⟩ := copyAt_of_copyNode hup
  obtain ⟨cu, ref, co, l, hcu, hrefl, hco, hl, hrefc⟩ := copyAt_left hS hi0 hi hvo'
  rw [hsrc'] at hco
  obtain ⟨c, hc, hcl⟩ := rawParent_eq_some.mp hpa
  have hcc : c = co := Option.some.inj (hc.symm.trans hco)
  subst hcc
  have hll : pa = l := Option.some.inj (hcl.symm.trans hl)
  subst hll
  have hraw : rawParent R v = some ref := rawParent_eq_some.mpr ⟨cu, hcu, hrefl⟩
  -- the emit of `v⁺` is the upper copy of `m⁺`
  obtain ⟨y, es, j, hcy, hyx, hyb, hvc, hvi, hes, hj, ho⟩ := hvo'
  have hSite := site_of_copyAt hS hi0 hi hcy hyx hyb hvc hes
  have hupper : CopyAt M R n ρ.cr ρ.x0 (official t.row) i (up v) (.upper (up m)) := by
    refine ⟨y, es, j, hcy, hyx, hyb, hvc, hvi, hes, hj, ?_⟩
    rw [ho]
    cases o' with
    | upper r =>
        simp only [Origin.src] at hsrc'
        rw [hsrc']
    | plain r =>
        exfalso
        simp only [Origin.src] at hsrc'
        subst hsrc'
        obtain ⟨c', hmem, hlt'⟩ :=
          LegJump.emitsT_plainBelow hes es[j] (List.getElem_mem hj) (up m) ho
        simp only [ctxAt] at hmem
        have hcell := LegJump.cell?_of_mem_realNodes hmem
        have hcc' : c' = c := Option.some.inj (hcell.symm.trans hco)
        subst hcc'
        obtain ⟨hmc, _⟩ := Recon.RowLaw.realNodes_column hmem
        obtain ⟨root, hTop, hroot, hx0⟩ := LegJump.site_top hSite
        have h := hT s M t root hTop (up m) c' pa (by rw [hroot, hmc]; exact hcy)
          (by rw [hmc, ← hx0]; exact le_of_lt hyx) hco hl
          (Recon.row_lt_of_official hTop.row_one_le hlt')
        omega
    | clean r b =>
        exfalso
        simp only [Origin.src] at hsrc'
        subst hsrc'
        obtain ⟨C, cs, hcs, ref', cl', hn, hr⟩ :=
          emitsT_cleanAsc hes es[j] (List.getElem_mem hj) (up m) b ho
        simp only [ctxAt] at hcs hn hr
        obtain ⟨_, _, hcscell, _⟩ := Classification.nodeAt_spec hcs
        have hcs' : cs = c := Option.some.inj (hcscell.symm.trans hco)
        subst hcs'
        have h := leg_of_ascension hS.splice.build hcy hn hr hcs hl
        omega
  have hrow : cu.row = c.row := upper_row hS hi0 hi hupper hcu hco
  -- both raw parents are the highest nodes strictly below the upper nodes
  obtain ⟨cpe, hcpe, hlt1, hmax1⟩ :=
    canonical_rawParent_highest_below (build_success_legal hS.canon) hS.canon (u := v) hcu hraw
  obtain ⟨cpa, hcpa, hlt2, hmax2⟩ :=
    canonical_rawParent_highest_below (build_success_legal hS.splice.build) hS.splice.build
      (u := m) hco hpa
  have hrefcol : ref.column = pa.column := by rw [hrefc, mapColumn_of_lt hlt]
  have hA := hinv.1
  have hi1 : ref.index ≤ pa.index := by
    apply hmax2 ref.index cpe
    · have h1 : (⟨pa.column, ref.index⟩ : Ref) = ref := ref_eq_of hrefcol.symm rfl
      rw [h1, ← cell?_agree hA (by omega)]
      exact hcpe
    · rw [← hrow]; exact hlt1
  have hi2 : pa.index ≤ ref.index := by
    apply hmax1 pa.index cpa
    · have h1 : (⟨ref.column, pa.index⟩ : Ref) = pa := ref_eq_of hrefcol rfl
      rw [h1, cell?_agree hA (by omega)]
      exact hcpa
    · rw [hrow]; exact hlt2
  have href : ref = pa := ref_eq_of hrefcol (le_antisymm hi1 hi2)
  rw [← href]
  exact hraw

/-! ## `pa` right of the root column -/

/-- **`pa` right of `cr`: the lookup is a copy node of `pa`.** -/
theorem legLookup_inner (hA : ChainCorr.CopyOrder) (hB : Inner.CopyEmitted)
    (hC2 : Inner.CopyFirst) (hG : LegGapTop) {s : List Nat} {n D : Nat} {M : Mountain}
    {out : List Nat} {ρ : Root} {R : Mountain} {col : Column} {t : Cell}
    (hS : Setting s n D M out ρ R col t) {i : Nat} (hi0 : 0 < i) (hi : i < n + 1) {v m : Ref}
    (hvm : CopyNode M R n ρ.cr ρ.x0 (official t.row) i v m)
    (hup : CopyNode M R n ρ.cr ρ.x0 (official t.row) i (up v) (up m))
    {pa : Ref} (hpa : rawParent M m = some pa) (hlt : ρ.cr < pa.column)
    {cv : Cell} (hcv : cell? R v = some cv) {pe : Ref}
    (hpe : highestAtMost R (pa.column + (ρ.x0 - ρ.cr) * i) cv.row = some pe) :
    CopyNode M R n ρ.cr ρ.x0 (official t.row) i pe pa := by
  have hV := build_valid_of_success hS.splice.build
  have hVR := build_valid_of_success hS.canon
  have hdat : SpliceData s n D M out ρ R t :=
    ⟨hS.splice, hS.deg, hS.run, hS.canon, ⟨col, hS.hcol, hS.ht⟩⟩
  obtain ⟨col', t', hcol', ht', _, hcrx, hinv⟩ := spliceCase_data hS.splice hS.run
  have hcc0 : col = col' := Option.some.inj (hS.hcol.symm.trans hcol')
  subst hcc0
  have htt : t = t' := Option.some.inj (hS.ht.symm.trans ht')
  subst htt
  have hm0 := (copyNode_index_pos hvm).2
  obtain ⟨⟨cm, hcm⟩, ⟨cpa, hcpa⟩, hpam⟩ := rawParent_cells hV hpa
  have hvm' := hvm
  obtain ⟨y, es, jv, hcy, hyx, hyb, hvc, hvi, hes, hjv, hsrcv, hcutv⟩ := hvm
  have hncv : cutOrigin es[jv].2 = false := by
    rcases hcutv with h | h
    · exact h
    · rw [h] at hpa; cases hpa
  have hmy : m.column = y := by
    have := (src_inner hyx hes jv hjv).1
    rw [hsrcv] at this
    exact this
  have hes' : emitsT (ctxAt M R y i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 (y + (ρ.x0 - ρ.cr) * i))
      (official t.row) = .ok es := by rw [← hvc]; exact hes
  have hblx : blockEmits M R ρ.cr ρ.x0 (official t.row) i y = .ok es := hes'
  -- the row of `v`
  have hSv := site_of_copyAt hS hi0 hi hcy hyx hyb hvc hes
  obtain ⟨cX, hRX, hcopyX⟩ := hSv.copy
  obtain ⟨_, hcellsX⟩ := cells_of_copy hRX hcopyX hSv.emits
  obtain ⟨cellv, hcellv, hrowv'⟩ := hcellsX jv hjv
  have hcv2 : cell? R ⟨v.column, jv + 1⟩ = some cv := by rw [← hvi]; exact hcv
  have hrowcu : cv.row = stored es[jv].1.row := by
    rw [Option.some.inj (hcv2.symm.trans hcellv)]
    exact hrowv'
  have hcvm : cell? M es[jv].2.src = some cm := by rw [hsrcv]; exact hcm
  -- `pa` is the highest node of its column at or below the row of `m`
  have hpaM := canon_rawParent_hAM hS.splice.build hm0 hcm hpa
  have hyx' : pa.column < ρ.x0 := by omega
  have hymem : pa.column ∈ blockColumns ρ.cr ρ.x0 n i := by
    unfold blockColumns
    rw [if_neg (by omega)]
    simp only [List.mem_range'_1]
    split <;> omega
  -- the output column `L = col pa + w·i`
  obtain ⟨hpecol, hpe0, colL, hcolL, hpeL, hperow, hpemax⟩ := highestAtMost_spec hpe
  have hL0 : ρ.x0 ≤ pa.column + (ρ.x0 - ρ.cr) * i := by
    have : ρ.x0 - ρ.cr ≤ (ρ.x0 - ρ.cr) * i := Nat.le_mul_of_pos_right _ hi0
    omega
  obtain ⟨hLsz, _⟩ := column_of_getElem? hcolL
  obtain ⟨i', x', _, hx', hLeq, hcopyL⟩ := hinv.2.2 _ hLsz hL0
  obtain ⟨hii, hxy⟩ := blockCol_unique_inner hcrx hlt hyx' hi0 hx' hLeq
  subst i' x'
  have hcolL' : R[pa.column + (ρ.x0 - ρ.cr) * i]? = some R[pa.column + (ρ.x0 - ρ.cr) * i] :=
    Array.getElem?_eq_getElem hLsz
  have hcc : colL = R[pa.column + (ρ.x0 - ρ.cr) * i] :=
    Option.some.inj (hcolL.symm.trans hcolL')
  obtain ⟨esl, hesl, _⟩ := copyColumn_emitsT hcopyL
  obtain ⟨hszL, hcellsL⟩ := cells_of_copy hcolL' hcopyL hesl
  have hbl : blockEmits M R ρ.cr ρ.x0 (official t.row) i pa.column = .ok esl := hesl
  -- the index of `pe`
  have hksl : pe.index - 1 < esl.length := by
    have : pe.index < colL.size := hpeL
    rw [hcc, hszL] at this
    omega
  have hpeidx : pe.index = (pe.index - 1) + 1 := by omega
  have hrowL : ∀ k (hk : k < esl.length) (hk' : k + 1 < colL.size),
      (colL[k + 1]'hk').row = stored esl[k].1.row := by
    intro k hk hk'
    obtain ⟨cell, hcell, hrow⟩ := hcellsL k hk
    obtain ⟨col', hcol', hp', hcell'⟩ := cell?_column hcell
    simp only at hcol' hp' hcell'
    have : col' = colL := Option.some.inj (hcol'.symm.trans hcolL)
    subst this
    rw [hcell', hrow]
  have hle_ks : ∀ k (hk : k < esl.length), esl[k].1.row ≤ es[jv].1.row → k ≤ pe.index - 1 := by
    intro k hk hrk
    have hk' : k + 1 < colL.size := by rw [hcc, hszL]; omega
    have h1 := hpemax (k + 1) hk' (by omega) (by
      rw [hrowL k hk hk', hrowcu]
      exact stored_mono hrk)
    omega
  have hks_le : esl[pe.index - 1].1.row ≤ es[jv].1.row := by
    have h1 : (colL[pe.index]'hpeL).row ≤ cv.row := hperow
    have hk' : pe.index - 1 + 1 < colL.size := by omega
    have h2 := hrowL (pe.index - 1) hksl hk'
    have h3 : (colL[pe.index]'hpeL) = (colL[pe.index - 1 + 1]'hk') := by
      congr 1
    rw [h3, h2, hrowcu] at h1
    exact stored_le_iff.mp h1
  have hmonoL : ∀ k k' (hk : k < esl.length) (hk' : k' < esl.length), k ≤ k' →
      esl[k].1.row ≤ esl[k'].1.row := by
    intro k k' hk hk' hkk
    rcases Nat.lt_or_eq_of_le hkk with h | h
    · obtain ⟨c1, hc1, hr1⟩ := hcellsL k hk
      obtain ⟨c2, hc2, hr2⟩ := hcellsL k' hk'
      have := cell_row_lt hVR hc1 hc2 (by omega)
      rw [hr1, hr2] at this
      exact le_of_lt (stored_lt_iff.mp this)
    · subst h
      exact le_refl _
  -- the node `pa` of `M(s)`
  obtain ⟨hpacol, hpa0, colY, hcolY, hpaY, hparow, hpamax⟩ := highestAtMost_spec hpaM
  obtain ⟨colY', hcolY', hpaY', hcpaY⟩ := cell?_column hcpa
  have hYY : colY' = colY := Option.some.inj (hcolY'.symm.trans (by rw [hpacol]; exact hcolY))
  subst colY'
  have hcpa_le : cpa.row ≤ cm.row := by rw [← hcpaY]; exact hparow
  -- (B): the non-cut copy of `pa`
  obtain ⟨kπ, hkπ, hkπsrc, hkπnc⟩ := hB s n D M out ρ R col t hS i hi0 hi pa.column esl hlt
    hyx' hbl pa cpa rfl (by omega) hcpa
  have hcpaπ : cell? M esl[kπ].2.src = some cpa := by rw [hkπsrc]; exact hcpa
  have hkπ_le : kπ ≤ pe.index - 1 := by
    apply hle_ks kπ hkπ
    have hA' := hA s n D M out ρ R t hdat i hi0 hi pa.column y esl es hymem hyb hbl
      hblx kπ hkπ jv hjv hkπnc hncv cpa cm hcpaπ hcvm
    rcases lt_or_eq_of_le hcpa_le with h | h
    · exact le_of_lt (hA'.1 h)
    · exact le_of_eq (hA'.2 h)
  -- the origin `ν` of the emit at `pe.index - 1`
  obtain ⟨hνcol, hν1, cν, hcν⟩ := src_of_inner (ne_of_lt hyx') hbl (pe.index - 1) hksl
  -- its first emit is not cut (C2)
  obtain ⟨k0, hk0l, hk0src, hk0min⟩ : ∃ k0, ∃ hk0l : k0 < esl.length,
      esl[k0].2.src = esl[pe.index - 1].2.src ∧
        ∀ k' (hk' : k' < esl.length), k' < k0 → esl[k'].2.src ≠ esl[pe.index - 1].2.src := by
    classical
    have hex : ∃ k, ∃ hk : k < esl.length, esl[k].2.src = esl[pe.index - 1].2.src :=
      ⟨pe.index - 1, hksl, rfl⟩
    obtain ⟨hk0l, hk0src⟩ := Nat.find_spec hex
    exact ⟨Nat.find hex, hk0l, hk0src, fun k' hk' hlt' heq => Nat.find_min hex hlt' ⟨hk', heq⟩⟩
  have hk0le : k0 ≤ pe.index - 1 := by
    by_contra hn
    exact hk0min (pe.index - 1) hksl (by omega) rfl
  have hk0nc : cutOrigin esl[k0].2 = false := by
    apply hC2 s n D M out ρ R col t hS i hi0 hi pa.column esl hlt hyx' hbl k0 hk0l
    intro k' hk' hlt' heq
    exact hk0min k' hk' hlt' (heq.trans hk0src)
  have hcν0 : cell? M esl[k0].2.src = some cν := by rw [hk0src]; exact hcν
  -- the origin of the emit at `pe.index - 1` is at or below the row of `m`
  have hcν_le : cν.row ≤ cm.row := by
    by_contra hn
    have hlt' : cm.row < cν.row := lt_of_not_ge hn
    have hA' := hA s n D M out ρ R t hdat i hi0 hi y pa.column es esl hyb hymem hblx
      hbl jv hjv k0 hk0l hncv hk0nc cm cν hcvm hcν0
    have h1 := hA'.1 hlt'
    have h2 := hmonoL k0 (pe.index - 1) hk0l hksl hk0le
    exact absurd (lt_of_lt_of_le h1 (le_trans h2 hks_le)) (lt_irrefl _)
  -- so it is `pa`
  have hνpa : esl[pe.index - 1].2.src = pa := by
    obtain ⟨colN, hcolN, hνN, hcνN⟩ := cell?_column hcν
    have hNN : colN = colY := Option.some.inj (hcolN.symm.trans (by rw [hνcol]; exact hcolY))
    subst colN
    have hidx_le : esl[pe.index - 1].2.src.index ≤ pa.index :=
      hpamax _ hνN (by omega) (by rw [hcνN]; exact hcν_le)
    have hmono := copyMono_holds s n D M out ρ R col t hS i hi0 hi pa.column esl hlt hyx' hbl kπ
      (pe.index - 1) hkπ hksl hkπ_le cpa cν hcpaπ hcν
    have hpa' : cell? M ⟨pa.column, pa.index⟩ = some cpa := hcpa
    have hν' : cell? M ⟨pa.column, esl[pe.index - 1].2.src.index⟩ = some cν := by
      rw [← hνcol]; exact hcν
    have hidx_ge : pa.index ≤ esl[pe.index - 1].2.src.index := cell_index_le hV hpa' hν' hmono
    exact ref_eq_of (by rw [hνcol]) (le_antisymm hidx_le hidx_ge)
  -- the copy node
  have hesl' : emitsT (ctxAt M R pa.column i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 pe.column)
      (official t.row) = .ok esl := by rw [hpecol]; exact hesl
  refine ⟨pa.column, esl, pe.index - 1, hlt, hyx', hymem, hpecol, hpeidx, hesl', hksl, hνpa, ?_⟩
  cases hcut : cutOrigin esl[pe.index - 1].2
  · exact Or.inl rfl
  · refine Or.inr (hG s n D M out ρ R col t hS i hi0 hi v m hvm' hup pa hpa hlt esl hesl
      (pe.index - 1) hksl hcut hνpa cv hcv ?_)
    rw [hrowcu]
    exact stored_mono hks_le

/-! ## `pa` in the root column -/

/-- **`pa` in the root column: the chain of the lookup follows the chain of `pa`.** -/
theorem legLookup_root (hBC : ChainCorr.BoundaryChain) (hO : LegOriginReach) {s : List Nat}
    {n D : Nat} {M : Mountain} {out : List Nat} {ρ : Root} {R : Mountain} {col : Column}
    {t : Cell} (hS : Setting s n D M out ρ R col t) {i : Nat} (hi0 : 0 < i) (hi : i < n + 1)
    {v m : Ref} (hvm : CopyNode M R n ρ.cr ρ.x0 (official t.row) i v m)
    (hup : CopyNode M R n ρ.cr ρ.x0 (official t.row) i (up v) (up m))
    {pa : Ref} (hpa : rawParent M m = some pa) (heq : pa.column = ρ.cr) {pe : Ref}
    (hraw : rawParent R v = some pe) {row : Row}
    (hpe : highestAtMost R (mapColumn ρ.cr ((ρ.x0 - ρ.cr) * i) pa.column) row = some pe) :
    ∀ k m'', MStep M k m pa → MStep M k pa m'' → ScaleReach R k pe m'' := by
  intro kk m'' hst1 hst2
  have hdat : SpliceData s n D M out ρ R t :=
    ⟨hS.splice, hS.deg, hS.run, hS.canon, ⟨col, hS.hcol, hS.ht⟩⟩
  obtain ⟨col', t', hcol', ht', _, hcrx, hinv⟩ := spliceCase_data hS.splice hS.run
  have hcc0 : col = col' := Option.some.inj (hS.hcol.symm.trans hcol')
  subst hcc0
  have htt : t = t' := Option.some.inj (hS.ht.symm.trans ht')
  subst htt
  obtain ⟨hpecol, hpe0, colB, hcolB, hpeB, _, _⟩ := highestAtMost_spec hpe
  rw [← hpecol] at hcolB
  rw [heq, mapColumn_of_ge (le_refl _), boundary_eq hcrx hi0] at hpecol
  obtain ⟨hBsz, _⟩ := column_of_getElem? hcolB
  have hB0 : ρ.x0 ≤ pe.column := by rw [hpecol]; omega
  obtain ⟨i', x', _, hx', hBeq, hcopyB⟩ := hinv.2.2 pe.column hBsz hB0
  obtain ⟨hii, hxx⟩ := block_unique_boundary hcrx hx' (by rw [← hpecol]; exact hBeq)
  subst i' x'
  have hcolB' : R[pe.column]? = some R[pe.column] := Array.getElem?_eq_getElem hBsz
  have hcc : colB = R[pe.column] := Option.some.inj (hcolB.symm.trans hcolB')
  obtain ⟨esB, hesB, _⟩ := copyColumn_emitsT hcopyB
  obtain ⟨hszB, _⟩ := cells_of_copy hcolB' hcopyB hesB
  have hbl : blockEmits M R ρ.cr ρ.x0 (official t.row) (i - 1) ρ.x0 = .ok esB := by
    have h' : ρ.x0 + (ρ.x0 - ρ.cr) * (i - 1) = pe.column := hpecol.symm
    simp only [blockEmits, h']
    exact hesB
  have hksl : pe.index - 1 < esB.length := by
    have : pe.index < colB.size := hpeB
    rw [hcc, hszB] at this
    omega
  have hreachM := hO s n D M out ρ R col t hS i hi0 hi v m hvm hup pa hpa heq pe hraw esB hbl
    (pe.index - 1) hksl (by omega) kk m'' hst1 hst2
  have hm'' : m''.column < ρ.cr := heq ▸ hst2.column_lt
  have hreachR := hBC s n D M out ρ R t hdat i hi0 hi esB hbl (pe.index - 1) hksl kk m''
    hm'' hreachM
  have hpe' : pe = ⟨ρ.x0 + (ρ.x0 - ρ.cr) * (i - 1), pe.index - 1 + 1⟩ :=
    ref_eq_of (by rw [hpecol]) (by simp only; omega)
  rw [hpe']
  exact hreachR

/-! ## The result -/

/-- **`LegLookup` from the block profile (`CopyOrder`, `CopyEmitted`, `CopyFirst`) and four open
statements (`LegBelowTop`, `LegGapTop`, `BoundaryChain`, `LegOriginReach`).** -/
theorem legLookup_of_parts (hA : ChainCorr.CopyOrder) (hB : Inner.CopyEmitted)
    (hC2 : Inner.CopyFirst) (hT : LegJump.LegBelowTop) (hG : LegGapTop)
    (hBC : ChainCorr.BoundaryChain) (hO : LegOriginReach) : Inner.LegLookup := by
  intro s n D M out ρ R col t hS i hi0 hi v m hvm hup pa hpa cv hcv
  obtain ⟨pe, hraw, _, hpe⟩ := legLookup_common hS hi0 hi hvm hup hpa hcv
  refine ⟨pe, hpe, fun hlt => ?_, fun heq => ?_, fun hlt => ?_⟩
  · have h := legLookup_left hT hS hi0 hi hup hpa hlt
    exact Option.some.inj (hraw.symm.trans h)
  · exact legLookup_root hBC hO hS hi0 hi hvm hup hpa heq hraw hpe
  · rw [mapColumn_of_ge (le_of_lt hlt)] at hpe
    exact legLookup_inner hA hB hC2 hG hS hi0 hi hvm hup hpa hlt hcv hpe

/-- **`StepInner` from the block profile, the open statements of `LegLookup` and the three
clean statements.** -/
theorem stepInner_of_open (hA : ChainCorr.CopyOrder) (hB : Inner.CopyEmitted)
    (hC2 : Inner.CopyFirst) (hT : LegJump.LegBelowTop) (hG : LegGapTop)
    (hBC : ChainCorr.BoundaryChain) (hO : LegOriginReach) (hCN : Inner.CleanNext)
    (hCL : Inner.CleanLookup) (hCP : Inner.CleanParent) : StepInner :=
  Inner.stepInner_of_rest hB hC2 (legLookup_of_parts hA hB hC2 hT hG hBC hO)
    (bumpCopyLower_of_copyFirst hC2) hCN hCL hCP

end OmegaY.Official.Classification.Proofs.ChainCorr.InnerLookup

#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.InnerLookup.legLookup_common
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.InnerLookup.legLookup_left
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.InnerLookup.legLookup_inner
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.InnerLookup.legLookup_root
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.InnerLookup.legLookup_of_parts
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.InnerLookup.stepInner_of_open
