/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/ChainCorrStartCopy.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.ChainCorrRegions
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.Certificate

set_option backward.do.legacy false

/-!
# `StartCopy` from the profile of a block

`StartCopy` (`ChainCorrRegions.lean`) asks: for a node `u` of a column of block `i ≥ 1`
whose origin `o = (x, σ)` is not a gap copy and whose leg `l` is right of the root column,
the highest node `pe` of the output leg column `φ(l) = l + w·i` at or below the row of `u`
is a copy of `pa`, the highest node of the column `l` of `M(s)` at or below `σ`.

## The profile of a block

The numerical tests (`reference/official/startcopy-root-parts.cjs`) show a simple shape of
every copied column of a block `i ≥ 1`:

* (A) `CopyOrder`: the row of a non-cut copy depends only on the row of its origin, in the
  same increasing way in every column of the block. For non-cut emits `a` of the copy of
  `y` and `a'` of the copy of `y'` (both in block `i`): `row(src a) < row(src a')` gives
  `row a < row a'`, and equal origin rows give equal rows.
* (B) `CopyEmitted`: in an inner column `y` (`cr < y < x₀`) every node of `M(s)` is the
  origin of a non-cut copy.
* (C1) `CopyMono`: in an inner column, the origin rows of the emits do not decrease
  (proved in `ChainCorrCopyMono.lean` for every column, from the rule alone).
* (C2) `CopyFirst`: in an inner column, the first emit of every origin is not a cut copy
  (later copies of a root-row node are the gap copies, `b = 1`).

So in an inner column the copies of a node `ν` come in one run: first a non-cut copy at the
row `F(row ν)`, then gap copies, then the copies of the next node; and `F` is the same map
in every column of the block.

With these, the highest emit of `φ(l)` at or below `row u = F(σ)` is a copy of the highest
node of `l` at or below `σ`, which is `pa` (`startCopy_of_parts`). It is the non-cut copy
unless the gap copies of `pa` reach up to `row u`; in the numerical tests this happens only
when `pa` is the top of the column `l` (`CutTop`, 36 nodes of the standard samples).

## Numerical tests

`reference/official/startcopy-root-parts.cjs` (counts: pairs of emits for `CopyOrder`,
nodes otherwise):

| sample | `CopyOrder` | `CopyEmitted` | `CopyMono` | `CopyFirst` | `CutTop` (used) | failures |
|---|---:|---:|---:|---:|---:|---:|
| standard S1–S3, S6, `n = 1,2,3` | 24257067 | 560136 | 1174933 | 560136 | 36 | 0 |
| legal, length ≤ 6, entries ≤ 6 | 2810418 | 209802 | 313066 | 209802 | 0 | 0 |
| legal, length ≤ 5, entries ≤ 8 | 2123166 | 139320 | 475381 | 139320 | 0 | 0 |
| random legal (`--random 20000,10,10,7`) | 14388984 | 638262 | 3845475 | 638262 | 78 | 0 |
-/

namespace OmegaY.Official.Classification.Proofs.ChainCorr

open Canonical Reserve Official Descent Classification Proofs


/-! ## Tools -/

theorem stored_le_iff {a b : Row} : stored a ≤ stored b ↔ a ≤ b := by
  constructor
  · intro h
    by_contra hn
    exact absurd h (not_le.mpr (Recon.stored_strictMono (lt_of_not_ge hn)))
  · exact stored_mono

theorem stored_lt_iff {a b : Row} : stored a < stored b ↔ a < b := by
  constructor
  · intro h
    by_contra hn
    exact absurd h (not_lt.mpr (stored_mono (le_of_not_gt hn)))
  · exact Recon.stored_strictMono

theorem pairwise_getLast' {α : Type} {R : α → α → Prop} {l : List α} (hl : l.Pairwise R)
    {x : α} (hx : l.getLast? = some x) {y : α} (hy : y ∈ l) : y = x ∨ R y x := by
  obtain ⟨front, rfl⟩ := List.getLast?_eq_some_iff.mp hx
  rw [List.pairwise_append] at hl
  rcases List.mem_append.mp hy with hy | hy
  · exact Or.inr (hl.2.2 y hy x (by simp))
  · exact Or.inl (List.mem_singleton.mp hy)

/-- The highest node of a column at or below a row. -/
theorem highestAtMost_spec {M : Mountain} {l : Nat} {row : Row} {p : Ref}
    (h : highestAtMost M l row = some p) :
    p.column = l ∧ 0 < p.index ∧ ∃ col : Column, M[l]? = some col ∧
      ∃ hp : p.index < col.size, col[p.index].row ≤ row ∧
        ∀ j (hj : j < col.size), 0 < j → col[j].row ≤ row → j ≤ p.index := by
  simp only [highestAtMost, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨col, hcol, j, hj, rfl⟩ := h
  have hmem := List.mem_of_getLast? hj
  rw [List.mem_filter, List.mem_range] at hmem
  obtain ⟨hjs, hjP⟩ := hmem
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hjP
  obtain ⟨hj0, hjrow⟩ := hjP
  rw [Array.getElem?_eq_getElem hjs] at hjrow
  simp only [decide_eq_true_eq] at hjrow
  refine ⟨rfl, hj0, col, hcol, hjs, hjrow, ?_⟩
  intro j' hj' hj'0 hj'row
  have hmem' : j' ∈ (List.range col.size).filter fun j =>
      0 < j && (match col[j]? with | some c => decide (c.row ≤ row) | none => false) := by
    rw [List.mem_filter, List.mem_range]
    refine ⟨hj', ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨hj'0, ?_⟩
    rw [Array.getElem?_eq_getElem hj']
    simpa using hj'row
  have hpw : ((List.range col.size).filter fun j =>
      0 < j && (match col[j]? with | some c => decide (c.row ≤ row) | none => false)).Pairwise
        (· < ·) := (List.pairwise_lt_range).filter _
  rcases pairwise_getLast' hpw hj hmem' with h' | h'
  · exact le_of_eq h'
  · exact le_of_lt h'

theorem cell?_column {M : Mountain} {p : Ref} {c : Cell} (h : cell? M p = some c) :
    ∃ col : Column, M[p.column]? = some col ∧ ∃ hp : p.index < col.size, col[p.index] = c := by
  unfold cell? at h
  cases hcol : M[p.column]? with
  | none => simp [hcol] at h
  | some col =>
      simp only [hcol, Option.bind_eq_bind, Option.bind_some] at h
      obtain ⟨hp, rfl⟩ := Array.getElem?_eq_some_iff.mp h
      exact ⟨col, rfl, hp, rfl⟩

/-- Rows strictly increase up a column of a valid mountain. -/
theorem cell_row_lt {M : Mountain} (hV : MountainValid M) {c a b : Nat} {x y : Cell}
    (hx : cell? M ⟨c, a⟩ = some x) (hy : cell? M ⟨c, b⟩ = some y) (hab : a < b) :
    x.row < y.row := by
  obtain ⟨col, hcol, ha, rfl⟩ := cell?_column hx
  obtain ⟨col', hcol', hb, rfl⟩ := cell?_column hy
  simp only at hcol hcol' ha hb ⊢
  rw [hcol] at hcol'
  cases hcol'
  obtain ⟨hc, hcolEq⟩ := column_of_getElem? hcol
  have hCV := hV c hc
  rw [hcolEq] at hCV
  exact hCV.rows_strict a b col[a] col[b] (Array.getElem?_eq_getElem ha)
    (Array.getElem?_eq_getElem hb) hab

theorem cell_index_le {M : Mountain} (hV : MountainValid M) {c a b : Nat} {x y : Cell}
    (hx : cell? M ⟨c, a⟩ = some x) (hy : cell? M ⟨c, b⟩ = some y) (h : x.row ≤ y.row) :
    a ≤ b := by
  by_contra hn
  exact absurd h (not_le.mpr (cell_row_lt hV hy hx (by omega)))

/-- The cells of a column made by `copyColumn` carry the stored rows of the emits. -/
theorem cells_of_copy {R : Mountain} {ctx : Context} {τ : Row} {X : Nat} {c : Column}
    {es : List (Emit × Origin)} (hRX : R[X]? = some c) (hcopy : copyColumn ctx τ = .ok c)
    (hes : emitsT ctx τ = .ok es) :
    c.size = es.length + 1 ∧ ∀ k (hk : k < es.length), ∃ cell, cell? R ⟨X, k + 1⟩ = some cell ∧
      cell.row = stored es[k].1.row := by
  obtain ⟨es', hes', hasm⟩ := copyColumn_emitsT hcopy
  have hee : es' = es := Except.ok.inj (hes'.symm.trans hes)
  subst hee
  obtain ⟨hsize, hcells⟩ := assemble_spec hasm
  simp only [List.length_map] at hsize
  refine ⟨hsize, fun k hk => ?_⟩
  obtain ⟨cell, hcell, hrow, _⟩ := hcells k (by simpa using hk)
  refine ⟨cell, ?_, by simpa using hrow⟩
  simp [cell?, hRX, hcell]

/-- A column `y + w·i` with `cr < y < x₀`, `i ≥ 1` is produced only by block `i` from `y`. -/
theorem blockCol_unique_inner {cr x0 n i i' y x' : Nat} (hcr : cr < x0) (hy : cr < y) (hyx : y < x0)
    (hi : 0 < i) (hx' : x' ∈ blockColumns cr x0 n i')
    (heq : y + (x0 - cr) * i = x' + (x0 - cr) * i') : i' = i ∧ x' = y := by
  have hw : 0 < x0 - cr := by omega
  have hx'le : x' ≤ x0 ∧ (0 < i' → cr < x') := by
    unfold blockColumns at hx'
    split at hx'
    · simp only [List.mem_singleton] at hx'
      exact ⟨by omega, fun h => by omega⟩
    · simp only [List.mem_range'_1] at hx'
      exact ⟨by split at hx' <;> omega, fun _ => by omega⟩
  rcases Nat.lt_trichotomy i' i with h | h | h
  · obtain ⟨d, rfl⟩ : ∃ d, i = i' + d + 1 := ⟨i - i' - 1, by omega⟩
    have h1 : (x0 - cr) * (i' + d + 1) = (x0 - cr) * i' + (x0 - cr) * (d + 1) := by
      rw [show i' + d + 1 = i' + (d + 1) by omega, Nat.mul_add]
    have h2 : x0 - cr ≤ (x0 - cr) * (d + 1) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  · subst h
    exact ⟨rfl, by omega⟩
  · obtain ⟨d, rfl⟩ : ∃ d, i' = i + d + 1 := ⟨i' - i - 1, by omega⟩
    have h1 : (x0 - cr) * (i + d + 1) = (x0 - cr) * i + (x0 - cr) * (d + 1) := by
      rw [show i + d + 1 = i + (d + 1) by omega, Nat.mul_add]
    have h2 : x0 - cr ≤ (x0 - cr) * (d + 1) := Nat.le_mul_of_pos_right _ (by omega)
    have := hx'le.2 (by omega)
    omega

/-! ## The statements -/

/-- The emits of the copy of the column `y` in block `i` (the column `y + w·i`). -/
def blockEmits (M R : Mountain) (cr x0 : Nat) (τ : Row) (i y : Nat) :
    Result (List (Emit × Origin)) :=
  emitsT (ctxAt M R y i cr (x0 - cr) x0 (y + (x0 - cr) * i)) τ

/-- The data of a splice expansion shared by the statements below. -/
structure SpliceData (s : List Nat) (n D : Nat) (M : Mountain) (out : List Nat) (ρ : Root)
    (R : Mountain) (t : Cell) : Prop where
  splice : SpliceCase s n D M out ρ
  deg : DegreeOK s D
  run : Official.expandDiagram s n = .ok R
  canon : Canonical.build out = .ok R
  last : ∃ col : Column, M[M.size - 1]? = some col ∧ col.back? = some t

theorem Site.data {s : List Nat} {n D : Nat} {M : Mountain} {out : List Nat} {ρ : Root}
    {R : Mountain} {t : Cell} {X x i : Nat} {es : List (Emit × Origin)}
    (h : Site s n D M out ρ R t X x i es) : SpliceData s n D M out ρ R t :=
  ⟨h.splice, h.deg, h.run, h.canon, h.last⟩

/-- (A, open) The rows of the non-cut copies are ordered like the rows of their origins,
across all columns of a block. -/
def CopyOrder : Prop :=
  ∀ s n D M out ρ R t, SpliceData s n D M out ρ R t → ∀ i, 0 < i → i < n + 1 →
    ∀ y y' es es', y ∈ blockColumns ρ.cr ρ.x0 n i → y' ∈ blockColumns ρ.cr ρ.x0 n i →
      blockEmits M R ρ.cr ρ.x0 (official t.row) i y = .ok es →
      blockEmits M R ρ.cr ρ.x0 (official t.row) i y' = .ok es' →
      ∀ k (hk : k < es.length) k' (hk' : k' < es'.length),
        cutOrigin es[k].2 = false → cutOrigin es'[k'].2 = false →
        ∀ c c', cell? M es[k].2.src = some c → cell? M es'[k'].2.src = some c' →
          (c.row < c'.row → es[k].1.row < es'[k'].1.row) ∧
            (c.row = c'.row → es[k].1.row = es'[k'].1.row)

/-- (B, open) In an inner column every node is the origin of a non-cut copy. -/
def CopyEmitted : Prop :=
  ∀ s n D M out ρ R t, SpliceData s n D M out ρ R t → ∀ i, 0 < i → i < n + 1 →
    ∀ y es, ρ.cr < y → y < ρ.x0 → blockEmits M R ρ.cr ρ.x0 (official t.row) i y = .ok es →
      ∀ (p : Ref) c, p.column = y → 1 ≤ p.index → cell? M p = some c →
        ∃ k, ∃ hk : k < es.length, es[k].2.src = p ∧ cutOrigin es[k].2 = false

/-- (C1) In an inner column the origin rows of the emits do not decrease (proved:
`ChainCorrCopyMono.copyMono`). -/
def CopyMono : Prop :=
  ∀ s n D M out ρ R t, SpliceData s n D M out ρ R t → ∀ i, 0 < i → i < n + 1 →
    ∀ y es, ρ.cr < y → y < ρ.x0 → blockEmits M R ρ.cr ρ.x0 (official t.row) i y = .ok es →
      ∀ k k' (hk : k < es.length) (hk' : k' < es.length), k ≤ k' →
        ∀ c c', cell? M es[k].2.src = some c → cell? M es[k'].2.src = some c' → c.row ≤ c'.row

/-- (C2, open) In an inner column the first emit of every origin is not a gap copy. -/
def CopyFirst : Prop :=
  ∀ s n D M out ρ R t, SpliceData s n D M out ρ R t → ∀ i, 0 < i → i < n + 1 →
    ∀ y es, ρ.cr < y → y < ρ.x0 → blockEmits M R ρ.cr ρ.x0 (official t.row) i y = .ok es →
      ∀ k (hk : k < es.length),
        (∀ k' (hk' : k' < es.length), k' < k → es[k'].2.src ≠ es[k].2.src) →
        cutOrigin es[k].2 = false

/-- (open) A gap copy of `pa` at or below the row of `u` occurs only when `pa` is the top of
its column. -/
def CutTop : Prop :=
  ∀ s n D M out ρ R t X x i es, Site s n D M out ρ R t X x i es →
    ∀ j (hj : j < es.length), cutOrigin es[j].2 = false →
    ∀ cu cv ref l pe pa cpe cpa, Legs M R X j es[j].2 cu cv ref l pe pa cpe cpa →
      ρ.cr < l.column →
      ∀ esl, blockEmits M R ρ.cr ρ.x0 (official t.row) i l.column = .ok esl →
      ∀ k (hk : k < esl.length), cutOrigin esl[k].2 = true → esl[k].2.src = pa →
        esl[k].1.row ≤ es[j].1.row → rawParent M pa = none


/-! ## The reduction -/

/-- The origin of an emit of an inner column is a real node of that column. -/
theorem src_of_inner {M R : Mountain} {cr x0 : Nat} {τ : Row} {i y : Nat}
    {es : List (Emit × Origin)} (hy : y ≠ x0)
    (hes : blockEmits M R cr x0 τ i y = .ok es) (k : Nat) (hk : k < es.length) :
    es[k].2.src.column = y ∧ 1 ≤ es[k].2.src.index ∧ ∃ c, cell? M es[k].2.src = some c := by
  obtain ⟨hcol, hidx, c, hc, _⟩ := emitsT_good hes es[k] (List.getElem_mem hk)
  refine ⟨?_, hidx, c, hc⟩
  rw [hcol]
  split
  · simp [upperColumn, ctxAt, hy]
  · simp [ctxAt]

theorem upperColumn_le {M R : Mountain} {x i cr w x0 X : Nat} (hcr : cr ≤ x0) (hx : x ≤ x0) :
    upperColumn (ctxAt M R x i cr w x0 X) ≤ x0 := by
  unfold upperColumn ctxAt
  dsimp only
  split <;> omega

theorem ref_eq_of {a b : Ref} (h1 : a.column = b.column) (h2 : a.index = b.index) : a = b := by
  cases a
  cases b
  simp_all

/-- **`StartCopy` from the profile of a block.** -/
theorem startCopy_of_parts (hA : CopyOrder) (hB : CopyEmitted) (hC1 : CopyMono)
    (hC2 : CopyFirst) (hT : CutTop) : StartCopy := by
  intro s n D M out ρ R t X x i es hS j hj hnc cu cv ref l pe pa cpe cpa hL hlt
  have hdat := hS.data
  have hV := build_valid_of_success hS.splice.build
  have hVR := build_valid_of_success hS.canon
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
  -- the leg column of the origin
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
  -- the column `L = y + w·i` of the output
  obtain ⟨hpecol, hpe0, colL, hcolL, hpeL, hperow, hpemax⟩ := highestAtMost_spec hL.hpe
  have hL0 : ρ.x0 ≤ ref.column := by
    rw [himg]
    have : ρ.x0 - ρ.cr ≤ (ρ.x0 - ρ.cr) * i := Nat.le_mul_of_pos_right _ hipos
    omega
  obtain ⟨hLsz, _⟩ := column_of_getElem? hcolL
  obtain ⟨i', x', hi', hx', hLeq, hcopyL⟩ := hinv.2.2 ref.column hLsz hL0
  obtain ⟨hii, hxy⟩ := blockCol_unique_inner hcrx hlt hyx hipos hx' (by rw [← himg]; exact hLeq)
  subst i' x'
  have hcolL' : R[ref.column]? = some R[ref.column] := Array.getElem?_eq_getElem hLsz
  have hcc : colL = R[ref.column] := Option.some.inj (hcolL.symm.trans hcolL')
  obtain ⟨esl, hesl, _⟩ := copyColumn_emitsT hcopyL
  obtain ⟨hszL, hcellsL⟩ := cells_of_copy hcolL' hcopyL hesl
  have hbl : blockEmits M R ρ.cr ρ.x0 (official t.row) i l.column = .ok esl := by
    have h' : l.column + (ρ.x0 - ρ.cr) * i = ref.column := himg.symm
    simp only [blockEmits, h']
    exact hesl
  -- the row of the node `u`
  obtain ⟨cX, hRX, hcopyX⟩ := hS.copy
  obtain ⟨_, hcellsX⟩ := cells_of_copy hRX hcopyX hS.emits
  obtain ⟨cellu, hcellu, hrowu⟩ := hcellsX j hj
  have hrowcu : cu.row = stored es[j].1.row := by
    rw [Option.some.inj (hL.hcu.symm.trans hcellu)]
    exact hrowu
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
  have hle_ks : ∀ k (hk : k < esl.length), esl[k].1.row ≤ es[j].1.row → k ≤ pe.index - 1 := by
    intro k hk hrk
    have hk' : k + 1 < colL.size := by rw [hcc, hszL]; omega
    have h1 := hpemax (k + 1) hk' (by omega) (by
      rw [hrowL k hk hk', hrowcu]
      exact stored_mono hrk)
    omega
  have hks_le : esl[pe.index - 1].1.row ≤ es[j].1.row := by
    have h1 : (colL[pe.index]'hpeL).row ≤ cu.row := hperow
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
  obtain ⟨hpacol, hpa0, colY, hcolY, hpaY, hparow, hpamax⟩ := highestAtMost_spec hL.hpa
  obtain ⟨colY', hcolY', hpaY', hcpaY⟩ := cell?_column hL.hcpa
  have hYY : colY' = colY := Option.some.inj (hcolY'.symm.trans (by rw [hpacol]; exact hcolY))
  subst colY'
  have hcpa_le : cpa.row ≤ cv.row := by rw [← hcpaY]; exact hparow
  -- (B): the non-cut copy of `pa`
  obtain ⟨kπ, hkπ, hkπsrc, hkπnc⟩ := hB s n D M out ρ R t hdat i hipos hS.iLt l.column esl hlt
    hyx hbl pa cpa hpacol (by omega) hL.hcpa
  have hcpaπ : cell? M esl[kπ].2.src = some cpa := by rw [hkπsrc]; exact hL.hcpa
  have hkπ_le : kπ ≤ pe.index - 1 := by
    apply hle_ks kπ hkπ
    rcases lt_or_eq_of_le hcpa_le with h | h
    · have hA' := hA s n D M out ρ R t hdat i hipos hS.iLt l.column x esl es hymem hS.xMem hbl
        hblx kπ hkπ j hj hkπnc hnc cpa cv hcpaπ hL.hcv
      exact le_of_lt (hA'.1 h)
    · have hA' := hA s n D M out ρ R t hdat i hipos hS.iLt l.column x esl es hymem hS.xMem hbl
        hblx kπ hkπ j hj hkπnc hnc cpa cv hcpaπ hL.hcv
      exact le_of_eq (hA'.2 h)
  -- the origin `ν` of the emit at `pe.index - 1`
  obtain ⟨hνcol, hν1, cν, hcν⟩ := src_of_inner (ne_of_lt hyx) hbl (pe.index - 1) hksl
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
    apply hC2 s n D M out ρ R t hdat i hipos hS.iLt l.column esl hlt hyx hbl k0 hk0l
    intro k' hk' hlt' heq
    exact hk0min k' hk' hlt' (heq.trans hk0src)
  have hcν0 : cell? M esl[k0].2.src = some cν := by rw [hk0src]; exact hcν
  -- the origin of the emit at `pe.index - 1` is at or below `σ`
  have hcν_le : cν.row ≤ cv.row := by
    by_contra hn
    have hlt' : cv.row < cν.row := lt_of_not_ge hn
    have hA' := hA s n D M out ρ R t hdat i hipos hS.iLt x l.column es esl hS.xMem hymem hblx
      hbl j hj k0 hk0l hnc hk0nc cv cν hL.hcv hcν0
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
    have hmono := hC1 s n D M out ρ R t hdat i hipos hS.iLt l.column esl hlt hyx hbl kπ
      (pe.index - 1) hkπ hksl hkπ_le cpa cν hcpaπ hcν
    have hpa' : cell? M ⟨l.column, pa.index⟩ = some cpa := by
      rw [← hpacol]; exact hL.hcpa
    have hν' : cell? M ⟨l.column, esl[pe.index - 1].2.src.index⟩ = some cν := by
      rw [← hνcol]; exact hcν
    have hidx_ge : pa.index ≤ esl[pe.index - 1].2.src.index := cell_index_le hV hpa' hν' hmono
    exact ref_eq_of (by rw [hνcol, hpacol]) (le_antisymm hidx_le hidx_ge)
  -- the copy node
  refine ⟨l.column, esl, pe.index - 1, hlt, hyx, hymem, by rw [hpecol, himg], hpeidx,
    by rw [hpecol]; exact hesl, hksl, hνpa, ?_⟩
  cases hcut : cutOrigin esl[pe.index - 1].2
  · exact Or.inl rfl
  · exact Or.inr (hT s n D M out ρ R t X x i es hS j hj hnc cu cv ref l pe pa cpe cpa hL hlt esl
      hbl (pe.index - 1) hksl hcut hνpa hks_le)

end OmegaY.Official.Classification.Proofs.ChainCorr

#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.startCopy_of_parts

