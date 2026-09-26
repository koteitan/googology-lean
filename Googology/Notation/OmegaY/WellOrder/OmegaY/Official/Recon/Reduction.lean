/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/Reduction.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.Execution

set_option backward.do.legacy false

/-!
# `ReconstructionHolds` from two statements about the new columns

`Reconstruction.ReconstructionHolds` says that the mountain assembled by the official
expansion is the canonical mountain of its values. This file reduces it to two
statements about the columns `X ≥ x₀` of the assembled mountain `R` (the columns
left of `x₀` are those of `M(s)`, and the deleting expansions need nothing):

* `BottomHolds` — the bottom real cell of every new column `X` is at stored row `1`
  and its left endpoint is the phantom `⟨X - 1, 0⟩` of the previous column (the
  first emitted node of `copyColumn` is the official row `0`, with no source leg or
  the source leg `x - 1`);
* `NewGeometryHolds` — every new column has the parent geometry of Phyrion's
  reconstruction (`Expansion.ColumnParentGeometry`): for every real node `u` with a
  node `u⁺` above it, the stored left endpoint of `u⁺` is the canonical parent search
  answer `findParent R u`, and the row of `u⁺` is `Row.B (row u) (row of that parent)`.

Everything else is proved: the validity of every new column, the value sums and the
value-1 tops (from `Expansion.finish`), and the certificate of the unchanged prefix
(from the canonical mountain of `s` without its last term).

* `certified_of_inv`: a run output with the two statements for its new columns is
  `Certified`.
* `reconstructionHolds_of_open`: `BottomHolds → NewGeometryHolds → ReconstructionHolds`.
* `blockReconstruction_of_reconstructionHolds`: the hypothesis of
  `Dimension.output_degree` follows from `ReconstructionHolds`.
-/

namespace OmegaY.Official.Recon

open Canonical Expansion Dimension

/-! ## The statements on the new columns -/

/-- The bottom real cell of column `c` is at stored row `1` with the left endpoint the
phantom of column `c - 1`. -/
def BottomOK (c : Nat) (col : Column) : Prop :=
  ∃ b : Cell, col[1]? = some b ∧ b.row = 1 ∧ b.left = some ⟨c - 1, 0⟩

/-- The bottom of every new column. Proved in `FirstEmit.lean` (`bottomHolds`). -/
def BottomHolds : Prop :=
  ∀ (s : List Nat) (n : Nat) (R : Mountain), Official.expandDiagram s n = .ok R →
    ∀ c (hc : c < R.size), s.length - 1 ≤ c → BottomOK c R[c]

/-- The parent geometry of every new column. Reduced in `Search.lean` to `RowLawHolds` and
`ChainHolds` (`newGeometryHolds_of_parts`). -/
def NewGeometryHolds : Prop :=
  ∀ (s : List Nat) (n : Nat) (R : Mountain), Official.expandDiagram s n = .ok R →
    ∀ c (hc : c < R.size), s.length - 1 ≤ c → ColumnParentGeometry R c R[c]

/-! ## One new column -/

theorem nodup_rows {cells : List Cell} (hrows : (cells.map Cell.row).Pairwise (· < ·))
    (hne : ∀ cell ∈ cells, cell.row ≠ 0) : ((phantom :: cells).map Cell.row).Nodup := by
  simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and]
  refine ⟨fun cell hc he => hne cell hc (by rw [he]; rfl), ?_⟩
  exact hrows.imp (fun h => ne_of_lt h)

/-- The parent read by `below` in a valid mountain: an existing cell of a smaller row, and
a real one when the row is above `1`. -/
theorem below_parent {m : Mountain} (hV : MountainValid m) {q : Nat} {nodes : Column}
    (hq : m[q]? = some nodes) {row : Row} {ref : Ref} (h : Expansion.below m q row = .ok ref) :
    ∃ parent, Expansion.lookup m ref = .ok parent ∧ ref.column < m.size ∧ parent.row < row ∧
      ((1 : Row) < row → 0 < parent.value) := by
  obtain ⟨hcol, parent, hp, hrow⟩ := below_result hq h
  have hqs : q < m.size := (Array.getElem?_eq_some_iff.mp hq).1
  have hnodes : m[q] = nodes := (Array.getElem?_eq_some_iff.mp hq).2
  have hCV : ColumnValid m q nodes := hnodes ▸ hV q hqs
  refine ⟨parent, lookup_ok_iff.mpr ⟨nodes, by rw [hcol]; exact hq, hp⟩, by omega, hrow, ?_⟩
  intro h1
  obtain ⟨b1, hb1⟩ : ∃ b1, nodes[1]? = some b1 :=
    ⟨nodes[1]'(by have := hCV.size_ge_two; omega),
      Array.getElem?_eq_getElem (by have := hCV.size_ge_two; omega)⟩
  have hb1row : b1.row = 1 := hCV.bottom_row b1 hb1
  have hidx : 1 ≤ ref.index := below_max_index hq h hb1 (by rw [hb1row]; exact h1)
  exact hCV.real_positive ref.index parent hp (by omega)

/-- **One new column.** A `NewCol` column with the bottom extends the basic facts. -/
theorem basic_push_newCol {m : Mountain} (h : Basic m) (hpos : 0 < m.size)
    {col : Column} (hN : NewCol m col) (hB : BottomOK m.size col) : Basic (m.push col) := by
  obtain ⟨cells, hfin, hrows, hne, hlegs⟩ := hN
  obtain ⟨b, hb, hbrow, hbleft⟩ := hB
  obtain ⟨hShape, hFinished⟩ := Expansion.finish_success_spec hfin
  have hShape' : ColumnShape (finishSort (phantom :: cells)) col := hShape
  have hmem : ∀ cell ∈ phantom :: cells, cell ≠ phantom → cell ∈ cells := by
    intro cell hc hne'
    rcases List.mem_cons.mp hc with rfl | hc
    · exact absurd rfl hne'
    · exact hc
  have hInput : FinishInput m (phantom :: cells) := by
    refine ⟨nodup_rows hrows hne, List.mem_cons_self, ?_, ?_⟩
    · obtain ⟨orig, horig, hsame⟩ := hShape'.getElem hb
      refine ⟨orig, (finishSort_perm _).mem_iff.mp (List.mem_of_getElem? horig), ?_⟩
      rw [hsame.1, hbrow]
    · intro cell hc h1
      have hcell : cell ∈ cells := hmem cell hc (by
        intro he
        rw [he] at h1
        exact absurd h1 (not_lt.mpr (Row.zero_le 1)))
      obtain ⟨ref, hleft, hcase⟩ := hlegs cell hcell
      rcases hcase with ⟨hr1, _⟩ | ⟨q, nodes, hq, hbelow⟩
      · rw [hr1] at h1
        exact absurd h1 (lt_irrefl _)
      · obtain ⟨parent, hl, _, _, hvp⟩ := below_parent h.valid hq hbelow
        exact ⟨ref, parent, hleft, hl, hvp h1⟩
  have hExists : ∀ cell ∈ phantom :: cells, cell.row ≠ 0 → ∃ ref, cell.left = some ref := by
    intro cell hc h0
    have hcell : cell ∈ cells := hmem cell hc (by intro he; rw [he] at h0; exact h0 rfl)
    obtain ⟨ref, hleft, _⟩ := hlegs cell hcell
    exact ⟨ref, hleft⟩
  have hStored : ∀ cell ∈ phantom :: cells, ∀ ref, cell.left = some ref →
      ∃ parent, Expansion.lookup m ref = .ok parent ∧ ref.column < m.size ∧
        parent.row ≤ cell.row := by
    intro cell hc ref hleft
    have hcell : cell ∈ cells := hmem cell hc (by intro he; rw [he] at hleft; cases hleft)
    obtain ⟨ref', hleft', hcase⟩ := hlegs cell hcell
    have href : ref' = ref := Option.some.inj (hleft'.symm.trans hleft)
    subst href
    rcases hcase with ⟨_, rfl⟩ | ⟨q, nodes, hq, hbelow⟩
    · have hlast : m.size - 1 < m.size := by omega
      have hCV := h.valid (m.size - 1) hlast
      refine ⟨phantom, lookup_ok_iff.mpr ⟨m[m.size - 1], Array.getElem?_eq_getElem hlast,
        hCV.phantom⟩, hlast, ?_⟩
      exact Row.zero_le _
    · obtain ⟨parent, hl, hc', hr, _⟩ := below_parent h.valid hq hbelow
      exact ⟨parent, hl, hc', le_of_lt hr⟩
  obtain ⟨hCV, _⟩ := hInput.output_valid hpos hExists hStored hShape' hFinished
  refine h.push hCV hFinished hb ?_
  rw [if_neg (by omega), hbleft]

/-! ## The whole output -/

/-- Transport of the parent geometry of column `c` between mountains that agree on the
columns up to `c`. -/
theorem columnParentGeometry_transport {R R' : Mountain} {c : Nat} {col : Column}
    (hV : ∀ (i : Nat) (cell : Cell) (ref : Ref), col[i]? = some cell → cell.left = some ref →
      ref.column < c)
    (hagree : ∀ i, i ≤ c → R[i]? = R'[i]?) (h : ColumnParentGeometry R c col) :
    ColumnParentGeometry R' c col := by
  intro i lower upper hl hu hi
  obtain ⟨ref, parent, hleft, hcell, hfind, hrow⟩ := h i lower upper hl hu hi
  have href := hV _ _ _ hu hleft
  refine ⟨ref, parent, hleft, ?_, ?_, hrow⟩
  · rw [← cellAt_eq_of_column_eq (hagree ref.column (by omega))]
    exact hcell
  · rw [← findParent_eq_of_columns (fun j hj => hagree j hj)]
    exact hfind

theorem extract_pop_of_inv {M R : Mountain} (hI : Inv M (M.size - 1) R) :
    R.extract 0 (M.size - 1) = M.pop := by
  obtain ⟨hs, hpre, _⟩ := hI
  apply Array.ext_getElem?
  intro i
  by_cases hi : i < M.size - 1
  · rw [Array.getElem?_pop, if_pos (by omega), ← hpre i hi]
    simp [hi, show i < R.size by omega]
  · rw [Array.getElem?_pop, if_neg (by omega)]
    simp [Array.getElem?_extract]
    omega

/-- **The basic facts of a run output**, given the bottoms of its new columns. -/
theorem basic_of_inv {s : List Nat} {M R : Mountain} (hb : Canonical.build s = .ok M)
    (hI : Inv M (M.size - 1) R)
    (hB : ∀ c (hc : c < R.size), M.size - 1 ≤ c → BottomOK c R[c]) :
    Basic R := by
  have hpop := extract_pop_of_inv hI
  obtain ⟨hs, hpre, hnew⟩ := hI
  set x0 := M.size - 1 with hx0
  have hbase : Basic (R.extract 0 x0) := by
    rw [hpop]
    exact (certified_of_build (Reconstruction.build_dropLast hb)).toBasic
  have hstep : ∀ k, x0 + k ≤ R.size → Basic (R.extract 0 (x0 + k)) := by
    intro k
    induction k with
    | zero => intro _; simpa using hbase
    | succ k ih =>
      intro hk
      have hlt : x0 + k < R.size := by omega
      rw [show x0 + (k + 1) = (x0 + k) + 1 by omega, Array.extract_succ_right (by omega) hlt]
      have hmsize : (R.extract 0 (x0 + k)).size = x0 + k := by simp; omega
      obtain ⟨hpos, hN⟩ := hnew (x0 + k) hlt (by omega)
      have hBc : BottomOK (R.extract 0 (x0 + k)).size R[x0 + k] := by
        rw [hmsize]
        exact hB (x0 + k) hlt (by omega)
      exact basic_push_newCol (ih (by omega)) (by omega) hN hBc
  have := hstep (R.size - x0) (by omega)
  rw [show x0 + (R.size - x0) = R.size by omega, Array.extract_eq_self_of_le (le_refl _)] at this
  exact this

/-- **The parent geometry of the columns left of `x₀`** (those of `M(s)`). -/
theorem prefix_geometry {s : List Nat} {M R : Mountain} (hb : Canonical.build s = .ok M)
    (hI : Inv M (M.size - 1) R) :
    ∀ c (hc : c < R.size), c < M.size - 1 → ColumnParentGeometry R c R[c] := by
  intro c hc hcx
  have hpop := extract_pop_of_inv hI
  obtain ⟨hs, hpre, _⟩ := hI
  have hcert := certified_of_build (Reconstruction.build_dropLast hb)
  rw [← hpop] at hcert
  have hce : c < (R.extract 0 (M.size - 1)).size := by simp; omega
  have hcol : (R.extract 0 (M.size - 1))[c] = R[c] := by simp
  have hG := hcert.geometry c hce
  have hV := hcert.valid c hce
  rw [hcol] at hG hV
  refine columnParentGeometry_transport (fun i cell ref hci hleft =>
    (hV.stored_valid i cell ref hci hleft).1) ?_ hG
  intro i hi
  simp [show i < M.size - 1 by omega, show i < R.size by omega]

/-- **A run output with the two open statements is certified.** -/
theorem certified_of_inv {s : List Nat} {M R : Mountain} (hb : Canonical.build s = .ok M)
    (hI : Inv M (M.size - 1) R)
    (hB : ∀ c (hc : c < R.size), M.size - 1 ≤ c → BottomOK c R[c])
    (hG : ∀ c (hc : c < R.size), M.size - 1 ≤ c → ColumnParentGeometry R c R[c]) :
    Certified R := by
  refine certified_of_basic (basic_of_inv hb hI hB) ?_
  intro c hc
  rcases Nat.lt_or_ge c (M.size - 1) with h | h
  · exact prefix_geometry hb hI c hc h
  · exact hG c hc h

/-- **Reduction of `ReconstructionHolds`.** -/
theorem reconstructionHolds_of_open (hB : BottomHolds) (hG : NewGeometryHolds) :
    Reconstruction.ReconstructionHolds := by
  intro s n R out hR hv
  obtain ⟨M, hM, _⟩ := Reconstruction.expandDiagram_cases hR
  have hI := expandDiagram_inv hM n R hR
  have hMs := Canonical.build_size hM
  refine reconstruct_of_certified (certified_of_inv hM hI ?_ ?_) hv
  · intro c hc hx
    exact hB s n R hR c hc (by omega)
  · intro c hc hx
    exact hG s n R hR c hc (by omega)

/-- The hypothesis of `Dimension.output_degree` is a special case of
`ReconstructionHolds`. -/
theorem blockReconstruction_of_reconstructionHolds (h : Reconstruction.ReconstructionHolds) :
    Dimension.BlockReconstruction :=
  fun s n R out _ hR hv => h s n R out hR hv

end OmegaY.Official.Recon

#print axioms OmegaY.Official.Recon.certified_of_inv
#print axioms OmegaY.Official.Recon.reconstructionHolds_of_open
