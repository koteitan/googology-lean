/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/JumpLawBase.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.RowLawColumn
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Columns
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.ChainsCanonParent

set_option backward.do.legacy false

/-!
# The jump law, column by column

`RowLaw.JumpLawHolds` (`RowLawColumn.lean`) is a statement about the cells of the output
mountain `R`. This file restates it for the emitted nodes of one new column
(`ColJump`), in official rows:

* consecutive emitted nodes `em k`, `em (k+1)` with `row (k+1) = bump (row k) e`;
* the source leg `l` of `em (k+1)` and the output column `legCol ctx l = φ_i(l)` where the
  parent is read (`Official.assemble`);
* the highest official row `p` of that column below `row (k+1)` (`HighestBelow`);

and asks `jump (row k) p = e`. `jumpLawHolds_of_col` proves `JumpLawHolds` from
`ColJumpHolds`, the same statement for every new column of every splice run. The
translation uses `Expansion.below` (the parent is the highest cell below the new row), the
validity of the output (`basic_of_inv`), and `jump (stored a) (stored b) = jump a b`.
-/

namespace OmegaY.Official.Recon.JumpLaw

open Canonical Expansion Dimension RowLaw

/-! ## Rows -/

theorem stored_inj {a b : Row} (h : stored a = stored b) : a = b :=
  (show StrictMono stored from fun _ _ h => stored_strictMono h).injective h

theorem jump_stored (a b : Row) : Row.jump (stored a) (stored b) = Row.jump a b := by
  apply Nat.le_antisymm
  · rw [Row.jump_le_iff]
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · have hab : a = b := Row.jump_eq_zero.mp (by omega)
      rw [hab]
    · rw [coeff_stored_pos _ hpos, coeff_stored_pos _ hpos]
      exact Row.coeff_eq_of_jump_le le_rfl hi
  · rw [Row.jump_le_iff]
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · have hab : stored a = stored b := Row.jump_eq_zero.mp (by omega)
      rw [stored_inj hab]
    · rw [← coeff_stored_pos a hpos, ← coeff_stored_pos b hpos]
      exact Row.coeff_eq_of_jump_le le_rfl hi

theorem one_le_stored (ρ : Row) : (1 : Row) ≤ stored ρ :=
  row_one_le_of_ne_zero (stored_ne_zero ρ)

theorem official_stored (ρ : Row) : official (stored ρ) = ρ :=
  stored_inj (Classification.stored_official (one_le_stored ρ))

theorem bump_exponent_inj {a : Row} {e e' : Nat} (h : Row.bump a e = Row.bump a e') : e = e' :=
  (Row.bump_strictMono_exponent a).injective h

/-! ## The column statement -/

/-- `p` is the highest row of `l` strictly below `θ`. -/
def HighestBelow (l : List Row) (θ p : Row) : Prop :=
  p ∈ l ∧ p < θ ∧ ∀ r ∈ l, r < θ → r ≤ p

/-- The output column read for a source leg `l` (the image `φ_i(l)`). -/
def legCol (ctx : Context) (l : Nat) : Nat :=
  if ctx.rootColumn ≤ l then l + ctx.width * ctx.block else l

/-- **The jump law for the emitted nodes of one column**, in official rows. -/
def ColJump (ctx : Context) (R : Mountain) (emits : List Emit) : Prop :=
  ∀ k (hk : k + 1 < emits.length) (l e : Nat) (p : Row),
    emits[k + 1].leftColumn = some l →
    emits[k + 1].row = Row.bump emits[k].row e →
    HighestBelow (rowsOf R (legCol ctx l)) emits[k + 1].row p →
    Row.jump emits[k].row p = e

/-- The context of the call of `copyColumn` that makes the column `x + w·i`. -/
def colCtx (M R : Mountain) (root : Ref) (i x : Nat) : Context :=
  Classification.ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1)
    (x + (M.size - 1 - root.column) * i)

/-- A new column `X = x + w·i` of a successful splice run. -/
structure NewColumn (s : List Nat) (n : Nat) (R M : Mountain) (t : Cell) (root : Ref)
    (i x : Nat) : Prop where
  run : Official.expandDiagram s n = .ok R
  top : Top s M t root
  copies : n ≠ 0
  inv : Classification.ColumnsInv M n root.column (M.size - 1 - root.column) (M.size - 1)
    (official t.row) R
  block : i < n + 1
  mem : x ∈ blockColumns root.column (M.size - 1) n i
  lt : x + (M.size - 1 - root.column) * i < R.size
  copy : ∃ col, R[x + (M.size - 1 - root.column) * i]? = some col ∧
    copyColumn (colCtx M R root i x) (official t.row) = .ok col

/-- The lower part of `copyColumn`: the emitted lists of the first items. -/
def LowerRun (ctx : Context) (τ : Row) (vs : List (List Emit)) : Prop :=
  (lowerItems τ).mapM (fun x : Nat × Item => runItem ctx x.1 x.2) = .ok vs

/-- The upper part of `copyColumn`. -/
def UpperRun (ctx : Context) (τ : Row) (us : List Emit) : Prop :=
  ((realNodes ctx.source (Classification.upperColumn ctx)).filter
      (fun p => decide (τ ≤ official p.2.row))).mapM
      (fun x : Ref × Cell => Except.bind (leftColumn x.2)
        (fun v => Except.ok ({ row := official x.2.row, leftColumn := some v } : Emit))) =
    .ok us

/-- **The jump law for every new column.** -/
def ColJumpHolds : Prop :=
  ∀ (s : List Nat) (n : Nat) (R M : Mountain) (t : Cell) (root : Ref) (i x : Nat),
    NewColumn s n R M t root i x →
    ∀ vs us, LowerRun (colCtx M R root i x) (official t.row) vs →
      UpperRun (colCtx M R root i x) (official t.row) us →
      ∀ col, assemble (colCtx M R root i x) (vs.flatten ++ us) = .ok col →
      ColJump (colCtx M R root i x) R (vs.flatten ++ us)

/-! ## The cells of an assembled column -/

theorem assemble_below {ctx : Context} {emits : List Emit} {col : Column}
    (h : assemble ctx emits = .ok col) :
    col.size = emits.length + 1 ∧ ∀ k (hk : k < emits.length), ∃ cell : Cell,
      col[k + 1]? = some cell ∧ cell.row = stored emits[k].row ∧
      (emits[k].leftColumn = none → emits[k].row = 0) ∧
      ∀ l, emits[k].leftColumn = some l → ∃ ref, cell.left = some ref ∧
        Expansion.below ctx.result (legCol ctx l) (stored emits[k].row) = .ok ref := by
  unfold assemble at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  by_cases hE : emits.isEmpty = true
  · rw [if_pos hE] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  · rw [if_neg hE] at h
    split at h
    · cases h
    · rename_i u hloop
      have hrows := Classification.forIn_check_ok
        (fun pair : Emit × Emit => pair.1.row < pair.2.row)
        (Except.error Error.rowsNotIncreasing) (fun r h' => by cases h') _ _ hloop
      split at h
      · cases h
      · rename_i cells hcells
        obtain ⟨hlen, hall⟩ := Classification.mapM_except_spec _ _ _ hcells
        have hcell : ∀ k (hk : k < emits.length) (hk' : k < cells.length),
            cells[k].row = stored emits[k].row ∧
            (emits[k].leftColumn = none → emits[k].row = 0) ∧
            ∀ l, emits[k].leftColumn = some l → ∃ ref, cells[k].left = some ref ∧
              Expansion.below ctx.result (legCol ctx l) (stored emits[k].row) = .ok ref := by
          intro k hk hk'
          have hf := hall k hk hk'
          split at hf
          · rename_i p hp
            split at hf
            · cases hf
            · rename_i ref href
              rw [(Except.ok.inj hf).symm]
              refine ⟨rfl, fun h0 => absurd (hp.symm.trans h0) (by simp), ?_⟩
              intro l hl
              rw [hp] at hl
              obtain rfl := Option.some.inj hl
              refine ⟨ref, rfl, ?_⟩
              simp only [liftE, Except.mapError] at href
              split at href
              · cases href
              · rename_i r hr
                cases href
                exact hr
          · rename_i hp
            split at hf
            · rename_i h0
              rw [(Except.ok.inj hf).symm]
              refine ⟨rfl, fun _ => h0, ?_⟩
              intro l hl
              rw [hp] at hl
              cases hl
            · simp [throw, throwThe, MonadExceptOf.throw] at hf
        simp only [liftE, Except.mapError] at h
        split at h
        · cases h
        · rename_i c hfin
          have hc : c = col := Except.ok.inj h
          subst hc
          have hshape := (Expansion.finish_success_spec hfin).1
          have hsorted : (phantom :: cells).Pairwise
              (fun a b : Cell => decide (a.row ≤ b.row) = true) := by
            have hr := Classification.pairwise_of_zip_tail hrows
            have hcr : cells.map Cell.row = emits.map (fun em => stored em.row) := by
              apply List.ext_getElem (by simp [hlen])
              intro k hk1 hk2
              simp only [List.getElem_map]
              exact (hcell k (by simpa using hk2) (by simpa using hk1)).1
            simp only [List.pairwise_cons, decide_eq_true_eq]
            refine ⟨fun a _ => by simp [phantom, Row.zero_le], ?_⟩
            have : (cells.map Cell.row).Pairwise (· ≤ ·) := by
              rw [hcr, List.pairwise_map]
              rw [List.pairwise_map] at hr
              exact hr.imp (fun hlt => Classification.stored_mono (le_of_lt hlt))
            rw [List.pairwise_map] at this
            exact this.imp (fun h' => by simpa using h')
          rw [List.mergeSort_of_pairwise hsorted] at hshape
          obtain ⟨hrowsEq, hleftsEq⟩ := hshape
          have hsize : c.size = cells.length + 1 := by
            have := congrArg List.length hrowsEq
            simp only [List.length_map, List.length_cons, Array.length_toList] at this
            omega
          refine ⟨by omega, ?_⟩
          intro k hk
          have hk' : k < cells.length := by omega
          have hkc : k + 1 < c.size := by omega
          obtain ⟨hrow, hnone, hsome⟩ := hcell k hk hk'
          have hcrow : c[k + 1].row = cells[k].row := by
            have := congrArg (fun l => l[k + 1]?) hrowsEq
            simp only [List.getElem?_map, List.getElem?_cons_succ, Array.getElem?_toList,
              List.getElem?_eq_getElem hk', Array.getElem?_eq_getElem hkc, Option.map_some,
              Option.some.injEq] at this
            exact this.symm
          have hcleft : c[k + 1].left = cells[k].left := by
            have := congrArg (fun l => l[k + 1]?) hleftsEq
            simp only [List.getElem?_map, List.getElem?_cons_succ, Array.getElem?_toList,
              List.getElem?_eq_getElem hk', Array.getElem?_eq_getElem hkc, Option.map_some,
              Option.some.injEq] at this
            exact this.symm
          refine ⟨c[k + 1], Array.getElem?_eq_getElem hkc, by rw [hcrow, hrow], hnone, ?_⟩
          intro l hl
          obtain ⟨ref, href, hb⟩ := hsome l hl
          exact ⟨ref, by rw [hcleft, href], hb⟩

/-- The emitted rows of an assembled column increase strictly. -/
theorem assemble_sorted {ctx : Context} {emits : List Emit} {col : Column}
    (h : assemble ctx emits = .ok col) : (emits.map Emit.row).Pairwise (· < ·) := by
  unfold assemble at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  by_cases hE : emits.isEmpty = true
  · rw [if_pos hE] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  · rw [if_neg hE] at h
    split at h
    · cases h
    · rename_i u hloop
      exact Classification.pairwise_of_zip_tail (Classification.forIn_check_ok
        (fun pair : Emit × Emit => pair.1.row < pair.2.row)
        (Except.error Error.rowsNotIncreasing) (fun r h' => by cases h') _ _ hloop)

/-- In a strictly increasing list, an entry below entry `k + 1` is at most entry `k`. -/
theorem le_of_consecutive {emits : List Emit} (hs : (emits.map Emit.row).Pairwise (· < ·))
    {k : Nat} (hk : k + 1 < emits.length) {em : Emit} (hem : em ∈ emits)
    (hlt : em.row < emits[k + 1].row) : em.row ≤ emits[k].row := by
  obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hem
  have hp := List.pairwise_iff_getElem.mp hs
  rcases Nat.lt_trichotomy m k with h | h | h
  · have := hp m k (by simpa using hm) (by simp; omega) h
    simp only [List.getElem_map] at this
    exact this.le
  · subst h; exact le_rfl
  · rcases Nat.eq_or_lt_of_le (show k + 1 ≤ m by omega) with h' | h'
    · subst h'; exact absurd hlt (lt_irrefl _)
    · have := hp (k + 1) m (by simp; omega) (by simpa using hm) h'
      simp only [List.getElem_map] at this
      exact absurd (this.trans hlt) (lt_irrefl _)

/-! ## The reduction -/

theorem getElem?_extract_lt {R : Mountain} {X q : Nat} (hq : q < X) :
    (R.extract 0 X)[q]? = R[q]? := by
  simp only [Array.getElem?_extract]
  by_cases hs : q < R.size
  · simp [hq, hs]
  · rw [Array.getElem?_eq_none (by omega)]
    simp [hq]
    omega

/-- **`JumpLawHolds` from the column statement.** -/
theorem jumpLawHolds_of_col (h : ColJumpHolds) : RowLaw.JumpLawHolds := by
  intro s n R hrun c hc hx index lower upper parent ref e hl hu hi hleft hcell hbump
  obtain ⟨M, hM, hcases⟩ := Reconstruction.expandDiagram_cases hrun
  have hMs := Canonical.build_size hM
  rcases hcases with ⟨rfl, rfl⟩ | ⟨_, col, t, hcol, ht, hcases⟩
  · simp only [List.length_nil] at hMs
    omega
  rcases hcases with ⟨_, rfl⟩ | ⟨hτ, hn, root, hroot, hcr, _, _⟩
  · simp at hc
    omega
  obtain ⟨_, hinv⟩ := Classification.expandDiagram_splice hrun hM hcol ht
    (by rintro (h1 | h1) <;> contradiction) hroot
  obtain ⟨i, x, hi', hxm, hX, hcopy⟩ := hinv.2.2 c hc (by omega)
  have hTop : Top s M t root := ⟨hM, by rw [hcol]; exact ht, hτ, hroot, hcr⟩
  subst hX
  have hNC : NewColumn s n R M t root i x :=
    ⟨hrun, hTop, hn, hinv, hi', hxm, hc,
      ⟨_, Array.getElem?_eq_getElem hc, hcopy⟩⟩
  obtain ⟨vs, us, hvs, hus, hasm⟩ := copyColumn_parts hcopy
  have hCJ := h s n R M t root i x hNC vs us hvs hus _ hasm
  replace hasm : assemble (colCtx M R root i x) (vs.flatten ++ us) =
      .ok R[x + (M.size - 1 - root.column) * i] := hasm
  generalize hctx : colCtx M R root i x = ctx at hCJ hasm
  generalize hemits : vs.flatten ++ us = emits at hCJ hasm
  -- the two cells
  obtain ⟨k, rfl⟩ : ∃ k, index = k + 1 := ⟨index - 1, by omega⟩
  obtain ⟨hsize, hcells⟩ := assemble_below hasm
  have hk1 : k + 1 < emits.length := by
    have := (Array.getElem?_eq_some_iff.mp hu).1
    omega
  obtain ⟨cl, hcl, hclrow, _, _⟩ := hcells k (by omega)
  obtain ⟨cu, hcu, hcurow, hcunone, hcusome⟩ := hcells (k + 1) hk1
  have hcl' : cl = lower := Option.some.inj (hcl.symm.trans hl)
  have hcu' : cu = upper := Option.some.inj (hcu.symm.trans hu)
  subst hcl' hcu'
  -- the new row is above the bottom
  have hθ : emits[k + 1].row = Row.bump emits[k].row e := by
    apply stored_inj
    rw [stored_bump, ← hcurow, ← hclrow, hbump]
  have hθpos : emits[k].row < emits[k + 1].row := by
    rw [hθ]; exact Row.lt_bump _ _
  obtain ⟨l, hlsome⟩ : ∃ l, emits[k + 1].leftColumn = some l := by
    cases hlc : emits[k + 1].leftColumn with
    | some l => exact ⟨l, rfl⟩
    | none =>
      have h0 := hcunone hlc
      rw [h0] at hθpos
      exact absurd hθpos (not_lt.mpr (Row.zero_le _))
  obtain ⟨ref', href', hbelow⟩ := hcusome l hlsome
  have hrr : ref' = ref := Option.some.inj (href'.symm.trans hleft)
  subst hrr
  -- the output is valid
  have hI := expandDiagram_inv hM n R hrun
  have hB := basic_of_inv hM hI (fun c hc hx => bottomHolds s n R hrun c hc (by omega))
  have hV := hB.valid
  -- the column read
  have hres : ctx.result = R.extract 0 (x + (M.size - 1 - root.column) * i) := by
    rw [← hctx]; rfl
  obtain ⟨nodes, hnodes⟩ := below_nodes hbelow
  have hq : legCol ctx l < x + (M.size - 1 - root.column) * i := by
    have := (Array.getElem?_eq_some_iff.mp hnodes).1
    rw [hres] at this
    simp only [Array.size_extract] at this
    omega
  have hnodesR : R[legCol ctx l]? = some nodes := by
    rw [← hnodes, hres]
    exact (getElem?_extract_lt hq).symm
  obtain ⟨hrefc, pc, hpc, hpcrow⟩ := Expansion.below_result hnodes hbelow
  have hpar : pc = parent := by
    obtain ⟨col', hcol', hcell'⟩ := cellAt_ok_iff.mp hcell
    rw [hrefc, hnodesR] at hcol'
    obtain rfl := Option.some.inj hcol'
    exact Option.some.inj (hpc.symm.trans hcell')
  subst hpar
  have hqs : legCol ctx l < R.size := (Array.getElem?_eq_some_iff.mp hnodesR).1
  have hCV : ColumnValid R (legCol ctx l) nodes := by
    have := hV _ hqs
    rwa [(Array.getElem?_eq_some_iff.mp hnodesR).2] at this
  -- the parent is real
  obtain ⟨b1, hb1⟩ : ∃ b1, nodes[1]? = some b1 :=
    ⟨nodes[1]'(by have := hCV.size_ge_two; omega),
      Array.getElem?_eq_getElem (by have := hCV.size_ge_two; omega)⟩
  have hθ1 : (1 : Row) < stored emits[k + 1].row := by
    have := stored_strictMono (lt_of_le_of_lt (Row.zero_le _) hθpos)
    rwa [stored_zero] at this
  have hidx : 1 ≤ ref'.index :=
    Expansion.below_max_index hnodes hbelow hb1 (by rw [hCV.bottom_row b1 hb1]; exact hθ1)
  have hpc1 : (1 : Row) ≤ pc.row :=
    row_one_le_of_ne_zero (ne_of_gt (hCV.rows_strict 0 ref'.index phantom pc hCV.phantom hpc
      (by omega)))
  -- the highest row below
  have hHB : HighestBelow (rowsOf R (legCol ctx l)) emits[k + 1].row (official pc.row) := by
    refine ⟨?_, ?_, ?_⟩
    · refine List.mem_map.mpr ⟨(⟨legCol ctx l, ref'.index⟩, pc), ?_, rfl⟩
      refine mem_realNodes_iff.mpr ⟨nodes, ref'.index - 1, hnodesR, ?_, ?_⟩
      · rw [show ref'.index - 1 + 1 = ref'.index by omega]; exact hpc
      · simp only [Ref.mk.injEq, true_and]; omega
    · have := official_strictMono hpc1 hpcrow
      rwa [official_stored] at this
    · intro r hr hrθ
      obtain ⟨q, hqm, rfl⟩ := List.mem_map.mp hr
      obtain ⟨col', j, hcol', hcellj, hq1⟩ := mem_realNodes_iff.mp hqm
      rw [hnodesR] at hcol'
      obtain rfl := Option.some.inj hcol'
      have hq1r : (1 : Row) ≤ q.2.row := realNodes_row_one_le hV hqm
      have hlt : q.2.row < stored emits[k + 1].row := by
        have := stored_strictMono hrθ
        rwa [Classification.stored_official hq1r] at this
      have hj := Expansion.below_max_index hnodes hbelow hcellj hlt
      apply official_mono hq1r
      rcases Nat.eq_or_lt_of_le hj with he | hlt'
      · rw [he] at hcellj
        rw [Option.some.inj (hcellj.symm.trans hpc)]
      · exact (hCV.rows_strict _ _ _ _ hcellj hpc hlt').le
  have hj := hCJ k hk1 l e (official pc.row) hlsome hθ hHB
  rw [hclrow, ← Classification.stored_official hpc1, jump_stored]
  exact hj

end OmegaY.Official.Recon.JumpLaw

#print axioms OmegaY.Official.Recon.JumpLaw.jumpLawHolds_of_col
