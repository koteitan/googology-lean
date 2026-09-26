/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/ParentBelowLowerCols.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.ParentBelowLowerCore
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.JumpLawBlock0

set_option backward.do.legacy false

/-!
# `LowerParentBelowHolds`: the columns of a run

Tools that read the columns of the output `R` of a splice run through the traced copies:

* `colData`: a new column `X = x + w·i` with its traced lower and upper copies, and the row
  and leg of each of its real nodes;
* `origCell`: a column left of `x₀` is a column of `M(s)`;
* `legRows`: for `c_r ≤ ℓ < x₀` and `i ≥ 1`, a row below `τ` of the column `ℓ + w·i` is the row
  of a lower copy made by the copy of `ℓ` in block `i` (for `ℓ = c_r`, the hypothetical copy
  of `c_r`, by `Boundary`);
* `legUpper`: for the same columns, a row at or above `τ` is the row of a node of `ℓ`.
-/

namespace OmegaY.Official.Recon.LowerPB

open Canonical Expansion Geometry Frame Classification Reserve

/-! ## Small facts -/

theorem left_lt {M : Mountain} (hV : MountainValid M) {c k : Nat} {co : Cell} {r : Ref}
    (h : cell? M ⟨c, k⟩ = some co) (hl : co.left = some r) : r.column < c := by
  obtain ⟨colv, hcolv, hcv⟩ := cell?_spec h
  simp only at hcolv hcv
  obtain ⟨hc, hce⟩ := Array.getElem?_eq_some_iff.mp hcolv
  subst hce
  exact ((hV c hc).stored_valid k co r hcv hl).1

theorem cell_row_one_le {M : Mountain} (hV : MountainValid M) {c k : Nat} {co : Cell}
    (h : cell? M ⟨c, k⟩ = some co) (hk : 1 ≤ k) : (1 : Row) ≤ co.row := by
  obtain ⟨colv, hcolv, hcv⟩ := cell?_spec h
  simp only at hcolv hcv
  obtain ⟨hc, hce⟩ := Array.getElem?_eq_some_iff.mp hcolv
  subst hce
  have hCV := hV c hc
  exact row_one_le_of_ne_zero (ne_of_gt (hCV.rows_strict 0 k phantom co hCV.phantom hcv
    (by omega)))

theorem mem_realNodes_of_cell {M : Mountain} {c k : Nat} {co : Cell}
    (h : cell? M ⟨c, k⟩ = some co) (hk : 1 ≤ k) : ((⟨c, k⟩ : Ref), co) ∈ realNodes M c := by
  obtain ⟨colv, hcolv, hcv⟩ := cell?_spec h
  simp only at hcolv hcv
  refine mem_realNodes_iff.mpr ⟨colv, k - 1, hcolv, ?_, ?_⟩
  · rw [show k - 1 + 1 = k by omega]; exact hcv
  · simp only [Ref.mk.injEq, true_and]; omega

theorem origCell {M R : Mountain} (hI : Inv M (M.size - 1) R) {q kz : Nat}
    (hq : q < M.size - 1) (hqR : q < R.size) (hkz : kz < R[q].size) :
    cell? M ⟨q, kz⟩ = some R[q][kz] := by
  have h := hI.2.1 q hq
  unfold cell?
  simp only
  rw [← h, Array.getElem?_eq_getElem hqR]
  simp [Array.getElem?_eq_getElem hkz]

theorem official_lt_of_stored_lt {a b : Row} (h : stored a < b) (hb : (1 : Row) ≤ b) :
    a < official b := by
  have h' : stored a < stored (official b) := by rw [stored_official hb]; exact h
  exact lt_of_stored_lt h'

theorem lt_official_of_lt_stored {a b : Row} (h : a < stored b) (ha : (1 : Row) ≤ a) :
    official a < b := by
  have h' : stored (official a) < stored b := by rw [stored_official ha]; exact h
  exact lt_of_stored_lt h'

/-! ## The data of one new column -/

/-- The data of a new column `X = x + w·i` of a splice run. -/
structure ColData (s : List Nat) (n : Nat) (R M : Mountain) (t : Cell) (root : Ref)
    (X i x : Nat) (lo us : List (Emit × Origin)) : Prop where
  run : Official.expandDiagram s n = .ok R
  top : Top s M t root
  ci : ColumnsInv M n root.column (M.size - 1 - root.column) (M.size - 1) (official t.row) R
  inv : Inv M (M.size - 1) R
  XR : X < R.size
  xb : x ∈ blockColumns root.column (M.size - 1) n i
  iln : i ≤ n
  Xeq : X = x + (M.size - 1 - root.column) * i
  hlo : lowerT (ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1) X)
    (official t.row) = .ok lo
  hus : upperT (ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1) X)
    (official t.row) = .ok us
  asm : assemble (ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1) X)
    ((lo ++ us).map Prod.fst) = .ok (R[X]'XR)

theorem colData {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}
    (hrun : Official.expandDiagram s n = .ok R) (hTop : Top s M t root)
    (hCI : ColumnsInv M n root.column (M.size - 1 - root.column) (M.size - 1)
      (official t.row) R)
    (hI : Inv M (M.size - 1) R) {X : Nat} (hX : X < R.size) (hx : M.size - 1 ≤ X) :
    ∃ i x lo us, ColData s n R M t root X i x lo us := by
  obtain ⟨i, x, lo, us, hi, hxb, hXeq, hlo, hus, hasm⟩ := colView hCI hX hx
  exact ⟨i, x, lo, us, ⟨hrun, hTop, hCI, hI, hX, hxb, by omega, hXeq, hlo, hus, hasm⟩⟩

namespace ColData

variable {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}
  {X i x : Nat} {lo us : List (Emit × Origin)}

theorem xgt (h : ColData s n R M t root X i x lo us) : root.column < x :=
  (mem_blockColumns h.top.lt h.xb).1

theorem xle (h : ColData s n R M t root X i x lo us) : x ≤ M.size - 1 :=
  (mem_blockColumns h.top.lt h.xb).2

theorem bctx (h : ColData s n R M t root X i x lo us) :
    BCtx M R root.column (M.size - 1) i
      (ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1) X) :=
  bctx_ctxAt (le_of_lt h.xgt) h.xle (by rw [h.Xeq]; have := h.xgt; omega)

theorem size (h : ColData s n R M t root X i x lo us) :
    (R[X]'h.XR).size = (lo ++ us).length + 1 := by
  have := (assemble_spec h.asm).1
  simpa using this

/-- The row and leg of a real node of `X`. -/
theorem node (h : ColData s n R M t root X i x lo us) {k : Nat} (hk : k < (R[X]'h.XR).size)
    (hk1 : 1 ≤ k) :
    ∃ hk' : k - 1 < (lo ++ us).length, (R[X]'h.XR)[k].row = stored (lo ++ us)[k - 1].1.row ∧
      ∃ ref : Ref, (R[X]'h.XR)[k].left = some ref ∧
        ref.column = legColumn (ctxAt M R x i root.column (M.size - 1 - root.column)
          (M.size - 1) X) (lo ++ us)[k - 1].1 := by
  have hk' : k - 1 < (lo ++ us).length := by have := h.size; omega
  refine ⟨hk', ?_⟩
  obtain ⟨cell, hcell, hrow, ref, hl, hrc⟩ := (assemble_spec h.asm).2 (k - 1) (by simpa using hk')
  rw [show k - 1 + 1 = k by omega, Array.getElem?_eq_getElem hk] at hcell
  have he : (R[X]'h.XR)[k] = cell := Option.some.inj hcell
  rw [he]
  simp only [List.getElem_map] at hrow hrc
  exact ⟨hrow, ref, hl, hrc⟩

theorem sorted (h : ColData s n R M t root X i x lo us) :
    (((lo ++ us).map Prod.fst).map Emit.row).Pairwise (· < ·) :=
  JumpLaw.assemble_sorted h.asm

theorem lo_lt (h : ColData s n R M t root X i x lo us) : ∀ e ∈ lo, e.1.row < official t.row :=
  lowerT_rows_lt (runCtx_ctxAt h.top h.xb h.Xeq (le_of_lt h.XR)) h.hlo

theorem us_ge (h : ColData s n R M t root X i x lo us) : ∀ e ∈ us, official t.row ≤ e.1.row := by
  intro e he
  obtain ⟨k, c, _, _, _, hrow, hτ, _⟩ := (upperT_spec h.hus).1 e he
  rw [hrow]
  exact hτ

theorem emitsT (h : ColData s n R M t root X i x lo us) :
    emitsT (ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1) X)
      (official t.row) = .ok (lo ++ us) := by
  unfold Classification.emitsT
  rw [h.hlo, h.hus]
  rfl

/-- In block `0`, a lower copy sits at the row of its origin. -/
theorem block0_row (h : ColData s n R M t root X i x lo us) (hi : i = 0) {e : Emit × Origin}
    (he : e ∈ lo) {c : Cell} (hc : cell? M e.2.src = some c) : official c.row = e.1.row := by
  have hup := ((lowerT_good h.hlo) e he).2
  obtain ⟨cv, hcv, hrow⟩ := Proofs.emitsT_block0 (ctx := ctxAt M R x i root.column
    (M.size - 1 - root.column) (M.size - 1) X) hi h.emitsT e (List.mem_append_left _ he) hup
  have hcc : cv = c := Option.some.inj (hcv.symm.trans hc)
  subst hcc
  exact hrow

/-- A non-cut copy is not below its origin (block `0`: the same row; block `i ≥ 1`: `Lift`). -/
theorem lift (hP : Profile) (h : ColData s n R M t root X i x lo us) {e : Emit × Origin}
    (he : e ∈ lo) (hcut : cutO e.2 = false) {c : Cell} (hc : cell? M e.2.src = some c) :
    official c.row ≤ e.1.row := by
  rcases Nat.eq_zero_or_pos i with hi | hi
  · exact le_of_eq (h.block0_row hi he hc)
  · exact hP.lift s n R h.run M t root h.top i hi h.iln _ h.bctx lo h.hlo e he hcut c hc

end ColData

/-! ## Block `0`: every node of `x₀` below `τ` is copied -/

/-- The traced lower part gives the untraced one. -/
theorem lowerRun_of_lowerT {ctx : Context} {τ : Row} {lo : List (Emit × Origin)}
    (h : lowerT ctx τ = .ok lo) :
    ∃ vs, JumpLaw.LowerRun ctx τ vs ∧ vs.flatten = lo.map Prod.fst := by
  unfold lowerT at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i outs houts
    cases h
    have hm := mapM_map_fst (fun p : Nat × Item => runItem ctx p.1 p.2)
      (fun p : Nat × Item => runItemT ctx p.1 p.2) (List.map Prod.fst)
      (fun p => runItemT_fst ctx p.1 p.2) (lowerItems τ)
    rw [houts] at hm
    refine ⟨outs.map (List.map Prod.fst), hm.symm, ?_⟩
    rw [List.map_flatten]

theorem index_eq_of_row {M : Mountain} (hV : MountainValid M) {c k k' : Nat} {a b : Cell}
    (ha : cell? M ⟨c, k⟩ = some a) (hb : cell? M ⟨c, k'⟩ = some b) (h : a.row = b.row) :
    k = k' := by
  obtain ⟨colv, hcolv, hav⟩ := cell?_spec ha
  obtain ⟨colv', hcolv', hbv⟩ := cell?_spec hb
  simp only at hcolv hav hcolv' hbv
  have hcc : colv' = colv := Option.some.inj (hcolv'.symm.trans hcolv)
  subst hcc
  obtain ⟨hcs, hce⟩ := Array.getElem?_eq_some_iff.mp hcolv
  subst hce
  have hCV := hV c hcs
  rcases Nat.lt_trichotomy k k' with hl | he | hl
  · exact absurd h (ne_of_lt (hCV.rows_strict k k' a b hav hbv hl))
  · exact he
  · exact absurd h.symm (ne_of_lt (hCV.rows_strict k' k b a hbv hav hl))

namespace ColData

variable {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}
  {X i x : Nat} {lo us : List (Emit × Origin)}

/-- **Block `0`: `Emitted`.** Every node of `x` below `τ` is the origin of a lower copy. -/
theorem emitted0 (h : ColData s n R M t root X i x lo us) (hi : i = 0) {k : Nat} {c : Cell}
    (hk : 1 ≤ k) (hc : cell? M ⟨x, k⟩ = some c) (hτ : official c.row < official t.row) :
    ∃ f ∈ lo, f.2.src = ⟨x, k⟩ := by
  have hVM := build_valid_of_success h.top.build
  obtain ⟨vs, hvs, hflat⟩ := lowerRun_of_lowerT h.hlo
  obtain ⟨em, hem, hrow⟩ := (JumpLaw.lower_id (runCtx_ctxAt h.top h.xb h.Xeq (le_of_lt h.XR))
    hi hvs).2 _ (mem_realNodes_of_cell hc hk) hτ
  rw [hflat] at hem
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hem
  obtain ⟨k', cv, hsrc, hk', hcv, _⟩ := lowerT_src h.hlo hf
  change cell? M ⟨x, k'⟩ = some cv at hcv
  have hfc : cell? M f.2.src = some cv := by rw [hsrc]; exact hcv
  have hr := h.block0_row hi hf hfc
  have hrr : cv.row = c.row := by
    have e1 := stored_official (cell_row_one_le hVM hcv hk')
    have e2 := stored_official (cell_row_one_le hVM hc hk)
    rw [← e1, ← e2, hr]
    exact congrArg stored hrow
  have hkk := index_eq_of_row hVM hcv hc hrr
  subst hkk
  exact ⟨f, hf, hsrc⟩

/-- A node of `x` below `τ` has a lower copy at or above its row (block `0`: `emitted0`; block
`i ≥ 1`: `Emitted` and `Lift`). -/
theorem emittedLift (hP : Profile) (h : ColData s n R M t root X i x lo us) {k : Nat} {c : Cell}
    (hk : 1 ≤ k) (hc : cell? M ⟨x, k⟩ = some c) (hτ : official c.row < official t.row) :
    ∃ f ∈ lo, f.2.src = ⟨x, k⟩ ∧ official c.row ≤ f.1.row := by
  have hfc : ∀ f : Emit × Origin, f.2.src = ⟨x, k⟩ → cell? M f.2.src = some c := by
    intro f hf; rw [hf]; exact hc
  rcases Nat.eq_zero_or_pos i with hi | hi
  · obtain ⟨f, hf, hsrc⟩ := h.emitted0 hi hk hc hτ
    exact ⟨f, hf, hsrc, le_of_eq (h.block0_row hi hf (hfc f hsrc))⟩
  · obtain ⟨f, hf, hcut, hsrc⟩ := hP.emitted s n R h.run M t root h.top i hi h.iln _ h.bctx
      h.xgt lo h.hlo k c hk hc hτ
    exact ⟨f, hf, hsrc, h.lift hP hf hcut (hfc f hsrc)⟩

end ColData

/-! ## The columns of the legs -/

theorem mul_ge_self {w i : Nat} (hi : 1 ≤ i) : w ≤ w * i := Nat.le_mul_of_pos_right _ hi

/-- The column `ℓ + w·i` (`c_r ≤ ℓ < x₀`, `i ≥ 1`) is a new column read from `ℓ` above `τ`, and
for `ℓ > c_r` it is the copy of `ℓ` in block `i`. -/
theorem legView {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}
    (hrun : Official.expandDiagram s n = .ok R) (hTop : Top s M t root)
    (hCI : ColumnsInv M n root.column (M.size - 1 - root.column) (M.size - 1)
      (official t.row) R)
    (hI : Inv M (M.size - 1) R) {i ℓ : Nat} (hi1 : 1 ≤ i) (hℓ1 : root.column ≤ ℓ)
    (hℓ2 : ℓ < M.size - 1) (hq : ℓ + (M.size - 1 - root.column) * i < R.size) :
    ∃ i' y lo us, ColData s n R M t root (ℓ + (M.size - 1 - root.column) * i) i' y lo us ∧
      upperColumn (ctxAt M R y i' root.column (M.size - 1 - root.column) (M.size - 1)
        (ℓ + (M.size - 1 - root.column) * i)) = ℓ ∧
      (root.column < ℓ → y = ℓ ∧ i' = i) := by
  have hcr := hTop.lt
  have hwpos : 0 < M.size - 1 - root.column := by omega
  have hwi := mul_ge_self (w := M.size - 1 - root.column) hi1
  obtain ⟨i', y, lo, us, hD⟩ := colData hrun hTop hCI hI hq (by omega)
  have hyg := hD.xgt
  have hyl := hD.xle
  have hqq := hD.Xeq
  refine ⟨i', y, lo, us, hD, ?_, ?_⟩
  · rw [upperColumn_ctxAt]
    by_cases hre : ℓ = root.column
    · have hrep : (M.size - 1 - root.column) + (M.size - 1 - root.column) * (i - 1) =
          (y - root.column) + (M.size - 1 - root.column) * i' := by
        have e1 : (M.size - 1 - root.column) + (M.size - 1 - root.column) * (i - 1) =
            (M.size - 1 - root.column) * i := by
          have hi' : i = (i - 1) + 1 := by omega
          conv_rhs => rw [hi']
          rw [Nat.mul_succ]
          omega
        rw [hre] at hqq
        omega
      have := repr_unique hwpos le_rfl (by omega) (by omega) hrep
      rw [if_pos (show y = M.size - 1 by omega)]
      exact hre.symm
    · have hrep : (ℓ - root.column) + (M.size - 1 - root.column) * i =
          (y - root.column) + (M.size - 1 - root.column) * i' := by omega
      have := repr_unique (by omega) (by omega) (by omega) (by omega) hrep
      rw [if_neg (show ¬ y = M.size - 1 by omega)]
      omega
  · intro hlt
    obtain ⟨h1, h2⟩ := block_unique hlt (by omega) hyg hyl hqq
    exact ⟨h2.symm, h1.symm⟩

/-- **The rows below `τ` of the column of a leg.** -/
theorem legRows (hP : Profile) {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell}
    {root : Ref} (hrun : Official.expandDiagram s n = .ok R) (hTop : Top s M t root)
    (hCI : ColumnsInv M n root.column (M.size - 1 - root.column) (M.size - 1)
      (official t.row) R)
    (hI : Inv M (M.size - 1) R) {i ℓ : Nat} (hi1 : 1 ≤ i) (hin : i ≤ n)
    (hℓ1 : root.column ≤ ℓ) (hℓ2 : ℓ < M.size - 1)
    (hq : ℓ + (M.size - 1 - root.column) * i < R.size) {kz : Nat}
    (hkz : kz < R[ℓ + (M.size - 1 - root.column) * i].size) (hkz1 : 1 ≤ kz)
    (hlt : official R[ℓ + (M.size - 1 - root.column) * i][kz].row < official t.row) :
    ∃ ctx' es' e', BCtx M R root.column (M.size - 1) i ctx' ∧ ctx'.x = ℓ ∧
      lowerT ctx' (official t.row) = .ok es' ∧ e' ∈ es' ∧
      e'.1.row = official R[ℓ + (M.size - 1 - root.column) * i][kz].row := by
  rcases eq_or_lt_of_le hℓ1 with hre | hgt
  · subst hre
    obtain ⟨es, hes, hall⟩ := hP.boundary s n R hrun M t root hTop i hi1 hin
    obtain ⟨e, he, hrow⟩ := hall hq kz hkz hkz1 hlt
    exact ⟨_, es, e, bctx_root M R _ _ i (le_of_lt hTop.lt), rfl, hes, he, hrow⟩
  · obtain ⟨i', y, lo, us, hD, _, hyi⟩ := legView hrun hTop hCI hI hi1 hℓ1 hℓ2 hq
    obtain ⟨hy, hi'⟩ := hyi hgt
    subst hy
    subst hi'
    obtain ⟨hk', hrow, _⟩ := hD.node hkz hkz1
    have hrow' : official R[y + (M.size - 1 - root.column) * i'][kz].row =
        (lo ++ us)[kz - 1].1.row := by
      rw [hrow, official_stored']
    have hlo : kz - 1 < lo.length := by
      by_contra hn
      have hmem : (lo ++ us)[kz - 1] ∈ us := by
        rw [List.getElem_append_right (by omega)]
        exact List.getElem_mem _
      have := hD.us_ge _ hmem
      rw [← hrow'] at this
      exact absurd hlt (not_lt.mpr this)
    refine ⟨_, lo, (lo ++ us)[kz - 1], hD.bctx, rfl, hD.hlo, ?_, hrow'.symm⟩
    rw [List.getElem_append_left hlo]
    exact List.getElem_mem _

/-- **The rows at or above `τ` of the column of a leg** are rows of nodes of `ℓ`. -/
theorem legUpper {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell}
    {root : Ref} (hrun : Official.expandDiagram s n = .ok R) (hTop : Top s M t root)
    (hCI : ColumnsInv M n root.column (M.size - 1 - root.column) (M.size - 1)
      (official t.row) R)
    (hI : Inv M (M.size - 1) R) {i ℓ : Nat} (hi1 : 1 ≤ i)
    (hℓ1 : root.column ≤ ℓ) (hℓ2 : ℓ < M.size - 1)
    (hq : ℓ + (M.size - 1 - root.column) * i < R.size) {kz : Nat}
    (hkz : kz < R[ℓ + (M.size - 1 - root.column) * i].size) (hkz1 : 1 ≤ kz)
    (hge : official t.row ≤ official R[ℓ + (M.size - 1 - root.column) * i][kz].row) :
    ∃ k c, 1 ≤ k ∧ cell? M ⟨ℓ, k⟩ = some c ∧
      official c.row = official R[ℓ + (M.size - 1 - root.column) * i][kz].row := by
  obtain ⟨i', y, lo, us, hD, hup, _⟩ := legView hrun hTop hCI hI hi1 hℓ1 hℓ2 hq
  obtain ⟨hk', hrow, _⟩ := hD.node hkz hkz1
  have hrow' : official R[ℓ + (M.size - 1 - root.column) * i][kz].row =
      (lo ++ us)[kz - 1].1.row := by
    rw [hrow, official_stored']
  have hus : lo.length ≤ kz - 1 := by
    by_contra hn
    have hmem : (lo ++ us)[kz - 1] ∈ lo := by
      rw [List.getElem_append_left (by omega)]
      exact List.getElem_mem _
    have := hD.lo_lt _ hmem
    rw [← hrow'] at this
    exact absurd hge (not_le.mpr this)
  have hmem : (lo ++ us)[kz - 1] ∈ us := by
    rw [List.getElem_append_right (by omega)]
    exact List.getElem_mem _
  obtain ⟨k, c, hk1, hc, _, hr, _, _⟩ := (upperT_spec hD.hus).1 _ hmem
  rw [hup] at hc
  exact ⟨k, c, hk1, hc, by rw [hrow', hr]⟩

end OmegaY.Official.Recon.LowerPB

#print axioms OmegaY.Official.Recon.LowerPB.legRows
#print axioms OmegaY.Official.Recon.LowerPB.legUpper
#print axioms OmegaY.Official.Recon.LowerPB.ColData.emitted0
