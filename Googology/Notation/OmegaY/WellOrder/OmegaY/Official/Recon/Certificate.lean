/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/Certificate.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Reconstruction
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Dimension
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.ReconstructionCertificate
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.FinishPreservation
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.Selection
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.Reconstruction
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.Normal

set_option backward.do.legacy false

/-!
# Reconstruction from column certificates

`Canonical.build_reconstruct_of_valuesOf` (Phyrion) rebuilds any mountain `R` from
its bottom values when `R` is valid, numerically normal and has the exact bottom
legs. Numerical normality follows from the value sums, the value-1 tops and the
*parent geometry* of every column (`Expansion.normal_of_sums_geometry`). This file
packs these facts into one predicate `Certified` on a mountain, shows that it gives
the reconstruction (`reconstruct_of_certified`), that a canonical mountain is
certified (`certified_of_build`), and that certificates extend column by column
(`Certified.push`).

The rows of a new column of the official expansion are stored rows (`stored`); the
last section proves that `stored` is strictly monotone and never `0`.
-/

namespace OmegaY.Official.Recon

open Canonical Expansion

/-! ## Certified mountains -/

/-- The five local facts that make a mountain the canonical mountain of its bottom
values. -/
structure Certified (R : Mountain) : Prop where
  valid : MountainValid R
  sums : MountainSums R
  tops : MountainTops R
  legs : BottomLegs R
  geometry : MountainParentGeometry R

/-- **Reconstruction from a certificate.** -/
theorem reconstruct_of_certified {R : Mountain} (h : Certified R) {out : List Nat}
    (hv : Expansion.valuesOf R = .ok out) : Canonical.build out = .ok R :=
  build_reconstruct_of_valuesOf h.valid
    (normal_of_sums_geometry h.valid h.sums h.tops h.geometry) h.legs hv

/-- The parent geometry of a column from its canonical steps. -/
theorem columnParentGeometry_of_steps {M : Mountain} {c : Nat} {col : Column}
    (h : ColumnSteps M c col) : ColumnParentGeometry M c col := by
  intro i lower upper hl hu hi
  obtain ⟨_, ref, parent, _, hfind, hcell, hrow, _, hleft⟩ := h i lower upper hl hu hi
  exact ⟨ref, parent, hleft, hcell, hfind, hrow⟩

/-- A canonical mountain is certified. -/
theorem certified_of_build {s : List Nat} {M : Mountain} (h : Canonical.build s = .ok M) :
    Certified M := by
  obtain ⟨M', hM', _, hT⟩ := build_total (build_success_legal h)
  have he : M' = M := Except.ok.inj (hM'.symm.trans h)
  subst he
  exact ⟨build_valid_of_success h, build_mountain_sums h, hT, build_bottom_legs h,
    fun c hc => columnParentGeometry_of_steps (build_steps h c hc)⟩

/-! ## Pushing a column -/

theorem cellAt_push_left' {m : Mountain} {col : Column} {ref : Ref} (hc : ref.column < m.size) :
    cellAt (m.push col) ref = cellAt m ref := cellAt_push_left hc

theorem lookup_push_left {m : Mountain} {col : Column} {ref : Ref} (hc : ref.column < m.size) :
    Expansion.lookup (m.push col) ref = Expansion.lookup m ref := by
  unfold Expansion.lookup
  rw [cellAt_push_left hc]

theorem getElem_push_left {m : Mountain} {col : Column} {c : Nat} (hc : c < m.size) :
    (m.push col)[c]? = m[c]? := by
  rw [Array.getElem?_push, if_neg (by omega)]

/-- The parent geometry of an old column survives appending a column. -/
theorem ColumnParentGeometry.push {m : Mountain} {col : Column} {c : Nat} {column : Column}
    (hV : ColumnValid m c column) (hc : c < m.size) (h : ColumnParentGeometry m c column) :
    ColumnParentGeometry (m.push col) c column := by
  intro i lower upper hl hu hi
  obtain ⟨ref, parent, hleft, hcell, hfind, hrow⟩ := h i lower upper hl hu hi
  have href : ref.column < c := (hV.stored_valid _ _ _ hu hleft).1
  refine ⟨ref, parent, hleft, ?_, ?_, hrow⟩
  · rw [cellAt_push_left (by omega)]
    exact hcell
  · rw [findParent_push (by simpa using hc)]
    exact hfind

/-- Bottom legs of a pushed column. -/
theorem BottomLegs.push' {m : Mountain} (h : BottomLegs m) {col : Column} {b : Cell}
    (hb : col[1]? = some b) (hleft : b.left = if m.size = 0 then none else some ⟨m.size - 1, 0⟩) :
    BottomLegs (m.push col) := by
  intro c hc
  by_cases he : c = m.size
  · subst he
    exact ⟨b, by simpa using hb, hleft⟩
  · have hOld : c < m.size := by simp only [Array.size_push] at hc; omega
    simpa only [Array.getElem_push_lt hOld] using h c hOld

/-- **Extending a certificate by one column.** The new column must be valid over the
old mountain, finished (values from the top), have the exact bottom leg, and have
parent geometry in the extended mountain. -/
theorem Certified.push {m : Mountain} (h : Certified m) {col : Column}
    (hV : ColumnValid m m.size col) (hF : FinishedColumn m col) {b : Cell}
    (hb : col[1]? = some b) (hleft : b.left = if m.size = 0 then none else some ⟨m.size - 1, 0⟩)
    (hG : ColumnParentGeometry (m.push col) m.size col) : Certified (m.push col) := by
  refine ⟨h.valid.push hV, h.sums.push hF, h.tops.push hF.topOne, BottomLegs.push' h.legs hb hleft, ?_⟩
  intro c hc
  by_cases he : c = m.size
  · subst he
    simpa only [Array.getElem_push_eq] using hG
  · have hOld : c < m.size := by simp only [Array.size_push] at hc; omega
    simp only [Array.getElem_push_lt hOld]
    exact ColumnParentGeometry.push (h.valid c hOld) hOld (h.geometry c hOld)

/-! ## Certificates without the parent geometry -/

/-- The facts of `Certified` other than the parent geometry. -/
structure Basic (R : Mountain) : Prop where
  valid : MountainValid R
  sums : MountainSums R
  tops : MountainTops R
  legs : BottomLegs R

theorem Basic.push {m : Mountain} (h : Basic m) {col : Column}
    (hV : ColumnValid m m.size col) (hF : FinishedColumn m col) {b : Cell}
    (hb : col[1]? = some b) (hleft : b.left = if m.size = 0 then none else some ⟨m.size - 1, 0⟩) :
    Basic (m.push col) :=
  ⟨h.valid.push hV, h.sums.push hF, h.tops.push hF.topOne, BottomLegs.push' h.legs hb hleft⟩

theorem Certified.toBasic {R : Mountain} (h : Certified R) : Basic R :=
  ⟨h.valid, h.sums, h.tops, h.legs⟩

theorem certified_of_basic {R : Mountain} (h : Basic R) (hG : MountainParentGeometry R) :
    Certified R :=
  ⟨h.valid, h.sums, h.tops, h.legs, hG⟩

/-! ## Stored rows -/

theorem isFinite_iff' (r : Row) : isFinite r = true ↔ ∀ i, 1 ≤ i → r.coeff i = 0 := by
  simp only [isFinite, decide_eq_true_eq]
  exact Dimension.len_le_iff

theorem finite_lt_infinite' {a b : Row} (ha : ∀ i, 1 ≤ i → a.coeff i = 0)
    (hb : ¬ ∀ i, 1 ≤ i → b.coeff i = 0) : a < b := by
  push Not at hb
  obtain ⟨i0, hi0, hne⟩ := hb
  have hmem : i0 ∈ b.coeffs.support := Finsupp.mem_support_iff.mpr hne
  have hne' : b.coeffs.support.Nonempty := ⟨i0, hmem⟩
  set i := b.coeffs.support.max' hne' with hi
  have hi0le : i0 ≤ i := Finset.le_max' _ _ hmem
  have himem : i ∈ b.coeffs.support := Finset.max'_mem _ _
  refine Row.lt_iff.mpr ⟨i, ?_, ?_⟩
  · intro j hj
    rw [ha j (by omega)]
    by_contra hbj
    have hjmem : j ∈ b.coeffs.support := Finsupp.mem_support_iff.mpr (Ne.symm hbj)
    have := Finset.le_max' _ _ hjmem
    omega
  · rw [ha i (by omega)]
    exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp himem)

theorem nat_lt_nat {m n : Nat} (h : m < n) : (m : Row) < (n : Row) :=
  Row.lt_iff.mpr ⟨0, fun j hj => by simp [Row.coeff_nat, Nat.ne_of_gt hj], by simpa using h⟩

theorem coeff0_lt_of_finite {a b : Row} (ha : ∀ i, 1 ≤ i → a.coeff i = 0)
    (hb : ∀ i, 1 ≤ i → b.coeff i = 0) (h : a < b) : a.coeff 0 < b.coeff 0 := by
  obtain ⟨i, hi, hlt⟩ := Row.lt_iff.mp h
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · exact hlt
  · rw [ha i hpos, hb i hpos] at hlt
    omega

/-- `stored` is strictly monotone. -/
theorem stored_strictMono {a b : Row} (h : a < b) : stored a < stored b := by
  unfold stored
  by_cases ha : isFinite a = true
  · by_cases hb : isFinite b = true
    · rw [if_pos ha, if_pos hb]
      exact nat_lt_nat (by
        have := coeff0_lt_of_finite ((isFinite_iff' a).mp ha) ((isFinite_iff' b).mp hb) h
        omega)
    · rw [if_pos ha, if_neg hb]
      apply finite_lt_infinite' _ (fun h' => hb ((isFinite_iff' b).mpr h'))
      intro i hi
      simp only [Row.coeff_nat]
      split <;> omega
  · by_cases hb : isFinite b = true
    · exfalso
      have hba := finite_lt_infinite' ((isFinite_iff' b).mp hb)
        (fun h' => ha ((isFinite_iff' a).mpr h'))
      exact absurd (lt_trans h hba) (lt_irrefl _)
    · rw [if_neg ha, if_neg hb]
      exact h

/-- A stored row is never the phantom row `0`. -/
theorem stored_ne_zero (a : Row) : stored a ≠ 0 := by
  unfold stored
  split
  · intro h
    have := congrArg (fun r : Row => r.coeff 0) h
    simp [Row.coeff_nat] at this
  · rename_i ha
    intro h
    apply ha
    rw [isFinite_iff', h]
    intro i _
    exact Row.coeff_zero i

/-- The stored row of the official row `0` is `1`. -/
theorem stored_zero : stored 0 = 1 := by decide

theorem stored_eq_one {a : Row} (h : stored a = 1) : a = 0 := by
  by_contra hne
  have hpos : (0 : Row) < a := lt_of_le_of_ne (Row.zero_le a) (Ne.symm hne)
  have := stored_strictMono hpos
  rw [stored_zero, h] at this
  exact lt_irrefl _ this

end OmegaY.Official.Recon
