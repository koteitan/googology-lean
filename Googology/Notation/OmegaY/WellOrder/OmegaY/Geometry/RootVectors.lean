/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Geometry/RootVectors.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Geometry/RootVectors.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Geometry.CanonicalRootKeys
import Googology.Notation.OmegaY.WellOrder.OmegaY.Rows.Truncate

set_option backward.do.legacy false

/-!
# Finite high-to-low vectors of actual scale roots

The coefficient at scale `k` is the actual scale root's column. Reading
the Cantor order therefore reads the root columns from high scale to low
scale. A cut retains the complete high prefix, not merely one coordinate.
-/

namespace OmegaY.Geometry.Frame

universe u

def rootVector {F : Frame} (hF : F.Ordered) (D : Nat) (u : F.Node) : Row :=
  Row.ofList ((List.range (D + 1)).map fun k => (scaleRoot hF k u).1.val)

theorem coeff_rootVector {F : Frame} (hF : F.Ordered) (D : Nat) (u : F.Node)
    (k : Nat) : Row.coeff (rootVector hF D u) k =
      if k ≤ D then (scaleRoot hF k u).1.val else 0 := by
  by_cases hk : k ≤ D
  · unfold rootVector
    rw [Row.coeff_ofList_at _ k (by simp; omega)]
    simp [hk]
  · unfold rootVector
    rw [Row.coeff_ofList_above _ k (by simp; omega)]
    simp [hk]

def rootPrefix {F : Frame} (hF : F.Ordered) (D k : Nat) (u : F.Node) : Row :=
  Row.cut (rootVector hF D u) k

theorem coeff_rootPrefix {F : Frame} (hF : F.Ordered) (D k : Nat) (u : F.Node)
    (i : Nat) : Row.coeff (rootPrefix hF D k u) i =
      if k ≤ i ∧ i ≤ D then (scaleRoot hF i u).1.val else 0 := by
  unfold rootPrefix
  rw [Row.coeff_cut, coeff_rootVector]
  split_ifs <;> simp_all

theorem rootPrefix_eq_of_raw {F : Frame} (hF : F.Ordered) {u p : F.Node}
    (hRaw : F.rawParent u = some p) {D k : Nat}
    (hScale : Row.jump (F.height u) (F.height p) ≤ k) :
    rootPrefix hF D k u = rootPrefix hF D k p := by
  ext i
  simp only [coeff_rootPrefix]
  split_ifs with hi
  · rw [scaleRoot_eq_of_raw hF hRaw (hScale.trans hi.1)]
  · rfl

theorem Normal.rootPrefix_candidate_le {F : Frame} (hF : F.Normal)
    {u q : F.Node} (hReal : Real u) (hQ : F.Q u = some q) (D k : Nat) :
    rootPrefix hF.toOrdered D k q ≤ rootPrefix hF.toOrdered D k u := by
  apply Row.le_of_coeff_le
  intro i
  simp only [coeff_rootPrefix]
  split_ifs
  · exact hF.scaleRoot_candidate_column_le hReal hQ i
  · exact le_rfl

theorem rootPrefix_strict_finer {F : Frame} (hF : F.Ordered) {D fine coarse : Nat}
    {u v : F.Node} (hScale : fine ≤ coarse)
    (h : rootPrefix hF D coarse u < rootPrefix hF D coarse v) :
    rootPrefix hF D fine u < rootPrefix hF D fine v :=
  Row.cut_strict_finer hScale h

theorem rootPrefix_le_coarser {F : Frame} (hF : F.Ordered) {D fine coarse : Nat}
    {u v : F.Node} (hScale : fine ≤ coarse)
    (h : rootPrefix hF D fine u ≤ rootPrefix hF D fine v) :
    rootPrefix hF D coarse u ≤ rootPrefix hF D coarse v :=
  Row.cut_le_of_cut_le hScale h

/-- A strict Cantor-prefix comparison has a genuine named-root witness
inside the retained finite coordinates. -/
theorem rootPrefix_lt_witness {F : Frame} (hF : F.Ordered) {D k : Nat}
    {u v : F.Node} (h : rootPrefix hF D k u < rootPrefix hF D k v) :
    ∃ i, k ≤ i ∧ i ≤ D ∧
      (∀ j, i < j → j ≤ D → (scaleRoot hF j u).1 = (scaleRoot hF j v).1) ∧
      (scaleRoot hF i u).1 < (scaleRoot hF i v).1 := by
  obtain ⟨i, hHigher, hAt⟩ := Row.lt_iff.mp h
  have hi : k ≤ i ∧ i ≤ D := by
    by_contra hn
    simp only [coeff_rootPrefix, if_neg hn] at hAt
    exact (Nat.lt_irrefl _ hAt)
  refine ⟨i, hi.1, hi.2, ?_, ?_⟩
  · intro j hij hjD
    apply Fin.ext
    have hj := hHigher j hij
    have hji : k ≤ j ∧ j ≤ D := ⟨hi.1.trans hij.le, hjD⟩
    simpa only [coeff_rootPrefix, if_pos hji] using hj
  · change (scaleRoot hF i u).1.val < (scaleRoot hF i v).1.val
    simpa only [coeff_rootPrefix, if_pos hi] using hAt

/-- The row encoding is sound for the literal finite/infinity truncated
key, with arbitrary strictly increasing labels in any universe. -/
theorem rootPrefix_lt_truncate {F : Frame} (hF : F.Ordered) {D k : Nat}
    {u v : F.Node} {Label : Type u} [LinearOrder Label]
    (f : Fin F.width → Label) (hf : StrictMono f)
    (h : rootPrefix hF D k u < rootPrefix hF D k v) :
    Keys.truncate (fun i : Fin (D + 1) => f (scaleRoot hF (D - i.val) u).1)
        (D + 1 - k) <
      Keys.truncate (fun i : Fin (D + 1) => f (scaleRoot hF (D - i.val) v).1)
        (D + 1 - k) := by
  obtain ⟨i, hki, hiD, hHigher, hAt⟩ := rootPrefix_lt_witness hF h
  let index : Fin (D + 1) := ⟨D - i, by omega⟩
  have hIndex : index.val < D + 1 - k := by dsimp only [index]; omega
  apply Keys.truncate_lt_at index hIndex hIndex
  · intro j hj
    apply congrArg f
    apply hHigher (D - j.val)
    · have hj' : j.val < D - i := hj
      omega
    · omega
  · have he : D - index.val = i := by dsimp only [index]; omega
    simpa only [he] using hf hAt

end OmegaY.Geometry.Frame

#print axioms OmegaY.Geometry.Frame.Normal.rootPrefix_candidate_le
