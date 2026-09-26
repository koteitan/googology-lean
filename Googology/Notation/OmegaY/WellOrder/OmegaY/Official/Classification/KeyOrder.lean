/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/KeyOrder.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.KeyUpper

set_option backward.do.legacy false

/-!
# Order facts for raw keys, and the split of the seam condition

`keyLt` is transitive with `keyLe` on its left (`keyLt_of_keyLe_of_keyLt`), and the
column map `mapKey` preserves `keyLt` (`keyLt_mapKey`). Hence the seam condition
`key(e) < μ_b(Kc)` follows from `key(e) ≤ μ_b(key(a))` and `key(a) < Kc`
(`keyOK_of_keyOK2`): the reflection condition becomes a statement about the input
mountain only (the witness `a` is a leg atom of column `x₀` below the top node).
-/

set_option linter.unnecessarySeqFocus false

namespace OmegaY.Official.Classification

open Canonical Reserve Official Descent

theorem keyLt_spec {m : Nat} {a b : RawKey} :
    keyLt m a b = true ↔ ∃ i, i < m ∧ (∀ j, j < i → a[j]? = b[j]?) ∧
      entryLt (a[i]?.getD none) (b[i]?.getD none) = true := by
  simp only [keyLt, List.any_eq_true, List.mem_range, Bool.and_eq_true, List.all_eq_true,
    beq_iff_eq]

theorem keyEq_spec {m : Nat} {a b : RawKey} :
    keyEq m a b = true ↔ ∀ j, j < m → a[j]? = b[j]? := by
  simp only [keyEq, List.all_eq_true, List.mem_range, beq_iff_eq]

theorem entryLt_trans {x y z : Option Nat} (h1 : entryLt x y = true) (h2 : entryLt y z = true) :
    entryLt x z = true := by
  cases x <;> cases y <;> cases z <;> simp_all [entryLt] <;> omega

theorem entryLt_irrefl (x : Option Nat) : entryLt x x = false := by
  cases x <;> simp [entryLt]

theorem keyLt_trans {m : Nat} {a b c : RawKey} (h1 : keyLt m a b = true)
    (h2 : keyLt m b c = true) : keyLt m a c = true := by
  obtain ⟨i, hi, hbi, hli⟩ := keyLt_spec.mp h1
  obtain ⟨k, hk, hbk, hlk⟩ := keyLt_spec.mp h2
  apply keyLt_spec.mpr
  rcases Nat.lt_trichotomy i k with hik | rfl | hki
  · refine ⟨i, hi, fun j hj => (hbi j hj).trans (hbk j (by omega)), ?_⟩
    rw [← hbk i hik]
    exact hli
  · exact ⟨i, hi, fun j hj => (hbi j hj).trans (hbk j hj), entryLt_trans hli hlk⟩
  · refine ⟨k, hk, fun j hj => (hbi j (by omega)).trans (hbk j hj), ?_⟩
    rw [hbi k hki]
    exact hlk

theorem keyLt_of_keyLe_of_keyLt {m : Nat} {a b c : RawKey} (h1 : keyLe m a b = true)
    (h2 : keyLt m b c = true) : keyLt m a c = true := by
  simp only [keyLe, Bool.or_eq_true] at h1
  rcases h1 with h1 | h1
  · have heq := keyEq_spec.mp h1
    obtain ⟨k, hk, hbk, hlk⟩ := keyLt_spec.mp h2
    exact keyLt_spec.mpr ⟨k, hk, fun j hj => (heq j (by omega)).trans (hbk j hj),
      by rw [heq k hk]; exact hlk⟩
  · exact keyLt_trans h1 h2

theorem getElem?_mapKey (cr sh : Nat) (K : RawKey) (j : Nat) :
    (mapKey cr sh K)[j]? = K[j]?.map (Option.map (mapColumn cr sh)) := by
  simp only [mapKey, List.getElem?_map]
  rfl

theorem entryLt_map {cr sh : Nat} {x y : Option Nat} (h : entryLt x y = true) :
    entryLt (x.map (mapColumn cr sh)) (y.map (mapColumn cr sh)) = true := by
  cases x <;> cases y <;> simp_all [entryLt, mapColumn] <;> split <;> split <;> omega

theorem keyLt_mapKey {m cr sh : Nat} {a b : RawKey} (h : keyLt m a b = true) :
    keyLt m (mapKey cr sh a) (mapKey cr sh b) = true := by
  obtain ⟨i, hi, hb, hl⟩ := keyLt_spec.mp h
  refine keyLt_spec.mpr ⟨i, hi, fun j hj => by rw [getElem?_mapKey, getElem?_mapKey, hb j hj], ?_⟩
  rw [getElem?_mapKey, getElem?_mapKey]
  have := entryLt_map (cr := cr) (sh := sh) hl
  cases ha : a[i]? <;> cases hb' : b[i]? <;> simp_all

/-- `KeyOK` with the seam control condition moved to the input side: the witness `a`
is below the control. -/
def KeyOK2 (D cr w x0 : Nat) (Kc : RawKey) (X : Nat) (o : Origin) (e a : RawAtom) : Prop :=
  if X = x0 + blockOf x0 w X * w ∧ o.isUpper = false then
    keyLe (D + 1) e.key (mapKey cr (blockOf x0 w X * w) a.key) = true ∧
      keyLt (D + 1) a.key Kc = true
  else
    keyLe (D + 1) e.key (mapKey cr ((blockOf x0 w X + 1) * w) a.key) = true

theorem keyOK_of_keyOK2 {D cr w x0 : Nat} {Kc : RawKey} {X : Nat} {o : Origin} {e a : RawAtom}
    (h : KeyOK2 D cr w x0 Kc X o e a) : KeyOK D cr w x0 Kc X o e a := by
  unfold KeyOK2 at h
  unfold KeyOK
  split at h
  · rw [if_pos (by assumption)]
    exact ⟨h.1, keyLt_of_keyLe_of_keyLt h.1 (keyLt_mapKey h.2)⟩
  · rw [if_neg (by assumption)]
    exact h

/-- **The remaining statement**, with the proved case (upper part, leg left of the root
column) removed and the seam control condition moved to the witness. -/
def KeyWitnessRest : Prop :=
  ∀ s n D M out ρ R (col : Column) (t : Cell), SpliceCase s n D M out ρ → DegreeOK s D →
    Official.expandDiagram s n = .ok R → Canonical.build out = .ok R →
    M[M.size - 1]? = some col → col.back? = some t →
    ∀ X x i (_ : ρ.x0 ≤ X) (hXR : X < R.size), X = x + (ρ.x0 - ρ.cr) * i → i < n + 1 →
      x ∈ blockColumns ρ.cr ρ.x0 n i →
      copyColumn (ctxAt M R x i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 X) (official t.row) = .ok R[X] →
      ∀ es, emitsT (ctxAt M R x i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 X) (official t.row) = .ok es →
      ∀ k (hk : k < es.length) e a, legAtom? R D ⟨X, k + 1⟩ = some e →
        legAtom? M D es[k].2.src = some a →
        ¬ (es[k].2.isUpper = true ∧ a.parent < ρ.cr) →
        KeyOK2 D ρ.cr (ρ.x0 - ρ.cr) ρ.x0 ρ.control X es[k].2 e a

theorem keyWitnessHolds_of_rest (h : KeyWitnessRest) : KeyWitnessHolds := by
  intro s n D M out ρ R col t hc hdeg hR hRb hcol ht X x i hX0 hXR hXeq hi hx hcopy es hes k hk
    e a he ha
  by_cases hlow : es[k].2.isUpper = true ∧ a.parent < ρ.cr
  · exact keyOK_upper_low hc hR hXR hcopy hes hk he ha hlow.1 hlow.2
  · exact keyOK_of_keyOK2 (h s n D M out ρ R col t hc hdeg hR hRb hcol ht X x i hX0 hXR hXeq hi
      hx hcopy es hes k hk e a he ha hlow)

/-- **Well-foundedness of the official expansion from the open statements.** -/
theorem wellFounded_of_rest (h1 : Reconstructs) (h2 : DegreePreserved) (h3 : LengthOK)
    (h4 : KeyWitnessRest) : WellFounded Step :=
  wellFounded_of_keys h1 h2 h3 (keyWitnessHolds_of_rest h4)

end OmegaY.Official.Classification

#print axioms OmegaY.Official.Classification.wellFounded_of_rest
