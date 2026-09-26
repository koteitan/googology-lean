/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Locality.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.ReserveShape

set_option backward.do.legacy false

/-!
# Locality of the leg atoms

The leg atom of a node of column `c` (`Reserve.legAtom?`) only reads the columns
`≤ c` of the mountain: the node itself, the highest node of its leg column (which is
left of `c` in a valid mountain), and the scale roots of that node (which only move
left). So two mountains that agree on the columns below `k` have the same leg atoms
with child below `k`.

This is used for the base part of the classification (`notes/04-official-design.md`
§1.2, item (base)): the columns `< x₀` of the output mountain are the columns `< x₀`
of the input mountain.
-/

namespace OmegaY.Official.Classification

open Canonical Reserve

/-- Two mountains agree on every column below `k`. -/
def AgreeBelow (M M' : Mountain) (k : Nat) : Prop := ∀ c, c < k → M[c]? = M'[c]?

theorem AgreeBelow.symm {M M' : Mountain} {k : Nat} (h : AgreeBelow M M' k) :
    AgreeBelow M' M k := fun c hc => (h c hc).symm

theorem AgreeBelow.mono {M M' : Mountain} {k k' : Nat} (h : AgreeBelow M M' k)
    (hk : k' ≤ k) : AgreeBelow M M' k' := fun c hc => h c (by omega)

theorem cell?_congr {M M' : Mountain} {k : Nat} (h : AgreeBelow M M' k) {r : Ref}
    (hr : r.column < k) : cell? M r = cell? M' r := by
  simp only [cell?, h r.column hr]

theorem rawParent_congr {M M' : Mountain} {k : Nat} (h : AgreeBelow M M' k) {r : Ref}
    (hr : r.column < k) : rawParent M r = rawParent M' r := by
  simp only [rawParent, h r.column hr]

theorem scaleRoot_congr {M M' : Mountain} {k : Nat} (h : AgreeBelow M M' k) (s : Nat) :
    ∀ (fuel : Nat) (r : Ref), r.column < k → scaleRoot M s fuel r = scaleRoot M' s fuel r := by
  intro fuel
  induction fuel with
  | zero => intro r _; rfl
  | succ fuel ih =>
      intro r hr
      simp only [scaleRoot]
      rw [rawParent_congr h hr, cell?_congr h hr]
      cases rawParent M' r with
      | none => rfl
      | some p =>
          cases cell? M' r with
          | none => rfl
          | some c =>
              simp only
              by_cases hp : p.column < r.column
              · rw [cell?_congr h (by omega), ih p (by omega)]
              · cases cell? M p <;> cases cell? M' p <;> simp [hp]

theorem highestAtMost_congr {M M' : Mountain} {k : Nat} (h : AgreeBelow M M' k) {l : Nat}
    (hl : l < k) (row : Row) : highestAtMost M l row = highestAtMost M' l row := by
  simp only [highestAtMost, h l hl]

theorem keyAt_congr {M M' : Mountain} {k : Nat} (h : AgreeBelow M M' k) (D : Nat) (row : Row)
    {p : Ref} (hp : p.column < k) : keyAt M D row p = keyAt M' D row p := by
  unfold keyAt
  rw [cell?_congr h hp]
  cases cell? M' p with
  | none => rfl
  | some cp =>
      simp only
      congr 1
      funext s
      rw [scaleRoot_congr h s (p.column + 1) p hp]

/-- The left leg of a real node of a valid mountain lies left of the node. -/
theorem left_lt_of_valid {M : Mountain} (hV : MountainValid M) {u : Ref} {cu : Cell} {l : Ref}
    (hu : cell? M u = some cu) (hl : cu.left = some l) : l.column < u.column := by
  unfold cell? at hu
  cases hcol : M[u.column]? with
  | none => simp [hcol] at hu
  | some col =>
      simp only [hcol, Option.bind_eq_bind, Option.bind_some] at hu
      have hc : u.column < M.size := by
        rcases Nat.lt_or_ge u.column M.size with h' | h'
        · exact h'
        · simp [Array.getElem?_eq_none h'] at hcol
      have hcolEq : M[u.column] = col := by
        have := hcol; rw [Array.getElem?_eq_getElem hc] at this; exact Option.some.inj this
      have hCV := hV u.column hc
      rw [hcolEq] at hCV
      exact (hCV.stored_valid u.index cu l hu hl).1

/-- The leg atom of a node below column `k` depends only on the columns below `k`. -/
theorem legAtom?_congr {M M' : Mountain} {k : Nat} (h : AgreeBelow M M' k)
    (hV : MountainValid M) (D : Nat) {u : Ref} (hu : u.column < k) :
    legAtom? M D u = legAtom? M' D u := by
  unfold legAtom?
  rw [← cell?_congr h hu]
  cases hcu : cell? M u with
  | none => rfl
  | some cu =>
      simp only [Option.bind_eq_bind, Option.bind_some]
      cases hl : cu.left with
      | none => rfl
      | some l =>
          have hlu := left_lt_of_valid hV hcu hl
          simp only [Option.bind_some]
          rw [highestAtMost_congr h (show l.column < k by omega) cu.row]
          cases hp : highestAtMost M' l.column cu.row with
          | none => rfl
          | some p =>
              have hpc := (highestAtMost_cell hp).1
              simp only [Option.bind_some]
              rw [keyAt_congr h D cu.row (show p.column < k by omega)]

/-- Membership in `atoms`, unfolded. -/
theorem mem_atoms_iff {M : Mountain} {D : Nat} {a : RawAtom} :
    a ∈ atoms M D ↔ ∃ c i col, c < M.size ∧ c ≠ 0 ∧ M[c]? = some col ∧ i < col.size ∧
      i ≠ 0 ∧ legAtom? M D ⟨c, i⟩ = some a := by
  constructor
  · intro ha
    simp only [atoms, List.mem_flatMap, List.mem_range] at ha
    obtain ⟨c, hc, ha⟩ := ha
    split at ha
    · simp at ha
    · rename_i hc0
      cases hcol : M[c]? with
      | none => simp [hcol] at ha
      | some col =>
          simp only [hcol, List.mem_filterMap, List.mem_range] at ha
          obtain ⟨i, hi, hsome⟩ := ha
          split at hsome
          · simp at hsome
          · rename_i hi0
            exact ⟨c, i, col, hc, hc0, hcol, hi, hi0, hsome⟩
  · rintro ⟨c, i, col, hc, hc0, hcol, hi, hi0, ha⟩
    exact mem_atoms hc hc0 hcol hi hi0 ha

/-- Leg atoms with child below `k` are shared by mountains that agree below `k`. -/
theorem atoms_sub_of_agree {M M' : Mountain} {k : Nat} (h : AgreeBelow M M' k)
    (hV' : MountainValid M') (D : Nat) {a : RawAtom} (ha : a ∈ atoms M' D)
    (hk : a.child < k) : a ∈ atoms M D := by
  obtain ⟨c, i, col, hc, hc0, hcol, hi, hi0, hleg⟩ := mem_atoms_iff.mp ha
  have hac : a.child = c := (legAtom?_spec hleg).1
  have hck : c < k := by omega
  have hcolM : M[c]? = some col := (h c hck).trans hcol
  have hcM : c < M.size := by
    rcases Nat.lt_or_ge c M.size with h' | h'
    · exact h'
    · simp [Array.getElem?_eq_none h'] at hcolM
  refine mem_atoms_iff.mpr ⟨c, i, col, hcM, hc0, hcolM, hi, hi0, ?_⟩
  rw [legAtom?_congr h.symm hV' D (u := ⟨c, i⟩) hck] at hleg
  exact hleg

theorem keyEq_refl (m : Nat) (K : RawKey) : keyEq m K K = true := by
  simp [keyEq]

theorem keyLe_refl (m : Nat) (K : RawKey) : keyLe m K K = true := by
  simp [keyLe, keyEq_refl]

/-- An atom of the input system is classified as (base) by itself. -/
theorem baseOK_of_mem {D : Nat} {Es : List RawAtom} {e : RawAtom} (he : e ∈ Es) :
    baseOK D Es e = true := by
  simp only [baseOK, List.any_eq_true, Bool.and_eq_true, beq_iff_eq]
  exact ⟨e, he, ⟨⟨rfl, rfl⟩, keyLe_refl _ _⟩⟩

/-- **Base part.** If the output mountain agrees with the input mountain below `k`,
every output leg atom with child below `k` is a (base) atom. -/
theorem baseOK_of_agree {M MO : Mountain} {k : Nat} (h : AgreeBelow M MO k)
    (hVO : MountainValid MO) (D : Nat) {e : RawAtom} (he : e ∈ atoms MO D)
    (hk : e.child < k) : baseOK D (atoms M D) e = true :=
  baseOK_of_mem (atoms_sub_of_agree h hVO D he hk)

end OmegaY.Official.Classification
