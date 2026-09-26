/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/ReserveShape.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Reserve
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.Domain

set_option backward.do.legacy false

/-!
# The shape of the leg atoms

Every leg atom of a valid mountain is well formed (`Reserve.wellFormed`): its parent
column is left of its child column, its child is a column of the mountain, its key
has `D + 1` entries, and every column entry of the key is at most the parent.
Canonical mountains are valid (`Canonical.build_valid_of_success`), so this holds
for the mountain of every legal sequence.
-/

namespace OmegaY.Official.Reserve

open Canonical

theorem scaleRoot_column_le (M : Mountain) (k : Nat) :
    ∀ (fuel : Nat) (r : Ref), (scaleRoot M k fuel r).column ≤ r.column := by
  intro fuel
  induction fuel with
  | zero => intro r; simp [scaleRoot]
  | succ fuel ih =>
      intro r
      simp only [scaleRoot]
      split
      · rename_i p c _ _
        split
        · rename_i cp _
          split
          · rename_i h
            exact le_trans (ih p) (le_of_lt h.2)
          · exact le_refl _
        · exact le_refl _
      · exact le_refl _

theorem keyAt_length {M : Mountain} {D : Nat} {row : Row} {p : Ref} {cp : Cell}
    (h : cell? M p = some cp) : (keyAt M D row p).length = D + 1 := by
  simp [keyAt, h]

theorem keyAt_entry {M : Mountain} {D : Nat} {row : Row} {p : Ref} {v : Nat}
    (h : some v ∈ keyAt M D row p) : v ≤ p.column := by
  unfold keyAt at h
  split at h
  · simp at h
  · simp only [List.mem_map, List.mem_reverse, List.mem_range] at h
    obtain ⟨k, _, hk⟩ := h
    split at hk
    · simp only [Option.some.injEq] at hk
      rw [← hk]
      exact scaleRoot_column_le M k _ p
    · simp at hk

theorem highestAtMost_cell {M : Mountain} {l : Nat} {row : Row} {p : Ref}
    (h : highestAtMost M l row = some p) : p.column = l ∧ ∃ cp, cell? M p = some cp := by
  simp only [highestAtMost, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨col, hcol, j, hj, hp⟩ := h
  subst hp
  refine ⟨rfl, ?_⟩
  have hmem := List.mem_of_getLast? hj
  rw [List.mem_filter, List.mem_range] at hmem
  obtain ⟨hjs, _⟩ := hmem
  exact ⟨col[j], by simp [cell?, hcol, hjs]⟩

/-- Every leg atom of a valid mountain is well formed. -/
theorem atoms_wellFormed {M : Mountain} (hV : MountainValid M) (D : Nat) :
    ∀ a ∈ atoms M D, wellFormed D M.size a = true := by
  intro a ha
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
          have hcolEq : M[c] = col := by
            have := hcol; rw [Array.getElem?_eq_getElem hc] at this; exact Option.some.inj this
          have hCV := hV c hc
          rw [hcolEq] at hCV
          unfold legAtom? at hsome
          simp only [Option.bind_eq_bind] at hsome
          cases hcu : cell? M ⟨c, i⟩ with
          | none => simp [hcu] at hsome
          | some cu =>
              simp only [hcu, Option.bind_some] at hsome
              have hcu' : col[i]? = some cu := by simpa [cell?, hcol] using hcu
              cases hl : cu.left with
              | none => simp [hl] at hsome
              | some l =>
                  simp only [hl, Option.bind_some] at hsome
                  cases hp : highestAtMost M l.column cu.row with
                  | none => simp [hp] at hsome
                  | some p =>
                      simp only [hp, Option.bind_some, Option.pure_def, Option.some.injEq] at hsome
                      subst hsome
                      obtain ⟨hlc, _⟩ := hCV.stored_valid i cu l hcu' hl
                      obtain ⟨hpl, cp, hcp⟩ := highestAtMost_cell hp
                      simp only [wellFormed, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
                      refine ⟨⟨⟨hlc, hc⟩, keyAt_length hcp⟩, ?_⟩
                      intro e he
                      cases e with
                      | none => rfl
                      | some v =>
                          have := keyAt_entry he
                          simp only [decide_eq_true_eq]
                          omega

theorem legAtom?_spec {M : Mountain} {D : Nat} {u : Ref} {a : RawAtom}
    (h : legAtom? M D u = some a) : a.child = u.column ∧ ∃ cu l, cell? M u = some cu ∧
      cu.left = some l ∧ a.parent = l.column := by
  unfold legAtom? at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨cu, hcu, l, hl, p, _, rfl⟩ := h
  exact ⟨rfl, cu, l, hcu, hl, rfl⟩

theorem mem_atoms {M : Mountain} {D c i : Nat} {col : Column} {a : RawAtom}
    (hc : c < M.size) (hc0 : c ≠ 0) (hcol : M[c]? = some col) (hi : i < col.size) (hi0 : i ≠ 0)
    (h : legAtom? M D ⟨c, i⟩ = some a) : a ∈ atoms M D := by
  simp only [atoms, List.mem_flatMap, List.mem_range]
  refine ⟨c, hc, ?_⟩
  simp only [hc0, if_false, hcol, List.mem_filterMap, List.mem_range]
  exact ⟨i, hi, by simp [hi0, h]⟩

/-- The root data of a valid mountain: the last column is `size - 1`, the root column
is left of it, and the control is the key of a leg atom from the root column into the
last column. -/
theorem root?_spec {M : Mountain} (hV : MountainValid M) {D : Nat} {ρ : Root}
    (h : root? M D = some ρ) :
    ρ.x0 + 1 = M.size ∧ ρ.cr < ρ.x0 ∧
      ∃ a ∈ atoms M D, a.parent = ρ.cr ∧ a.child = ρ.x0 ∧ a.key = ρ.control := by
  unfold root? at h
  split at h
  · exact absurd h (by simp)
  · rename_i col hcol
    split at h
    · exact absurd h (by simp)
    · rename_i hi
      split at h
      · exact absurd h (by simp)
      · rename_i t ht
        split at h
        · exact absurd h (by simp)
        · rename_i r hr
          split at h
          · exact absurd h (by simp)
          · rename_i a ha
            split at h
            · rename_i hra
              simp only [Option.some.injEq] at h
              subst h
              have hsz : M.size - 1 < M.size := by
                have := Array.size_pos_of_mem (Array.mem_of_getElem? hcol) -- nonempty
                omega
              have hcolEq : M[M.size - 1] = col := by
                have := hcol; rw [Array.getElem?_eq_getElem hsz] at this; exact Option.some.inj this
              have hCV := hV (M.size - 1) hsz
              rw [hcolEq] at hCV
              obtain ⟨hrx, _⟩ := hCV.stored_valid (col.size - 1) t r ht hr
              have hi' : col.size - 1 < col.size := by omega
              refine ⟨show M.size - 1 + 1 = M.size by omega, hrx, a,
                mem_atoms hsz (by omega) hcol hi' (by omega) ha, hra.symm,
                (legAtom?_spec ha).1, rfl⟩
            · exact absurd h (by simp)

end OmegaY.Official.Reserve
