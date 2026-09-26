/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/LegRowMatchInnerMap.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CopyShapeMaps

set_option backward.do.legacy false

/-!
# The row map of a copied column that knows where the column ascends

`Φ` (`CopyShapeMaps.lean`) is the row map of a block under the hypothesis (MA): it lifts a row
`r` in every region `S` whose root top `ρ` is below `r`. (MA) is false
(`CopyShapeMAFalse.lean`): a column that does not ascend in `S` can have nodes above `ρ`, and it
copies them without a lift.

`Ψ E top` is `Φ E` with the root top of a region read from a function `top` instead of
`topIn E.M E.cr`. For a copied column `ctx`, `topA ctx` is the root top of the region when the
column ascends there and `none` otherwise (`topA`). Then a region where the column does not
ascend is handled like a region without root top: the rows keep their slots.

* `Ψ_congr`: two functions `top₁`, `top₂` that are each either `none` or the root top, and that
  agree on every region `S ∋ r` whose root top is below `r`, give the same image of `r`.
-/

namespace OmegaY.Official.Classification.Proofs.CopyShape.InnerRow

open Canonical Reserve Official Descent Classification Proofs

/-! ## The map -/

/-- `Φ` with the root top of a region read from `top`. -/
def Ψ (E : Env) (top : Nat → Row → Option (Ref × Cell)) : Bool → Nat → Row → Row → Row → Row
  | _, 0, _, T, _ => T
  | _, 1, _, T, _ => T
  | false, d + 2, S, T, r =>
      match top (d + 2) S with
      | none => Ψ E top false (d + 1) (slot (d + 2) S (r.coeff d)) (slot (d + 2) T (r.coeff d)) r
      | some (_, ρc) =>
          if r ≤ official ρc.row then
            Ψ E top false (d + 1) (slot (d + 2) S (r.coeff d)) (slot (d + 2) T (r.coeff d)) r
          else if r.coeff d = (official ρc.row).coeff d then
            Ψ E top true (d + 1) (slot (d + 2) S (r.coeff d))
              (slot (d + 2) T ((official ρc.row).coeff d + E.lift (d + 2) S)) r
          else
            Ψ E top false (d + 1) (slot (d + 2) S (r.coeff d))
              (slot (d + 2) T (r.coeff d + E.lift (d + 2) S)) r
  | true, d + 2, S, T, r =>
      match top (d + 2) S with
      | none => T
      | some (_, ρc) =>
          if r.coeff d = (official ρc.row).coeff d then
            Ψ E top true (d + 1) (slot (d + 2) S (r.coeff d)) (slot (d + 2) T (E.hB (d + 2) T)) r
          else
            Ψ E top false (d + 1) (slot (d + 2) S (r.coeff d))
              (slot (d + 2) T (r.coeff d + E.hB (d + 2) T - (official ρc.row).coeff d)) r

/-- Whether the column of `ctx` ascends in the region with root top `ρ` (errors count as no). -/
def ascB (ctx : Context) (ρ : Ref × Cell) : Bool :=
  match ascends ctx (some ρ) with
  | .ok b => b
  | .error _ => false

/-- The root top of a region, if the column of `ctx` ascends there. -/
def topA (ctx : Context) (d : Nat) (S : Row) : Option (Ref × Cell) :=
  match topIn ctx.source ctx.rootColumn d S with
  | none => none
  | some ρ => if ascB ctx ρ then some ρ else none

theorem ascB_iff {ctx : Context} {ρ : Ref × Cell} :
    ascB ctx ρ = true ↔ ascends ctx (some ρ) = .ok true := by
  unfold ascB
  cases h : ascends ctx (some ρ) with
  | error e => simp
  | ok b => cases b <;> simp

theorem topA_of_asc {ctx : Context} {d : Nat} {S : Row} {ρ : Ref × Cell}
    (h : topIn ctx.source ctx.rootColumn d S = some ρ) (ha : ascends ctx (some ρ) = .ok true) :
    topA ctx d S = some ρ := by
  unfold topA
  rw [h]
  simp [ascB_iff.mpr ha]

theorem topA_of_not_asc {ctx : Context} {d : Nat} {S : Row}
    (h : ∀ ρ, topIn ctx.source ctx.rootColumn d S = some ρ → ascends ctx (some ρ) = .ok false) :
    topA ctx d S = none := by
  unfold topA
  cases ht : topIn ctx.source ctx.rootColumn d S with
  | none => rfl
  | some ρ =>
      have hf := h ρ ht
      have : ascB ctx ρ = false := by unfold ascB; rw [hf]
      simp [this]

theorem topA_cases (ctx : Context) (d : Nat) (S : Row) :
    topA ctx d S = none ∨ topA ctx d S = topIn ctx.source ctx.rootColumn d S := by
  unfold topA
  cases topIn ctx.source ctx.rootColumn d S with
  | none => left; rfl
  | some ρ =>
      by_cases h : ascB ctx ρ = true
      · right; simp [h]
      · left; simp [h]

/-! ## Unfolding -/

theorem Ψ_one (E : Env) (top : Nat → Row → Option (Ref × Cell)) (m : Bool) (S T r : Row) :
    Ψ E top m 1 S T r = T := by
  cases m <;> rfl

theorem ΨF_none {E : Env} {top : Nat → Row → Option (Ref × Cell)} {d : Nat} {S T r : Row}
    (h : top (d + 2) S = none) :
    Ψ E top false (d + 2) S T r =
      Ψ E top false (d + 1) (slot (d + 2) S (r.coeff d)) (slot (d + 2) T (r.coeff d)) r := by
  simp only [Ψ, h]

theorem ΨF_low {E : Env} {top : Nat → Row → Option (Ref × Cell)} {d : Nat} {S T r : Row}
    {ρr : Ref} {ρc : Cell} (h : top (d + 2) S = some (ρr, ρc)) (hr : r ≤ official ρc.row) :
    Ψ E top false (d + 2) S T r =
      Ψ E top false (d + 1) (slot (d + 2) S (r.coeff d)) (slot (d + 2) T (r.coeff d)) r := by
  simp only [Ψ, h, if_pos hr]

theorem ΨF_mid {E : Env} {top : Nat → Row → Option (Ref × Cell)} {d : Nat} {S T r : Row}
    {ρr : Ref} {ρc : Cell} (h : top (d + 2) S = some (ρr, ρc)) (hr : official ρc.row < r)
    (hσ : r.coeff d = (official ρc.row).coeff d) :
    Ψ E top false (d + 2) S T r =
      Ψ E top true (d + 1) (slot (d + 2) S (r.coeff d))
        (slot (d + 2) T ((official ρc.row).coeff d + E.lift (d + 2) S)) r := by
  simp only [Ψ, h, if_neg (not_le.mpr hr), if_pos hσ]

theorem ΨF_high {E : Env} {top : Nat → Row → Option (Ref × Cell)} {d : Nat} {S T r : Row}
    {ρr : Ref} {ρc : Cell} (h : top (d + 2) S = some (ρr, ρc)) (hr : official ρc.row < r)
    (hσ : r.coeff d ≠ (official ρc.row).coeff d) :
    Ψ E top false (d + 2) S T r =
      Ψ E top false (d + 1) (slot (d + 2) S (r.coeff d))
        (slot (d + 2) T (r.coeff d + E.lift (d + 2) S)) r := by
  simp only [Ψ, h, if_neg (not_le.mpr hr), if_neg hσ]

theorem ΨG_none {E : Env} {top : Nat → Row → Option (Ref × Cell)} {d : Nat} {S T r : Row}
    (h : top (d + 2) S = none) : Ψ E top true (d + 2) S T r = T := by
  simp only [Ψ, h]

theorem ΨG_mid {E : Env} {top : Nat → Row → Option (Ref × Cell)} {d : Nat} {S T r : Row}
    {ρr : Ref} {ρc : Cell} (h : top (d + 2) S = some (ρr, ρc))
    (hσ : r.coeff d = (official ρc.row).coeff d) :
    Ψ E top true (d + 2) S T r =
      Ψ E top true (d + 1) (slot (d + 2) S (r.coeff d)) (slot (d + 2) T (E.hB (d + 2) T)) r := by
  simp only [Ψ, h, if_pos hσ]

theorem ΨG_high {E : Env} {top : Nat → Row → Option (Ref × Cell)} {d : Nat} {S T r : Row}
    {ρr : Ref} {ρc : Cell} (h : top (d + 2) S = some (ρr, ρc))
    (hσ : r.coeff d ≠ (official ρc.row).coeff d) :
    Ψ E top true (d + 2) S T r =
      Ψ E top false (d + 1) (slot (d + 2) S (r.coeff d))
        (slot (d + 2) T (r.coeff d + E.hB (d + 2) T - (official ρc.row).coeff d)) r := by
  simp only [Ψ, h, if_neg hσ]

/-- In the mode `false`, a region without root top and a region whose root top is at or above
`r` give the same step. -/
theorem ΨF_keep {E : Env} {top : Nat → Row → Option (Ref × Cell)} {d : Nat} {S T r : Row}
    (h : top (d + 2) S = none ∨ ∃ ρr ρc, top (d + 2) S = some (ρr, ρc) ∧ r ≤ official ρc.row) :
    Ψ E top false (d + 2) S T r =
      Ψ E top false (d + 1) (slot (d + 2) S (r.coeff d)) (slot (d + 2) T (r.coeff d)) r := by
  rcases h with h | ⟨ρr, ρc, h, hr⟩
  · exact ΨF_none h
  · exact ΨF_low h hr

/-! ## Two root-top functions that agree where it matters -/

/-- **The image of `r` depends only on the root tops below `r`.** -/
theorem Ψ_congr (E : Env) (top₁ top₂ : Nat → Row → Option (Ref × Cell)) (r : Row)
    (h₁ : ∀ d S, top₁ d S = none ∨ top₁ d S = topIn E.M E.cr d S)
    (h₂ : ∀ d S, top₂ d S = none ∨ top₂ d S = topIn E.M E.cr d S)
    (hag : ∀ d S ρ, inRegion (d + 2) S r = true → topIn E.M E.cr (d + 2) S = some ρ →
      official ρ.2.row < r → top₁ (d + 2) S = top₂ (d + 2) S) :
    ∀ (d : Nat) (m : Bool) (S T : Row), inRegion (d + 1) S r = true →
      (m = true → ∀ ρ, topIn E.M E.cr (d + 1) S = some ρ → official ρ.2.row < r) →
      Ψ E top₁ m (d + 1) S T r = Ψ E top₂ m (d + 1) S T r
  | 0, m, S, T, _, _ => by rw [Ψ_one, Ψ_one]
  | d + 1, m, S, T, hS, hm => by
      have hsl : inRegion (d + 1) (slot (d + 2) S (r.coeff d)) r = true := slot_mem hS
      -- the root top of `S`
      cases ht : topIn E.M E.cr (d + 2) S with
      | none =>
          have e₁ : top₁ (d + 2) S = none := by
            rcases h₁ (d + 2) S with h | h
            · exact h
            · rw [h, ht]
          have e₂ : top₂ (d + 2) S = none := by
            rcases h₂ (d + 2) S with h | h
            · exact h
            · rw [h, ht]
          cases m with
          | true => rw [ΨG_none e₁, ΨG_none e₂]
          | false =>
              rw [ΨF_none e₁, ΨF_none e₂]
              exact Ψ_congr E top₁ top₂ r h₁ h₂ hag d false _ _ hsl (fun h => by cases h)
      | some ρ =>
          obtain ⟨ρr, ρc⟩ := ρ
          have hρsub : topIn E.M E.cr (d + 1) (slot (d + 2) S ((official ρc.row).coeff d)) =
              some (ρr, ρc) := ChainCorr.Inner.topIn_slot ht
          by_cases hlt : official ρc.row < r
          · have he := hag d S (ρr, ρc) hS ht hlt
            -- both functions give the same value here
            have hmid : ∀ m', r.coeff d = (official ρc.row).coeff d →
                (m' = true → ∀ ρ', topIn E.M E.cr (d + 1) (slot (d + 2) S (r.coeff d)) = some ρ' →
                  official ρ'.2.row < r) := by
              intro m' hσ _ ρ' hρ'
              rw [hσ, hρsub] at hρ'
              cases hρ'
              exact hlt
            cases m with
            | false =>
                rcases h₁ (d + 2) S with e₁ | e₁
                · have e₂ : top₂ (d + 2) S = none := by rw [← he]; exact e₁
                  rw [ΨF_none e₁, ΨF_none e₂]
                  exact Ψ_congr E top₁ top₂ r h₁ h₂ hag d false _ _ hsl (fun h => by cases h)
                · rw [ht] at e₁
                  have e₂ : top₂ (d + 2) S = some (ρr, ρc) := by rw [← he]; exact e₁
                  by_cases hσ : r.coeff d = (official ρc.row).coeff d
                  · rw [ΨF_mid e₁ hlt hσ, ΨF_mid e₂ hlt hσ]
                    exact Ψ_congr E top₁ top₂ r h₁ h₂ hag d true _ _ hsl (hmid true hσ)
                  · rw [ΨF_high e₁ hlt hσ, ΨF_high e₂ hlt hσ]
                    exact Ψ_congr E top₁ top₂ r h₁ h₂ hag d false _ _ hsl (fun h => by cases h)
            | true =>
                rcases h₁ (d + 2) S with e₁ | e₁
                · have e₂ : top₂ (d + 2) S = none := by rw [← he]; exact e₁
                  rw [ΨG_none e₁, ΨG_none e₂]
                · rw [ht] at e₁
                  have e₂ : top₂ (d + 2) S = some (ρr, ρc) := by rw [← he]; exact e₁
                  by_cases hσ : r.coeff d = (official ρc.row).coeff d
                  · rw [ΨG_mid e₁ hσ, ΨG_mid e₂ hσ]
                    exact Ψ_congr E top₁ top₂ r h₁ h₂ hag d true _ _ hsl (hmid true hσ)
                  · rw [ΨG_high e₁ hσ, ΨG_high e₂ hσ]
                    exact Ψ_congr E top₁ top₂ r h₁ h₂ hag d false _ _ hsl (fun h => by cases h)
          · have hle : r ≤ official ρc.row := le_of_not_gt hlt
            cases m with
            | true => exact absurd (hm rfl (ρr, ρc) ht) hlt
            | false =>
                have k₁ : top₁ (d + 2) S = none ∨
                    ∃ a b, top₁ (d + 2) S = some (a, b) ∧ r ≤ official b.row := by
                  rcases h₁ (d + 2) S with e | e
                  · exact Or.inl e
                  · exact Or.inr ⟨ρr, ρc, by rw [e, ht], hle⟩
                have k₂ : top₂ (d + 2) S = none ∨
                    ∃ a b, top₂ (d + 2) S = some (a, b) ∧ r ≤ official b.row := by
                  rcases h₂ (d + 2) S with e | e
                  · exact Or.inl e
                  · exact Or.inr ⟨ρr, ρc, by rw [e, ht], hle⟩
                rw [ΨF_keep k₁, ΨF_keep k₂]
                exact Ψ_congr E top₁ top₂ r h₁ h₂ hag d false _ _ hsl (fun h => by cases h)

end OmegaY.Official.Classification.Proofs.CopyShape.InnerRow

#print axioms OmegaY.Official.Classification.Proofs.CopyShape.InnerRow.Ψ_congr
