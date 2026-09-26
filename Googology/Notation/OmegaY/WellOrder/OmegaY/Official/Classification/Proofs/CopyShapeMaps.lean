/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/CopyShapeMaps.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.ChainCorrStartCopy
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.ChainCorrStepInner

set_option backward.do.legacy false

/-!
# The row map of a block (`CopyShape`)

In a block `i ≥ 1` the rule sends a source row `r` of a region `S` (level `d`) with target
region `T` to a row that does not depend on the copied column. `Φ E false d S T r` is this
row for a plain item (`F` below), `Φ E true d S T r` for an item that skips the bottom of
its region (`G`, rows above the top `ρ` of the root column in `S`).

Write `σ = h_S(r)`, `h_ρ = h_S(row ρ)`, `C = row ρ`, `L = max((h_κ - h_ρ)·i, 1)` and
`h_q` for the height of the top of the boundary column in `T`:

* `F(S, T, r) = F(S[σ], T[σ], r)` if there is no `ρ` or `r ≤ C`;
  `G(S[σ], T[h_ρ + L], r)` if `r > C` and `σ = h_ρ`; `F(S[σ], T[σ + L], r)` otherwise.
* `G(S, T, r) = G(S[σ], T[h_q], r)` if `σ = h_ρ`; `F(S[σ], T[σ + h_q - h_ρ], r)` otherwise.
* At level 1 both are the target row `T`.

This file proves that the maps land in `T` (`Φ_mem`) and are strictly increasing
(`Φ_strictMono`).
-/

namespace OmegaY.Official.Classification.Proofs.CopyShape

open Canonical Reserve Official Descent Classification Proofs

/-- The data of a block that the row map reads. -/
structure Env where
  M : Mountain
  R : Mountain
  cr : Nat
  x0 : Nat
  B : Nat
  i : Nat

/-- The height of the top of the boundary column in a target region. -/
def Env.hB (E : Env) (d : Nat) (T : Row) : Nat := heightOf d (topIn E.R E.B d T)

/-- The lift of a region: `max((h_κ - h_ρ)·i, 1)`. -/
def Env.lift (E : Env) (d : Nat) (S : Row) : Nat :=
  max ((heightOf d (topIn E.M E.x0 d S) - heightOf d (topIn E.M E.cr d S)) * E.i) 1

theorem Env.one_le_lift (E : Env) (d : Nat) (S : Row) : 1 ≤ E.lift d S := le_max_right _ _

/-- The row map of a block: `Φ E false` is `F`, `Φ E true` is `G`. -/
def Φ (E : Env) : Bool → Nat → Row → Row → Row → Row
  | _, 0, _, T, _ => T
  | _, 1, _, T, _ => T
  | false, d + 2, S, T, r =>
      match topIn E.M E.cr (d + 2) S with
      | none => Φ E false (d + 1) (slot (d + 2) S (r.coeff d)) (slot (d + 2) T (r.coeff d)) r
      | some (_, ρc) =>
          if r ≤ official ρc.row then
            Φ E false (d + 1) (slot (d + 2) S (r.coeff d)) (slot (d + 2) T (r.coeff d)) r
          else if r.coeff d = (official ρc.row).coeff d then
            Φ E true (d + 1) (slot (d + 2) S (r.coeff d))
              (slot (d + 2) T ((official ρc.row).coeff d + E.lift (d + 2) S)) r
          else
            Φ E false (d + 1) (slot (d + 2) S (r.coeff d))
              (slot (d + 2) T (r.coeff d + E.lift (d + 2) S)) r
  | true, d + 2, S, T, r =>
      match topIn E.M E.cr (d + 2) S with
      | none => T
      | some (_, ρc) =>
          if r.coeff d = (official ρc.row).coeff d then
            Φ E true (d + 1) (slot (d + 2) S (r.coeff d)) (slot (d + 2) T (E.hB (d + 2) T)) r
          else
            Φ E false (d + 1) (slot (d + 2) S (r.coeff d))
              (slot (d + 2) T (r.coeff d + E.hB (d + 2) T - (official ρc.row).coeff d)) r

/-! ## Unfolding -/

theorem Φ_one (E : Env) (m : Bool) (S T r : Row) : Φ E m 1 S T r = T := by
  cases m <;> rfl

theorem ΦF_none {E : Env} {d : Nat} {S T r : Row} (h : topIn E.M E.cr (d + 2) S = none) :
    Φ E false (d + 2) S T r =
      Φ E false (d + 1) (slot (d + 2) S (r.coeff d)) (slot (d + 2) T (r.coeff d)) r := by
  simp only [Φ, h]

theorem ΦF_low {E : Env} {d : Nat} {S T r : Row} {ρr : Ref} {ρc : Cell}
    (h : topIn E.M E.cr (d + 2) S = some (ρr, ρc)) (hr : r ≤ official ρc.row) :
    Φ E false (d + 2) S T r =
      Φ E false (d + 1) (slot (d + 2) S (r.coeff d)) (slot (d + 2) T (r.coeff d)) r := by
  simp only [Φ, h, if_pos hr]

theorem ΦF_mid {E : Env} {d : Nat} {S T r : Row} {ρr : Ref} {ρc : Cell}
    (h : topIn E.M E.cr (d + 2) S = some (ρr, ρc)) (hr : official ρc.row < r)
    (hσ : r.coeff d = (official ρc.row).coeff d) :
    Φ E false (d + 2) S T r =
      Φ E true (d + 1) (slot (d + 2) S (r.coeff d))
        (slot (d + 2) T ((official ρc.row).coeff d + E.lift (d + 2) S)) r := by
  simp only [Φ, h, if_neg (not_le.mpr hr), if_pos hσ]

theorem ΦF_high {E : Env} {d : Nat} {S T r : Row} {ρr : Ref} {ρc : Cell}
    (h : topIn E.M E.cr (d + 2) S = some (ρr, ρc)) (hr : official ρc.row < r)
    (hσ : r.coeff d ≠ (official ρc.row).coeff d) :
    Φ E false (d + 2) S T r =
      Φ E false (d + 1) (slot (d + 2) S (r.coeff d))
        (slot (d + 2) T (r.coeff d + E.lift (d + 2) S)) r := by
  simp only [Φ, h, if_neg (not_le.mpr hr), if_neg hσ]

theorem ΦG_none {E : Env} {d : Nat} {S T r : Row} (h : topIn E.M E.cr (d + 2) S = none) :
    Φ E true (d + 2) S T r = T := by
  simp only [Φ, h]

theorem ΦG_mid {E : Env} {d : Nat} {S T r : Row} {ρr : Ref} {ρc : Cell}
    (h : topIn E.M E.cr (d + 2) S = some (ρr, ρc)) (hσ : r.coeff d = (official ρc.row).coeff d) :
    Φ E true (d + 2) S T r =
      Φ E true (d + 1) (slot (d + 2) S (r.coeff d)) (slot (d + 2) T (E.hB (d + 2) T)) r := by
  simp only [Φ, h, if_pos hσ]

theorem ΦG_high {E : Env} {d : Nat} {S T r : Row} {ρr : Ref} {ρc : Cell}
    (h : topIn E.M E.cr (d + 2) S = some (ρr, ρc)) (hσ : r.coeff d ≠ (official ρc.row).coeff d) :
    Φ E true (d + 2) S T r =
      Φ E false (d + 1) (slot (d + 2) S (r.coeff d))
        (slot (d + 2) T (r.coeff d + E.hB (d + 2) T - (official ρc.row).coeff d)) r := by
  simp only [Φ, h, if_neg hσ]

/-! ## The image lies in the target region -/

theorem Φ_mem (E : Env) : ∀ (d : Nat) (m : Bool) (S T r : Row),
    inRegion (d + 1) T (Φ E m (d + 1) S T r) = true
  | 0, m, S, T, r => by rw [Φ_one]; exact inRegion_self 1 T
  | d + 1, m, S, T, r => by
      have hsl : ∀ (m' : Bool) (S' : Row) (j : Nat),
          inRegion (d + 2) T (Φ E m' (d + 1) S' (slot (d + 2) T j) r) = true :=
        fun m' S' j => Recon.RowLaw.inRegion_of_slot (Φ_mem E d m' S' _ r)
      cases m with
      | false =>
          cases h : topIn E.M E.cr (d + 2) S with
          | none => rw [ΦF_none h]; exact hsl _ _ _
          | some p =>
              obtain ⟨ρr, ρc⟩ := p
              by_cases hr : r ≤ official ρc.row
              · rw [ΦF_low h hr]; exact hsl _ _ _
              · by_cases hσ : r.coeff d = (official ρc.row).coeff d
                · rw [ΦF_mid h (lt_of_not_ge hr) hσ]; exact hsl _ _ _
                · rw [ΦF_high h (lt_of_not_ge hr) hσ]; exact hsl _ _ _
      | true =>
          cases h : topIn E.M E.cr (d + 2) S with
          | none => rw [ΦG_none h]; exact inRegion_self _ T
          | some p =>
              obtain ⟨ρr, ρc⟩ := p
              by_cases hσ : r.coeff d = (official ρc.row).coeff d
              · rw [ΦG_mid h hσ]; exact hsl _ _ _
              · rw [ΦG_high h hσ]; exact hsl _ _ _

/-! ## Strict monotonicity -/

theorem slot_mem {d : Nat} {S r : Row} (h : inRegion (d + 2) S r = true) :
    inRegion (d + 1) (slot (d + 2) S (r.coeff d)) r = true :=
  Recon.RowLaw.inRegion_slot_iff.mpr ⟨h, rfl⟩

/-- Images in slots with smaller index are smaller. -/
theorem img_lt {E : Env} {d : Nat} {T : Row} {m m' : Bool} {S S' r r' : Row} {j j' : Nat}
    (h : j < j') :
    Φ E m (d + 1) S (slot (d + 2) T j) r < Φ E m' (d + 1) S' (slot (d + 2) T j') r' :=
  ChainCorr.Inner.slot_rows_lt (Φ_mem E d m S _ r) (Φ_mem E d m' S' _ r') h

theorem Φ_strictMono (E : Env) : ∀ (d : Nat) (S T r r' : Row),
    inRegion (d + 1) S r = true → inRegion (d + 1) S r' = true → r < r' →
      Φ E false (d + 1) S T r < Φ E false (d + 1) S T r' ∧
      (∀ ρr ρc, topIn E.M E.cr (d + 1) S = some (ρr, ρc) → official ρc.row < r →
        Φ E true (d + 1) S T r < Φ E true (d + 1) S T r')
  | 0, S, T, r, r', hr, hr', hlt => by
      rw [inRegion_one hr, inRegion_one hr'] at hlt
      exact absurd hlt (lt_irrefl _)
  | d + 1, S, T, r, r', hr, hr', hlt => by
      have hσ : r.coeff d ≤ r'.coeff d := Recon.RowLaw.coeff_le_of_inRegion hr hr' hlt.le
      have hs := slot_mem hr
      have hs' := slot_mem hr'
      -- two rows of the same slot
      have same : r.coeff d = r'.coeff d →
          inRegion (d + 1) (slot (d + 2) S (r.coeff d)) r' = true := by
        intro he; rw [he]; exact hs'
      have IH := fun T' (he : r.coeff d = r'.coeff d) =>
        Φ_strictMono E d (slot (d + 2) S (r.coeff d)) T' r r' hs (same he) hlt
      refine ⟨?_, ?_⟩
      · cases h : topIn E.M E.cr (d + 2) S with
        | none =>
            rw [ΦF_none h, ΦF_none h]
            rcases Nat.lt_or_eq_of_le hσ with hl | he
            · exact img_lt hl
            · have := (IH (slot (d + 2) T (r.coeff d)) he).1
              rw [← he]; exact this
        | some p =>
            obtain ⟨ρr, ρc⟩ := p
            have hρ := topIn_inRegion h
            by_cases hc : r ≤ official ρc.row
            · rw [ΦF_low h hc]
              by_cases hc' : r' ≤ official ρc.row
              · rw [ΦF_low h hc']
                rcases Nat.lt_or_eq_of_le hσ with hl | he
                · exact img_lt hl
                · have := (IH (slot (d + 2) T (r.coeff d)) he).1
                  rw [← he]; exact this
              · have hσρ : r.coeff d ≤ (official ρc.row).coeff d :=
                  Recon.RowLaw.coeff_le_of_inRegion hr hρ hc
                by_cases he : r'.coeff d = (official ρc.row).coeff d
                · rw [ΦF_mid h (lt_of_not_ge hc') he]
                  exact img_lt (by have := E.one_le_lift (d + 2) S; omega)
                · rw [ΦF_high h (lt_of_not_ge hc') he]
                  exact img_lt (by have := E.one_le_lift (d + 2) S; omega)
            · have hc' : ¬ r' ≤ official ρc.row := fun h' => hc (le_trans hlt.le h')
              have hρr : (official ρc.row).coeff d ≤ r.coeff d :=
                Recon.RowLaw.coeff_le_of_inRegion hρ hr (le_of_lt (lt_of_not_ge hc))
              by_cases he : r.coeff d = (official ρc.row).coeff d
              · rw [ΦF_mid h (lt_of_not_ge hc) he]
                by_cases he' : r'.coeff d = (official ρc.row).coeff d
                · rw [ΦF_mid h (lt_of_not_ge hc') he']
                  have hsub : topIn E.M E.cr (d + 1) (slot (d + 2) S (r.coeff d)) = some (ρr, ρc) := by
                    rw [he]; exact ChainCorr.Inner.topIn_slot h
                  have := (IH (slot (d + 2) T ((official ρc.row).coeff d + E.lift (d + 2) S))
                    (he.trans he'.symm)).2 ρr ρc hsub (lt_of_not_ge hc)
                  rw [← he.trans he'.symm]; exact this
                · rw [ΦF_high h (lt_of_not_ge hc') he']
                  exact img_lt (by omega)
              · rw [ΦF_high h (lt_of_not_ge hc) he]
                have he' : r'.coeff d ≠ (official ρc.row).coeff d := by omega
                rw [ΦF_high h (lt_of_not_ge hc') he']
                rcases Nat.lt_or_eq_of_le hσ with hl | he2
                · exact img_lt (by omega)
                · have := (IH (slot (d + 2) T (r.coeff d + E.lift (d + 2) S)) he2).1
                  rw [← he2]; exact this
      · intro ρr ρc h hc
        have hρ := topIn_inRegion h
        have hc' : official ρc.row < r' := lt_trans hc hlt
        have hρr : (official ρc.row).coeff d ≤ r.coeff d :=
          Recon.RowLaw.coeff_le_of_inRegion hρ hr hc.le
        by_cases he : r.coeff d = (official ρc.row).coeff d
        · rw [ΦG_mid h he]
          by_cases he' : r'.coeff d = (official ρc.row).coeff d
          · rw [ΦG_mid h he']
            have hsub : topIn E.M E.cr (d + 1) (slot (d + 2) S (r.coeff d)) = some (ρr, ρc) := by
              rw [he]; exact ChainCorr.Inner.topIn_slot h
            have := (IH (slot (d + 2) T (E.hB (d + 2) T)) (he.trans he'.symm)).2 ρr ρc hsub hc
            rw [← he.trans he'.symm]; exact this
          · rw [ΦG_high h he']
            exact img_lt (by omega)
        · rw [ΦG_high h he]
          have he' : r'.coeff d ≠ (official ρc.row).coeff d := by omega
          rw [ΦG_high h he']
          rcases Nat.lt_or_eq_of_le hσ with hl | he2
          · exact img_lt (by omega)
          · have := (IH (slot (d + 2) T (r.coeff d + E.hB (d + 2) T - (official ρc.row).coeff d))
              he2).1
            rw [← he2]; exact this

end OmegaY.Official.Classification.Proofs.CopyShape
