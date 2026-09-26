/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/TopChainLowExp.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CopyShapeFinal

set_option backward.do.legacy false

set_option autoImplicit false

/-!
# The row map does not raise the lowest non-zero exponent (proved)

`Ψ_lowExp`: for the row map `Ψ E top` of a copied column (`LegRowMatchInnerMap.lean`) with a
root-top function `top` satisfying `TopOK`, and a row `r` of the source region: if `r` has a
non-zero coefficient at an exponent `k` inside the region, then the image `Ψ r` has a non-zero
coefficient at an exponent `≤ k`.

The `F` mode keeps a non-zero coefficient non-zero (`σ`, `σ + lift`, `ρ_d + lift`); the `G`
mode (entered above the root top `ρ`, which it keeps: `TopOK`) ends at the first exponent where
`r` exceeds `ρ`, with the non-zero coefficient `σ + h_B - ρ_d`.
-/

namespace OmegaY.Official.Classification.Proofs.CopyShape.TopChainLE

open Canonical Reserve Official Descent Classification Proofs
open CopyShape.InnerRow CopyShape.ProfileLeg

/-- The coefficient of an image at the exponent of its slot. -/
theorem Ψ_coeff_slot (E : Env) (top : Nat → Row → Option (Ref × Cell)) (d : Nat) (m : Bool)
    (S T r : Row) (j : Nat) : (Ψ E top m (d + 1) S (slot (d + 2) T j) r).coeff d = j := by
  have h := (Classification.inRegion_iff _ _ _).mp (Ψ_mem E top d m S (slot (d + 2) T j) r) d
    (by omega)
  rw [h]
  exact Proofs.ChainCorr.CopyMonoProof.slot_coeff_at

/-- Of two rows that agree above `d` and differ at `d`, the larger one is larger at `d`. -/
theorem coeff_lt_of_lt {a b : Row} {d : Nat} (hlt : a < b)
    (hag : ∀ k, d < k → a.coeff k = b.coeff k) (hne : a.coeff d ≠ b.coeff d) :
    a.coeff d < b.coeff d := by
  obtain ⟨i, hi, hlt'⟩ := Row.lt_iff.mp hlt
  rcases Nat.lt_trichotomy i d with h | h | h
  · exact absurd (hi d h) hne
  · subst h; exact hlt'
  · exact absurd (hag i h) (ne_of_lt hlt')

/-- **`Ψ` does not raise the lowest non-zero exponent.** Statement for the level `d + 1`
(exponents `< d`). -/
theorem Ψ_lowExp (E : Env) (top : Nat → Row → Option (Ref × Cell)) (hT : TopOK E top) :
    ∀ (d : Nat) (S T r : Row), inRegion (d + 1) S r = true →
      (∀ k, k < d → r.coeff k ≠ 0 →
        ∃ k', k' ≤ k ∧ (Ψ E top false (d + 1) S T r).coeff k' ≠ 0) ∧
      (∀ ρr ρc, top (d + 1) S = some (ρr, ρc) → official ρc.row < r →
        (∃ k', k' < d ∧ (Ψ E top true (d + 1) S T r).coeff k' ≠ 0) ∧
        (∀ k, k < d → r.coeff k ≠ 0 →
          ∃ k', k' ≤ k ∧ (Ψ E top true (d + 1) S T r).coeff k' ≠ 0))
  | 0, S, T, r, hr => by
      refine ⟨fun k hk => absurd hk (Nat.not_lt_zero _), fun ρr ρc h hlt => ?_⟩
      exfalso
      have hρ := (Classification.inRegion_iff _ _ _).mp (top_inRegion hT h)
      have hr' := (Classification.inRegion_iff _ _ _).mp hr
      obtain ⟨i, _, hi⟩ := Row.lt_iff.mp hlt
      have := (hρ i (by omega)).trans (hr' i (by omega)).symm
      omega
  | d + 1, S, T, r, hr => by
      have hS' : inRegion (d + 1) (slot (d + 2) S (r.coeff d)) r = true := Proofs.ChainCorr.CopyMonoProof.mem_slot_height hr
      have IH := Ψ_lowExp E top hT d (slot (d + 2) S (r.coeff d))
      -- the F mode keeps a non-zero coefficient at `d` and below
      have hF : ∀ (T' : Row) (j : Nat), (r.coeff d ≠ 0 → j ≠ 0) →
          ∀ k, k < d + 1 → r.coeff k ≠ 0 → ∃ k', k' ≤ k ∧
            (Ψ E top false (d + 1) (slot (d + 2) S (r.coeff d)) (slot (d + 2) T' j) r).coeff k'
              ≠ 0 := by
        intro T' j hj k hk hrk
        rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hk) with hk' | hk'
        · exact (IH (slot (d + 2) T' j) r hS').1 k hk' hrk
        · subst hk'
          exact ⟨k, le_rfl, by rw [Ψ_coeff_slot]; exact hj hrk⟩
      refine ⟨fun k hk hrk => ?_, fun ρr ρc h hlt => ?_⟩
      · -- the F mode
        cases htop : top (d + 2) S with
        | none =>
            rw [ΨF_none htop]
            exact hF T (r.coeff d) id k hk hrk
        | some p =>
            obtain ⟨ρr, ρc⟩ := p
            by_cases hle : r ≤ official ρc.row
            · rw [ΨF_low htop hle]
              exact hF T (r.coeff d) id k hk hrk
            · by_cases hσ : r.coeff d = (official ρc.row).coeff d
              · rw [ΨF_mid htop (lt_of_not_ge hle) hσ]
                rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hk) with hk' | hk'
                · have htop' := hT.2 d S ρr ρc htop
                  rw [← hσ] at htop'
                  exact ((IH _ r hS').2 ρr ρc htop' (lt_of_not_ge hle)).2 k hk' hrk
                · subst hk'
                  refine ⟨k, le_rfl, ?_⟩
                  rw [Ψ_coeff_slot]
                  have := E.one_le_lift (k + 2) S
                  omega
              · rw [ΨF_high htop (lt_of_not_ge hle) hσ]
                exact hF T _ (fun _ => by have := E.one_le_lift (d + 2) S; omega) k hk hrk
      · -- the G mode
        have hρ := (Classification.inRegion_iff _ _ _).mp (top_inRegion hT h)
        have hr' := (Classification.inRegion_iff _ _ _).mp hr
        have hag : ∀ k, d < k → (official ρc.row).coeff k = r.coeff k :=
          fun k hk => (hρ k (by omega)).trans (hr' k (by omega)).symm
        by_cases hσ : r.coeff d = (official ρc.row).coeff d
        · rw [ΨG_mid h hσ]
          have htop' := hT.2 d S ρr ρc h
          rw [← hσ] at htop'
          obtain ⟨⟨k', hk', hne⟩, hall⟩ := (IH _ r hS').2 ρr ρc htop' hlt
          refine ⟨⟨k', by omega, hne⟩, fun k hk hrk => ?_⟩
          rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hk) with hk'' | hk''
          · exact hall k hk'' hrk
          · exact ⟨k', by omega, hne⟩
        · rw [ΨG_high h hσ]
          have hgt := coeff_lt_of_lt hlt hag (fun h' => hσ h'.symm)
          have hnz : (Ψ E top false (d + 1) (slot (d + 2) S (r.coeff d))
              (slot (d + 2) T (r.coeff d + E.hB (d + 2) T - (official ρc.row).coeff d)) r).coeff d
                ≠ 0 := by
            rw [Ψ_coeff_slot]; omega
          refine ⟨⟨d, by omega, hnz⟩, fun k hk hrk => ?_⟩
          rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hk) with hk' | hk'
          · exact (IH _ r hS').1 k hk' hrk
          · subst hk'; exact ⟨k, le_rfl, hnz⟩

/-! ## Stored rows -/

theorem coeff_zero_row (i : Nat) : (0 : Row).coeff i = 0 := by
  show Row.coeff (Row.ofList [0]) i = 0
  rw [Row.coeff_ofList]
  cases i <;> simp

theorem stored_coeff0_ne {ρ : Row} (h : isFinite ρ = true ∨ ρ.coeff 0 ≠ 0) :
    (stored ρ).coeff 0 ≠ 0 := by
  unfold stored
  by_cases hf : isFinite ρ = true
  · rw [if_pos hf]
    show Row.coeff (Row.ofList [ρ.coeff 0 + 1]) 0 ≠ 0
    rw [Row.coeff_ofList]; simp
  · rw [if_neg hf]
    rcases h with h | h
    · exact absurd h hf
    · exact h

theorem stored_coeff0_inf {ρ : Row} (hf : ¬ isFinite ρ = true) : (stored ρ).coeff 0 = ρ.coeff 0 := by
  unfold stored
  rw [if_neg hf]

/-- A positive finite row has a non-zero coefficient at `0`. -/
theorem coeff0_of_finite {r : Row} (hr : (0 : Row) < r) (hf : isFinite r = true) :
    r.coeff 0 ≠ 0 := by
  obtain ⟨i, _, hi⟩ := Row.lt_iff.mp hr
  rw [coeff_zero_row] at hi
  have hlen : len r ≤ 1 := by simpa [isFinite] using hf
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · subst h0; omega
  · rw [Classification.coeff_eq_zero_of_len_le (by omega)] at hi; omega

/-- **The lowest non-zero exponent of stored rows.** If every non-zero coefficient of `r`
has a non-zero coefficient of `q` at or below it, the same holds for the stored rows. -/
theorem stored_lowExp {r q : Row} (hr0 : (0 : Row) < r)
    (hΨ : ∀ k0, r.coeff k0 ≠ 0 → ∃ k', k' ≤ k0 ∧ q.coeff k' ≠ 0) :
    ∀ k, (∀ k', k' ≤ k → (stored q).coeff k' = 0) → ∀ k', k' ≤ k → (stored r).coeff k' = 0 := by
  intro k hq k' hk'
  by_contra hne
  -- a non-zero coefficient of `r` at or below `k`
  obtain ⟨k0, hk0, hr⟩ : ∃ k0, k0 ≤ k ∧ r.coeff k0 ≠ 0 := by
    rcases Nat.eq_zero_or_pos k' with h0 | hpos
    · subst h0
      by_cases hf : isFinite r = true
      · exact ⟨0, Nat.zero_le _, coeff0_of_finite hr0 hf⟩
      · exact ⟨0, Nat.zero_le _, by rw [← stored_coeff0_inf hf]; exact hne⟩
    · exact ⟨k', hk', by rw [← Recon.coeff_stored_pos r hpos]; exact hne⟩
  obtain ⟨k'', hk'', hqk⟩ := hΨ k0 hr
  rcases Nat.eq_zero_or_pos k'' with h0 | hpos
  · subst h0
    exact stored_coeff0_ne (Or.inr hqk) (hq 0 (Nat.zero_le _))
  · exact hqk (by rw [← Recon.coeff_stored_pos q hpos]; exact hq k'' (by omega))

end OmegaY.Official.Classification.Proofs.CopyShape.TopChainLE

#print axioms OmegaY.Official.Classification.Proofs.CopyShape.TopChainLE.Ψ_lowExp
