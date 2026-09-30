import Mathlib.SetTheory.Ordinal.Principal
import Mathlib.SetTheory.Ordinal.FixedPoint

/-!
# Cantor normal form as sums of powers of `ω`

* `sumOmega [β_1, …, β_m] = ω^β_1 + ⋯ + ω^β_m`.
* `sumOmega_lt`: if every `β_i < α`, the sum is below `ω^α` (`ω^α` is additive
  principal).
* `exists_sumOmega`: every `γ < ω^α` is such a sum with `β_1 ≥ ⋯ ≥ β_m`, all
  below `α` (the Cantor normal form, with repeated exponents instead of
  coefficients).
-/

namespace Googology.Trans.PSS.Phi

open Ordinal

/-- `ω^β_1 + ⋯ + ω^β_m`. -/
noncomputable def sumOmega : List Ordinal.{0} → Ordinal.{0}
  | [] => 0
  | b :: bs => ω ^ b + sumOmega bs

theorem sumOmega_nil : sumOmega [] = 0 := rfl

theorem sumOmega_cons (b : Ordinal.{0}) (bs : List Ordinal.{0}) :
    sumOmega (b :: bs) = ω ^ b + sumOmega bs := rfl

/-- **Sums of smaller powers stay below `ω^α`.** -/
theorem sumOmega_lt {α : Ordinal.{0}} : ∀ bs : List Ordinal.{0}, (∀ b ∈ bs, b < α) →
    sumOmega bs < ω ^ α
  | [], _ => opow_pos _ omega0_pos
  | b :: bs, h =>
    isPrincipal_add_omega0_opow α ((opow_lt_opow_iff_right one_lt_omega0).mpr (h b (by simp)))
      (sumOmega_lt bs (fun b' hb' => h b' (by simp [hb'])))

theorem sub_opow_log_lt {γ : Ordinal.{0}} (hγ : γ ≠ 0) : γ - ω ^ log ω γ < γ := by
  have hle : ω ^ log ω γ ≤ γ := opow_log_le_self ω hγ
  rcases lt_or_eq_of_le (sub_le_self γ (ω ^ log ω γ)) with h | h
  · exact h
  · exfalso
    have e : ω ^ log ω γ + γ = γ := by
      have := Ordinal.add_sub_cancel_of_le hle
      rw [h] at this
      exact this
    have h2 := add_eq_right_iff_mul_omega0_le.mp e
    rw [← opow_succ] at h2
    exact absurd (lt_opow_succ_log_self one_lt_omega0 γ) (not_lt.mpr h2)

/-- **Cantor normal form**: every `γ` is `ω^β_1 + ⋯ + ω^β_m` with
`β_1 ≥ ⋯ ≥ β_m` and every `ω^β_i ≤ γ`. -/
theorem exists_sumOmega' (γ : Ordinal.{0}) : ∃ bs : List Ordinal.{0},
    bs.Pairwise (fun a b => b ≤ a) ∧ (∀ b ∈ bs, ω ^ b ≤ γ) ∧ sumOmega bs = γ := by
  induction γ using WellFoundedLT.induction with
  | _ γ ih =>
    rcases eq_or_ne γ 0 with rfl | hγ
    · exact ⟨[], by simp, by simp, rfl⟩
    · set β := log ω γ with hβ
      have hle : ω ^ β ≤ γ := opow_log_le_self ω hγ
      obtain ⟨bs, hbs, hbγ, hsum⟩ := ih _ (sub_opow_log_lt hγ)
      refine ⟨β :: bs, ?_, ?_, ?_⟩
      · rw [List.pairwise_cons]
        refine ⟨fun b hb => ?_, hbs⟩
        have h1 : ω ^ b < ω ^ Order.succ β :=
          lt_of_le_of_lt (le_trans (hbγ b hb) (sub_le_self _ _)) (lt_opow_succ_log_self one_lt_omega0 γ)
        rw [opow_lt_opow_iff_right one_lt_omega0] at h1
        exact Order.lt_succ_iff.mp h1
      · intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact hle
        · exact le_trans (hbγ b hb) (sub_le_self _ _)
      · rw [sumOmega_cons, hsum, Ordinal.add_sub_cancel_of_le hle]

/-- **Every `γ < ω^α` is a sum of non-increasing powers `ω^β` with `β < α`.** -/
theorem exists_sumOmega {γ α : Ordinal.{0}} (h : γ < ω ^ α) : ∃ bs : List Ordinal.{0},
    bs.Pairwise (fun a b => b ≤ a) ∧ (∀ b ∈ bs, b < α) ∧ sumOmega bs = γ := by
  obtain ⟨bs, h1, h2, h3⟩ := exists_sumOmega' γ
  refine ⟨bs, h1, fun b hb => ?_, h3⟩
  exact (opow_lt_opow_iff_right one_lt_omega0).mp (lt_of_le_of_lt (h2 b hb) h)

end Googology.Trans.PSS.Phi
