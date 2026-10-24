import Googology.Trans.PoR.InaccPsi.R2.GoIt

/-!
# A FUNDAMENTAL SEQUENCE FOR EVERY LIMIT BELOW `ε₀` (no choice between sequences is ever compared)

Every ordinal below `ε₀` is countable (`gp_card_tower`, `gp_countable`), so every limit `λ < ε₀` has a strictly
increasing sequence `gpFs λ k < λ` cofinal in `λ` (`gpFs_lt`, `gpFs_mono`, `gpFs_cof`).  The recursion of `R2.GpRec`
uses this sequence only to supply the `ℕ`-indexed data a union of digit systems asks for; the readings of the union
do not depend on it (they are those of every earlier system, `R2.GpRec`).

* `gp_card_tower`, `gp_countable`, `gp_surj`, `gpUp` (`f ↦` a strictly increasing majorant), `gpFs`.

No new axiom.  New definitions: `gpUp`, `gpFs`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gp

open Ordinal Order Set

/-- The towers `ω ↑↑ n` are countable. -/
theorem gp_card_tower : ∀ n : ℕ, ((fun a : Ordinal.{0} => ω ^ a)^[n] 0).card ≤ Cardinal.aleph0
  | 0 => by simp
  | n + 1 => by
    rw [Function.iterate_succ_apply']
    refine (card_opow_le _ _).trans (max_le le_rfl (max_le ?_ (gp_card_tower n)))
    rw [card_omega0]

/-- **Every ordinal below `ε₀` is countable.** -/
theorem gp_countable {l : Ordinal.{0}} (hl : l < ε₀) : Countable (Iio l) := by
  obtain ⟨n, hn⟩ := lt_epsilon_zero.1 hl
  rw [← Cardinal.mk_le_aleph0_iff, Cardinal.mk_Iio_ordinal, Cardinal.lift_le_aleph0]
  exact (card_le_card hn.le).trans (gp_card_tower n)

/-- A surjection of `ℕ` onto the ordinals below `λ` (`0 < λ < ε₀`). -/
theorem gp_surj {l : Ordinal.{0}} (hl : l < ε₀) (h0 : 0 < l) :
    ∃ f : ℕ → Ordinal.{0}, (∀ k, f k < l) ∧ ∀ t, t < l → ∃ k, f k = t := by
  haveI := gp_countable hl
  haveI : Nonempty (Iio l) := ⟨⟨0, h0⟩⟩
  obtain ⟨f, hf⟩ := exists_surjective_nat (Iio l)
  refine ⟨fun k => (f k).1, fun k => (f k).2, fun t ht => ?_⟩
  obtain ⟨k, hk⟩ := hf ⟨t, ht⟩
  exact ⟨k, by show (f k).1 = t; rw [hk]⟩

/-- A strictly increasing majorant of `f`. -/
noncomputable def gpUp (f : ℕ → Ordinal.{0}) : ℕ → Ordinal.{0}
  | 0 => f 0
  | k + 1 => max (gpUp f k + 1) (f (k + 1))

theorem gpUp_ge (f : ℕ → Ordinal.{0}) : ∀ k, f k ≤ gpUp f k
  | 0 => le_rfl
  | k + 1 => le_max_right _ _

theorem gpUp_mono (f : ℕ → Ordinal.{0}) (k : ℕ) : gpUp f k < gpUp f (k + 1) :=
  (lt_add_one _).trans_le (le_max_left _ _)

theorem gpUp_lt {f : ℕ → Ordinal.{0}} {l : Ordinal.{0}} (hl : IsSuccLimit l) (hf : ∀ k, f k < l) :
    ∀ k, gpUp f k < l
  | 0 => hf 0
  | k + 1 => max_lt (hl.add_one_lt (gpUp_lt hl hf k)) (hf (k + 1))

open Classical in
/-- **The fundamental sequence of a limit `λ < ε₀`** (an arbitrary one: nothing below depends on the choice). -/
noncomputable def gpFs (l : Ordinal.{0}) : ℕ → Ordinal.{0} :=
  if h : l < ε₀ ∧ 0 < l then gpUp (Classical.choose (gp_surj h.1 h.2)) else fun _ => 0

section Fs

variable {l : Ordinal.{0}} (hl : IsSuccLimit l) (hl0 : l < ε₀)
include hl hl0

theorem gpFs_eq : gpFs l = gpUp (Classical.choose (gp_surj hl0 hl.bot_lt)) := by
  unfold gpFs; rw [dif_pos ⟨hl0, hl.bot_lt⟩]

theorem gpFs_lt (k : ℕ) : gpFs l k < l := by
  rw [gpFs_eq hl hl0]
  exact gpUp_lt hl (Classical.choose_spec (gp_surj hl0 hl.bot_lt)).1 k

theorem gpFs_mono (k : ℕ) : gpFs l k < gpFs l (k + 1) := by
  rw [gpFs_eq hl hl0]; exact gpUp_mono _ k

/-- **Cofinality**: every `t < λ` lies below some `gpFs λ k`. -/
theorem gpFs_cof (t : Ordinal.{0}) (ht : t < l) : ∃ k, t < gpFs l k := by
  rw [gpFs_eq hl hl0]
  obtain ⟨k, hk⟩ := (Classical.choose_spec (gp_surj hl0 hl.bot_lt)).2 t ht
  refine ⟨k + 1, ?_⟩
  rw [← hk]
  exact (gpUp_ge _ k).trans_lt (gpUp_mono _ k)

theorem gpFs_mono' {j k : ℕ} (h : j ≤ k) : gpFs l j ≤ gpFs l k := by
  induction k, h using Nat.le_induction with
  | base => exact le_rfl
  | succ k _ ih => exact ih.trans (gpFs_mono hl hl0 k).le

end Fs

end Googology.Trans.PoR.InaccPsi.R2.Gp
