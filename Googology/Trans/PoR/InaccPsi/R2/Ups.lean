import Googology.Trans.PoR.InaccPsi.R2.Points
import Googology.Trans.PoR.InaccPsi.R2.CitedR1

/-!
# The Lean `υ` is Wilken's `υ`

[G20] G. Wilken, "A glimpse of Σ₃-elementarity", Def 21.4: `υ₀ := 0`, `υ_{ξ+1} := υ_ξ^∞ = T^{υ_ξ} ∩ Ω`,
`υ_λ := sup{υ_ι | ι < λ}`.  `R2.Points` defines `upsilon` as the enumeration of
`{0} ∪ {α > 0 | α <₁ ∞}`.  From the cited facts ([W07a] Def 9.1, [W07b] Cor 5.10, in
`R2.CitedR1` and `R2.Cited`):

* `upsPt_iff_tauW`: the nonzero `υ`-points are the `τ_ρ` of [W07a] Def 9.1;
* `upsSet_closed`, `upsSet_unbounded`, `upsPt_sSup`: the class of `υ`-points is closed and
  unbounded;
* `upsilon_normal`: `upsilon` is a normal function; `upsilon_zero`: `υ₀ = 0`;
* `upsilon_isNext`: `υ_{ξ+1}` is the least `υ`-point above `υ_ξ` (= `υ_ξ^∞`);
* `upsilon_succ_T`: for countable `υ_{ξ+1}`, `T^{υ_ξ} ∩ Ω₁ = υ_{ξ+1}` (base `1` for `ξ = 0`), the
  successor clause of [G20] Def 21.4;
* `upsilon_limit`: `υ_λ` is the supremum of `υ_ι`, `ι < λ`, the limit clause;
* `upsPt_iff_upsilon`: the nonzero `υ`-points are the `υ_ι`, `ι > 0`;
* `next_lt_Om1`, `upsilon_nat_lt_Om1`, `upsilon_omega_lt_Om1`: `υ_n` (`n < ω`) and `υ_ω` are
  countable.

So `upsilon` satisfies the three clauses of [G20] Def 21.4 (for the countable values, where `Tᵗ` is
taken with `Ω₁ = ω₁`), which determine it.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order

theorem not_ltInf1_zero : ¬ LtInf1 0 := fun h =>
  lt_irrefl _ (le1R_lim_P (h 1 zero_le) zero_lt_one).1

theorem tauW_pos (ρ : Ordinal.{0}) : 0 < tauW ρ := by
  have h : LtInf1 (tauW ρ) := (ltInf1_iff_tauW _).2 ⟨ρ, rfl⟩
  rcases eq_or_ne (tauW ρ) 0 with h0 | h0
  · rw [h0] at h; exact absurd h not_ltInf1_zero
  · exact pos_iff_ne_zero.2 h0

/-- The nonzero `υ`-points are the `τ_ρ` ([W07b] Cor 5.10). -/
theorem upsPt_iff_tauW {a : Ordinal.{0}} : UpsPt a ↔ ∃ ρ, a = tauW ρ := by
  constructor
  · intro h; exact (ltInf1_iff_tauW a).1 h.2
  · rintro ⟨ρ, rfl⟩; exact ⟨tauW_pos ρ, (ltInf1_iff_tauW _).2 ⟨ρ, rfl⟩⟩

theorem le_tauW (ρ : Ordinal.{0}) : ρ ≤ tauW ρ := tauW_normal.strictMono.le_apply

/-- The class of `υ`-points is closed under suprema. -/
theorem upsSet_closed : ∀ t ⊆ UpsSet, t.Nonempty → BddAbove t → sSup t ∈ UpsSet := by
  intro t ht hne hbdd
  by_cases h0 : sSup t = 0
  · exact Or.inl h0
  right
  set t' := {s | s ∈ t ∧ s ≠ 0} with ht'
  have hne' : t'.Nonempty := by
    by_contra hn
    apply h0
    refine le_antisymm (csSup_le hne fun s hs => ?_) zero_le
    by_contra hs0
    exact hn ⟨s, hs, fun e => hs0 (by rw [e])⟩
  have hsup : sSup t = sSup t' := by
    refine le_antisymm (csSup_le hne fun s hs => ?_) (csSup_le_csSup hbdd hne' fun s hs => hs.1)
    by_cases hs0 : s = 0
    · rw [hs0]; exact zero_le
    · exact le_csSup (hbdd.mono fun s hs => hs.1) ⟨hs, hs0⟩
  set R := {ρ | tauW ρ ∈ t} with hR
  have himg : t' = tauW '' R := by
    ext s
    constructor
    · rintro ⟨hs, hs0⟩
      rcases ht hs with e | hu
      · exact absurd e hs0
      · obtain ⟨ρ, rfl⟩ := upsPt_iff_tauW.1 hu
        exact ⟨ρ, hs, rfl⟩
    · rintro ⟨ρ, hρ, rfl⟩
      exact ⟨hρ, (tauW_pos ρ).ne'⟩
  have hRne : R.Nonempty := by
    obtain ⟨s, hs⟩ := hne'
    rw [himg] at hs
    obtain ⟨ρ, hρ, -⟩ := hs
    exact ⟨ρ, hρ⟩
  have hRbdd : BddAbove R := by
    obtain ⟨B, hB⟩ := hbdd
    exact ⟨B, fun ρ hρ => (le_tauW ρ).trans (hB hρ)⟩
  rw [hsup, himg, ← tauW_normal.map_sSup hRne hRbdd]
  exact upsPt_iff_tauW.2 ⟨_, rfl⟩

theorem upsSet_unbounded : ¬ BddAbove UpsSet := by
  rintro ⟨B, hB⟩
  have h := hB (Or.inr (upsPt_iff_tauW.2 ⟨succ B, rfl⟩) : tauW (succ B) ∈ UpsSet)
  exact absurd (lt_of_lt_of_le (lt_succ B) ((le_tauW _).trans h)) (lt_irrefl _)

/-- A nonempty bounded set of nonzero `υ`-points has a nonzero `υ`-point as supremum. -/
theorem upsPt_sSup {t : Set Ordinal.{0}} (hne : t.Nonempty) (hbdd : BddAbove t)
    (ht : ∀ s ∈ t, UpsPt s) : UpsPt (sSup t) := by
  rcases upsSet_closed t (fun s hs => Or.inr (ht s hs)) hne hbdd with h0 | h
  · obtain ⟨s, hs⟩ := hne
    have := le_csSup hbdd hs
    rw [h0] at this
    exact absurd (lt_of_lt_of_le (ht s hs).1 this) (lt_irrefl _)
  · exact h

/-- If `υ`-points are cofinal below `b > 0`, then `b` is a `υ`-point. -/
theorem upsPt_of_cofinal {b : Ordinal.{0}} (hb : 0 < b)
    (h : ∀ c < b, ∃ u, c < u ∧ u < b ∧ UpsPt u) : UpsPt b := by
  set t := {u | u < b ∧ UpsPt u}
  have hne : t.Nonempty := by
    obtain ⟨u, -, hu, hu'⟩ := h 0 hb
    exact ⟨u, hu, hu'⟩
  have hbdd : BddAbove t := ⟨b, fun u hu => hu.1.le⟩
  have hsup : sSup t = b := by
    refine le_antisymm (csSup_le hne fun u hu => hu.1.le) ?_
    by_contra hlt
    obtain ⟨u, hcu, hub, hu⟩ := h _ (not_le.1 hlt)
    exact absurd (le_csSup hbdd ⟨hub, hu⟩) (not_le.2 hcu)
  rw [← hsup]
  exact upsPt_sSup hne hbdd fun u hu => hu.2

/-- `upsilon` is a normal function. -/
theorem upsilon_normal : Order.IsNormal upsilon := isNormal_enumOrd upsSet_closed upsSet_unbounded

theorem upsilon_mem (ι : Ordinal.{0}) : upsilon ι ∈ UpsSet := enumOrd_mem upsSet_unbounded ι

/-- [G20] Def 21.4 (1): `υ₀ = 0`. -/
theorem upsilon_zero : upsilon 0 = 0 := by
  unfold upsilon
  rw [enumOrd_zero]
  exact le_antisymm (csInf_le' (Or.inl rfl : (0 : Ordinal.{0}) ∈ UpsSet)) zero_le

theorem upsPt_upsilon {ι : Ordinal.{0}} (hι : 0 < ι) : UpsPt (upsilon ι) := by
  rcases upsilon_mem ι with h | h
  · have := upsilon_normal.strictMono hι
    rw [upsilon_zero, h] at this
    exact absurd this (lt_irrefl _)
  · exact h

/-- The nonzero `υ`-points are exactly the `υ_ι`, `ι > 0`. -/
theorem upsPt_iff_upsilon {a : Ordinal.{0}} : UpsPt a ↔ ∃ ι, 0 < ι ∧ a = upsilon ι := by
  constructor
  · intro h
    obtain ⟨ι, hι⟩ := enumOrd_surjective upsSet_unbounded (Or.inr h : a ∈ UpsSet)
    refine ⟨ι, pos_iff_ne_zero.2 fun h0 => ?_, hι.symm⟩
    have hι' : upsilon ι = a := hι
    rw [h0, upsilon_zero] at hι'
    exact absurd hι'.symm h.1.ne'
  · rintro ⟨ι, hι, rfl⟩
    exact upsPt_upsilon hι

/-- `υ_{ξ+1} = υ_ξ^∞`, the least `υ`-point above `υ_ξ`. -/
theorem upsilon_isNext (ξ : Ordinal.{0}) : IsNext (upsilon ξ) (upsilon (succ ξ)) :=
  ⟨upsilon_normal.strictMono (lt_succ ξ), upsPt_upsilon (lt_of_le_of_lt zero_le (lt_succ ξ)),
    fun u hu hup => enumOrd_succ_le upsSet_unbounded (Or.inr hup) hu⟩

/-- **[G20] Def 21.4 (2)**: for countable `υ_{ξ+1}`, `T^{υ_ξ} ∩ Ω₁ = υ_{ξ+1}` (with base `1` when
`ξ = 0`, the base of [W07a] Def 9.1). -/
theorem upsilon_succ_T (ξ : Ordinal.{0}) (hc : upsilon (succ ξ) < Om1) :
    ∀ a, a < Om1 → (a ∈ Tset (if ξ = 0 then 1 else upsilon ξ) ↔ a < upsilon (succ ξ)) := by
  have hn := upsilon_isNext ξ
  by_cases hξ : ξ = 0
  · rw [if_pos hξ]
    obtain ⟨m, h1m, hm, hmin, hT⟩ := T_inter_Om1_one
    have hmc : m = upsilon (succ ξ) := by
      have hc1 : 1 < upsilon (succ ξ) := by
        have hE := upsPt_inE hn.2.1
        have hpos := hn.2.1.1
        unfold InE at hE
        calc (1 : Ordinal.{0}) < ω := one_lt_omega0
          _ = ω ^ (1 : Ordinal.{0}) := (opow_one ω).symm
          _ ≤ ω ^ upsilon (succ ξ) := opow_le_opow_right omega0_pos (one_le_iff_pos.2 hpos)
          _ = upsilon (succ ξ) := hE
      refine le_antisymm (hmin _ hc1 hn.2.1.2) ?_
      refine hn.2.2 m ?_ ⟨lt_trans zero_lt_one h1m, hm⟩
      rw [hξ, upsilon_zero]; exact lt_trans zero_lt_one h1m
    rw [← hmc]; exact hT
  · rw [if_neg hξ]
    have hb : UpsPt (upsilon ξ) := upsPt_upsilon (pos_iff_ne_zero.2 hξ)
    obtain ⟨m, hmn, hT⟩ := exists_next hb (lt_trans hn.1 hc)
    rw [← hmn.unique hn]; exact hT

/-- **[G20] Def 21.4 (3)**: `υ_λ = sup{υ_ι | ι < λ}` for limits `λ`. -/
theorem upsilon_limit {l : Ordinal.{0}} (hl : IsSuccLimit l) :
    IsLUB (upsilon '' Set.Iio l) (upsilon l) :=
  upsilon_normal.isLUB_image_Iio_of_isSuccLimit hl

/-! ## Countability of the first `υ`-points -/

/-- A sequence of countable ordinals that bounds every countable element of `Tset τ` forces
`Tᵗ ∩ Ω₁ < Ω₁`. -/
theorem lt_Om1_of_bound {τ m : Ordinal.{0}} (hT : ∀ a, a < Om1 → (a ∈ Tset τ ↔ a < m))
    {f : ℕ → Ordinal.{0}} (hf : ∀ n, f n < Om1) (hb : ∀ a, a < Om1 → a ∈ Tset τ → ∃ n, a < f n) :
    m < Om1 := by
  by_contra hm
  have hs : (⨆ n, f n) < Om1 := Ordinal.iSup_lt_omega_one hf
  obtain ⟨n, hn⟩ := hb _ hs ((hT _ hs).2 (lt_of_lt_of_le hs (not_lt.1 hm)))
  have hbdd : BddAbove (Set.range f) := ⟨Om1, by rintro _ ⟨k, rfl⟩; exact (hf k).le⟩
  exact absurd (le_ciSup hbdd n) (not_le.2 hn)

/-- The next `υ`-point above `0` or above a countable `υ`-point is countable ([W07a] Thm 3.23, Lemma
3.27, through `T_one_bound` and `ht_spec`, `Dl_spec`). -/
theorem next_lt_Om1 {b m : Ordinal.{0}} (hn : IsNext b m) (hb : b = 0 ∨ UpsPt b) (hb1 : b < Om1) :
    m < Om1 := by
  rcases hb with rfl | hb
  · obtain ⟨m', h1m', hm', hmin', hT'⟩ := T_inter_Om1_one
    obtain ⟨f, hf, hfb⟩ := T_one_bound
    have hm'1 : m' < Om1 := lt_Om1_of_bound hT' hf hfb
    have hmm' : m ≤ m' := hn.2.2 m' (lt_trans zero_lt_one h1m') ⟨lt_trans zero_lt_one h1m', hm'⟩
    exact lt_of_le_of_lt hmm' hm'1
  · obtain ⟨m', hmn, hT⟩ := exists_next hb hb1
    rw [hn.unique hmn]
    have hE := upsPt_inE hb
    refine lt_Om1_of_bound hT (f := Dl b) (fun n => (Dl_spec hE hb1 n).2.1) ?_
    intro a ha haT
    exact (ht_spec hE hb1 haT ha).1

theorem upsilon_nat_lt_Om1 (n : ℕ) : upsilon n < Om1 := by
  induction n with
  | zero => rw [Nat.cast_zero, upsilon_zero]; exact omega_pos 1
  | succ k ih =>
    have hn := upsilon_isNext (k : Ordinal.{0})
    rw [Order.succ_eq_add_one] at hn
    rw [Nat.cast_succ]
    refine next_lt_Om1 hn ?_ ih
    rcases eq_or_ne k 0 with rfl | hk
    · left; rw [Nat.cast_zero, upsilon_zero]
    · right; exact upsPt_upsilon (by exact_mod_cast Nat.pos_of_ne_zero hk)

/-- `υ_ω` is countable. -/
theorem upsilon_omega_lt_Om1 : upsilon ω < Om1 := by
  have hlub := upsilon_limit isSuccLimit_omega0
  have hs : (⨆ n : ℕ, upsilon n) < Om1 := Ordinal.iSup_lt_omega_one upsilon_nat_lt_Om1
  refine lt_of_le_of_lt (hlub.2 ?_) hs
  rintro _ ⟨i, hi, rfl⟩
  obtain ⟨n, rfl⟩ := lt_omega0.1 hi
  exact le_ciSup (f := fun n : ℕ => upsilon n) ⟨Om1, by rintro _ ⟨k, rfl⟩; exact (upsilon_nat_lt_Om1 k).le⟩ n

end Googology.Trans.PoR.InaccPsi.R2
