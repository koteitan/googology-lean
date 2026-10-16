import Googology.Trans.PoR.InaccPsi.R2.OC2

/-!
# `ν_C` is a restart, and the shape of `U₂`

Let `ρ_L <₂ ν_C` be the first non-standard pair of `R₂^C` (`left_restart_nuC`, `pairs_cof_nuC`) and
`U₂ = {u ≤ ν_C : u ≤₁ ν_C}`.

* `U2_shape` (the shape clause of the project's Theorem LIFT-0 at `k = 2`):
  `U₂ = Pred₁(ρ_L) ∪ {ρ_L, ν_C}`.  A member `u` of `U₂` with `ρ_L < u < ν_C` would give `ρ_L ≤₂ u`
  (`≤₂` respects `≤₁`, [C09] Lemma 5.5 (6), `le2_of_le1`), against "a restart has no `<₂`-successor
  below `ν_C`" (`noSucc_C`).
* `nuC_restart` (**`ν_C` is a restart**: `ν_C = υ_ξ` with `ξ` a nonzero multiple of `ω²`).  By
  `classify`, `ν_C` is a restart or a point of a block `(υ_{bot}, δ]` with
  `δ = υ_{μ+ω(j+1)+1}`.  In a block, a `<₂`-pair `p <₂ q` with `υ_{bot} < p < q < ν_C` exists
  (pairs are cofinal below `ν_C`, `pairs_cof_nuC`); it is standard (`q < ν_C`), so `p = υ_{L'}` with
  `L'` a limit, and `μ + ω·j ≤ bot < L' < μ + ω·(j+1)`: no limit lies there.
* `nuC_upsPt`, `nuC_reach` (`lh(ρ_L) = ν_C`), `level2_restart` (the first block of level 2 with both
  ends restarts).

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order

section Shape

variable {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlν : upsilon l < nuC) (h2 : le2 (upsilon l) nuC)
include hl hlν h2

/-- **The shape of `U₂`** (LIFT-0 at `k = 2`, the shape clause): `u ≤ ν_C ∧ u ≤₁ ν_C` iff `u` is a
`<₁`-predecessor of `ρ_L`, or `ρ_L`, or `ν_C`. -/
theorem U2_shape (u : Ordinal.{0}) :
    (u ≤ nuC ∧ le1 u nuC) ↔ ((u < upsilon l ∧ le1 u (upsilon l)) ∨ u = upsilon l ∨ u = nuC) := by
  have h1 := le2_le1 h2
  constructor
  · rintro ⟨hu, hu1⟩
    rcases lt_trichotomy u (upsilon l) with hlt | heq | hgt
    · exact Or.inl ⟨hlt, le1_of_le_of_le1 hlt.le hlν.le hu1⟩
    · exact Or.inr (Or.inl heq)
    · rcases eq_or_lt_of_le hu with he | hlt'
      · exact Or.inr (Or.inr he)
      · exact absurd (le2_of_le1 hgt.le hu h2 hu1) (noSucc_C hl u hgt hlt')
  · rintro (⟨hlt, hu1⟩ | rfl | rfl)
    · exact ⟨(hlt.trans hlν).le, le1_trans hu1 h1⟩
    · exact ⟨hlν.le, h1⟩
    · exact ⟨le_rfl, le1_refl _⟩

/-- No member of `U₂` lies strictly between `ρ_L` and `ν_C`. -/
theorem U2_gap {u : Ordinal.{0}} (h1u : upsilon l < u) (hu : u < nuC) : ¬ le1 u nuC := by
  intro hu1
  rcases (U2_shape hl hlν h2 u).1 ⟨hu.le, hu1⟩ with ⟨h, -⟩ | h | h
  · exact absurd h (not_lt.2 h1u.le)
  · exact absurd h (ne_of_gt h1u)
  · exact absurd h (ne_of_lt hu)

end Shape

/-- `ν_C > 0`. -/
theorem nuC_pos : 0 < nuC := by
  obtain ⟨⟨l, -, hlν, -, -⟩, -⟩ := pairs_cof_nuC
  exact lt_of_le_of_lt zero_le hlν

/-- **`ν_C` is a restart**: `ν_C = υ_ξ` for a restart index `ξ` (a nonzero multiple of `ω²`). -/
theorem nuC_restart : ∃ ξ, IsRestartIdx ξ ∧ nuC = upsilon ξ := by
  obtain ⟨-, hcof⟩ := pairs_cof_nuC
  rcases classify nuC_pos with hr | ⟨μ, j, hμ, hb, hct⟩
  · exact hr
  exfalso
  obtain ⟨p, q, hzp, hpq, hqν, h2⟩ := hcof _ hb
  obtain ⟨L', hL'lim, -, rfl, rfl⟩ := (std_of_lt_nuC hqν hpq h2).parts
  have i1 : botI μ j < L' := upsilon_normal.strictMono.lt_iff_lt.1 hzp
  have i2 : L' + 1 < μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1 :=
    upsilon_normal.strictMono.lt_iff_lt.1 (lt_of_lt_of_le hqν hct)
  have hL'L : L' < μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) :=
    Order.add_one_le_iff.1 (Order.lt_add_one_iff.1 i2)
  have hLe : μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) = μ + ω * (j : Ordinal.{0}) + ω := by
    rw [omega_mul_succ, add_assoc]
  have he := limit_eq_add_omega hL'lim (lt_of_le_of_lt (botI_ge μ j) i1) (by rw [← hLe]; exact hL'L.le)
  rw [he, ← hLe] at hL'L
  exact lt_irrefl _ hL'L

/-- `ν_C` is a `υ`-point. -/
theorem nuC_upsPt : UpsPt nuC := by
  obtain ⟨ξ, hξ, he⟩ := nuC_restart
  rw [he]; exact upsPt_upsilon (pos_iff_ne_zero.2 hξ.1)

/-- **`lh(ρ_L) = ν_C`** for the left end `ρ_L` of the first non-standard pair. -/
theorem nuC_reach {l : Ordinal.{0}} (hlν : upsilon l < nuC) (h2 : le2 (upsilon l) nuC) :
    IsReach R2C (upsilon l) nuC :=
  reach_U2 hlν.le (le2_le1 h2)

/-- **The first block of level 2 with both ends restarts**: `ρ_L <₂ ν_C = ρ_ξ`, `L < ξ` restart
indices, `ρ_L` the only `<₂`-predecessor of `ν_C`, `lh(ρ_L) = ν_C`, and
`U₂ = Pred₁(ρ_L) ∪ {ρ_L, ν_C}`. -/
theorem level2_restart : ∃ L ξ, IsRestartIdx L ∧ IsRestartIdx ξ ∧ L < ξ ∧ nuC = upsilon ξ ∧
    le2 (upsilon L) nuC ∧ (∀ c < nuC, le2 c nuC → c = upsilon L) ∧
    IsReach R2C (upsilon L) nuC ∧
    (∀ u, (u ≤ nuC ∧ le1 u nuC) ↔ ((u < upsilon L ∧ le1 u (upsilon L)) ∨ u = upsilon L ∨ u = nuC)) := by
  obtain ⟨⟨L, hL, hLν, h2, -⟩, -⟩ := pairs_cof_nuC
  obtain ⟨ξ, hξ, he⟩ := nuC_restart
  have hLξ : L < ξ := upsilon_normal.strictMono.lt_iff_lt.1 (he ▸ hLν)
  exact ⟨L, ξ, hL, hξ, hLξ, he, h2, fun c hc hc2 => left_unique hL hLν h2 hc hc2,
    nuC_reach hLν h2, U2_shape hL hLν h2⟩

end Googology.Trans.PoR.InaccPsi.R2
