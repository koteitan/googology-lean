import Googology.Trans.PoR.InaccPsi.R2.CitedUv

/-!
# The two earlier twin citations as theorems, and the split at every level below `B₂`

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

* `uvDat_eq_rj` (**`ucDat z = rjDat z` for `z < ε_{Ω₁+1}`**: `Uc.ucDat_lt_X`, `Tl.tlDat_eq_tf`, `Tf.tfDat_eq_rj`),
  `uv_E_lt_B` (`ε_{Ω₁+1} < B₂`);
* `uvVt_tr2` (**the exact statement of `R2.urVt_tr2`**, from `R2.uvVt_trL`), `uvVt_tr3` (**the exact statement of
  `R2.ukVt_tr3`**, from `R2.uvVt_trH`);
* `uvIns` (the inserted countable part: `α + ρ` if `ucDat Γ < α`, else `ρ`), `uvVt_tr` (**both translations at every
  level `Γ = Ω₁·M < B₂`, `1 ≤ M`**, in one statement with `uvIns`), `uvVt_trS` (the same as a disjunction of the two
  subcases), `uvIns_lt` (`uvIns α Γ ρ < Ω₁`);
* `uv_Om1_mul_E` (`Ω₁·ε_{Ω₁+1} = ε_{Ω₁+1}`), `uv_new_level` (the level `Γ = ε_{Ω₁+1}` is new: `ε_{Ω₁+1} ≤ Γ < B₂`),
  `uvDat_E` (`ucDat Γ = 1` there).

No new axiom, no new definition other than `uvIns`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Uv

open Ordinal Googology.Trans.PoR.InaccPsi.R2

/-- `ε_{Ω₁+1} < B₂`. -/
theorem uv_E_lt_B : Gg.ggE < Uc.ucB := (Tf.tf_E_lt_BG.trans Tl.tl_BG_lt_X).trans Uc.uc_X_lt_B

/-- **`ucDat = rjDat` below `ε_{Ω₁+1}`.** -/
theorem uvDat_eq_rj {z : Ordinal.{0}} (hz : z < Gg.ggE) : Uc.ucDat z = Rj.rjDat z := by
  rw [Uc.ucDat_lt_X (hz.trans (Tf.tf_E_lt_BG.trans Tl.tl_BG_lt_X)), Tl.tlDat_eq_tf z (hz.trans Tf.tf_E_lt_BG),
    Tf.tfDat_eq_rj z hz]

/-- **`R2.urVt_tr2` as a theorem** (same statement), from `R2.uvVt_trL`. -/
theorem uvVt_tr2 {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) {n : ℕ} (hn : 1 ≤ n) {M ρ : Ordinal.{0}}
    (hM1 : 1 ≤ M) (hME : Om1 * M < Gg.ggE) (hMα : Rj.rjDat (Om1 * M) < Dl τ n) (hρ1 : ρ < Om1) :
    (Om1 * M + ρ ∈ Tset (Dl τ n) → vt (Dl τ n) (Om1 * M + ρ) < Dp τ n →
      Om1 * M + (Dl τ n + ρ) ∈ Tset τ ∧ vt (Dl τ n) (Om1 * M + ρ) = vt τ (Om1 * M + (Dl τ n + ρ))) ∧
    (Om1 * M + (Dl τ n + ρ) ∈ Tset τ → vt τ (Om1 * M + (Dl τ n + ρ)) < Dp τ n →
      Om1 * M + ρ ∈ Tset (Dl τ n) ∧ vt τ (Om1 * M + (Dl τ n + ρ)) = vt (Dl τ n) (Om1 * M + ρ)) :=
  uvVt_trL hτ hτ1 hn hM1 (hME.trans uv_E_lt_B) (by rwa [uvDat_eq_rj hME]) hρ1

/-- **`R2.ukVt_tr3` as a theorem** (same statement), from `R2.uvVt_trH`. -/
theorem uvVt_tr3 {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) {n : ℕ} (hn : 1 ≤ n) {M ρ : Ordinal.{0}}
    (hM1 : 1 ≤ M) (hME : Om1 * M < Gg.ggE) (hMα : Dl τ n ≤ Rj.rjDat (Om1 * M)) (hρ1 : ρ < Om1) :
    (Om1 * M + ρ ∈ Tset (Dl τ n) → vt (Dl τ n) (Om1 * M + ρ) < Dp τ n →
      Om1 * M + ρ ∈ Tset τ ∧ vt (Dl τ n) (Om1 * M + ρ) = vt τ (Om1 * M + ρ)) ∧
    (Om1 * M + ρ ∈ Tset τ → vt τ (Om1 * M + ρ) < Dp τ n →
      Om1 * M + ρ ∈ Tset (Dl τ n) ∧ vt τ (Om1 * M + ρ) = vt (Dl τ n) (Om1 * M + ρ)) :=
  uvVt_trH hτ hτ1 hn hM1 (hME.trans uv_E_lt_B) (by rwa [uvDat_eq_rj hME]) hρ1

/-- **The inserted countable part** of the translation at the level `Γ`: `α + ρ` in the subcase `Γ^* < α`
(`ucDat Γ < α`), `ρ` in the subcase `Γ^* ≥ α`. -/
noncomputable def uvIns (α Γ ρ : Ordinal.{0}) : Ordinal.{0} :=
  if Uc.ucDat Γ < α then α + ρ else ρ

theorem uvIns_low {α Γ ρ : Ordinal.{0}} (h : Uc.ucDat Γ < α) : uvIns α Γ ρ = α + ρ := by
  rw [uvIns, if_pos h]

theorem uvIns_high {α Γ ρ : Ordinal.{0}} (h : α ≤ Uc.ucDat Γ) : uvIns α Γ ρ = ρ := by
  rw [uvIns, if_neg (not_lt.2 h)]

/-- `α + ρ < Ω₁` for countable `α, ρ` (`Ω₁` is additively principal). -/
theorem uvIns_lt {α Γ ρ : Ordinal.{0}} (hα : α < Om1) (hρ : ρ < Om1) : uvIns α Γ ρ < Om1 := by
  unfold uvIns
  split_ifs
  · have h := Ordinal.isPrincipal_add_omega0_opow (Om1 : Ordinal.{0})
    rw [Rj.rj_Om1_opow] at h
    exact h hα hρ
  · exact hρ

/-- **Both translations of [W07a] Def 6.2 at every level `Γ = Ω₁·M`, `1 ≤ M`, `Γ < B₂`** (one statement, both
subcases): `ϑ^α(Γ + ρ) = ϑᵗ(Γ + uvIns α Γ ρ)` in both directions, with membership. -/
theorem uvVt_tr {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) {n : ℕ} (hn : 1 ≤ n) {M ρ : Ordinal.{0}}
    (hM1 : 1 ≤ M) (hMB : Om1 * M < Uc.ucB) (hρ1 : ρ < Om1) :
    (Om1 * M + ρ ∈ Tset (Dl τ n) → vt (Dl τ n) (Om1 * M + ρ) < Dp τ n →
      Om1 * M + uvIns (Dl τ n) (Om1 * M) ρ ∈ Tset τ ∧
        vt (Dl τ n) (Om1 * M + ρ) = vt τ (Om1 * M + uvIns (Dl τ n) (Om1 * M) ρ)) ∧
    (Om1 * M + uvIns (Dl τ n) (Om1 * M) ρ ∈ Tset τ → vt τ (Om1 * M + uvIns (Dl τ n) (Om1 * M) ρ) < Dp τ n →
      Om1 * M + ρ ∈ Tset (Dl τ n) ∧
        vt τ (Om1 * M + uvIns (Dl τ n) (Om1 * M) ρ) = vt (Dl τ n) (Om1 * M + ρ)) := by
  rcases lt_or_ge (Uc.ucDat (Om1 * M)) (Dl τ n) with hd | hd
  · rw [uvIns_low hd]; exact uvVt_trL hτ hτ1 hn hM1 hMB hd hρ1
  · rw [uvIns_high hd]; exact uvVt_trH hτ hτ1 hn hM1 hMB hd hρ1

/-- **The split at every level `Γ = Ω₁·M < B₂`**: under the hypotheses of part (i), either the data is `< α` and the
translation inserts `α`, or it is `≥ α` and the translation keeps the argument. -/
theorem uvVt_trS {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) {n : ℕ} (hn : 1 ≤ n) {M ρ : Ordinal.{0}}
    (hM1 : 1 ≤ M) (hMB : Om1 * M < Uc.ucB) (hρ1 : ρ < Om1) (hT : Om1 * M + ρ ∈ Tset (Dl τ n))
    (hv : vt (Dl τ n) (Om1 * M + ρ) < Dp τ n) :
    (Uc.ucDat (Om1 * M) < Dl τ n ∧ Om1 * M + (Dl τ n + ρ) ∈ Tset τ ∧
        vt (Dl τ n) (Om1 * M + ρ) = vt τ (Om1 * M + (Dl τ n + ρ))) ∨
      (Dl τ n ≤ Uc.ucDat (Om1 * M) ∧ Om1 * M + ρ ∈ Tset τ ∧
        vt (Dl τ n) (Om1 * M + ρ) = vt τ (Om1 * M + ρ)) := by
  rcases lt_or_ge (Uc.ucDat (Om1 * M)) (Dl τ n) with hd | hd
  · exact Or.inl ⟨hd, (uvVt_trL hτ hτ1 hn hM1 hMB hd hρ1).1 hT hv⟩
  · exact Or.inr ⟨hd, (uvVt_trH hτ hτ1 hn hM1 hMB hd hρ1).1 hT hv⟩

/-- `Ω₁·ε_{Ω₁+1} = ε_{Ω₁+1}`. -/
theorem uv_Om1_mul_E : Om1 * Gg.ggE = Gg.ggE := by
  have hE := Gg.ggE_spec.1
  have hab : (Om1 : Ordinal.{0}) + Gg.ggE = Gg.ggE :=
    Ordinal.add_of_omega0_opow_le (by rw [hE]; exact Rj.rj_Om1_lt_E) hE.le
  conv_lhs => rw [← Rj.rj_Om1_opow, ← hE]
  rw [← opow_add, hab, hE]

/-- **The level `ε_{Ω₁+1}` is new**: `Γ = Ω₁·ε_{Ω₁+1} = ε_{Ω₁+1}` has `1 ≤ M`, `Γ < B₂` and `Γ ≥ ε_{Ω₁+1}` (outside
the range of `R2.urVt_tr2`, `R2.ukVt_tr3`). -/
theorem uv_new_level : 1 ≤ Gg.ggE ∧ Om1 * Gg.ggE < Uc.ucB ∧ Gg.ggE ≤ Om1 * Gg.ggE := by
  rw [uv_Om1_mul_E]
  exact ⟨Order.one_le_iff_pos.2 (Rj.rj_Om1_pos.trans Rj.rj_Om1_lt_E), uv_E_lt_B, le_rfl⟩

/-- **The data of the new level `ε_{Ω₁+1}`** is `1` (`Tf.tfDat_E`), so at every base `α > 1` it falls in the subcase
`Γ^* < α` of `R2.uvVt_trL`. -/
theorem uvDat_E : Uc.ucDat (Om1 * Gg.ggE) = 1 := by
  rw [uv_Om1_mul_E, Uc.ucDat_lt_X (Tf.tf_E_lt_BG.trans Tl.tl_BG_lt_X), Tl.tlDat_eq_tf _ Tf.tf_E_lt_BG, Tf.tfDat_E]

end Googology.Trans.PoR.InaccPsi.R2.Uv
