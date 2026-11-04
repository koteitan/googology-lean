import Googology.Trans.PoR.InaccPsi.R2.ZfSC
import Googology.Trans.PoR.InaccPsi.R2.CitedZf

/-!
# `Dl τ n` is strongly critical for `n ≥ 2` (`Za.ZaDlSC`), and every point of `Tᵗ ∩ Ω₁` lies below one

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`Dl τ n = ϑ₀(⋯ϑₙ(0)⋯)` over `τ`.  The cited axiom `R2.zfDl_vt` reads `Dl τ n` (`n ≥ 2`) as `ϑᵗ(Δ)` with `Δ ∈ Tᵗ ∩
Ω₂`, `Ω₁·Ω₁ ≤ Δ`; writing `Δ = Ω₁·M + η` (`M = Δ / Ω₁ ≥ Ω₁`, `η = Δ mod Ω₁`), `Zf.zf_vt_SC` gives strong criticality.

* `zfDlSC` (**`Za.ZaDlSC`**: the statement of the skeleton leaf `skDlSC`, now a theorem from `R2.zfDl_vt`);
* `zf_Dl_lt_succ`, `zf_Dl_mono` (`Dl τ n < Dl τ (n+1)`, from `R2.ht_spec`, `R2.Dl_spec`), `zf_SC_above` (**every
  `x ∈ Tᵗ ∩ Ω₁` lies below a strongly critical `q = Dl τ N ∈ Tᵗ ∩ Ω₁`**).

No new axiom (uses `R2.zfDl_vt` of `R2.CitedZf`), no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zf

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2

/-- **`Za.ZaDlSC`**: `Dl τ n` is strongly critical for every `τ ∈ E ∩ Ω₁` and `n ≥ 2`. -/
theorem zfDlSC (S : InaccSeq.{0}) : Za.ZaDlSC := by
  intro τ hτ hτ1 n hn
  obtain ⟨Δ, hT, hΔ, hΔ2, e⟩ := zfDl_vt hτ hτ1 hn
  have hO0 : (Om1 : Ordinal.{0}) ≠ 0 := Rj.rj_Om1_pos.ne'
  have hsplit : Om1 * (Δ / Om1) + Δ % Om1 = Δ := Ordinal.div_add_mod Δ Om1
  have hM1 : Om1 ≤ Δ / Om1 := (Ordinal.le_div hO0).2 hΔ
  have hη1 : Δ % Om1 < Om1 := Ordinal.mod_lt Δ hO0
  rw [e, ← hsplit]
  rw [← hsplit] at hT hΔ2
  exact zf_vt_SC S hτ hτ1 hM1 hη1 hT hΔ2

/-- `Dl τ n < Dl τ (n+1)`. -/
theorem zf_Dl_lt_succ {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (n : ℕ) : Dl τ n < Dl τ (n + 1) := by
  obtain ⟨hT, h1, hht⟩ := Dl_spec hτ hτ1 n
  obtain ⟨hex, hEq⟩ := ht_spec hτ hτ1 hT h1
  have hne : {k : ℕ | Dl τ n < Dl τ k}.Nonempty := hex
  have hmem := Nat.sInf_mem hne
  rw [← hEq, hht] at hmem
  exact hmem

/-- `Dl τ` is strictly increasing. -/
theorem zf_Dl_mono {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) {n m : ℕ} (h : n ≤ m) : Dl τ n ≤ Dl τ m := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (zf_Dl_lt_succ hτ hτ1 _).le

/-- **Every `x ∈ Tᵗ ∩ Ω₁` lies below a strongly critical `q = Dl τ N ∈ Tᵗ ∩ Ω₁` (`N ≥ 2`).** -/
theorem zf_SC_above (S : InaccSeq.{0}) {τ x : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hx : x ∈ Tset τ)
    (hx1 : x < Om1) : ∃ q, SC q ∧ q ∈ Tset τ ∧ q < Om1 ∧ x < q := by
  obtain ⟨⟨n, hn⟩, -⟩ := ht_spec hτ hτ1 hx hx1
  refine ⟨Dl τ (max n 2), zfDlSC S τ hτ hτ1 _ (le_max_right n 2), (Dl_spec hτ hτ1 _).1, (Dl_spec hτ hτ1 _).2.1,
    hn.trans_le (zf_Dl_mono hτ hτ1 (le_max_left n 2))⟩

end Googology.Trans.PoR.InaccPsi.R2.Zf
