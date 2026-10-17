import Googology.Trans.PoR.InaccPsi.R2.LhGen
import Googology.Trans.PoR.InaccPsi.R2.LwName
import Googology.Trans.PoR.InaccPsi.R2.PpIdx

/-!
# The general reach of `R₁⁺` in InaccPsi terms, and the named points

`θ = ψ_{Ω₂}(Ω_ω)`, `P(η) = ψ_{Ω₁}(Ω_ω + θ·η)` (`Nm.Pv`), Theorem GEN (`ups_iota`): `υ_{ι(η)} = P(η)`, and
`ι(η+1) = ι(η) + 1` for good `η` (`iota_good`).  `P' = ψ_{Ω₂}(Ω_ω·2)` (`ncPp`), `L(ξ) = ψ_{Ω₁}(Ω_ω·2 + P'·ξ)`
(`ncL`) `= P(Ω_ω + P'·ξ)` (`lw_L_eq`).  Through the bridge, `R2.LhGen` reads:

* `lhPv_inf` (**every `P(η)` has `R₁⁺`-reach `∞`**): `P(η)` is a `υ`-point (`ncPsi_upsPt`), so
  `P(η) ≤₁ β` for every `β ≥ P(η)` and `lh(P(η))` does not exist;
* `lhL_inf` (**the `R₁⁺`-reach of `L(ξ)` is `∞`**, every `ξ`, in particular `L(n)`, `L(ω)`, `L(ω+1)`);
* `lhL_mono_R1`, `lhL_R1` (**in `R₁⁺`**): `L(ξ) ≤₁ L(ξ')` for `ξ ≤ ξ'`; so `L(n) ≤₁ L(n+1)` (every `n`, also
  `n = 0`), `L(n+1) ≤₁ L(ω)`, `L(ω) ≤₁ L(ω+1)`; `lhCross_R1` (**CROSS-LIM in `R₁⁺`**):
  `L(ξ) ≤₁ P(Ω_ω + P'·ξ + c)` for every `c` (in particular `c = c_k = ψ_{Ω₂}(Ω_ω + Ω_{k+1})`);
* `lhGap_Pv` (**the reach of every point of a named gap**): for good `η` and `P(η) < α < P(η+1)`
  (`P(η+1) = ψ_{Ω₁}(Ω_ω + θ·η + θ)`), `α` is not a `υ`-point and `lh(α)` exists, lies in `[α, P(η+1))`, and is
  `α` (decomposable), `α + logend(α')` (`α = ω^{α'} ∉ E`) or `lhᵗ(α)` with `τ = P(η)` and `α·2 ≤ lhᵗ(α)` (`α ∈ E`);
* `lhGap_L`: the same in the gap `(L(ξ), P(Ω_ω + P'·ξ + 1))` above `L(ξ)` (`ξ < L(ξ)`, e.g. `ξ ≤ ω + 1`), with
  `τ = L(ξ)`.

No new axiom, no new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Lh

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt
  Googology.Trans.PoR.InaccPsi.R2.Nc

/-- **Every `P(η) = ψ_{Ω₁}(Ω_ω + θ·η)` has `R₁⁺`-reach `∞`.** -/
theorem lhPv_inf (S : InaccSeq.{0}) (η : Ordinal.{0}) :
    UpsPt (Nm.Pv S η) ∧ LtInf1 (Nm.Pv S η) ∧ ¬ ∃ r, IsLh1 (Nm.Pv S η) r :=
  ⟨ncPsi_upsPt S η, (ncPsi_upsPt S η).2, lhUps_none (ncPsi_upsPt S η)⟩

/-- **The `R₁⁺`-reach of `L(ξ)` is `∞`** (target (1): `L(n)`, `L(ω)`, `L(ω+1)` and every other `L(ξ)`). -/
theorem lhL_inf (S : InaccSeq.{0}) (ξ : Ordinal.{0}) :
    UpsPt (ncL S ξ) ∧ LtInf1 (ncL S ξ) ∧ ¬ ∃ r, IsLh1 (ncL S ξ) r := by
  rw [Lw.lw_L_eq]; exact lhPv_inf S _

/-- In `R₁⁺`, `L(ξ) ≤₁ L(ξ')` for `ξ ≤ ξ'`. -/
theorem lhL_mono_R1 (S : InaccSeq.{0}) {ξ ξ' : Ordinal.{0}} (h : ξ ≤ ξ') :
    le1R (ncL S ξ) (ncL S ξ') :=
  (lhL_inf S ξ).2.1 _ (Pp.ppL_mono h)

/-- **Target (2) in `R₁⁺`**: `L(n) ≤₁ L(n+1)`, `L(n+1) ≤₁ L(ω)`, `L(ω) ≤₁ L(ω+1)`. -/
theorem lhL_R1 (S : InaccSeq.{0}) :
    (∀ n : ℕ, le1R (ncL S (n : Ordinal.{0})) (ncL S ((n + 1 : ℕ) : Ordinal.{0}))) ∧
    (∀ n : ℕ, le1R (ncL S ((n + 1 : ℕ) : Ordinal.{0})) (ncL S ω)) ∧
    le1R (ncL S ω) (ncL S (ω + 1)) :=
  ⟨fun n => lhL_mono_R1 S (by exact_mod_cast Nat.le_succ n),
    fun n => lhL_mono_R1 S (natCast_lt_omega0 _).le, lhL_mono_R1 S le_self_add⟩

/-- **CROSS-LIM in `R₁⁺`**: `L(ξ) ≤₁ P(Ω_ω + P'·ξ + c)` for every `c`. -/
theorem lhCross_R1 (S : InaccSeq.{0}) (ξ c : Ordinal.{0}) :
    le1R (ncL S ξ) (Nm.Pv S (Om ω + ncPp S * ξ + c)) := by
  refine (lhL_inf S ξ).2.1 _ ?_
  rw [Lw.lw_L_eq]; exact Nm.Pv_mono le_self_add

/-- **The `R₁⁺`-reach of every point of the gap `(P(η), P(η+1))`**, `η` good. -/
theorem lhGap_Pv (S : InaccSeq.{0}) {η a : Ordinal.{0}} (hg : Bt.Good S η)
    (h1 : Nm.Pv S η < a) (h2 : a < Nm.Pv S (η + 1)) :
    ¬ UpsPt a ∧ ∃ r, IsLh1 a r ∧ a ≤ r ∧ r < Nm.Pv S (η + 1) ∧
      ((¬ Indec a ∧ r = a) ∨ (∃ a', a' ≠ 0 ∧ a = ω ^ a' ∧ ¬ InE a ∧ r = a + lg a') ∨
       (InE a ∧ r = lhT (Nm.Pv S η) a ∧ a * 2 ≤ r)) := by
  have hu : upsilon (iota S η) = Nm.Pv S η := ups_iota S η
  have hu1 : upsilon (iota S η + 1) = Nm.Pv S (η + 1) := by
    rw [← iota_good hg]; exact ups_iota S (η + 1)
  have hξ0 : iota S η ≠ 0 := (lt_of_lt_of_le zero_lt_one (one_le_iota η)).ne'
  have hn := upsilon_isNext (iota S η)
  rw [succ_eq_add_one] at hn
  have h1' : upsilon (iota S η) < a := by rw [hu]; exact h1
  have h2' : a < upsilon (iota S η + 1) := by rw [hu1]; exact h2
  have hU : ¬ UpsPt a := not_upsPt_gap hn h1' h2'
  have ha1 : a < Om1 := h2.trans (by rw [Br.Om1_eq]; exact Nm.Pv_lt_Om1 S _)
  obtain ⟨r, hr, har, hr1, hcase⟩ := lhR1_at ha1 hU h1'.le h2'
  refine ⟨hU, r, hr, har, by rw [← hu1]; exact hr1, ?_⟩
  rw [if_neg hξ0, hu] at hcase
  rcases hcase with h | ⟨ha, -⟩ | h | h
  · exact Or.inl h
  · exfalso
    rw [ha] at h1
    exact absurd h1 (not_lt.2 (one_lt_omega0.trans (Lw.lw_omega_lt_SC (Nm.Pv_SC S η))).le)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-- **The `R₁⁺`-reach of every point of the gap above `L(ξ)`** (`ξ < L(ξ)`, e.g. `ξ ≤ ω + 1`): in
`(L(ξ), P(Ω_ω + P'·ξ + 1))`, with `τ = L(ξ)`. -/
theorem lhGap_L (S : InaccSeq.{0}) {ξ a : Ordinal.{0}} (hξ : ξ < ncL S ξ) (h1 : ncL S ξ < a)
    (h2 : a < Nm.Pv S (Om ω + ncPp S * ξ + 1)) :
    ¬ UpsPt a ∧ ∃ r, IsLh1 a r ∧ a ≤ r ∧ r < Nm.Pv S (Om ω + ncPp S * ξ + 1) ∧
      ((¬ Indec a ∧ r = a) ∨ (∃ a', a' ≠ 0 ∧ a = ω ^ a' ∧ ¬ InE a ∧ r = a + lg a') ∨
       (InE a ∧ r = lhT (ncL S ξ) a ∧ a * 2 ≤ r)) := by
  rw [Lw.lw_L_eq] at h1 ⊢
  exact lhGap_Pv S (Lw.lw_good_L hξ) h1 h2

end Googology.Trans.PoR.InaccPsi.R2.Lh
