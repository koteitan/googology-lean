import Googology.Trans.PoR.InaccPsi.R2.NcCPB
import Googology.Trans.PoR.InaccPsi.R2.BtN
import Googology.Trans.PoR.InaccPsi.R2.LfNuC
import Googology.Trans.PoR.InaccPsi.R2.BtF

/-!
# CPB at named points: an InaccPsi upper bound for `ν_C` from (P) and (Q) at one named pair

`θ = ψ_{Ω₂}(Ω_ω)`, `A_η = Ω_ω + θ·η`, `ψ = ψ_{Ω₁}`; Theorem GEN (`ups_iota`) gives
`υ_{ι(η)} = ψ(A_η)` for every `η`.  `P' = ψ_{Ω₂}(Ω_ω·2)` (`ncPp`), `L(ξ) = ψ(Ω_ω·2 + P'·ξ)` (`ncL`).

* `ncPsi_upsPt`, `ncPsi_indec`: `ψ(A_η)` is a nonzero `υ`-point, hence indecomposable;
* `ncTau_ups_iff`: `υ_ι` is a `τ`-point iff `ι = μ + ω·(j+1)` with `μ = 0` or a restart index;
* `ncQ_R1_fails`: at a nonzero `υ`-point `u`, `u ≤₁ g` holds in `R₁⁺` for every `g ≥ u`, so (Q) never
  follows from `R₁⁺` through `R₂^C ≤₁ ⊆ R₁⁺ ≤₁` (`inc1`);
* `ncUpper_named` (**CPB at named points**): `η₁ ≤ η₂`, `ψ(A_{η₁})` not a `τ`-point, (P) and (Q) at
  `(ψ(A_{η₁}), ψ(A_{η₂}))`  ⟹  `ν_C ≤ ψ(A_{η₂})` and `ν_C = ψ(A_η)` for some `η ≤ η₂`;
* `ncL_eq_A`, `ncL_succ_omega`: `L(ξ) = ψ(A_{Ω_ω + P'·ξ})`, `L(ω+1) = ψ(Ω_ω·2 + ω^{P'+1} + P')`;
* `ncUpper_L` (**the named pair `(L(ω), L(ω+1))`**): if `L(ω)` is not a `τ`-point and (P), (Q) hold at
  `(L(ω), L(ω+1))`, then `ν_C ≤ L(ω+1) = ψ(Ω_ω·2 + ω^{P'+1} + P')` and `ν_C` has a name `ψ(A_η)`,
  `η ≤ Ω_ω + P'·(ω+1)`;
* `ncBounds_L`: with the lower bound of `BtF`: `Φ₁ = ψ(Ω_ω + θ·Ω₁·Φ₁) < ν_C ≤ L(ω+1)` under the same
  hypotheses.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Nc

open Ordinal Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt

/-- `ψ_{Ω₁}(Ω_ω + θ·η)` is a nonzero `υ`-point. -/
theorem ncPsi_upsPt (S : InaccSeq.{0}) (η : Ordinal.{0}) :
    UpsPt (S.psi (ConjT.Aη S η) (Om 1)) := by
  rw [← ups_iota S η]
  exact upsPt_upsilon (lt_of_lt_of_le zero_lt_one (one_le_iota η))

theorem ncPsi_indec (S : InaccSeq.{0}) (η : Ordinal.{0}) :
    Indec (S.psi (ConjT.Aη S η) (Om 1)) :=
  indec_of_upsPt (ncPsi_upsPt S η)

/-- `υ_ι` is a `τ`-point iff `ι = μ + ω·(j+1)` with `μ = 0` or `μ` a restart index. -/
theorem ncTau_ups_iff (ι : Ordinal.{0}) :
    NcTauPt (upsilon ι) ↔ ∃ μ, ∃ j : ℕ, (μ = 0 ∨ IsRestartIdx μ) ∧
      ι = μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) := by
  constructor
  · rintro ⟨μ, j, hμ, e⟩
    exact ⟨μ, j, hμ, upsilon_normal.strictMono.injective e⟩
  · rintro ⟨μ, j, hμ, rfl⟩
    exact ⟨μ, j, hμ, rfl⟩

/-- At a nonzero `υ`-point `u`, `u ≤₁ g` in `R₁⁺` for every `g ≥ u`: (Q) at `u` is not a consequence of
`R₁⁺`. -/
theorem ncQ_R1_fails {u : Ordinal.{0}} (hu : UpsPt u) {g : Ordinal.{0}} (hg : u ≤ g) : le1R u g :=
  hu.2 g hg

/-- `ν_C` has a name as soon as it lies below a named point. -/
theorem ncNamed_of_le (S : InaccSeq.{0}) {η₂ : Ordinal.{0}}
    (hν : nuC ≤ S.psi (ConjT.Aη S η₂) (Om 1)) :
    ∃ η ≤ η₂, nuC = S.psi (Om ω + ConjT.th S * η) (Om 1) := by
  obtain ⟨ξ, hξ, e⟩ := nuC_restart
  have h1 : 1 ≤ ξ := Order.one_le_iff_ne_zero.2 hξ.1
  rw [e] at hν ⊢
  exact ups_below_named S h1 hν

/-- **A realized pair under a named point**: `c <₂ d ≤ ψ(A_η₂)`, `c` not a `τ`-point  ⟹
`ν_C ≤ ψ(A_η₂)` and `ν_C = ψ(A_η)` for some `η ≤ η₂`. -/
theorem ncUpper_pair_named (S : InaccSeq.{0}) {η₂ c d : Ordinal.{0}} (hcd : c < d) (h2 : le2 c d)
    (hτ : ¬ NcTauPt c) (hd : d ≤ S.psi (ConjT.Aη S η₂) (Om 1)) :
    nuC ≤ S.psi (ConjT.Aη S η₂) (Om 1) ∧
      ∃ η ≤ η₂, nuC = S.psi (Om ω + ConjT.th S * η) (Om 1) := by
  have hν := (ncPair_bound hcd h2 hτ).trans hd
  exact ⟨hν, ncNamed_of_le S hν⟩

/-- **CPB at named points.** -/
theorem ncUpper_named (S : InaccSeq.{0}) {η₁ η₂ : Ordinal.{0}} (h12 : η₁ ≤ η₂)
    (hτ : ¬ NcTauPt (S.psi (ConjT.Aη S η₁) (Om 1)))
    (hP : NcCofPred (S.psi (ConjT.Aη S η₁) (Om 1)) (S.psi (ConjT.Aη S η₂) (Om 1)))
    (hQ : ¬ le1 (S.psi (ConjT.Aη S η₁) (Om 1)) (S.psi (ConjT.Aη S η₂) (Om 1) + 1)) :
    nuC ≤ S.psi (ConjT.Aη S η₂) (Om 1) ∧
      ∃ η ≤ η₂, nuC = S.psi (Om ω + ConjT.th S * η) (Om 1) := by
  have hub : S.psi (ConjT.Aη S η₁) (Om 1) ≤ S.psi (ConjT.Aη S η₂) (Om 1) :=
    (psi_mono Low.InR_Om_one (ConjT.A_mono S h12)).1
  have hν := ncCpb (ncPsi_indec S η₁) hτ hub hP hQ
  exact ⟨hν, ncNamed_of_le S hν⟩

/-- `P' = ψ_{Ω₂}(Ω_ω·2)`. -/
noncomputable def ncPp (S : InaccSeq.{0}) : Ordinal.{0} := S.psi (Om ω + Om ω) (Om (1 + 1))

/-- `L(ξ) = ψ_{Ω₁}(Ω_ω·2 + P'·ξ)`. -/
noncomputable def ncL (S : InaccSeq.{0}) (ξ : Ordinal.{0}) : Ordinal.{0} :=
  S.psi (Om ω + Om ω + ncPp S * ξ) (Om 1)

theorem ncPp_SC (S : InaccSeq.{0}) : SC (ncPp S) := SC_psi (InR_Om_succ 1) _

theorem ncTh_lt_Pp (S : InaccSeq.{0}) : ConjT.th S < ncPp S := by
  have hω : Om (ω : Ordinal.{0}) < Om ω + Om ω :=
    lt_add_of_pos_right _ (Om_pos omega0_ne_zero)
  exact lt_psi_of_mem (InR_Om_succ 1) (ConjT.th_mem S hω) (psi_lt (InR_Om_succ 1) _)

/-- `θ·P' = P'`. -/
theorem ncTh_mul_Pp (S : InaccSeq.{0}) : ConjT.th S * ncPp S = ncPp S := by
  have e := Low.opow_eq_self_of_SC (ncPp_SC S)
  conv_lhs => rw [← e]
  rw [th_mul_opow, (ncPp_SC S).isPrincipal.add_eq_right (ncTh_lt_Pp S), e]

/-- `L(ξ) = ψ_{Ω₁}(A_{Ω_ω + P'·ξ})`: `L(ξ)` is a GEN name. -/
theorem ncL_eq_A (S : InaccSeq.{0}) (ξ : Ordinal.{0}) :
    ncL S ξ = S.psi (ConjT.Aη S (Om ω + ncPp S * ξ)) (Om 1) := by
  unfold ncL ConjT.Aη
  rw [mul_add, th_mul_Om_omega, ← mul_assoc, ncTh_mul_Pp, add_assoc]

/-- `L(ω+1) = ψ_{Ω₁}(Ω_ω·2 + ω^{P'+1} + P')`. -/
theorem ncL_succ_omega (S : InaccSeq.{0}) :
    ncL S (ω + 1) = S.psi (Om ω + Om ω + ω ^ (ncPp S + 1) + ncPp S) (Om 1) := by
  have e := Low.opow_eq_self_of_SC (ncPp_SC S)
  have hw : ncPp S * ω = ω ^ (ncPp S + 1) := by rw [opow_add, opow_one, e]
  unfold ncL
  rw [mul_add_one, hw, ← add_assoc]

/-- **The named pair `(L(ω), L(ω+1))`.**  If `L(ω)` is not a `τ`-point and (P), (Q) hold at
`(L(ω), L(ω+1))`, then `ν_C ≤ L(ω+1) = ψ_{Ω₁}(Ω_ω·2 + ω^{P'+1} + P')` and `ν_C = ψ_{Ω₁}(Ω_ω + θ·η)`
for some `η ≤ Ω_ω + P'·(ω+1)`. -/
theorem ncUpper_L (S : InaccSeq.{0}) (hτ : ¬ NcTauPt (ncL S ω))
    (hP : NcCofPred (ncL S ω) (ncL S (ω + 1))) (hQ : ¬ le1 (ncL S ω) (ncL S (ω + 1) + 1)) :
    nuC ≤ S.psi (Om ω + Om ω + ω ^ (ncPp S + 1) + ncPp S) (Om 1) ∧
      ∃ η ≤ Om ω + ncPp S * (ω + 1), nuC = S.psi (Om ω + ConjT.th S * η) (Om 1) := by
  have h12 : Om ω + ncPp S * ω ≤ Om ω + ncPp S * (ω + 1) :=
    by gcongr; exact le_self_add
  rw [ncL_eq_A] at hτ hP hQ
  rw [ncL_eq_A] at hP hQ
  have := ncUpper_named S h12 hτ hP hQ
  rw [← ncL_eq_A, ncL_succ_omega] at this
  exact this

/-- With the lower bound of `BtF`: `Φ₁ = ψ_{Ω₁}(Ω_ω + θ·Ω₁·Φ₁) < ν_C ≤ L(ω+1)`, given the
hypotheses of `ncUpper_L`. -/
theorem ncBounds_L (S : InaccSeq.{0}) (hτ : ¬ NcTauPt (ncL S ω))
    (hP : NcCofPred (ncL S ω) (ncL S (ω + 1))) (hQ : ¬ le1 (ncL S ω) (ncL S (ω + 1) + 1)) :
    S.psi (Om ω + ConjT.th S * (Om 1 * Phi1)) (Om 1) < nuC ∧
      nuC ≤ S.psi (Om ω + Om ω + ω ^ (ncPp S + 1) + ncPp S) (Om 1) := by
  refine ⟨?_, (ncUpper_L S hτ hP hQ).1⟩
  obtain ⟨L, ξ, -, -, -, -, e, h1, h2, h3, h4, -⟩ := rhoL_psi_bound S
  rw [e]
  exact (((h1.trans h2).trans_le h3).trans h4)

end Googology.Trans.PoR.InaccPsi.R2.Nc
