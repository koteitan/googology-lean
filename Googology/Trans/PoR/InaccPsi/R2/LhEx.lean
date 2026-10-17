import Googology.Trans.PoR.InaccPsi.R2.LhSk
import Googology.Trans.PoR.InaccPsi.R2.CitedVz
import Googology.Trans.PoR.InaccPsi.R2.EvV
import Googology.Trans.PoR.InaccPsi.R2.EpsK

/-!
# Exact values of the `ε`-case: `lh(ε_{τ+1+k}) = ε_{τ+1+k}·2`, and at the named gaps

`eK (k+1) τ = ε_{τ+1+k}` (`R2.EpsK`; `= ϑᵗ(Ω₁ + k)`, `vt_Om1_eq`).  [W07b] Def 4.1 at `α = ϑᵗ(Ω₁ + k)` (repo axioms
`vzLhT_fix` at `n = 1`, `η = 0`, and `lhT_Om1_add` at `η = k ≥ 1`, with `logend(k) = 0`):

* `lhT_eK`: `lhᵗ(ε_{τ+1+k}) = ε_{τ+1+k}·2` for every countable `ε`-number `τ` and `k < ω`;
* `lhEx_Pv` (InaccPsi): for good `η`, `ε_{P(η)+1+k}` lies in the gap `(P(η), P(η+1))`, its `R₁⁺`-reach is
  `ε_{P(η)+1+k}·2`, and so is its `R₂^C`-reach when it lies below `ν_C`;
* `lhEx_L`: the same above `L(ξ)` (`ξ < L(ξ)`): `lh(ε_{L(ξ)+1+k}) = ε_{L(ξ)+1+k}·2`.

No new axiom, no new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Lh

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt
  Googology.Trans.PoR.InaccPsi.R2.Nc

/-- **`lhᵗ(ε_{τ+1+k}) = ε_{τ+1+k}·2`** ([W07b] Def 4.1 through the repo axioms `vzLhT_fix`, `lhT_Om1_add`). -/
theorem lhT_eK {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (k : ℕ) :
    lhT τ (eK (k + 1) τ) = eK (k + 1) τ * 2 := by
  rw [← vt_Om1_eq hτ hτ1 k]
  have hwτ : (ω : Ordinal.{0}) ≤ τ := lhInE_omega_le hτ
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have h := vzLhT_fix (n := 1) hτ hτ1 le_rfl (mem_T_of_le hτ hτ1 zero_le)
      (lt_of_le_of_lt zero_le hτ1) (fun σ hσ => absurd hσ (not_lt.2 zero_le))
    have e1 : Om1 * ((1 : ℕ) : Ordinal.{0}) + 0 = Om1 + ((0 : ℕ) : Ordinal.{0}) := by simp
    have e2 : (((1 + 1 : ℕ) : ℕ) : Ordinal.{0}) = 2 := by norm_num
    rw [e1, e2] at h
    exact h
  · have hkτ : (k : Ordinal.{0}) < τ := lt_of_lt_of_le (natCast_lt_omega0 k) hwτ
    have hk0 : (k : Ordinal.{0}) ≠ 0 := by exact_mod_cast hk.ne'
    have hv0 : vt τ (Om1 + 0) = eK 1 τ := by
      have := vt_Om1_eq hτ hτ1 0
      rwa [Nat.cast_zero] at this
    have hlim : ∃ σ, σ < (k : Ordinal.{0}) ∧ (k : Ordinal.{0}) < vt τ (Om1 + σ) := by
      refine ⟨0, pos_iff_ne_zero.2 hk0, ?_⟩
      rw [hv0]; exact hkτ.trans (eK_lt_succ 0 τ)
    rw [lhT_Om1_add hτ hτ1 (mem_T_of_le hτ hτ1 hkτ.le) (hkτ.trans hτ1) hk0 hlim, lg_nat hk.ne', add_zero]

/-- **InaccPsi form**: for good `η`, `ε_{P(η)+1+k}` lies in `(P(η), P(η+1))`, its `R₁⁺`-reach is
`ε_{P(η)+1+k}·2`, and below `ν_C` this is also its `R₂^C`-reach. -/
theorem lhEx_Pv (S : InaccSeq.{0}) {η : Ordinal.{0}} (hg : Bt.Good S η) (k : ℕ) :
    Nm.Pv S η < eK (k + 1) (Nm.Pv S η) ∧ eK (k + 1) (Nm.Pv S η) < Nm.Pv S (η + 1) ∧
      IsLh1 (eK (k + 1) (Nm.Pv S η)) (eK (k + 1) (Nm.Pv S η) * 2) ∧
      (eK (k + 1) (Nm.Pv S η) < nuC →
        IsReach R2C (eK (k + 1) (Nm.Pv S η)) (eK (k + 1) (Nm.Pv S η) * 2)) := by
  have hU := (lhPv_inf S η).1
  have hU1 := (lhPv_inf S (η + 1)).1
  have hP1 : Nm.Pv S η < Om1 := by rw [Br.Om1_eq]; exact Nm.Pv_lt_Om1 S _
  have h1 : Nm.Pv S η < eK (k + 1) (Nm.Pv S η) := eK_lt (Nat.succ_pos k) _
  have h2 : eK (k + 1) (Nm.Pv S η) < Nm.Pv S (η + 1) :=
    eK_lt_ups hU hP1 (k + 1) _ (Nm.Pv_lt_succ hg) hU1
  obtain ⟨hnU, r, hr, -, -, hcase⟩ := lhGap_Pv S hg h1 h2
  have hE : InE (eK (k + 1) (Nm.Pv S η)) := eK_E_succ k _
  have hrv : r = eK (k + 1) (Nm.Pv S η) * 2 := by
    rcases hcase with ⟨hI, -⟩ | ⟨-, -, -, hnE, -⟩ | ⟨-, hr', -⟩
    · exact absurd (lhInE_indec hE) hI
    · exact absurd hE hnE
    · rw [hr', lhT_eK (upsPt_inE hU) hP1 k]
  rw [hrv] at hr
  exact ⟨h1, h2, hr, fun hC => (lhSk_reach hC hnU).2 hr⟩

/-- **At a named gap**: `lh(ε_{L(ξ)+1+k}) = ε_{L(ξ)+1+k}·2` in `R₁⁺` (`ξ < L(ξ)`), and in `R₂^C` below `ν_C`. -/
theorem lhEx_L (S : InaccSeq.{0}) {ξ : Ordinal.{0}} (hξ : ξ < ncL S ξ) (k : ℕ) :
    ncL S ξ < eK (k + 1) (ncL S ξ) ∧ eK (k + 1) (ncL S ξ) < Nm.Pv S (Om ω + ncPp S * ξ + 1) ∧
      IsLh1 (eK (k + 1) (ncL S ξ)) (eK (k + 1) (ncL S ξ) * 2) ∧
      (eK (k + 1) (ncL S ξ) < nuC →
        IsReach R2C (eK (k + 1) (ncL S ξ)) (eK (k + 1) (ncL S ξ) * 2)) := by
  rw [Lw.lw_L_eq]
  exact lhEx_Pv S (Lw.lw_good_L hξ) k

end Googology.Trans.PoR.InaccPsi.R2.Lh
