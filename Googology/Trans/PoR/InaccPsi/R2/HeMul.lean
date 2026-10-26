import Googology.Trans.PoR.InaccPsi.R2.HdRho

/-!
# HeMul: THE EXPONENT OF A POWER IN `Tᵖ[σ]`, AND `π(u·c) = π(u)·π(c)` FOR EVERY `c ∈ Tᵖ[σ] ∩ Ω₁`

`Hc.hc_pi_mulL` gives `π(u·c) = π(u)·c` for constants `c < σ`, `Hd.hd_pi_mulR` the case `c = ρ`.  Here, for an
`ε`-number `u ∈ Tᵖ[σ] ∩ Ω₁` (`υ`-points `σ < ρ`), `π(u·c) = π(u)·π(c)` for every `c ∈ Tᵖ[σ] ∩ Ω₁`, by induction on
the Cantor normal form `c = ω^L·k + r` (`k < ω`, `r < ω^L`).  Two facts are used:

* the CNF prefix: `ω^L` and `r` are again in `Tᵖ[σ]` (their additive components are components of `c`,
  `Si.siTB_of_comps`, from the cited `Par_comps_eq`);
* the exponent: `ω^j ∈ Tᵖ[σ]` ⇒ `j ∈ Tᵖ[σ]` (`he_TB_exp`): `π(ω^j)` is indecomposable (`down_indec`), say `ω^{j'}`;
  `j' ∈ T^σ` (`T^σ ∩ Ω₁` is an initial segment, `T_next`), so `j' = π(k)` for some `k ∈ Tᵖ[σ] ∩ Ω₁` (`π` is onto),
  and `π(ω^k) = ω^{π(k)} = π(ω^j)` (`pi_opowZ`) gives `k = j` (`π` is 1-1).

* `he_comps_opow`, `he_TB_exp` (**THE EXPONENT OF A POWER IN `Tᵖ[σ]`**), `he_TB_cnf` (**THE CNF PREFIX**),
  `he_pi_mul` (**`π(u·c) = π(u)·π(c)`**).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.He

open Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Hd Googology.Trans.PoR.InaccPsi.R2.Gl
open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2

/-- The additive components of `ω^L`: `[ω^L]`. -/
theorem he_comps_opow (L : Ordinal.{0}) : comps (ω ^ L) = [ω ^ L] := by
  rw [Si.si_comps_cons (opow_pos L omega0_pos).ne', log_opow one_lt_omega0, Ordinal.mod_self, Si.si_comps_zero]

/-- **THE EXPONENT OF A POWER IN `Tᵖ[σ]`**: `ω^j ∈ Tᵖ[σ] ∩ Ω₁` ⇒ `j ∈ Tᵖ[σ]` (`υ`-points `σ < ρ`). -/
theorem he_TB_exp {σ ρ j : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) (hj : ω ^ j ∈ TB ρ σ)
    (hj1 : ω ^ j < Om1) : j ∈ TB ρ σ := by
  have hσ1 : σ < Om1 := hB.2.2.1.trans hB.2.2.2
  obtain ⟨m, -, -, -, hTm, -⟩ := T_next (Or.inr hB.1) hσ1
  have hI := down_indec hB hj hj1 (indec_opow j)
  obtain ⟨hne, hpa⟩ := indec_iff.1 hI
  obtain ⟨j', hj'⟩ : ∃ j' : Ordinal.{0}, ω ^ j' = pi σ ρ (ω ^ j) := by
    rcases (isPrincipal_add_iff_zero_or_omega0_opow).1 hpa with h0 | ⟨j', hj'⟩
    · exact absurd h0 hne
    · exact ⟨j', hj'⟩
  have hy1 : pi σ ρ (ω ^ j) < Om1 := vz_pi_lt_Om1 hB hj hj1
  have hyT : pi σ ρ (ω ^ j) ∈ Tset σ := (pi_bijOn hB).1.mapsTo hj
  have hj'le : j' ≤ pi σ ρ (ω ^ j) := by rw [← hj']; exact right_le_opow j' one_lt_omega0
  have hj'1 : j' < Om1 := hj'le.trans_lt hy1
  have hj'T : j' ∈ Tset σ := (hTm j' hj'1).2 (hj'le.trans_lt ((hTm _ hy1).1 hyT))
  obtain ⟨k, hkTB, hkj⟩ := (pi_bijOn hB).1.surjOn hj'T
  have hk1 : k < Om1 := by
    by_contra hge
    push Not at hge
    have h' := ((pi_bijOn hB).2.le_iff_le (pi_Om1 hB).1 hkTB).2 hge
    rw [(pi_Om1 hB).2, hkj] at h'
    exact absurd hj'1 (not_lt.2 h')
  obtain ⟨hwTB, hwπ⟩ := pi_opowZ hσ hρ hB hkTB hk1
  rw [hkj, hj'] at hwπ
  have e : ω ^ k = ω ^ j := (pi_bijOn hB).1.injOn hwTB hj hwπ
  rw [← opow_inj e]
  exact hkTB

/-- **THE CNF PREFIX**: for `c ∈ Tᵖ[σ] ∩ Ω₁`, `c ≠ 0`, the leading power `ω^{log c}`, its exponent and the remainder
`c mod ω^{log c}` are in `Tᵖ[σ]`. -/
theorem he_TB_cnf {σ ρ c : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) (hc : c ∈ TB ρ σ)
    (hc1 : c < Om1) (hc0 : c ≠ 0) :
    ω ^ log ω c ∈ TB ρ σ ∧ log ω c ∈ TB ρ σ ∧ c % ω ^ log ω c ∈ TB ρ σ := by
  have hLc : ω ^ log ω c ≤ c := opow_log_le_self ω hc0
  have hrc : c % ω ^ log ω c ≤ c := (Ordinal.mod_lt c (opow_pos _ omega0_pos).ne').le.trans hLc
  rcases lt_or_ge c ρ with hcρ | hρc
  · have hcσ : c < σ := (TB_inter_lt hB hcρ).1 hc
    have hL : log ω c ≤ ω ^ log ω c := right_le_opow _ one_lt_omega0
    exact ⟨mem_TB_of_lt hB (hLc.trans_lt hcσ), mem_TB_of_lt hB ((hL.trans hLc).trans_lt hcσ),
      mem_TB_of_lt hB (hrc.trans_lt hcσ)⟩
  have hcomps := Si.si_comps_cons hc0
  have hwTB : ω ^ log ω c ∈ TB ρ σ := Si.siTB_of_comps hB hc hρc (fun p hp => by
    rw [he_comps_opow, List.mem_singleton] at hp
    rw [hcomps, hp]; exact List.mem_cons_self ..)
  refine ⟨hwTB, he_TB_exp hσ hρ hB hwTB (hLc.trans_lt hc1), ?_⟩
  exact Si.siTB_of_comps hB hc hρc (fun p hp => by rw [hcomps]; exact List.mem_cons_of_mem _ hp)

/-- **`π(u·c) = π(u)·π(c)`** for an `ε`-number `u ∈ Tᵖ[σ] ∩ Ω₁` and every `c ∈ Tᵖ[σ] ∩ Ω₁` (`υ`-points `σ < ρ`),
with `u·c ∈ Tᵖ[σ]`. -/
theorem he_pi_mul {σ ρ u : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) (hu : u ∈ TB ρ σ)
    (hu1 : u < Om1) (huE : InE u) :
    ∀ c, c ∈ TB ρ σ → c < Om1 → u * c ∈ TB ρ σ ∧ pi σ ρ (u * c) = pi σ ρ u * pi σ ρ c := by
  have hπuE : InE (pi σ ρ u) := by
    obtain ⟨-, hp⟩ := pi_opowZ hσ hρ hB hu hu1
    rw [show ω ^ u = u from huE] at hp
    exact hp.symm
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hc1
  rcases lt_or_ge c ρ with hcρ | hρc
  · have hcσ : c < σ := (TB_inter_lt hB hcρ).1 hc
    rw [pi_lt hB hcσ]
    exact hc_pi_mulL hσ hρ hB hu hu1 huE c hcσ
  have hc0 : c ≠ 0 := (hB.2.1.pos.trans_le hρc).ne'
  obtain ⟨hwTB, hLTB, hrTB⟩ := he_TB_cnf hσ hρ hB hc hc1 hc0
  have hω0 : ω ^ log ω c ≠ 0 := (opow_pos _ omega0_pos).ne'
  have hLc : ω ^ log ω c ≤ c := opow_log_le_self ω hc0
  have hrc : c % ω ^ log ω c < c := (Ordinal.mod_lt c hω0).trans_le hLc
  have hL1 : log ω c < Om1 := ((right_le_opow _ one_lt_omega0).trans hLc).trans_lt hc1
  obtain ⟨k, hk⟩ := lt_omega0.1 (div_opow_log_lt c one_lt_omega0)
  have hdec : c = ω ^ log ω c * (k : Ordinal.{0}) + c % ω ^ log ω c := by
    rw [← hk]; exact (Ordinal.div_add_mod c (ω ^ log ω c)).symm
  -- `π(c) = ω^{π L}·k + π(r)`
  obtain ⟨-, hwπ⟩ := pi_opowZ hσ hρ hB hLTB hL1
  obtain ⟨hwk, hwkπ⟩ := pi_mul_nat hB hwTB hwπ k
  obtain ⟨-, hcπ⟩ := pi_add hB hwk hrTB
  rw [hwkπ, ← hdec] at hcπ
  -- `u·c = ω^{u+L}·k + u·r`
  obtain ⟨huLTB, huLπ⟩ := pi_add hB hu hLTB
  have huL1 : u + log ω c < Om1 := (inE_indec gl_Om1_E).add_lt hu1 hL1
  obtain ⟨hoTB, hoπ⟩ := pi_opowZ hσ hρ hB huLTB huL1
  rw [huLπ] at hoπ
  obtain ⟨hmk, hmkπ⟩ := pi_mul_nat hB hoTB hoπ k
  obtain ⟨hr1, hr2⟩ := IH _ hrc hrTB (hrc.trans hc1)
  obtain ⟨hs1, hs2⟩ := pi_add hB hmk hr1
  have e1 : ω ^ (u + log ω c) = u * ω ^ log ω c := by rw [opow_add, show ω ^ u = u from huE]
  have e2 : ω ^ (pi σ ρ u + pi σ ρ (log ω c)) = pi σ ρ u * ω ^ pi σ ρ (log ω c) := by
    rw [opow_add, show ω ^ pi σ ρ u = pi σ ρ u from hπuE]
  have euc : ω ^ (u + log ω c) * (k : Ordinal.{0}) + u * (c % ω ^ log ω c) = u * c := by
    conv_rhs => rw [hdec]
    rw [mul_add, e1, mul_assoc]
  rw [euc] at hs1 hs2
  refine ⟨hs1, ?_⟩
  rw [hs2, hmkπ, hr2, e2, hcπ, mul_add, mul_assoc]

end Googology.Trans.PoR.InaccPsi.R2.He
