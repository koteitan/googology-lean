import Googology.Trans.PoR.InaccPsi.R2.TeNu

/-!
# The codes `≥ P'` below `L(ω+1)`: exactly the points `L(k)` (`k < ω`) and `L(ω)`

`P' = ψ_{Ω₂}(Ω_ω·2)`, `L(ξ) = P(Ω_ω + P'·ξ)`.  ENUM-REACH ([`Cd.CdRange`]) is stated for codes `< P'`.  Here the
restarts of `[B₀, L(ω+1))` that it leaves out are listed:

* `teCode_mid` (**every restart strictly between `L(ξ)` and `L(ξ+1)` has code `< P'`**, for every `ξ`: its name
  lies in `(Ω_ω + P'·ξ, Ω_ω + P'·ξ + P')` and `ω^{P'} = P'` divides `Ω_ω + P'·ξ`; this is `Se.seCode_mid` for
  every `ξ`, in particular `ξ = 0` and `ξ = ω`);
* `teCode_hi_iff` (**for a restart `λ ≠ 0` with `ρ_λ < L(ω+1)`: `P' ≤ m_λ` iff `ρ_λ = L(k)` for some `k < ω` or
  `ρ_λ = L(ω)`**; the codes there are `P'` and `P' + 1`), `teRange_iff` (**a restart `λ ≥ B₀` with
  `ρ_λ < L(ω+1)` is in the range of ENUM-REACH iff it is none of the `L(k)`, `L(ω)`**);
* `teHi_mem` (the indices `L(k)` and `L(ω)` are restarts `≥ B₀` below `L(ω+1)`).

So "ENUM-REACH for the codes `≥ P'`" on `[B₀, L(ω+1))` is ENUM-REACH at the `ω + 1` points `L(k)`, `L(ω)` and
nothing else (`Te.TeEnumHi`, next module).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Te

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm

variable {S : InaccSeq.{0}}

/-- **Every restart strictly between `L(ξ)` and `L(ξ+1)` has code `< P'`.** -/
theorem teCode_mid {ξ l : Ordinal.{0}} (hl0 : l ≠ 0) (h1 : Nc.ncL S ξ < upsilon l)
    (h2 : upsilon l < Nc.ncL S (ξ + 1)) : cdCode S l < Nc.ncPp S := by
  have hPE : ω ^ Nc.ncPp S = Nc.ncPp S := Lw.lw_Pp_opow S
  have hWE : ω ^ Om ω = Om ω := Low.opow_eq_self_of_SC (SC_Om omega0_ne_zero)
  have hc1 : Nc.ncL S ξ = Pv S (Om ω + Nc.ncPp S * ξ) := Lw.lw_L_eq S _
  have hc2 : Nc.ncL S (ξ + 1) = Pv S (Om ω + Nc.ncPp S * ξ + Nc.ncPp S) := by
    rw [Lw.lw_L_eq S, mul_add_one, add_assoc]
  obtain ⟨hg, hι, hlt, hpv⟩ := cdEta_pv_spec hl0 (h2.trans_eq hc2)
  have hgt : Om ω + Nc.ncPp S * ξ < cdEta S l := by
    by_contra hle
    push Not at hle
    rcases hle.lt_or_eq with h | h
    · have h3 := upsilon_normal.strictMono (cd_iota_lt_of_good hg h)
      rw [hι, ups_iota S] at h3
      exact absurd (h3.trans_eq hc1.symm) (not_lt.2 h1.le)
    · rw [h, ← hc1] at hpv
      exact absurd hpv (ne_of_lt h1)
  have hdvd : ω ^ Nc.ncPp S ∣ Om ω + Nc.ncPp S * ξ := by
    refine dvd_add ?_ ?_
    · conv_rhs => rw [← hWE]
      exact opow_dvd_opow ω (cdPp_lt_Om_omega S).le
    · rw [hPE]; exact dvd_mul_right _ _
  have hlt' : cdEta S l < Om ω + Nc.ncPp S * ξ + ω ^ Nc.ncPp S := by
    rw [hPE]; exact hlt
  exact (cdCodeOf_le_exp S _).trans_lt (cdWin hdvd hgt hlt').1

/-- The indices `L(k)` and `L(ω)` are restart indices. -/
theorem teRst_L (k : ℕ) : IsRestartIdx (Nc.ncL S (k : Ordinal.{0})) := by
  cases k with
  | zero => simpa using (Ls.lsM_named (S := S)).2.2.2.2.1
  | succ n => exact (Ls.lsL_named (S := S) n).2.2.2.2.1

theorem teRst_Lw : IsRestartIdx (Nc.ncL S ω) := (Ra.raLw_named (S := S)).2.2.2.2.1

theorem teB0_le_L (k : ℕ) : cdB0 ≤ Nc.ncL S (k : Ordinal.{0}) :=
  (Fp.fpB0_lt_M' (S := S)).le.trans (Pp.ppL_mono zero_le)

theorem teB0_le_Lw : cdB0 ≤ Nc.ncL S ω := (Fp.fpB0_lt_M' (S := S)).le.trans (Pp.ppL_mono zero_le)

/-- **The indices `L(k)`, `L(ω)` are restarts `≥ B₀` with `ρ < L(ω+1)` and code `≥ P'`.** -/
theorem teHi_mem (k : ℕ) :
    (IsRestartIdx (Nc.ncL S (k : Ordinal.{0})) ∧ cdB0 ≤ Nc.ncL S (k : Ordinal.{0}) ∧
      upsilon (Nc.ncL S (k : Ordinal.{0})) < Nc.ncL S (ω + 1) ∧
      cdCode S (Nc.ncL S (k : Ordinal.{0})) = Nc.ncPp S) ∧
    (IsRestartIdx (Nc.ncL S ω) ∧ cdB0 ≤ Nc.ncL S ω ∧ upsilon (Nc.ncL S ω) < Nc.ncL S (ω + 1) ∧
      cdCode S (Nc.ncL S ω) = Nc.ncPp S + 1) := by
  refine ⟨⟨teRst_L k, teB0_le_L k, ?_, ?_⟩, teRst_Lw, teB0_le_Lw, ?_, cdCode_Lω Rc.rcUps_Lw⟩
  · rw [teUps_L]; exact (teL_lt_omega k).trans (Qq.qqL_lt_succ S)
  · cases k with
    | zero => exact (cdCode_L0 (by simpa using teUps_L (S := S) 0)).2
    | succ n => exact cdCode_L n (teUps_L (n + 1))
  · rw [Rc.rcUps_Lw]; exact Qq.qqL_lt_succ S

/-- **The codes `≥ P'` below `L(ω+1)` are those of the `L(k)` and of `L(ω)`.** -/
theorem teCode_hi_iff {l : Ordinal.{0}} (hl0 : l ≠ 0) (hlt : upsilon l < Nc.ncL S (ω + 1)) :
    Nc.ncPp S ≤ cdCode S l ↔ (∃ k : ℕ, upsilon l = Nc.ncL S (k : Ordinal.{0})) ∨ upsilon l = Nc.ncL S ω := by
  constructor
  · intro hP
    by_contra hno
    push Not at hno
    obtain ⟨hk, hw⟩ := hno
    rcases lt_or_ge (upsilon l) (cdMstar S) with h0 | h0
    · exact absurd (cdCode_lt_level1 hl0 h0) (not_lt.2 hP)
    rcases lt_or_gt_of_ne hw with h1 | h1
    · exact absurd (cdCode_lt_level2 hl0 h0 h1 hk) (not_lt.2 hP)
    · exact absurd (teCode_mid hl0 h1 hlt) (not_lt.2 hP)
  · rintro (⟨k, hk⟩ | hw)
    · have hl : l = Nc.ncL S (k : Ordinal.{0}) :=
        upsilon_normal.strictMono.injective (hk.trans (teUps_L k).symm)
      subst hl
      exact ((teHi_mem k).1.2.2.2).ge
    · have hl : l = Nc.ncL S ω := Rc.rcIdx_Lw hw
      subst hl
      rw [(teHi_mem 0).2.2.2.2]
      exact le_self_add

/-- **A restart `λ ≥ B₀` with `ρ_λ < L(ω+1)` is in the range of ENUM-REACH iff it is none of the `L(k)`, `L(ω)`.** -/
theorem teRange_iff {l : Ordinal.{0}} (hl : IsRestartIdx l) (hB : cdB0 ≤ l)
    (hlt : upsilon l < Nc.ncL S (ω + 1)) :
    CdRange S l ↔ (∀ k : ℕ, upsilon l ≠ Nc.ncL S (k : Ordinal.{0})) ∧ upsilon l ≠ Nc.ncL S ω := by
  have hiff := teCode_hi_iff (S := S) hl.1 hlt
  constructor
  · rintro ⟨-, -, -, hc⟩
    refine ⟨fun k hk => ?_, fun hw => ?_⟩
    · exact absurd (hiff.2 (Or.inl ⟨k, hk⟩)) (not_le.2 hc)
    · exact absurd (hiff.2 (Or.inr hw)) (not_le.2 hc)
  · rintro ⟨hk, hw⟩
    refine ⟨hl, hB, hlt, not_le.1 fun hP => ?_⟩
    rcases hiff.1 hP with ⟨k, h⟩ | h
    · exact hk k h
    · exact hw h

end Googology.Trans.PoR.InaccPsi.R2.Te
