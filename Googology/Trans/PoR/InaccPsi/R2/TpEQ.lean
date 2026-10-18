import Googology.Trans.PoR.InaccPsi.R2.TpMove

/-!
# EQ above `L(n+1)`: the restart part from (S1), the code of the image, and the reach equation

`L(ξ) = Nc.ncL S ξ`, `P' = Nc.ncPp S`, `B_n = Bc.bcB S n`, `r(λ) = k_λ(Θ_λ(m_λ))` (`cdR`).

* `tpCode_top` (**every restart strictly between `L(ω)` and `L(ω+1)` has code `< P'`**): its name is
  `η = Ω_ω + P'·ω + η''` with `0 < η'' < P'`, so `ω^{P'}` does not divide `η` and the last exponent is
  `< P'`;
* `TpEQall S` (**the reach equation of Theorem EQ^all at the top code**, for `T = B_n`): for `λ` of the
  range with `L(n+1) < ρ_λ`, `r(λ) < L(n+2)`, and the restart `λ'` with `B_n(ρ_λ) = ρ_{λ'}`,
  `B_n(r(λ)) = r(λ')`;
* `tpEQtop`: (S1) `TpRstMove` (restarts go to restarts) and `TpEQall` give `CxEQtop` (`λ'` is in the
  range: a restart, `λ' > λ ≥ B₀`, `ρ_{λ'} < L(ω+1)`, code `< P'` by `tpCode_top`).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Tp

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cx
  Googology.Trans.PoR.InaccPsi.R2.Nm

variable {S : InaccSeq.{0}}

/-- **The code of a restart in `(L(ω), L(ω+1))` is `< P'`.** -/
theorem tpCode_top {l : Ordinal.{0}} (hl : IsRestartIdx l) (h1 : Nc.ncL S ω < upsilon l)
    (h2 : upsilon l < Nc.ncL S (ω + 1)) : cdCode S l < Nc.ncPp S := by
  have hL1 : Nc.ncL S (ω + 1) = Pv S (Om ω + Nc.ncPp S * (ω + 1)) := Lw.lw_L_eq S (ω + 1)
  have hL0 : Nc.ncL S ω = Pv S (Om ω + Nc.ncPp S * ω) := Lw.lw_L_eq S ω
  obtain ⟨-, -, hηt, hpv⟩ :=
    cdEta_pv_spec (S := S) (η0 := Om ω + Nc.ncPp S * (ω + 1)) hl.1 (hL1 ▸ h2)
  have hlow : Om ω + Nc.ncPp S * ω < cdEta S l := by
    by_contra hle
    push Not at hle
    have := Pv_mono (S := S) hle
    rw [hpv, ← hL0] at this
    exact absurd h1 (not_lt.2 this)
  obtain ⟨η'', hη''⟩ := exists_add_of_le hlow.le
  have hη0 : η'' ≠ 0 := by
    rintro rfl; rw [add_zero] at hη''; rw [hη''] at hlow; exact lt_irrefl _ hlow
  have hηlt : η'' < Nc.ncPp S := by
    rw [hη'', mul_add_one, ← add_assoc] at hηt
    exact (add_lt_add_iff_left _).1 hηt
  have hSC : SC (Om (ω : Ordinal.{0})) := SC_Om omega0_ne_zero
  have hOw : ω ^ Om (ω : Ordinal.{0}) = Om ω := Low.opow_eq_self_of_SC hSC
  have hne : cdEta S l ≠ 0 := (lt_of_le_of_lt zero_le hlow).ne'
  have hexp : cdExp (cdEta S l) < Nc.ncPp S := by
    by_contra h
    push Not at h
    have hd : ω ^ Nc.ncPp S ∣ cdEta S l := (opow_dvd_opow ω h).trans (cdExp_dvd hne)
    have hdO : ω ^ Nc.ncPp S ∣ Om ω := by
      rw [← hOw]; exact opow_dvd_opow ω (cdPp_lt_Om_omega S).le
    have hdP : ω ^ Nc.ncPp S ∣ Nc.ncPp S * ω := by
      rw [Lw.lw_Pp_opow]; exact dvd_mul_right _ _
    rw [hη''] at hd
    have hd2 := (dvd_add_iff (dvd_add hdO hdP)).1 hd
    have := le_of_dvd hη0 hd2
    rw [Lw.lw_Pp_opow] at this
    exact absurd hηlt (not_lt.2 this)
  unfold cdCode
  rw [cdCodeOf_of_lt (hexp.trans (cdPp_lt_Om2 S))]
  exact (cdOff_le _).trans_lt hexp

/-- `ρ_λ ≤ r(λ)`. -/
theorem tpRho_le_R (l : Ordinal.{0}) : upsilon l ≤ cdR S l := by
  unfold cdR cdRc
  exact (upsilon_normal.strictMono.monotone (le_self_add.trans le_self_add)).trans (cdk_ge _ _)

/-- **The reach equation of EQ^all at the top code, for `B_n`**: if `λ` is in the range with
`L(n+1) < ρ_λ` and `r(λ) < L(n+2)`, and `B_n(ρ_λ) = ρ_{λ'}` for a restart `λ'`, then
`B_n(r(λ)) = r(λ')`. -/
def TpEQall (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
    IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' → Bc.bcB S n (cdR S l) = cdR S l'

/-- **`CxEQtop` from (S1) and the reach equation.** -/
theorem tpEQtop (hst : TpRstMove S) (hq : TpEQall S) : CxEQtop S := by
  intro n l hl h1 hr
  have h2 : upsilon l < Bc.bcC S (n + 1) := (tpRho_le_R l).trans_lt hr
  obtain ⟨μ', hμ', e⟩ := hst n l hl.1 h1.le h2
  have hw := cxB_window (S := S) h1.le h2
  rw [e] at hw
  have hlo : Nc.ncL S ω < upsilon μ' := by
    rw [← e, ← cxB_base (S := S) n]
    exact Bc.bcB_mono' S n (cxC_lt n) h2 h1
  have hlμ : l < μ' := by
    refine tpUps_lt_iff.1 (lt_trans ?_ hlo)
    exact h2.trans (Bc.bcC_lt S (n + 1))
  exact ⟨μ', ⟨hμ', hl.2.1.trans hlμ.le, hw.2, tpCode_top hμ' hlo hw.2⟩, e,
    hq n l μ' hl h1 hr hμ' e⟩

end Googology.Trans.PoR.InaccPsi.R2.Tp
