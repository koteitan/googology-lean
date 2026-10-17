import Googology.Trans.PoR.InaccPsi.R2.RzSpec
import Googology.Trans.PoR.InaccPsi.R2.RzClosed
import Googology.Trans.PoR.InaccPsi.R2.RzName
import Googology.Trans.PoR.InaccPsi.R2.CdLow

/-!
# LOWER of ENUM-REACH on `[B₀, Λ_B⁺)` away from the fixed points of `υ`, and the caps there

`r(λ) = k_λ(Θ_λ(m_λ))` (`cdR`), LOWER `ρ_λ ≤₁ r(λ)` (`CdLower`), UPPER `¬ ρ_λ ≤₁ r(λ) + 1` (`CdUpper`), the
range `[B₀, L(ω+1))` with codes `< P'` (`CdRange`), the cap `P(η_λ + ω^{e(η_λ)})` (`cdCapB`, `CdCapAt`,
`CdCapV`) of `R2.CdEnum`, `R2.CdLow`; `Λ_B⁺` (`rzLam`) and `lh(ρ_λ) = δ_λ + VzOrec(λ)` below it (`R2.RzSpec`);
`c(λ) = sup{k : ω^{1+k} ∣ λ}` (`cL`).

* `rzOrec_ge_cL` (**the realizers of the constants**): `c(λ) ≤ VzOrec(λ)` for every restart index `λ < Ω₁`
  (the constant `z < c(λ)` is realized by the restarts `μ` with `z ≤ c(μ)`, cofinal below `λ`, `cL_dense`);
* `rzEnum` (**ENUM-REACH below `Λ_B⁺` is an equation of ordinals**): for a restart index `λ < Λ_B⁺`,
  LOWER iff `Θ_λ(m_λ) ≤ VzOrec(λ)`, UPPER iff `VzOrec(λ) ≤ Θ_λ(m_λ)`, both iff `Θ_λ(m_λ) = VzOrec(λ)`;
* `rzLower_nonfix` (**LOWER at every restart index `λ < Λ_B⁺` with `λ < υ_λ`**, `ρ_λ` below a value of
  `P`): `Θ_λ(m_λ) = c(λ) ≤ VzOrec(λ)`; `rzUpper_nonfix`: there UPPER iff `VzOrec(λ) ≤ c(λ)`;
* `rzExact_succ` (**ENUM-REACH, both halves, at every successor restart index `λ < Λ_B⁺`**): `m_λ = 1`,
  `VzOrec(λ) = 1`, `r(λ) = δ_λ + 1 = lh(ρ_λ)`;
* `rzCapAt_nonfix`, `rzCapV_nonfix` (**the caps**): at a restart index `λ < Λ_B⁺` with `λ < υ_λ`, every
  `≤₁`-successor of `ρ_λ` and the predicted reach `r(λ)` lie below `υ_{λ+ω+2} ≤ P(η_λ + ω^{e(η_λ)})`;
* `rzRange_nonfix`: a restart index `λ ≥ B₀` with `λ < υ_λ` and `ρ_λ < L(ω+1)` is in the range;
* `rzInit` (**the initial part**): every `λ` of the range with `λ < Λ_B⁺` and `λ < υ_λ` has LOWER, CAP and the
  cap of the value; `rzFix`: at the fixed points `λ = υ_λ < Λ_B⁺` of the range, LOWER iff
  `Θ_λ(m_λ) ≤ VzOrec(λ)`; `rzLower_fix` (**LOWER there when `m_λ ≤ Ω₁`**: `Θ_λ(m_λ) ≤ Θ_λ(Ω₁) = ρ_λ = c(λ)`),
  `rzOrec_gt_fix`, `rzLower_fix_lim` (**and when `m_λ ≤ Ω₁ + 1` at a limit of fixed points**: there the base is
  realized, `ρ_λ < VzOrec(λ)`);
* `rz_lt_nuC`, `rzInit_nu`, `rzB0_exact`, `rzExact_succ_range` (**with `ν_C ≤ L(ω+1)`** every restart index of
  `[B₀, Λ_B⁺)` is below `L(ω+1)`): the initial part from that bound; ENUM-REACH at `B₀`;
* `rzLOWER_of_rest`, `rzUPPER_of_rest`, `rzCapV_of_rest`, `rzCAP0_of_rest`, `rzCAP1_of_rest` (**what is left
  of each hypothesis of the road**): it suffices to have it at the `λ` of the range with `Λ_B⁺ ≤ λ` or
  `λ = υ_λ` (for UPPER also: `VzOrec(λ) ≤ c(λ)` at the other `λ < Λ_B⁺`).

No new axiom, no new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Rz

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Cd VzTm

variable {S : InaccSeq.{0}}

/-- **`c(λ) ≤ VzOrec(λ)`** for every restart index `λ < Ω₁`. -/
theorem rzOrec_ge_cL : ∀ l, IsRestartIdx l → l < Om1 → cL l ≤ VzOrec l := by
  intro l
  induction l using WellFoundedLT.induction with
  | ind l IH =>
  intro hl hl1
  refine le_of_forall_lt fun z hz => ?_
  rcases eq_or_ne z 0 with rfl | hz0
  · exact lt_of_lt_of_le zero_lt_one (one_le_vzOrec hl hl1)
  · have hz1 : 1 ≤ z := Order.one_le_iff_ne_zero.2 hz0
    have hzl : z < l := hz.trans_le (cL_le hl)
    have hzρ : z < upsilon l := hz.trans_le (cL_le_ups hl)
    have hc : VzCofReal VzOrec l (cst z) := by
      intro ν hν
      obtain ⟨μ, hμ, h1, h2, h3⟩ := cL_dense hl hz1 hz (max ν z) (max_lt hν hzl)
      refine ⟨μ, hμ, (le_max_left ν z).trans_lt h1, h2, ?_, ?_⟩
      · show z < upsilon μ
        exact ((le_max_right ν z).trans_lt h1).trans_le (upsilon_normal.strictMono.id_le μ)
      · show z ≤ VzOrec μ
        exact h3.trans (IH μ h2 hμ (h2.trans hl1))
    exact lt_vzOrec_of_cof hl hl1 (s := cst z) hzρ hc

/-- **ENUM-REACH below `Λ_B⁺` as an equation of ordinals.** -/
theorem rzEnum {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlR : l < rzLam) :
    (CdLower S l ↔ cdTheta S l (cdCode S l) ≤ VzOrec l) ∧
      (CdUpper S l ↔ VzOrec l ≤ cdTheta S l (cdCode S l)) ∧
      ((CdUpper S l ∧ CdLower S l) ↔ cdTheta S l (cdCode S l) = VzOrec l) :=
  rzEnum_of_reach (rstGen rzSpec hl hlR).1 (rzSpec.le l hl hlR) (rzReach hl hlR)

/-- **LOWER at every restart index `λ < Λ_B⁺` with `λ < υ_λ`.** -/
theorem rzLower_nonfix {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hlR : l < rzLam)
    (hfix : upsilon l ≠ l) (hX : upsilon l < Pv S ηx) : CdLower S l := by
  refine (rzEnum hl hlR).1.2 ?_
  rw [rzTheta_nonfix hl hfix hX]
  exact rzOrec_ge_cL l hl (hlR.trans rzLam_lt_Om1)

/-- At a restart index `λ < Λ_B⁺` with `λ < υ_λ`: UPPER iff `VzOrec(λ) ≤ c(λ)`, both halves iff
`VzOrec(λ) = c(λ)`. -/
theorem rzUpper_nonfix {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hlR : l < rzLam)
    (hfix : upsilon l ≠ l) (hX : upsilon l < Pv S ηx) :
    (CdUpper S l ↔ VzOrec l ≤ cL l) ∧ ((CdUpper S l ∧ CdLower S l) ↔ VzOrec l = cL l) := by
  obtain ⟨-, hU, hE⟩ := rzEnum (S := S) hl hlR
  rw [rzTheta_nonfix hl hfix hX] at hU hE
  exact ⟨hU, hE.trans eq_comm⟩

/-- A restart index with `c(λ) < 2` is not a fixed point of `υ`. -/
theorem rz_succ_nonfix {l : Ordinal.{0}} (hl : IsRestartIdx l) (h2 : cL l < 2) : upsilon l ≠ l := by
  intro hfix
  rw [cL_fp (pos_iff_ne_zero.2 hl.1) hfix] at h2
  have hw : (2 : Ordinal.{0}) ≤ l := by
    have h1 : (2 : Ordinal.{0}) ≤ ω * ω :=
      (natCast_lt_omega0 2).le.trans (le_mul_left _ omega0_pos)
    exact h1.trans (le_of_dvd hl.1 (ri_iff.1 hl).2)
  exact absurd hw (not_le.2 h2)

/-- **ENUM-REACH, both halves, at every successor restart index `λ < Λ_B⁺`** (`ρ_λ` below a value of `P`):
`m_λ = 1` and `r(λ) = δ_λ + 1 = lh(ρ_λ)`. -/
theorem rzExact_succ {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hlR : l < rzLam) (h2 : cL l < 2)
    (hX : upsilon l < Pv S ηx) :
    cdCode S l = 1 ∧ CdUpper S l ∧ CdLower S l ∧ cdR S l = cdDelta l + 1 := by
  have hfix := rz_succ_nonfix hl h2
  have hc1 : cL l = 1 :=
    le_antisymm (Order.lt_add_one_iff.1 (by rw [one_add_one_eq_two]; exact h2)) (one_le_cL hl)
  have hO : VzOrec l = 1 := vzOrec_succ hl h2
  have hE := (rzUpper_nonfix (S := S) hl hlR hfix hX).2.2 (by rw [hO, hc1])
  have hcode : cdCode S l = 1 := by rw [rzCode_nonfix hl hfix hX, hc1]
  refine ⟨hcode, hE.1, hE.2, ?_⟩
  have hr := cdExact_iff.1 hE
  rw [Lb.lbReach_unique hr (rzReach hl hlR), hO]
  rfl

/-- `ω + 1 + 1 < u` for an indecomposable `u > ω`. -/
theorem rz_small_lt {u : Ordinal.{0}} (hu : Indec u) (hω : ω < u) : ω + 1 + 1 < u := by
  have hp := (indec_iff.1 hu).2
  have h1 : (1 : Ordinal.{0}) < u := one_lt_omega0.trans hω
  exact hp (hp hω h1) h1

/-- **`υ_{λ+ω+2} ≤ P(η_λ + ω^{e(η_λ)})`** at a restart index `λ < υ_λ` below a value of `P`. -/
theorem rzCap_ge {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hfix : upsilon l ≠ l)
    (hX : upsilon l < Pv S ηx) : upsilon (l + ω + 1 + 1) ≤ cdCapB S l := by
  have hU := ups_ri hl
  have hy : ω + 1 + 1 ≤ upsilon l := (rz_small_lt (indec_of_upsPt hU) (omega0_lt_inE (upsPt_inE hU))).le
  obtain ⟨-, hP⟩ := rzP_small (S := S) hl.1 hX hy
  have he := rzExp_nonfix (S := S) hl hfix hX
  have h2 : (1 + 1 : Ordinal.{0}) ≤ cdExp l := cdExp_max hl.1 (dvd_one_of_ri hl)
  have hww : ω + 1 + 1 < ω ^ (1 + 1 : Ordinal.{0}) := by
    have hω : ω < ω ^ (1 + 1 : Ordinal.{0}) := by
      rw [opow_add, opow_one]; exact lt_mul_of_one_lt_right omega0_pos one_lt_omega0
    exact rz_small_lt (indec_opow _) hω
  have hle : ω + 1 + 1 ≤ ω ^ cdExp (cdEta S l) := by
    rw [he]; exact hww.le.trans (opow_le_opow_right omega0_pos h2)
  unfold cdCapB
  calc upsilon (l + ω + 1 + 1) = upsilon (l + (ω + 1 + 1)) := by simp only [add_assoc]
    _ = Pv S (cdEta S l + (ω + 1 + 1)) := hP.symm
    _ ≤ Pv S (cdEta S l + ω ^ cdExp (cdEta S l)) := Pv_mono ((add_le_add_iff_left _).2 hle)

/-- `δ_λ + x < υ_{λ+ω+2}` for `x < δ_λ`. -/
theorem rz_delta_add_lt {l x : Ordinal.{0}} (hx : x < cdDelta l) :
    cdDelta l + x < upsilon (l + ω + 1 + 1) := by
  have hδ : cdDelta l < upsilon (l + ω + 1 + 1) := upsilon_normal.strictMono (lt_add_one _)
  have hI : Indec (upsilon (l + ω + 1 + 1)) :=
    indec_of_upsPt (upsPt_upsilon (lt_of_le_of_lt zero_le (lt_add_one _)))
  exact (indec_iff.1 hI).2 hδ (hx.trans hδ)

/-- **CAP at every restart index `λ < Λ_B⁺` with `λ < υ_λ`**: every `≤₁`-successor of `ρ_λ` is below the cap. -/
theorem rzCapAt_nonfix {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hlR : l < rzLam)
    (hfix : upsilon l ≠ l) (hX : upsilon l < Pv S ηx) : CdCapAt S l := fun g hg =>
  lt_of_le_of_lt ((rzReach hl hlR).2 g hg)
    ((rz_delta_add_lt (rzSpec.le l hl hlR)).trans_le (rzCap_ge hl hfix hX))

/-- **The cap of the predicted value at every restart index `λ < Λ_B⁺` with `λ < υ_λ`.** -/
theorem rzCapV_nonfix {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hlR : l < rzLam)
    (hfix : upsilon l ≠ l) (hX : upsilon l < Pv S ηx) : CdCapV S l := by
  have hcδ : cL l < cdDelta l :=
    (cL_le_ups hl).trans_lt (cdRho_lt_delta l)
  have hΘ : cdTheta S l (cdCode S l) < cdDelta l := by rw [rzTheta_nonfix hl hfix hX]; exact hcδ
  unfold CdCapV
  rw [rzR_eq (rstGen rzSpec hl hlR).1 hΘ, rzTheta_nonfix hl hfix hX]
  exact (rz_delta_add_lt hcδ).trans_le (rzCap_ge hl hfix hX)

/-- A restart index `λ ≥ B₀` with `λ < υ_λ` and `ρ_λ < L(ω+1)` is in the range of ENUM-REACH. -/
theorem rzRange_nonfix {l : Ordinal.{0}} (hl : IsRestartIdx l) (hB : cdB0 ≤ l)
    (hfix : upsilon l ≠ l) (hX : upsilon l < Nc.ncL S (ω + 1)) : CdRange S l := by
  have hX' : upsilon l < Pv S (Om ω + Nc.ncPp S * (ω + 1)) := Lw.lw_L_eq S (ω + 1) ▸ hX
  refine ⟨hl, hB, hX, ?_⟩
  rw [rzCode_nonfix hl hfix hX']
  exact (cL_le_ups hl).trans_lt ((hX'.trans (Pv_lt_Om1 S _)).trans (Lw.lw_Om1_lt_Pp S))

theorem rz_range_pv {l : Ordinal.{0}} (hr : CdRange S l) :
    upsilon l < Pv S (Om ω + Nc.ncPp S * (ω + 1)) := Lw.lw_L_eq S (ω + 1) ▸ hr.2.2.1

/-- **The initial part of ENUM-REACH's range that is proved**: every `λ` of the range with `λ < Λ_B⁺` and
`λ < υ_λ` has LOWER, CAP, the cap of the predicted value, and `m_λ = c(λ)`. -/
theorem rzInit {l : Ordinal.{0}} (hr : CdRange S l) (hlR : l < rzLam) (hfix : upsilon l ≠ l) :
    CdLower S l ∧ CdCapAt S l ∧ CdCapV S l ∧ cdCode S l = cL l :=
  ⟨rzLower_nonfix hr.1 hlR hfix (rz_range_pv hr), rzCapAt_nonfix hr.1 hlR hfix (rz_range_pv hr),
    rzCapV_nonfix hr.1 hlR hfix (rz_range_pv hr), rzCode_nonfix hr.1 hfix (rz_range_pv hr)⟩

/-- **At the fixed points below `Λ_B⁺`** LOWER is the inequality `Θ_λ(m_λ) ≤ VzOrec(λ)`. -/
theorem rzFix {l : Ordinal.{0}} (hr : CdRange S l) (hlR : l < rzLam) :
    CdLower S l ↔ cdTheta S l (cdCode S l) ≤ VzOrec l := (rzEnum hr.1 hlR).1

/-- `otp_C(m + 1) ≤ otp_C(m) + 1`. -/
theorem rz_otp_succ (C : Set Ordinal.{0}) (m : Ordinal.{0}) : cdOtp C (m + 1) ≤ cdOtp C m + 1 := by
  classical
  rw [cdOtp_eq C (m + 1)]
  refine ciSup_le' fun c => ?_
  split_ifs with hc
  · rcases (Order.lt_add_one_iff.1 (show c.1 < m + 1 from c.2)).lt_or_eq with h | h
    · exact (Order.add_one_le_of_lt (cdOtp_lt_of_mem hc h)).trans le_self_add
    · rw [h]
  · exact zero_le

/-- **LOWER at a fixed point `λ = υ_λ < Λ_B⁺` with a code `m_λ ≤ Ω₁`**: `Θ_λ(m_λ) ≤ Θ_λ(Ω₁) = ρ_λ = c(λ)`. -/
theorem rzLower_fix {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hlR : l < rzLam)
    (hX : upsilon l < Pv S ηx) (hfix : upsilon l = l) (hm : cdCode S l ≤ Om 1) : CdLower S l := by
  refine (rzEnum hl hlR).1.2 ?_
  have hΘ : cdTheta S l (cdCode S l) ≤ upsilon l :=
    (cdTheta_mono S l hm).trans_eq (cdTheta_Om1 (cdEta_pv hl.1 hX))
  calc cdTheta S l (cdCode S l) ≤ upsilon l := hΘ
    _ = cL l := by rw [cL_fp (pos_iff_ne_zero.2 hl.1) hfix, hfix]
    _ ≤ VzOrec l := rzOrec_ge_cL l hl (hlR.trans rzLam_lt_Om1)

/-- At a limit `λ < Ω₁` of fixed points of `υ`, the base is realized: `ρ_λ < VzOrec(λ)`. -/
theorem rzOrec_gt_fix {l : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : l < Om1)
    (hlim : ∀ ν < l, ∃ μ, ν < μ ∧ μ < l ∧ upsilon μ = μ) : upsilon l < VzOrec l := by
  have hc : VzCofReal VzOrec l bs := by
    intro ν hν
    obtain ⟨μ, h1, h2, hμ⟩ := hlim ν hν
    have hμ0 : 0 < μ := lt_of_le_of_lt zero_le h1
    have hμr := ri_of_fp hμ0 hμ
    refine ⟨μ, hμr, h1, h2, trivial, ?_⟩
    show upsilon μ ≤ VzOrec μ
    calc upsilon μ = cL μ := by rw [cL_fp hμ0 hμ, hμ]
      _ ≤ VzOrec μ := rzOrec_ge_cL μ hμr (h2.trans hl1)
  exact lt_vzOrec_of_cof hl hl1 (s := bs) trivial hc

/-- **LOWER at a fixed point `λ = υ_λ < Λ_B⁺` that is a limit of fixed points, with a code `m_λ ≤ Ω₁ + 1`**:
`Θ_λ(m_λ) ≤ Θ_λ(Ω₁) + 1 = ρ_λ + 1 ≤ VzOrec(λ)`. -/
theorem rzLower_fix_lim {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hlR : l < rzLam)
    (hX : upsilon l < Pv S ηx) (hlim : ∀ ν < l, ∃ μ, ν < μ ∧ μ < l ∧ upsilon μ = μ)
    (hm : cdCode S l ≤ Om 1 + 1) : CdLower S l := by
  refine (rzEnum hl hlR).1.2 ?_
  have hΘ : cdTheta S l (cdCode S l) ≤ upsilon l + 1 :=
    (cdTheta_mono S l hm).trans ((rz_otp_succ _ _).trans_eq
      (by rw [show cdOtp (cdHull S l) (Om 1) = cdTheta S l (Om 1) from rfl,
        cdTheta_Om1 (cdEta_pv hl.1 hX)]))
  exact hΘ.trans (Order.add_one_le_of_lt (rzOrec_gt_fix hl (hlR.trans rzLam_lt_Om1) hlim))

/-- Every restart below `Λ_B⁺` lies below `ν_C` (`rzFirst`). -/
theorem rz_lt_nuC {l : Ordinal.{0}} (hlR : l < rzLam) : upsilon l < nuC := by
  obtain ⟨L, -, hL, hLν, -⟩ := rzFirst
  exact (upsilon_normal.strictMono (hlR.trans_le hL)).trans hLν

/-- **The initial part, from `ν_C ≤ L(ω+1)`**: every restart index `λ ∈ [B₀, Λ_B⁺)` with `λ < υ_λ` is in the
range and has LOWER, CAP, the cap of the value and `m_λ = c(λ)`. -/
theorem rzInit_nu (hν : nuC ≤ Nc.ncL S (ω + 1)) {l : Ordinal.{0}} (hl : IsRestartIdx l)
    (hB : cdB0 ≤ l) (hlR : l < rzLam) (hfix : upsilon l ≠ l) :
    CdRange S l ∧ CdLower S l ∧ CdCapAt S l ∧ CdCapV S l ∧ cdCode S l = cL l := by
  have hr := rzRange_nonfix (S := S) hl hB hfix ((rz_lt_nuC hlR).trans_le hν)
  exact ⟨hr, rzInit hr hlR hfix⟩

/-- **ENUM-REACH at `B₀`** (both halves), from `ν_C ≤ L(ω+1)`: `B₀` is in the range, `m_{B₀} = 1`, and
`r(B₀) = δ_{B₀} + 1 = lh(ρ_{B₀})`. -/
theorem rzB0_exact (hν : nuC ≤ Nc.ncL S (ω + 1)) :
    CdRange S cdB0 ∧ cdCode S cdB0 = 1 ∧ CdUpper S cdB0 ∧ CdLower S cdB0 ∧
      cdR S cdB0 = cdDelta cdB0 + 1 := by
  have hl : IsRestartIdx cdB0 :=
    ri_iff.2 ⟨(lt_of_lt_of_le (mul_pos omega0_pos omega0_pos) le_add_self).ne',
      dvd_add (ri_iff.1 vzLam_ri).2 (dvd_refl _)⟩
  have h2 : cL cdB0 < 2 := rz_cL_succ (ri_iff.1 vzLam_ri).2
  have hX : upsilon cdB0 < Nc.ncL S (ω + 1) := (rz_lt_nuC rzB0_lt).trans_le hν
  have hr := rzRange_nonfix (S := S) hl le_rfl (rz_succ_nonfix hl h2) hX
  exact ⟨hr, rzExact_succ hl rzB0_lt h2 (rz_range_pv hr)⟩

/-- **ENUM-REACH at every successor restart index of the range below `Λ_B⁺`** (both halves). -/
theorem rzExact_succ_range {l : Ordinal.{0}} (hr : CdRange S l) (hlR : l < rzLam) (h2 : cL l < 2) :
    cdCode S l = 1 ∧ CdUpper S l ∧ CdLower S l ∧ cdR S l = cdDelta l + 1 :=
  rzExact_succ hr.1 hlR h2 (rz_range_pv hr)

/-- **LOWER on the range from LOWER at the `λ` with `Λ_B⁺ ≤ λ` or `λ = υ_λ`.** -/
theorem rzLOWER_of_rest (h : ∀ l, CdRange S l → (rzLam ≤ l ∨ upsilon l = l) → CdLower S l) :
    CdLOWER S := by
  intro l hr
  by_cases hc : rzLam ≤ l ∨ upsilon l = l
  · exact h l hr hc
  · push Not at hc
    exact (rzInit hr hc.1 hc.2).1

/-- **UPPER on the range** from UPPER at the `λ` with `Λ_B⁺ ≤ λ` or `λ = υ_λ`, and `VzOrec(λ) ≤ c(λ)` at the
other `λ` of the range. -/
theorem rzUPPER_of_rest (h : ∀ l, CdRange S l → (rzLam ≤ l ∨ upsilon l = l) → CdUpper S l)
    (hO : ∀ l, CdRange S l → l < rzLam → upsilon l ≠ l → VzOrec l ≤ cL l) : CdUPPER S := by
  intro l hr
  by_cases hc : rzLam ≤ l ∨ upsilon l = l
  · exact h l hr hc
  · push Not at hc
    exact (rzUpper_nonfix hr.1 hc.1 hc.2 (rz_range_pv hr)).1.2 (hO l hr hc.1 hc.2)

/-- **The cap of the values below `L(ω)`** from the cap at the `λ` with `Λ_B⁺ ≤ λ` or `λ = υ_λ`. -/
theorem rzCapV_of_rest
    (h : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → (rzLam ≤ l ∨ upsilon l = l) → CdCapV S l) :
    ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → CdCapV S l := by
  intro l hr hlX
  by_cases hc : rzLam ≤ l ∨ upsilon l = l
  · exact h l hr hlX hc
  · push Not at hc
    exact (rzInit hr hc.1 hc.2).2.2.1

/-- **CAP-0** from CAP at the restarts `λ ≥ B₀` of level 1 with `Λ_B⁺ ≤ λ` or `λ = υ_λ`. -/
theorem rzCAP0_of_rest
    (h : ∀ l, IsRestartIdx l → cdB0 ≤ l → upsilon l < cdMstar S → (rzLam ≤ l ∨ upsilon l = l) →
      CdCapAt S l) : CdCAP0 S := by
  intro l hl hB hlev
  by_cases hc : rzLam ≤ l ∨ upsilon l = l
  · exact h l hl hB hlev hc
  · push Not at hc
    exact rzCapAt_nonfix hl hc.1 hc.2 hlev

/-- **CAP-1 below `L(ω)`** from CAP at the restarts of level 2 there with `Λ_B⁺ ≤ λ` or `λ = υ_λ`. -/
theorem rzCAP1_of_rest
    (h : ∀ l, IsRestartIdx l → cdB0 ≤ l → cdMstar S ≤ upsilon l → upsilon l < Nc.ncL S ω →
      cdCode S l < Nc.ncPp S → (rzLam ≤ l ∨ upsilon l = l) → CdCapAt S l) :
    CdCAP1 S (Nc.ncL S ω) := by
  intro l hl hB hlev hlX hcode
  by_cases hc : rzLam ≤ l ∨ upsilon l = l
  · exact h l hl hB hlev hlX hcode hc
  · push Not at hc
    exact rzCapAt_nonfix hl hc.1 hc.2 (Lw.lw_L_eq S ω ▸ hlX)

end Googology.Trans.PoR.InaccPsi.R2.Rz
