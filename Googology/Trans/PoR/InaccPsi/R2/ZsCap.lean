import Googology.Trans.PoR.InaccPsi.R2.ZsBig

/-!
# Zs: short readings below `K_ω`, no supply at the base, CapV at the codes `≤ K_ω`

`K_ω = ψ_{Ω₂}(Ω_ω + Ω₂) = sup_j K_j` (`Zr.zrK_sup`).  At a range restart `λ` below `L(ω)` with a name `η ≠ 0`
(`A = A_η = Ω_ω + θ·η > Ω_ω`, own, `Θ(θ) = ψ_{Ω₁}(A + θ)` by `Wl.wlThVal`, `Θ(Ω₁) = ρ_λ`):

* `zsShortK` (**every code `c ≤ K_ω` reads short**: `Θ_λ(c) ≤ ψ_{Ω₁}(A + θ + Ω₁) < δ_λ`, `Zr.zrTh_K`);
* `zsShortLow` (**below `ι(Ω₂)` every code reads short**: for `η ≤ Ω₂`, `A ≤ Ω_ω + Ω₂`, every atom lies below
  `K_ω`, so `Θ_λ(Ω₂) ≤ ψ_{Ω₁}(A + θ + Ω₁) < δ_λ`, `Zr.zrTh_Om2`);
* `zsSup_false` (**NO-GO for the supply branch at the base `l₀ = ι(Ω₂)`**: the supply asks restarts `μ` cofinal
  below `l₀` with `υ_{μ+ω+2} ≤ r(μ)`, but every such `μ` reads short, so `r(μ) = δ_μ + Θ_μ(m_μ) < υ_{μ+ω+2}`);
* `zsCapV_K` (**CapV at a `υ`-fixed restart with a code `≤ K_ω`**, `Zn.znCapV_fixTh`).

So at `l₀` every branch of the RS input (term, value, successor, supply) fails or is LOWER itself
(`Zs.zsBaseRs_lower`, `zsSup_false`).

No new axiom.  No new definition.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Googology.Trans.PoR.InaccPsi.R2.Zs

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Zo Googology.Trans.PoR.InaccPsi.R2.Zr

variable {S : InaccSeq.{0}}

section Hull

variable {l : Ordinal.{0}} (hr : CdRange S l) (hω : upsilon l < Nc.ncL S ω)

include hr hω

theorem zsPvLt : upsilon l < Pv S (Om ω + Nc.ncPp S * ω) := by
  rw [← Lw.lw_L_eq]; exact hω

theorem zsRho : S.psi (ConjT.Aη S (cdEta S l)) (Om 1) = upsilon l :=
  (cdEta_pv_spec (S := S) hr.1.1 (zsPvLt hr hω)).2.2.2

theorem zsOwn : ConjT.Aη S (cdEta S l) ∈ S.CSet (ConjT.Aη S (cdEta S l)) (upsilon l) := by
  obtain ⟨-, -, hown0⟩ := Rc.rcOwn hr.1 hω
  rw [← zsRho hr hω]; exact hown0

theorem zsOwn' : ConjT.Aη S (cdEta S l) ∈
    S.CSet (ConjT.Aη S (cdEta S l)) (S.psi (ConjT.Aη S (cdEta S l)) (Om 1)) := by
  rw [zsRho hr hω]; exact zsOwn hr hω

theorem zsThθ : cdOtp (S.CSet (ConjT.Aη S (cdEta S l)) (upsilon l)) (ConjT.th S) =
    S.psi (ConjT.Aη S (cdEta S l) + ConjT.th S) (Om 1) := by
  have hρ := zsRho hr hω
  have hθg := Wl.wlThVal (l := l) hr.1 (zsPvLt hr hω) (zsOwn' hr hω) hρ
  have hat : Ld.ldAtR S l = Ls.lsAt S (ConjT.Aη S (cdEta S l)) (upsilon l) := by
    unfold Ld.ldAtR; ext s
    exact ⟨fun ⟨a, h1, h2, h3⟩ => ⟨a, h2, h1, h3⟩, fun ⟨a, h1, h2, h3⟩ => ⟨a, h2, h1, h3⟩⟩
  have hθ2 : ConjT.th S < Om (1 + 1) := psi_lt (InR_Om_succ 1) _
  rw [Ls.lsOtp_eq (m := ConjT.th S) hρ hθ2.le, ← hat]
  exact hθg

theorem zsThΩ : cdOtp (S.CSet (ConjT.Aη S (cdEta S l)) (upsilon l)) (Om 1) = upsilon l := by
  have h := cdTheta_Om1 (S := S) (l := l) (zsRho hr hω)
  unfold cdTheta cdHull at h
  exact h

theorem zsDelta : S.psi (ConjT.Aη S (cdEta S l) + ConjT.th S * (ω + 1)) (Om 1) = cdDelta l := by
  have hSC : SC (upsilon l) := by rw [← zsRho hr hω]; exact SC_psi Low.InR_Om_one _
  have hγ : ω + 1 ≤ upsilon l := Order.add_one_le_of_lt (Lw.lw_omega_lt_SC hSC)
  have hu := Rg.rgUps_eq hr hγ
  unfold cdDelta; rw [add_assoc l]; exact hu.symm

variable (hη0 : cdEta S l ≠ 0)

include hη0

theorem zsOmw : Om ω < ConjT.Aη S (cdEta S l) := by
  show Om ω < Om ω + ConjT.th S * cdEta S l
  exact lt_add_of_pos_right _ (mul_pos zrTh_pos (pos_iff_ne_zero.2 hη0))

/-- A hull bound `ψ_{Ω₁}(A + θ + Ω₁)` gives a short reading. -/
theorem zsTh_lt {c : Ordinal.{0}}
    (hc : cdOtp (S.CSet (ConjT.Aη S (cdEta S l)) (upsilon l)) c ≤ zrPs S (ConjT.Aη S (cdEta S l)) (Om 1)) :
    cdTheta S l c < cdDelta l := by
  have hy := zrY_lt (zsOwn' hr hω) (zsOmw hr hω hη0)
  unfold cdTheta cdHull
  exact hc.trans_lt (hy.trans_le (zsDelta hr hω).le)

/-- **Every code `c ≤ K_ω` reads short.** -/
theorem zsShortK {c : Ordinal.{0}} (hc : c ≤ S.psi (Om ω + Om (1 + 1)) (Om (1 + 1))) :
    cdTheta S l c < cdDelta l :=
  zsTh_lt hr hω hη0 ((cdOtp_mono _ hc).trans
    (zrTh_K (zsRho hr hω) (zsOmw hr hω hη0) (zsOwn hr hω) (zsThθ hr hω) (zsThΩ hr hω)))

/-- **Below `ι(Ω₂)` every code reads short** (`η ≤ Ω₂`). -/
theorem zsShortLow (hη2 : cdEta S l ≤ Om (1 + 1)) {c : Ordinal.{0}} (hc : c ≤ Om (1 + 1)) :
    cdTheta S l c < cdDelta l := by
  have hA2 : ConjT.Aη S (cdEta S l) ≤ Om ω + Om (1 + 1) := by
    show Om ω + ConjT.th S * cdEta S l ≤ Om ω + Om (1 + 1)
    refine add_le_add le_rfl ?_
    calc ConjT.th S * cdEta S l ≤ ConjT.th S * Om (1 + 1) := mul_le_mul_left' hη2 _
      _ = Om (1 + 1) := zr_th_Om2
  exact zsTh_lt hr hω hη0 ((cdOtp_mono _ hc).trans
    (zrTh_Om2 (zsRho hr hω) (zsOmw hr hω hη0) (zsOwn hr hω) (zsThθ hr hω) (zsThΩ hr hω) hA2))

end Hull

/-- `P(0) < ρ_{l₀}`. -/
theorem zsP0_lt : Pv S 0 < upsilon (zoBase S) := by
  rw [zrBase_rho]
  refine (Pv_lt_succ (S := S) (Nm.good_zero S)).trans_le (Pv_mono ?_)
  rw [zero_add]
  exact Order.one_le_iff_pos.2 (Om_pos (by rw [one_add_one_eq_two]; exact two_ne_zero))

/-- A range restart above `P(0)` has a name `≠ 0`. -/
theorem zsEta_ne {μ : Ordinal.{0}} (hr : CdRange S μ) (hω : upsilon μ < Nc.ncL S ω)
    (h0 : Pv S 0 < upsilon μ) : cdEta S μ ≠ 0 := by
  intro h
  have hpv := (cdEta_pv_spec (S := S) hr.1.1 (zsPvLt hr hω)).2.2.2
  rw [h] at hpv
  exact absurd hpv (ne_of_lt h0)

/-- `ρ_{l₀} < L(ω)`. -/
theorem zsBase_lt_Lw : upsilon (zoBase S) < Nc.ncL S ω := zsLt_L0.trans_le (Pp.ppL_mono (S := S) zero_le)

/-- **NO-GO for the supply branch at the base**: every range restart `μ` below `l₀` reads short, so no
`υ_{μ+β}` with `β ≥ ω + 2` lies below its reach, while `r(l₀) > δ_{l₀}` asks such a `β`. -/
theorem zsSup_false
    (hlow : ∀ μ, CdRange S μ → μ < iota S (Om (1 + 1)) → CdUpper S μ ∧ CdLower S μ ∧ CdCapV S μ)
    (B : Ordinal.{0}) : ¬ Zh.ZhSupInB S (zoBase S) B := by
  rintro ⟨β, -, hrB, hsup⟩
  have hm := upsilon_normal.strictMono
  have hν := zrNu hlow
  have hpos : 0 < cdTheta S (zoBase S) (cdCode S (zoBase S)) := lt_of_le_of_lt zero_le zsBig
  have hδr : cdDelta (zoBase S) < cdR S (zoBase S) :=
    lt_of_lt_of_le (lt_add_of_pos_right _ hpos) (Zh.zhR_ge_theta (S := S) _)
  rcases le_or_gt β (ω + 1) with hβ | hβ
  · have : upsilon (zoBase S + β) ≤ cdDelta (zoBase S) := by
      unfold cdDelta; rw [add_assoc]; exact hm.monotone (add_le_add le_rfl hβ)
    exact absurd (hrB.trans this) (not_le.2 hδr)
  · have hβ2 : ω + 2 ≤ β := by
      rw [show (ω + 2 : Ordinal.{0}) = ω + 1 + 1 by rw [add_assoc]; norm_num]
      exact Order.add_one_le_of_lt hβ
    obtain ⟨μ, hR, h1, h2, -, -, h6⟩ := hsup (Pv S 0) zsP0_lt
    have hωμ : upsilon μ < Nc.ncL S ω := h2.trans zsBase_lt_Lw
    have hη0 := zsEta_ne hR hωμ h1
    have hη2 : cdEta S μ ≤ Om (1 + 1) := by
      by_contra hgt
      have hpv := (cdEta_pv_spec (S := S) hR.1.1 (zsPvLt hR hωμ)).2.2.2
      have hle : Pv S (Om (1 + 1)) ≤ Pv S (cdEta S μ) := Pv_mono (not_le.1 hgt).le
      rw [hpv, ← zrBase_rho] at hle
      exact absurd h2 (not_lt.2 hle)
    have hcode : cdCode S μ ≤ Om (1 + 1) := (hR.2.2.2.trans (cdPp_lt_Om2 S)).le
    have hθμ := zsShortLow hR hωμ hη0 hη2 hcode
    have hRμ := Zh.zhR_short_theta hR.1 (h2.trans hν) hθμ
    have hlt : μ + ω + 1 < μ + (ω + 2) := by
      rw [← add_assoc]
      exact (add_lt_add_iff_left _).2 (by exact_mod_cast (show (1 : ℕ) < 2 by norm_num))
    have hpos' : 0 < μ + (ω + 2) := lt_of_le_of_lt zero_le hlt
    have hI := indec_of_upsPt (upsPt_upsilon hpos')
    have hδ2 : cdDelta μ < upsilon (μ + (ω + 2)) := hm hlt
    have hsmall : cdR S μ < upsilon (μ + (ω + 2)) := by
      rw [hRμ]; exact hI.add_lt hδ2 (hθμ.trans hδ2)
    have hbig : upsilon (μ + (ω + 2)) ≤ cdR S μ :=
      (hm.monotone (add_le_add le_rfl hβ2)).trans h6
    exact absurd hbig (not_le.2 hsmall)

/-- **CapV at a `υ`-fixed restart with a code `≤ K_ω`** (below `ν_C` and `m* = L(0)`). -/
theorem zsCapV_K {l : Ordinal.{0}} (hr : CdRange S l) (hfix : upsilon l = l) (hν : upsilon l < nuC)
    (hm : upsilon l < cdMstar S) (hη0 : cdEta S l ≠ 0)
    (hc : cdCode S l ≤ S.psi (Om ω + Om (1 + 1)) (Om (1 + 1))) : CdCapV S l :=
  Zn.znCapV_fixTh hr.1 hfix hν hm (zsShortK hr (hm.trans_le (cdMstar_le_L S ω)) hη0 hc)

/-- The names of the range restarts above `l₀` are `≠ 0`. -/
theorem zsEta_ne_above {μ : Ordinal.{0}} (hr : CdRange S μ) (h0 : zoBase S < μ) (hm : upsilon μ < cdMstar S) :
    cdEta S μ ≠ 0 :=
  zsEta_ne hr (hm.trans_le (cdMstar_le_L S ω)) (zsP0_lt.trans (upsilon_normal.strictMono h0))

end Googology.Trans.PoR.InaccPsi.R2.Zs
