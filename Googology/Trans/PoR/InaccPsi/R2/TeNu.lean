import Googology.Trans.PoR.InaccPsi.R2.TbLong

/-!
# `ν_C` is a closed point of every restart below it: the predicted reach against `ν_C`

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.

Lemma CAP at `ν_C` (`nuC_cap`: no `α ≤ ν_C` is `≤₁` a point above `ν_C`) makes `ν_C` closed relative to every
restart `λ` with `δ_λ ≤ ν_C`, with no hypothesis (`teNu_closed`, `teNu_mem`).  So `ν_C = k_λ(otp(K_λ ∩ ν_C))`, and
the predicted reach `r(λ) = k_λ(Θ_λ(m_λ))` is compared with `ν_C` by comparing two readings:

* `teR_le_nu_iff`, `teNu_le_R_iff`, `teR_eq_nu_iff` (**`r(λ) ≤ ν_C ⇔ Θ_λ(m_λ) ≤ otp(K_λ ∩ ν_C)`**, and `≥`, `=`);
* `teUpper_of_le` (**UPPER at `λ` whenever `ρ_λ ≤ ν_C ≤ r(λ)`**, for every code), `teR_le_of_lower` (**LOWER at
  `λ` forces `r(λ) ≤ ν_C`**), `teReach_nu_iff` (`lh(ρ_λ) = ν_C ⇔ ρ_λ ≤₁ ν_C`);
* `teEnum_nu_iff` (**ENUM-REACH at `λ` with the value `ν_C` iff `ρ_λ ≤₁ ν_C` and `Θ_λ(m_λ) = otp(K_λ ∩ ν_C)`**),
  `teEnum_iff_count`, `teUpper_iff_count`, `teLower_iff_count` (**when `lh(ρ_λ) = ν_C`: ENUM-REACH, UPPER,
  LOWER at `λ` are `=`, `≥`, `≤` between `Θ_λ(m_λ)` and `otp(K_λ ∩ ν_C)`**);
* the points `L(k)` (`k < ω`) and `L(ω)` as restart indices: `teUps_L` (`υ_{L(k)} = L(k)`), `teL_lt_succ`,
  `teDelta_L` (`δ_{L(k)} < L(k+1)`), `teDelta_Lw` (`δ_{L(ω)} ≤ L(ω+1)`), and under UPPER, CapV, LOWER at the
  range restarts (`Sh.shNu`: `L(ω+1) ≤ ν_C`) `teNu_mem_L`, `teNu_mem_Lw` (**`ν_C ∈ K_{L(k)}`, `ν_C ∈ K_{L(ω)}`**).

`teNu_mem_Lw` replaces the hypothesis `lh(L(ω)) = L(ω+1)` of `Rc.rcLw_closed` by the closedness of `ν_C`.

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Te

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-! ## `ν_C` is closed -/

/-- **`ν_C` is closed relative to every `λ` with `δ_λ ≤ ν_C`** (Lemma CAP at `ν_C`). -/
theorem teNu_closed {l : Ordinal.{0}} (hδ : cdDelta l ≤ nuC) : cdClosed l nuC :=
  ⟨hδ, fun a _ ha g hg => not_lt.1 fun h => nuC_cap a ha g h hg⟩

theorem teNu_mem {l : Ordinal.{0}} (hδ : cdDelta l ≤ nuC) : nuC ∈ cdK l := Or.inl (teNu_closed hδ)

/-- `k_λ(otp(K_λ ∩ ν_C)) = ν_C`. -/
theorem teK_nu {l : Ordinal.{0}} (hδ : cdDelta l ≤ nuC) : cdk l (cdOtp (cdK l) nuC) = nuC :=
  Rc.rcEnum_otp (cdK_unbdd l) (teNu_mem hδ)

/-! ## The predicted reach against `ν_C` -/

/-- **`ν_C ≤ r(λ) ⇔ otp(K_λ ∩ ν_C) ≤ Θ_λ(m_λ)`** (no hypothesis). -/
theorem teNu_le_R_iff (l : Ordinal.{0}) :
    nuC ≤ cdR S l ↔ cdOtp (cdK l) nuC ≤ cdTheta S l (cdCode S l) :=
  Rc.rcLe_R_iff S l nuC

/-- **`r(λ) ≤ ν_C ⇔ Θ_λ(m_λ) ≤ otp(K_λ ∩ ν_C)`** when `δ_λ ≤ ν_C`. -/
theorem teR_le_nu_iff {l : Ordinal.{0}} (hδ : cdDelta l ≤ nuC) :
    cdR S l ≤ nuC ↔ cdTheta S l (cdCode S l) ≤ cdOtp (cdK l) nuC := by
  have he := teK_nu hδ
  unfold cdR cdRc
  conv_lhs => rw [← he]
  exact (cdk_strictMono l).le_iff_le

/-- **`r(λ) = ν_C ⇔ Θ_λ(m_λ) = otp(K_λ ∩ ν_C)`** when `δ_λ ≤ ν_C`. -/
theorem teR_eq_nu_iff {l : Ordinal.{0}} (hδ : cdDelta l ≤ nuC) :
    cdR S l = nuC ↔ cdTheta S l (cdCode S l) = cdOtp (cdK l) nuC :=
  Rc.rcR_eq_iff S (teNu_mem hδ)

/-- **UPPER at every `λ` with `ρ_λ ≤ ν_C ≤ r(λ)`**, whatever the code. -/
theorem teUpper_of_le {l : Ordinal.{0}} (hρ : upsilon l ≤ nuC) (h : nuC ≤ cdR S l) : CdUpper S l :=
  fun h1 => nuC_cap _ hρ _ (lt_of_le_of_lt h (lt_add_one _)) h1

/-- **LOWER at `λ` (`ρ_λ ≤ ν_C`) forces `r(λ) ≤ ν_C`.** -/
theorem teR_le_of_lower {l : Ordinal.{0}} (hρ : upsilon l ≤ nuC) (h : CdLower S l) : cdR S l ≤ nuC :=
  not_lt.1 fun hlt => nuC_cap _ hρ _ hlt h

/-- **`lh(ρ_λ) = ν_C ⇔ ρ_λ ≤₁ ν_C`** for `ρ_λ ≤ ν_C`. -/
theorem teReach_nu_iff {a : Ordinal.{0}} (hρ : a ≤ nuC) : IsReach R2C a nuC ↔ le1 a nuC :=
  ⟨fun h => h.1, fun h => ⟨h, fun _ hg => not_lt.1 fun hlt => nuC_cap _ hρ _ hlt hg⟩⟩

/-- **ENUM-REACH at `λ` with the value `ν_C` iff `ρ_λ ≤₁ ν_C` and `Θ_λ(m_λ) = otp(K_λ ∩ ν_C)`.** -/
theorem teEnum_nu_iff {l : Ordinal.{0}} (hρ : upsilon l ≤ nuC) (hδ : cdDelta l ≤ nuC) :
    (CdUpper S l ∧ CdLower S l ∧ cdR S l = nuC) ↔
      (le1 (upsilon l) nuC ∧ cdTheta S l (cdCode S l) = cdOtp (cdK l) nuC) := by
  constructor
  · rintro ⟨-, hL, he⟩
    refine ⟨?_, (teR_eq_nu_iff hδ).1 he⟩
    have h := hL; unfold CdLower at h; rwa [he] at h
  · rintro ⟨h1, h2⟩
    have e := (teR_eq_nu_iff hδ).2 h2
    refine ⟨teUpper_of_le hρ e.ge, ?_, e⟩
    unfold CdLower; rw [e]; exact h1

/-- **When `lh(ρ_λ) = ν_C`: ENUM-REACH at `λ` iff `Θ_λ(m_λ) = otp(K_λ ∩ ν_C)`.** -/
theorem teEnum_iff_count {l : Ordinal.{0}} (hr : IsReach R2C (upsilon l) nuC) (hδ : cdDelta l ≤ nuC) :
    (CdUpper S l ∧ CdLower S l) ↔ cdTheta S l (cdCode S l) = cdOtp (cdK l) nuC := by
  rw [cdExact_iff]
  constructor
  · intro h; exact (teR_eq_nu_iff hδ).1 (Lb.lbReach_unique h hr)
  · intro h
    have e := (teR_eq_nu_iff hδ).2 h
    rw [e]; exact hr

/-- **When `lh(ρ_λ) = ν_C`: UPPER at `λ` iff `otp(K_λ ∩ ν_C) ≤ Θ_λ(m_λ)`.** -/
theorem teUpper_iff_count {l : Ordinal.{0}} (hr : IsReach R2C (upsilon l) nuC) :
    CdUpper S l ↔ cdOtp (cdK l) nuC ≤ cdTheta S l (cdCode S l) :=
  (cdUpper_iff_ge hr).trans (teNu_le_R_iff l)

/-- **When `lh(ρ_λ) = ν_C`: LOWER at `λ` iff `Θ_λ(m_λ) ≤ otp(K_λ ∩ ν_C)`.** -/
theorem teLower_iff_count {l : Ordinal.{0}} (hr : IsReach R2C (upsilon l) nuC) (hδ : cdDelta l ≤ nuC) :
    CdLower S l ↔ cdTheta S l (cdCode S l) ≤ cdOtp (cdK l) nuC :=
  (cdLower_iff_le hr).trans (teR_le_nu_iff hδ)

/-! ## The points `L(k)` and `L(ω)` as restart indices -/

/-- `υ_{L(k)} = L(k)`. -/
theorem teUps_L (k : ℕ) : upsilon (Nc.ncL S (k : Ordinal.{0})) = Nc.ncL S (k : Ordinal.{0}) := by
  cases k with
  | zero => simpa using Rm.rm_M_fix (S := S)
  | succ n =>
    obtain ⟨-, hι, hP, -⟩ := Ls.lsL_named (S := S) n
    have h := Bt.ups_iota S (Om ω + Nc.ncPp S * ((n + 1 : ℕ) : Ordinal.{0}))
    rw [hι] at h
    exact h.trans hP

/-- `L(k) < L(k+1)`. -/
theorem teL_lt_succ (k : ℕ) : Nc.ncL S (k : Ordinal.{0}) < Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) := by
  cases k with
  | zero => simpa using Rl.rlM_lt_L1 (S := S)
  | succ n => exact Pp.ppL_lt_succ n

/-- `L(k) < L(ω)`. -/
theorem teL_lt_omega (k : ℕ) : Nc.ncL S (k : Ordinal.{0}) < Nc.ncL S ω :=
  (teL_lt_succ k).trans_le (Pp.ppL_mono (Ordinal.natCast_lt_omega0 _).le)

/-- **`δ_{L(k)} < L(k+1)`.** -/
theorem teDelta_L (k : ℕ) : cdDelta (Nc.ncL S (k : Ordinal.{0})) < Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) := by
  have hE : InE (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) := Gg.gg_SC_eps (Lw.lw_L_SC S _)
  have hw : ω < Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) := Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)
  have h1 : (1 : Ordinal.{0}) < Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) := one_lt_omega0.trans hw
  have hlt : Nc.ncL S (k : Ordinal.{0}) + ω + 1 < Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) :=
    hE.add_lt (hE.add_lt (teL_lt_succ k) hw) h1
  unfold cdDelta
  calc upsilon (Nc.ncL S (k : Ordinal.{0}) + ω + 1)
      < upsilon (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) := upsilon_normal.strictMono hlt
    _ = Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) := teUps_L (k + 1)

/-- **`δ_{L(ω)} ≤ L(ω+1)`.** -/
theorem teDelta_Lw : cdDelta (Nc.ncL S ω) ≤ Nc.ncL S (ω + 1) := by
  have hw : ω < Nc.ncL S ω := Lw.lw_omega_lt_SC (Lw.lw_L_SC S ω)
  unfold cdDelta
  refine le_trans (upsilon_normal.strictMono.monotone ?_) Ra.raLw_AA
  rw [add_assoc]
  exact add_le_add le_rfl (Order.add_one_le_of_lt hw)

section Hyp

variable (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
  (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
  (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
  (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
include hU hV hVt hL

/-- `L(k) < ν_C` (from `Sh.shNu`). -/
theorem teL_lt_nu (k : ℕ) : Nc.ncL S (k : Ordinal.{0}) < nuC :=
  ((teL_lt_omega k).trans (Qq.qqL_lt_succ S)).trans_le (Sh.shNu hU hV hVt hL)

theorem teLw_lt_nu : Nc.ncL S ω < nuC := (Qq.qqL_lt_succ S).trans_le (Sh.shNu hU hV hVt hL)

/-- **`ν_C ∈ K_{L(k)}`**. -/
theorem teNu_mem_L (k : ℕ) : nuC ∈ cdK (Nc.ncL S (k : Ordinal.{0})) := by
  refine teNu_mem ((teDelta_L k).le.trans ?_)
  have := teL_lt_nu hU hV hVt hL (k + 1)
  exact this.le

/-- **`ν_C ∈ K_{L(ω)}`** (no hypothesis on `lh(L(ω))`, compare `Rc.rcLw_closed`). -/
theorem teNu_mem_Lw : nuC ∈ cdK (Nc.ncL S ω) :=
  teNu_mem (teDelta_Lw.trans (Sh.shNu hU hV hVt hL))

/-- **ENUM-REACH at `L(k)` with the value `ν_C` iff `L(k) ≤₁ ν_C` and `Θ_{L(k)}(P') = otp(K_{L(k)} ∩ ν_C)`.** -/
theorem teEnum_L_iff (k : ℕ) :
    (CdUpper S (Nc.ncL S (k : Ordinal.{0})) ∧ CdLower S (Nc.ncL S (k : Ordinal.{0})) ∧
        cdR S (Nc.ncL S (k : Ordinal.{0})) = nuC) ↔
      (le1 (Nc.ncL S (k : Ordinal.{0})) nuC ∧
        cdTheta S (Nc.ncL S (k : Ordinal.{0})) (Nc.ncPp S) = cdOtp (cdK (Nc.ncL S (k : Ordinal.{0}))) nuC) := by
  have hcode : cdCode S (Nc.ncL S (k : Ordinal.{0})) = Nc.ncPp S := by
    cases k with
    | zero => exact (cdCode_L0 (by simpa using teUps_L (S := S) 0)).2
    | succ n => exact cdCode_L n (teUps_L (n + 1))
  have hρ : upsilon (Nc.ncL S (k : Ordinal.{0})) ≤ nuC := by
    rw [teUps_L]; exact (teL_lt_nu hU hV hVt hL k).le
  have hδ : cdDelta (Nc.ncL S (k : Ordinal.{0})) ≤ nuC :=
    (teDelta_L k).le.trans (teL_lt_nu hU hV hVt hL (k + 1)).le
  have h := teEnum_nu_iff (S := S) hρ hδ
  rw [hcode, teUps_L] at h
  exact h

/-- **ENUM-REACH at `L(ω)` with the value `ν_C` iff `L(ω) ≤₁ ν_C` and
`Θ_{L(ω)}(P' + 1) = otp(K_{L(ω)} ∩ ν_C)`.** -/
theorem teEnum_Lw_iff :
    (CdUpper S (Nc.ncL S ω) ∧ CdLower S (Nc.ncL S ω) ∧ cdR S (Nc.ncL S ω) = nuC) ↔
      (le1 (Nc.ncL S ω) nuC ∧
        cdTheta S (Nc.ncL S ω) (Nc.ncPp S + 1) = cdOtp (cdK (Nc.ncL S ω)) nuC) := by
  have hcode : cdCode S (Nc.ncL S ω) = Nc.ncPp S + 1 := cdCode_Lω Rc.rcUps_Lw
  have hρ : upsilon (Nc.ncL S ω) ≤ nuC := by rw [Rc.rcUps_Lw]; exact (teLw_lt_nu hU hV hVt hL).le
  have hδ : cdDelta (Nc.ncL S ω) ≤ nuC := teDelta_Lw.trans (Sh.shNu hU hV hVt hL)
  have h := teEnum_nu_iff (S := S) hρ hδ
  rw [hcode, Rc.rcUps_Lw] at h
  exact h

end Hyp

end Googology.Trans.PoR.InaccPsi.R2.Te
