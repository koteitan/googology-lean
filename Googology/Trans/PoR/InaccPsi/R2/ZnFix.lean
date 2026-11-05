import Googology.Trans.PoR.InaccPsi.R2.ZnAll
import Googology.Trans.PoR.InaccPsi.R2.WdSplit

/-!
# Zn: the RS input and CapV at the `υ`-fixed restarts with a short reading

At a `υ`-fixed restart `λ = υ_λ` (`λ` an `ε`-number, `c(λ) = λ`) the code is at least `λ` (`Fx.fxCode_fix`), so
`Θ_λ(m_λ) ≥ ρ_λ`.  Two cases are theorems here:

* `znO_ge_cL` (**the bound is at least the offset**, no `ν_C`): `c(μ) ≤ O(μ) = r(μ) − δ_μ` at every restart
  `μ > ω²` with a name (the code is `c(μ)` off the fixed points, `≥ μ ≥ c(μ)` at them);
* `zn_cL_fix`: `c(λ) = λ` at a `υ`-fixed restart;
* `znRsIn_fixShort` (**the RS input at a fixed restart with `Θ_λ(m_λ) ≤ ρ_λ`**): then `O(λ) = ρ_λ` and the
  term input holds with the constant terms `w < ρ_λ` (restarts with `c(μ) ≥ w` are cofinal, `R2.cL_dense`);
* `znCapV_theta` (**CapV at a short reading**): `Θ_λ(m_λ) < δ_λ`, `2 ≤ e(η_λ)`, `ρ_λ < ν_C` give
  `r(λ) = δ_λ + Θ_λ(m_λ) < υ_{λ+ω+2} ≤ P(η_λ + ω^e)`; `znCapV_fixTh` at the fixed restarts (`e ≥ λ`);
* `znSupInB_false` (**NO-GO for the supply branch at an isolated fixed restart**): if no fixed restart lies
  in `(x₀, λ)`, `ρ_λ < ν_C` and `Θ_λ(m_λ) > 0`, then `Zh.ZhSupInB S λ B` is false for every `B` (a target
  `r(λ) ≤ υ_{λ+β}` needs `β ≥ ω+2`, the supply then needs `υ_{μ+ω+2} ≤ r(μ) = δ_μ + c(μ)` at non-fixed `μ`);
* `znRsTerm_iso_false` (**NO-GO for the term branch** at an isolated fixed restart with `O(λ) > ρ_λ`).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Zn

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.OT

variable {S : InaccSeq.{0}}

/-- `Θ_μ(m_μ) ≤ O(μ)`. -/
theorem zn_theta_le_O (μ : Ordinal.{0}) : cdTheta S μ (cdCode S μ) ≤ Ys.ysO S μ := by
  have h1 := Zh.zhR_ge_theta (S := S) μ
  rw [← Ys.ysO_eq S μ] at h1
  exact (add_le_add_iff_left _).1 h1

/-- **The offset is at most the code** at every restart `μ > ω²` with a name. -/
theorem zn_cL_le_code {μ η1 : Ordinal.{0}} (hμ : IsRestartIdx μ) (hww : ω * ω < μ)
    (hn : upsilon μ < Nm.Pv S η1) : cL μ ≤ cdCode S μ := by
  rcases eq_or_lt_of_le (upsilon_normal.strictMono.le_apply (x := μ)) with he | hfix
  · have := Fx.fxCode_fix hμ he.symm hn
    exact (cL_le_ups hμ).trans (by rw [← he]; exact this)
  · exact (Zh.zh_code_cL hμ hww hfix hn).ge

/-- **The bound is at least the offset**: `c(μ) ≤ O(μ)`. -/
theorem znO_ge_cL {μ η1 : Ordinal.{0}} (hμ : IsRestartIdx μ) (hww : ω * ω < μ)
    (hn : upsilon μ < Nm.Pv S η1) : cL μ ≤ Ys.ysO S μ := by
  have h1 : cdTheta S μ (cL μ) = cL μ := cdTheta_small S (cL_le_ups hμ)
  calc cL μ = cdTheta S μ (cL μ) := h1.symm
    _ ≤ cdTheta S μ (cdCode S μ) := cdTheta_mono S μ (zn_cL_le_code hμ hww hn)
    _ ≤ Ys.ysO S μ := zn_theta_le_O μ

/-- **`c(λ) = λ` at a `υ`-fixed restart.** -/
theorem zn_cL_fix {l : Ordinal.{0}} (hl : IsRestartIdx l) (hfix : upsilon l = l) : cL l = l := by
  obtain ⟨hE, -, hww⟩ := Cp.cp_fix_facts hl hfix
  have hωl : ω ≤ l := (le_mul_left _ omega0_pos).trans hww.le
  refine le_antisymm (by have := cL_le_ups hl; rwa [hfix] at this) (le_cL hl.1 ?_)
  rw [one_add_of_omega0_le hωl, hE]

/-- `Θ_λ(m_λ) ≥ ρ_λ` at a `υ`-fixed restart with a name. -/
theorem zn_theta_ge_fix {l η1 : Ordinal.{0}} (hl : IsRestartIdx l) (hfix : upsilon l = l)
    (hn : upsilon l < Nm.Pv S η1) : upsilon l ≤ cdTheta S l (cdCode S l) := by
  calc upsilon l = cdTheta S l (upsilon l) := (cdTheta_small S le_rfl).symm
    _ ≤ cdTheta S l (cdCode S l) := cdTheta_mono S l (hfix.symm ▸ Fx.fxCode_fix hl hfix hn)

/-- **The RS input at a `υ`-fixed restart with a short reading** `Θ_λ(m_λ) ≤ ρ_λ` (below `ν_C`): the term
input with constant terms. -/
theorem znRsIn_fixShort {l η1 : Ordinal.{0}} (hl : IsRestartIdx l) (hfix : upsilon l = l)
    (hν : upsilon l < nuC) (hn : upsilon l < Nm.Pv S η1)
    (hθ : cdTheta S l (cdCode S l) ≤ upsilon l) : Zc.ZcRsIn (Ys.ysO S) l := by
  obtain ⟨hE, -, hww⟩ := Cp.cp_fix_facts hl hfix
  have hρδ : upsilon l < cdDelta l :=
    upsilon_normal.strictMono (lt_of_lt_of_le (lt_add_of_pos_right l omega0_pos) le_self_add)
  have hR := Zh.zhR_short_theta hl hν (hθ.trans_lt hρδ)
  have hθeq : cdTheta S l (cdCode S l) = upsilon l := le_antisymm hθ (zn_theta_ge_fix hl hfix hn)
  have hO : Ys.ysO S l = l := by
    unfold Ys.ysO
    rw [hR, hθeq, hfix]
    exact Ordinal.add_sub_cancel _ _
  have hcL := zn_cL_fix hl hfix
  have h1l : (1 : Ordinal.{0}) < l :=
    lt_of_le_of_lt (Order.one_le_iff_pos.2 (mul_pos omega0_pos omega0_pos)) hww
  have h2l : (2 : Ordinal.{0}) ≤ l := by
    have : (2 : Ordinal.{0}) < ω := by exact_mod_cast natCast_lt_omega0 2
    exact (this.trans_le ((le_mul_left _ omega0_pos).trans hww.le)).le
  refine Or.inr (Or.inr ⟨by rw [hcL]; exact h2l, by rw [hO]; exact h1l.le, fun z hz => ?_⟩)
  rw [hO] at hz
  refine ⟨OT.k z, show z < upsilon l by rw [hfix]; exact hz, le_rfl, fun ν hν' => ?_⟩
  have hz1 : max z 1 < cL l := by rw [hcL]; exact max_lt hz h1l
  obtain ⟨μ, hμ, hνμ, hμl, hzμ⟩ :=
    cL_dense hl (le_max_right _ _) hz1 (max ν (ω * ω)) (max_lt hν' hww)
  have hwwμ : ω * ω < μ := (le_max_right _ _).trans_lt hνμ
  have hnμ : upsilon μ < Nm.Pv S η1 := (upsilon_normal.strictMono hμl).trans hn
  refine ⟨μ, hμ, (le_max_left _ _).trans_lt hνμ, hμl, ?_⟩
  show z ≤ Ys.ysO S μ
  exact (le_max_left _ _).trans (hzμ.trans (znO_ge_cL hμ hwwμ hnμ))

theorem zn_two_lt_omega : (2 : Ordinal.{0}) < ω := by exact_mod_cast natCast_lt_omega0 2

/-- `ω + 2 < ω²`. -/
theorem zn_omega_add_two_lt : ω + 2 < ω ^ (2 : Ordinal.{0}) := by
  have hP := isPrincipal_add_omega0_opow (2 : Ordinal.{0})
  have h1 : ω < ω ^ (2 : Ordinal.{0}) := by
    have := (opow_lt_opow_iff_right one_lt_omega0).2 (one_lt_two (α := Ordinal.{0}))
    rwa [opow_one] at this
  exact hP h1 (zn_two_lt_omega.trans h1)

/-- **CapV at a short reading**: `Θ_λ(m_λ) < δ_λ`, `2 ≤ e(η_λ)`, `ρ_λ < ν_C`. -/
theorem znCapV_theta {l η1 : Ordinal.{0}} (hl : IsRestartIdx l) (hν : upsilon l < nuC)
    (hn : upsilon l < Nm.Pv S η1) (hθ : cdTheta S l (cdCode S l) < cdDelta l)
    (he2 : 2 ≤ cdExp (cdEta S l)) : CdCapV S l := by
  have hm := upsilon_normal.strictMono
  obtain ⟨hg, hι, -, hpv⟩ := cdEta_pv_spec (S := S) hl.1 hn
  have hR := Zh.zhR_short_theta hl hν hθ
  have hww : ω * ω < upsilon l := Zc.zcWW_lt hl
  have hW2 : ω ^ (2 : Ordinal.{0}) = ω * ω := by
    rw [show (2 : Ordinal.{0}) = ((2 : ℕ) : Ordinal.{0}) by norm_num, opow_natCast, pow_two]
  have hx : ω + 2 < Nm.Pv S (cdEta S l) := by
    rw [hpv]; exact zn_omega_add_two_lt.trans (hW2 ▸ hww)
  have hxe : ω + 2 ≤ ω ^ cdExp (cdEta S l) :=
    zn_omega_add_two_lt.le.trans (opow_le_opow_right omega0_pos he2)
  have hcap : upsilon (l + (ω + 2)) ≤ cdCapB S l := by
    have h := Bt.ups_iota S (cdEta S l + (ω + 2))
    rw [Cp.cpIota_add hg hx, hι] at h
    have e : Nm.Pv S (cdEta S l + (ω + 2)) = upsilon (l + (ω + 2)) := h.symm
    unfold cdCapB
    rw [← e]
    exact Nm.Pv_mono (add_le_add le_rfl hxe)
  unfold CdCapV
  rw [hR]
  refine lt_of_lt_of_le ?_ hcap
  have hlt : l + ω + 1 < l + (ω + 2) := by
    rw [← add_assoc]
    exact (add_lt_add_iff_left _).2 (by exact_mod_cast (show (1 : ℕ) < 2 by norm_num))
  have hpos : 0 < l + (ω + 2) := lt_of_le_of_lt zero_le hlt
  have hI := indec_of_upsPt (upsPt_upsilon hpos)
  exact hI.add_lt (hm hlt) (hθ.trans (hm hlt))

/-- **CapV at a `υ`-fixed restart with a short reading** `Θ_λ(m_λ) < δ_λ` (below `ν_C`). -/
theorem znCapV_fixTh {l η1 : Ordinal.{0}} (hl : IsRestartIdx l) (hfix : upsilon l = l)
    (hν : upsilon l < nuC) (hn : upsilon l < Nm.Pv S η1)
    (hθ : cdTheta S l (cdCode S l) < cdDelta l) : CdCapV S l := by
  obtain ⟨-, -, hww⟩ := Cp.cp_fix_facts hl hfix
  have he := Fx.fxExp_fix hl hfix hn
  have h2 : (2 : Ordinal.{0}) ≤ l := (zn_two_lt_omega.trans_le ((le_mul_left _ omega0_pos).trans hww.le)).le
  exact znCapV_theta hl hν hn hθ (h2.trans he)

/-- **NO-GO for the supply branch at an isolated fixed restart**: if every restart `μ` with
`x₀ < ρ_μ < ρ_λ` is no `υ`-fixed point, `υ_{ω²} ≤ x₀ < ρ_λ`, `ρ_λ < ν_C`, `ρ_λ < P(η₁)` and
`Θ_λ(m_λ) > 0`, then `Zh.ZhSupInB S λ B` is false. -/
theorem znSupInB_false {l B x0 η1 : Ordinal.{0}} (hν : upsilon l < nuC) (hn : upsilon l < Nm.Pv S η1)
    (hpos : 0 < cdTheta S l (cdCode S l)) (hx0 : upsilon (ω * ω) ≤ x0) (hx0l : x0 < upsilon l)
    (hiso : ∀ μ, IsRestartIdx μ → x0 < upsilon μ → upsilon μ < upsilon l → μ < upsilon μ) :
    ¬ Zh.ZhSupInB S l B := by
  rintro ⟨β, -, hr, hsup⟩
  have hm := upsilon_normal.strictMono
  have hδr : cdDelta l < cdR S l :=
    lt_of_lt_of_le (lt_add_of_pos_right _ hpos) (Zh.zhR_ge_theta (S := S) l)
  rcases le_or_gt β (ω + 1) with hβ | hβ
  · have : upsilon (l + β) ≤ cdDelta l := by
      unfold cdDelta; rw [add_assoc]; exact hm.monotone (add_le_add le_rfl hβ)
    exact absurd (hr.trans this) (not_le.2 hδr)
  · have hβ2 : ω + 2 ≤ β := by
      rw [show (ω + 2 : Ordinal.{0}) = ω + 1 + 1 by rw [add_assoc]; norm_num]
      exact Order.add_one_le_of_lt hβ
    obtain ⟨μ, hR, h1, h2, -, -, h6⟩ := hsup x0 hx0l
    have hww : ω * ω < μ := hm.lt_iff_lt.1 (lt_of_le_of_lt hx0 h1)
    have hfixμ := hiso μ hR.1 h1 h2
    have hRμ := Zh.zhR_nonfix hR.1 hww hfixμ (h2.trans hν) (h2.trans hn)
    have hlt : μ + ω + 1 < μ + (ω + 2) := by
      rw [← add_assoc]
      exact (add_lt_add_iff_left _).2 (by exact_mod_cast (show (1 : ℕ) < 2 by norm_num))
    have hpos' : 0 < μ + (ω + 2) := lt_of_le_of_lt zero_le hlt
    have hI := indec_of_upsPt (upsPt_upsilon hpos')
    have hρδμ : upsilon μ < cdDelta μ :=
      hm (lt_of_lt_of_le (lt_add_of_pos_right μ omega0_pos) le_self_add)
    have hsmall : cdDelta μ + cL μ < upsilon (μ + (ω + 2)) :=
      hI.add_lt (hm hlt) (((cL_le_ups hR.1).trans_lt hρδμ).trans (hm hlt))
    have hbig : upsilon (μ + (ω + 2)) ≤ cdDelta μ + cL μ :=
      (hm.monotone (add_le_add le_rfl hβ2)).trans (hRμ ▸ h6)
    exact absurd hbig (not_le.2 hsmall)

/-- The value of an offset term with constants below an `ε`-number `ρ` reaches `ρ` only through a node
`ω^{x+t}`, and then its value at every `ε`-number `y` is at least `y`. -/
theorem zn_ev_ge {ρ : Ordinal.{0}} (hρ : Indec ρ) :
    ∀ s : OT, CB s ρ → ρ ≤ ev s ρ → ∀ y, InE y → y ≤ ev s y := by
  intro s
  induction s with
  | k a => intro hs hle; exact absurd hle (not_le.2 hs)
  | xw s _ =>
    intro _ _ y hy
    show y ≤ ω ^ (y + ev s y)
    calc y = ω ^ y := hy.symm
      _ ≤ ω ^ (y + ev s y) := opow_le_opow_right omega0_pos le_self_add
  | add s u ihs ihu =>
    intro hs hle y hy
    show y ≤ ev s y + ev u y
    by_cases h1 : ρ ≤ ev s ρ
    · exact (ihs hs.1 h1 y hy).trans le_self_add
    · by_cases h2 : ρ ≤ ev u ρ
      · exact (ihu hs.2 h2 y hy).trans le_add_self
      · exact absurd hle (not_le.2 (hρ.add_lt (not_le.1 h1) (not_le.1 h2)))

/-- `O(μ) = c(μ)` at a non-fixed restart below `ν_C`. -/
theorem zn_O_nonfix {μ η1 : Ordinal.{0}} (hμ : IsRestartIdx μ) (hww : ω * ω < μ) (hfix : μ < upsilon μ)
    (hν : upsilon μ < nuC) (hn : upsilon μ < Nm.Pv S η1) : Ys.ysO S μ = cL μ := by
  have hR := Zh.zhR_nonfix hμ hww hfix hν hn
  unfold Ys.ysO
  rw [hR]
  exact Ordinal.add_sub_cancel _ _

/-- `c(μ) < ρ_μ` at a non-fixed restart. -/
theorem zn_cL_lt_nonfix {μ : Ordinal.{0}} (hμ : IsRestartIdx μ) (hfix : μ < upsilon μ) :
    cL μ < upsilon μ := by
  rw [Zh.zh_cL_eq hμ]
  exact ((cdOff_le _).trans (Cp.cpExp_le hμ.1)).trans_lt hfix

/-- **NO-GO for the term branch at an isolated fixed restart**: if every restart `μ` with `x₀ < ρ_μ < ρ_λ` is
no `υ`-fixed point (`υ_{ω²} ≤ x₀ < ρ_λ`, `ρ_λ < ν_C`, `ρ_λ < P(η₁)`) and `ρ_λ < O(λ)`, the term input fails at
`z = ρ_λ`: a term reaching `ρ_λ` has value `≥ ρ_μ > c(μ) = O(μ)` at every `ρ_μ`. -/
theorem znRsTerm_iso_false {l x0 η1 : Ordinal.{0}} (hl : IsRestartIdx l) (hν : upsilon l < nuC)
    (hn : upsilon l < Nm.Pv S η1) (hx0 : upsilon (ω * ω) ≤ x0) (hx0l : x0 < upsilon l)
    (hiso : ∀ μ, IsRestartIdx μ → x0 < upsilon μ → upsilon μ < upsilon l → μ < upsilon μ)
    (hlong : upsilon l < Ys.ysO S l) : ¬ Zc.ZcRsTerm (Ys.ysO S) l := by
  intro h
  have hm := upsilon_normal.strictMono
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have hρI := indec_of_upsPt (upsPt_upsilon hl0)
  obtain ⟨t, ht, hzt, hcof⟩ := h (upsilon l) hlong
  have hlim : IsSuccLimit l := by
    obtain ⟨q, hq⟩ := (ri_iff.1 hl).2
    have hq0 : q ≠ 0 := by intro h0; rw [h0, mul_zero] at hq; exact hl.1 hq
    rw [hq]
    exact isSuccLimit_mul_left (isSuccLimit_mul_right omega0_pos isSuccLimit_omega0)
      (pos_iff_ne_zero.2 hq0)
  obtain ⟨_, ⟨ι, hι, rfl⟩, hxι⟩ := (lt_isLUB_iff (upsilon_limit hlim)).1 hx0l
  obtain ⟨μ, hμ, hιμ, hμl, hle⟩ := hcof ι hι
  have h1 : x0 < upsilon μ := hxι.trans (hm hιμ)
  have h2 : upsilon μ < upsilon l := hm hμl
  have hww : ω * ω < μ := hm.lt_iff_lt.1 (lt_of_le_of_lt hx0 h1)
  have hfixμ := hiso μ hμ h1 h2
  have hO := zn_O_nonfix hμ hww hfixμ (h2.trans hν) (h2.trans hn)
  have hμ0 : 0 < μ := lt_of_le_of_lt zero_le hww
  have hge := zn_ev_ge hρI t ht hzt (upsilon μ) (upsPt_inE (upsPt_upsilon hμ0))
  rw [hO] at hle
  exact absurd (hge.trans hle) (not_le.2 (zn_cL_lt_nonfix hμ hfixμ))

/-- **The reach at a far-but-short reading**: `Θ_λ(m_λ) < δ_λ·ω`, `ρ_λ < ν_C` give `r(λ) = δ_λ + Θ_λ(m_λ)`
(`Wd.wdk_eq`, `δ_λ < υ_{λ+ω²} ≤ ν_C`). -/
theorem znR_thetaW {l : Ordinal.{0}} (hl : IsRestartIdx l) (hν : upsilon l < nuC)
    (hθ : cdTheta S l (cdCode S l) < cdDelta l * ω) :
    cdR S l = cdDelta l + cdTheta S l (cdCode S l) := by
  have hm := upsilon_normal.strictMono
  have hδW : cdDelta l < upsilon (l + ω * ω) := hm (by simpa using idx_lt l 0 1)
  have hC : cdDelta l < nuC := hδW.trans_le (Yx.yxNext_le_nuC hl hν)
  unfold cdR cdRc
  exact Wd.wdk_eq hl hC hθ

/-- **CapV at a reading below `δ_λ·ω`**: `Θ_λ(m_λ) < δ_λ·ω`, `2 ≤ e(η_λ)`, `ρ_λ < ν_C` give
`r(λ) = δ_λ + Θ_λ(m_λ) < δ_λ·ω ≤ υ_{λ+ω+2} ≤ P(η_λ + ω^e)`. -/
theorem znCapV_thetaW {l η1 : Ordinal.{0}} (hl : IsRestartIdx l) (hν : upsilon l < nuC)
    (hn : upsilon l < Nm.Pv S η1) (hθ : cdTheta S l (cdCode S l) < cdDelta l * ω)
    (he2 : 2 ≤ cdExp (cdEta S l)) : CdCapV S l := by
  have hm := upsilon_normal.strictMono
  obtain ⟨hg, hι, -, hpv⟩ := cdEta_pv_spec (S := S) hl.1 hn
  have hR := znR_thetaW hl hν hθ
  have hww : ω * ω < upsilon l := Zc.zcWW_lt hl
  have hW2 : ω ^ (2 : Ordinal.{0}) = ω * ω := by
    rw [show (2 : Ordinal.{0}) = ((2 : ℕ) : Ordinal.{0}) by norm_num, opow_natCast, pow_two]
  have hx : ω + 2 < Nm.Pv S (cdEta S l) := by
    rw [hpv]; exact zn_omega_add_two_lt.trans (hW2 ▸ hww)
  have hxe : ω + 2 ≤ ω ^ cdExp (cdEta S l) :=
    zn_omega_add_two_lt.le.trans (opow_le_opow_right omega0_pos he2)
  have hcap : upsilon (l + (ω + 2)) ≤ cdCapB S l := by
    have h := Bt.ups_iota S (cdEta S l + (ω + 2))
    rw [Cp.cpIota_add hg hx, hι] at h
    have e : Nm.Pv S (cdEta S l + (ω + 2)) = upsilon (l + (ω + 2)) := h.symm
    unfold cdCapB
    rw [← e]
    exact Nm.Pv_mono (add_le_add le_rfl hxe)
  have hlt : l + ω + 1 < l + (ω + 2) := by
    rw [← add_assoc]
    exact (add_lt_add_iff_left _).2 (by exact_mod_cast (show (1 : ℕ) < 2 by norm_num))
  have hpos : 0 < l + (ω + 2) := lt_of_le_of_lt zero_le hlt
  have hI := indec_of_upsPt (upsPt_upsilon hpos)
  have hδI := Wd.wdDelta_indec hl
  have hmw : cdDelta l * ω ≤ upsilon (l + (ω + 2)) := Wd.wd_mulw_le hδI hI (hm hlt)
  unfold CdCapV
  rw [hR]
  exact ((Wd.wd_add_lt_mulw hδI hθ).trans_le hmw).trans_le hcap

/-- **CapV at a `υ`-fixed restart with a reading below `δ_λ·ω`** (below `ν_C`). -/
theorem znCapV_fixThW {l η1 : Ordinal.{0}} (hl : IsRestartIdx l) (hfix : upsilon l = l)
    (hν : upsilon l < nuC) (hn : upsilon l < Nm.Pv S η1)
    (hθ : cdTheta S l (cdCode S l) < cdDelta l * ω) : CdCapV S l := by
  obtain ⟨-, -, hww⟩ := Cp.cp_fix_facts hl hfix
  have he := Fx.fxExp_fix hl hfix hn
  have h2 : (2 : Ordinal.{0}) ≤ l := (zn_two_lt_omega.trans_le ((le_mul_left _ omega0_pos).trans hww.le)).le
  exact znCapV_thetaW hl hν hn hθ (h2.trans he)

/-- **The value input cannot pass `υ_{λ+1}`**: if `υ_{λ+1} < O(λ)`, `ZnRsVal O λ` is false. -/
theorem znRsVal_false {O : Ordinal.{0} → Ordinal.{0}} {l : Ordinal.{0}} (h : upsilon (succ l) < O l) :
    ¬ ZnRsVal O l := by
  intro hv
  obtain ⟨v, hzv, hv1, -⟩ := hv _ h
  exact absurd hzv (not_le.2 hv1)

/-- **The code continuity at `λ`** (a statement on the readings and the base change only): every
`z < Θ_λ(m_λ)` is below a value `v < υ_{λ+1}` with `π_{ρ_μ, ρ_λ}(v) ≤ Θ_μ(m_μ)` at restarts `μ` cofinal
below `λ`. -/
def ZnThCont (S : InaccSeq.{0}) (l : Ordinal.{0}) : Prop :=
  ∀ z < cdTheta S l (cdCode S l), ∃ v, z ≤ v ∧ v < upsilon (succ l) ∧
    ∀ ν < l, ∃ μ, IsRestartIdx μ ∧ ν < μ ∧ μ < l ∧
      pi (upsilon μ) (upsilon l) v ≤ cdTheta S μ (cdCode S μ)

/-- **The code continuity gives the value input** (`Θ_λ(m_λ) < δ_λ·ω`, `ρ_λ < ν_C`: `O(λ) = Θ_λ(m_λ)`, and
`Θ_μ(m_μ) ≤ O(μ)`). -/
theorem znVal_of_cont {l : Ordinal.{0}} (hl : IsRestartIdx l) (hν : upsilon l < nuC)
    (hθ : cdTheta S l (cdCode S l) < cdDelta l * ω) (hc : ZnThCont S l) : ZnRsVal (Ys.ysO S) l := by
  have hO : Ys.ysO S l = cdTheta S l (cdCode S l) := by
    unfold Ys.ysO
    rw [znR_thetaW hl hν hθ]
    exact Ordinal.add_sub_cancel _ _
  intro z hz
  rw [hO] at hz
  obtain ⟨v, h1, h2, h3⟩ := hc z hz
  refine ⟨v, h1, h2, fun ν hν' => ?_⟩
  obtain ⟨μ, hμ, a, b, hle⟩ := h3 ν hν'
  exact ⟨μ, hμ, a, b, hle.trans (zn_theta_le_O μ)⟩

/-- **The reading is onto an initial segment**: `z < Θ_λ(m)` ⇒ `z ≤ Θ_λ(c)` for a hull element `c < m`. -/
theorem zn_otp_surj {C : Set Ordinal.{0}} {m z : Ordinal.{0}} (hz : z < cdOtp C m) :
    ∃ c ∈ C, c < m ∧ z ≤ cdOtp C c := by
  have hm0 : 0 < m := by
    by_contra h0
    rw [not_lt, nonpos_iff_eq_zero] at h0
    rw [h0] at hz
    exact absurd (hz.trans_le (cdOtp_le_self C 0)) (not_lt.2 zero_le)
  haveI : Nonempty (Iio m) := ⟨⟨0, hm0⟩⟩
  rw [cdOtp_eq C m] at hz
  obtain ⟨⟨c, hc⟩, hzc⟩ := exists_lt_of_lt_ciSup hz
  by_cases hC : c ∈ C
  · simp only [hC, if_true] at hzc
    exact ⟨c, hC, hc, Order.lt_add_one_iff.1 hzc⟩
  · simp only [hC, if_false] at hzc
    exact absurd hzc (not_lt.2 zero_le)

/-- **The code continuity from the hull**: if for every hull code `c < m_λ` the restarts `μ` with
`π_{ρ_μ, ρ_λ}(Θ_λ(c)) ≤ Θ_μ(m_μ)` are cofinal below `λ`, and `Θ_λ(m_λ) ≤ υ_{λ+1}`, then `ZnThCont S λ`. -/
theorem znThCont_of_code {l : Ordinal.{0}} (hθ : cdTheta S l (cdCode S l) ≤ upsilon (succ l))
    (h : ∀ c ∈ cdHull S l, c < cdCode S l → ∀ ν < l, ∃ μ, IsRestartIdx μ ∧ ν < μ ∧ μ < l ∧
      pi (upsilon μ) (upsilon l) (cdTheta S l c) ≤ cdTheta S μ (cdCode S μ)) : ZnThCont S l := by
  intro z hz
  obtain ⟨c, hcH, hcm, hzc⟩ := zn_otp_surj hz
  refine ⟨cdTheta S l c, hzc, lt_of_lt_of_le (cdOtp_lt_of_mem hcH hcm) hθ, h c hcH hcm⟩

/-- **NO-GO for the value branch at an isolated fixed restart**: if every restart `μ` with `x₀ < ρ_μ < ρ_λ` is
no `υ`-fixed point (`υ_{ω²} ≤ x₀ < ρ_λ`, `ρ_λ < ν_C`, `ρ_λ < P(η₁)`) and `ρ_λ < O(λ)`, the value input fails
at `z = ρ_λ`: a value `v ∈ [ρ_λ, υ_{λ+1})` has `π_{ρ_μ, ρ_λ}(v) ≥ π(ρ_λ) = ρ_μ > c(μ) = O(μ)` once `ρ_μ` is
above the parameters of `v`. -/
theorem znRsVal_iso_false {l x0 η1 : Ordinal.{0}} (hl : IsRestartIdx l) (hν : upsilon l < nuC)
    (hn : upsilon l < Nm.Pv S η1) (hx0 : upsilon (ω * ω) ≤ x0) (hx0l : x0 < upsilon l)
    (hiso : ∀ μ, IsRestartIdx μ → x0 < upsilon μ → upsilon μ < upsilon l → μ < upsilon μ)
    (hlong : upsilon l < Ys.ysO S l) : ¬ ZnRsVal (Ys.ysO S) l := by
  classical
  intro h
  have hm := upsilon_normal.strictMono
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have hρU : UpsPt (upsilon l) := upsPt_upsilon hl0
  have hρE : InE (upsilon l) := upsPt_inE hρU
  obtain ⟨v, hρv, hv, hcof⟩ := h (upsilon l) hlong
  have hnx := upsilon_isNext l
  have hs1 : upsilon (succ l) < Om1 :=
    ((hm (show succ l < l + ω * ω by
      rw [Order.succ_eq_add_one]
      exact (add_lt_add_iff_left l).2 (lt_of_lt_of_le one_lt_omega0 (le_mul_left ω omega0_pos)))).trans_le
      (Yx.yxNext_le_nuC hl hν)).trans_le nuC_le_Om1
  have hρ1 : upsilon l < Om1 := hnx.1.trans hs1
  have hseg : InSeg (upsilon l) v := ⟨hρv, hv.trans hs1, fun u hu hu' => lt_of_lt_of_le hv (hnx.2.2 u hu hu')⟩
  have hvT : v ∈ Tset (upsilon l) := ((inSeg_iff hρU hρ1).1 hseg).2.2
  have hPar := Par_sub hρE hρ1 hvT
  set m : Ordinal.{0} := (insert x0 (Par (upsilon l) v)).sup id with hmdef
  have hmρ : m < upsilon l := by
    rw [hmdef, Finset.sup_lt_iff hρU.1]
    intro b hb
    rcases Finset.mem_insert.1 hb with rfl | hb
    · exact hx0l
    · exact hPar (Finset.mem_coe.2 hb)
  have hlim : IsSuccLimit l := by
    obtain ⟨q, hq⟩ := (ri_iff.1 hl).2
    have hq0 : q ≠ 0 := by intro h0; rw [h0, mul_zero] at hq; exact hl.1 hq
    rw [hq]
    exact isSuccLimit_mul_left (isSuccLimit_mul_right omega0_pos isSuccLimit_omega0)
      (pos_iff_ne_zero.2 hq0)
  obtain ⟨_, ⟨ι, hι, rfl⟩, hmι⟩ := (lt_isLUB_iff (upsilon_limit hlim)).1 hmρ
  obtain ⟨μ, hμ, hιμ, hμl, hle⟩ := hcof ι hι
  have hmμ : m < upsilon μ := hmι.trans (hm hιμ)
  have h1 : x0 < upsilon μ :=
    lt_of_le_of_lt (Finset.le_sup (f := id) (Finset.mem_insert_self x0 _)) hmμ
  have h2 : upsilon μ < upsilon l := hm hμl
  have hww : ω * ω < μ := hm.lt_iff_lt.1 (lt_of_le_of_lt hx0 h1)
  have hfixμ := hiso μ hμ h1 h2
  have hO := zn_O_nonfix hμ hww hfixμ (h2.trans hν) (h2.trans hn)
  have hμ0 : 0 < μ := lt_of_le_of_lt zero_le hww
  have hB : Bases (upsilon μ) (upsilon l) := ⟨upsPt_inE (upsPt_upsilon hμ0), hρE, h2, hρ1⟩
  have hvTB : v ∈ TB (upsilon l) (upsilon μ) := ⟨hvT, fun p hp =>
    lt_of_le_of_lt (Finset.le_sup (f := id) (Finset.mem_insert_of_mem (Finset.mem_coe.1 hp))) hmμ⟩
  have hb := pi_base hB
  have hS : ({upsilon l, v} : Set Ordinal.{0}) ⊆ TB (upsilon l) (upsilon μ) := by
    intro x hx
    rcases hx with rfl | rfl
    · exact hb.1
    · exact hvTB
  have hmono := (down_mono hB hS).monotoneOn (by simp) (by simp) hρv
  rw [hb.2] at hmono
  rw [hO] at hle
  exact absurd (hmono.trans hle) (not_le.2 (zn_cL_lt_nonfix hμ hfixμ))

/-- An isolated fixed restart (`Cp.CpIso`) gives the bound `x₀` of the no-go lemmas. -/
theorem zn_iso_x0 {l : Ordinal.{0}} (hl : IsRestartIdx l) (hfix : upsilon l = l) (hiso : Cp.CpIso l) :
    ∃ x0, upsilon (ω * ω) ≤ x0 ∧ x0 < upsilon l ∧
      ∀ μ, IsRestartIdx μ → x0 < upsilon μ → upsilon μ < upsilon l → μ < upsilon μ := by
  have hm := upsilon_normal.strictMono
  obtain ⟨-, -, hww⟩ := Cp.cp_fix_facts hl hfix
  obtain ⟨ν, hνl, hν⟩ := hiso
  refine ⟨max (upsilon (ω * ω)) (upsilon ν), le_max_left _ _, max_lt (hm hww) (hm hνl), ?_⟩
  intro μ hμ h1 h2
  exact hν μ hμ (hm.lt_iff_lt.1 ((le_max_right _ _).trans_lt h1)) (hm.lt_iff_lt.1 h2)

/-- **At an isolated fixed restart with a long reading the RS input is LOWER**: if `Cp.CpIso λ`,
`ρ_λ < Θ_λ(m_λ)`, `ρ_λ < ν_C`, `ρ_λ < P(η₁)`, then `ZcRsIn ∨ ZhSupInB ∨ ZnRsVal` gives LOWER at `λ` (the supply,
term, value and successor branches are all false there). -/
theorem znIn_iso_lower {l B η1 : Ordinal.{0}} (hl : IsRestartIdx l) (hfix : upsilon l = l)
    (hiso : Cp.CpIso l) (hν : upsilon l < nuC) (hn : upsilon l < Nm.Pv S η1)
    (hθ : upsilon l < cdTheta S l (cdCode S l))
    (h : Zc.ZcRsIn (Ys.ysO S) l ∨ Zh.ZhSupInB S l B ∨ ZnRsVal (Ys.ysO S) l) : CdLower S l := by
  obtain ⟨x0, hx0, hx0l, hiso'⟩ := zn_iso_x0 hl hfix hiso
  have hO : upsilon l < Ys.ysO S l := hθ.trans_le (zn_theta_le_O l)
  have hpos : 0 < cdTheta S l (cdCode S l) := lt_of_le_of_lt zero_le hθ
  rcases h with (h | ⟨h2, -⟩ | ⟨-, -, ht⟩) | h | h
  · unfold CdLower; rw [← Ys.ysO_eq S l]; exact h
  · obtain ⟨-, -, hww⟩ := Cp.cp_fix_facts hl hfix
    rw [zn_cL_fix hl hfix] at h2
    have : (2 : Ordinal.{0}) < l := zn_two_lt_omega.trans_le ((le_mul_left _ omega0_pos).trans hww.le)
    exact absurd h2 (not_lt.2 this.le)
  · exact absurd ht (znRsTerm_iso_false hl hν hn hx0 hx0l hiso' hO)
  · exact absurd h (znSupInB_false hν hn hpos hx0 hx0l hiso')
  · exact absurd h (znRsVal_iso_false hl hν hn hx0 hx0l hiso' hO)

/-- **The code statement at the isolated fixed restarts of `(l₀, B)`**: `Θ_λ(m_λ) ≤ ρ_λ` (e.g. `m_λ ≤ Ω₁`, as at
the isolated fixed points below `cpB1`, `Cp.cpFix_code`). -/
def ZnIsoCode (S : InaccSeq.{0}) (l0 B : Ordinal.{0}) : Prop :=
  ∀ l, IsRestartIdx l → l0 < l → l < B → upsilon l = l → Cp.CpIso l →
    cdTheta S l (cdCode S l) ≤ upsilon l

/-- `m_λ ≤ Ω₁` gives the code statement at `λ` (`Θ_λ(Ω₁) = ρ_λ`). -/
theorem zn_theta_le_of_code {l η1 : Ordinal.{0}} (hl : IsRestartIdx l) (hn : upsilon l < Nm.Pv S η1)
    (hc : cdCode S l ≤ Om 1) : cdTheta S l (cdCode S l) ≤ upsilon l := by
  have hpv : Nm.Pv S (cdEta S l) = upsilon l := (cdEta_pv_spec (S := S) hl.1 hn).2.2.2
  calc cdTheta S l (cdCode S l) ≤ cdTheta S l (Om 1) := cdTheta_mono S l hc
    _ = upsilon l := cdTheta_Om1 hpv

/-- **The code statement from the last exponent**: if every isolated fixed restart of `(l₀, B)` has a name with
`e(η_λ) ≤ Ω₁` (as `η_F = η₀ + Ω₁` at the first fixed point after `η₀`), then `ZnIsoCode S l₀ B` (the code is at
most the exponent, `Cd.cdCodeOf_le_exp`). -/
theorem znIsoCode_of_exp {l0 B η1 : Ordinal.{0}} (hB : ∀ l, l < B → upsilon l < Nm.Pv S η1)
    (he : ∀ l, IsRestartIdx l → l0 < l → l < B → upsilon l = l → Cp.CpIso l → cdExp (cdEta S l) ≤ Om 1) :
    ZnIsoCode S l0 B := by
  intro l hl h1 h2 hfix hiso
  exact zn_theta_le_of_code hl (hB l h2) ((cdCodeOf_le_exp S _).trans (he l hl h1 h2 hfix hiso))

end Googology.Trans.PoR.InaccPsi.R2.Zn
