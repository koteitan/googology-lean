import Googology.Trans.PoR.InaccPsi.R2.HlLv
import Googology.Trans.PoR.InaccPsi.R2.Exact

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hm

open Ordinal Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
open Googology.Trans.PoR.InaccPsi.R2.Mx
open Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Gv
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Gw
  Googology.Trans.PoR.InaccPsi.R2.Rj Googology.Trans.PoR.InaccPsi.R2.Lu

/-- The first union level after Ω₁·q for q < Ω₁: the endpoint Ω₁², read as x·x. -/
noncomputable def hmL : Ordinal.{0} := Om 1 * Om 1

/-- The cube cutoff still excludes the `G` atom: multiply the known
`Ω₁² < G` and `Ω₁ < G` bounds inside the epsilon number `G`. -/
theorem hmSq_lt_G : Om 1 * Om 1 * Om 1 < Gc.gcG 0 := by
  have h2 : Om 1 * Om 1 < Gc.gcG 0 := Gw.gw_OmOm_lt_G
  have h1 : Om 1 < Gc.gcG 0 := Gc.gcG_Om1_lt 0
  simpa [mul_assoc] using
    (InE.mul_lt (Low.opow_eq_self_of_SC (Gc.gcG_SC 0)) h2 h1)

/-- Taking the remainder below Ω₁² preserves the G-code grammar. A principal
Veblen term above Ω₁² is divisible by Ω₁²; sums are handled by the usual
principal-remainder calculation. -/
theorem hmSq_cl_mod {Z : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om 1) {y : Ordinal.{0}}
    (h : GxCl Z {Gc.gcG 0} y) : GxCl Z {Gc.gcG 0} (y % (Om 1 * Om 1)) := by
  let B : Ordinal.{0} := Om 1 * Om 1
  have hB0 : 0 < B := mul_pos Gw.gw_Om_pos Gw.gw_Om_pos
  have hBne : B ≠ 0 := hB0.ne'
  have hBpow : B = ω ^ (Om 1 + Om 1) := by
    dsimp [B]
    exact Gw.gw_OmOm_eq
  have hBp : IsPrincipal (· + ·) B := by
    dsimp [B]
    rw [Gw.gw_OmOm_eq]
    exact isPrincipal_add_omega0_opow _
  have hBg : B < Gc.gcG 0 := Gw.gw_OmOm_lt_G
  induction h with
  | @small x hx =>
    have h1 : Om 1 < B := by
      dsimp [B]
      exact lt_mul_of_one_lt_right Gw.gw_Om_pos (by rw [← Br.Om1_eq]; exact Lu.lu_one_lt_E Rj.rj_Om1_inE)
    rw [Ordinal.mod_eq_of_lt ((hx.trans_le hZ1).trans h1)]
    exact GxCl.small hx
  | om =>
    have h1 : Om 1 < B := by
      dsimp [B]
      exact lt_mul_of_one_lt_right Gw.gw_Om_pos (by rw [← Br.Om1_eq]; exact Lu.lu_one_lt_E Rj.rj_Om1_inE)
    rw [Ordinal.mod_eq_of_lt h1]
    exact GxCl.om
  | @atom s hs =>
    rw [Set.mem_singleton_iff] at hs
    subst s
    have hG : InE (Gc.gcG 0) := Low.opow_eq_self_of_SC (Gc.gcG_SC 0)
    have hGe : Om 1 + Om 1 ≤ Gc.gcG 0 := by
      have hpow : ω ^ (Om 1 + Om 1) ≤ ω ^ Gc.gcG 0 := by
        calc
          ω ^ (Om 1 + Om 1) = B := hBpow.symm
          _ ≤ Gc.gcG 0 := hBg.le
          _ = ω ^ Gc.gcG 0 := hG.symm
      exact (opow_le_opow_iff_right one_lt_omega0).1 hpow
    have hdiv : B ∣ Gc.gcG 0 := by
      rw [hBpow]
      rw [← hG]
      exact opow_dvd_opow ω hGe
    have hz : Gc.gcG 0 % B = 0 := (Ordinal.dvd_iff_mod_eq_zero).1 hdiv
    rw [hz]
    exact GxCl.zero hZ.1
  | @add x y _ _ ihx ihy =>
    have hxD := Ordinal.div_add_mod x B
    have hyD := Ordinal.div_add_mod y B
    have hrx : x % B < B := Ordinal.mod_lt x hBne
    rcases lt_or_ge y B with hyB | hyB
    · have e : x + y = B * (x / B) + (x % B + y) := by
        conv_lhs => rw [← hxD]
        rw [add_assoc]
      rw [e, Gw.gwY_mod_eq hB0 (hBp hrx hyB)]
      rw [Ordinal.mod_eq_of_lt hyB] at ihy
      exact GxCl.add ihx ihy
    · have hq : 1 ≤ y / B := by
        rw [Order.one_le_iff_pos]
        exact (Ordinal.div_pos hBne).2 hyB
      obtain ⟨q, hq⟩ := exists_add_of_le hq
      have hry : y % B < B := Ordinal.mod_lt y hBne
      have e1 : x % B + B * (1 + q) = B * (1 + q) := by
        rw [mul_add, mul_one, ← add_assoc, hBp.add_eq_right hrx]
      have e : x + y = B * (x / B + y / B) + y % B := by
        conv_lhs => rw [← hxD, ← hyD]
        rw [hq, ← add_assoc (B * (x / B) + x % B), add_assoc (B * (x / B)) (x % B), e1, ← mul_add]
      rw [e, Gw.gwY_mod_eq hB0 hry]
      exact ihy
  | @phi a b ha hb _ _ =>
    rcases lt_or_ge (veblen a b) B with hv | hv
    · rw [Ordinal.mod_eq_of_lt hv]
      exact GxCl.phi ha hb
    · have hdiv : B ∣ veblen a b := by
        rcases eq_or_ne a 0 with rfl | ha0
        · rw [veblen_zero_apply] at hv ⊢
          have hpow : ω ^ (Om 1 + Om 1) ≤ ω ^ b := by
            calc
              ω ^ (Om 1 + Om 1) = B := hBpow.symm
              _ ≤ ω ^ b := hv
          have hbE : Om 1 + Om 1 ≤ b := by
            exact (opow_le_opow_iff_right one_lt_omega0).1 hpow
          rw [hBpow]
          exact (opow_dvd_opow ω hbE)
        · have hE : InE (veblen a b) := gg_veblen_eps ha0
          have hfix : ω ^ veblen a b = veblen a b := hE
          have hbE : Om 1 + Om 1 ≤ veblen a b := by
            have hB' : ω ^ (Om 1 + Om 1) ≤ ω ^ veblen a b := by
              calc
                ω ^ (Om 1 + Om 1) = B := hBpow.symm
                _ ≤ veblen a b := hv
                _ = ω ^ veblen a b := hfix.symm
            apply (opow_le_opow_iff_right one_lt_omega0).1
            exact hB'
          rw [hBpow]
          rw [← hfix]
          exact opow_dvd_opow ω hbE
      rw [Ordinal.dvd_iff_mod_eq_zero] at hdiv
      rw [hdiv]
      exact GxCl.zero hZ.1

/-- The Ω₁ coefficient of the remainder below Ω₁² is below the code gate. -/
theorem hmSq_gate_cube_remcoef {Z y : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om 1)
    (h : GxCl Z {Gc.gcG 0} y) :
    (y % (Om 1 * Om 1)) / Om 1 < Z := by
  have hrem := hmSq_cl_mod hZ hZ1 h
  have hr : y % (Om 1 * Om 1) < Om 1 * Om 1 :=
    Ordinal.mod_lt y (mul_ne_zero Gw.gw_Om_pos.ne' Gw.gw_Om_pos.ne')
  exact Gw.gw_cl_coef hZ hZ1 hrem hr

/-- The Ω₁-digit is exactly μ on the band between Ω₁²+Ω₁·μ and
Ω₁²+Ω₁·(μ+1). -/
theorem hmSq_band_coeff {μ y : Ordinal.{0}} (hμ : μ < Om 1)
    (hlo : Om 1 * Om 1 + Om 1 * μ ≤ y)
    (hhi : y < Om 1 * Om 1 + Om 1 * (μ + 1)) :
    (y % (Om 1 * Om 1)) / Om 1 = μ := by
  let B : Ordinal.{0} := Om 1 * Om 1
  have hΩ : 0 < Om 1 := Gw.gw_Om_pos
  have hΩ0 : Om 1 ≠ 0 := hΩ.ne'
  have hB0 : 0 < B := mul_pos hΩ hΩ
  have hB0n : B ≠ 0 := hB0.ne'
  have hμ' : μ < Om1 := by simpa [Rj.rj_Om1] using hμ
  have hlim : Order.IsSuccLimit (Om1 : Ordinal.{0}) := by
    rw [Rj.rj_Om1]
    exact InaccSeq.Om_isSuccLimit one_ne_zero
  have hμs : μ + 1 < Om 1 := by
    simpa [Rj.rj_Om1] using hlim.succ_lt hμ'
  have htail : Om 1 * (μ + 1) < B := by
    apply (mul_lt_mul_iff_right₀ hΩ).2 hμs
  have hhiB : y < B + B := by
    exact hhi.trans ((add_lt_add_iff_left B).2 htail)
  have hqLt : y / B < 2 := by
    apply (Ordinal.lt_mul_iff_div_lt hB0n).1
    simpa [B, show (2 : Ordinal.{0}) = 1 + 1 by norm_num, mul_add, mul_one] using hhiB
  have hqGe : 1 ≤ y / B := by
    apply (Ordinal.le_div hB0n).2
    simpa [B] using (le_self_add.trans hlo)
  have hq : y / B = 1 := by
    apply le_antisymm
    · have hqLe : y / B ≤ 1 := (Order.lt_succ_iff).1 (by simpa using hqLt)
      exact hqLe
    · exact hqGe
  have hdecomp := Ordinal.div_add_mod y B
  rw [hq, mul_one] at hdecomp
  have hlo' := hlo
  conv_rhs at hlo' => rw [hdecomp.symm]
  have hloR : Om 1 * μ ≤ y % B := (add_le_add_iff_left B).1 hlo'
  have hhi' := hhi
  conv_lhs at hhi' => rw [hdecomp.symm]
  have hhiR : y % B < Om 1 * (μ + 1) := (add_lt_add_iff_left B).1 hhi'
  have hμle : μ ≤ (y % B) / Om 1 := by
    apply (Ordinal.le_div hΩ0).2
    exact hloR
  have hq2lt : (y % B) / Om 1 < μ + 1 :=
    (Ordinal.lt_mul_iff_div_lt hΩ0).1 hhiR
  have hq2le : (y % B) / Om 1 ≤ μ := (Order.lt_succ_iff).1 hq2lt
  exact le_antisymm hq2le hμle

/-- A code in the μ-th Ω₁-band above Ω₁² forces μ below the base gate Z. -/
theorem hmSq_band_gate {Z μ y : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om 1)
    (hμ : μ < Om 1) (h : GxCl Z {Gc.gcG 0} y)
    (hlo : Om 1 * Om 1 + Om 1 * μ ≤ y)
    (hhi : y < Om 1 * Om 1 + Om 1 * (μ + 1)) : μ < Z := by
  rw [← hmSq_band_coeff hμ hlo hhi]
  exact hmSq_gate_cube_remcoef hZ hZ1 h

/-- The Ω₁² coefficient of a code below Ω₁³ remains below its strongly critical
base. The φ(0,b) case uses the existing code-tail decomposition. -/
theorem hmSq_gate_cube_quot {Z y : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om 1)
    (h : GxCl Z {Gc.gcG 0} y) (hy : y < Om 1 * Om 1 * Om 1) :
    y / (Om 1 * Om 1) < Z := by
  induction h with
  | @small x hx =>
    have hO := Gw.gw_Om_pos
    have hOne : 1 < Om 1 := by rw [← Br.Om1_eq]; exact Lu.lu_one_lt_E Rj.rj_Om1_inE
    have hB : Om 1 < Om 1 * Om 1 := lt_mul_of_one_lt_right hO.pos hOne
    have hxB : x < Om 1 * Om 1 := (hx.trans_le hZ1).trans hB
    rw [Ordinal.div_eq_zero_of_lt hxB]
    exact hZ.1
  | om =>
    have hO := Gw.gw_Om_pos
    have hOne : 1 < Om 1 := by rw [← Br.Om1_eq]; exact Lu.lu_one_lt_E Rj.rj_Om1_inE
    have hB : Om 1 < Om 1 * Om 1 := lt_mul_of_one_lt_right hO.pos hOne
    change Om 1 / (Om 1 * Om 1) < Z
    rw [Ordinal.div_eq_zero_of_lt hB]
    exact hZ.1
  | @atom s hs =>
    rw [Set.mem_singleton_iff] at hs
    rw [hs] at hy
    exact absurd (hy.trans_le hmSq_lt_G.le) (lt_irrefl _)
  | @add x y hx hy ihx ihy =>
    let B : Ordinal.{0} := Om 1 * Om 1
    have hO := Gw.gw_Om_pos
    have hBne : B ≠ 0 := by simp [B, hO.ne']
    have hP : IsPrincipal (· + ·) B := by
      dsimp [B]
      rw [Gw.gw_OmOm_eq]
      exact isPrincipal_add_omega0_opow _
    have hx' : x < Om 1 * Om 1 * Om 1 := lt_of_le_of_lt le_self_add hy
    have hy' : y < Om 1 * Om 1 * Om 1 := lt_of_le_of_lt le_add_self hy
    have h1 := ihx hx'
    have h2 := ihy hy'
    have ex := Ordinal.div_add_mod x B
    have ey := Ordinal.div_add_mod y B
    have hr1 : x % B < B := Ordinal.mod_lt x hBne
    have hr2 : y % B < B := Ordinal.mod_lt y hBne
    rcases lt_or_ge y B with hyB | hyB
    · have e : x + y = B * (x / B) + (x % B + y) := by
        conv_lhs => rw [← ex]
        rw [add_assoc]
      rw [e, Ordinal.mul_add_div _ hBne, Ordinal.div_eq_zero_of_lt (hP hr1 hyB), add_zero]
      exact h1
    · have hq : 1 ≤ y / B := by
        rw [Order.one_le_iff_pos]
        exact (Ordinal.div_pos hBne).2 hyB
      obtain ⟨b', hb'⟩ := exists_add_of_le hq
      have e1 : x % B + B * (1 + b') = B * (1 + b') := by
        rw [mul_add, mul_one, ← add_assoc, hP.add_eq_right hr1]
      have e : x + y = B * (x / B + y / B) + y % B := by
        conv_lhs => rw [← ex, ← ey]
        rw [hb', ← add_assoc (B * (x / B) + x % B), add_assoc (B * (x / B)) (x % B), e1,
          ← mul_add]
      rw [e, Ordinal.mul_add_div _ hBne, Ordinal.div_eq_zero_of_lt hr2, add_zero]
      exact hZ.isPrincipal h1 h2
  | @phi a b ha hb ihA ihB =>
    have hO := Gw.gw_Om_pos
    have hOne : 1 < Om 1 := by rw [← Br.Om1_eq]; exact Lu.lu_one_lt_E Rj.rj_Om1_inE
    have hB : Om 1 < Om 1 * Om 1 := lt_mul_of_one_lt_right hO.pos hOne
    rcases lt_or_ge (veblen a b) (Om 1) with hv | hv
    · rw [Ordinal.div_eq_zero_of_lt (hv.trans hB)]
      exact hZ.1
    · rcases eq_or_ne a 0 with rfl | ha0
      · rw [veblen_zero_apply] at hv hy ⊢
        simp only [← Br.Om1_eq] at hv hy ⊢
        have hOmPow : ω ^ Om1 = Om1 := by simpa [Br.Om1_eq] using Bt.Om1_opow
        have hOb : Om1 ≤ b := by
          rw [← hOmPow] at hv
          exact (opow_le_opow_iff_right one_lt_omega0).1 hv
        have hsq : Om1 * Om1 = ω ^ (Om1 + Om1) := by
          simpa [Br.Om1_eq] using Gw.gw_OmOm_eq
        have hCube : Om1 * Om1 * Om1 = ω ^ (Om1 * 3) := by
          calc
            Om1 * Om1 * Om1 = ω ^ (Om1 + Om1) * ω ^ Om1 := by rw [hsq, hOmPow]
            _ = ω ^ ((Om1 + Om1) + Om1) := by rw [← opow_add]
            _ = ω ^ (Om1 * 3) := by
              congr 1
              simp [show (3 : Ordinal.{0}) = 1 + (1 + 1) by norm_num, mul_add, add_assoc]
        have hb3 : b < Om1 * 3 := by
          rw [hCube] at hy
          exact (opow_lt_opow_iff_right one_lt_omega0).1 hy
        obtain ⟨q', r', hr', e⟩ := gv_cl_tail hZ hZ1 gr_GxAt hb
        have hOmNe : Om1 ≠ 0 := by simpa [Br.Om1_eq] using Gw.gw_Om_pos.ne'
        have hZ1' : Z ≤ Om1 := by simpa [Br.Om1_eq] using hZ1
        have hrO : r' < Om1 := hr'.trans_le hZ1'
        rw [← Br.Om1_eq] at e
        have hbdiv : b / Om1 = q' := by
          rw [e, Ordinal.mul_add_div _ hOmNe, Ordinal.div_eq_zero_of_lt hrO, add_zero]
        have hq3 : q' < 3 := by
          rw [← hbdiv]
          exact (Ordinal.lt_mul_iff_div_lt hOmNe).1 hb3
        have hq3le : q' ≤ 2 := by
          have hq3' : q' < (2 : Ordinal.{0}) + 1 :=
            by simpa [show (3 : Ordinal.{0}) = 2 + 1 by norm_num] using hq3
          exact (Order.lt_succ_iff).1 hq3'
        have hq1 : 1 ≤ q' := by
          rw [Order.one_le_iff_pos, ← hbdiv]
          exact (Ordinal.div_pos hOmNe).2 hOb
        by_cases hqone : q' = 1
        · have hpow : ω ^ b = Om1 * ω ^ r' := by
            rw [e, hqone, mul_one, opow_add, hOmPow]
          have hsmall : ω ^ r' < Om1 := by
            rw [← hOmPow]
            exact (opow_lt_opow_iff_right one_lt_omega0).2 hrO
          have hltB : ω ^ b < Om1 * Om1 := by
            rw [hpow]
            exact mul_lt_mul_of_pos_left hsmall (by simpa [Br.Om1_eq] using Gw.gw_Om_pos)
          rw [Ordinal.div_eq_zero_of_lt hltB]
          exact hZ.1
        · have hq2 : 2 ≤ q' := by
            apply le_of_not_gt
            intro hqLt
            have hqLt' : q' < (1 : Ordinal.{0}) + 1 :=
              by simpa [show (2 : Ordinal.{0}) = 1 + 1 by norm_num] using hqLt
            have hqle1 : q' ≤ 1 := (Order.lt_succ_iff).1 hqLt'
            have : q' = 1 := le_antisymm hqle1 hq1
            exact hqone this
          have hqeq : q' = 2 := le_antisymm hq3le hq2
          have hpow2 : ω ^ (Om1 * 2) = Om1 * Om1 := by
            rw [show (2 : Ordinal.{0}) = 1 + 1 by norm_num, mul_add, mul_one, opow_add]
            simpa only [hOmPow]
          have hpow : ω ^ b = (Om1 * Om1) * ω ^ r' := by
            rw [e, hqeq, opow_add, hpow2]
          have hBne : Om1 * Om1 ≠ 0 := mul_ne_zero hOmNe hOmNe
          rw [hpow, Ordinal.mul_div_cancel _ hBne]
          have htail := hZ.2 0 hZ.1 r' hr'
          simpa [veblen_zero_apply] using htail
      · have hE : InE (veblen a b) := gg_veblen_eps ha0
        rcases hv.lt_or_eq with hlt | heq
        · have hSq : Om 1 * Om 1 < veblen a b := InE.mul_lt hE hlt hlt
          have hCube : Om 1 * Om 1 * Om 1 < veblen a b := by
            simpa [mul_assoc] using InE.mul_lt hE hSq hlt
          exact absurd (hy.trans_le hCube.le) (lt_irrefl _)
        · rw [← heq, Ordinal.div_eq_zero_of_lt hB]
          exact hZ.1

/-- At the endpoint Ω₁², the gate on the next union interval
`[Ω₁², Ω₁²·2)` is 0. -/
theorem hmSq_code_gate {Z y : Ordinal.{0}} (hZ : SC Z) (_hZ1 : Z ≤ Om 1)
    (_hy : GxCl Z {Gc.gcG 0} y) (hL : hmL ≤ y) (_hy2 : y < Om 1 * Om 1 * 2) :
    0 < Z := hZ.1

/-- EXACT for the first family of levels after Ω₁²: Ω₁²+Ω₁·μ+η, with both
coefficients below the image base. -/
theorem hmSq_level_exact {σ ρ μ η : Ordinal.{0}} (hB : Bases σ ρ)
    (hμ : μ < σ) (hη : η < σ) :
    ρ * ρ + ρ * μ + η ∈ TB ρ σ ∧
      pi σ ρ (ρ * ρ + ρ * μ + η) = σ * σ + σ * μ + η := by
  obtain ⟨hsq, hsqπ⟩ := pi_sq hB
  obtain ⟨hmul, hmulπ⟩ := pi_mul hB μ hμ
  obtain ⟨hadd, haddπ⟩ := pi_add hB hsq hmul
  obtain ⟨htail, htailπ⟩ := pi_add hB hadd (mem_TB_of_lt hB hη)
  exact ⟨htail, by rw [htailπ, haddπ, hsqπ, hmulπ, pi_lt hB hη]⟩

/-- The next union reading x²·2 bounds the outer low-field offset x²+x. -/
theorem hmSq_next_bound {x : Ordinal.{0}} (hx : InE x) : x * x + x < x * x * 2 := by
  have hx2 : x < x * x := Hl.hl_lt_sq hx
  calc
    x * x + x < x * x + x * x := (add_lt_add_iff_left (x * x)).2 hx2
    _ = x * x * 2 := by rw [← mul_two_eq]

/-- Each Ω₁·μ reading plus one base unit lies below the reading at μ+2. This is the
low-field bound needed when the outer field is measured by the next union. -/
theorem hmLayer_next_bound {x μ : Ordinal.{0}} (hx : InE x) :
    x * x + x * μ + x < x * x + x * (μ + 2) := by
  have hxpos : 0 < x := hx.pos
  have hxadd : x < x + x := by
    have h := (add_lt_add_iff_left x).2 hxpos
    simpa using h
  have htwo : x * 2 = x + x := by
    rw [show (2 : Ordinal.{0}) = 1 + 1 by norm_num, mul_add_one, mul_one]
  rw [mul_add, htwo]
  calc
    (x * x + x * μ) + x = x * x + (x * μ + x) := add_assoc _ _ _
    _ < x * x + (x * μ + (x + x)) :=
      (add_lt_add_iff_left (x * x)).2 ((add_lt_add_iff_left (x * μ)).2 hxadd)

/-- The next-union bound is uniform in the coefficient μ: the reading
`x² + x·μ` and its next reading `x² + x·(μ+2)` leave room for one base unit. -/
theorem hmLayer_next_bound_uniform {x μ : Ordinal.{0}} (hx : InE x) :
    x * x + x * μ + x < x * x + x * (μ + 2) := hmLayer_next_bound hx

/-- Transfer of the shifted level `Ω₁² + Ω₁·μ` at bases above μ. -/
theorem hmLayer_exact {σ ρ μ : Ordinal.{0}} (hB : Bases σ ρ) (hμ : μ < σ) :
    ρ * ρ + ρ * μ ∈ TB ρ σ ∧
      pi σ ρ (ρ * ρ + ρ * μ) = σ * σ + σ * μ := by
  obtain ⟨hsq, hsqπ⟩ := pi_sq hB
  obtain ⟨hmul, hmulπ⟩ := pi_mul hB μ hμ
  obtain ⟨hmem, hpi⟩ := pi_add hB hsq hmul
  exact ⟨hmem, by rw [hpi, hsqπ, hmulπ]⟩

/-- A shifted layer datum at `Ω₁² + Ω₁·μ`. The exactness field carries the
necessary side condition μ < σ explicitly; this is the changed-bound data for
the union whose next reading is `x² + x·(μ+2)`. -/
structure HmShiftLayerRead (μ : Ordinal.{0}) where
  l : Ordinal.{0} → Ordinal.{0}
  next : Ordinal.{0} → Ordinal.{0}
  l_ge : ∀ x, InE x → x < Om1 → x ≤ l x
  l_lt_next : ∀ x, InE x → x < Om1 → l x < next x
  l_add_lt_next : ∀ x, InE x → x < Om1 → l x + x < next x
  l_pi : ∀ σ ρ, Bases σ ρ → μ < σ →
    l ρ ∈ TB ρ σ ∧ pi σ ρ (l ρ) = l σ

/-- The shifted level `Ω₁² + Ω₁·μ`, read as `x²+x·μ`, with the outer
low-field bound taken from the next union reading. -/
noncomputable def hmShiftLayerRead (μ : Ordinal.{0}) : HmShiftLayerRead μ where
  l := fun x => x * x + x * μ
  next := fun x => x * x + x * (μ + 2)
  l_ge := fun x hx _ => (Hl.hl_lt_sq hx).le.trans le_self_add
  l_lt_next := fun x hx _ =>
    (lt_add_of_pos_right _ hx.pos).trans (hmLayer_next_bound hx)
  l_add_lt_next := fun x hx _ => hmLayer_next_bound hx
  l_pi := fun σ ρ hB hμ => hmLayer_exact hB hμ

/-- A band level above Ω₁², with its code gate and the next-union reading
recorded together. -/
structure HmBandLv (μ : Ordinal.{0}) where
  L : Ordinal.{0}
  l : Ordinal.{0} → Ordinal.{0}
  next : Ordinal.{0} → Ordinal.{0}
  gate : Ordinal.{0}
  gate_lt : gate < Om1
  L_eq : L = Om 1 * Om 1 + Om 1 * μ
  g_cl : ∀ Z y, SC Z → Z ≤ Om 1 → GxCl Z {Gc.gcG 0} y →
    L ≤ y → y < L + Om 1 → gate < Z
  l_ge : ∀ x, InE x → x < Om1 → x ≤ l x
  l_lt_next : ∀ x, InE x → x < Om1 → l x < next x
  l_add_lt_next : ∀ x, InE x → x < Om1 → l x + x < next x
  l_pi : ∀ σ ρ, Bases σ ρ → μ < σ →
    l ρ ∈ TB ρ σ ∧ pi σ ρ (l ρ) = l σ

/-- The level Ω₁²+Ω₁·μ uses the band coefficient itself as its gate, and the
next union at x²+x·(μ+2) for the outer low-field estimate. -/
noncomputable def hmBandLevel (μ : Ordinal.{0}) (hμ : μ < Om1) : HmBandLv μ where
  L := Om 1 * Om 1 + Om 1 * μ
  l := fun x => x * x + x * μ
  next := fun x => x * x + x * (μ + 2)
  gate := μ
  gate_lt := by simpa [Br.Om1_eq] using hμ
  L_eq := rfl
  g_cl := by
    intro Z y hZ hZ1 hy hyL hyU
    apply hmSq_band_gate hZ hZ1 (by simpa [Rj.rj_Om1] using hμ) hy
    · exact hyL
    · simpa [add_assoc, mul_add_one] using hyU
  l_ge := fun x hx _ => (Hl.hl_lt_sq hx).le.trans le_self_add
  l_lt_next := fun x hx _ => (lt_add_of_pos_right _ hx.pos).trans (hmLayer_next_bound hx)
  l_add_lt_next := fun x hx _ => hmLayer_next_bound hx
  l_pi := fun σ ρ hB hμσ => hmLayer_exact hB hμσ

/-- Advancing the band by one Ω₁ unit adds one base unit to its reading. -/
theorem hmBandLevel_succ_l {μ x : Ordinal.{0}} (hμ : μ + 1 < Om1) :
    (hmBandLevel (μ + 1) hμ).l x = (hmBandLevel μ (lt_trans (lt_add_one μ) hμ)).l x + x := by
  simp [hmBandLevel, mul_add_one, add_assoc]

/-- The changed reading invariant for the next union. Unlike `HlLv`, this small datum
measures the outer low field against the next reading `x²·2`, rather than against
the current reading `x²`. It records only the fields that change at this boundary. -/
structure HmLayerRead where
  l : Ordinal.{0} → Ordinal.{0}
  next : Ordinal.{0} → Ordinal.{0}
  l_ge : ∀ x, InE x → x < Om1 → x ≤ l x
  l_lt_next : ∀ x, InE x → x < Om1 → l x < next x
  l_add_lt_next : ∀ x, InE x → x < Om1 → l x + x < next x
  l_pi : ∀ σ ρ, Bases σ ρ → l ρ ∈ TB ρ σ ∧ pi σ ρ (l ρ) = l σ

/-- The endpoint `Ω₁²` read as `x²`, with the low-field bound taken from
the following union reading `x²·2`. -/
noncomputable def hmLayerRead : HmLayerRead where
  l := fun x => x * x
  next := fun x => x * x * 2
  l_ge := fun x hx hx1 => (Hl.hl_lt_sq hx).le
  l_lt_next := fun x hx _ => by
    have hpos : 0 < x * x := mul_pos hx.pos hx.pos
    calc
      x * x < x * x + x * x := by
        simpa using (add_lt_add_iff_left (x * x)).2 hpos
      _ = x * x * 2 := by rw [← mul_two_eq]
  l_add_lt_next := fun x hx _ => hmSq_next_bound hx
  l_pi := fun σ ρ hB => pi_sq hB

/-- The old bound `L + ν < Ω₁²` cannot be carried to the endpoint level. -/
theorem hmSq_no_old_L_add_bound (ν : Ordinal.{0}) : ¬ hmL + ν < Om 1 * Om 1 := by
  intro h
  exact not_lt_of_ge (le_self_add : hmL ≤ hmL + ν) h

#print axioms hmSq_code_gate
#print axioms hmSq_lt_G
#print axioms hmSq_gate_cube_quot
#print axioms hmSq_cl_mod
#print axioms hmSq_gate_cube_remcoef
#print axioms hmSq_band_coeff
#print axioms hmSq_band_gate
#print axioms hmBandLevel
#print axioms hmBandLevel_succ_l
#print axioms hmSq_level_exact
#print axioms hmSq_next_bound
#print axioms hmLayer_next_bound
#print axioms hmLayer_exact
#print axioms hmShiftLayerRead
#print axioms hmSq_no_old_L_add_bound
#print axioms hmLayerRead

end Googology.Trans.PoR.InaccPsi.R2.Hm
