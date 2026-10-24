import Googology.Trans.PoR.InaccPsi.R2.SvCL

/-!
# CONV and EQ at every level `μ < Γ_{Ω₁+1}` of the generic hierarchy `ssP`

`ψ = S.psi`, `Φ_μ = Ss.ssP μ` (data `ssDatL μ = ssDat(Ω₁ + μ)`), `u_μ = Ω₁^μ = Le.leOe μ`.  An argument `B` is *own*
when `B ∈ Cl(B, ψ_{Ω₁}(B))`.  FWD at every level is `Ss.ssFwdAll`; here the other two lemmas of `R2.RkPsi` (levels
`< ε_{Ω₁+1}`) and `R2.SsLev` (the level `ε_{Ω₁+1}`) are proved at every Veblen level, from `R2.SvLev` and `R2.SvCL`:

* `sv_U_mem`, `sv_U_mul_mem` (**`u_μ`, `u_μ·D ∈ Cl(a, b)`** from `ssDatL μ < b`, `b` strongly critical, `μ <
  Γ_{Ω₁+1}`);
* `sv_conv` (**CONV(μ): `u_{μ+1} ∣ B` for every own `B` with `ψ_{Ω₁}(B)` a fixed point of `Φ_μ`**, `μ <
  Γ_{Ω₁+1}`);
* `sv_eq` (**EQ(μ): `ψ_{Ω₁}(B + u_μ·D) = Φ_μ(c + D)` and `D < ψ_{Ω₁}(B + u_μ·D)`** when `d < Φ_μ(c+d)` for every
  `d ≤ D`, `B` own, `u_μ ∣ B`, `Φ_μ(c) = ψ_{Ω₁}(B)`, `ssDatL μ < ψ_{Ω₁}(B)`, `μ < Γ_{Ω₁+1}`), `sv_valid` (the
  converse, `μ ≤ Γ_{Ω₁+1}`);
* `sv_conv_iff` (**for an own `B ≠ 0` with `ssDatL μ < ψ_{Ω₁}(B)`: `ψ_{Ω₁}(B)` is a fixed point of `Φ_μ` iff
  `u_{μ+1} ∣ B`**), `sv_dvd_eps` (an `ε`-number `p > Ω₁` is a multiple of every `u_μ`, `μ ≤ Γ_{Ω₁+1}`, when
  `Γ_{Ω₁+1} ≤ p`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Sv

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Lq Googology.Trans.PoR.InaccPsi.R2.Rb
  Googology.Trans.PoR.InaccPsi.R2.Rd Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Trans.PoR.InaccPsi.R2.Ri
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rk Googology.Trans.PoR.InaccPsi.R2.Ss

variable {S : InaccSeq.{0}}

/-- `u_μ ∈ Cl(a, b)` from `ssDatL μ < b`, `b` strongly critical, `μ < Γ_{Ω₁+1}`. -/
theorem sv_U_mem {μ a b : Ordinal.{0}} (hb : SC b) (hμ : μ < ggGam) (h : ssDatL μ < b) :
    Le.leOe μ ∈ S.CSet a b := rkU_mem hb (ss_code_lvl hb hμ h)

/-- `u_μ·D ∈ Cl(a, b)` from `ssDatL μ < b`, `D < b`, `b` strongly critical, `μ < Γ_{Ω₁+1}`. -/
theorem sv_U_mul_mem {μ a b D : Ordinal.{0}} (hb : SC b) (hμ : μ < ggGam) (h : ssDatL μ < b) (hD : D < b) :
    Le.leOe μ * D ∈ S.CSet a b := rkU_mul_mem hb (ss_code_lvl hb hμ h) hD

/-- **CONV(μ)**: `u_{μ+1} ∣ B` for every own `B` with `ψ_{Ω₁}(B)` a fixed point of `Φ_μ`, `μ < Γ_{Ω₁+1}`. -/
theorem sv_conv {μ : Ordinal.{0}} (hμ : μ < ggGam) {B : Ordinal.{0}} (hown : B ∈ S.CSet B (S.psi B (Om 1)))
    (hfix : ssP μ (S.psi B (Om 1)) = S.psi B (Om 1)) : Le.leOe (μ + 1) ∣ B := by
  set p := S.psi B (Om 1) with hpdef
  have hpSC : SC p := SC_psi Low.InR_Om_one B
  have hcoll : ∀ e, e < B → e ∈ S.CSet B p → RiDg p e → SvLev p e → S.psi e (Om 1) < p :=
    fun e he heC _ _ => lt_psi_of_mem Low.InR_Om_one
      (CSet.psi_mem he Low.InR_Om_one (mem_CSet_psi Low.InR_Om_one B) heC) (psi_lt Low.InR_Om_one _)
  have hdl := sv_diglev (S := S) hpSC hcoll B hown
  refine ri_dvd_of_dig (μ + 1) fun j hj => ?_
  have hjμ : j ≤ μ := Order.lt_add_one_iff.1 hj
  have hjΩ : j < ggGam := hjμ.trans_lt hμ
  induction j using WellFoundedLT.induction with
  | ind j IHj =>
  by_contra hd0
  have hdj : ssDatL j < p := hdl.2.1 j hjΩ hd0
  have hfj : ssP j p = p := ssP_fix_mono hjμ hfix hdj
  have huj : Le.leOe j ∣ B := ri_dvd_of_dig j fun i hi =>
    IHj i hi (hi.trans hj) (hi.le.trans hjμ) (hi.trans hjΩ)
  set u := Le.leOe j with hudef
  set u2 := Le.leOe (j + 1) with hu2def
  have hu2 : u2 = u * Om 1 := Le.leOe_succ j
  have hupos : 0 < u := rhU_pos j
  have h0 := rd_Om1_ne
  obtain ⟨m, hm⟩ := huj
  set D0 := m % Om 1 with hD0
  set B0 := u2 * (m / Om 1) with hB0
  have hBe : B0 + u * D0 = B := by
    rw [hm, hB0, hD0, hu2, mul_assoc, ← mul_add, Ordinal.div_add_mod]
  have hD0lt : D0 < Om 1 := Ordinal.mod_lt m h0
  have hmdiv : B / u = m := by rw [hm, Ordinal.mul_div_cancel _ (rhU_ne _)]
  have hD00 : D0 ≠ 0 := by rw [hD0, ← hmdiv]; exact hd0
  have hD0p : D0 < p := by have := hdl.1 j; rwa [← hudef, hmdiv] at this
  have hlt' : u * D0 < u2 := by rw [hu2]; exact (mul_lt_mul_iff_right₀ hupos).2 hD0lt
  have hBdiv : B / u2 = m / Om 1 := by
    calc B / u2 = (u2 * (m / Om 1) + u * D0) / u2 := by rw [← hB0, hBe]
      _ = m / Om 1 := by
        rw [Ordinal.mul_add_div _ (rhU_ne (j + 1)), Ordinal.div_eq_zero_of_lt hlt', add_zero]
  have hB0m : B0 ∈ S.CSet B p := by
    have := rh_mod_mem (S := S) (m := j + 1) le_add_self B hown
    rwa [← hu2def, hBdiv] at this
  have hB0B : B0 < B := by
    rw [← hBe]; exact lt_add_of_pos_right _ (mul_pos hupos (pos_iff_ne_zero.2 hD00))
  have hB0p : S.psi B0 (Om 1) < p := psi_lt_psi_of_mem Low.InR_Om_one hB0B hB0m
  have hle := sv_UB (S := S) hjΩ.le B0 (S.psi B0 (Om 1)) D0
    (by rw [hB0]; exact (rhU_dvd le_self_add).trans (dvd_mul_right _ _)) (ssP_le_self _ _) hD0lt.le
  rw [hBe] at hle
  have hlt : S.psi B0 (Om 1) + D0 < p := (lq_SC_indec hpSC).add_lt hB0p hD0p
  have h2 : ssP j (S.psi B0 (Om 1) + D0) < p := by
    conv_rhs => rw [← hfj]
    exact (ssP_lt_iff j).2 hlt
  exact absurd (hle.trans_lt h2) (lt_irrefl _)

/-- **FWD and CONV together**: for an own `B ≠ 0` with `ssDatL μ < ψ_{Ω₁}(B)`, `μ < Γ_{Ω₁+1}`: `ψ_{Ω₁}(B)` is a
fixed point of `Φ_μ` iff `u_{μ+1} ∣ B`. -/
theorem sv_conv_iff {μ B : Ordinal.{0}} (hμ : μ < ggGam) (hown : B ∈ S.CSet B (S.psi B (Om 1))) (hB0 : B ≠ 0)
    (hd : ssDatL μ < S.psi B (Om 1)) :
    ssP μ (S.psi B (Om 1)) = S.psi B (Om 1) ↔ Le.leOe (μ + 1) ∣ B :=
  ⟨sv_conv hμ hown, fun h => ssFwdAll μ hμ B hown h hB0 hd⟩

/-- **EQ(μ)**: `ψ_{Ω₁}(B + u_μ·D) = Φ_μ(c + D)`, and `D < ψ_{Ω₁}(B + u_μ·D)`, when `d < Φ_μ(c+d)` for every `d ≤ D`,
for an own `B` with `u_μ ∣ B`, `Φ_μ(c) = ψ_{Ω₁}(B)` and `ssDatL μ < ψ_{Ω₁}(B)` (`μ < Γ_{Ω₁+1}`). -/
theorem sv_eq {μ : Ordinal.{0}} (hμ : μ < ggGam)
    {B c : Ordinal.{0}} (hown : B ∈ S.CSet B (S.psi B (Om 1))) (hB : Le.leOe μ ∣ B)
    (hc : ssP μ c = S.psi B (Om 1)) (hdB : ssDatL μ < S.psi B (Om 1)) :
    ∀ D, D < Om 1 → (∀ d, d ≤ D → d < ssP μ (c + d)) →
      D < S.psi (B + Le.leOe μ * D) (Om 1) ∧ S.psi (B + Le.leOe μ * D) (Om 1) = ssP μ (c + D) := by
  set u := Le.leOe μ with hudef
  have hupos : 0 < u := rhU_pos μ
  intro D
  induction D using WellFoundedLT.induction with
  | ind D IH =>
  intro hDΩ hcond
  have hIH : ∀ d, d < D → S.psi (B + u * d) (Om 1) = ssP μ (c + d) :=
    fun d hd => (IH d hd (hd.trans hDΩ) fun d' hd' => hcond d' (hd'.trans hd.le)).2
  have heq : S.psi (B + u * D) (Om 1) = ssP μ (c + D) := by
    rcases eq_or_ne D 0 with rfl | hD0
    · rw [mul_zero, add_zero, add_zero, hc]
    set v := S.psi (B + u * D) (Om 1) with hv
    have hvSC : SC v := SC_psi Low.InR_Om_one _
    have hBv : S.psi B (Om 1) < v :=
      rh_psi_lt_of_own hown (lt_add_of_pos_right _ (mul_pos hupos (pos_iff_ne_zero.2 hD0)))
    have hdv : ssDatL μ < v := hdB.trans hBv
    have hlt : ∀ d, d < D → ssP μ (c + d) < v := by
      intro d hd
      have hle : S.psi (B + u * d) (Om 1) ≤ v :=
        (psi_mono (S := S) Low.InR_Om_one ((add_le_add_iff_left B).2 (mul_le_mul_right hd.le _))).1
      have hdv' : d < v := (hcond d hd.le).trans_le (by rw [← hIH d hd]; exact hle)
      have hmem : B + u * d ∈ S.CSet (B + u * D) v :=
        CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one (le_self_add : B ≤ B + u * D)).2 hown)
          (sv_U_mul_mem (SC_psi Low.InR_Om_one _) hμ hdv hdv')
      rw [← hIH d hd]
      exact psi_lt_psi_of_mem Low.InR_Om_one
        ((add_lt_add_iff_left B).2 ((mul_lt_mul_iff_right₀ hupos).2 hd)) hmem
    apply le_antisymm
    · exact sv_UB hμ.le B c D hB hc.ge hDΩ.le
    · rcases zero_or_succ_or_isSuccLimit D with h0 | ⟨d0, rfl⟩ | hlim
      · exact absurd h0 hD0
      · rw [Order.succ_eq_add_one] at hlt hDΩ ⊢
        have hd0v : d0 < v := (hcond d0 (Order.le_succ d0)).trans (hlt d0 (lt_add_one d0))
        have hDv : d0 + 1 < v := hvSC.add_one_lt hd0v
        have hown1 : B + u * (d0 + 1) ∈ S.CSet (B + u * (d0 + 1)) v :=
          CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one (le_self_add : B ≤ B + u * (d0 + 1))).2 hown)
            (sv_U_mul_mem (SC_psi Low.InR_Om_one _) hμ hdv hDv)
        have hne : B + u * (d0 + 1) ≠ 0 :=
          (lt_of_lt_of_le (mul_pos hupos (lt_of_le_of_lt zero_le (lt_add_one d0))) le_add_self).ne'
        have hfix : ∀ j < μ, ssDatL j < v → ssP j v = v := fun j hj hdj =>
          ssFwdAll j (hj.trans hμ) _ hown1 ((rhU_dvd_succ hj).trans (dvd_add hB (dvd_mul_right _ _))) hne hdj
        obtain ⟨e, he⟩ := ssP_range hvSC hdv hfix
        rw [← he]
        refine (ssP_le_iff μ).2 (not_lt.1 fun hlt' => ?_)
        have hle : e ≤ c + d0 := by
          rw [← add_assoc] at hlt'; exact Order.lt_add_one_iff.1 hlt'
        have := ((ssP_le_iff μ).2 hle).trans_lt (hlt d0 (lt_add_one d0))
        rw [he] at this
        exact lt_irrefl _ this
      · refine not_lt.1 fun hlt' => ?_
        obtain ⟨e, he, hve⟩ := ((ssP_normal μ).lt_iff_exists_lt (isSuccLimit_add c hlim)).1 hlt'
        rcases lt_or_ge e c with hec | hce
        · have : ssP μ e < v := ((ssP_lt_iff μ).2 hec).trans_le (by rw [hc]; exact hBv.le)
          exact absurd hve (not_lt.2 this.le)
        · have hσe : c + (e - c) = e := Ordinal.add_sub_cancel_of_le hce
          have hσ : e - c < D := by rw [← hσe] at he; exact (add_lt_add_iff_left c).1 he
          have := hlt _ hσ
          rw [hσe] at this
          exact absurd hve (not_lt.2 this.le)
  exact ⟨by rw [heq]; exact hcond D le_rfl, heq⟩

/-- **A valid `D` has `d < Φ_μ(c+d)` for every `d ≤ D`** (`u_μ ∣ B`, `Φ_μ(c) = ψ_{Ω₁}(B)`, `μ ≤ Γ_{Ω₁+1}`). -/
theorem sv_valid {μ B c D : Ordinal.{0}} (hμ : μ ≤ ggGam) (hB : Le.leOe μ ∣ B)
    (hc : ssP μ c = S.psi B (Om 1))
    (hv : D < S.psi (B + Le.leOe μ * D) (Om 1)) : ∀ d, d ≤ D → d < ssP μ (c + d) := by
  intro d hd
  by_contra hle
  push Not at hle
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact absurd hle (not_le.2 (ssP_SC _ _).1)
  have hDΩ : D ≤ Om 1 := hv.le.trans (psi_lt Low.InR_Om_one _).le
  have hprev : ∀ d'', d'' < D → d'' < ssP μ (c + d) →
      S.psi (B + Le.leOe μ * d'') (Om 1) < ssP μ (c + d) := fun d'' hd'' hq =>
    (sv_UB hμ B c d'' hB hc.ge (hd''.le.trans hDΩ)).trans_lt
      ((ssP_lt_iff μ).2 ((add_lt_add_iff_left c).2 (hq.trans_le hle)))
  have h := sv_inv (S := S) hμ hB (ssP_SC μ (c + d)) (sv_clo_val μ _)
    (by rw [← hc]; exact (ssP_lt_iff μ).2 (lt_add_of_pos_right _ (pos_iff_ne_zero.2 hd0))) hDΩ hprev
  exact absurd ((h.trans hle).trans hd) (not_le.2 hv)

/-- An `ε`-number `p ≥ Γ_{Ω₁+1}` is a multiple of every `u_μ`, `μ ≤ Γ_{Ω₁+1}`. -/
theorem sv_dvd_eps {μ p : Ordinal.{0}} (hμ : μ ≤ ggGam) (hp : ω ^ p = p) (hG : ggGam ≤ p) :
    Le.leOe μ ∣ p := by
  have hI : Indec p := inE_indec hp
  have hk : Om 1 * μ ≤ p := by
    have hGG : Om 1 * ggGam = ggGam := by
      conv_lhs => rw [← Bt.Om1_opow, ← sv_Gam_inE]
      rw [← opow_add, Ordinal.add_of_omega0_opow_le (by rw [sv_Gam_inE]; exact ggGam_spec.2) sv_Gam_inE.le,
        sv_Gam_inE]
    calc Om 1 * μ ≤ Om 1 * ggGam := mul_le_mul_right hμ _
      _ = ggGam := hGG
      _ ≤ p := hG
  refine rh_dvd_of_indec μ hI ?_
  unfold Le.leOe
  rw [← hp]
  exact opow_le_opow_right omega0_pos hk

end Googology.Trans.PoR.InaccPsi.R2.Sv
