import Googology.Trans.PoR.InaccPsi.R2.UlEq
import Googology.Trans.PoR.InaccPsi.R2.UiArgs

/-!
# CONV at every level of the lifted hierarchy, and the instance `s = 0`: the levels `Φ_μ` below `Ω₂`

`ψ = S.psi · W`, `W = Ω_{s+1}`, `L = Ω_s`, `Hˡ_γ = ulH S s γ`, `K_q = UlK S s q`, `ulD` (`R2.UlK`, `R2.UlUB`,
`R2.UlEq`).  An argument `B` is *own* when `B ∈ Cl(B, ψ(B))`.

* `ulK_of_succ` (`j + 1 ∈ K_q ⇒ j ∈ K_q`), `ulD_le_succ` (**the visibility datum of `j` is at most that of `j + 1`**
  at every strongly critical point);
* `UlCONV`, `ul_conv` (**CONV(γ) at every level `γ`, no hypothesis**: `W^{γ+1} ∣ B` for every own `B` with `ψ(B)` a
  fixed point of `Hˡ_γ`);
* the instance `s = 0` (`W = Ω₁`, `L = 0`, `V = Ω₂`): `Φ_μ := Hˡ_μ` at every level `μ < Ω₂`, in particular at every
  `μ < θ = ψ_{Ω₂}(Ω_ω)`: `ul_phi_UB` (**UB: `ψ_{Ω₁}(B + Ω₁^μ·D) ≤ Φ_μ(c + D)`**), `ul_phi_inv` (**INV**), `ul_phi_conv`
  (**CONV**), all unconditional; `ul_phi_fwd` (**FWD**), `ul_phi_eq` (**EQ: `ψ_{Ω₁}(B + Ω₁^μ·D) = Φ_μ(c + D)`**) under
  `UlDV S 0`; `ul_phi_eq_ui` (**`Φ_μ = H⁰_μ` below `ε_{Ω₁+1}`**), `ul_th_lt_Om2` (`θ < Ω₂`).

No new axiom.  New definition: the statement name `UlCONV`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ul

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Uc

variable {S : InaccSeq.{0}} {s : Ordinal.{0}}

/-- `j + 1 ∈ K_q ⇒ j ∈ K_q`. -/
theorem ulK_of_succ {q : Ordinal.{0}} (hq : SC q) {j : Ordinal.{0}} (h : UlK S s q (j + 1)) : UlK S s q j := by
  have hω0 : (ω : Ordinal.{0}) ≠ 0 := omega0_pos.ne'
  have hfin : j % ω + 1 < ω := isSuccLimit_omega0.add_one_lt (Ordinal.mod_lt j hω0)
  have hdec : j + 1 = ω * (j / ω) + (j % ω + 1) := by rw [← add_assoc, Ordinal.div_add_mod]
  have hd : (j + 1) / ω = j / ω := by
    rw [hdec, Ordinal.mul_add_div _ hω0, Ordinal.div_eq_zero_of_lt hfin, add_zero]
  have h1 : UlK S s q ((j + 1) / ω ^ (1 : Ordinal.{0})) := ulK_div hq _ h 1 UlK.one
  rw [opow_one, hd] at h1
  have h2 : UlK S s q (ω ^ (1 : Ordinal.{0}) * (j / ω)) := ulK_opow_mul hq UlK.one _ h1
  rw [opow_one] at h2
  obtain ⟨n, hn⟩ := lt_omega0.1 (Ordinal.mod_lt j hω0)
  have h3 : UlK S s q (j % ω) := by rw [hn]; exact UlK.nat n
  rw [← Ordinal.div_add_mod j ω]; exact UlK.add h2 h3

/-- **`ulD j < q` whenever `ulD (j + 1) < q`** (`q` strongly critical). -/
theorem ulD_le_succ {q j : Ordinal.{0}} (hq : SC q) (h : ulD S s (j + 1) < q) : ulD S s j < q :=
  (ul_vis hq).2 (ulK_of_succ hq ((ul_vis hq).1 h))

/-- **CONV(γ)**: `W^{γ+1} ∣ B` for every own `B` with `ψ(B)` a fixed point of `Hˡ_γ`. -/
def UlCONV (S : InaccSeq.{0}) (s γ : Ordinal.{0}) : Prop :=
  ∀ B : Ordinal.{0}, B ∈ S.CSet B (S.psi B (Om (s + 1))) →
    ulH S s γ (S.psi B (Om (s + 1))) = S.psi B (Om (s + 1)) → Om (s + 1) ^ (γ + 1) ∣ B

/-- **CONV(γ) at every level `γ`** (no hypothesis). -/
theorem ul_conv (hs : s < ω) : ∀ γ : Ordinal.{0}, UlCONV S s γ := by
  have hκ : S.InR (Om (s + 1)) := InR_Om_succ s
  intro γ
  induction γ using WellFoundedLT.induction with
  | ind γ IH =>
  intro B hown hfix
  set p := S.psi B (Om (s + 1)) with hpdef
  have hpSC : SC p := Ui.ui_psi_SC B
  have hpL : Om s < p := Ui.ui_L_lt_psi B
  have hK : UlK S s p B := ul_K_of_mem hown
  have hu : Om (s + 1) ^ γ ∣ B := by
    rcases zero_or_succ_or_isSuccLimit γ with hz | ⟨j, rfl⟩ | hl
    · rw [hz, opow_zero]; exact one_dvd B
    · rw [Order.succ_eq_add_one] at hfix ⊢
      have hC1 := ulH_D_lt (S := S) (s := s) (j + 1) p
      rw [hfix] at hC1
      have hfixj : ulH S s j p = p := ucG_fix_mono le_self_add hfix (ulD_le_succ hpSC hC1)
      exact IH j (Order.lt_succ j) B hown hfixj
    · by_contra hnd
      have hR0 : B % Om (s + 1) ^ γ ≠ 0 := fun h => hnd (Ordinal.dvd_of_mod_eq_zero h)
      have hRlt : B % Om (s + 1) ^ γ < Om (s + 1) ^ γ := Ordinal.mod_lt _ (Ui.ui_W_pos s γ).ne'
      have hRK : UlK S s p (B % Om (s + 1) ^ γ) := ulK_modW hpSC hK γ
      set R := B % Om (s + 1) ^ γ with hRdef
      set j0 := log (Om (s + 1)) R with hj0
      have hj0l : j0 < γ := by
        have h1 : Om (s + 1) ^ j0 ≤ R := opow_log_le_self _ hR0
        exact (opow_lt_opow_iff_right (Ui.ui_one_lt_W s)).1 (h1.trans_lt hRlt)
      have hj0K : UlK S s p j0 := by
        have hdg := ulK_dig hs hpSC hRK j0
        have hdpos : R / Om (s + 1) ^ j0 ≠ 0 :=
          ((Ordinal.div_pos (Ui.ui_W_pos s j0).ne').2 (opow_log_le_self _ hR0)).ne'
        rw [Ordinal.mod_eq_of_lt (Ui.ui_div_lt s R)] at hdg
        exact hdg.2 hdpos
      have hj1l : j0 + 1 < γ := hl.add_one_lt hj0l
      have hj1c : ulD S s (j0 + 1) < p := (ul_vis hpSC).2 (UlK.add hj0K UlK.one)
      have hfixj : ulH S s (j0 + 1) p = p := ucG_fix_mono hj1l.le hfix hj1c
      have hdiv := IH (j0 + 1) hj1l B hown hfixj
      have hd2 : Om (s + 1) ^ (j0 + 1 + 1) ∣ Om (s + 1) ^ γ * (B / Om (s + 1) ^ γ) :=
        (opow_dvd_opow _ (Order.add_one_le_of_lt hj1l)).trans (dvd_mul_right _ _)
      have hdR : Om (s + 1) ^ (j0 + 1 + 1) ∣ R := by
        have h := hdiv
        rw [← Ordinal.div_add_mod B (Om (s + 1) ^ γ)] at h
        exact (Ordinal.dvd_add_iff hd2).1 h
      have h1 : Om (s + 1) ^ (j0 + 1 + 1) ≤ R := Ordinal.le_of_dvd hR0 hdR
      have h2 : R < Om (s + 1) ^ (j0 + 1) := lt_opow_succ_log_self (Ui.ui_one_lt_W s) R
      have h3 : Om (s + 1) ^ (j0 + 1) ≤ Om (s + 1) ^ (j0 + 1 + 1) :=
        opow_le_opow_right (Ui.ui_SC_W s).1 le_self_add
      exact absurd (h3.trans h1) (not_le.2 h2)
  set u := Om (s + 1) ^ γ with hudef
  set u2 := Om (s + 1) ^ (γ + 1) with hu2def
  have hu2 : u2 = u * (Om (s + 1)) := Ui.ui_W_succ s γ
  have huu2 : u ∣ u2 := opow_dvd_opow _ le_self_add
  have hupos : 0 < u := Ui.ui_W_pos s γ
  have hu0 : u ≠ 0 := hupos.ne'
  obtain ⟨m, hm⟩ := hu
  by_contra hnd
  set D0 := m % (Om (s + 1)) with hD0
  set B0 := u2 * (m / (Om (s + 1))) with hB0
  have hBe : B0 + u * D0 = B := by
    rw [hm, hB0, hD0, hu2, mul_assoc, ← mul_add, Ordinal.div_add_mod]
  have hD0lt : D0 < Om (s + 1) := Ordinal.mod_lt m (Ui.ui_SC_W s).1.ne'
  have hD00 : D0 ≠ 0 := by
    intro e
    apply hnd
    rw [← hBe, e, mul_zero, add_zero, hB0]
    exact dvd_mul_right _ _
  have hmdiv : B / u = m := by rw [hm, Ordinal.mul_div_cancel _ hu0]
  have hD0p : D0 < p := by
    have hdg := (ulK_dig hs hpSC hK γ).1
    rw [← hudef, hmdiv] at hdg
    exact ulK_lt_W hs hpSC hpL hdg hD0lt
  have hlt' : u * D0 < u2 := by rw [hu2]; exact (mul_lt_mul_iff_right₀ hupos).2 hD0lt
  have hBdiv : B / u2 = m / (Om (s + 1)) := by
    calc B / u2 = (u2 * (m / (Om (s + 1))) + u * D0) / u2 := by rw [← hB0, hBe]
      _ = m / (Om (s + 1)) := by
        rw [Ordinal.mul_add_div _ (Ui.ui_W_pos s _).ne', Ordinal.div_eq_zero_of_lt hlt', add_zero]
  have hB0m : B0 ∈ S.CSet B p := by
    have := Ui.ui_mod_mem (S := S) (s := s) (m := γ + 1) le_add_self B hown
    rwa [← hu2def, hBdiv] at this
  have hB0B : B0 < B := by
    rw [← hBe]; exact lt_add_of_pos_right _ (mul_pos hupos (pos_iff_ne_zero.2 hD00))
  have hB0p : S.psi B0 (Om (s + 1)) < p := psi_lt_psi_of_mem hκ hB0B hB0m
  have hle := ulUB (S := S) hs γ B0 (S.psi B0 (Om (s + 1))) D0
    (by rw [hB0]; exact huu2.trans (dvd_mul_right _ _)) (ulH_le_self (S := S) (s := s) _ _) hD0lt.le
  rw [hBe] at hle
  have hlt : S.psi B0 (Om (s + 1)) + D0 < p := (Lq.lq_SC_indec hpSC).add_lt hB0p hD0p
  have h2 : ulH S s γ (S.psi B0 (Om (s + 1)) + D0) < p := by
    conv_rhs => rw [← hfix]
    exact (ulH_lt_iff (S := S) (s := s) γ).2 hlt
  exact absurd (hle.trans_lt h2) (lt_irrefl _)

/-! ## The instance `s = 0`: the levels `Φ_μ = Hˡ_μ` of `ψ_{Ω₁}` below `Ω₂` -/

/-- `θ = ψ_{Ω₂}(Ω_ω) < Ω₂`: every level below `θ` is a lifted level of `s = 0`. -/
theorem ul_th_lt_Om2 : ConjT.th S < Om (0 + 1 + 1) := by
  rw [zero_add]; exact Ui.ui_th_lt_Om2

/-- **UB at every level `μ`** (`s = 0`): `ψ_{Ω₁}(B + Ω₁^μ·D) ≤ Φ_μ(c + D)` for `Ω₁^μ ∣ B`, `ψ_{Ω₁}(B) ≤ Φ_μ(c)`,
`D ≤ Ω₁`. -/
theorem ul_phi_UB (μ : Ordinal.{0}) : UlUB S 0 μ := ulUB omega0_pos μ

/-- **INV at every level `μ`** (`s = 0`). -/
theorem ul_phi_inv {μ B D q : Ordinal.{0}} (hB : Om (0 + 1) ^ μ ∣ B) (hq : SC q)
    (hcl : ∀ j < μ, ulD S 0 j < q → ∀ z < q, ulH S 0 j z < q) (hBq : S.psi B (Om (0 + 1)) < q)
    (hD : D ≤ Om (0 + 1)) (hprev : ∀ d, d < D → d < q → S.psi (B + Om (0 + 1) ^ μ * d) (Om (0 + 1)) < q) :
    S.psi (B + Om (0 + 1) ^ μ * D) (Om (0 + 1)) ≤ q :=
  ulInv omega0_pos hB hq hcl hBq hD hprev

/-- **CONV at every level `μ`** (`s = 0`). -/
theorem ul_phi_conv (μ : Ordinal.{0}) : UlCONV S 0 μ := ul_conv omega0_pos μ

/-- **FWD at every level `μ < Ω₂`** (`s = 0`), given `UlDV S 0`. -/
theorem ul_phi_fwd (hDV : UlDV S 0) {μ : Ordinal.{0}} (hμ : μ < Om (0 + 1 + 1)) : UlFWD S 0 μ :=
  ul_fwd omega0_pos hDV μ hμ

/-- **EQ at every level `μ < Ω₂`** (`s = 0`), given `UlDV S 0`: `ψ_{Ω₁}(B + Ω₁^μ·D) = Φ_μ(c + D)`. -/
theorem ul_phi_eq (hDV : UlDV S 0) {μ B c D : Ordinal.{0}} (hμ : μ < Om (0 + 1 + 1))
    (hown : B ∈ S.CSet B (S.psi B (Om (0 + 1)))) (hB : Om (0 + 1) ^ μ ∣ B)
    (hμB : μ ∈ S.CSet B (S.psi B (Om (0 + 1)))) (hc : ulH S 0 μ c = S.psi B (Om (0 + 1)))
    (hD : D < Om (0 + 1)) (hcond : ∀ d, d ≤ D → d < ulH S 0 μ (c + d)) :
    D < S.psi (B + Om (0 + 1) ^ μ * D) (Om (0 + 1)) ∧
      S.psi (B + Om (0 + 1) ^ μ * D) (Om (0 + 1)) = ulH S 0 μ (c + D) :=
  ul_eq_all omega0_pos hDV hμ hown hB hμB hc hD hcond

/-- **`Φ_μ = H⁰_μ` below `ε_{Ω₁+1}`.** -/
theorem ul_phi_eq_ui {μ : Ordinal.{0}} (hμ : μ < Ui.uiE 0) : ulH S 0 μ = Ui.uiH 0 μ := ulH_eq_uiH omega0_pos hμ

end Googology.Trans.PoR.InaccPsi.R2.Ul
