import Googology.Trans.PoR.InaccPsi.R2.CitedRj
import Googology.Trans.PoR.InaccPsi.R2.RjArg
import Googology.Trans.PoR.InaccPsi.R2.RiTh
import Googology.Trans.PoR.InaccPsi.R2.LqLh
import Googology.Trans.PoR.InaccPsi.R2.GgFront
import Googology.Trans.PoR.InaccPsi.R2.RkArgT

/-!
# The terms `ϑᵗ(Ω₁·M + η)` at every level `Ω₁ ≤ M < ε_{Ω₁+1}`

`Ω₁ = Om1`, `ε_{Ω₁+1} = Gg.ggE`, `rjDat` the data of a code (`Rj.rjDat`), `Θ_y = Gg.ggTh y`; `τ` a strongly critical
base `< Ω₁`.  From the cited facts of `R2.CitedRj` (generic in the level):

* `rj_E_le_Om2`, `rj_arg_lt`, `rj_Om1_le_arg`;
* `rjK_facts` (**`ϑᵗ(Ω₁·M + η)` is an `ε`-number in `(τ, Ω₁) ∩ Tᵗ` above `rjDat M` and `η`**), `rjK_lt` (**`η ↦
  ϑᵗ(Ω₁·M + η)` is strictly increasing**), `rjK_lt_lower` (**a lower level `M' < M` stays below**), `rjK_lt_iff`
  (**Lemma 3.30 between two levels, both directions**), `rjK_SC` (**`ϑᵗ(Ω₁·M + η)` is strongly critical**: the `SC`
  hypothesis of `R2.rjLhT` is a theorem);
* `rj_Th_mul` (**`Θ_y(Ω₁·M) = y·Θ_y(M)`**), `rj_code_of` (**`M` is a code over `ϑᵗ(Ω₁·M + η)`**);
* `rjArg_T` (**`R2.riArg_T` from `Rk.rkArgT_gamma` and the theorem `rjArgT_beta`**), `rjLq_arg` (**`R2.lqArg_mem`
  from `R2.rjArg_mem`**), `rjLq_lh` (**the equation of `R2.lqLhT` from `R2.rjLhT`** at `M = Ω₁·γ + β`, a strongly
  critical base): the new cited facts agree with the old ones on their common range.

No new axiom beyond `R2.CitedRj`, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Rj

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gg

theorem rj_E_le_Om2 : (ggE : Ordinal.{0}) ≤ OmTwo := by
  have h := ggE_le_ggGam.trans ggGam_le_Om2
  rwa [Om_of_ne_zero (by norm_num), one_add_one_eq_two] at h

theorem rj_arg_lt {M η : Ordinal.{0}} (hME : M < ggE) (hηΩ : η < Om1) : Om1 * M + η < OmTwo := by
  have hO : Om1 < OmTwo := Om1_lt_OmTwo
  have h1 : M < OmTwo := hME.trans_le rj_E_le_Om2
  exact isPrincipal_add_omega 2 (isPrincipal_mul_omega 2 hO h1) (hηΩ.trans hO)

theorem rj_Om1_le_arg {M η : Ordinal.{0}} (hM1 : Om1 ≤ M) : Om1 ≤ Om1 * M + η :=
  (le_mul_of_one_le_right zero_le ((one_le_iff_pos.2 rj_Om1_pos).trans hM1)).trans le_self_add

section Base

variable {τ : Ordinal.{0}} (hτ : SC τ) (hτ1 : τ < Om1)
include hτ hτ1

/-- **The facts on `ϑᵗ(Ω₁·M + η)`** at a level `Ω₁ ≤ M < ε_{Ω₁+1}` with `rjDat M ∈ Tᵗ`. -/
theorem rjK_facts {M η : Ordinal.{0}} (hM1 : Om1 ≤ M) (hME : M < ggE) (hMT : rjDat M ∈ Tset τ)
    (hη : η ∈ Tset τ) (hηΩ : η < Om1) :
    Om1 * M + η ∈ Tset τ ∧ Om1 * M + η < OmTwo ∧ vt τ (Om1 * M + η) ∈ Tset τ ∧ τ < vt τ (Om1 * M + η) ∧
    vt τ (Om1 * M + η) < Om1 ∧ InE (vt τ (Om1 * M + η)) ∧ Indec (vt τ (Om1 * M + η)) ∧
    rjDat M < vt τ (Om1 * M + η) ∧ η < vt τ (Om1 * M + η) := by
  have hτE : InE τ := gg_SC_eps hτ
  have hargT := rjArg_mem hτE hτ1 hM1 hME hMT hη hηΩ
  have harg2 := rj_arg_lt hME hηΩ
  obtain ⟨hvT, -, hv1, hvP, -⟩ := vt_memTwo hτE hτ1 hargT harg2
  have hE := (vt_E_iff hτE hτ1 hargT harg2).2 (rj_Om1_le_arg hM1)
  have hl := rjLevel_lt_vt hτE hτ1 hM1 hME hMT hη hηΩ
  exact ⟨hargT, harg2, hvT, hE.1, hv1, hE.2, hvP, hl.1, hl.2⟩

/-- **`η ↦ ϑᵗ(Ω₁·M + η)` is strictly increasing.** -/
theorem rjK_lt {M σ η : Ordinal.{0}} (hM1 : Om1 ≤ M) (hME : M < ggE) (hMT : rjDat M ∈ Tset τ)
    (hσ : σ ∈ Tset τ) (hη : η ∈ Tset τ) (hηΩ : η < Om1) (h : σ < η) :
    vt τ (Om1 * M + σ) < vt τ (Om1 * M + η) := by
  have hτE : InE τ := gg_SC_eps hτ
  obtain ⟨-, -, -, -, -, -, -, hMv, hηv⟩ := rjK_facts hτ hτ1 hM1 hME hMT hη hηΩ
  exact rjVt_lt hτE hτ1 hME hMT hσ (h.trans hηΩ) hM1 hME hMT hη hηΩ ((add_lt_add_iff_left _).2 h) hMv
    (h.trans hηv)

/-- **A lower level stays below**: `ϑᵗ(Ω₁·M' + σ) < ϑᵗ(Ω₁·M + η)` for a code `M' < M` with `rjDat M'` and `σ` below
the right side. -/
theorem rjK_lt_lower {M' M σ η : Ordinal.{0}} (hM1 : Om1 ≤ M) (hME : M < ggE) (hMT : rjDat M ∈ Tset τ)
    (hM' : M' < M) (hσ : σ ∈ Tset τ) (hσΩ : σ < Om1) (hη : η ∈ Tset τ) (hηΩ : η < Om1)
    (hσv : σ < vt τ (Om1 * M + η)) (hM'v : rjDat M' < vt τ (Om1 * M + η)) :
    vt τ (Om1 * M' + σ) < vt τ (Om1 * M + η) := by
  have hτE : InE τ := gg_SC_eps hτ
  obtain ⟨-, -, hvT, -, hv1, -, -, -, -⟩ := rjK_facts hτ hτ1 hM1 hME hMT hη hηΩ
  have hM'T : rjDat M' ∈ Tset τ := vz_T_down hτE hτ1 hvT hv1 hM'v.le
  refine rjVt_lt hτE hτ1 (hM'.trans hME) hM'T hσ hσΩ hM1 hME hMT hη hηΩ ?_ hM'v hσv
  calc Om1 * M' + σ < Om1 * M' + Om1 := (add_lt_add_iff_left _).2 hσΩ
    _ = Om1 * (M' + 1) := by rw [mul_add_one]
    _ ≤ Om1 * M := mul_le_mul_right (Order.add_one_le_of_lt hM') _
    _ ≤ _ := le_self_add

/-- **Lemma 3.30 between two levels**: for codes `Ω₁ ≤ M', M < ε_{Ω₁+1}` with data in `Tᵗ`, each side's data and
remainder below the other side's value, `ϑᵗ(Ω₁·M' + σ) < ϑᵗ(Ω₁·M + η) ↔ Ω₁·M' + σ < Ω₁·M + η`. -/
theorem rjK_lt_iff {M' σ M η : Ordinal.{0}} (hM'1 : Om1 ≤ M') (hM'E : M' < ggE) (hM'T : rjDat M' ∈ Tset τ)
    (hσ : σ ∈ Tset τ) (hσΩ : σ < Om1) (hM1 : Om1 ≤ M) (hME : M < ggE) (hMT : rjDat M ∈ Tset τ)
    (hη : η ∈ Tset τ) (hηΩ : η < Om1) (hd1 : rjDat M' < vt τ (Om1 * M + η)) (hσ1 : σ < vt τ (Om1 * M + η))
    (hd2 : rjDat M < vt τ (Om1 * M' + σ)) (hη2 : η < vt τ (Om1 * M' + σ)) :
    vt τ (Om1 * M' + σ) < vt τ (Om1 * M + η) ↔ Om1 * M' + σ < Om1 * M + η := by
  have hτE : InE τ := gg_SC_eps hτ
  obtain ⟨hξT, hξ2, -⟩ := rjK_facts hτ hτ1 hM'1 hM'E hM'T hσ hσΩ
  exact ⟨rjLt_of_vt_lt hτE hτ1 hξT hξ2 hM1 hME hMT hη hηΩ hd2 hη2,
    fun h => rjVt_lt hτE hτ1 hM'E hM'T hσ hσΩ hM1 hME hMT hη hηΩ h hd1 hσ1⟩

/-- **`ϑᵗ(Ω₁·M + η)` is strongly critical** at every level `Ω₁ ≤ M < ε_{Ω₁+1}` (the argument of `Ri.riK_SC`, with
`R2.rjVt_lt` at the lower levels `Ω₁·a + ι`, `a < Ω₁`). -/
theorem rjK_SC {M η : Ordinal.{0}} (hM1 : Om1 ≤ M) (hME : M < ggE) (hMT : rjDat M ∈ Tset τ)
    (hη : η ∈ Tset τ) (hηΩ : η < Om1) : SC (vt τ (Om1 * M + η)) := by
  have hτE : InE τ := gg_SC_eps hτ
  obtain ⟨-, -, hvT, hτv, hv1, hvE, -, -, -⟩ := rjK_facts hτ hτ1 hM1 hME hMT hη hηΩ
  set v := vt τ (Om1 * M + η) with hv
  have hvE' : ω ^ v = v := hvE
  have hvl : IsSuccLimit v := ev_isSuccLimit_of_inE hvE
  have hTv : ∀ z, z < v → z ∈ Tset τ := fun z hz => vz_T_down hτE hτ1 hvT hv1 hz.le
  have key : ∀ a b, 1 ≤ a → a < v → (τ < a → ¬ SC a) → b < v → veblen a b < v := by
    intro a b ha1 hav haSC hbv
    by_cases hfix : veblen a b = b
    · rw [hfix]; exact hbv
    by_cases hle : veblen a b ≤ τ
    · exact hle.trans_lt hτv
    push Not at hle
    have hbP : ¬ Lu.LuP (a + 1) b := fun h => hfix (Lu.luP_succ.1 h)
    have hind : lvInd a τ b ≤ b := Cd.cdOtp_le_self _ b
    have hindv : lvInd a τ b < v := hind.trans_lt hbv
    have haT := hTv a hav
    have haΩ : a < Om1 := hav.trans hv1
    rw [lvPhLev hτ hτ1 ha1 haT haΩ (Mx.mxLev_u ha1 haSC) b hle hbP (hTv _ hindv) (hindv.trans hv1)]
    have haE : a < ggE := haΩ.trans rj_Om1_lt_E
    have harg : Om1 * a + lvInd a τ b < Om1 * M + η := by
      calc Om1 * a + lvInd a τ b < Om1 * a + Om1 := (add_lt_add_iff_left _).2 (hindv.trans hv1)
        _ = Om1 * (a + 1) := by rw [mul_add, mul_one]
        _ ≤ Om1 * Om1 := mul_le_mul_right (Order.add_one_le_of_lt haΩ) Om1
        _ ≤ Om1 * M := mul_le_mul_right hM1 _
        _ ≤ _ := le_self_add
    exact rjVt_lt hτE hτ1 haE (by rw [rjDat_small haΩ]; exact haT) (hTv _ hindv) (hindv.trans hv1) hM1 hME hMT
      hη hηΩ harg (by rw [rjDat_small haΩ]; exact hav) hindv
  refine ⟨hvE.pos, fun a ha b hb => ?_⟩
  rcases eq_or_ne a 0 with rfl | ha0
  · rw [veblen_zero_apply, ← hvE']; exact (opow_lt_opow_iff_right one_lt_omega0).2 hb
  have ha1 : 1 ≤ a := one_le_iff_ne_zero.2 ha0
  by_cases hs : τ < a ∧ SC a
  · have ha1v : a + 1 < v := hvl.add_one_lt ha
    have hnsc : τ < a + 1 → ¬ SC (a + 1) := fun _ h => SC.ne_add_one h a rfl
    have h2 := key (a + 1) b (le_add_self) ha1v hnsc hb
    have h3 : veblen a b ≤ veblen (a + 1) b := by
      calc veblen a b ≤ veblen a (veblen (a + 1) b) :=
            veblen_le_veblen_iff_right.2 (right_le_veblen _ _)
        _ = veblen (a + 1) b := veblen_veblen_of_lt (lt_add_one a) b
    exact h3.trans_lt h2
  · push Not at hs
    exact key a b ha1 ha hs hb

/-- **`M` is a code over `ϑᵗ(Ω₁·M + η)`.** -/
theorem rj_code_of {M η : Ordinal.{0}} (hM1 : Om1 ≤ M) (hME : M < ggE) (hMT : rjDat M ∈ Tset τ)
    (hη : η ∈ Tset τ) (hηΩ : η < Om1) : GgCl (vt τ (Om1 * M + η)) M := by
  obtain ⟨-, -, -, -, -, hvE, -, hMv, -⟩ := rjK_facts hτ hτ1 hM1 hME hMT hη hηΩ
  exact rj_code hvE.pos M hME hMv

end Base

/-- **`Θ_y(Ω₁·M) = y·Θ_y(M)`** for a code `M` over a strongly critical `y < Ω₁`. -/
theorem rj_Th_mul {y M : Ordinal.{0}} (hy : SC y) (hy1 : y < Om1) (hM : GgCl y M) :
    ggTh y (Om1 * M) = y * ggTh y M := by
  have hy1' : y < Om 1 := by rw [← rj_Om1]; exact hy1
  have e : (Om1 : Ordinal.{0}) * M = ω ^ (Om 1) * M := by rw [Bt.Om1_opow, rj_Om1]
  rw [e, Ph.phTh_opow_mul hy GgCl.om M hM, ggTh_Om1 hy hy1', gg_SC_eps hy]

/-- **`R2.riArg_T` without `R2.riArg_T`**: from the `γ` half `Rk.rkArgT_gamma` and the theorem `rjArgT_beta`. -/
theorem rjArg_T {τ γ β η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hγΩ : γ < Om1) (hβΩ : β < Om1)
    (hηΩ : η < Om1) (h : Om1 * (Om1 * γ + β) + η ∈ Tset τ) : γ ∈ Tset τ ∧ β ∈ Tset τ :=
  ⟨Rk.rkArgT_gamma hτ hτ1 hγΩ hβΩ hηΩ h, rjArgT_beta hτ hτ1 hγΩ hβΩ hηΩ h⟩

/-- The data of a level of `R2.CitedLq` lie in `Tᵗ`. -/
theorem rjLq_dat {τ γ β : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hγ : γ ∈ Tset τ) (hγΩ : γ < Om1)
    (hβ : β ∈ Tset τ) (hβΩ : β < Om1) : rjDat (Om1 * γ + β) ∈ Tset τ := by
  have hle := rjDat_OmL hβΩ γ hγΩ
  rcases le_total γ β with h | h
  · rw [max_eq_right h] at hle; exact vz_T_down hτ hτ1 hβ hβΩ hle
  · rw [max_eq_left h] at hle; exact vz_T_down hτ hτ1 hγ hγΩ hle

/-- **`R2.lqArg_mem` from `R2.rjArg_mem`.** -/
theorem rjLq_arg {τ γ β η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hγ1 : 1 ≤ γ) (hγ : γ ∈ Tset τ)
    (hγΩ : γ < Om1) (hβ : β ∈ Tset τ) (hβΩ : β < Om1) (hη : η ∈ Tset τ) (hηΩ : η < Om1) :
    Om1 * (Om1 * γ + β) + η ∈ Tset τ := by
  have hE := rj_E_inE
  have hM1 : Om1 ≤ Om1 * γ + β := (le_mul_of_one_le_right zero_le hγ1).trans le_self_add
  have hME : Om1 * γ + β < ggE :=
    hE.add_lt (hE.mul_lt rj_Om1_lt_E (hγΩ.trans rj_Om1_lt_E)) (hβΩ.trans rj_Om1_lt_E)
  exact rjArg_mem hτ hτ1 hM1 hME (rjLq_dat hτ hτ1 hγ hγΩ hβ hβΩ) hη hηΩ

/-- **The equation of `R2.lqLhT` from `R2.rjLhT`** at the levels `M = Ω₁·γ + β` (`1 ≤ γ`), over a strongly critical
base: the new cited `lhᵗ` agrees with the old one (`Θ_α(Ω₁·(Ω₁·γ + β)) = α·(α·γ + β)`, `log_ω` of it `= α·2 +
log_ω γ`). -/
theorem rjLq_lh {τ γ β η : Ordinal.{0}} (hτ : SC τ) (hτ1 : τ < Om1) (hγ1 : 1 ≤ γ) (hγ : γ ∈ Tset τ)
    (hγΩ : γ < Om1) (hβ : β ∈ Tset τ) (hβΩ : β < Om1) (hη : η ∈ Tset τ) (hηΩ : η < Om1) :
    lhT τ (vt τ (Om1 * (Om1 * γ + β) + η)) =
      lhT τ (vt τ (Om1 * (Om1 * γ + β) + η) * vt τ (Om1 * (Om1 * γ + β) + η) * ω ^ log ω γ) +
        ((vt τ (Om1 * (Om1 * γ + β) + η) * (vt τ (Om1 * (Om1 * γ + β) + η) * γ + β) +
            lqZeta τ (Om1 * (Om1 * γ + β)) η) -
          vt τ (Om1 * (Om1 * γ + β) + η) * vt τ (Om1 * (Om1 * γ + β) + η) * ω ^ log ω γ) := by
  have hτE : InE τ := gg_SC_eps hτ
  have hE := rj_E_inE
  set M := Om1 * γ + β with hMdef
  have hM1 : Om1 ≤ M := (le_mul_of_one_le_right zero_le hγ1).trans le_self_add
  have hME : M < ggE :=
    hE.add_lt (hE.mul_lt rj_Om1_lt_E (hγΩ.trans rj_Om1_lt_E)) (hβΩ.trans rj_Om1_lt_E)
  have hMT := rjLq_dat hτE hτ1 hγ hγΩ hβ hβΩ
  have hSC := rjK_SC hτ hτ1 hM1 hME hMT hη hηΩ
  obtain ⟨-, -, -, -, hv1, hvE, -, -, -⟩ := rjK_facts hτ hτ1 hM1 hME hMT hη hηΩ
  obtain ⟨-, -, -, -, -, -, -, hγv, hβv, -⟩ := Lq.lq_facts hτE hτ1 hγ1 hγ hγΩ hβ hβΩ hη hηΩ
  set a := vt τ (Om1 * M + η) with ha
  have haE : ω ^ a = a := hvE
  have hγT : GgCl a (Om1 * γ) := by
    refine rj_code hvE.pos _ ?_ ?_
    · exact hE.mul_lt rj_Om1_lt_E (hγΩ.trans rj_Om1_lt_E)
    · have h := rjDat_OmL (show (0 : Ordinal.{0}) < Om1 from rj_Om1_pos) γ hγΩ
      rw [add_zero] at h
      exact h.trans_lt (max_lt hγv hvE.pos)
  have hMcode : GgCl a M := rj_code hvE.pos M hME (rjK_facts hτ hτ1 hM1 hME hMT hη hηΩ).2.2.2.2.2.2.2.1
  have hTh : ggTh a (Om1 * M) = a * (a * γ + β) := by
    rw [rj_Th_mul hSC hv1 hMcode, hMdef, ggTh_add hSC hγT, rj_Th_mul hSC hv1 (GgCl.small hγv),
      ggTh_small hγv.le, ggTh_small hβv.le]
  have hγ0 : γ ≠ 0 := (lt_of_lt_of_le zero_lt_one hγ1).ne'
  have hlog : ω ^ log ω (a * (a * γ + β)) = a * a * ω ^ log ω γ := by
    have hf : a * (a * γ + β) = ω ^ (a * 2) * γ + a * β := by
      rw [mul_add, ← mul_assoc, mul_two_eq, opow_add, haE]
    have hlt : a * β < ω ^ (a * 2) := by
      rw [mul_two_eq, opow_add, haE]; exact (mul_lt_mul_iff_right₀ hvE.pos).2 hβv
    rw [hf, log_opow_mul_add one_lt_omega0 hγ0 hlt, opow_add, mul_two_eq, opow_add, haE]
  have h := rjLhT hτE hτ1 hM1 hME hMT hη hηΩ hSC
  rw [← ha, hTh, hlog] at h
  exact h

end Googology.Trans.PoR.InaccPsi.R2.Rj
