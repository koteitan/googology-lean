import Googology.Trans.PoR.InaccPsi.R2.CitedQf
import Googology.Trans.PoR.InaccPsi.R2.RjFacts
import Googology.Trans.PoR.InaccPsi.R2.TfSy
import Googology.Trans.PoR.InaccPsi.R2.SsDat
import Googology.Trans.PoR.InaccPsi.R2.QcBdV

/-!
# QfK: THE POINTS `ϑᵗ(Ω₁·M + η)` OF THE LEVELS `Ω₁ ≤ M < Γ_{Ω₁+1}`

`R2.RjFacts` for the levels `M < ε_{Ω₁+1}` (data `rjDat`), here for every level `Ω₁ ≤ M < Γ_{Ω₁+1}` with the data
`Tf.tfDat` (the generic citation `R2.CitedTf`):

* `qfK_facts` (**`ϑᵗ(Ω₁·M + η)` is an `ε`-number in `(τ, Ω₁) ∩ Tᵗ` above `tfDat M` and `η`**), `qfK_lt`,
  `qfK_lt_lower`, `qfK_SC` (**`ϑᵗ(Ω₁·M + η)` is strongly critical**: the `SC` hypothesis of `R2.qfLhT`), `qf_code_of`
  (**`M` is a code over `ϑᵗ(Ω₁·M + η)`**).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qf

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rj

theorem qf_gg_lt_BG : (ggGam : Ordinal.{0}) < Tf.tfBG := Tf.tf_gg_lt_BG

section Base

variable {τ : Ordinal.{0}} (hτ : SC τ) (hτ1 : τ < Om1)
include hτ hτ1

/-- **The facts on `ϑᵗ(Ω₁·M + η)`** at a level `Ω₁ ≤ M < Γ_{Ω₁+1}` with `tfDat M ∈ Tᵗ`. -/
theorem qfK_facts {M η : Ordinal.{0}} (hM1 : Om1 ≤ M) (hMG : M < ggGam) (hMT : Tf.tfDat M ∈ Tset τ)
    (hη : η ∈ Tset τ) (hηΩ : η < Om1) :
    Om1 * M + η ∈ Tset τ ∧ Om1 * M + η < OmTwo ∧ vt τ (Om1 * M + η) ∈ Tset τ ∧ τ < vt τ (Om1 * M + η) ∧
    vt τ (Om1 * M + η) < Om1 ∧ InE (vt τ (Om1 * M + η)) ∧ Indec (vt τ (Om1 * M + η)) ∧
    Tf.tfDat M < vt τ (Om1 * M + η) ∧ η < vt τ (Om1 * M + η) := by
  have hτE : InE τ := gg_SC_eps hτ
  have hMB : M < Tf.tfBG := hMG.trans qf_gg_lt_BG
  have hargT := tfArg_mem hτE hτ1 hM1 hMB hMT hη hηΩ
  have harg2 := Qd.qd_arg_lt hMG hηΩ
  obtain ⟨hvT, -, hv1, hvP, -⟩ := vt_memTwo hτE hτ1 hargT harg2
  have hE := (vt_E_iff hτE hτ1 hargT harg2).2 (rj_Om1_le_arg hM1)
  have hl := tfLevel_lt hτE hτ1 hM1 hMB hMT hη hηΩ
  exact ⟨hargT, harg2, hvT, hE.1, hv1, hE.2, hvP, hl.1, hl.2⟩

/-- **`η ↦ ϑᵗ(Ω₁·M + η)` is strictly increasing.** -/
theorem qfK_lt {M σ η : Ordinal.{0}} (hM1 : Om1 ≤ M) (hMG : M < ggGam) (hMT : Tf.tfDat M ∈ Tset τ)
    (hσ : σ ∈ Tset τ) (hη : η ∈ Tset τ) (hηΩ : η < Om1) (h : σ < η) :
    vt τ (Om1 * M + σ) < vt τ (Om1 * M + η) := by
  have hτE : InE τ := gg_SC_eps hτ
  obtain ⟨-, -, -, -, -, -, -, hMv, hηv⟩ := qfK_facts hτ hτ1 hM1 hMG hMT hη hηΩ
  exact tfVt_lt hτE hτ1 hM1 (hMG.trans qf_gg_lt_BG) le_rfl hMT hσ (h.trans hηΩ) hMT hη hηΩ
    ((add_lt_add_iff_left _).2 h) hMv (h.trans hηv)

/-- **A lower level stays below**: `ϑᵗ(Ω₁·M' + σ) < ϑᵗ(Ω₁·M + η)` for `M' < M` with `tfDat M'` and `σ` below the
right side. -/
theorem qfK_lt_lower {M' M σ η : Ordinal.{0}} (hM1 : Om1 ≤ M) (hMG : M < ggGam) (hMT : Tf.tfDat M ∈ Tset τ)
    (hM' : M' < M) (hσ : σ ∈ Tset τ) (hσΩ : σ < Om1) (hη : η ∈ Tset τ) (hηΩ : η < Om1)
    (hσv : σ < vt τ (Om1 * M + η)) (hM'v : Tf.tfDat M' < vt τ (Om1 * M + η)) :
    vt τ (Om1 * M' + σ) < vt τ (Om1 * M + η) := by
  have hτE : InE τ := gg_SC_eps hτ
  obtain ⟨-, -, hvT, -, hv1, -, -, -, -⟩ := qfK_facts hτ hτ1 hM1 hMG hMT hη hηΩ
  have hM'T : Tf.tfDat M' ∈ Tset τ := vz_T_down hτE hτ1 hvT hv1 hM'v.le
  refine tfVt_lt hτE hτ1 hM1 (hMG.trans qf_gg_lt_BG) hM'.le hM'T hσ hσΩ hMT hη hηΩ ?_ hM'v hσv
  calc Om1 * M' + σ < Om1 * M' + Om1 := (add_lt_add_iff_left _).2 hσΩ
    _ = Om1 * (M' + 1) := by rw [mul_add_one]
    _ ≤ Om1 * M := mul_le_mul_right (Order.add_one_le_of_lt hM') _
    _ ≤ _ := le_self_add

/-- **`ϑᵗ(Ω₁·M + η)` is strongly critical** at every level `Ω₁ ≤ M < Γ_{Ω₁+1}` (the proof of `Rj.rjK_SC`). -/
theorem qfK_SC {M η : Ordinal.{0}} (hM1 : Om1 ≤ M) (hMG : M < ggGam) (hMT : Tf.tfDat M ∈ Tset τ)
    (hη : η ∈ Tset τ) (hηΩ : η < Om1) : SC (vt τ (Om1 * M + η)) := by
  have hτE : InE τ := gg_SC_eps hτ
  obtain ⟨-, -, hvT, hτv, hv1, hvE, -, -, -⟩ := qfK_facts hτ hτ1 hM1 hMG hMT hη hηΩ
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
    have harg : Om1 * a + lvInd a τ b < Om1 * M + η := by
      calc Om1 * a + lvInd a τ b < Om1 * a + Om1 := (add_lt_add_iff_left _).2 (hindv.trans hv1)
        _ = Om1 * (a + 1) := by rw [mul_add, mul_one]
        _ ≤ Om1 * Om1 := mul_le_mul_right (Order.add_one_le_of_lt haΩ) Om1
        _ ≤ Om1 * M := mul_le_mul_right hM1 _
        _ ≤ _ := le_self_add
    have haM : a ≤ M := (haΩ.trans_le hM1).le
    exact tfVt_lt hτE hτ1 hM1 (hMG.trans qf_gg_lt_BG) haM (by rw [Tf.tfDat_small haΩ]; exact haT) (hTv _ hindv)
      (hindv.trans hv1) hMT hη hηΩ harg (by rw [Tf.tfDat_small haΩ]; exact hav) hindv
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
theorem qf_code_of {M η : Ordinal.{0}} (hM1 : Om1 ≤ M) (hMG : M < ggGam) (hMT : Tf.tfDat M ∈ Tset τ)
    (hη : η ∈ Tset τ) (hηΩ : η < Om1) : GgCl (vt τ (Om1 * M + η)) M := by
  obtain ⟨-, -, -, -, -, hvE, -, hMv, -⟩ := qfK_facts hτ hτ1 hM1 hMG hMT hη hηΩ
  exact Ss.ss_code hvE.pos M hMG (by rw [← Tf.tfDat_eq_ss M hMG]; exact hMv)

end Base

end Googology.Trans.PoR.InaccPsi.R2.Qf
