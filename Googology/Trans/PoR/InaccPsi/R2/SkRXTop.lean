import Googology.Trans.PoR.InaccPsi.R2.VxDyn
import Googology.Trans.PoR.InaccPsi.R2.VqWit
import Googology.Trans.PoR.InaccPsi.R2.CvNamed
import Googology.Trans.PoR.InaccPsi.R2.RlNoGo

/-!
# Refutation of the dynamic top with an image independent of the exponent (`skTopDyn`)

`Θ = gxTh ρ_λ (ldAtR λ)`, `T_X(β) = ψ₂(β + W^X)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `Y₂ = ψ₂(Ω₂)`.

`VtTopDyn λ 0 Ω₃ X̂ e` at `e = 0` and `e = 1` with ONE image `X̂` (not depending on `e`) is false:

* `e = 0`, `β = 0`: `Ω^{X̂(0)} ≤ Y₂` (`Vx.vxDyn_le0`), so `X̂(0) ≤ Y₂`;
* `e = 0`, `β = Ω₃`: `Y₂ < Ω^{X̂(Ω₃)}` (`Vx.vxDyn_gtOm3`), so `X̂(Ω₃) ≥ Y₂ + 1`, and
  `Θ(ψ₂(Ω₃ + Ω₃)) = ψ₁(A + 1 + Y₂ + Ω^{X̂(Ω₃)}) ≥ ψ₁(A + 1 + Ω^{Y₂+1})`;
* `e = 1`, `β = 0`: `Θ(ψ₂(Ω₃·Ω₂)) = ψ₁(A + 1 + Ω^{X̂(0)+1}) ≤ ψ₁(A + 1 + Ω^{Y₂+1})`;
* but `ψ₂(Ω₃ + Ω₃) < ψ₂(Ω₃·Ω₂)` is an atom, so `Θ(ψ₂(Ω₃ + Ω₃)) < Θ(ψ₂(Ω₃·Ω₂))`.

`skrxTopDynAll_false`: the skeleton statement `TopDynAll` (copied verbatim as `SkRXTopDynAll`) is false, with the
restart of `m* = L(0)` as witness.  No new axiom.  No new definition except the verbatim copy.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.SkRX

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Ro Googology.Trans.PoR.InaccPsi.R2.Rv
  Googology.Trans.PoR.InaccPsi.R2.Ug Googology.Trans.PoR.InaccPsi.R2.Uj Googology.Trans.PoR.InaccPsi.R2.Vk
  Googology.Trans.PoR.InaccPsi.R2.Vn Googology.Trans.PoR.InaccPsi.R2.Vq

variable {S : InaccSeq.{0}}

/-- `Ω₃ + Ω₃ < W^{Ω₃+1} = Ω₃·Ω₂`. -/
theorem skrxOm3_two_lt : Om (1 + 1 + 1 : Ordinal.{0}) + Om (1 + 1 + 1) < leWe (Om (1 + 1 + 1) + 1) := by
  have h3 : (1 + 1 + 1 : Ordinal.{0}) ≠ 0 := (add_pos_of_right zero_lt_one _).ne'
  have h1 : (1 : Ordinal.{0}) < Om (1 + 1) := gg_one_lt_of_SC ldOm2_SC
  have h2 : (1 + 1 : Ordinal.{0}) < Om (1 + 1) := ldOm2_SC.isPrincipal h1 h1
  rw [leWe_succ, vnWe_Om3]
  calc Om (1 + 1 + 1 : Ordinal.{0}) + Om (1 + 1 + 1) = Om (1 + 1 + 1) * (1 + 1) := by rw [mul_add, mul_one]
    _ < Om (1 + 1 + 1) * Om (1 + 1) := (mul_lt_mul_iff_right₀ (Om_pos h3)).2 h2

/-- **One image for `e = 0` and `e = 1` is impossible**: no `X̂` has both `VtTopDyn λ 0 Ω₃ X̂ 0` and
`VtTopDyn λ 0 Ω₃ X̂ 1`. -/
theorem skrxDyn01 {l ηx A : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
    (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)
    {Xh : Ordinal.{0} → Ordinal.{0}}
    (h0 : Vt.VtTopDyn S l 0 (Om (1 + 1 + 1)) Xh 0) (h1 : Vt.VtTopDyn S l 0 (Om (1 + 1 + 1)) Xh 1) : False := by
  have hκ1 : S.InR (Om 1) := Low.InR_Om_one
  have h3 : (1 + 1 + 1 : Ordinal.{0}) ≠ 0 := (add_pos_of_right zero_lt_one _).ne'
  set Y2 := S.psi (Om (1 + 1)) (Om (1 + 1)) with hY2
  have hY2SC : SC Y2 := SC_psi (InR_Om_succ 1) _
  have hΩ1Y2 : Om 1 < Y2 := (psiS_bounds (S := S) _ 1).1
  have hfix : leOe Y2 = Y2 := Ua.uaOe_fix (gg_SC_eps hY2SC) hΩ1Y2
  -- X̂(0) ≤ Y₂ and Y₂ + 1 ≤ X̂(Ω₃)
  have hle0 := Vx.vxDyn_le0 hl hX hA hρ h0
  have hgt := Vx.vxDyn_gtOm3 hl hX hA hρ h0
  have hX0 : Xh 0 ≤ Y2 := by
    by_contra h
    push Not at h
    have h' := leOe_lt h
    rw [hfix] at h'
    exact absurd hle0 (not_le.2 h')
  have hXO : Y2 < Xh (Om (1 + 1 + 1)) := by
    by_contra h
    push Not at h
    have h' := leOe_mono h
    rw [hfix] at h'
    exact absurd hgt (not_lt.2 h')
  have hXO1 : Xh 0 + 1 ≤ Xh (Om (1 + 1 + 1)) :=
    (add_le_add hX0 (le_refl (1 : Ordinal.{0}))).trans (Order.add_one_le_of_lt hXO)
  -- the reading at β = Ω₃, e = 0
  have hAω := vnA_ge hl hX hA hρ
  have hle : A ≤ A + 1 + Y2 := le_self_add.trans le_self_add
  have hΩ2 : Om (1 + 1) < A + 1 + Y2 := (vkOmW.2.trans_le hAω).trans_le hle
  have hÂ : A + 1 + Y2 ∈ S.CSet (A + 1 + Y2) (S.psi (A + 1 + Y2) (Om 1)) :=
    CSet.add_mem (CSet.add_mem ((psi_mono (S := S) hκ1 hle).2 hA) (CSet.one_mem _ _)) (vqY2_mem hΩ2)
  have hbase := vnRead_W hl hX hA hρ (X := Om (1 + 1 + 1)) (by rw [vnWe_Om3]; exact ugY_lt_Om3.le)
    vnWe_Om3.le
  rw [vnWe_Om3] at hbase
  have hR3 := h0 _ _ (vqBase_Om3Om3 l) zero_le hÂ hbase
  rw [add_zero, gxTh_zero, add_zero] at hR3
  -- the reading at β = 0, e = 1
  have hρSC : SC (upsilon l) := hρ ▸ SC_psi Low.InR_Om_one A
  have h1ρ : (1 : Ordinal.{0}) < upsilon l := gg_one_lt_of_SC hρSC
  have hB1 : RoBaseE S l (Om (1 + 1 + 1)) 1 0 := by
    have h13 : (1 : Ordinal.{0}) < Om (1 + 1 + 1) := gg_one_lt_of_SC (SC_Om h3)
    refine ⟨dvd_zero _, CSet.zero_mem _ _, ?_, fun d _ => CSet.zero_mem _ _, fun e' _ h' => ?_⟩
    · rw [zero_add]
      exact (leWe_lt_SC vkOmW.1 vkOmW.2 (vqOm3_add_lt h13)).1.trans_le (ConjT.OmW_le_A S _)
    · exact h'.trans_lt ((gg_one_lt_of_SC (SC_Om one_ne_zero)).trans (leOm1_lt_Te (S := S) _ _))
  have hR1 := h1 0 (A + 1) hB1 zero_le (Vx.vxHatA1 (S := S) hA) (ldBlk_zero hA hρ)
  rw [gxTh_small h1ρ.le] at hR1
  -- strict order of the two atoms
  have hlt : gxTh (upsilon l) (ldAtR S l) (leTe S (Om (1 + 1 + 1)) (Om (1 + 1 + 1))) <
      gxTh (upsilon l) (ldAtR S l) (leTe S (Om (1 + 1 + 1) + 1) 0) := by
    have hat : leTe S (Om (1 + 1 + 1)) (Om (1 + 1 + 1)) ∈ ldAtR S l := by
      unfold leTe
      rw [vnWe_Om3]
      exact ⟨_, CSet.add_mem (Ry.ryOm3_mem _ _) (Ry.ryOm3_mem _ _),
        vqOm3_lt_A l (vkOmW.1.isPrincipal Ry.ryOm3_lt Ry.ryOm3_lt), rfl⟩
    refine gxTh_lt (GxCl.atom hat) ?_
    unfold leTe
    rw [vnWe_Om3, zero_add]
    exact psi_lt_psi_of_mem (InR_Om_succ 1) skrxOm3_two_lt
      (CSet.add_mem (Ry.ryOm3_mem _ _) (Ry.ryOm3_mem _ _))
  rw [hR3, hR1] at hlt
  have hle2 : A + 1 + leOe (Xh 0 + 1) ≤ A + 1 + Y2 + leOe (Xh (Om (1 + 1 + 1))) := by
    rw [add_assoc (A + 1) Y2]
    exact (add_le_add_iff_left _).2 ((leOe_mono hXO1).trans le_add_self)
  exact absurd hlt (not_lt.2 (psi_mono (S := S) hκ1 hle2).1)

/-- Verbatim copy of the skeleton statement `TopDynAll` (node `skTopDyn`). -/
def SkRXTopDynAll (S : InaccSeq.{0}) : Prop :=
  ∀ (k : ℕ) (l ηx A : Ordinal.{0}), IsRestartIdx l → upsilon l < Nm.Pv S ηx →
    A ∈ S.CSet A (S.psi A (Om 1)) → S.psi A (Om 1) = upsilon l →
    ∃ Xh : Ordinal.{0} → Ordinal.{0}, ∀ e, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) →
      Vt.VtTopDyn S l 0 (Om ((k + 3 : ℕ) : Ordinal.{0})) Xh e

/-- **At every restart, `k = 0`: no `X̂` independent of `e` gives the dynamic tops at `Ω₃` for all codes `e < Ω₂`.** -/
theorem skrxTopDyn_k0 {l ηx A : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
    (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l) :
    ¬ ∃ Xh : Ordinal.{0} → Ordinal.{0}, ∀ e, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) →
      Vt.VtTopDyn S l 0 (Om (((0 : ℕ) + 3 : ℕ) : Ordinal.{0})) Xh e := by
  rintro ⟨Xh, hT⟩
  have e3 : ((((0 : ℕ) + 3 : ℕ)) : Ordinal.{0}) = 1 + 1 + 1 := by norm_num
  rw [e3] at hT
  have hρSC : SC (upsilon l) := hρ ▸ SC_psi Low.InR_Om_one A
  have h1ρ : (1 : Ordinal.{0}) < upsilon l := gg_one_lt_of_SC hρSC
  have h1W : (1 : Ordinal.{0}) < Om (1 + 1) := gg_one_lt_of_SC ldOm2_SC
  exact skrxDyn01 hl hX hA hρ (hT 0 (GxCl.small (zero_lt_one.trans h1ρ)) (zero_lt_one.trans h1W))
    (hT 1 (GxCl.small h1ρ) h1W)

/-- **`TopDynAll` (the skeleton node `skTopDyn`) is FALSE**: the restart of `m* = L(0)` with `η_x = Ω_ω + P′`
(`ρ = L(0) < L(1) = P(Ω_ω + P′)`) and its own `A` refute it at `k = 0`. -/
theorem skrxTopDynAll_false (S : InaccSeq.{0}) : ¬ SkRXTopDynAll S := by
  intro hT
  obtain ⟨l, hl, e⟩ := Cv.cvM_restart (S := S)
  have hX : upsilon l < Pv S (Om ω + Nc.ncPp S * 1) := by
    rw [← e, ← Lw.lw_L_eq]; exact Rl.rlM_lt_L1
  have hL1 : Nc.ncL S 1 = Bc.bcC S 0 := by simp [Bc.bcC]
  have hn : upsilon l < Bc.bcC S (0 + 1) := by
    rw [← e]
    exact (Rl.rlM_lt_L1 (S := S)).trans_le (hL1 ▸ Bc.bcC_mono (S := S) (Nat.zero_le _))
  obtain ⟨hA, hρ⟩ := vqA_spec hl hX (n := 0) hn
  exact skrxTopDyn_k0 hl hX hA hρ (hT 0 l _ _ hl hX hA hρ)


end Googology.Trans.PoR.InaccPsi.R2.SkRX
