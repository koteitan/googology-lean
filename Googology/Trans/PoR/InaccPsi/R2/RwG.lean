import Googology.Trans.PoR.InaccPsi.R2.RwLC2

/-!
# The base-indexed family of the shifts with code exponents, and its top law

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `EE_j(X₀, β, E) = Rv.rvEE S X₀ β E j`,
`EX_j(X₀, β) = Rw.rwEX S X₀ β j`.

`RwG S λ β X X̂ E` (**the family over the base `β`**, `E` the last level): `X = W^{E₁}·ζ₁ + … + W^{E_k}·ζ_k`,
`X̂ = Ω^{Θ E₁}·Θ ζ₁ + … + Ω^{Θ E_k}·Θ ζ_k`, codes `E₁ > … > E_k = E ≥ 1` with `Θ E_i < Ω₁`, each `E_i` own over the
offset `X_{<i}` (`E_i < EX_j(X_{<i}, β)` for some `j`), and codes `ζ_i ≠ 0` with `Θ ζ_i < Ω₁`,
`ζ_i < EE_j(X_{<i}, β, E_i)` for some `j`.  It contains `Rw.RwF` (the levels below `ρ_λ`, `Θ f = f`).

* `rwG_data` (`W^E ∣ X`, `X ≠ 0`, `X < ψ_{Ω₃}(0)`, `X̂ < ψ_{Ω₂}(0)`, `E < Ω₂`), `rwG_mono` (**hereditary**);
* `rwG_sh` (**every member is a shift own relative to `β` with the top law at the bases `≥ β`**, by
  `Rw.rwFamC` and `Rw.rwLevC_all`), `rwShG` (the family `∃ E, RwG β X X̂ E`), `rwShG_sh`, `rwShG_mono`.

No new axiom.  New definitions: `RwG`, `rwShG`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Rw

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv

variable {S : InaccSeq.{0}}

/-- **The family of the shifts with code exponents over the base `β`** (last level `E`). -/
inductive RwG (S : InaccSeq.{0}) (l : Ordinal.{0}) : Ordinal.{0} → Ordinal.{0} → Ordinal.{0} → Ordinal.{0} → Prop
  | one {β E ζ : Ordinal.{0}} : 1 ≤ E → GxCl (upsilon l) (ldAtR S l) E →
      gxTh (upsilon l) (ldAtR S l) E < Om 1 → (∃ j, E < rwEX S 0 β j) →
      GxCl (upsilon l) (ldAtR S l) ζ → ζ ≠ 0 →
      gxTh (upsilon l) (ldAtR S l) ζ < Om 1 → (∃ j, ζ < rvEE S 0 β E j) →
      RwG S l β (leWe E * ζ) (leOe (gxTh (upsilon l) (ldAtR S l) E) * gxTh (upsilon l) (ldAtR S l) ζ) E
  | add {β X0 Xh0 E0 E ζ : Ordinal.{0}} : RwG S l β X0 Xh0 E0 → 1 ≤ E → E < E0 →
      GxCl (upsilon l) (ldAtR S l) E → gxTh (upsilon l) (ldAtR S l) E < Om 1 → (∃ j, E < rwEX S X0 β j) →
      GxCl (upsilon l) (ldAtR S l) ζ → ζ ≠ 0 → gxTh (upsilon l) (ldAtR S l) ζ < Om 1 →
      (∃ j, ζ < rvEE S X0 β E j) →
      RwG S l β (X0 + leWe E * ζ)
        (Xh0 + leOe (gxTh (upsilon l) (ldAtR S l) E) * gxTh (upsilon l) (ldAtR S l) ζ) E

/-- The family `∃ E, RwG β X X̂ E`. -/
def rwShG (S : InaccSeq.{0}) (l b X Xh : Ordinal.{0}) : Prop := ∃ E, RwG S l b X Xh E

/-- `W^E·ζ < ψ_{Ω₃}(0)`, `W^{E+1} < ψ_{Ω₃}(0)`, `Ω^y·z < ψ_{Ω₂}(0)`, `Ω^{y+1} < ψ_{Ω₂}(0)` for `E, ζ < Ω₂` and
countable `y`, `z`. -/
theorem rwTermC_lt {E ζ y z : Ordinal.{0}} (hE : E < Om (1 + 1)) (hζ : ζ < Om (1 + 1)) (hy : y < Om 1)
    (hz : z < Om 1) :
    leWe E * ζ < S.psi 0 (Om (1 + 1 + 1)) ∧ leWe (E + 1) < S.psi 0 (Om (1 + 1 + 1)) ∧
      leOe y * z < S.psi 0 (Om (1 + 1)) ∧ leOe (y + 1) < S.psi 0 (Om (1 + 1)) := by
  have hG3 := rwG3_SC (S := S)
  have hWG3 := rwW_lt_G3 (S := S)
  have hG1 := rwG_SC (S := S)
  have hΩG1 := rwO_lt_G (S := S)
  have hE1 : E + 1 < Om (1 + 1) := ldOm2_SC.isSuccLimit.succ_lt hE
  have hy1 : y + 1 < Om 1 := Ph.ph_SC_Om1.isSuccLimit.succ_lt hy
  refine ⟨ldMul_lt_SC hG3 (leWe_lt_SC hG3 hWG3 (hE.trans hWG3)).1 (hζ.trans hWG3),
    (leWe_lt_SC hG3 hWG3 (hE1.trans hWG3)).1,
    ldMul_lt_SC hG1 (leOe_lt_SC hG1 hΩG1 (hy.trans hΩG1)).1 (hz.trans hΩG1),
    (leOe_lt_SC hG1 hΩG1 (hy1.trans hΩG1)).1⟩

/-- **The data of a member.** -/
theorem rwG_data {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
    {β X Xh E : Ordinal.{0}} (h : RwG S l β X Xh E) :
    1 ≤ E ∧ GxCl (upsilon l) (ldAtR S l) E ∧ gxTh (upsilon l) (ldAtR S l) E < Om 1 ∧ E < Om (1 + 1) ∧
      leWe E ∣ X ∧ X ≠ 0 ∧ X < S.psi 0 (Om (1 + 1 + 1)) ∧ Xh < S.psi 0 (Om (1 + 1)) := by
  obtain ⟨-, hρ1⟩ := leRho hl hX
  have hG3 := rwG3_SC (S := S)
  have hG1 := rwG_SC (S := S)
  induction h with
  | @one E ζ h1 hE hΘE hEX hζ hζ0 hΘ hj =>
    obtain ⟨j', hj'⟩ := hEX
    obtain ⟨j, hj⟩ := hj
    have hEW : E < Om (1 + 1) := hj'.trans (rwEX_lt_Om2 j')
    obtain ⟨t1, -, t3, -⟩ := rwTermC_lt (S := S) hEW (hj.trans (rvEE_lt_Om2 j)) hΘE hΘ
    exact ⟨h1, hE, hΘE, hEW, dvd_mul_right _ _, mul_ne_zero (leWe_pos E).ne' hζ0, t1, t3⟩
  | @add X0 Xh0 E0 E ζ h0 h1 hEE hE hΘE hEX hζ hζ0 hΘ hj ih =>
    obtain ⟨-, -, -, hE0W, hd0, -, hX0, hXh0⟩ := ih
    obtain ⟨j, hj⟩ := hj
    have hEW : E < Om (1 + 1) := hEE.trans hE0W
    obtain ⟨t1, -, t3, -⟩ := rwTermC_lt (S := S) hEW (hj.trans (rvEE_lt_Om2 j)) hΘE hΘ
    refine ⟨h1, hE, hΘE, hEW, dvd_add ((leWe_dvd hEE.le).trans hd0) (dvd_mul_right _ _), ?_,
      hG3.isPrincipal hX0 t1, hG1.isPrincipal hXh0 t3⟩
    intro h
    have := le_antisymm (h ▸ le_add_self : leWe E * ζ ≤ 0) zero_le
    exact mul_ne_zero (leWe_pos E).ne' hζ0 this

/-- **The family is hereditary.** -/
theorem rwG_mono {l β β' X Xh E : Ordinal.{0}} (hββ : β ≤ β') (h : RwG S l β X Xh E) : RwG S l β' X Xh E := by
  induction h with
  | @one E ζ h1 hE hΘE hEX hζ hζ0 hΘ hj =>
    obtain ⟨j', hj'⟩ := hEX
    obtain ⟨j, hj⟩ := hj
    exact RwG.one h1 hE hΘE ⟨j', hj'.trans_le (rwEX_mono_base hββ j')⟩ hζ hζ0 hΘ
      ⟨j, hj.trans_le (rvEE_mono_base hββ j)⟩
  | @add X0 Xh0 E0 E ζ h0 h1 hEE hE hΘE hEX hζ hζ0 hΘ hj ih =>
    obtain ⟨j', hj'⟩ := hEX
    obtain ⟨j, hj⟩ := hj
    exact RwG.add ih h1 hEE hE hΘE ⟨j', hj'.trans_le (rwEX_mono_base hββ j')⟩ hζ hζ0 hΘ
      ⟨j, hj.trans_le (rvEE_mono_base hββ j)⟩

theorem rwShG_mono {l b b' X Xh : Ordinal.{0}} (hbb : b ≤ b') (h : rwShG S l b X Xh) : rwShG S l b' X Xh := by
  obtain ⟨E, hE⟩ := h
  exact ⟨E, rwG_mono hbb hE⟩

section Sh

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **Every member is a shift own relative to `β` with the top law at the bases `≥ β`.** -/
theorem rwG_sh {β X Xh E : Ordinal.{0}} (h : RwG S l β X Xh E) : RvSh S l β X Xh ∧ RvTop S l β X Xh 0 := by
  have hG3 := rwG3_SC (S := S)
  have hWG3 := rwW_lt_G3 (S := S)
  have hG1 := rwG_SC (S := S)
  have hΩG1 := rwO_lt_G (S := S)
  induction h with
  | @one E ζ h1 hE hΘE hEX hζ hζ0 hΘ hj =>
    obtain ⟨j', hj'⟩ := hEX
    have hEW : E < Om (1 + 1) := hj'.trans (rwEX_lt_Om2 j')
    obtain ⟨-, t2, -, t4⟩ := rwTermC_lt (S := S) hEW gg_Om1_lt_Om2 hΘE hΘE
    have h := rwFamC hl hX h1 hE hEW (rwLevC_all hl hX E hE h1 hEW) (Or.inl ⟨rfl, rfl⟩) (dvd_zero _)
      (by rw [zero_add]; exact hG3.isPrincipal t2 hWG3) (by rw [zero_add]; exact hG1.isPrincipal t4 hΩG1)
      ⟨j', hj'⟩ ζ hζ hj hΘ
    rw [zero_add, zero_add] at h
    exact rvOff_ne h (mul_ne_zero (leWe_pos E).ne' hζ0)
  | @add X0 Xh0 E0 E ζ h0 h1 hEE hE hΘE hEX hζ hζ0 hΘ hj ih =>
    obtain ⟨-, -, -, hE0W, hd0, -, hX0, hXh0⟩ := rwG_data hl hX h0
    have hEW : E < Om (1 + 1) := hEE.trans hE0W
    obtain ⟨-, t2, -, t4⟩ := rwTermC_lt (S := S) hEW gg_Om1_lt_Om2 hΘE hΘE
    have h := rwFamC hl hX h1 hE hEW (rwLevC_all hl hX E hE h1 hEW) (Or.inr ih)
      ((leWe_dvd (Order.add_one_le_of_lt hEE)).trans hd0)
      (hG3.isPrincipal (hG3.isPrincipal hX0 t2) hWG3) (hG1.isPrincipal (hG1.isPrincipal hXh0 t4) hΩG1)
      hEX ζ hζ hj hΘ
    refine rvOff_ne h ?_
    intro h'
    have := le_antisymm (h' ▸ le_add_self : leWe E * ζ ≤ 0) zero_le
    exact mul_ne_zero (leWe_pos E).ne' hζ0 this

/-- **The family `rwShG` meets the hypotheses of the own-atom layer.** -/
theorem rwShG_sh : ∀ b X Xh, rwShG S l b X Xh → RvSh S l b X Xh ∧
    ∀ e, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) → RvTop S l b X Xh e := by
  rintro b X Xh ⟨E, hE⟩
  obtain ⟨hs, ht⟩ := rwG_sh hl hX hE
  exact ⟨hs, rvTopE hs hl hX ht⟩

end Sh

end Googology.Trans.PoR.InaccPsi.R2.Rw
