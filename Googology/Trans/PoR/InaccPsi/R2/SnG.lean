import Googology.Trans.PoR.InaccPsi.R2.SnOw

/-!
# The base-indexed family of the shifts with exponents below `ε_{Ω₂+1}`

`Θ = gxTh ρ_λ (ldAtR λ)`, `Θ̂ = Sg.sgThH S λ`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `EE_j(X₀, β, E) = Rv.rvEE S X₀ β E j`,
`ε = ε_{Ω₂+1}`, `CL = Sn.SnCL` (the closure condition).

`SnG S λ β X X̂ E` (**the family over the base `β`**, `E` the last level): `X = W^{E₁}·ζ₁ + … + W^{E_k}·ζ_k`,
`X̂ = Ω^{Θ̂ E₁}·Θ ζ₁ + … + Ω^{Θ̂ E_k}·Θ ζ_k`, exponents `E₁ > … > E_k = E ≥ 1` in the hull, below `ε`, each with
the closure condition over the offset `X_{<i}` at `β`, and codes `ζ_i ≠ 0` with `ζ_i < EE_j(X_{<i}, β, E_i)` for some
`j`.  It contains `Rw.RwG` (codes `E < Ω₂` own via `Rw.rwEX` satisfy the closure condition, and `Θ̂ E = Θ E`).

* `snG_data` (`W^E ∣ X`, `X ≠ 0`, `X < ψ_{Ω₃}(0)`, `X̂ < ψ_{Ω₂}(0)`), `snG_mono` (**hereditary**);
* `snG_sh` (**every member is a shift own relative to `β` with the top law at the bases `≥ β`**, by `Sc.scFam`,
  `Sn.snOwP`, `Sn.snLev`), `snShG` (the family `∃ E, SnG β X X̂ E`), `snShG_sh`, `snShG_mono`.

No new axiom.  New definitions: `SnG`, `snShG`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Sn

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Sj

variable {S : InaccSeq.{0}}

/-- **The family of the shifts with exponents below `ε_{Ω₂+1}` over the base `β`** (last level `E`). -/
inductive SnG (S : InaccSeq.{0}) (l : Ordinal.{0}) : Ordinal.{0} → Ordinal.{0} → Ordinal.{0} → Ordinal.{0} → Prop
  | one {β E ζ : Ordinal.{0}} : 1 ≤ E → E ∈ cdHull S l → E < veblen 1 (Om (1 + 1) + 1) → SnCL S E β 0 →
      GxCl (upsilon l) (ldAtR S l) ζ → ζ ≠ 0 → (∃ j, ζ < rvEE S 0 β E j) →
      SnG S l β (leWe E * ζ) (leOe (sgThH S l E) * gxTh (upsilon l) (ldAtR S l) ζ) E
  | add {β X0 Xh0 E0 E ζ : Ordinal.{0}} : SnG S l β X0 Xh0 E0 → 1 ≤ E → E < E0 → E ∈ cdHull S l →
      E < veblen 1 (Om (1 + 1) + 1) → SnCL S E β X0 →
      GxCl (upsilon l) (ldAtR S l) ζ → ζ ≠ 0 → (∃ j, ζ < rvEE S X0 β E j) →
      SnG S l β (X0 + leWe E * ζ) (Xh0 + leOe (sgThH S l E) * gxTh (upsilon l) (ldAtR S l) ζ) E

/-- The family `∃ E, SnG β X X̂ E`. -/
def snShG (S : InaccSeq.{0}) (l b X Xh : Ordinal.{0}) : Prop := ∃ E, SnG S l b X Xh E

/-- `ε_{Ω₂+1} < ψ_{Ω₃}(0)`. -/
theorem snEps_lt_G3 : veblen 1 (Om (1 + 1) + 1) < S.psi 0 (Om (1 + 1 + 1)) := by
  have hG3 := rwG3_SC (S := S)
  have hWG3 := rwW_lt_G3 (S := S)
  have h1 : (1 : Ordinal.{0}) < S.psi 0 (Om (1 + 1 + 1)) := (gg_one_lt_of_SC ldOm2_SC).trans hWG3
  exact hG3.2 1 h1 _ (hG3.isPrincipal hWG3 h1)

/-- `W^{E+1} < ψ_{Ω₃}(0)` for `E < ε_{Ω₂+1}`. -/
theorem snWe_lt_G3 {E : Ordinal.{0}} (hE : E < veblen 1 (Om (1 + 1) + 1)) :
    leWe (E + 1) < S.psi 0 (Om (1 + 1 + 1)) := by
  have hG3 := rwG3_SC (S := S)
  have hWG3 := rwW_lt_G3 (S := S)
  have hE1 : E + 1 < S.psi 0 (Om (1 + 1 + 1)) := hG3.isSuccLimit.succ_lt (hE.trans snEps_lt_G3)
  exact (leWe_lt_SC hG3 hWG3 hE1).1

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- `Ω^{Θ̂ E + 1} < ψ_{Ω₂}(0)` for `E < ε_{Ω₂+1}` in the hull. -/
theorem snOe_lt_G {E : Ordinal.{0}} (hEH : E ∈ cdHull S l) (hE : E < veblen 1 (Om (1 + 1) + 1)) :
    leOe (sgThH S l E + 1) < S.psi 0 (Om (1 + 1)) := by
  have hG1 := rwG_SC (S := S)
  have hΩG1 := rwO_lt_G (S := S)
  exact (leOe_lt_SC hG1 hΩG1 (hG1.isSuccLimit.succ_lt (snThH_lt_G hl hX E hEH hE))).1

/-- **The data of a member.** -/
theorem snG_data {β X Xh E : Ordinal.{0}} (h : SnG S l β X Xh E) :
    1 ≤ E ∧ E ∈ cdHull S l ∧ E < veblen 1 (Om (1 + 1) + 1) ∧
      leWe E ∣ X ∧ X ≠ 0 ∧ X < S.psi 0 (Om (1 + 1 + 1)) ∧ Xh < S.psi 0 (Om (1 + 1)) := by
  have hG3 := rwG3_SC (S := S)
  have hG1 := rwG_SC (S := S)
  have hΩG1 := rwO_lt_G (S := S)
  have hterm : ∀ {E' X0 ζ : Ordinal.{0}}, E' ∈ cdHull S l → E' < veblen 1 (Om (1 + 1) + 1) →
      GxCl (upsilon l) (ldAtR S l) ζ → (∃ j, ζ < rvEE S X0 β E' j) →
      leWe E' * ζ < S.psi 0 (Om (1 + 1 + 1)) ∧
        leOe (sgThH S l E') * gxTh (upsilon l) (ldAtR S l) ζ < S.psi 0 (Om (1 + 1)) := by
    intro E' X0 ζ hEH hE _ hj
    obtain ⟨j, hj⟩ := hj
    have hζW : ζ < Om (1 + 1) := hj.trans (rvEE_lt_Om2 j)
    have hΘζ := snTh_lt_Om1 hl hX hζW.le
    refine ⟨(rvWe_lt_succ hζW).trans (snWe_lt_G3 hE), ?_⟩
    exact (rvOe_lt_succ hΘζ).trans (snOe_lt_G hl hX hEH hE)
  induction h with
  | @one E ζ h1 hEH hE _ hζ hζ0 hj =>
    obtain ⟨t1, t2⟩ := hterm hEH hE hζ hj
    exact ⟨h1, hEH, hE, dvd_mul_right _ _, mul_ne_zero (leWe_pos E).ne' hζ0, t1, t2⟩
  | @add X0 Xh0 E0 E ζ _ h1 hEE hEH hE _ hζ hζ0 hj ih =>
    obtain ⟨-, -, -, hd0, -, hX0, hXh0⟩ := ih
    obtain ⟨t1, t2⟩ := hterm hEH hE hζ hj
    refine ⟨h1, hEH, hE, dvd_add ((leWe_dvd hEE.le).trans hd0) (dvd_mul_right _ _), ?_,
      hG3.isPrincipal hX0 t1, hG1.isPrincipal hXh0 t2⟩
    intro h'
    have := le_antisymm (h' ▸ le_add_self : leWe E * ζ ≤ 0) zero_le
    exact mul_ne_zero (leWe_pos E).ne' hζ0 this

omit hl hX in
/-- **The family is hereditary.** -/
theorem snG_mono {β β' X Xh E : Ordinal.{0}} (hββ : β ≤ β') (h : SnG S l β X Xh E) : SnG S l β' X Xh E := by
  induction h with
  | @one E ζ h1 hEH hE hcl hζ hζ0 hj =>
    obtain ⟨j, hj⟩ := hj
    exact SnG.one h1 hEH hE (snCL_mono hcl hββ le_rfl) hζ hζ0 ⟨j, hj.trans_le (rvEE_mono_base hββ j)⟩
  | @add X0 Xh0 E0 E ζ _ h1 hEE hEH hE hcl hζ hζ0 hj ih =>
    obtain ⟨j, hj⟩ := hj
    exact SnG.add ih h1 hEE hEH hE (snCL_mono hcl hββ le_rfl) hζ hζ0
      ⟨j, hj.trans_le (rvEE_mono_base hββ j)⟩

omit hl hX in
theorem snShG_mono {b b' X Xh : Ordinal.{0}} (hbb : b ≤ b') (h : snShG S l b X Xh) : snShG S l b' X Xh := by
  obtain ⟨E, hE⟩ := h
  exact ⟨E, snG_mono hbb hE⟩

/-- **Every member is a shift own relative to `β` with the top law at the bases `≥ β`.** -/
theorem snG_sh {β X Xh E : Ordinal.{0}} (h : SnG S l β X Xh E) : RvSh S l β X Xh ∧ RvTop S l β X Xh 0 := by
  have hG3 := rwG3_SC (S := S)
  have hWG3 := rwW_lt_G3 (S := S)
  have hG1 := rwG_SC (S := S)
  have hΩG1 := rwO_lt_G (S := S)
  have hne := (snG_data hl hX h).2.2.2.2.1
  induction h with
  | @one E ζ h1 hEH hE hcl hζ hζ0 hj =>
    obtain ⟨j0, hj0⟩ := hj
    have hζW : ζ < Om (1 + 1) := hj0.trans (rvEE_lt_Om2 j0)
    have h := scFam hl hX (snOwP hl hX hEH h1 hE) (snLev hl hX hEH h1 hE) (X0 := 0) (Xh0 := 0) (β := β)
      (Or.inl ⟨rfl, rfl⟩) (dvd_zero _)
      (by rw [zero_add]; exact hG3.isPrincipal (snWe_lt_G3 hE) hWG3)
      (by rw [zero_add]; exact hG1.isPrincipal (snOe_lt_G hl hX hEH hE) hΩG1) hcl ζ hζ ⟨j0, hj0⟩
      (snTh_lt_Om1 hl hX hζW.le)
    rw [zero_add, zero_add] at h
    exact rvOff_ne h hne
  | @add X0 Xh0 E0 E ζ h0 h1 hEE hEH hE hcl hζ hζ0 hj ih =>
    obtain ⟨-, -, -, hd0, hne0, hX0, hXh0⟩ := snG_data hl hX h0
    obtain ⟨j0, hj0⟩ := hj
    have hζW : ζ < Om (1 + 1) := hj0.trans (rvEE_lt_Om2 j0)
    have h := scFam hl hX (snOwP hl hX hEH h1 hE) (snLev hl hX hEH h1 hE) (β := β)
      (Or.inr (ih hne0)) ((leWe_dvd (Order.add_one_le_of_lt hEE)).trans hd0)
      (hG3.isPrincipal (hG3.isPrincipal hX0 (snWe_lt_G3 hE)) hWG3)
      (hG1.isPrincipal (hG1.isPrincipal hXh0 (snOe_lt_G hl hX hEH hE)) hΩG1) hcl ζ hζ ⟨j0, hj0⟩
      (snTh_lt_Om1 hl hX hζW.le)
    exact rvOff_ne h hne

/-- **The family `snShG` meets the hypotheses of the own-atom layer** (`hSh` of `Rw.rwOwnRead`, `Rw.rwDigMove`). -/
theorem snShG_sh : ∀ b X Xh, snShG S l b X Xh → RvSh S l b X Xh ∧
    ∀ e, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) → RvTop S l b X Xh e := by
  rintro b X Xh ⟨E, hE⟩
  obtain ⟨hs, ht⟩ := snG_sh hl hX hE
  exact ⟨hs, rvTopE hs hl hX ht⟩

end Main

end Googology.Trans.PoR.InaccPsi.R2.Sn
