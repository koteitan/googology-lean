import Googology.Trans.PoR.InaccPsi.R2.ZdMove

/-!
# REFUTE-FIRST records and non-vacuity for the chain of shifts `X_ξ = Ω_{k+3} + Ω₂·ξ`

* `zdRB0` (`0` is a base of every countable exponent of every shift `X < Ω_ω`),
* `zdTestOm2p1` (**REFUTE-FIRST point `E = Ω₂ + 1`**, `k = 0`, `β = 0`, at the restart of `m* = L(0)` with its own `A`:
  `Θ(ψ₂(W^{Ω₃+Ω₂+1})) = ψ₁(A + 1 + ψ₂(Ω^{Ω₂+Ω₁+1}))`: the law HOLDS),
* `zdTestNV` (**NON-VACUITY of `Zd.zdChain`, `Zd.zdTopMove`**: at every restart, for every `k`, `ξ < ε₀` and every
  countable code `c`, `(c, 0)` is a top base of the shift `X_ξ` and the law holds there).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Vk
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Nm

variable {S : InaccSeq.{0}}

/-- `Ro.RoBaseE λ X c 0` for every shift `X < Ω_ω` and every countable `c`. -/
theorem zdRB0 {X : Ordinal.{0}} (hXW : X < Om ω) (l : Ordinal.{0}) {c : Ordinal.{0}} (hc : c < Om 1) :
    Ro.RoBaseE S l X c 0 := by
  have hgW : X + c < Om ω :=
    vkOmW.1.isPrincipal hXW (hc.trans ((Om_lt_Om.2 (lt_add_one 1)).trans vkOmW.2))
  refine ⟨dvd_zero _, CSet.zero_mem _ _, ?_, fun d _ => CSet.zero_mem _ _, fun e' _ h' => ?_⟩
  · rw [zero_add]
    exact (leWe_lt_SC vkOmW.1 vkOmW.2 hgW).1.trans_le (ConjT.OmW_le_A S _)
  · exact (h'.trans_lt hc).trans (psiS_bounds (S := S) _ 1).1

/-- **NON-VACUITY**: at every restart with its own `A`, every `k`, `ξ < ε₀` and every countable code `c < ρ_λ`,
`(c, 0)` is a top base of `X_ξ` and `Θ(ψ₂(W^{X_ξ+c})) = ψ₁(A + 1 + ψ₂(Ω^{K_ξ+c}))`. -/
theorem zdTestNV {l ηx A : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
    (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l) (k : ℕ) {ξ c : Ordinal.{0}}
    (hξ : ξ < ε₀) (hcρ : c < upsilon l) :
    Ro.RoBaseE S l (zdX k ξ) c 0 ∧
      gxTh (upsilon l) (ldAtR S l) (S.psi (leWe (zdX k ξ + c)) (Om (1 + 1))) =
        S.psi (A + 1 + S.psi (leOe (zdK k ξ + c)) (Om (1 + 1))) (Om 1) := by
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hs := zdSh_chain hl hX k hξ
  have hc1 : c < Om 1 := hcρ.trans hρ1
  have hc2 : c < Om (1 + 1) := hc1.trans (Om_lt_Om.2 (lt_add_one 1))
  have hcc : GxCl (upsilon l) (ldAtR S l) c := GxCl.small hcρ
  have hb := zdRB0 (S := S) hs.lt l hc1
  have h := zdChain hl hX hA hρ k ξ hξ c hcc hc2 0 (Xi.xiD_zero l) hb
  have hcH : c ∈ cdHull S l := (ldHull_iff hl hX hc2).2 hcc
  have hcθ : c < ConjT.th S := hc1.trans (psiS_bounds (S := S) (Om ω) 1).1
  obtain ⟨-, hT⟩ := zdT_top hl hX hs (Xi.xiD_zero l) hcH hc2 hcθ
  unfold ZdLaw leTe at h
  rw [hT, Vh.vhT_zero hl hX, zero_add, gxTh_small hcρ.le] at h
  rw [zero_add] at h
  exact ⟨hb, h⟩

/-- **REFUTE-FIRST point `E = Ω₂ + 1`** (`k = 0`, `β = 0`, the restart of `m* = L(0)` with its own `A`): the law holds,
`Θ(ψ₂(W^{Ω₃+Ω₂+1})) = ψ₁(A + 1 + ψ₂(Ω^{Ω₂+Ω₁+1}))`. -/
theorem zdTestOm2p1 (S : InaccSeq.{0}) :
    ∃ l ηx A : Ordinal.{0}, IsRestartIdx l ∧ upsilon l < Pv S ηx ∧ A ∈ S.CSet A (S.psi A (Om 1)) ∧
      S.psi A (Om 1) = upsilon l ∧
      gxTh (upsilon l) (ldAtR S l)
          (S.psi (leWe (Om (((0 : ℕ) : Ordinal.{0}) + 1 + 1 + 1) + Om (1 + 1) + 1)) (Om (1 + 1))) =
        S.psi (A + 1 + S.psi (leOe (Om (((0 : ℕ) : Ordinal.{0}) + 1 + 1) + Om 1 + 1)) (Om (1 + 1))) (Om 1) := by
  obtain ⟨l, hl, -, hX, hA, hρ⟩ := Xd.xdWit S
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have h1ρ : (1 : Ordinal.{0}) < upsilon l := gg_one_lt_of_SC hρSC
  have h1e : (1 : Ordinal.{0}) < ε₀ := one_lt_omega0.trans (omega0_lt_epsilon 0)
  obtain ⟨-, h⟩ := zdTestNV hl hX hA hρ 0 h1e h1ρ
  unfold zdX zdK at h
  rw [mul_one, mul_one] at h
  exact ⟨l, _, _, hl, hX, hA, hρ, h⟩

end Googology.Trans.PoR.InaccPsi.R2.Zd
