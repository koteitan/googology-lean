import Googology.Trans.PoR.InaccPsi.R2.YtUx

/-!
# REFUTE-FIRST points of the leaf: `(a)` at `γ = ω`, `γ = ω + 1`, `(b)` at `δ = Ω₂²`, over `t = W^{Ω₃}` (`β = 0`, `k = 0`)

At every restart `λ` with `ρ_λ < P(η)` and every own `A` with `ψ₁(A) = ρ_λ`, `t = 0 + W^{Ω₃+0}`, `Â = A + 1 + ψ₂(T t)`:

* `ytTestBase` (`t` is own, `Ω₂²`- and `G₃`-divisible, in `H_λ`, and `Θ(ψ₂ t) = ψ₁(Â)` with `Â` own);
* `ytTestOm` (**`Θ(ψ₂(t + Ω₂·ω)) = ψ₁(Â + Ω₁·ω)`, `Θ(ψ₂(t + Ω₂·(ω+1))) = ψ₁(Â + Ω₁·(ω+1))`**, by `Yt.ytLaw`);
* `ytTestSq` (**`Θ(ψ₂(t + W^2·1 + 0)) = ψ₁(Â + Ω^2·1 + 0)`**, i.e. `Θ(ψ₂(t + Ω₂²)) = ψ₁(Â + Ω₁²)`, by `Le.leOwnRead`
  at the base `t`, `Yt.ytBaseE`).

So none of the three points is refuted: the laws hold there.  No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yt

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Vk Googology.Trans.PoR.InaccPsi.R2.Vb

variable {S : InaccSeq.{0}}

section T

variable {l ηx A : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)

include hl hX hA hρ

/-- The base data at `t = W^{Ω₃}`. -/
theorem ytTestBase :
    (∀ d, d ≤ Om (1 + 1) → (0 : Ordinal.{0}) + leWe (Om (((0 : ℕ) : Ordinal.{0}) + 1 + 1 + 1) + 0) ∈
      S.CSet (0 + leWe (Om (((0 : ℕ) : Ordinal.{0}) + 1 + 1 + 1) + 0) + d)
        (S.psi (0 + leWe (Om (((0 : ℕ) : Ordinal.{0}) + 1 + 1 + 1) + 0) + d) (Om (1 + 1)))) ∧
    Om (1 + 1) * Om (1 + 1) ∣ (0 : Ordinal.{0}) + leWe (Om (((0 : ℕ) : Ordinal.{0}) + 1 + 1 + 1) + 0) ∧
    S.psi 0 (Om (1 + 1 + 1)) ∣ (0 : Ordinal.{0}) + leWe (Om (((0 : ℕ) : Ordinal.{0}) + 1 + 1 + 1) + 0) ∧
    VbD S l ((0 : Ordinal.{0}) + leWe (Om (((0 : ℕ) : Ordinal.{0}) + 1 + 1 + 1) + 0)) ∧
    A + 1 + S.psi (vbT S l (0 + leWe (Om (((0 : ℕ) : Ordinal.{0}) + 1 + 1 + 1) + 0))) (Om (1 + 1)) ∈
      S.CSet (A + 1 + S.psi (vbT S l (0 + leWe (Om (((0 : ℕ) : Ordinal.{0}) + 1 + 1 + 1) + 0))) (Om (1 + 1)))
        (S.psi (A + 1 + S.psi (vbT S l (0 + leWe (Om (((0 : ℕ) : Ordinal.{0}) + 1 + 1 + 1) + 0))) (Om (1 + 1)))
          (Om 1)) ∧
    gxTh (upsilon l) (ldAtR S l) (S.psi (0 + leWe (Om (((0 : ℕ) : Ordinal.{0}) + 1 + 1 + 1) + 0)) (Om (1 + 1))) =
      S.psi (A + 1 + S.psi (vbT S l (0 + leWe (Om (((0 : ℕ) : Ordinal.{0}) + 1 + 1 + 1) + 0))) (Om (1 + 1)))
        (Om 1) := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hB0 : Ro.RoBaseE S l (Om (((0 : ℕ) : Ordinal.{0}) + 1 + 1 + 1)) 0 0 := Xm.xmRB0 0 l (Om_pos one_ne_zero)
  obtain ⟨htD, -, htown⟩ := Xq.xqTopD hl hX 0 (GxCl.zero hρSC.1) ldOm2_SC.1 (Xi.xiD_zero l) hB0
  have htn : (0 : Ordinal.{0}) + leWe (Om (((0 : ℕ) : Ordinal.{0}) + 1 + 1 + 1) + 0) ∈
      S.CSet (0 + leWe (Om (((0 : ℕ) : Ordinal.{0}) + 1 + 1 + 1) + 0))
        (S.psi (0 + leWe (Om (((0 : ℕ) : Ordinal.{0}) + 1 + 1 + 1) + 0)) (Om (1 + 1))) := by
    have h := htown 0 zero_le; rwa [add_zero] at h
  have hlaw := Xi.xiTopUp0 hl hX hA hρ 0 (Xi.xiD_zero l) hB0
  unfold leTe at hlaw
  refine ⟨htown, ?_, ?_, htD, Xq.xqOwn hl hX hA hρ htD htn, hlaw⟩
  · rw [zero_add]; exact ytDvdWe (ytTwo_le_X 0 0)
  · rw [zero_add]; exact ytG3_dvd_We 0 0

/-- **REFUTE-FIRST `(a)` at `γ = ω` and `γ = ω + 1`**: the base-`t` law holds. -/
theorem ytTestOm :
    gxTh (upsilon l) (ldAtR S l)
        (S.psi (0 + leWe (Om (((0 : ℕ) : Ordinal.{0}) + 1 + 1 + 1) + 0) + Om (1 + 1) * ω) (Om (1 + 1))) =
      S.psi (A + 1 + S.psi (vbT S l (0 + leWe (Om (((0 : ℕ) : Ordinal.{0}) + 1 + 1 + 1) + 0))) (Om (1 + 1)) +
        Om 1 * ω) (Om 1) ∧
    gxTh (upsilon l) (ldAtR S l)
        (S.psi (0 + leWe (Om (((0 : ℕ) : Ordinal.{0}) + 1 + 1 + 1) + 0) + Om (1 + 1) * (ω + 1)) (Om (1 + 1))) =
      S.psi (A + 1 + S.psi (vbT S l (0 + leWe (Om (((0 : ℕ) : Ordinal.{0}) + 1 + 1 + 1) + 0))) (Om (1 + 1)) +
        Om 1 * (ω + 1)) (Om 1) := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  obtain ⟨hown, hdvd, -, htD, hÂ, hlaw⟩ := ytTestBase hl hX hA hρ
  have haA := (vkOmW.1.isPrincipal htD.2.2 ldOm2sq_lt_OmW).trans_le (ConjT.OmW_le_A S (cdEta S l))
  have hω : ω < upsilon l := Lw.lw_omega_lt_SC hρSC
  have hω1 : ω + 1 < upsilon l := hρSC.isSuccLimit.succ_lt hω
  have hG : ∀ {x : Ordinal.{0}}, x < upsilon l → x < ytG S (0 + leWe (Om (((0 : ℕ) : Ordinal.{0}) + 1 + 1 + 1) + 0)) :=
    fun hx => ((hx.trans ((cdEta_pv (S := S) hl.1 hX) ▸ psi_lt Low.InR_Om_one _)).trans (ytOm1_lt_G _))
  have h1 := ytLaw hl hX hown hdvd htD.1 haA hÂ hlaw ω (GxCl.small hω) (hG hω)
  have h2 := ytLaw hl hX hown hdvd htD.1 haA hÂ hlaw (ω + 1) (GxCl.small hω1) (hG hω1)
  rw [gxTh_small hω.le] at h1
  rw [gxTh_small hω1.le] at h2
  exact ⟨h1, h2⟩

/-- **REFUTE-FIRST `(b)` at `δ = Ω₂² = W^2`**: `Θ(ψ₂(t + W^2·1 + 0)) = ψ₁(Â + Ω^{Θ 2}·Θ 1 + 0)`. -/
theorem ytTestSq :
    gxTh (upsilon l) (ldAtR S l)
        (S.psi (0 + leWe (Om (((0 : ℕ) : Ordinal.{0}) + 1 + 1 + 1) + 0) + (leWe (1 + 1) * 1 + 0)) (Om (1 + 1))) =
      S.psi (A + 1 + S.psi (vbT S l (0 + leWe (Om (((0 : ℕ) : Ordinal.{0}) + 1 + 1 + 1) + 0))) (Om (1 + 1)) +
        (leOe (1 + 1) * 1 + 0)) (Om 1) := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  obtain ⟨hown, -, hG3, htD, hÂ, hlaw⟩ := ytTestBase hl hX hA hρ
  set t := (0 : Ordinal.{0}) + leWe (Om (((0 : ℕ) : Ordinal.{0}) + 1 + 1 + 1) + 0) with htdef
  have haA : t + leWe (Om (1 + 1)) < ConjT.Aη S (cdEta S l) :=
    (vkOmW.1.isPrincipal htD.2.2 leWW_lt_OmW).trans_le (ConjT.OmW_le_A S _)
  have hρ1 : upsilon l < Om 1 := (cdEta_pv (S := S) hl.1 hX) ▸ psi_lt Low.InR_Om_one _
  have hsm : ∀ {x : Ordinal.{0}}, x < ω → x < upsilon l := fun hx => hx.trans (Lw.lw_omega_lt_SC hρSC)
  have h2ω : (1 + 1 : Ordinal.{0}) < ω := by
    have : (1 + 1 : Ordinal.{0}) = ((2 : ℕ) : Ordinal.{0}) := by norm_num
    rw [this]; exact natCast_lt_omega0 2
  have h3ω : (1 + 1 + 1 : Ordinal.{0}) < ω := by
    have : (1 + 1 + 1 : Ordinal.{0}) = ((3 : ℕ) : Ordinal.{0}) := by norm_num
    rw [this]; exact natCast_lt_omega0 3
  have hF : ∀ {x : Ordinal.{0}}, x < ω → x < ytFW S t := fun hx =>
    ((hsm hx).trans hρ1).trans (psiS_bounds (S := S) _ 1).1
  have hb3 := ytBaseE hown hG3 htD.1 haA (hF h3ω)
  have h1T : (1 : Ordinal.{0}) < leTe S (1 + 1 + 1) t :=
    (one_lt_omega0.trans (Lw.lw_omega_lt_SC Ph.ph_SC_Om1)).trans (leOm1_lt_Te _ _)
  have hownc : LeOwnH S l (1 + 1 + 1) t (leWe (1 + 1) * 1 + 0)
      (leOe (gxTh (upsilon l) (ldAtR S l) (1 + 1)) * gxTh (upsilon l) (ldAtR S l) 1 + 0) :=
    LeOwnH.succ (GxCl.small (hsm h2ω)) le_add_self (GxCl.small (hsm one_lt_omega0)) one_ne_zero h1T zero_le
      LeOwnH.zero
  obtain ⟨hth, -, -, -⟩ := leOwnRead hl hX hownc _ hb3 hÂ hlaw
  rw [gxTh_small (hsm h2ω).le, gxTh_small (hsm one_lt_omega0).le] at hth
  exact hth

end T

end Googology.Trans.PoR.InaccPsi.R2.Yt
