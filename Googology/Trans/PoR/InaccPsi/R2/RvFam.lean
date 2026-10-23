import Googology.Trans.PoR.InaccPsi.R2.RvLim

/-!
# The shifts `X = Ω₂·ξ` relative to a base `b`: one induction over the codes `1 ≤ ξ < T_{Ω₂·Ω₂}(b)`

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `T_E(β) = ψ_{Ω₂}(β + W^E)`.  The base `b` satisfies
`W^{Ω₂·Ω₂} ∣ b` and `b ∈ Cl(b + d, ψ_{Ω₂}(b + d))` for `d ≤ W^{Ω₂·Ω₂}` (as a base of the shift `Ω₂·Ω₂`).

* `rvSh_c` (**`(Ω₂·ξ, Ω₁·Θ ξ)` is a shift own relative to `b`** for every code `1 ≤ ξ < T_{Ω₂·Ω₂}(b)` with
  `Θ ξ < Ω₁`; such `ξ` need not be own over `0`: `Rq.rqW2_gt`);
* `rvTopC` (**`RvTop b (Ω₂·ξ) (Ω₁·Θ ξ) 0`** for these `ξ`, one induction on `ξ` as `Rq.rqTopC`).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Rv

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq

variable {S : InaccSeq.{0}}

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) {b : Ordinal.{0}}
  (hbown : ∀ d, d ≤ leWe (Om (1 + 1) * Om (1 + 1)) → b ∈ S.CSet (b + d) (S.psi (b + d) (Om (1 + 1))))
  (hbd : leWe (Om (1 + 1) * Om (1 + 1)) ∣ b)

include hl hX hbown hbd

/-- **The code shifts below `T_{Ω₂·Ω₂}(b)` are own relative to `b`.** -/
theorem rvSh_c {ξ : Ordinal.{0}} (hξ : GxCl (upsilon l) (ldAtR S l) ξ) (h1 : 1 ≤ ξ)
    (hj : ξ < leTe S (Om (1 + 1) * Om (1 + 1)) b) (hΘ1 : gxTh (upsilon l) (ldAtR S l) ξ < Om 1) :
    RvSh S l b (Om (1 + 1) * ξ) (Om 1 * gxTh (upsilon l) (ldAtR S l) ξ) := by
  have hG3 : SC (S.psi 0 (Om (1 + 1 + 1))) := SC_psi (InR_Om_succ (1 + 1)) 0
  have hWG3 : Om (1 + 1 : Ordinal.{0}) < S.psi 0 (Om (1 + 1 + 1)) := (psiS_bounds (S := S) 0 (1 + 1)).1
  have hG1 : SC (S.psi 0 (Om (1 + 1))) := SC_psi (InR_Om_succ 1) 0
  have hΩG1 : Om (1 : Ordinal.{0}) < S.psi 0 (Om (1 + 1)) := (psiS_bounds (S := S) 0 1).1
  have hξW : ξ < Om (1 + 1) := hj.trans (leTe_lt_Om2 _ _)
  have hown : ξ < S.psi (b + leWe (Om (1 + 1) * ξ)) (Om (1 + 1)) := rqW2_gt hbown hbd hj
  have hΘown := gxTh_lt (Z := upsilon l) (At := ldAtR S l) hξ hown
  have hΩC : ∀ a b, Om (1 : Ordinal.{0}) ∈ S.CSet a b := fun a b => CSet.Om_mem (CSet.one_mem a b)
  refine ⟨mul_ne_zero ldOm2_SC.1.ne' (Order.one_le_iff_ne_zero.1 h1), dvd_mul_right _ _,
    rqMulK_mem ldOm2_SC (mxOm2_mem _ _) ((ldHull_iff hl hX hξW).2 hξ),
    rqMulK_mem ldOm2_SC (mxOm2_mem _ _) (CSet.of_lt hown),
    rqMulK_mem Ph.ph_SC_Om1 (hΩC _ _) (CSet.of_lt hΘown), ?_, ?_,
    fun Q hQ hb => LeCl.mulK hQ ldOm2_SC ξ (LeCl.small (hown.trans_le hb)),
    fun Q hQ hb => LeCl.mulK hQ Ph.ph_SC_Om1 _ (LeCl.small (hΘown.trans_le hb))⟩
  · rw [← mul_add_one]
    exact ldMul_lt_SC hG3 hWG3 ((ldOm2_SC.isSuccLimit.succ_lt hξW).trans hWG3)
  · rw [← mul_add_one]
    exact ldMul_lt_SC hG1 hΩG1 ((Ph.ph_SC_Om1.isSuccLimit.succ_lt hΘ1).trans hΩG1)

/-- **`RvTop b (Ω₂·ξ) (Ω₁·Θ ξ) 0` for every code `1 ≤ ξ < T_{Ω₂·Ω₂}(b)` with `Θ ξ < Ω₁`** (one induction on `ξ`). -/
theorem rvTopC : ∀ ξ, GxCl (upsilon l) (ldAtR S l) ξ → 1 ≤ ξ → ξ < leTe S (Om (1 + 1) * Om (1 + 1)) b →
    gxTh (upsilon l) (ldAtR S l) ξ < Om 1 →
    RvTop S l b (Om (1 + 1) * ξ) (Om 1 * gxTh (upsilon l) (ldAtR S l) ξ) 0 := by
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  have hΩ0 : Om (1 : Ordinal.{0}) ≠ 0 := (Om_pos one_ne_zero).ne'
  intro ξ
  induction ξ using WellFoundedLT.induction with
  | ind ξ IH =>
  intro hξ h1 hj hΘ1
  have hξW : ξ < Om (1 + 1) := hj.trans (leTe_lt_Om2 _ _)
  rcases zero_or_succ_or_isSuccLimit ξ with h0 | ⟨ξ0, hξ0⟩ | hlim
  · subst h0; exact absurd h1 (by simp)
  · rw [succ_eq_add_one] at hξ0
    subst hξ0
    have hξ0c := rqCode_pred hl hX hξ hξW
    rw [rqTh_succ hl hX hξ0c]
    rcases eq_or_ne ξ0 0 with rfl | h00
    · have h := roTop_one (S := S) hl hX
      rw [Nat.cast_one] at h
      rw [zero_add, gxTh_zero, zero_add]
      exact rvTop_of_ro h
    · have hΘ0 : gxTh (upsilon l) (ldAtR S l) ξ0 < Om 1 := (gxTh_mono (lt_add_one ξ0).le).trans_lt hΘ1
      have hj0 : ξ0 < leTe S (Om (1 + 1) * Om (1 + 1)) b := (lt_add_one ξ0).trans hj
      have h10 : 1 ≤ ξ0 := Order.one_le_iff_ne_zero.2 h00
      have hs := rvSh_c hl hX hbown hbd hξ0c h10 hj0 hΘ0
      have h := rvTopW hs hl hX (rvTopE hs hl hX (IH ξ0 (lt_add_one ξ0) hξ0c h10 hj0 hΘ0))
      rwa [← mul_add_one, ← mul_add_one] at h
  · refine rvTopLimSh hl hX (rvSh_c hl hX hbown hbd hξ h1 hj hΘ1) (fun x hxH hx => ?_) (fun z hz => ?_)
    · have hq : x / Om (1 + 1) < ξ := (Ordinal.lt_mul_iff_div_lt hW0).1 hx
      have hq1 := hlim.succ_lt hq
      have hq1c := rqCode_succ hl hX ((ldHull_iff hl hX (hq.trans hξW)).1 (ldDivK_mem ldOm2_SC hxH))
        (hq1.trans hξW)
      have hΘq : gxTh (upsilon l) (ldAtR S l) (x / Om (1 + 1) + 1) < Om 1 := (gxTh_mono hq1.le).trans_lt hΘ1
      refine ⟨Om (1 + 1) * (x / Om (1 + 1) + 1), Om 1 * gxTh (upsilon l) (ldAtR S l) (x / Om (1 + 1) + 1),
        mul_le_mul_right hq1.le _, ?_, (mul_lt_mul_iff_right₀ (Om_pos one_ne_zero)).2 (gxTh_lt hq1c hq1),
        rvSh_c hl hX hbown hbd hq1c le_add_self (hq1.trans hj) hΘq,
        IH _ hq1 hq1c le_add_self (hq1.trans hj) hΘq⟩
      rw [mul_add_one]; exact Ordinal.lt_mul_div_add x hW0
    · have hq : z / Om 1 < gxTh (upsilon l) (ldAtR S l) ξ := (Ordinal.lt_mul_iff_div_lt hΩ0).1 hz
      obtain ⟨c, hc, hcξ, hcz⟩ := gxTh_onto hq
      have hc1 := hlim.succ_lt hcξ
      have hc1c := rqCode_succ hl hX hc (hc1.trans hξW)
      have hΘc : gxTh (upsilon l) (ldAtR S l) (c + 1) < Om 1 := (gxTh_mono hc1.le).trans_lt hΘ1
      refine ⟨Om (1 + 1) * (c + 1), Om 1 * gxTh (upsilon l) (ldAtR S l) (c + 1),
        (mul_lt_mul_iff_right₀ ldOm2_SC.1).2 hc1, ?_, rvSh_c hl hX hbown hbd hc1c le_add_self (hc1.trans hj) hΘc,
        IH _ hc1 hc1c le_add_self (hc1.trans hj) hΘc⟩
      rw [rqTh_succ hl hX hc, hcz, mul_add_one]; exact Ordinal.lt_mul_div_add z hΩ0

end Main

end Googology.Trans.PoR.InaccPsi.R2.Rv
