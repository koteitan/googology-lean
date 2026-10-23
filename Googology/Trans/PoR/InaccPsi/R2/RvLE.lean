import Googology.Trans.PoR.InaccPsi.R2.RvEE

/-!
# Ordinal levels `1 ≤ e < ρ_λ`: the statement `RvLevSE e` and the level-`e` family

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E` (`Le.leWe`), `Ω^x = Ω₁^x` (`Le.leOe`), `T_E(β) = ψ_{Ω₂}(β + W^E)`.

`RvLevSE S λ e`: for every base bound `b` and every offset `(X₀, X̂₀)` over `b` (`Rv.RvOff`) with `W^e ∣ X₀`,
`X₀ + W^e + Ω₂ < ψ_{Ω₃}(0)`, `X̂₀ + Ω^e + Ω₁ < ψ_{Ω₂}(0)`: `RvTop b (X₀ + W^e) (X̂₀ + Ω^e) 0`.

* `rvFamE` (**the level-`e` family**: under `RvLevSE e`, every code `ζ < T_{X₀ + W^{e+1}}(β)` with `Θ ζ < Ω₁` gives
  the offset `(X₀ + W^e·ζ, X̂₀ + Ω^e·Θ ζ)` over `β`), as `Rv.rvFam`.

No new axiom.  New definition: `RvLevSE`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Rv

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq

variable {S : InaccSeq.{0}}

/-- **The level-`e` statement**: the top law at `X₀ + W^e` over every offset. -/
def RvLevSE (S : InaccSeq.{0}) (l e : Ordinal.{0}) : Prop :=
  ∀ b X0 Xh0, RvOff S l b X0 Xh0 → leWe e ∣ X0 → X0 + leWe e + Om (1 + 1) < S.psi 0 (Om (1 + 1 + 1)) →
    Xh0 + leOe e + Om 1 < S.psi 0 (Om (1 + 1)) → RvTop S l b (X0 + leWe e) (Xh0 + leOe e) 0

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  {e : Ordinal.{0}} (he1 : 1 ≤ e) (heρ : e < upsilon l) (IH : RvLevSE S l e)

include hl hX he1 heρ IH

/-- **The level-`e` family over a base `β` of the shift `X₀ + W^{e+1}`.** -/
theorem rvFamE {X0 Xh0 β : Ordinal.{0}} (hoff : RvOff S l β X0 Xh0) (hd : leWe (e + 1) ∣ X0)
    (hG3 : X0 + leWe (e + 1) + Om (1 + 1) < S.psi 0 (Om (1 + 1 + 1)))
    (hG : Xh0 + leOe (e + 1) + Om 1 < S.psi 0 (Om (1 + 1)))
    (hβd : leWe (X0 + leWe (e + 1)) ∣ β)
    (hβown : ∀ d, d ≤ leWe (X0 + leWe (e + 1)) → β ∈ S.CSet (β + d) (S.psi (β + d) (Om (1 + 1)))) :
    ∀ ζ, GxCl (upsilon l) (ldAtR S l) ζ → ζ < leTe S (X0 + leWe (e + 1)) β →
      gxTh (upsilon l) (ldAtR S l) ζ < Om 1 →
      RvOff S l β (X0 + leWe e * ζ) (Xh0 + leOe e * gxTh (upsilon l) (ldAtR S l) ζ) := by
  obtain ⟨-, -, hX0m, -, hX0cl, -⟩ := rvOff_data hoff
  have heΩ : e < Om 1 := heρ.trans (leRho hl hX).2
  have hX0G3 : X0 + leWe (e + 1) < S.psi 0 (Om (1 + 1 + 1)) := le_self_add.trans_lt hG3
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  have hk0 : leWe e ≠ 0 := (leWe_pos e).ne'
  have hOk0 : leOe e ≠ 0 := (leOe_pos e).ne'
  have hdk : leWe e ∣ X0 := (leWe_dvd le_self_add).trans hd
  have hmem : ∀ ζ, GxCl (upsilon l) (ldAtR S l) ζ → ζ < leTe S (X0 + leWe (e + 1)) β →
      gxTh (upsilon l) (ldAtR S l) ζ < Om 1 → ζ ≠ 0 →
      RvSh S l β (X0 + leWe e * ζ) (Xh0 + leOe e * gxTh (upsilon l) (ldAtR S l) ζ) := fun ζ hζ hζT hΘ hζ0 =>
    rvSh_me hl hX he1 heρ hoff hζ (hζT.trans (leTe_lt_Om2 _ _)) (rvEE_gtT hβown hX0m heΩ hβd hX0cl hX0G3 hζT) hΘ
      (fun h => (mul_ne_zero hk0 hζ0) (le_antisymm (h ▸ le_add_self) zero_le)) hG3 hG
  intro ζ
  induction ζ using WellFoundedLT.induction with
  | ind ζ IHz =>
  intro hζ hζT hΘ1
  have hζW : ζ < Om (1 + 1) := hζT.trans (leTe_lt_Om2 _ _)
  rcases zero_or_succ_or_isSuccLimit ζ with h0 | ⟨ζ0, hζ0⟩ | hlim
  · subst h0; simpa only [mul_zero, add_zero, gxTh_zero] using hoff
  · rw [succ_eq_add_one] at hζ0
    subst hζ0
    have hζ0c := rqCode_pred hl hX hζ hζW
    have hΘ0 : gxTh (upsilon l) (ldAtR S l) ζ0 < Om 1 := (gxTh_mono (lt_add_one ζ0).le).trans_lt hΘ1
    have hT0 : ζ0 < leTe S (X0 + leWe (e + 1)) β := (lt_add_one ζ0).trans hζT
    have hoff0 := IHz ζ0 (lt_add_one ζ0) hζ0c hT0 hΘ0
    have hΘs := rqTh_succ hl hX hζ0c
    have hle1 : leWe e * ζ0 + leWe e ≤ leWe (e + 1) := by
      rw [← mul_add_one]; exact (rvWe_lt_succ hζW).le
    have hle2 : leOe e * gxTh (upsilon l) (ldAtR S l) ζ0 + leOe e ≤ leOe (e + 1) := by
      rw [← mul_add_one, ← hΘs]; exact (rvOe_lt_succ hΘ1).le
    have ht := IH β _ _ hoff0 (dvd_add hdk (dvd_mul_right _ _))
      (lt_of_le_of_lt (add_le_add_left (by rw [add_assoc]; exact (add_le_add_iff_left X0).2 hle1) _) hG3)
      (lt_of_le_of_lt (add_le_add_left (by rw [add_assoc]; exact (add_le_add_iff_left Xh0).2 hle2) _) hG)
    rw [add_assoc, add_assoc, ← mul_add_one, ← mul_add_one, ← hΘs] at ht
    exact Or.inr ⟨hmem _ hζ hζT hΘ1 (by simp), ht⟩
  · have hζ0 : ζ ≠ 0 := hlim.ne_bot
    have hs := hmem ζ hζ hζT hΘ1 hζ0
    have hΘpos : 0 < gxTh (upsilon l) (ldAtR S l) ζ := by
      have := gxTh_lt (Z := upsilon l) (At := ldAtR S l) (GxCl.zero (leRho hl hX).1.1) (pos_iff_ne_zero.2 hζ0)
      rwa [gxTh_zero] at this
    have hsub : ∀ c, GxCl (upsilon l) (ldAtR S l) c → c < ζ →
        RvSh S l β (X0 + leWe e * (c + 1)) (Xh0 + leOe e * gxTh (upsilon l) (ldAtR S l) (c + 1)) ∧
        RvTop S l β (X0 + leWe e * (c + 1)) (Xh0 + leOe e * gxTh (upsilon l) (ldAtR S l) (c + 1)) 0 ∧
        gxTh (upsilon l) (ldAtR S l) (c + 1) < gxTh (upsilon l) (ldAtR S l) ζ := by
      intro c hc hcζ
      have hc1 := hlim.succ_lt hcζ
      have hc1c := rqCode_succ hl hX hc (hc1.trans hζW)
      have hΘc : gxTh (upsilon l) (ldAtR S l) (c + 1) < Om 1 := (gxTh_mono hc1.le).trans_lt hΘ1
      have h := rvOff_ne (IHz _ hc1 hc1c (hc1.trans hζT) hΘc)
        (fun h => (mul_ne_zero hk0 (by simp)) (le_antisymm (h ▸ le_add_self) zero_le))
      exact ⟨h.1, h.2, gxTh_lt hc1c hc1⟩
    refine Or.inr ⟨hs, rvTopLimSh hl hX hs (fun x hxH hx => ?_) (fun z hz => ?_)⟩
    · rcases lt_or_ge x X0 with hxX | hxX
      · have hX00 : X0 ≠ 0 := (zero_le.trans_lt hxX).ne'
        obtain ⟨hs0, ht0⟩ := rvOff_ne hoff hX00
        refine ⟨X0, Xh0, le_self_add, hxX, lt_add_of_pos_right _ (mul_pos (leOe_pos e) hΘpos), hs0, ht0⟩
      · obtain ⟨r, rfl⟩ := exists_add_of_le hxX
        have hr : r < leWe e * ζ := (add_lt_add_iff_left X0).1 hx
        have hrW : r < leWe (e + 1) := hr.trans (rvWe_lt_succ hζW)
        have hrH : r ∈ cdHull S l := by
          have h1 := leModP_mem (S := S) (Om (1 + 1) * (e + 1)) hxH
          have hm : (X0 + r) % ω ^ (Om (1 + 1) * (e + 1)) = r := by
            obtain ⟨q, hq⟩ := hd
            change (X0 + r) % leWe (e + 1) = r
            rw [hq, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hrW]
          rwa [hm] at h1
        have hq : r / leWe e < ζ := (Ordinal.lt_mul_iff_div_lt hk0).1 hr
        have hqc := (ldHull_iff hl hX (hq.trans hζW)).1
          (leDivOp_mem (dvd_mul_right _ _) hrH (by rw [← mul_add_one]; exact hrW))
        obtain ⟨hs1, ht1, hΘlt⟩ := hsub _ hqc hq
        refine ⟨_, _, ?_, ?_, (add_lt_add_iff_left Xh0).2 ((mul_lt_mul_iff_right₀ (leOe_pos e)).2 hΘlt), hs1, ht1⟩
        · exact (add_le_add_iff_left X0).2 (mul_le_mul_right (Order.add_one_le_of_lt hq) _)
        · refine (add_lt_add_iff_left X0).2 ?_
          rw [mul_add_one]; exact Ordinal.lt_mul_div_add r hk0
    · rcases lt_or_ge z Xh0 with hzX | hzX
      · have hXh00 : Xh0 ≠ 0 := (zero_le.trans_lt hzX).ne'
        obtain ⟨hs0, ht0⟩ := rvOff_neh hoff hXh00
        exact ⟨X0, Xh0, lt_add_of_pos_right _ (mul_pos (leWe_pos e) (pos_iff_ne_zero.2 hζ0)), hzX, hs0, ht0⟩
      · obtain ⟨u, rfl⟩ := exists_add_of_le hzX
        have hu : u < leOe e * gxTh (upsilon l) (ldAtR S l) ζ := (add_lt_add_iff_left Xh0).1 hz
        have hq : u / leOe e < gxTh (upsilon l) (ldAtR S l) ζ := (Ordinal.lt_mul_iff_div_lt hOk0).1 hu
        obtain ⟨c, hc, hcζ, hcz⟩ := gxTh_onto hq
        obtain ⟨hs1, ht1, -⟩ := hsub c hc hcζ
        refine ⟨_, _, (add_lt_add_iff_left X0).2 ((mul_lt_mul_iff_right₀ (leWe_pos e)).2 (hlim.succ_lt hcζ)), ?_,
          hs1, ht1⟩
        refine (add_lt_add_iff_left Xh0).2 ?_
        rw [rqTh_succ hl hX hc, hcz, mul_add_one]; exact Ordinal.lt_mul_div_add u hOk0

end Main

end Googology.Trans.PoR.InaccPsi.R2.Rv
