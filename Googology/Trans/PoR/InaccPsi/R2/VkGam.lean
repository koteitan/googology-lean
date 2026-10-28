import Googology.Trans.PoR.InaccPsi.R2.VkLim

/-!
# The ladder `X + Ω₂·n`, its limit `X + Ω₂·ω` and the reading at the base `0`, for every shift with no bound

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `(X, X̂)` a shift `Vk.VkSh` (no bound `Y₃`), `Ω_ω = Om ω`.

* `vkBase0` (**`β = 0` is a base of every shift `X < Ω_ω`**, `Uj.ujBase0` had `X < Y₃`), `vkSh_addW`, `vkShN`,
  `vkShW` (the shifts `X + Ω₂`, `X + Ω₂·n`, `X + Ω₂·ω`);
* `vkTopN`, `vkTopNE`, `vkTopW_om` (**the ladder and its limit**: `RvTop X 0 ⇒ RvTop (X + Ω₂·n) 0`, every code
  exponent on it, `RvTop (X + Ω₂·ω) 0`);
* `vkRead0` (**the reading at the base `0`**: `Θ_λ(ψ_{Ω₂}(W^X)) = ψ_{Ω₁}(A + 1 + Ω^{X̂})` for every shift `X < Ω_ω`
  with `RvTop X 0`).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Vk

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Ro Googology.Trans.PoR.InaccPsi.R2.Rq
  Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Ug Googology.Trans.PoR.InaccPsi.R2.Uj

variable {S : InaccSeq.{0}}

/-- `Ω₂ < Ω_ω` and `Ω_ω` is strongly critical. -/
theorem vkOmW : SC (Om (ω : Ordinal.{0})) ∧ Om (1 + 1 : Ordinal.{0}) < Om ω :=
  ⟨SC_Om omega0_ne_zero, (Om_lt_Om.2 (lt_add_one _)).trans Ry.ryOm3_lt⟩

/-- **`β = 0` is a base of every shift `X < Ω_ω`.** -/
theorem vkBase0 (l : Ordinal.{0}) {X : Ordinal.{0}} (hX : X < Om ω) : RoBaseE S l X 0 0 := by
  refine ⟨dvd_zero _, CSet.zero_mem _ _, ?_, fun d _ => CSet.zero_mem _ _, fun e' _ h' => ?_⟩
  · rw [zero_add, add_zero]
    exact (leWe_lt_SC vkOmW.1 vkOmW.2 hX).1.trans_le (ConjT.OmW_le_A S _)
  · obtain rfl : e' = 0 := le_antisymm h' zero_le
    exact (SC_psi (InR_Om_succ 1) _).1

/-- **The next shift**: `VkSh X X̂ ⇒ VkSh (X + Ω₂) (X̂ + Ω₁)`. -/
theorem vkSh_addW {l b X Xh : Ordinal.{0}} (hs : VkSh S l b X Xh) : VkSh S l b (X + Om (1 + 1)) (Xh + Om 1) := by
  have hle : S.psi (b + leWe X) (Om (1 + 1)) ≤ S.psi (b + leWe (X + Om (1 + 1))) (Om (1 + 1)) :=
    (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left b).2 (leWe_mono le_self_add))).1
  refine ⟨fun h => hs.ne (le_antisymm (h ▸ le_self_add) zero_le), dvd_add hs.dvd dvd_rfl,
    CSet.add_mem hs.hull (mxOm2_mem _ _),
    CSet.add_mem (CSet_mono le_self_add hle hs.mem) (mxOm2_mem _ _),
    CSet.add_mem (CSet_mono le_self_add (gxTh_mono hle) hs.memh) (CSet.Om_mem (CSet.one_mem _ _)),
    fun Q hQ hb => VkA.add (hs.cl Q hQ (hle.trans hb)) (VkA.om hQ.1 le_rfl),
    fun Q hQ hb => VkA.add (hs.clh Q hQ ((gxTh_mono hle).trans hb)) (VkA.om hQ.1 le_rfl)⟩

/-- The shifts `X + Ω₂·n`. -/
theorem vkShN {l b X Xh : Ordinal.{0}} (hs : VkSh S l b X Xh) :
    ∀ n : ℕ, VkSh S l b (X + Om (1 + 1) * (n : Ordinal.{0})) (Xh + Om 1 * (n : Ordinal.{0}))
  | 0 => by simpa only [Nat.cast_zero, mul_zero, add_zero] using hs
  | n + 1 => by
    have h := vkSh_addW (vkShN hs n)
    rw [Nat.cast_succ, mul_add_one, mul_add_one, ← add_assoc, ← add_assoc]; exact h

/-- **`X + Ω₂·ω` is a shift.** -/
theorem vkShW {l b X Xh : Ordinal.{0}} (hs : VkSh S l b X Xh) :
    VkSh S l b (X + Om (1 + 1) * ω) (Xh + Om 1 * ω) := by
  have h2 : (1 + 1 : Ordinal.{0}) ≠ 0 := by rw [one_add_one_eq_two]; exact two_ne_zero
  have hle : S.psi (b + leWe X) (Om (1 + 1)) ≤ S.psi (b + leWe (X + Om (1 + 1) * ω)) (Om (1 + 1)) :=
    (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left b).2 (leWe_mono le_self_add))).1
  have hΩC : ∀ a c, Om (1 : Ordinal.{0}) ∈ S.CSet a c := fun a c => CSet.Om_mem (CSet.one_mem a c)
  refine ⟨fun h => hs.ne (le_antisymm (h ▸ le_self_add) zero_le), dvd_add hs.dvd (dvd_mul_right _ _),
    CSet.add_mem hs.hull (rqMulK_mem ldOm2_SC (mxOm2_mem _ _) (ConjT.omega_mem S _ _)),
    CSet.add_mem (CSet_mono le_self_add hle hs.mem) (rqMulK_mem ldOm2_SC (mxOm2_mem _ _) (ConjT.omega_mem S _ _)),
    CSet.add_mem (CSet_mono le_self_add (gxTh_mono hle) hs.memh)
      (rqMulK_mem Ph.ph_SC_Om1 (hΩC _ _) (ConjT.omega_mem S _ _)),
    fun Q hQ hb => VkA.add (hs.cl Q hQ (hle.trans hb)) (vkA_mulK hQ h2 ω (VkA.small (Lw.lw_omega_lt_SC hQ))),
    fun Q hQ hb => VkA.add (hs.clh Q hQ ((gxTh_mono hle).trans hb))
      (vkA_mulK hQ one_ne_zero ω (VkA.small (Lw.lw_omega_lt_SC hQ)))⟩

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **The ladder over any shift**: `RvTop X 0 ⇒ RvTop (X + Ω₂·n) (X̂ + Ω₁·n) 0` for every `n`. -/
theorem vkTopN {b X Xh : Ordinal.{0}} (hs : VkSh S l b X Xh) (h0 : RvTop S l b X Xh 0) :
    ∀ n : ℕ, RvTop S l b (X + Om (1 + 1) * (n : Ordinal.{0})) (Xh + Om 1 * (n : Ordinal.{0})) 0
  | 0 => by simpa only [Nat.cast_zero, mul_zero, add_zero] using h0
  | n + 1 => by
    have hsn := vkShN hs n
    have h := vkTopW hsn hl hX (vkTopE hsn hl hX (vkTopN hs h0 n))
    rw [Nat.cast_succ, mul_add_one, mul_add_one, ← add_assoc, ← add_assoc]; exact h

/-- **Every code exponent on the ladder.** -/
theorem vkTopNE {b X Xh : Ordinal.{0}} (hs : VkSh S l b X Xh) (h0 : RvTop S l b X Xh 0) (n : ℕ) :
    ∀ e, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) →
      RvTop S l b (X + Om (1 + 1) * (n : Ordinal.{0})) (Xh + Om 1 * (n : Ordinal.{0})) e :=
  vkTopE (vkShN hs n) hl hX (vkTopN hl hX hs h0 n)

/-- **The limit of the ladder**: `RvTop X 0 ⇒ RvTop (X + Ω₂·ω) (X̂ + Ω₁·ω) 0`. -/
theorem vkTopW_om {b X Xh : Ordinal.{0}} (hs : VkSh S l b X Xh) (h0 : RvTop S l b X Xh 0) :
    RvTop S l b (X + Om (1 + 1) * ω) (Xh + Om 1 * ω) 0 := by
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  have hΩ0 : Om (1 : Ordinal.{0}) ≠ 0 := (Om_pos one_ne_zero).ne'
  have hnω : ∀ n : ℕ, ((n : ℕ) : Ordinal.{0}) < ω := fun n => natCast_lt_omega0 n
  refine vkTopLimSh hl hX (vkShW hs) (fun x _ hx => ?_) (fun z hz => ?_)
  · obtain ⟨n, -, hn⟩ := ujLt_omega hW0 hx
    refine ⟨_, _, (add_le_add_iff_left X).2 (mul_le_mul_right (hnω n).le _), hn,
      (add_lt_add_iff_left Xh).2 ((mul_lt_mul_iff_right₀ (Om_pos one_ne_zero)).2 (hnω n)),
      vkShN hs n, vkTopN hl hX hs h0 n⟩
  · obtain ⟨n, -, hn⟩ := ujLt_omega hΩ0 hz
    exact ⟨_, _, (add_lt_add_iff_left X).2 ((mul_lt_mul_iff_right₀ ldOm2_SC.1).2 (hnω n)), hn,
      vkShN hs n, vkTopN hl hX hs h0 n⟩

end Main

/-- **The reading at the base `0` of a restart**: `Θ_λ(ψ_{Ω₂}(W^X)) = ψ_{Ω₁}(A + 1 + Ω^{X̂})` for `X < Ω_ω`. -/
theorem vkRead0 {l X Xh A : Ordinal.{0}} (hT : RvTop S l 0 X Xh 0) (hXY : X < Om ω)
    (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l) :
    gxTh (upsilon l) (ldAtR S l) (S.psi (leWe X) (Om (1 + 1))) = S.psi (A + 1 + leOe Xh) (Om 1) := by
  have hÂ : A + 1 ∈ S.CSet (A + 1) (S.psi (A + 1) (Om 1)) :=
    CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hA) (CSet.one_mem _ _)
  have h := hT 0 (A + 1) (vkBase0 l hXY) le_rfl hÂ (ldBlk_zero hA hρ)
  rw [add_zero, gxTh_zero, add_zero] at h
  unfold leTe at h
  rwa [zero_add] at h

end Googology.Trans.PoR.InaccPsi.R2.Vk
