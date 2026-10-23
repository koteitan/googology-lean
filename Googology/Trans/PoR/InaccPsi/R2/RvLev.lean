import Googology.Trans.PoR.InaccPsi.R2.RvEM

/-!
# The top law at the shifts `X₀ + Ω₂^k` for every `k ≥ 1`, by induction on `k`

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `W_k = Ω₂^k` (`Le.leW k`), `O_k = Ω₁^k` (`Le.leO k`),
`T_E(β) = ψ_{Ω₂}(β + W^E)`, `EM_j = rvEM S X₀ β k j`.

`RvLevS S λ k`: for every base bound `b` and every offset `(X₀, X̂₀)` over `b` (`Rv.RvOff`) with `W_k ∣ X₀`,
`X₀ + W_k + Ω₂ < ψ_{Ω₃}(0)`, `X̂₀ + O_k + Ω₁ < ψ_{Ω₂}(0)`: `RvTop b (X₀ + W_k) (X̂₀ + O_k) 0`.

* `rvOff_ne` (a nonzero offset is a relative shift with the top law);
* `rvLev_one` (`k = 1`: the pull-back `Rv.rvTopW`, or `Ro.roTop_one` at `X₀ = 0`);
* `rvFam` (**the level-`k` family**: under `RvLevS k`, every code `ζ < T_{X₀ + W_{k+1}}(β)` with `Θ ζ < Ω₁` gives the
  offset `(X₀ + W_k·ζ, X̂₀ + O_k·Θ ζ)` over `β`; one induction on `ζ`);
* `rvEM_code` (`EM_j` is a code with `Θ(EM_j) < Ω₁`);
* `rvLev_succ` (**`RvLevS k ⇒ RvLevS (k+1)`**: the top at `X₀ + W_{k+1}` from the family at `β`).

No new axiom.  New definition: `RvLevS`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Rv

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq

variable {S : InaccSeq.{0}}

/-- **The level-`k` statement**: the top law at `X₀ + W_k` over every offset. -/
def RvLevS (S : InaccSeq.{0}) (l : Ordinal.{0}) (k : ℕ) : Prop :=
  ∀ b X0 Xh0, RvOff S l b X0 Xh0 → leW k ∣ X0 → X0 + leW k + Om (1 + 1) < S.psi 0 (Om (1 + 1 + 1)) →
    Xh0 + leO k + Om 1 < S.psi 0 (Om (1 + 1)) → RvTop S l b (X0 + leW k) (Xh0 + leO k) 0

theorem rvOff_ne {l b X0 Xh0 : Ordinal.{0}} (h : RvOff S l b X0 Xh0) (hne : X0 ≠ 0) :
    RvSh S l b X0 Xh0 ∧ RvTop S l b X0 Xh0 0 := by
  rcases h with ⟨rfl, -⟩ | h
  · exact absurd rfl hne
  · exact h

theorem rvOff_neh {l b X0 Xh0 : Ordinal.{0}} (h : RvOff S l b X0 Xh0) (hne : Xh0 ≠ 0) :
    RvSh S l b X0 Xh0 ∧ RvTop S l b X0 Xh0 0 := by
  rcases h with ⟨-, rfl⟩ | h
  · exact absurd rfl hne
  · exact h

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **Level `1`**: the pull-back. -/
theorem rvLev_one : RvLevS S l 1 := by
  intro b X0 Xh0 hoff _ _ _
  rw [leW_one, leO_one]
  rcases hoff with ⟨rfl, rfl⟩ | ⟨hs, ht⟩
  · have h := roTop_one (S := S) hl hX
    rw [Nat.cast_one, mul_one, mul_one] at h
    rw [zero_add, zero_add]; exact rvTop_of_ro h
  · exact rvTopW hs hl hX (rvTopE hs hl hX ht)

variable {k : ℕ} (hk : 1 ≤ k) (IH : RvLevS S l k)

include hk IH

/-- **The level-`k` family over a base `β` of the shift `X₀ + W_{k+1}`.** -/
theorem rvFam {X0 Xh0 β : Ordinal.{0}} (hoff : RvOff S l β X0 Xh0) (hd : leW (k + 1) ∣ X0)
    (hG3 : X0 + leW (k + 1) + Om (1 + 1) < S.psi 0 (Om (1 + 1 + 1)))
    (hG : Xh0 + leO (k + 1) + Om 1 < S.psi 0 (Om (1 + 1)))
    (hβd : leWe (X0 + leW (k + 1)) ∣ β)
    (hβown : ∀ d, d ≤ leWe (X0 + leW (k + 1)) → β ∈ S.CSet (β + d) (S.psi (β + d) (Om (1 + 1)))) :
    ∀ ζ, GxCl (upsilon l) (ldAtR S l) ζ → ζ < leTe S (X0 + leW (k + 1)) β →
      gxTh (upsilon l) (ldAtR S l) ζ < Om 1 →
      RvOff S l β (X0 + leW k * ζ) (Xh0 + leO k * gxTh (upsilon l) (ldAtR S l) ζ) := by
  obtain ⟨-, -, hX0m, -, hX0cl, -⟩ := rvOff_data hoff
  have hX0G3 : X0 + leW (k + 1) < S.psi 0 (Om (1 + 1 + 1)) := le_self_add.trans_lt hG3
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  have hk0 : leW k ≠ 0 := (leW_pos k).ne'
  have hOk0 : leO k ≠ 0 := (leO_pos k).ne'
  have hdk : leW k ∣ X0 := (leW_dvd (Nat.le_succ k)).trans hd
  have hmem : ∀ ζ, GxCl (upsilon l) (ldAtR S l) ζ → ζ < leTe S (X0 + leW (k + 1)) β →
      gxTh (upsilon l) (ldAtR S l) ζ < Om 1 → ζ ≠ 0 →
      RvSh S l β (X0 + leW k * ζ) (Xh0 + leO k * gxTh (upsilon l) (ldAtR S l) ζ) := fun ζ hζ hζT hΘ hζ0 =>
    rvSh_m hl hX hk hoff hζ (hζT.trans (leTe_lt_Om2 _ _)) (rvEM_gtT hβown hX0m hβd hX0cl hX0G3 hζT) hΘ
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
    have hT0 : ζ0 < leTe S (X0 + leW (k + 1)) β := (lt_add_one ζ0).trans hζT
    have hoff0 := IHz ζ0 (lt_add_one ζ0) hζ0c hT0 hΘ0
    have hΘs := rqTh_succ hl hX hζ0c
    have hle1 : leW k * ζ0 + leW k ≤ leW (k + 1) := by
      rw [← mul_add_one]; exact (rvW_lt_succ hζW).le
    have hle2 : leO k * gxTh (upsilon l) (ldAtR S l) ζ0 + leO k ≤ leO (k + 1) := by
      rw [← mul_add_one, ← hΘs]; exact (rvO_lt_succ hΘ1).le
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
        RvSh S l β (X0 + leW k * (c + 1)) (Xh0 + leO k * gxTh (upsilon l) (ldAtR S l) (c + 1)) ∧
        RvTop S l β (X0 + leW k * (c + 1)) (Xh0 + leO k * gxTh (upsilon l) (ldAtR S l) (c + 1)) 0 ∧
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
        refine ⟨X0, Xh0, le_self_add, hxX, lt_add_of_pos_right _ (mul_pos (leO_pos k) hΘpos), hs0, ht0⟩
      · obtain ⟨r, rfl⟩ := exists_add_of_le hxX
        have hr : r < leW k * ζ := (add_lt_add_iff_left X0).1 hx
        have hrW : r < leW (k + 1) := hr.trans (rvW_lt_succ hζW)
        have hrH : r ∈ cdHull S l := by
          have h1 := leModP_mem (S := S) (Om (1 + 1) * ((k + 1 : ℕ) : Ordinal.{0})) hxH
          have hm : (X0 + r) % ω ^ (Om (1 + 1) * ((k + 1 : ℕ) : Ordinal.{0})) = r := by
            obtain ⟨q, hq⟩ := hd
            change (X0 + r) % leW (k + 1) = r
            rw [hq, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hrW]
          rwa [hm] at h1
        have hq : r / leW k < ζ := (Ordinal.lt_mul_iff_div_lt hk0).1 hr
        have hqc := (ldHull_iff hl hX (hq.trans hζW)).1 (leDivW_mem k hrH)
        obtain ⟨hs1, ht1, hΘlt⟩ := hsub _ hqc hq
        refine ⟨_, _, ?_, ?_, (add_lt_add_iff_left Xh0).2 ((mul_lt_mul_iff_right₀ (leO_pos k)).2 hΘlt), hs1, ht1⟩
        · exact (add_le_add_iff_left X0).2 (mul_le_mul_right (Order.add_one_le_of_lt hq) _)
        · refine (add_lt_add_iff_left X0).2 ?_
          rw [mul_add_one]; exact Ordinal.lt_mul_div_add r hk0
    · rcases lt_or_ge z Xh0 with hzX | hzX
      · have hXh00 : Xh0 ≠ 0 := (zero_le.trans_lt hzX).ne'
        obtain ⟨hs0, ht0⟩ := rvOff_neh hoff hXh00
        exact ⟨X0, Xh0, lt_add_of_pos_right _ (mul_pos (leW_pos k) (pos_iff_ne_zero.2 hζ0)), hzX, hs0, ht0⟩
      · obtain ⟨u, rfl⟩ := exists_add_of_le hzX
        have hu : u < leO k * gxTh (upsilon l) (ldAtR S l) ζ := (add_lt_add_iff_left Xh0).1 hz
        have hq : u / leO k < gxTh (upsilon l) (ldAtR S l) ζ := (Ordinal.lt_mul_iff_div_lt hOk0).1 hu
        obtain ⟨c, hc, hcζ, hcz⟩ := gxTh_onto hq
        obtain ⟨hs1, ht1, -⟩ := hsub c hc hcζ
        refine ⟨_, _, (add_lt_add_iff_left X0).2 ((mul_lt_mul_iff_right₀ (leW_pos k)).2 (hlim.succ_lt hcζ)), ?_,
          hs1, ht1⟩
        refine (add_lt_add_iff_left Xh0).2 ?_
        rw [rqTh_succ hl hX hc, hcz, mul_add_one]; exact Ordinal.lt_mul_div_add u hOk0

end Main

end Googology.Trans.PoR.InaccPsi.R2.Rv
