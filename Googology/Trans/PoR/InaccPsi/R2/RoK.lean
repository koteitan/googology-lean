import Googology.Trans.PoR.InaccPsi.R2.RoPull

/-!
# The shifts `X = Ω₂·k`: the top law at every exponent `Ω₂·k + e`

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `T_E(β) = ψ_{Ω₂}(β + W^E)`.

* `roSh_k` (**`(Ω₂·k, Ω₁·k)` is a shift** for every `k ≥ 1`), `roWe_lt_OmW`;
* `roTop_one` (`RoTop (Ω₂·1) (Ω₁·1) 0` is `Rn.rnTopW`), `roTopK` (**`RoTop (Ω₂·k) (Ω₁·k) 0` for every `k ≥ 1`**,
  by `Ro.roTopW`), `roTopKE` (**`RoTop (Ω₂·k) (Ω₁·k) e` for every `k ≥ 1` and every code `e`**:
  `Θ(ψ_{Ω₂}(β + W^{Ω₂·k+e})) = ψ_{Ω₁}(Â + Ω^{Ω₁·k + Θ e})`);
* `roTh_k0` (**at the base `0`: `Θ_λ(ψ_{Ω₂}(Ω₂^{Ω₂·k+e})) = ψ_{Ω₁}(A + 1 + Ω₁^{Ω₁·k + Θ_λ e})`** for every code
  `e < ψ_{Ω₂}(Ω₂^{Ω₂·k+e})`, `A` own with `ψ_{Ω₁}(A) = ρ_λ`; e.g. `F₂ = ψ_{Ω₂}(Ω₂^{Ω₂·2})` is read as
  `ψ_{Ω₁}(A + 1 + Ω₁^{Ω₁·2})`).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ro

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn

variable {S : InaccSeq.{0}}

theorem roWe_lt_OmW {x : Ordinal.{0}} (hx : x < Om ω) : leWe x < Om ω :=
  (leWe_lt_SC (SC_Om omega0_ne_zero) ldOm2_lt_OmW hx).1

theorem roNat_lt_SC {G : Ordinal.{0}} (hG : SC G) (k : ℕ) : (k : Ordinal.{0}) < G :=
  (natCast_lt_omega0 k).trans (Lw.lw_omega_lt_SC hG)

/-- **`(Ω₂·k, Ω₁·k)` is a shift** for every `k ≥ 1`. -/
theorem roSh_k {k : ℕ} (hk : 1 ≤ k) : RoSh S (Om (1 + 1) * (k : Ordinal.{0})) (Om 1 * (k : Ordinal.{0})) := by
  have hG3 : SC (S.psi 0 (Om (1 + 1 + 1))) := SC_psi (InR_Om_succ (1 + 1)) 0
  have hWG3 : Om (1 + 1 : Ordinal.{0}) < S.psi 0 (Om (1 + 1 + 1)) := (psiS_bounds (S := S) 0 (1 + 1)).1
  have hG1 : SC (S.psi 0 (Om (1 + 1))) := SC_psi (InR_Om_succ 1) 0
  have hΩG1 : Om (1 : Ordinal.{0}) < S.psi 0 (Om (1 + 1)) := (psiS_bounds (S := S) 0 1).1
  have hk0 : (k : Ordinal.{0}) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hk)
  refine ⟨mul_ne_zero ldOm2_SC.1.ne' hk0, dvd_mul_right _ _, fun a b => mul_nat_mem (mxOm2_mem a b) k,
    fun a b => mul_nat_mem (CSet.Om_mem (CSet.one_mem a b)) k, ?_, ?_, fun Q hQ => LeCl.natMul hQ.1 k,
    fun Q hQ => LeCl.natMul hQ.1 k⟩
  · rw [← mul_add_one]
    exact ldMul_lt_SC hG3 hWG3 (by exact_mod_cast roNat_lt_SC hG3 (k + 1))
  · rw [← mul_add_one]
    exact ldMul_lt_SC hG1 hΩG1 (by exact_mod_cast roNat_lt_SC hG1 (k + 1))

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- `RoTop (Ω₂·1) (Ω₁·1) 0` is `Rn.rnTopW`. -/
theorem roTop_one : RoTop S l (Om (1 + 1) * ((1 : ℕ) : Ordinal.{0})) (Om 1 * ((1 : ℕ) : Ordinal.{0})) 0 := by
  intro β Â hb hÂ hbase
  obtain ⟨hβd, hβH, hβA, hβown, -⟩ := hb
  simp only [Nat.cast_one, mul_one, add_zero, gxTh_zero] at hβd hβA hβown ⊢
  have e1 := rnTopW hl hX ⟨hβd, hβH, hβA, hβown⟩ hÂ hbase
  exact e1

/-- **`RoTop (Ω₂·k) (Ω₁·k) 0` for every `k ≥ 1`.** -/
theorem roTopK : ∀ k : ℕ, 1 ≤ k →
    RoTop S l (Om (1 + 1) * (k : Ordinal.{0})) (Om 1 * (k : Ordinal.{0})) 0
  | 0, h => absurd h (by norm_num)
  | 1, _ => roTop_one hl hX
  | k + 2, _ => by
    have hs := roSh_k (S := S) (k := k + 1) (by omega)
    have IH := roTopK (k + 1) (by omega)
    have h := roTopW hs hl hX (roTopE hs hl hX IH)
    rw [← mul_add_one, ← mul_add_one] at h
    have e : ((k + 1 : ℕ) : Ordinal.{0}) + 1 = ((k + 2 : ℕ) : Ordinal.{0}) := (Nat.cast_succ (k + 1)).symm
    rw [e] at h
    exact h

/-- **`RoTop (Ω₂·k) (Ω₁·k) e` for every `k ≥ 1` and every code `e`.** -/
theorem roTopKE {k : ℕ} (hk : 1 ≤ k) :
    ∀ e, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) →
      RoTop S l (Om (1 + 1) * (k : Ordinal.{0})) (Om 1 * (k : Ordinal.{0})) e :=
  roTopE (roSh_k hk) hl hX (roTopK hl hX k hk)

/-- **At the base `0`: `Θ_λ(ψ_{Ω₂}(Ω₂^{Ω₂·k+e})) = ψ_{Ω₁}(A + 1 + Ω₁^{Ω₁·k + Θ_λ e})`.** -/
theorem roTh_k0 {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)
    {k : ℕ} (hk : 1 ≤ k) {e : Ordinal.{0}} (hec : GxCl (upsilon l) (ldAtR S l) e)
    (hexp : ∀ e', GxCl (upsilon l) (ldAtR S l) e' → e' ≤ e →
      e' < S.psi (leWe (Om (1 + 1) * (k : Ordinal.{0}) + e')) (Om (1 + 1))) :
    gxTh (upsilon l) (ldAtR S l) (S.psi (leWe (Om (1 + 1) * (k : Ordinal.{0}) + e)) (Om (1 + 1))) =
      S.psi (A + 1 + leOe (Om 1 * (k : Ordinal.{0}) + gxTh (upsilon l) (ldAtR S l) e)) (Om 1) := by
  have hA1 : A + 1 ∈ S.CSet (A + 1) (S.psi (A + 1) (Om 1)) :=
    CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hA) (CSet.one_mem _ _)
  have heW : e < Om (1 + 1) := (hexp e hec le_rfl).trans (psi_lt (InR_Om_succ 1) _)
  have hkW : Om (1 + 1) * (k : Ordinal.{0}) + e < Om ω := by
    refine (Om_isPrincipal omega0_ne_zero) (ldMulNat_lt (Om_isPrincipal omega0_ne_zero) ldOm2_lt_OmW k)
      (heW.trans ldOm2_lt_OmW)
  have hb : RoBaseE S l (Om (1 + 1) * (k : Ordinal.{0})) e 0 := by
    refine ⟨dvd_zero _, CSet.zero_mem _ _, ?_, fun d _ => CSet.zero_mem _ _, fun e' he' h' => ?_⟩
    · rw [zero_add]; exact (roWe_lt_OmW hkW).trans_le le_self_add
    · have := hexp e' he' h'; rwa [zero_add]
  have h := roTopKE hl hX hk e hec heW 0 (A + 1) hb hA1 (ldBlk_zero hA hρ)
  unfold leTe at h
  rwa [zero_add] at h

end Main

end Googology.Trans.PoR.InaccPsi.R2.Ro
