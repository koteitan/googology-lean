import Googology.Trans.PoR.InaccPsi.R2.RvStep

/-!
# The tops at `Ω₂^k` (every `k ≥ 1`) and at `Ω₂^ω`, and their readings over `0`

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E` (`Le.leWe`), `Ω^x = Ω₁^x` (`Le.leOe`), `W_k = Ω₂^k`, `O_k = Ω₁^k`.

* `rvShK` (`(W_k, O_k)` is a shift of `Ro.RoSh`), `rvTopK` (**`RoTop W_k O_k 0` for every `k ≥ 1`**, from
  `Rv.rvLev_all` with the offset `0`), `rvTopKE` (every code exponent);
* `rvTh_k0` (**`Θ_λ(ψ_{Ω₂}(Ω₂^{Ω₂^k})) = ψ_{Ω₁}(A + 1 + Ω₁^{Ω₁^k})`**);
* `rvShWw`, `rvTopWw` (**`RoTop Ω₂^ω Ω₁^ω 0`**, the limit of the `W_k`), `rvTh_w0`
  (**`Θ_λ(ψ_{Ω₂}(Ω₂^{Ω₂^ω})) = ψ_{Ω₁}(A + 1 + Ω₁^{Ω₁^ω})`**).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Rv

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq

variable {S : InaccSeq.{0}}

theorem rvO_mem (a b : Ordinal.{0}) (k : ℕ) : leO k ∈ S.CSet a b := by
  have := leMulO_mem (S := S) (a := a) (b := b) k (CSet.one_mem a b); rwa [mul_one] at this

theorem rvW_dvd {k : ℕ} (hk : 1 ≤ k) : Om (1 + 1 : Ordinal.{0}) ∣ leW k := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [add_comm, ← rvW_mul j]; exact dvd_mul_right _ _

theorem rvG3 (k : ℕ) : leW k + Om (1 + 1) < S.psi 0 (Om (1 + 1 + 1)) := by
  have hG3 : SC (S.psi 0 (Om (1 + 1 + 1))) := SC_psi (InR_Om_succ (1 + 1)) 0
  have hWG3 : Om (1 + 1 : Ordinal.{0}) < S.psi 0 (Om (1 + 1 + 1)) := (psiS_bounds (S := S) 0 (1 + 1)).1
  exact hG3.isPrincipal (leW_lt_SC hG3 hWG3 k).1 hWG3

theorem rvG1 (k : ℕ) : leO k + Om 1 < S.psi 0 (Om (1 + 1)) := by
  have hG1 : SC (S.psi 0 (Om (1 + 1))) := SC_psi (InR_Om_succ 1) 0
  have hΩG1 : Om (1 : Ordinal.{0}) < S.psi 0 (Om (1 + 1)) := (psiS_bounds (S := S) 0 1).1
  exact hG1.isPrincipal (leO_lt_G1 k) hΩG1

/-- **`(Ω₂^k, Ω₁^k)` is a shift of `Ro.RoSh`** for `k ≥ 1`. -/
theorem rvShK {k : ℕ} (hk : 1 ≤ k) : RoSh S (leW k) (leO k) := by
  refine ⟨(leW_pos k).ne', rvW_dvd hk, fun a b => leW_mem a b k, fun a b => rvO_mem a b k, rvG3 k, rvG1 k,
    fun Q hQ => ?_, fun Q hQ => ?_⟩
  · have := rvClW hQ k (LeCl.small (Q := Q) (κ := Om (1 + 1)) (one_lt_omega0.trans (Lw.lw_omega_lt_SC hQ)))
    rwa [mul_one] at this
  · have := rvClO hQ k (LeCl.small (Q := Q) (κ := Om 1) (one_lt_omega0.trans (Lw.lw_omega_lt_SC hQ)))
    rwa [mul_one] at this

theorem rvBaseK0 {l : Ordinal.{0}} (k : ℕ) : RoBaseE S l (leW k) 0 0 := by
  refine ⟨dvd_zero _, CSet.zero_mem _ _, ?_, fun d _ => CSet.zero_mem _ _, fun e' _ h' => ?_⟩
  · rw [zero_add, add_zero]; exact (roWe_lt_OmW (leW_lt_OmW k)).trans_le le_self_add
  · obtain rfl : e' = 0 := le_antisymm h' zero_le
    exact (SC_psi (InR_Om_succ 1) _).1

/-- Every `x < Ω₂^ω` is below some `Ω₂^k`, `k ≥ 1`. -/
theorem rvLt_Ww {x : Ordinal.{0}} (hx : x < leWe ω) : ∃ k : ℕ, 1 ≤ k ∧ x < leW k := by
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  rcases eq_or_ne x 0 with rfl | hx0
  · exact ⟨1, le_rfl, leW_pos 1⟩
  have hlog : log ω x < Om (1 + 1) * ω :=
    (opow_lt_opow_iff_right one_lt_omega0).1 ((opow_log_le_self ω hx0).trans_lt hx)
  have hm : log ω x / Om (1 + 1) < ω := (Ordinal.lt_mul_iff_div_lt hW0).1 hlog
  obtain ⟨n, hn⟩ := lt_omega0.1 hm
  refine ⟨n + 1, Nat.le_add_left 1 n, ?_⟩
  have h := roLt_We_log x
  rw [hn] at h
  unfold leWe at h; unfold leW; rwa [Nat.cast_succ]

/-- Every `z < Ω₁^ω` is below some `Ω₁^k`, `k ≥ 1`. -/
theorem rvLt_Ow {z : Ordinal.{0}} (hz : z < leOe ω) : ∃ k : ℕ, 1 ≤ k ∧ z < leO k := by
  have hΩ0 : Om (1 : Ordinal.{0}) ≠ 0 := (Om_pos one_ne_zero).ne'
  rcases eq_or_ne z 0 with rfl | hz0
  · exact ⟨1, le_rfl, leO_pos 1⟩
  have hlog : log ω z < Om 1 * ω :=
    (opow_lt_opow_iff_right one_lt_omega0).1 ((opow_log_le_self ω hz0).trans_lt hz)
  have hm : log ω z / Om 1 < ω := (Ordinal.lt_mul_iff_div_lt hΩ0).1 hlog
  obtain ⟨n, hn⟩ := lt_omega0.1 hm
  refine ⟨n + 1, Nat.le_add_left 1 n, ?_⟩
  have h := roLt_Oe_log z
  rw [hn] at h
  unfold leOe at h; unfold leO; rwa [Nat.cast_succ]

theorem rvW_lt_Ww (k : ℕ) : leW k < leWe ω :=
  (opow_lt_opow_iff_right one_lt_omega0).2 ((mul_lt_mul_iff_right₀ ldOm2_SC.1).2 (natCast_lt_omega0 k))

theorem rvO_lt_Ow (k : ℕ) : leO k < leOe ω :=
  (opow_lt_opow_iff_right one_lt_omega0).2 ((mul_lt_mul_iff_right₀ (Om_pos one_ne_zero)).2 (natCast_lt_omega0 k))

/-- **`(Ω₂^ω, Ω₁^ω)` is a shift of `Ro.RoSh`.** -/
theorem rvShWw : RoSh S (leWe ω) (leOe ω) := by
  have hG3 : SC (S.psi 0 (Om (1 + 1 + 1))) := SC_psi (InR_Om_succ (1 + 1)) 0
  have hWG3 : Om (1 + 1 : Ordinal.{0}) < S.psi 0 (Om (1 + 1 + 1)) := (psiS_bounds (S := S) 0 (1 + 1)).1
  have hG1 : SC (S.psi 0 (Om (1 + 1))) := SC_psi (InR_Om_succ 1) 0
  have hΩG1 : Om (1 : Ordinal.{0}) < S.psi 0 (Om (1 + 1)) := (psiS_bounds (S := S) 0 1).1
  have hωm : ∀ a b, (ω : Ordinal.{0}) ∈ S.CSet a b :=
    roSmall_mem ω (by
      have := (opow_lt_opow_iff_right (a := (ω : Ordinal.{0})) one_lt_omega0).2 (one_lt_omega0 : (1 : Ordinal.{0}) < ω)
      rwa [opow_one] at this)
  refine ⟨(leWe_pos _).ne', ?_, fun a b => leWe_mem (hωm a b), fun a b => leOe_mem (hωm a b), ?_, ?_,
    fun Q hQ => ?_, fun Q hQ => ?_⟩
  · have h : leWe 1 ∣ leWe ω := leWe_dvd one_lt_omega0.le
    rwa [leWe_one] at h
  · exact hG3.isPrincipal (leWe_lt_SC hG3 hWG3 ((Lw.lw_omega_lt_SC hG3))).1 hWG3
  · exact hG1.isPrincipal (leOe_lt_SC hG1 hΩG1 ((Lw.lw_omega_lt_SC hG1))).1 hΩG1
  · exact LeCl.opow hQ.1 (LeCl.mulK hQ ldOm2_SC _ (LeCl.small (Lw.lw_omega_lt_SC hQ)))
  · exact LeCl.opow hQ.1 (LeCl.mulK hQ Ph.ph_SC_Om1 _ (LeCl.small (Lw.lw_omega_lt_SC hQ)))

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **`RoTop (Ω₂^k) (Ω₁^k) 0` for every `k ≥ 1`.** -/
theorem rvTopK {k : ℕ} (hk : 1 ≤ k) : RoTop S l (leW k) (leO k) 0 := by
  have h := rvLev_all hl hX k hk 0 0 0 (Or.inl ⟨rfl, rfl⟩) (dvd_zero _) (by rw [zero_add]; exact rvG3 k)
    (by rw [zero_add]; exact rvG1 k)
  rw [zero_add, zero_add] at h
  exact rvTop_zero h

/-- `RoTop (Ω₂^k) (Ω₁^k) e` for every code `e`. -/
theorem rvTopKE {k : ℕ} (hk : 1 ≤ k) : ∀ e, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) →
    RoTop S l (leW k) (leO k) e :=
  roTopE (rvShK hk) hl hX (rvTopK hl hX hk)

/-- **`Θ_λ(ψ_{Ω₂}(Ω₂^{Ω₂^k})) = ψ_{Ω₁}(A + 1 + Ω₁^{Ω₁^k})`** for `k ≥ 1`. -/
theorem rvTh_k0 {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)
    {k : ℕ} (hk : 1 ≤ k) :
    gxTh (upsilon l) (ldAtR S l) (S.psi (leWe (leW k)) (Om (1 + 1))) =
      S.psi (A + 1 + leOe (leO k)) (Om 1) := by
  have hA1 : A + 1 ∈ S.CSet (A + 1) (S.psi (A + 1) (Om 1)) :=
    CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hA) (CSet.one_mem _ _)
  have h := rvTopK hl hX hk 0 (A + 1) (rvBaseK0 k) hA1 (ldBlk_zero hA hρ)
  unfold leTe at h
  rwa [zero_add, add_zero, gxTh_zero, add_zero] at h

/-- **`RoTop (Ω₂^ω) (Ω₁^ω) 0`**: the limit of the shifts `Ω₂^k`. -/
theorem rvTopWw : RoTop S l (leWe ω) (leOe ω) 0 := by
  refine roTopLimSh hl hX rvShWw (fun x _ hx => ?_) (fun z hz => ?_)
  · obtain ⟨k, hk, hxk⟩ := rvLt_Ww hx
    exact ⟨leW k, leO k, (rvW_lt_Ww k).le, hxk, rvO_lt_Ow k, fun a b => rvO_mem a b k, rvTopK hl hX hk⟩
  · obtain ⟨k, hk, hzk⟩ := rvLt_Ow hz
    exact ⟨leW k, leO k, rvW_lt_Ww k, hzk, fun a b => leW_mem a b k, rvTopK hl hX hk⟩

/-- **`Θ_λ(ψ_{Ω₂}(Ω₂^{Ω₂^ω})) = ψ_{Ω₁}(A + 1 + Ω₁^{Ω₁^ω})`.** -/
theorem rvTh_w0 {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l) :
    gxTh (upsilon l) (ldAtR S l) (S.psi (leWe (leWe ω)) (Om (1 + 1))) =
      S.psi (A + 1 + leOe (leOe ω)) (Om 1) := by
  have hA1 : A + 1 ∈ S.CSet (A + 1) (S.psi (A + 1) (Om 1)) :=
    CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hA) (CSet.one_mem _ _)
  have hb : RoBaseE S l (leWe ω) 0 0 := by
    refine ⟨dvd_zero _, CSet.zero_mem _ _, ?_, fun d _ => CSet.zero_mem _ _, fun e' _ h' => ?_⟩
    · rw [zero_add, add_zero]; exact (roWe_lt_OmW leWw_lt_OmW).trans_le le_self_add
    · obtain rfl : e' = 0 := le_antisymm h' zero_le
      exact (SC_psi (InR_Om_succ 1) _).1
  have h := rvTopWw hl hX 0 (A + 1) hb hA1 (ldBlk_zero hA hρ)
  unfold leTe at h
  rwa [zero_add, add_zero, gxTh_zero, add_zero] at h

end Main

end Googology.Trans.PoR.InaccPsi.R2.Rv
