import Googology.Trans.PoR.InaccPsi.R2.SoPoly

/-!
# The polynomial supply: `υ_{μ+ρ_μ^ω} ≤ r(μ)` at every Range restart with code `G_{k+1} + 1`

`ρ = ρ_μ = υ_μ`, `θ₂ = ψ_{Ω₃}(Ω_ω)`, `G(z) = ψ_{Ω₂}(Ω_ω + θ₂·z)`.  The reading `x = Σ ρ^i·c_i < ρ^ω`
(`c_i < ρ`) has the code `soP Ω₁ ρ x = Σ Ω₁^i·c_i`: a member of every `Cl(a, b)` with `a > Ω_ω`, `b ≥ ρ`, below
`Ω₁^ω < θ_{k+1}`.  `So.soSup_gen` along this code map gives the supply for the polynomial renaming.

* `soPMem` (`ω^e·soP Ω₁ ρ x` is a member when `e` is), `soP_lt_th` (`soP Ω₁ ρ x < θ_{k+1}`);
* `soSupP` (**`υ_{μ+ρ_μ^ω} ≤ Θ_μ(G') ≤ r(μ)`, unconditionally**), `soSupW_of_P` (`Sl.SlSupW` again).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.So

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- `ω^e·soP Ω₁ ρ x ∈ Cl(a, b)` for a member `e`, `x < ρ^n`, `ρ ≤ b`. -/
theorem soPMem {a b ρ : Ordinal.{0}} (hρ1 : 1 < ρ) (hb : ρ ≤ b) :
    ∀ n : ℕ, ∀ x, x < ρ ^ n → ∀ e, e ∈ S.CSet a b → ω ^ e * soP (Om 1) ρ x ∈ S.CSet a b := by
  intro n
  induction n with
  | zero =>
    intro x hx e _
    rw [pow_zero, Order.lt_one_iff] at hx
    rw [hx, soP_zero, mul_zero]; exact CSet.zero_mem a b
  | succ n ih =>
    intro x hx e he
    obtain ⟨ex, hm, -⟩ := soSplit (g := x) hρ1
    have hQ := soDivPow hρ1 hx
    have hQω := hQ.trans (soPow_lt_omega hρ1 n)
    have hO : ω ^ e * Om 1 = ω ^ (e + Om 1) := by rw [opow_add, soOm1_opow]
    rw [ex, soP_bot (Om 1) hρ1 hm hQω, mul_add, ← mul_assoc, hO]
    exact CSet.add_mem (ih _ hQ _ (CSet.add_mem he (CSet.Om_mem (CSet.one_mem a b))))
      (Nm.mem_opow_mul he (hm.trans_le hb))

/-- `soP Ω₁ ρ x < θ_{k+1}` for `x < ρ^ω`, `ρ < Ω₁`. -/
theorem soP_lt_th {ρ x : Ordinal.{0}} (k : ℕ) (hρ1 : 1 < ρ) (hρΩ : ρ < Om 1) (hx : x < ρ ^ ω) :
    soP (Om 1) ρ x < Lc.lcTh S (k + 1) := by
  have hO1 : (1 : Ordinal.{0}) < Om 1 := hρ1.trans hρΩ
  have h1 := soP_lt hρ1 hO1 hx ((soMD_lt hρ1 hx).trans hρΩ)
  have hE : InE (Lc.lcTh S (k + 1)) := Low.opow_eq_self_of_SC (Ls.lsTh_SC (k + 1))
  exact h1.trans (soE_opow_lt hE (Rp.rpOm1_lt_th k) (Sl.slE_omega_lt hE))

/-- **The polynomial supply**: `υ_{μ+ρ_μ^ω} ≤ Θ_μ(G') ≤ r(μ)` at every Range restart `μ` with code
`G_{k+1} + 1`. -/
theorem soSupP (k : ℕ) {μ : Ordinal.{0}} (hR : CdRange S μ) (hc : cdCode S μ = Ls.lsG S (k + 1) + 1) :
    upsilon (μ + upsilon μ ^ ω) ≤ cdTheta S μ (Ls.lsG S (k + 1)) ∧
      upsilon (μ + upsilon μ ^ ω) ≤ cdR S μ := by
  obtain ⟨hgμ, -, hpv⟩ := Ra.raName hR
  set ρ := upsilon μ with hρdef
  have hρE : InE ρ := by rw [← hpv]; exact Sl.slPv_E _
  have hρ1 : 1 < ρ := soOne_lt_E hρE
  have hρΩ : ρ < Om 1 := soRho_lt_Om1 hR
  have hlim : IsSuccLimit (ρ ^ ω) := isSuccLimit_opow hρ1 isSuccLimit_omega0
  refine soSup_gen hR hc hlim (fun y hy => soGood hgμ (by rw [hpv]; exact hy))
    (by rw [← hpv]; exact (soPvOpow_lt_Om1 _ hgμ).le) (soP (Om 1) ρ) ?_ ?_ ?_ ?_
  · intro x hx
    have hxω : x < ρ ^ ω := (lt_add_one x).trans hx
    exact soP_succ (Om 1) hρ1 hxω (hρE.add_lt (Ordinal.mod_lt x hρE.pos.ne') hρ1)
  · intro y x hyx hx
    rcases hyx.lt_or_eq with h | h
    · exact (soP_strict hρ1 h hx ((soMD_lt hρ1 (h.trans hx)).trans hρΩ) ((soMD_lt hρ1 hx).trans hρΩ)).le
    · rw [h]
  · intro x hx a b ha hb
    obtain ⟨n, hn⟩ := soExists_pow hρ1 hx
    have h := soPMem (S := S) hρ1 hb n x hn _ (Ls.lsTh_mem ha 2)
    rw [Ls.lsTh_opow] at h
    exact CSet.add_mem (ConjT.OmW_mem S a b) h
  · intro x hx
    exact soP_lt_th k hρ1 hρΩ hx

/-- `Sl.SlSupW` from the polynomial supply (`ρ_μ·ω ≤ ρ_μ^ω`). -/
theorem soSupW_of_P (k : ℕ) : Sl.SlSupW S k := by
  intro μ hR hc
  have hρ1 : 1 < upsilon μ := soOne_lt_E (by rw [← Ls.lsPv_range hR]; exact Sl.slPv_E _)
  have hle : upsilon μ * ω ≤ upsilon μ ^ ω := by
    calc upsilon μ * ω ≤ upsilon μ ^ (1 : Ordinal.{0}) * upsilon μ ^ ω :=
          by rw [opow_one]; exact mul_le_mul_of_nonneg_left (right_le_opow ω hρ1) zero_le
      _ = upsilon μ ^ ω := by rw [← opow_add, one_add_omega0]
  exact (upsilon_normal.strictMono.monotone (add_le_add le_rfl hle)).trans (soSupP k hR hc).2

end Googology.Trans.PoR.InaccPsi.R2.So
