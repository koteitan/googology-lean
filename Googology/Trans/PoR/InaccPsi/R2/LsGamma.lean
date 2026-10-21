import Googology.Trans.PoR.InaccPsi.R2.LsStrict

/-!
# The reading of a strongly critical code is a `Γ`-value: `Θ(s) = Γ(ξ₀ + 1 + otp(atoms ∩ s))`

`Γ = Ordinal.gamma` (the enumeration of the strongly critical ordinals, the fixed points of `φ(·, 0)`),
`ρ = ψ_{Ω₁}(A) = Γ(ξ₀)`, the hull `Cl(A, ρ)`, `Θ(m) = otp(Cl(A, ρ) ∩ m)`, the atoms `lsAt S A ρ` (the
`ψ_{Ω₂}(e)`, `e ∈ Cl(A, ρ) ∩ A`).  By `lsOtp_least`, `Θ(s)` is the least strongly critical ordinal above `ρ` and
the readings of the atoms below `s`; by induction on `s` this is a closed formula:

* `lsSC_of_veblen`, `lsGamma_SC`, `lsSC_gamma` (**the strongly critical ordinals are the values of `Γ`**);
* `lsOtp_gamma` (**`Θ(s) = Γ(ξ₀ + 1 + τ(s))` for every strongly critical `s ∈ (Ω₁, Ω₂]`**, `τ(s)` the order
  type of the atoms below `s`);
* `lsStrict_iff_gamma` (**LC-STRICT at `λ, k` ⇔ `ψ_{Ω₁}(A_{η_λ} + G_k) ≤ Γ(ξ₀ + 1 + τ(G_{k+1}))`**, with
  `Γ(ξ₀) = ρ_λ`): LC-STRICT is an inequality between the `Γ`-index of `H(η_λ + G_k)` and the number of
  `ψ_{Ω₂}`-atoms of the hull below `G_{k+1}`; `lsGamma_idx` (`ρ_λ` has a `Γ`-index).

No new axiom, no new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ls

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Mx

variable {S : InaccSeq.{0}}

/-- A positive fixed point of `φ(·, 0)` is strongly critical. -/
theorem lsSC_of_veblen {x : Ordinal.{0}} (h0 : 0 < x) (h : veblen x 0 = x) : SC x := by
  refine ⟨h0, fun a ha b hb => ?_⟩
  have h1 : veblen a x = x := by
    conv_lhs => rw [← h]
    rw [veblen_veblen_of_lt ha, h]
  calc veblen a b < veblen a x := veblen_lt_veblen_iff_right.2 hb
    _ = x := h1

theorem lsGamma_SC (y : Ordinal.{0}) : SC (gamma y) := lsSC_of_veblen gamma_pos (veblen_gamma_zero y)

/-- **A strongly critical ordinal is a value of `Γ`.** -/
theorem lsSC_gamma {x : Ordinal.{0}} (h : SC x) : ∃ y, gamma y = x :=
  mem_range_gamma.2 h.veblen_zero

/-- **`Θ(s) = Γ(ξ₀ + 1 + τ(s))`** for a strongly critical `s ∈ (Ω₁, Ω₂]`, `ρ = ψ_{Ω₁}(A) = Γ(ξ₀)`. -/
theorem lsOtp_gamma {A ρ ξ0 : Ordinal.{0}} (hρ : S.psi A (Om 1) = ρ) (hξ : gamma ξ0 = ρ) :
    ∀ s, SC s → Om 1 < s → s ≤ Om (1 + 1) →
      cdOtp (S.CSet A ρ) s = gamma (ξ0 + 1 + cdOtp (lsAt S A ρ) s) := by
  intro s
  induction s using WellFoundedLT.induction with
  | ind s IH =>
  intro hs h1 hs2
  have hat : ∀ t ∈ lsAt S A ρ, t < s → cdOtp (S.CSet A ρ) t = gamma (ξ0 + 1 + cdOtp (lsAt S A ρ) t) :=
    fun t ht hts => IH t hts ((lsAt_GxAt A ρ) t ht).1 ((lsAt_GxAt A ρ) t ht).2 (lsAt_lt_Om2 ht).le
  apply le_antisymm
  · refine lsOtp_least hρ hs2 (lsGamma_SC _) ?_ fun t ht hts => ?_
    · rw [← hξ]
      exact gamma_lt_gamma.2 ((lt_add_one ξ0).trans_le le_self_add)
    · rw [hat t ht hts]
      exact gamma_lt_gamma.2 ((add_lt_add_iff_left _).2 (cdOtp_lt_of_mem ht hts))
  · obtain ⟨y, hy⟩ := lsSC_gamma (lsOtp_SC hρ hs h1 hs2)
    rw [← hy]
    have hy0 : ξ0 < y := gamma_lt_gamma.1 (by rw [hy, hξ]; exact lsOtp_gt hρ h1 hs2)
    obtain ⟨w, hw⟩ := exists_add_of_le (Order.add_one_le_of_lt hy0)
    rw [hw]
    refine gamma_le_gamma.2 (add_le_add le_rfl (le_of_forall_lt fun ν hν => ?_))
    obtain ⟨t, ht, hts, rfl⟩ := Gg.ggOtp_onto (lsAt S A ρ) s ν hν
    have h2 := lsOtp_atom_lt ht hts
    rw [hat t ht hts, ← hy, hw] at h2
    exact (add_lt_add_iff_left _).1 (gamma_lt_gamma.1 h2)

/-- `ρ_λ` has a `Γ`-index. -/
theorem lsGamma_idx {l : Ordinal.{0}} (hpv : Nm.Pv S (cdEta S l) = upsilon l) :
    ∃ ξ0, gamma ξ0 = upsilon l :=
  lsSC_gamma (lsRho_SC hpv)

/-- **LC-STRICT ⇔ `ψ_{Ω₁}(A_{η_λ} + G_k) ≤ Γ(ξ₀ + 1 + τ(G_{k+1}))`.** -/
theorem lsStrict_iff_gamma {l ξ0 : Ordinal.{0}} {k : ℕ} (hpv : Nm.Pv S (cdEta S l) = upsilon l)
    (hξ : gamma ξ0 = upsilon l) :
    Lc.LcStrictAt S l k ↔ S.psi (ConjT.Aη S (cdEta S l) + lsG S k) (Om 1) ≤
      gamma (ξ0 + 1 + cdOtp (lsAt S (ConjT.Aη S (cdEta S l)) (upsilon l)) (lsG S (k + 1))) := by
  unfold Lc.LcStrictAt
  rw [lsH_G]
  have e : cdTheta S l (lsG S (k + 1)) =
      gamma (ξ0 + 1 + cdOtp (lsAt S (ConjT.Aη S (cdEta S l)) (upsilon l)) (lsG S (k + 1))) := by
    unfold cdTheta cdHull
    exact lsOtp_gamma hpv hξ _ (lsG_SC _) (lsG_Om1 _) (lsG_Om2 _)
  rw [← e]

end Googology.Trans.PoR.InaccPsi.R2.Ls
