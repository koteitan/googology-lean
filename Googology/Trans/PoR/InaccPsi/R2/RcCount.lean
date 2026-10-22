import Googology.Trans.PoR.InaccPsi.R2.RaLw

/-!
# The predicted reach as a count of closed points

`k_λ` enumerates the closed points `K_λ` (`Cd.cdK`), so a lower bound of `r(λ) = k_λ(Θ_λ(m_λ))` is exactly an
upper bound of the order type of `K_λ` below it:

* `rcOtp_enum` (**`otp(s ∩ enum_s(p)) = p`** for an unbounded `s`), `rcLe_enum_iff`
  (**`X ≤ enum_s(p) ⇔ otp(s ∩ X) ≤ p`**), `rcEnum_otp` (**`enum_s(otp(s ∩ X)) = X` for `X ∈ s`**);
* `rcLe_R_iff` (**`X ≤ r(λ) ⇔ otp(K_λ ∩ X) ≤ Θ_λ(m_λ)`**), `rcR_eq_iff` (**for `X ∈ K_λ`: `r(λ) = X ⇔
  Θ_λ(m_λ) = otp(K_λ ∩ X)`**), `rcCount_delta` (`otp(K_λ ∩ (δ_λ + x)) ≤ x`), `rcLe_R_of_read`
  (`X ≤ Θ_λ(m_λ)` gives `X ≤ r(λ)`), `rcSmall` (`υ_{λ+γ} ≤ r(λ)` for `γ ≤ ω + 1`);
* `rcSupAt_iff_count` (**`RaSupAt S a` as a count**: cofinal Range restarts `μ` with
  `otp(K_μ ∩ υ_{μ+γ}) ≤ Θ_μ(m_μ)`).

No new axiom, no new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Rc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- **`otp(s ∩ enum_s(p)) = p`** for an unbounded `s`. -/
theorem rcOtp_enum {s : Set Ordinal.{0}} (hs : ¬ BddAbove s) : ∀ p, cdOtp s (enumOrd s p) = p := by
  intro p
  induction p using WellFoundedLT.induction with
  | ind p IH =>
  have hm := enumOrd_strictMono hs
  refine le_antisymm ?_ (le_of_forall_lt fun x hx => ?_)
  · classical
    rw [cdOtp_eq]
    refine ciSup_le' fun c => ?_
    split_ifs with hc
    · obtain ⟨q, hq⟩ := enumOrd_surjective hs hc
      have hqp : q < p := hm.lt_iff_lt.1 (hq ▸ c.2)
      rw [← hq, IH q hqp]
      exact Order.add_one_le_of_lt hqp
    · exact zero_le
  · have h := cdOtp_lt_of_mem (enumOrd_mem hs x) (hm hx)
    rwa [IH x hx] at h

/-- **`X ≤ enum_s(p) ⇔ otp(s ∩ X) ≤ p`.** -/
theorem rcLe_enum_iff {s : Set Ordinal.{0}} (hs : ¬ BddAbove s) (X p : Ordinal.{0}) :
    X ≤ enumOrd s p ↔ cdOtp s X ≤ p := by
  constructor
  · intro h
    exact (cdOtp_mono s h).trans (rcOtp_enum hs p).le
  · intro h
    by_contra hlt
    rw [not_le] at hlt
    have h1 := cdOtp_lt_of_mem (enumOrd_mem hs p) hlt
    rw [rcOtp_enum hs p] at h1
    exact absurd (h1.trans_le h) (lt_irrefl _)

/-- **`enum_s(otp(s ∩ X)) = X` for `X ∈ s`.** -/
theorem rcEnum_otp {s : Set Ordinal.{0}} (hs : ¬ BddAbove s) {X : Ordinal.{0}} (hX : X ∈ s) :
    enumOrd s (cdOtp s X) = X := by
  obtain ⟨p, hp⟩ := enumOrd_surjective hs hX
  rw [← hp, rcOtp_enum hs p]

/-- **`X ≤ r(λ) ⇔ otp(K_λ ∩ X) ≤ Θ_λ(m_λ)`.** -/
theorem rcLe_R_iff (S : InaccSeq.{0}) (l X : Ordinal.{0}) :
    X ≤ cdR S l ↔ cdOtp (cdK l) X ≤ cdTheta S l (cdCode S l) := by
  unfold cdR cdRc cdk
  exact rcLe_enum_iff (cdK_unbdd l) X _

/-- **For a closed point `X ∈ K_λ`: `r(λ) = X ⇔ Θ_λ(m_λ) = otp(K_λ ∩ X)`.** -/
theorem rcR_eq_iff (S : InaccSeq.{0}) {l X : Ordinal.{0}} (hX : X ∈ cdK l) :
    cdR S l = X ↔ cdTheta S l (cdCode S l) = cdOtp (cdK l) X := by
  unfold cdR cdRc cdk
  constructor
  · intro h
    rw [← h, rcOtp_enum (cdK_unbdd l)]
  · intro h
    rw [h]
    exact rcEnum_otp (cdK_unbdd l) hX

/-- `otp(K_λ ∩ (δ_λ + x)) ≤ x`. -/
theorem rcCount_delta (l x : Ordinal.{0}) : cdOtp (cdK l) (cdDelta l + x) ≤ x := by
  have h : cdDelta l + x ≤ enumOrd (cdK l) x := Ra.raK_ge_add l x
  exact (rcLe_enum_iff (cdK_unbdd l) _ _).1 h

/-- A reading `X ≤ Θ_λ(m_λ)` gives `X ≤ r(λ)`. -/
theorem rcLe_R_of_read {l X : Ordinal.{0}} (h : X ≤ cdTheta S l (cdCode S l)) : X ≤ cdR S l :=
  (rcLe_R_iff S l X).2 ((cdOtp_le_self _ X).trans h)

/-- `υ_{λ+γ} ≤ r(λ)` for every `γ ≤ ω + 1` (the first block is always supplied). -/
theorem rcSmall (S : InaccSeq.{0}) {l γ : Ordinal.{0}} (hγ : γ ≤ ω + 1) : upsilon (l + γ) ≤ cdR S l := by
  refine le_trans ?_ (cdR_ge S l)
  unfold cdDelta
  rw [add_assoc]
  exact upsilon_normal.strictMono.monotone (add_le_add le_rfl hγ)

/-- **`RaSupAt S a` as a count of closed points.** -/
theorem rcSupAt_iff_count (a : Ordinal.{0}) :
    Ra.RaSupAt S a ↔ ∀ γ < a, ∃ μ, CdRange S μ ∧ γ < upsilon μ ∧ upsilon μ < a ∧
      ω ^ Om 1 ∣ cdEta S μ ∧ cdOtp (cdK μ) (upsilon (μ + γ)) ≤ cdTheta S μ (cdCode S μ) := by
  constructor
  · intro h γ hγ
    obtain ⟨μ, h1, h2, h3, h4, h5⟩ := h γ hγ
    exact ⟨μ, h1, h2, h3, h4, (rcLe_R_iff S μ _).1 h5⟩
  · intro h γ hγ
    obtain ⟨μ, h1, h2, h3, h4, h5⟩ := h γ hγ
    exact ⟨μ, h1, h2, h3, h4, (rcLe_R_iff S μ _).2 h5⟩

end Googology.Trans.PoR.InaccPsi.R2.Rc
