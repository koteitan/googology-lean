import Googology.Trans.PoR.InaccPsi.R2.CdDef

/-!
# Lower bounds of `k_λ`, of the predicted reach `r(λ)` and of the reading `Θ_λ`

`k_λ = Cd.cdk λ` (the enumeration of the closed points, all `≥ δ_λ`), `Θ_λ = Cd.cdTheta S λ` (the
order type of the codes of the hull `Cl(A_{η_λ}, ρ_λ)` below a code), `r(λ) = Cd.cdR S λ =
k_λ(Θ_λ(m_λ))`.  These are the inequalities that the bound clause `D(y) ≤ r(μ)` of a realizer map can
use:

* `rlk_ge`: `δ_λ + p ≤ k_λ(p)`; `rlRc_ge`: `δ_λ + Θ_λ(c) ≤ k_λ(Θ_λ(c))`;
  `rlR_ge`: `δ_λ + Θ_λ(m_λ) ≤ r(λ)`; `rlBound_of_theta`: `y ≤ δ_μ + Θ_μ(m_μ) → y ≤ r(μ)`;
* `rlOtp_ge_embed` (**order type by an embedding**): a strictly increasing `f` on `[0, x)` with values
  in `C ∩ [0, m)` gives `x ≤ otp(C ∩ [0, m))`;
* `rlOtp_add_ge` (**superadditivity**): if `C` is closed under `z ↦ e + z`, then
  `otp(C ∩ e) + otp(C ∩ x) ≤ otp(C ∩ (e + x))`;
* for the hull: `rlTheta_ge_min` (`min(c, ρ_λ) ≤ Θ_λ(c)`), `rlTheta_Om1_add`
  (`ρ_λ + Θ_λ(x) ≤ Θ_λ(Ω₁ + x)` when `ρ_λ = P(η_λ)`), `rlTheta_Om1_mul`
  (`ρ_λ·n + Θ_λ(x) ≤ Θ_λ(Ω₁·n + x)`), and `rlR_ge_Om1` (`δ_μ + (ρ_μ·n + Θ_μ(x)) ≤ r(μ)` when
  `Ω₁·n + x ≤ m_μ`).

No axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Rl

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Cd

/-- **`δ_λ + p ≤ k_λ(p)`.** -/
theorem rlk_ge (l p : Ordinal.{0}) : cdDelta l + p ≤ cdk l p := by
  induction p using WellFoundedLT.induction with
  | ind p IH =>
  refine le_of_forall_lt fun w hw => ?_
  rcases lt_or_ge w (cdDelta l) with h | h
  · exact h.trans_le (cdk_ge l p)
  · obtain ⟨v, rfl⟩ := exists_add_of_le h
    have hv : v < p := (add_lt_add_iff_left _).1 hw
    exact (IH v hv).trans_lt (cdk_strictMono l hv)

theorem rlRc_ge (S : InaccSeq.{0}) (l c : Ordinal.{0}) :
    cdDelta l + cdTheta S l c ≤ cdRc S l c := rlk_ge l _

/-- **`δ_λ + Θ_λ(m_λ) ≤ r(λ)`.** -/
theorem rlR_ge (S : InaccSeq.{0}) (l : Ordinal.{0}) :
    cdDelta l + cdTheta S l (cdCode S l) ≤ cdR S l := rlk_ge l _

/-- **The bound clause from the reading**: `y ≤ δ_μ + Θ_μ(m_μ)` gives `y ≤ r(μ)`. -/
theorem rlBound_of_theta {S : InaccSeq.{0}} {μ y : Ordinal.{0}}
    (h : y ≤ cdDelta μ + cdTheta S μ (cdCode S μ)) : y ≤ cdR S μ :=
  h.trans (rlR_ge S μ)

/-- **Order type by an embedding.** -/
theorem rlOtp_ge_embed {C : Set Ordinal.{0}} {x m : Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}}
    (hf : StrictMonoOn f (Iio x)) (hC : ∀ z < x, f z ∈ C) (hm : ∀ z < x, f z < m) :
    x ≤ cdOtp C m := by
  have key : ∀ z < x, z ≤ cdOtp C (f z) := by
    intro z
    induction z using WellFoundedLT.induction with
    | ind z IH =>
    intro hz
    refine le_of_forall_lt fun w hw => ?_
    have hwx : w < x := hw.trans hz
    exact (IH w hw hwx).trans_lt
      (cdOtp_lt_of_mem (hC w hwx) (hf (show w ∈ Iio x from hwx) (show z ∈ Iio x from hz) hw))
  exact le_of_forall_lt fun z hz => (key z hz).trans_lt (cdOtp_lt_of_mem (hC z hz) (hm z hz))

open Classical in
/-- **Superadditivity of the order type** along a set closed under `z ↦ e + z`. -/
theorem rlOtp_add_ge {C : Set Ordinal.{0}} {e : Ordinal.{0}} (he : ∀ z ∈ C, e + z ∈ C) :
    ∀ x, cdOtp C e + cdOtp C x ≤ cdOtp C (e + x) := by
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  refine le_of_forall_lt fun w hw => ?_
  rcases lt_or_ge w (cdOtp C e) with h | h
  · exact h.trans_le (cdOtp_mono C le_self_add)
  · obtain ⟨v, rfl⟩ := exists_add_of_le h
    have hv : v < cdOtp C x := (add_lt_add_iff_left _).1 hw
    rw [cdOtp_eq C x] at hv
    obtain ⟨z, hz⟩ := (Ordinal.lt_iSup_iff).1 hv
    split_ifs at hz with hzC
    · have hvz : v ≤ cdOtp C z.1 := Order.lt_add_one_iff.1 hz
      calc cdOtp C e + v ≤ cdOtp C e + cdOtp C z.1 := add_le_add_right hvz _
        _ ≤ cdOtp C (e + z.1) := IH z.1 z.2
        _ < cdOtp C (e + x) := cdOtp_lt_of_mem (he _ hzC) ((add_lt_add_iff_left e).2 z.2)
    · exact absurd hz (not_lt.2 zero_le)

/-- `min(c, ρ_λ) ≤ Θ_λ(c)`. -/
theorem rlTheta_ge_min (S : InaccSeq.{0}) (l c : Ordinal.{0}) : min c (upsilon l) ≤ cdTheta S l c := by
  rw [← cdTheta_small S (min_le_right c (upsilon l))]
  exact cdTheta_mono S l (min_le_left _ _)

/-- The hull is closed under `z ↦ Ω₁ + z`. -/
theorem rlHull_Om1_add (S : InaccSeq.{0}) (l : Ordinal.{0}) {z : Ordinal.{0}} (hz : z ∈ cdHull S l) :
    Om 1 + z ∈ cdHull S l :=
  CSet.add_mem (CSet.Om_mem (CSet.one_mem _ _)) hz

variable {S : InaccSeq.{0}}

/-- **`ρ_λ + Θ_λ(x) ≤ Θ_λ(Ω₁ + x)`** when `ρ_λ = P(η_λ)`. -/
theorem rlTheta_Om1_add {l : Ordinal.{0}} (hpv : Pv S (cdEta S l) = upsilon l) (x : Ordinal.{0}) :
    upsilon l + cdTheta S l x ≤ cdTheta S l (Om 1 + x) := by
  have h := rlOtp_add_ge (C := cdHull S l) (fun z hz => rlHull_Om1_add S l hz) x
  have e : cdOtp (cdHull S l) (Om 1) = upsilon l := cdTheta_Om1 hpv
  rw [e] at h
  exact h

/-- **`ρ_λ·n + Θ_λ(x) ≤ Θ_λ(Ω₁·n + x)`** when `ρ_λ = P(η_λ)`. -/
theorem rlTheta_Om1_mul {l : Ordinal.{0}} (hpv : Pv S (cdEta S l) = upsilon l) :
    ∀ (n : ℕ) (x : Ordinal.{0}),
      upsilon l * (n : Ordinal.{0}) + cdTheta S l x ≤ cdTheta S l (Om 1 * (n : Ordinal.{0}) + x)
  | 0, x => by simp
  | n + 1, x => by
    have h1 := rlTheta_Om1_mul hpv n (Om 1 + x)
    have h2 := rlTheta_Om1_add hpv x
    calc upsilon l * ((n + 1 : ℕ) : Ordinal.{0}) + cdTheta S l x
        = upsilon l * (n : Ordinal.{0}) + (upsilon l + cdTheta S l x) := by
          rw [Nat.cast_succ, mul_add_one, add_assoc]
      _ ≤ upsilon l * (n : Ordinal.{0}) + cdTheta S l (Om 1 + x) := add_le_add_right h2 _
      _ ≤ cdTheta S l (Om 1 * (n : Ordinal.{0}) + (Om 1 + x)) := h1
      _ = cdTheta S l (Om 1 * ((n + 1 : ℕ) : Ordinal.{0}) + x) := by
          rw [Nat.cast_succ, mul_add_one, add_assoc]

/-- **`δ_μ + (ρ_μ·n + Θ_μ(x)) ≤ r(μ)`** when `Ω₁·n + x ≤ m_μ` and `ρ_μ = P(η_μ)`. -/
theorem rlR_ge_Om1 {μ x : Ordinal.{0}} {n : ℕ} (hpv : Pv S (cdEta S μ) = upsilon μ)
    (hm : Om 1 * (n : Ordinal.{0}) + x ≤ cdCode S μ) :
    cdDelta μ + (upsilon μ * (n : Ordinal.{0}) + cdTheta S μ x) ≤ cdR S μ :=
  calc cdDelta μ + (upsilon μ * (n : Ordinal.{0}) + cdTheta S μ x)
      ≤ cdDelta μ + cdTheta S μ (cdCode S μ) :=
        add_le_add_right ((rlTheta_Om1_mul hpv n x).trans (cdTheta_mono S μ hm)) _
    _ ≤ cdR S μ := rlR_ge S μ

end Googology.Trans.PoR.InaccPsi.R2.Rl
