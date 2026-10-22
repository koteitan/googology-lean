import Googology.Trans.PoR.InaccPsi.R2.RcLow

/-!
# The supply is an order embedding of the closed points into the hull below the code

`ρ_μ = υ_μ`, `K_μ` the closed points (`Cd.cdK`), `r(μ) = k_μ(Θ_μ(m_μ))`, the hull `Cl(A_{η_μ}, ρ_μ)` (`Cd.cdHull`),
`Θ_μ(m) = otp(Cl(A_{η_μ}, ρ_μ) ∩ m)`, `otp(C ∩ X) = Cd.cdOtp C X`.

* `rgOtp_le_of_emb` (**an order embedding `f : C ∩ X → D ∩ m` gives `otp(C ∩ X) ≤ otp(D ∩ m)`**),
  `rgOtp_surj` (**every `p < otp(D ∩ m)` is `otp(D ∩ d)` for some `d ∈ D ∩ m`**), `rgEmb_of_otp_le` (the
  converse), `rgOtp_le_iff_emb` (**`otp(C ∩ X) ≤ otp(D ∩ m)` ⇔ an order embedding `C ∩ X → D ∩ m`**);
* `rgSupAt_iff_emb` (**`Ra.RaSupAt S a` ⇔ for every `γ < a` a Range restart `μ` with `γ < ρ_μ < a`,
  `ω^{Ω₁} ∣ η_μ` and an order embedding of `K_μ ∩ υ_{μ+γ}` into `Cl(A_{η_μ}, ρ_μ) ∩ m_μ`**, UNCONDITIONAL):
  a lower bound of the reading needs only the closed points below the target, not all of `υ_{μ+γ}`;
  `rgReadAt_emb` (`Rc.RcReadAt` is the case where all of `υ_{μ+γ}` is embedded).

No new axiom, no new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Rg

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

open Classical in
/-- **An order embedding `f : C ∩ X → D ∩ m` gives `otp(C ∩ X) ≤ otp(D ∩ m)`.** -/
theorem rgOtp_le_of_emb {C D : Set Ordinal.{0}} {X m : Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}}
    (hf : ∀ c ∈ C, ∀ c' ∈ C, c' < c → c < X → f c' < f c)
    (hD : ∀ c ∈ C, c < X → f c ∈ D ∧ f c < m) : cdOtp C X ≤ cdOtp D m := by
  have key : ∀ c, c ∈ C → c < X → cdOtp C c ≤ cdOtp D (f c) := by
    intro c
    induction c using WellFoundedLT.induction with
    | ind c IH =>
    intro hc hcX
    rw [cdOtp_eq C c]
    refine ciSup_le' fun c' => ?_
    split_ifs with h
    · have hc'X : c'.1 < X := c'.2.trans hcX
      exact Order.add_one_le_of_lt ((IH c'.1 c'.2 h hc'X).trans_lt
        (cdOtp_lt_of_mem (hD c'.1 h hc'X).1 (hf c hc c'.1 h c'.2 hcX)))
    · exact zero_le
  rw [cdOtp_eq C X]
  refine ciSup_le' fun c => ?_
  split_ifs with h
  · exact Order.add_one_le_of_lt ((key c.1 h c.2).trans_lt
      (cdOtp_lt_of_mem (hD c.1 h c.2).1 (hD c.1 h c.2).2))
  · exact zero_le

open Classical in
/-- **Every `p < otp(D ∩ m)` is `otp(D ∩ d)` for some `d ∈ D`, `d < m`.** -/
theorem rgOtp_surj (D : Set Ordinal.{0}) :
    ∀ m, ∀ p < cdOtp D m, ∃ d ∈ D, d < m ∧ cdOtp D d = p := by
  intro m
  induction m using WellFoundedLT.induction with
  | ind m IH =>
  intro p hp
  rw [cdOtp_eq] at hp
  obtain ⟨c, hc⟩ := exists_lt_of_lt_ciSup' hp
  split_ifs at hc with h
  · rcases (Order.lt_add_one_iff.1 hc).lt_or_eq with hlt | heq
    · obtain ⟨d, hd, hdc, he⟩ := IH c.1 c.2 p hlt
      exact ⟨d, hd, hdc.trans c.2, he⟩
    · exact ⟨c.1, h, c.2, heq.symm⟩
  · exact absurd hc (not_lt.2 zero_le)

/-- **The converse**: `otp(C ∩ X) ≤ otp(D ∩ m)` gives an order embedding `C ∩ X → D ∩ m`. -/
theorem rgEmb_of_otp_le {C D : Set Ordinal.{0}} {X m : Ordinal.{0}} (h : cdOtp C X ≤ cdOtp D m) :
    ∃ f : Ordinal.{0} → Ordinal.{0}, (∀ c ∈ C, ∀ c' ∈ C, c' < c → c < X → f c' < f c) ∧
      (∀ c ∈ C, c < X → f c ∈ D ∧ f c < m) := by
  classical
  have hex : ∀ c, c ∈ C ∧ c < X → ∃ d, d ∈ D ∧ d < m ∧ cdOtp D d = cdOtp C c := by
    intro c hc
    obtain ⟨d, hd, hdm, he⟩ := rgOtp_surj D m _ ((cdOtp_lt_of_mem hc.1 hc.2).trans_le h)
    exact ⟨d, hd, hdm, he⟩
  let f : Ordinal.{0} → Ordinal.{0} := fun c => if hc : c ∈ C ∧ c < X then (hex c hc).choose else 0
  have hspec : ∀ c (hc : c ∈ C ∧ c < X), f c ∈ D ∧ f c < m ∧ cdOtp D (f c) = cdOtp C c := by
    intro c hc
    have e : f c = (hex c hc).choose := dif_pos hc
    rw [e]; exact (hex c hc).choose_spec
  refine ⟨f, fun c hc c' hc' hcc hcX => ?_, fun c hc hcX => ⟨(hspec c ⟨hc, hcX⟩).1,
    (hspec c ⟨hc, hcX⟩).2.1⟩⟩
  have h1 := hspec c ⟨hc, hcX⟩
  have h2 := hspec c' ⟨hc', hcc.trans hcX⟩
  refine lt_of_not_ge fun hle => ?_
  have h3 := cdOtp_mono D hle
  rw [h1.2.2, h2.2.2] at h3
  exact absurd (cdOtp_lt_of_mem hc' hcc) (not_lt.2 h3)

/-- **`otp(C ∩ X) ≤ otp(D ∩ m)` ⇔ an order embedding `C ∩ X → D ∩ m`.** -/
theorem rgOtp_le_iff_emb {C D : Set Ordinal.{0}} {X m : Ordinal.{0}} :
    cdOtp C X ≤ cdOtp D m ↔ ∃ f : Ordinal.{0} → Ordinal.{0},
      (∀ c ∈ C, ∀ c' ∈ C, c' < c → c < X → f c' < f c) ∧ (∀ c ∈ C, c < X → f c ∈ D ∧ f c < m) :=
  ⟨rgEmb_of_otp_le, fun ⟨_, hf, hD⟩ => rgOtp_le_of_emb hf hD⟩

/-- **The supply as an order embedding of the closed points**: `Ra.RaSupAt S a` iff for every `γ < a` there
is a Range restart `μ` with `γ < ρ_μ < a`, `ω^{Ω₁} ∣ η_μ` and an order embedding of `K_μ ∩ υ_{μ+γ}` into
`Cl(A_{η_μ}, ρ_μ) ∩ m_μ`. -/
theorem rgSupAt_iff_emb (a : Ordinal.{0}) :
    Ra.RaSupAt S a ↔ ∀ γ < a, ∃ μ, CdRange S μ ∧ γ < upsilon μ ∧ upsilon μ < a ∧
      ω ^ Om 1 ∣ cdEta S μ ∧ ∃ f : Ordinal.{0} → Ordinal.{0},
        (∀ y ∈ cdK μ, ∀ y' ∈ cdK μ, y' < y → y < upsilon (μ + γ) → f y' < f y) ∧
        (∀ y ∈ cdK μ, y < upsilon (μ + γ) → f y ∈ cdHull S μ ∧ f y < cdCode S μ) := by
  rw [Rc.rcSupAt_iff_count]
  constructor
  · intro h γ hγ
    obtain ⟨μ, h1, h2, h3, h4, h5⟩ := h γ hγ
    exact ⟨μ, h1, h2, h3, h4, rgEmb_of_otp_le h5⟩
  · intro h γ hγ
    obtain ⟨μ, h1, h2, h3, h4, f, hf, hD⟩ := h γ hγ
    exact ⟨μ, h1, h2, h3, h4, rgOtp_le_of_emb hf hD⟩

/-- **`Rc.RcReadAt` is the embedding of all of `υ_{μ+γ}`**: `υ_{μ+γ} ≤ Θ_μ(m_μ)` iff an order embedding
`[0, υ_{μ+γ}) → Cl(A_{η_μ}, ρ_μ) ∩ m_μ` exists. -/
theorem rgReadAt_emb (μ X : Ordinal.{0}) :
    X ≤ cdTheta S μ (cdCode S μ) ↔ ∃ f : Ordinal.{0} → Ordinal.{0},
      (∀ y, ∀ y', y' < y → y < X → f y' < f y) ∧ (∀ y, y < X → f y ∈ cdHull S μ ∧ f y < cdCode S μ) := by
  have e : cdOtp Set.univ X = X := cdOtp_of_Iio _ X fun _ _ => Set.mem_univ _
  have h := rgOtp_le_iff_emb (C := Set.univ) (D := cdHull S μ) (X := X) (m := cdCode S μ)
  rw [e] at h
  unfold cdTheta
  rw [h]
  constructor
  · rintro ⟨f, hf, hD⟩
    exact ⟨f, fun y y' hy hyX => hf y (Set.mem_univ _) y' (Set.mem_univ _) hy hyX,
      fun y hy => hD y (Set.mem_univ _) hy⟩
  · rintro ⟨f, hf, hD⟩
    exact ⟨f, fun y _ y' _ hy hyX => hf y y' hy hyX, fun y _ hy => hD y hy⟩

end Googology.Trans.PoR.InaccPsi.R2.Rg
