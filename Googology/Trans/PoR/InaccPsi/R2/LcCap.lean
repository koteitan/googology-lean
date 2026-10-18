import Googology.Trans.PoR.InaccPsi.R2.RlBound

/-!
# The collapse bound LC-STRICT: its statement, the cap of the reading at the π-code, and what it gives

`Θ_λ(m)` (`Cd.cdTheta`) is the order type of `Cl(A_{η_λ}, ρ_λ) ∩ m` (`Cd.cdHull`), `A_η = Ω_ω + θ·η`,
`ρ_λ = υ_λ`, `π_η = ψ_{Ω₂}(A_η)` (`Cd.cdPi`), `H(η) = P(η) = ψ_{Ω₁}(A_η)` (`Nm.Pv`), `r(λ) = k_λ(Θ_λ(m_λ))`.
The docs' notation: `θ_k = ψ_{Ω_{k+1}}(Ω_ω)` (`lcTh`, so `θ_1 = θ`), `G(ζ) = ψ_{Ω₂}(Ω_ω + θ_2·ζ)` (`lcG`).

* `LcStrictAt S λ k` (**LC-STRICT at `λ`, `k`**, a proposition): `H(η_λ + G(θ_k·ω²)) ≤ Θ_λ(G(θ_{k+1}·ω²))`;
* `lcHull_lt_pi` (**the hull below `Ω₂` lies below the π-code**): `Cl(A_η, ρ) ∩ Ω₂ ⊆ π_η` for `ρ < Ω₁`
  (`Cl(A, ρ) ⊆ Cl(A, ψ_{Ω₂}(A))`, whose part below `Ω₂` is below `ψ_{Ω₂}(A)`, F4);
* `lcTheta_cap` (**`Θ_λ` is constant on `[π_{η_λ}, Ω₂]`**), `lcTheta_le_cap` (`Θ_λ(c) ≤ Θ_λ(π_{η_λ})` for
  `c ≤ Ω₂`); so LC-STRICT at `λ` only reads the hull below `min(G(θ_{k+1}·ω²), π_{η_λ})`
  (`lcStrict_cap`, `lcStrict_needs`: it implies `H(η_λ + G(θ_k·ω²)) ≤ Θ_λ(π_{η_λ})`);
* `lcStrict_of_embed` (**LC-STRICT from an order embedding** of `[0, H(η_λ + G(θ_k·ω²)))` into the hull
  below `G(θ_{k+1}·ω²)`, `Rl.rlOtp_ge_embed`): the map that LC-STRICT needs;
* `lcR_of_strict` (**clause (ii) of the realizer maps from LC-STRICT**): if `m_λ ≥ G(θ_{k+1}·ω²)`, every
  `y ≤ δ_λ + H(η_λ + G(θ_k·ω²))` is at most `r(λ)`.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Lc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Nm

variable {S : InaccSeq.{0}}

/-- `θ_k = ψ_{Ω_{k+1}}(Ω_ω)`. -/
noncomputable def lcTh (S : InaccSeq.{0}) (k : ℕ) : Ordinal.{0} := S.psi (Om ω) (Om ((k : Ordinal.{0}) + 1))

/-- `G(ζ) = ψ_{Ω₂}(Ω_ω + θ_2·ζ)`. -/
noncomputable def lcG (S : InaccSeq.{0}) (ζ : Ordinal.{0}) : Ordinal.{0} :=
  S.psi (Om ω + lcTh S 2 * ζ) (Om (1 + 1))

/-- **LC-STRICT at `λ`, `k`**: `H(η_λ + G(θ_k·ω²)) ≤ Θ_λ(G(θ_{k+1}·ω²))`. -/
def LcStrictAt (S : InaccSeq.{0}) (l : Ordinal.{0}) (k : ℕ) : Prop :=
  Pv S (cdEta S l + lcG S (lcTh S k * ω ^ 2)) ≤ cdTheta S l (lcG S (lcTh S (k + 1) * ω ^ 2))

theorem lcTh_one (S : InaccSeq.{0}) : lcTh S 1 = ConjT.th S := by
  unfold lcTh ConjT.th; rw [Nat.cast_one]

theorem lcG_lt_Om2 (ζ : Ordinal.{0}) : lcG S ζ < Om (1 + 1) := psi_lt (InR_Om_succ 1) _

/-- **The hull below `Ω₂` lies below the π-code.** -/
theorem lcHull_lt_pi {l x : Ordinal.{0}} (hρ : upsilon l < Om 1) (hx : x ∈ cdHull S l)
    (hx2 : x < Om (1 + 1)) : x < cdPi S (cdEta S l) := by
  have hle : upsilon l ≤ cdPi S (cdEta S l) := (hρ.trans (psiS_bounds _ 1).1).le
  have hx' : x ∈ S.CSet (ConjT.Aη S (cdEta S l)) (S.psi (ConjT.Aη S (cdEta S l)) (Om (1 + 1))) :=
    CSet_mono le_rfl hle hx
  exact lt_psi_of_mem (InR_Om_succ 1) hx' hx2

/-- `cdOtp C` is constant across a gap of `C`. -/
theorem lcOtp_const {C : Set Ordinal.{0}} {m m' : Ordinal.{0}} (hmm : m ≤ m')
    (h : ∀ x, m ≤ x → x < m' → x ∉ C) : cdOtp C m' = cdOtp C m := by
  classical
  refine le_antisymm ?_ (cdOtp_mono C hmm)
  rw [cdOtp_eq C m']
  refine ciSup_le' fun c => ?_
  split_ifs with hc
  · have hcm : c.1 < m := by
      by_contra hge
      exact h c.1 (not_lt.1 hge) c.2 hc
    exact Order.add_one_le_of_lt (cdOtp_lt_of_mem hc hcm)
  · exact zero_le

/-- **`Θ_λ` is constant on `[π_{η_λ}, Ω₂]`.** -/
theorem lcTheta_cap {l c : Ordinal.{0}} (hρ : upsilon l < Om 1) (hc1 : cdPi S (cdEta S l) ≤ c)
    (hc2 : c ≤ Om (1 + 1)) : cdTheta S l c = cdTheta S l (cdPi S (cdEta S l)) :=
  lcOtp_const hc1 fun _ hx1 hx2 hxC =>
    absurd (lcHull_lt_pi hρ hxC (lt_of_lt_of_le hx2 hc2)) (not_lt.2 hx1)

/-- `Θ_λ(c) ≤ Θ_λ(π_{η_λ})` for `c ≤ Ω₂`. -/
theorem lcTheta_le_cap {l c : Ordinal.{0}} (hρ : upsilon l < Om 1) (hc2 : c ≤ Om (1 + 1)) :
    cdTheta S l c ≤ cdTheta S l (cdPi S (cdEta S l)) := by
  rcases le_total c (cdPi S (cdEta S l)) with h | h
  · exact cdTheta_mono S l h
  · exact (lcTheta_cap hρ h hc2).le

/-- **LC-STRICT only reads the hull below `min(G(θ_{k+1}·ω²), π_{η_λ})`.** -/
theorem lcStrict_cap {l : Ordinal.{0}} (hρ : upsilon l < Om 1) (k : ℕ) :
    LcStrictAt S l k ↔ Pv S (cdEta S l + lcG S (lcTh S k * ω ^ 2)) ≤
      cdTheta S l (min (lcG S (lcTh S (k + 1) * ω ^ 2)) (cdPi S (cdEta S l))) := by
  unfold LcStrictAt
  rcases le_total (lcG S (lcTh S (k + 1) * ω ^ 2)) (cdPi S (cdEta S l)) with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h, lcTheta_cap hρ h (lcG_lt_Om2 _).le]

/-- **What LC-STRICT needs**: `H(η_λ + G(θ_k·ω²)) ≤ Θ_λ(π_{η_λ}) = otp(Cl(A_{η_λ}, ρ_λ) ∩ Ω₂)`. -/
theorem lcStrict_needs {l : Ordinal.{0}} (hρ : upsilon l < Om 1) {k : ℕ} (h : LcStrictAt S l k) :
    Pv S (cdEta S l + lcG S (lcTh S k * ω ^ 2)) ≤ cdTheta S l (cdPi S (cdEta S l)) :=
  h.trans (lcTheta_le_cap hρ (lcG_lt_Om2 _).le)

/-- **LC-STRICT from an order embedding** of `[0, H(η_λ + G(θ_k·ω²)))` into the hull below
`G(θ_{k+1}·ω²)`. -/
theorem lcStrict_of_embed {l : Ordinal.{0}} {k : ℕ} {f : Ordinal.{0} → Ordinal.{0}}
    (hf : StrictMonoOn f (Iio (Pv S (cdEta S l + lcG S (lcTh S k * ω ^ 2)))))
    (hC : ∀ z < Pv S (cdEta S l + lcG S (lcTh S k * ω ^ 2)), f z ∈ cdHull S l)
    (hm : ∀ z < Pv S (cdEta S l + lcG S (lcTh S k * ω ^ 2)), f z < lcG S (lcTh S (k + 1) * ω ^ 2)) :
    LcStrictAt S l k :=
  Rl.rlOtp_ge_embed hf hC hm

/-- **Clause (ii) of the realizer maps from LC-STRICT**: with `m_λ ≥ G(θ_{k+1}·ω²)`, every
`y ≤ δ_λ + H(η_λ + G(θ_k·ω²))` is at most `r(λ)`. -/
theorem lcR_of_strict {l : Ordinal.{0}} {k : ℕ} (h : LcStrictAt S l k)
    (hm : lcG S (lcTh S (k + 1) * ω ^ 2) ≤ cdCode S l) {y : Ordinal.{0}}
    (hy : y ≤ cdDelta l + Pv S (cdEta S l + lcG S (lcTh S k * ω ^ 2))) : y ≤ cdR S l :=
  Rl.rlBound_of_theta (hy.trans (add_le_add le_rfl (h.trans (cdTheta_mono S l hm))))

end Googology.Trans.PoR.InaccPsi.R2.Lc
