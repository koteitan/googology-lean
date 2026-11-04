import Googology.Trans.PoR.InaccPsi.R2.ZhReal

/-!
# Zh: the carry of the inner reaches from short codes with dense closed points

The carry `Zh.ZhCarry S λ μ β` asks, at every inner restart `λ + γ` whose predicted reach is below the target,
a form `r(λ+γ) = υ_{λ+σ} + w` (`w < ρ_λ`) and `υ_{μ+σ} + w ≤ r(μ+γ)`.  For a short code it reduces to statements
on codes and closed points:

* `zhk_ge`: `δ_λ + p ≤ k_λ(p)` (the enumeration of closed points starts at `δ_λ`);
* `zhR_ge_code`: `δ_μ + c ≤ r(μ)` for every `c ≤ ρ_μ` with `c ≤ m_μ`;
* `zhCarry_short` (**the short inner carry**): if the code `c = m_{λ+γ}` is below `ρ_λ` and `ρ_μ`, the points
  `δ_{λ+γ} + x` (`x ≤ c`) are closed for `λ + γ` and `c ≤ m_{μ+γ}`, then `r(λ+γ) = υ_{λ+(γ+ω+1)} + c` and
  `υ_{μ+(γ+ω+1)} + c ≤ r(μ+γ)`;
* `ZhInnerShort`, `zhCarry_of` (**the carry from the short inner data**): `ZhCarry` from the short inner data
  at the inner restarts with `r(λ+γ) < υ_{λ+β}` and the covering clause at the others;
* `zhDense` (**the closed points `δ_λ + x`, `x < δ_λ`, below `ν_C`**): every `α ∈ (ρ_λ, δ_λ]` has its reach in the
  block 0 (top `δ_λ`), every `α ∈ (δ_λ, δ_λ·2)` is `≤₁` no larger point (its `≤₁` is that of `R₁⁺` in the block 1,
  and `α` is no limit of additive principal numbers above `δ_λ`, [W07b] §2 via `R2.le1R_lim_P`);
* `zhCarry_of_codes` (**the carry from the inner codes alone**): if every inner code `m_{λ+γ}` is below `ρ_λ`
  and `ρ_μ` and at most `m_{μ+γ}`, then `ZhCarry S λ μ β` (`υ_{λ+β} ≤ ν_C`); the covering clause is automatic.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Zh

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- **`δ_λ + p ≤ k_λ(p)`.** -/
theorem zhk_ge (l : Ordinal.{0}) : ∀ p, cdDelta l + p ≤ cdk l p := by
  intro p
  induction p using WellFoundedLT.induction with
  | ind p IH =>
  refine le_of_forall_lt fun x hx => ?_
  rcases lt_or_ge x (cdDelta l) with h | h
  · exact lt_of_lt_of_le h (cdk_ge l p)
  · obtain ⟨q, rfl⟩ := exists_add_of_le h
    have hq : q < p := (add_lt_add_iff_left _).1 hx
    exact lt_of_le_of_lt (IH q hq) (cdk_strictMono l hq)

/-- **`δ_μ + c ≤ r(μ)`** for a code `c ≤ m_μ` with `c ≤ ρ_μ`. -/
theorem zhR_ge_code {μ c : Ordinal.{0}} (hc : c ≤ upsilon μ) (hcm : c ≤ cdCode S μ) :
    cdDelta μ + c ≤ cdR S μ := by
  have h1 : c ≤ cdTheta S μ (cdCode S μ) := by
    calc c = cdTheta S μ c := (cdTheta_small S hc).symm
      _ ≤ _ := cdTheta_mono S μ hcm
  exact (add_le_add le_rfl h1).trans (zhk_ge μ _)

/-- **The short inner carry.** -/
theorem zhCarry_short {l μ γ : Ordinal.{0}} (hc : cdCode S (l + γ) ≤ upsilon (l + γ))
    (hK : ∀ x ≤ cdCode S (l + γ), cdDelta (l + γ) + x ∈ cdK (l + γ))
    (hcμ : cdCode S (l + γ) ≤ upsilon (μ + γ)) (hcm : cdCode S (l + γ) ≤ cdCode S (μ + γ)) :
    cdR S (l + γ) = upsilon (l + (γ + ω + 1)) + cdCode S (l + γ) ∧
      upsilon (μ + (γ + ω + 1)) + cdCode S (l + γ) ≤ cdR S (μ + γ) := by
  refine ⟨?_, ?_⟩
  · rw [cdR_short hc hK]
    unfold cdDelta
    simp only [add_assoc]
  · have := zhR_ge_code (S := S) hcμ hcm
    unfold cdDelta at this
    simpa only [add_assoc] using this

/-- **The short inner data** at the inner restarts below the target. -/
def ZhInnerShort (S : InaccSeq.{0}) (l μ β : Ordinal.{0}) : Prop :=
  ∀ γ, 0 < γ → ω ^ 2 ∣ γ → γ < β → cdR S (l + γ) < upsilon (l + β) →
    cdCode S (l + γ) < upsilon l ∧ cdCode S (l + γ) ≤ upsilon μ ∧
    (∀ x ≤ cdCode S (l + γ), cdDelta (l + γ) + x ∈ cdK (l + γ)) ∧
    cdCode S (l + γ) ≤ cdCode S (μ + γ)

/-- **The carry from the short inner data and the covering clause.** -/
theorem zhCarry_of {l μ β : Ordinal.{0}} (hsh : ZhInnerShort S l μ β)
    (hbig : ∀ γ, 0 < γ → ω ^ 2 ∣ γ → γ < β → upsilon (l + β) ≤ cdR S (l + γ) →
      upsilon (μ + β) ≤ cdR S (μ + γ)) : ZhCarry S l μ β := by
  intro γ hγ0 hγd hγβ
  refine ⟨hbig γ hγ0 hγd hγβ, fun hlt => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hsh γ hγ0 hγd hγβ hlt
  have hm := upsilon_normal.strictMono.monotone
  have hc : cdCode S (l + γ) ≤ upsilon (l + γ) := h1.le.trans (hm le_self_add)
  have hcμ : cdCode S (l + γ) ≤ upsilon (μ + γ) := h2.trans (hm le_self_add)
  obtain ⟨e1, e2⟩ := zhCarry_short hc h3 hcμ h4
  exact ⟨γ + ω + 1, cdCode S (l + γ), h1, e1, e2⟩

/-- The blocks of a restart region below `ν_C` lie below `ν_C`. -/
theorem zh_blk {L : Ordinal.{0}} (hL : IsRestartIdx L) (hLν : upsilon L < nuC) (j : ℕ) :
    upsilon (L + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1) < nuC := by
  have hm := upsilon_normal.strictMono
  obtain ⟨ξ, hξ, hνe⟩ := nuC_restart
  rw [hνe] at hLν ⊢
  have hLξ := hm.lt_iff_lt.1 hLν
  have h2 := Lr.lr_dvd_add_le hL.2 hξ.2 hLξ
  refine hm (lt_of_lt_of_le ?_ h2)
  rw [add_assoc]; exact Lr.lr_addL (a := L) (Lr.lr_omega_mul_add_one_lt (j + 1))

/-- **The points `δ_λ + x` (`x < δ_λ`) are closed for `λ`** when `ρ_λ < ν_C`. -/
theorem zhDense {L x : Ordinal.{0}} (hL : IsRestartIdx L) (hLν : upsilon L < nuC)
    (hx : x < cdDelta L) : cdDelta L + x ∈ cdK L := by
  have hm := upsilon_normal.strictMono
  have e0 : upsilon (L + ω * ((0 + 1 : ℕ) : Ordinal.{0}) + 1) = cdDelta L := by
    unfold cdDelta; simp
  have hbot : upsilon (botI L 1) = cdDelta L := by
    unfold cdDelta; simp [botI]
  have hC0 := zh_blk hL hLν 0
  have hC1 := zh_blk hL hLν 1
  have htop : cdDelta L + cdDelta L < upsilon (L + ω * ((1 + 1 : ℕ) : Ordinal.{0}) + 1) := by
    have hlt : L + ω + 1 < L + ω * ((1 + 1 : ℕ) : Ordinal.{0}) + 1 := by
      have e : ω * ((1 + 1 : ℕ) : Ordinal.{0}) = ω + ω := by
        rw [Nat.cast_add, Nat.cast_one, mul_add, mul_one]
      rw [e, add_assoc L ω 1, add_assoc L (ω + ω) 1, add_assoc ω ω 1]
      exact Lr.lr_addL (a := L) (Lr.lr_addL (a := ω) (lt_of_lt_of_le one_lt_omega0 le_self_add))
    have hu := indec_of_upsPt (upsPt_upsilon (lt_of_le_of_lt zero_le hlt))
    have hδu : cdDelta L < upsilon (L + ω * ((1 + 1 : ℕ) : Ordinal.{0}) + 1) := hm hlt
    exact hu.add_lt hδu hδu
  refine Or.inl ⟨le_self_add, fun a ha hay g hag => ?_⟩
  rcases le_or_gt a (cdDelta L) with haδ | hδa
  · have hb := (block_le1 (Or.inr hL) 0 hC0 (by simpa [botI] using ha) (by rw [e0]; exact haδ) g).1 hag
    rw [e0] at hb
    exact hb.1.trans le_self_add
  · have ha2 : a ≤ upsilon (L + ω * ((1 + 1 : ℕ) : Ordinal.{0}) + 1) :=
      hay.trans ((add_le_add le_rfl hx.le).trans htop.le)
    have hb := (block_le1 (Or.inr hL) 1 hC1 (hbot ▸ hδa) ha2 g).1 hag
    rcases le_or_gt g a with hga | hag'
    · exact hga.trans hay
    · exfalso
      obtain ⟨-, hp⟩ := le1R_lim_P hb.2 hag'
      obtain ⟨p, hδp, hpa, hpI⟩ := hp (cdDelta L) hδa
      have h1 := hpI.add_lt hδp hδp
      have h2 : a < cdDelta L + cdDelta L := lt_of_le_of_lt hay (Lr.lr_addL (a := cdDelta L) hx)
      exact lt_irrefl _ ((h1.trans hpa).trans h2)

/-- **The carry from the inner codes alone.** -/
theorem zhCarry_of_codes {l μ β : Ordinal.{0}} (hl : IsRestartIdx l) (hνβ : upsilon (l + β) ≤ nuC)
    (hcodes : ∀ γ, 0 < γ → ω ^ 2 ∣ γ → γ < β →
      cdCode S (l + γ) < upsilon l ∧ cdCode S (l + γ) ≤ upsilon μ ∧ cdCode S (l + γ) ≤ cdCode S (μ + γ)) :
    ZhCarry S l μ β := by
  intro γ hγ0 hγd hγβ
  obtain ⟨h1, h2, h3⟩ := hcodes γ hγ0 hγd hγβ
  have hm := upsilon_normal.strictMono
  have hri := zh_ri_add hl hγd
  have hγν : upsilon (l + γ) < nuC := (hm (Lr.lr_addL (a := l) hγβ)).trans_le hνβ
  have hlδ : upsilon l < cdDelta (l + γ) := (hm.monotone le_self_add).trans_lt (cdRho_lt_delta _)
  have hK : ∀ x ≤ cdCode S (l + γ), cdDelta (l + γ) + x ∈ cdK (l + γ) := fun x hx =>
    zhDense hri hγν (lt_of_le_of_lt hx (h1.trans hlδ))
  have hc : cdCode S (l + γ) ≤ upsilon (l + γ) := h1.le.trans (hm.monotone le_self_add)
  have hcμ : cdCode S (l + γ) ≤ upsilon (μ + γ) := h2.trans (hm.monotone le_self_add)
  obtain ⟨e1, e2⟩ := zhCarry_short hc hK hcμ h3
  refine ⟨fun hbig => ?_, fun _ => ⟨γ + ω + 1, cdCode S (l + γ), h1, e1, e2⟩⟩
  have hlt : cdR S (l + γ) < upsilon (l + succ (γ + ω + 1)) := by
    rw [e1, ← Lr.lr_succ_add]
    have hI := indec_of_upsPt (upsPt_upsilon (lt_of_le_of_lt zero_le (lt_succ (l + (γ + ω + 1)))))
    exact hI.add_lt (hm (lt_succ _)) (h1.trans (hm (lt_of_le_of_lt le_self_add (lt_succ _))))
  have hβ : β ≤ γ + ω + 1 := by
    by_contra h
    have := hm.monotone (Lr.lr_addLe (a := l) (Order.succ_le_of_lt (not_le.1 h)))
    exact lt_irrefl _ (lt_of_le_of_lt hbig (hlt.trans_le this))
  calc upsilon (μ + β) ≤ upsilon (μ + (γ + ω + 1)) := hm.monotone (Lr.lr_addLe (a := μ) hβ)
    _ = cdDelta (μ + γ) := by unfold cdDelta; simp only [add_assoc]
    _ ≤ cdR S (μ + γ) := cdR_ge S _

/-- **The supply with small inner codes** (the carry is then `zhCarry_of_codes`). -/
def ZhSupCode (S : InaccSeq.{0}) (l β : Ordinal.{0}) : Prop :=
  ∀ x < upsilon l, ∃ μ, CdRange S μ ∧ x < upsilon μ ∧ upsilon μ < upsilon l ∧ μ + β ≤ l ∧
    upsilon (μ + β) ≤ cdR S μ ∧
    ∀ γ, 0 < γ → ω ^ 2 ∣ γ → γ < β →
      cdCode S (l + γ) < upsilon l ∧ cdCode S (l + γ) ≤ upsilon μ ∧ cdCode S (l + γ) ≤ cdCode S (μ + γ)

/-- **The supply bound from the reading**: `δ_μ + Θ_μ(m_μ) ≤ r(μ)`, so `Θ_μ(m_μ) ≥ υ_{μ+β}` gives
`υ_{μ+β} ≤ r(μ)`. -/
theorem zhR_ge_theta (μ : Ordinal.{0}) : cdDelta μ + cdTheta S μ (cdCode S μ) ≤ cdR S μ :=
  zhk_ge μ _

theorem zhSup_of_theta {μ β : Ordinal.{0}} (h : upsilon (μ + β) ≤ cdTheta S μ (cdCode S μ)) :
    upsilon (μ + β) ≤ cdR S μ :=
  (h.trans le_add_self).trans (zhR_ge_theta μ)

/-- **The short value at every restart below `ν_C`**: a code `m_λ ≤ ρ_λ` gives `r(λ) = δ_λ + m_λ`. -/
theorem zhR_short_all {l : Ordinal.{0}} (hl : IsRestartIdx l) (hν : upsilon l < nuC)
    (hc : cdCode S l ≤ upsilon l) : cdR S l = cdDelta l + cdCode S l :=
  cdR_short hc fun _ hx => zhDense hl hν (lt_of_le_of_lt hx (hc.trans_lt (cdRho_lt_delta l)))

/-- **A supply restart has a code above `ρ_λ`**: `υ_{λ+ω²} ≤ r(λ)` and `ρ_λ < ν_C` give `ρ_λ < m_λ`. -/
theorem zhLong_code {l : Ordinal.{0}} (hl : IsRestartIdx l) (hν : upsilon l < nuC)
    (hlong : upsilon (l + ω ^ 2) ≤ cdR S l) : upsilon l < cdCode S l := by
  by_contra hc
  have hc' : cdCode S l ≤ upsilon l := not_lt.1 hc
  have hm := upsilon_normal.strictMono
  rw [zhR_short_all hl hν hc'] at hlong
  have hlt : l + ω + 1 < l + ω ^ 2 := by
    rw [add_assoc]; exact Lr.lr_addL (a := l) (by simpa using Lr.lr_omega_mul_add_one_lt 1)
  have hI := indec_of_upsPt (upsPt_upsilon (lt_of_le_of_lt zero_le hlt))
  have h1 : cdDelta l < upsilon (l + ω ^ 2) := hm hlt
  have h2 : cdCode S l < upsilon (l + ω ^ 2) := hc'.trans_lt (h1.trans' (cdRho_lt_delta l))
  exact absurd hlong (not_le.2 (hI.add_lt h1 h2))

end Googology.Trans.PoR.InaccPsi.R2.Zh
