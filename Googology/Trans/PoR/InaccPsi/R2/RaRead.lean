import Googology.Trans.PoR.InaccPsi.R2.LsRoadR

/-!
# The supply at the family `m_μ = G_{k+1} + 1` is a statement about the reading `Θ_μ(G_{k+1})` alone

`G_k = G(θ_k·ω²)` (`Ls.lsG`), `G' = G_{k+1}`, `ρ_μ = υ_μ`, `δ_μ = υ_{μ+ω+1}`, `r(μ) = k_μ(Θ_μ(m_μ))`.  The supply
`Ls.LsSupCode S k` asks `υ_{μ+ρ_μ} ≤ r(μ)` at every Range restart `μ` with `m_μ = G' + 1`.

* `raK_ge_add` (**`δ_λ + p ≤ k_λ(p)`**: the enumeration of the closed points starts at `δ_λ` and is strictly
  increasing), `raR_ge_add` (**`δ_λ + Θ_λ(m_λ) ≤ r(λ)`**);
* `RaSupRead S k` (**the reading form of the supply**: `υ_{μ+ρ_μ} ≤ Θ_μ(G')` at the family),
  `raSupCode_of_read` (**`RaSupRead → LsSupCode`**), `raRead_of_strict` (**LC-STRICT at the family gives
  `RaSupRead`**: `υ_{μ+ρ_μ} = P(η_μ + ρ_μ) ≤ H(η_μ + G_k) ≤ Θ_μ(G')`);
* `raUps_le_iff` (`υ_{μ+ρ} ≤ X ⇔ υ_{μ+ν} < X` for all `ν < ρ`, `ρ = υ_μ` a limit), `RaGammaSup S k`
  (**the `Γ`-form**: `υ_{μ+ν} < Γ(ξ₀ + 1 + τ_μ(G'))` for every `ν < ρ_μ = Γ(ξ₀)`, `τ_μ(G')` the order type of the
  `ψ_{Ω₂}`-atoms of the hull below `G'`), `raRead_iff_gamma` (**`RaSupRead ↔ RaGammaSup`**);
* `raRead_route` (**with `A_{η_μ}` own, every hull code `c < θ·γ` reads below `υ_{μ+γ}`**, `γ ≤ ρ_μ`),
  `raR_low` (**`Θ_λ(m_λ) < δ_λ` gives `r(λ) = δ_λ + Θ_λ(m_λ)`**), `raSup_needs_delta` (**`υ_{μ+ω+2} ≤ r(μ)` forces
  `δ_μ ≤ Θ_μ(m_μ)`**): the supply beyond the first block must read a code `≥ θ·(ω+1)`;
* `raPsi_le_gamma` (**`ψ_{Ω₁}(A + ζ) ≤ Γ(ξ₀ + 1 + ζ)` for every `ζ`** when `ψ_{Ω₁}(A) = Γ(ξ₀)`): the level-1 count
  of a collapse is at most its offset; with `raRead_iff_gamma` the supply asks the converse direction, a lower bound
  of the level-2 atom count `τ_μ(G')` by the restarts `υ_{μ+ν}`, `ν < ρ_μ`.

No new axiom.  New definitions: `RaSupRead`, `RaGammaSup`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ra

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- **`δ_λ + p ≤ k_λ(p)`.** -/
theorem raK_ge_add (l : Ordinal.{0}) : ∀ p, cdDelta l + p ≤ cdk l p := by
  intro p
  induction p using WellFoundedLT.induction with
  | ind p IH =>
  refine le_of_forall_lt fun x hx => ?_
  rcases lt_or_ge x (cdDelta l) with h | h
  · exact h.trans_le (cdk_ge l p)
  · obtain ⟨q, rfl⟩ := exists_add_of_le h
    have hq : q < p := (add_lt_add_iff_left _).1 hx
    exact (IH q hq).trans_lt (cdk_strictMono l hq)

/-- **`δ_λ + Θ_λ(m_λ) ≤ r(λ)`.** -/
theorem raR_ge_add (S : InaccSeq.{0}) (l : Ordinal.{0}) :
    cdDelta l + cdTheta S l (cdCode S l) ≤ cdR S l := by
  unfold cdR cdRc
  exact raK_ge_add l _

/-- **The reading form of the supply**: `υ_{μ+ρ_μ} ≤ Θ_μ(G_{k+1})` at every Range restart with the code
`G_{k+1} + 1`. -/
def RaSupRead (S : InaccSeq.{0}) (k : ℕ) : Prop :=
  ∀ μ, CdRange S μ → cdCode S μ = Ls.lsG S (k + 1) + 1 →
    upsilon (μ + upsilon μ) ≤ cdTheta S μ (Ls.lsG S (k + 1))

/-- **`RaSupRead → LsSupCode`**: `υ_{μ+ρ_μ} ≤ Θ_μ(G') ≤ Θ_μ(G'+1) ≤ δ_μ + Θ_μ(m_μ) ≤ r(μ)`. -/
theorem raSupCode_of_read {k : ℕ} (h : RaSupRead S k) : Ls.LsSupCode S k := by
  intro μ hR hc
  refine (h μ hR hc).trans ?_
  refine (cdTheta_mono S μ (le_self_add : Ls.lsG S (k + 1) ≤ Ls.lsG S (k + 1) + 1)).trans ?_
  rw [← hc]
  exact le_add_self.trans (raR_ge_add S μ)

/-- The name data of a Range restart. -/
theorem raName {μ : Ordinal.{0}} (hR : CdRange S μ) :
    Bt.Good S (cdEta S μ) ∧ Bt.iota S (cdEta S μ) = μ ∧ Nm.Pv S (cdEta S μ) = upsilon μ := by
  obtain ⟨hgμ, hιμ, -⟩ := cdEta_spec (S := S) (Order.one_le_iff_ne_zero.2 hR.1.1)
    (cd_lt_iota (η0 := Om ω + Nc.ncPp S * (ω + 1)) (by rw [← Lw.lw_L_eq]; exact hR.2.2.1))
  exact ⟨hgμ, hιμ, Ls.lsPv_range hR⟩

/-- `υ_{μ+g} = P(η_μ + g)` for `g ≤ ρ_μ` at a Range restart. -/
theorem raUps_shift {μ g : Ordinal.{0}} (hR : CdRange S μ) (hg : g ≤ upsilon μ) :
    upsilon (μ + g) = Nm.Pv S (cdEta S μ + g) := by
  obtain ⟨hgμ, hιμ, hpv⟩ := raName hR
  have hsh := Rz.rz_iota_shift hgμ (show g ≤ Nm.Pv S (cdEta S μ) by rw [hpv]; exact hg)
  rw [hιμ] at hsh
  rw [← hsh, Bt.ups_iota]

/-- **LC-STRICT at the family gives the reading form of the supply.** -/
theorem raRead_of_strict {k : ℕ} (h : Ls.LsStrictCode S k) : RaSupRead S k := by
  intro μ hR hc
  have hpv := Ls.lsPv_range hR
  have hs := h μ hR hc
  unfold Lc.LcStrictAt at hs
  rw [raUps_shift hR le_rfl]
  refine (Nm.Pv_mono (add_le_add le_rfl ?_)).trans hs
  have h1 : upsilon μ < Om 1 := by rw [← hpv]; exact Nm.Pv_lt_Om1 S _
  exact (h1.trans (Ls.lsG_Om1 (S := S) k)).le

/-- `υ_{μ+ρ} ≤ X ⇔ υ_{μ+ν} < X` for every `ν < ρ`, `ρ = υ_μ` a limit. -/
theorem raUps_le_iff {μ X : Ordinal.{0}} (hlim : IsSuccLimit (upsilon μ)) :
    upsilon (μ + upsilon μ) ≤ X ↔ ∀ ν < upsilon μ, upsilon (μ + ν) < X := by
  have hm := upsilon_normal.strictMono
  constructor
  · intro h ν hν
    exact (hm ((add_lt_add_iff_left μ).2 hν)).trans_le h
  · intro h
    refine le_of_forall_lt fun y hy => ?_
    obtain ⟨ζ, hζ, hyζ⟩ := (upsilon_normal.lt_iff_exists_lt (isSuccLimit_add μ hlim)).1 hy
    rcases lt_or_ge ζ μ with h1 | h1
    · have h0 : (0 : Ordinal.{0}) < upsilon μ := hlim.bot_lt
      refine hyζ.trans ((hm h1).trans_le ?_ |>.trans (h 0 h0))
      rw [add_zero]
    · obtain ⟨ν, rfl⟩ := exists_add_of_le h1
      exact hyζ.trans (h ν ((add_lt_add_iff_left μ).1 hζ))

/-- `ρ_μ` is a limit at a Range restart. -/
theorem raRho_lim {μ : Ordinal.{0}} (hR : CdRange S μ) : IsSuccLimit (upsilon μ) :=
  (Ls.lsRho_SC (Ls.lsPv_range hR)).isSuccLimit

/-- **The `Γ`-form of the supply**: at every Range restart with the code `G' + 1` and `ρ_μ = Γ(ξ₀)`, every
`υ_{μ+ν}` (`ν < ρ_μ`) is below `Γ(ξ₀ + 1 + τ_μ(G'))`. -/
def RaGammaSup (S : InaccSeq.{0}) (k : ℕ) : Prop :=
  ∀ μ, CdRange S μ → cdCode S μ = Ls.lsG S (k + 1) + 1 → ∀ ξ0, gamma ξ0 = upsilon μ →
    ∀ ν < upsilon μ, upsilon (μ + ν) <
      gamma (ξ0 + 1 + cdOtp (Ls.lsAt S (ConjT.Aη S (cdEta S μ)) (upsilon μ)) (Ls.lsG S (k + 1)))

/-- `Θ_μ(G') = Γ(ξ₀ + 1 + τ_μ(G'))` at a Range restart with `ρ_μ = Γ(ξ₀)`. -/
theorem raTheta_gamma {μ ξ0 : Ordinal.{0}} (hR : CdRange S μ) (hξ : gamma ξ0 = upsilon μ) (k : ℕ) :
    cdTheta S μ (Ls.lsG S k) =
      gamma (ξ0 + 1 + cdOtp (Ls.lsAt S (ConjT.Aη S (cdEta S μ)) (upsilon μ)) (Ls.lsG S k)) := by
  unfold cdTheta cdHull
  exact Ls.lsOtp_gamma (Ls.lsPv_range hR) hξ _ (Ls.lsG_SC _) (Ls.lsG_Om1 _) (Ls.lsG_Om2 _)

/-- **`RaSupRead ↔ RaGammaSup`.** -/
theorem raRead_iff_gamma {k : ℕ} : RaSupRead S k ↔ RaGammaSup S k := by
  constructor
  · intro h μ hR hc ξ0 hξ
    rw [← raTheta_gamma hR hξ]
    exact (raUps_le_iff (raRho_lim hR)).1 (h μ hR hc)
  · intro h μ hR hc
    obtain ⟨ξ0, hξ⟩ := Ls.lsGamma_idx (Ls.lsPv_range hR)
    rw [raTheta_gamma hR hξ]
    exact (raUps_le_iff (raRho_lim hR)).2 (h μ hR hc ξ0 hξ)

theorem raA_add (η γ : Ordinal.{0}) : ConjT.Aη S (η + γ) = ConjT.Aη S η + ConjT.th S * γ := by
  unfold ConjT.Aη; rw [mul_add, add_assoc]

/-- **The route check of the reading form**: with `A_{η_μ}` own, every code `c` of the hull below `θ·γ`
(`γ ≤ ρ_μ`) reads below `υ_{μ+γ}`; so a supply `υ_{μ+γ} ≤ Θ_μ(m)` through the reading needs a code
`m ≥ θ·γ` (by `Ls.lsOtp_le_psi`).  With `Θ_μ(m) < δ_μ` for `θ < m ≤ θ·ω` this is the region of codes that
the supply must read: `[θ·γ, G')`, beyond the explicit readings (below `G_2 < θ`). -/
theorem raRead_route {μ γ c : Ordinal.{0}} (hR : CdRange S μ) (hγ : γ ≤ upsilon μ)
    (hown : ConjT.Aη S (cdEta S μ) ∈ S.CSet (ConjT.Aη S (cdEta S μ)) (Nm.Pv S (cdEta S μ)))
    (hc : c ∈ cdHull S μ) (hcγ : c < ConjT.th S * γ) : cdTheta S μ c < upsilon (μ + γ) := by
  have hpv := Ls.lsPv_range hR
  set A := ConjT.Aη S (cdEta S μ) with hA
  have hown' : A ∈ S.CSet A (S.psi A (Om 1)) := hown
  rw [raUps_shift hR hγ]
  show cdTheta S μ c < S.psi (ConjT.Aη S (cdEta S μ + γ)) (Om 1)
  rw [raA_add]
  refine (Ls.lsTheta_le_psi hpv hown c).trans_lt ?_
  have hmon := psi_mono (S := S) Low.InR_Om_one (le_self_add : A ≤ A + ConjT.th S * γ)
  refine psi_lt_psi_of_mem Low.InR_Om_one ((add_lt_add_iff_left A).2 hcγ) ?_
  refine CSet.add_mem (hmon.2 hown') ?_
  have hρ : upsilon μ ≤ S.psi (A + ConjT.th S * γ) (Om 1) := by
    rw [← hpv]; exact hmon.1
  exact CSet_mono le_self_add hρ hc

/-- **A reading below `δ_λ` gives the reach `r(λ) = δ_λ + Θ_λ(m_λ)`** (first block below `ν_C`). -/
theorem raR_low {l : Ordinal.{0}} (hl : IsRestartIdx l) (hC : upsilon (l + ω + 1) < nuC)
    (hθ : cdTheta S l (cdCode S l) < cdDelta l) : cdR S l = cdDelta l + cdTheta S l (cdCode S l) := by
  unfold cdR cdRc
  exact cdk_interval (fun y hy => Or.inl (Ls.lsClosed hl hC (lt_of_le_of_lt hy hθ))) _ le_rfl

/-- **The supply beyond the first block needs a reading `≥ δ_μ`**: if `υ_{μ+ω+2} ≤ r(μ)` (first block below
`ν_C`) then `δ_μ ≤ Θ_μ(m_μ)`.  With `raRead_route` (own `A_{η_μ}`): every code of the hull below `θ·(ω+1)`
reads below `δ_μ`, so the code `m_μ` must lie in `[θ·(ω+1), Ω₂)` and be read there. -/
theorem raSup_needs_delta {l : Ordinal.{0}} (hl : IsRestartIdx l) (hC : upsilon (l + ω + 1) < nuC)
    (h : upsilon (l + (ω + 2)) ≤ cdR S l) : cdDelta l ≤ cdTheta S l (cdCode S l) := by
  by_contra hlt
  rw [not_le] at hlt
  rw [raR_low hl hC hlt] at h
  have hE : InE (upsilon (l + (ω + 2))) := upsPt_inE (upsPt_upsilon
    (omega0_pos.trans_le (le_self_add.trans le_add_self)))
  have hδ : cdDelta l < upsilon (l + (ω + 2)) := by
    unfold cdDelta
    refine upsilon_normal.strictMono ?_
    rw [add_assoc]
    exact (add_lt_add_iff_left l).2 ((add_lt_add_iff_left ω).2 one_lt_two)
  exact absurd (h.trans_lt (hE.add_lt hδ (hlt.trans hδ))) (lt_irrefl _)

/-- **`ψ_{Ω₁}(A + ζ) ≤ Γ(ξ₀ + 1 + ζ)`** for every `ζ`, when `ψ_{Ω₁}(A) = Γ(ξ₀)`. -/
theorem raPsi_le_gamma {A ξ0 : Ordinal.{0}} (hρ : S.psi A (Om 1) = gamma ξ0) :
    ∀ ζ, S.psi (A + ζ) (Om 1) ≤ gamma (ξ0 + 1 + ζ) := by
  intro ζ
  induction ζ using WellFoundedLT.induction with
  | ind ζ IH =>
  refine Ls.lsPsi_le (Ls.lsGamma_SC _) ?_ fun ζ' hζ' => ?_
  · rw [hρ]
    exact gamma_lt_gamma.2 ((lt_add_one ξ0).trans_le le_self_add)
  · exact (IH ζ' hζ').trans_lt (gamma_lt_gamma.2 ((add_lt_add_iff_left _).2 hζ'))

end Googology.Trans.PoR.InaccPsi.R2.Ra
