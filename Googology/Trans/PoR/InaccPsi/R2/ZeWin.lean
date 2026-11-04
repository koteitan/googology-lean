import Googology.Trans.PoR.InaccPsi.R2.CdLow
import Googology.Trans.PoR.InaccPsi.R2.HlU
import Googology.Trans.PoR.InaccPsi.R2.SkelC

/-!
# The cap window below a restart

Notation: `P(η) = Nm.Pv S η`, `ι = Bt.iota S`, `ρ_λ = υ_λ`, `η_λ = Cd.cdEta S λ` (the good name of a restart),
`e(η) = Cd.cdExp η` (the last exponent), the cap of a restart `cap(λ) = P(η_λ + ω^{e(η_λ)})` (`Cd.cdCapB`).

* `zeCap_win` (**the cap window**): for every restart index `κ` with `ρ_κ < L(ω+1)` there is `x < ρ_κ` such that
  every restart index `μ` with `x < ρ_μ < ρ_κ` has `cap(μ) ≤ ρ_κ`.  Proof (as in `Cd.cdLow`): `η_m` the least `η`
  with `ι(η) = κ`, `η_m = η₀ + ω^e` (`Cd.cdExp_decomp`); `ι(η₀) < κ`; `x = υ_{ι(η₀)}`; the good name of `μ`
  lies in `(η₀, η_m)`, so `η_μ + ω^{e(η_μ)} < η_m` (`Cd.cdWin`) and `cap(μ) ≤ P(η_m) = ρ_κ`.  No property of
  the good name of `κ` is used.
* `zeCapHigh`: the frontier hypothesis `hVt` of the road (CapV at every range restart in `(L(ω), L(ω+1))` above
  the frontier `F = ι(Γ(φ(Ω₁·Ω₁, G+1))·ω)`) gives CapV at every range restart in `(L(ω), L(ω+1))`
  (below `F` by `Hl.hlU_capV`).
* `zeReach_lt_cap`: CapV and the window give `r(μ) < ρ_κ` for the restarts `μ` of the window.

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ze

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm

variable {S : InaccSeq.{0}}

/-- **The cap window**: below every restart `ρ_κ < L(ω+1)` there is `x < ρ_κ` such that every restart `ρ_μ` in
`(x, ρ_κ)` has `cap(μ) ≤ ρ_κ`. -/
theorem zeCap_win {κ : Ordinal.{0}} (hκ : IsRestartIdx κ) (hκL : upsilon κ < Nc.ncL S (ω + 1)) :
    ∃ x < upsilon κ, ∀ μ, IsRestartIdx μ → x < upsilon μ → upsilon μ < upsilon κ →
      cdCapB S μ ≤ upsilon κ := by
  have hLeq : Nc.ncL S (ω + 1) = Pv S (Om ω + Nc.ncPp S * (ω + 1)) := Lw.lw_L_eq S (ω + 1)
  have hlT : upsilon κ < Pv S (Om ω + Nc.ncPp S * (ω + 1)) := hLeq ▸ hκL
  have hκ1 : 1 ≤ κ := Order.one_le_iff_ne_zero.2 hκ.1
  obtain ⟨ηt, -, hηt⟩ := iota_onto (S := S) _ κ hκ1 (cd_lt_iota hlT).le
  have hne : {η | iota S η = κ}.Nonempty := ⟨ηt, hηt⟩
  have hηm : iota S (sInf {η | iota S η = κ}) = κ := csInf_mem hne
  have hmin : ∀ η < sInf {η | iota S η = κ}, iota S η ≠ κ := fun η h he =>
    (csInf_le' (s := {η | iota S η = κ}) he).not_gt h
  generalize sInf {η | iota S η = κ} = ηm at hηm hmin
  have hpvm : Pv S ηm = upsilon κ := by
    calc Pv S ηm = upsilon (iota S ηm) := (ups_iota S ηm).symm
      _ = upsilon κ := by rw [hηm]
  have hηm0 : ηm ≠ 0 := by
    rintro rfl
    rw [iota_zero] at hηm
    exact (ri_lim hκ).succ_ne 0 (by rw [succ_eq_add_one, zero_add]; exact hηm)
  obtain ⟨η0, hdec, hdvd⟩ := cdExp_decomp hηm0
  generalize cdExp ηm = e at hdec hdvd
  have hη0m : η0 < ηm := by
    rw [hdec]; exact lt_add_of_pos_right _ (opow_pos _ omega0_pos)
  have hν : iota S η0 < κ :=
    lt_of_le_of_ne ((iota_mono (S := S) ηm η0 hη0m.le).trans_eq hηm) (hmin η0 hη0m)
  refine ⟨upsilon (iota S η0), upsilon_normal.strictMono hν, fun μ hμ hx hμκ => ?_⟩
  have hμν : iota S η0 < μ := upsilon_normal.strictMono.lt_iff_lt.1 hx
  have hμl : μ < κ := upsilon_normal.strictMono.lt_iff_lt.1 hμκ
  obtain ⟨-, hιμ, -⟩ := cdEta_spec (S := S) (Order.one_le_iff_ne_zero.2 hμ.1) (hμl.trans_eq hηm.symm)
  have hx0 : η0 < cdEta S μ := by
    by_contra h
    push Not at h
    have h' := iota_mono (S := S) η0 _ h
    rw [hιμ] at h'
    exact absurd h' (not_le.2 hμν)
  have hxm : cdEta S μ < η0 + ω ^ e := by
    rw [← hdec]
    by_contra h
    push Not at h
    have h' := iota_mono (S := S) (cdEta S μ) ηm h
    rw [hιμ, hηm] at h'
    exact absurd h' (not_le.2 hμl)
  obtain ⟨-, hxw⟩ := cdWin hdvd hx0 hxm
  unfold cdCapB
  calc Pv S (cdEta S μ + ω ^ cdExp (cdEta S μ)) ≤ Pv S ηm := Pv_mono (hxw.le.trans_eq hdec.symm)
    _ = upsilon κ := hpvm

/-- **CapV on all of `(L(ω), L(ω+1))`** from the frontier hypothesis `hVt` of the road. -/
theorem zeCapHigh
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → CdCapV S l) :
    ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l := by
  intro l hr hu
  by_cases h : Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l
  · exact hVt l hr hu h
  · exact Hl.hlU_capV S hr (lt_of_not_ge h)

/-- **In the window, CapV gives `r(μ) < ρ_κ`.** -/
theorem zeReach_lt_cap {κ μ : Ordinal.{0}} (hV : CdCapV S μ) (hcap : cdCapB S μ ≤ upsilon κ) :
    cdR S μ < upsilon κ :=
  hV.trans_le hcap

end Googology.Trans.PoR.InaccPsi.R2.Ze
