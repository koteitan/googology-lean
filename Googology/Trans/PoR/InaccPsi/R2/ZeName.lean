import Googology.Trans.PoR.InaccPsi.R2.ZeBad
import Googology.Trans.PoR.InaccPsi.R2.ZeWin
import Googology.Trans.PoR.InaccPsi.R2.GgCl

/-!
# The name window below a restart: codes of the nearby restarts

Notation as in `R2.ZeWin`; `θ = ConjT.th S`, `m_λ = cdCode S λ`, `e(η)` the last exponent.

* `zeName_win` (**the name window**): for every restart index `κ` with `ρ_κ < L(ω+1)`, writing the good name
  `η_κ = β + ω^E` (`ω^E ∣ β`), every restart `ρ_μ ∈ (υ_{ι(β)}, ρ_κ)` has its good name in `(β, η_κ)`, hence
  `e(η_μ) < E` and `cap(μ) ≤ ρ_κ`; and `υ_{ι(β)} < ρ_κ` (`Ze.zeIota_prefix_lt`: the good name is never at the end
  of a bad interval).
* `ze_pi_gt` (`θ·ω < π_η` for `η ≠ 0`), `zeExp_le_of_code` (**`m_κ ≤ θ·ω` gives `E = e(η_κ) ≤ θ·ω`**: the
  π-code branch `E ≥ Ω₂` has `m_κ = π_η > θ·ω`).
* `zeCode_win` (**short codes are short near the top**): if `m_κ ≤ θ·ω`, every restart in the window has
  `m_μ < θ·ω`.

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ze

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm

variable {S : InaccSeq.{0}}

/-- **The name window**: below `ρ_κ` there is `x = υ_{ι(β)} < ρ_κ` (`η_κ = β + ω^E`) such that every restart
`ρ_μ ∈ (x, ρ_κ)` has `e(η_μ) < e(η_κ)` and `cap(μ) ≤ ρ_κ`. -/
theorem zeName_win {κ : Ordinal.{0}} (hκ : IsRestartIdx κ) (hκL : upsilon κ < Nc.ncL S (ω + 1)) :
    ∃ x < upsilon κ, ∀ μ, IsRestartIdx μ → x < upsilon μ → upsilon μ < upsilon κ →
      cdExp (cdEta S μ) < cdExp (cdEta S κ) ∧ cdCapB S μ ≤ upsilon κ := by
  have hLeq : Nc.ncL S (ω + 1) = Pv S (Om ω + Nc.ncPp S * (ω + 1)) := Lw.lw_L_eq S (ω + 1)
  have hlT : upsilon κ < Pv S (Om ω + Nc.ncPp S * (ω + 1)) := hLeq ▸ hκL
  obtain ⟨hg, hικ, -, hpv⟩ := cdEta_pv_spec (S := S) hκ.1 hlT
  have hη0 : cdEta S κ ≠ 0 := by
    intro h0
    rw [h0, iota_zero] at hικ
    exact (ri_lim hκ).succ_ne 0 (by rw [succ_eq_add_one, zero_add]; exact hικ)
  obtain ⟨β, hdec, hdvd⟩ := cdExp_decomp hη0
  have hg' : Bt.Good S (β + ω ^ cdExp (cdEta S κ)) := hdec ▸ hg
  have hlt := zeIota_prefix_lt hdvd hg'
  rw [← hdec, hικ] at hlt
  refine ⟨upsilon (iota S β), upsilon_normal.strictMono hlt, fun μ hμ hx hμκ => ?_⟩
  have hμν : iota S β < μ := upsilon_normal.strictMono.lt_iff_lt.1 hx
  have hμl : μ < κ := upsilon_normal.strictMono.lt_iff_lt.1 hμκ
  obtain ⟨-, hιμ, -⟩ := cdEta_spec (S := S) (Order.one_le_iff_ne_zero.2 hμ.1) (hμl.trans_eq hικ.symm)
  have hx0 : β < cdEta S μ := by
    by_contra h
    push Not at h
    have h' := iota_mono (S := S) β _ h
    rw [hιμ] at h'
    exact absurd h' (not_le.2 hμν)
  have hxm : cdEta S μ < β + ω ^ cdExp (cdEta S κ) := by
    rw [← hdec]
    by_contra h
    push Not at h
    have h' := iota_mono (S := S) (cdEta S μ) (cdEta S κ) h
    rw [hιμ, hικ] at h'
    exact absurd h' (not_le.2 hμl)
  obtain ⟨hxe, hxw⟩ := cdWin hdvd hx0 hxm
  refine ⟨hxe, ?_⟩
  unfold cdCapB
  calc Pv S (cdEta S μ + ω ^ cdExp (cdEta S μ)) ≤ Pv S (cdEta S κ) :=
        Pv_mono (hxw.le.trans_eq hdec.symm)
    _ = upsilon κ := hpv

/-- `θ·ω < π_η = ψ_{Ω₂}(A_η)` for `η ≠ 0`. -/
theorem ze_pi_gt (S : InaccSeq.{0}) {η : Ordinal.{0}} (hη : η ≠ 0) : ConjT.th S * ω < cdPi S η := by
  have hSC : SC (cdPi S η) := SC_psi (InR_Om_succ 1) _
  have hE : InE (cdPi S η) := Gg.gg_SC_eps hSC
  have hA : Om (ω : Ordinal.{0}) < ConjT.Aη S η := by
    unfold ConjT.Aη
    exact lt_add_of_pos_right _ (mul_pos (ConjT.SC_th S).1 (pos_iff_ne_zero.2 hη))
  have hθ : ConjT.th S < cdPi S η :=
    psi_lt_psi_of_mem (InR_Om_succ 1) hA (ConjT.OmW_mem S _ _)
  exact hE.mul_lt hθ (omega0_lt_inE hE)

/-- **`m ≤ θ·ω` gives `e(η) ≤ θ·ω`** (for `η ≠ 0`). -/
theorem zeExp_le_of_code {η : Ordinal.{0}} (hη : η ≠ 0) (hm : cdCodeOf S η ≤ ConjT.th S * ω) :
    cdExp η ≤ ConjT.th S * ω := by
  have hθω : (ω : Ordinal.{0}) ≤ ConjT.th S * ω := by
    calc (ω : Ordinal.{0}) = 1 * ω := (one_mul _).symm
      _ ≤ ConjT.th S * ω := mul_le_mul_right' (Order.one_le_iff_pos.2 (ConjT.SC_th S).1) _
  by_cases h2 : cdExp η < Om (1 + 1)
  · rw [cdCodeOf_of_lt h2] at hm
    unfold cdOff at hm
    split_ifs at hm with hω
    · exact hω.le.trans hθω
    · exact hm
  · have e : cdCodeOf S η = cdPi S η := if_neg h2
    rw [e] at hm
    exact absurd hm (not_le.2 (ze_pi_gt S hη))

/-- **Short codes are short near the top**: if `m_κ ≤ θ·ω`, the restarts of the name window have `m_μ < θ·ω`. -/
theorem zeCode_win {κ : Ordinal.{0}} (hκ : IsRestartIdx κ) (hκL : upsilon κ < Nc.ncL S (ω + 1))
    (hm : cdCode S κ ≤ ConjT.th S * ω) :
    ∃ x < upsilon κ, ∀ μ, IsRestartIdx μ → x < upsilon μ → upsilon μ < upsilon κ →
      cdCode S μ < ConjT.th S * ω := by
  have hLeq : Nc.ncL S (ω + 1) = Pv S (Om ω + Nc.ncPp S * (ω + 1)) := Lw.lw_L_eq S (ω + 1)
  have hlT : upsilon κ < Pv S (Om ω + Nc.ncPp S * (ω + 1)) := hLeq ▸ hκL
  obtain ⟨-, hικ, -, -⟩ := cdEta_pv_spec (S := S) hκ.1 hlT
  have hη0 : cdEta S κ ≠ 0 := by
    intro h0
    rw [h0, iota_zero] at hικ
    exact (ri_lim hκ).succ_ne 0 (by rw [succ_eq_add_one, zero_add]; exact hικ)
  have hE := zeExp_le_of_code hη0 hm
  obtain ⟨x, hx, hw⟩ := zeName_win hκ hκL
  refine ⟨x, hx, fun μ hμ h1 h2 => ?_⟩
  exact ((cdCodeOf_le_exp S _).trans_lt (hw μ hμ h1 h2).1).trans_le hE

end Googology.Trans.PoR.InaccPsi.R2.Ze
