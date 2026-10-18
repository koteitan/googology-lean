import Googology.Trans.PoR.InaccPsi.R2.GgUni
import Googology.Trans.PoR.InaccPsi.R2.RlBound

/-!
# The reading `Θ_λ` below `Γ_{Ω₁+1}` at every named restart: the substitution `Ω₁ ↦ ρ_λ`

`Θ_λ(m)` (`Cd.cdTheta`) is the order type of the codes of `Cl(A_{η_λ}, ρ_λ)` below `m`, `ρ_λ = υ_λ`,
`ggGam = Γ_{Ω₁+1}` (the least strongly critical ordinal above `Ω₁`), `GgCl Z` the codes over `Z` (built from
the ordinals `< Z` and `Ω₁` by `+` and `φ`), `ggTh y` the reading over `y` (`Gg.ggTh`), `W = Ω₁^{Ω₁}`.
`Gg.ggHull_iff` and `Gg.ggTheta_eq` hold at the fixed points `F = υ_F`; the fixed point is not needed:

* `rmHull_iff` (**at every named restart the hull below `Γ_{Ω₁+1}` is the set of codes over `ρ_λ`**; the
  countable members of the hull are below `ρ_λ = ψ_{Ω₁}(A_{η_λ})`, `Gg.ggKey`, `Gg.ggCl_of_CSet`);
* `rmTheta_eq` (**`Θ_λ(m) = Θ^Gg_{ρ_λ}(m)` for `m ≤ Γ_{Ω₁+1}`**);
* `rmTheta_add` (`Θ_λ(u + v) = Θ_λ(u) + Θ_λ(v)` for a code `u`), `rmTheta_opow` (`Θ_λ(ω^c) = ω^{Θ_λ(c)}`),
  `rmTheta_Om1_mul` (`Θ_λ(Ω₁·k) = ρ_λ·k`);
* the nonlinear values: `rmTheta_Om1_pow` (**`Θ_λ(Ω₁^k) = ρ_λ^k`**), `rmTheta_W` (**`Θ_λ(Ω₁^{Ω₁}) = ρ_λ^{ρ_λ}`**);
* `rmR_ge_W`: a code `m_λ ≥ Ω₁^{Ω₁}` gives `r(λ) ≥ δ_λ + ρ_λ^{ρ_λ}`.

These values lie below `Γ_{Ω₁+1}`; the collapse bound `Θ_μ(c) ≥ P(η_μ + …)` of LC-STRICT reads codes
`ψ_{Ω₂}(…)` above it and is not proved here.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Rm

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Cd
  Googology.Trans.PoR.InaccPsi.R2.Gg

variable {S : InaccSeq.{0}} {l ηx : Ordinal.{0}}

/-- **At every named restart the hull below `Γ_{Ω₁+1}` is the set of codes over `ρ_λ`.** -/
theorem rmHull_iff (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) {x : Ordinal.{0}} (hx : x < ggGam) :
    x ∈ cdHull S l ↔ GgCl (upsilon l) x := by
  constructor
  · intro h
    have h0 : 0 < upsilon l := (upsPt_upsilon (pos_iff_ne_zero.2 hl.1)).1
    exact ggCl_of_CSet h0 (ggKey hl hX) x h hx
  · intro h
    exact h.mem_CSet le_rfl

/-- **`Θ_λ(m) = Θ^Gg_{ρ_λ}(m)` for `m ≤ Γ_{Ω₁+1}`.** -/
theorem rmTheta_eq (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) {m : Ordinal.{0}} (hm : m ≤ ggGam) :
    cdTheta S l m = ggTh (upsilon l) m :=
  ggOtp_congr m fun _ hx => rmHull_iff hl hX (hx.trans_le hm)

theorem rm_SC (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) : SC (upsilon l) := by
  have := Pv_SC S (cdEta S l); rwa [cdEta_pv hl.1 hX] at this

theorem rm_ups_pos (hl : IsRestartIdx l) : 0 < upsilon l := (upsPt_upsilon (pos_iff_ne_zero.2 hl.1)).1

/-- `Θ_λ(u + v) = Θ_λ(u) + Θ_λ(v)` for a code `u` over `ρ_λ` and `u + v ≤ Γ_{Ω₁+1}`. -/
theorem rmTheta_add (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) {u v : Ordinal.{0}}
    (hu : GgCl (upsilon l) u) (huv : u + v ≤ ggGam) :
    cdTheta S l (u + v) = cdTheta S l u + cdTheta S l v := by
  rw [rmTheta_eq hl hX huv, rmTheta_eq hl hX (le_self_add.trans huv),
    rmTheta_eq hl hX (le_add_self.trans huv)]
  exact ggTh_add (rm_SC hl hX) hu v

/-- `Θ_λ(ω^c) = ω^{Θ_λ(c)}` for a code `c` over `ρ_λ` with `ω^c ≤ Γ_{Ω₁+1}`. -/
theorem rmTheta_opow (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) {c : Ordinal.{0}}
    (hc : GgCl (upsilon l) c) (h : ω ^ c ≤ ggGam) : cdTheta S l (ω ^ c) = ω ^ cdTheta S l c := by
  rw [rmTheta_eq hl hX h, rmTheta_eq hl hX ((right_le_opow c one_lt_omega0).trans h)]
  exact ggTh_opow (rm_SC hl hX) hc

theorem rm_Om1_lt_gam : Om (1 : Ordinal.{0}) < ggGam := ggGam_spec.2

theorem rm_Om1_eq : ω ^ Om (1 : Ordinal.{0}) = Om 1 :=
  Low.opow_eq_self_of_SC (SC_Om one_ne_zero)

theorem rm_gam_inE : ω ^ ggGam = ggGam := Low.opow_eq_self_of_SC ggGam_spec.1

/-- `Ω₁·k < Γ_{Ω₁+1}`. -/
theorem rm_Om1_mul_lt (k : ℕ) : Om (1 : Ordinal.{0}) * k < ggGam :=
  mul_lt_inE rm_gam_inE rm_Om1_lt_gam ((natCast_lt_omega0 k).trans (omega0_lt_inE rm_gam_inE))

/-- `Θ_λ(Ω₁·k) = ρ_λ·k`. -/
theorem rmTheta_Om1_mul (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) :
    ∀ k : ℕ, cdTheta S l (Om 1 * k) = upsilon l * k
  | 0 => by rw [Nat.cast_zero, mul_zero, mul_zero]; exact ggOtp_zero _
  | k + 1 => by
    have hlt := rm_Om1_mul_lt (k + 1)
    rw [Nat.cast_succ, mul_add_one] at hlt ⊢
    rw [rmTheta_add hl hX (GgCl.mul_nat (rm_ups_pos hl) GgCl.om k) hlt.le, rmTheta_Om1_mul hl hX k,
      mul_add_one]
    congr 1
    rw [rmTheta_eq hl hX rm_Om1_lt_gam.le]
    exact ggTh_Om1 (rm_SC hl hX) (by rw [← cdEta_pv hl.1 hX]; exact Pv_lt_Om1 S _)

/-- `x^k = ω^{x·k}` for an `ε`-number `x`. -/
theorem rm_pow_eq {x : Ordinal.{0}} (hx : ω ^ x = x) (a : Ordinal.{0}) : x ^ a = ω ^ (x * a) := by
  conv_lhs => rw [← hx]
  rw [opow_mul]

/-- **`Θ_λ(Ω₁^k) = ρ_λ^k`.** -/
theorem rmTheta_Om1_pow (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) (k : ℕ) :
    cdTheta S l (Om 1 ^ (k : Ordinal.{0})) = upsilon l ^ (k : Ordinal.{0}) := by
  have hρ : ω ^ upsilon l = upsilon l := Low.opow_eq_self_of_SC (rm_SC hl hX)
  rw [rm_pow_eq rm_Om1_eq, rm_pow_eq hρ]
  have hlt : ω ^ (Om (1 : Ordinal.{0}) * k) ≤ ggGam := by
    have := (opow_lt_opow_iff_right one_lt_omega0).2 (rm_Om1_mul_lt k)
    rw [rm_gam_inE] at this; exact this.le
  rw [rmTheta_opow hl hX (GgCl.mul_nat (rm_ups_pos hl) GgCl.om k) hlt, rmTheta_Om1_mul hl hX k]

/-- **`Θ_λ(Ω₁^{Ω₁}) = ρ_λ^{ρ_λ}`.** -/
theorem rmTheta_W (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) :
    cdTheta S l (Om 1 ^ Om 1) = upsilon l ^ upsilon l := by
  have hρ : ω ^ upsilon l = upsilon l := Low.opow_eq_self_of_SC (rm_SC hl hX)
  have hpos := rm_ups_pos hl
  -- `Ω₁·Ω₁ = ω^{Ω₁ + Ω₁}`, `Ω₁^{Ω₁} = ω^{Ω₁·Ω₁}`
  have e1 : Om (1 : Ordinal.{0}) * Om 1 = ω ^ (Om 1 + Om 1) := by
    conv_lhs => rw [← rm_Om1_eq]
    rw [opow_add]
  have eρ : upsilon l * upsilon l = ω ^ (upsilon l + upsilon l) := by
    conv_lhs => rw [← hρ]
    rw [opow_add]
  have h2 : Om (1 : Ordinal.{0}) + Om 1 < ggGam := ggGam_spec.1.isPrincipal rm_Om1_lt_gam rm_Om1_lt_gam
  have h3 : ω ^ (Om (1 : Ordinal.{0}) + Om 1) < ggGam := by
    have := (opow_lt_opow_iff_right one_lt_omega0).2 h2
    rwa [rm_gam_inE] at this
  have h4 : ω ^ (ω ^ (Om (1 : Ordinal.{0}) + Om 1)) ≤ ggGam := by
    have := (opow_lt_opow_iff_right one_lt_omega0).2 h3
    rw [rm_gam_inE] at this; exact this.le
  have hc2 : GgCl (upsilon l) (Om 1 + Om 1) := GgCl.add GgCl.om GgCl.om
  have hc3 : GgCl (upsilon l) (ω ^ (Om 1 + Om 1)) := GgCl.opow hpos hc2
  have hT1 : cdTheta S l (Om 1) = upsilon l := by
    rw [rmTheta_eq hl hX rm_Om1_lt_gam.le]
    exact ggTh_Om1 (rm_SC hl hX) (by rw [← cdEta_pv hl.1 hX]; exact Pv_lt_Om1 S _)
  have hT2 : cdTheta S l (Om 1 + Om 1) = upsilon l + upsilon l := by
    rw [rmTheta_add hl hX GgCl.om h2.le, hT1]
  rw [rm_pow_eq rm_Om1_eq, rm_pow_eq hρ, e1, eρ, rmTheta_opow hl hX hc3 h4,
    rmTheta_opow hl hX hc2 h3.le, hT2]

/-- **A code `m_λ ≥ Ω₁^{Ω₁}` gives `r(λ) ≥ δ_λ + ρ_λ^{ρ_λ}`.** -/
theorem rmR_ge_W (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) (hm : Om 1 ^ Om 1 ≤ cdCode S l) :
    cdDelta l + upsilon l ^ upsilon l ≤ cdR S l := by
  rw [← rmTheta_W hl hX]
  exact (add_le_add le_rfl (cdTheta_mono S l hm)).trans (Rl.rlR_ge S l)

end Googology.Trans.PoR.InaccPsi.R2.Rm
