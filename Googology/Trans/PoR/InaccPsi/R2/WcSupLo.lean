import Googology.Trans.PoR.InaccPsi.R2.WcPast
import Googology.Trans.PoR.InaccPsi.R2.WcQ

/-!
# The supply data of `Vr.VrSup` at one restart, up to the non-low carry

`a = υ_λ`, `u = υ_{λ+1}`, `g = ω^{ω^{u+1}}` (the witness offset of `Vo.voWit`), `μ` a Range restart with code
`G_{k+2}+1` below `L(ω)`, `u' = υ_{μ+1}`, `g' = ω^{ω^{u'+1}}`, `X = ω^{ω^{u'+1}+1}` (`Wc.wcX`).

* `wcSupLo` (**`WcRead0` at `μ` and `π_{υ_μ,υ_λ}(m z) < ω^{u'+1}` at the other offsets of `Os` give one offset map
  `f` with: `ω² ∣ X`, `υ_{μ+X} ≤ r(μ)`, `f` an `Sl.SlOff` map on `Os` with bound `X`, EQ at the witness
  `img(Ew) = r(μ+g')`, and the carry of every low decomposition `υ_{λ+z+ω+1} + m(z)`**): these are all clauses of
  `Vr.VrSup S λ β` at `μ` except `γ < υ_μ < υ_λ`, `μ + X ≤ λ`, and, in `Vr.VrCarry`, `CdLower(μ + f z)`, the
  big-reach clause and the image bound of the decompositions that are not of the two forms above.

No new definition, no new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Wc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

theorem wcX_dvd (u : Ordinal.{0}) : ω ^ 2 ∣ wcX u := by
  unfold wcX
  rw [← opow_natCast]
  refine opow_dvd_opow ω ?_
  have h2 : ((2 : ℕ) : Ordinal.{0}) ≤ ω := (natCast_lt_omega0 2).le
  exact h2.trans ((left_le_opow ω (lt_of_le_of_lt zero_le (lt_add_one u))).trans le_self_add)

/-- **The supply data at `μ` up to the non-low carry.** -/
theorem wcSupLo (k : ℕ) {l μ η1 : Ordinal.{0}} {Os : Finset Ordinal.{0}} (hR : CdRange S μ)
    (hc : cdCode S μ = Ls.lsG S (k + 1 + 1) + 1) (hω : upsilon μ < Nc.ncL S ω) (hr : WcRead0 S μ)
    (hOs : ∀ z ∈ Os, 0 < z ∧ ω ^ 2 ∣ z) (hg : ω ^ ω ^ (upsilon (l + 1) + 1) ∈ Os)
    (hP : ∀ z ∈ Os, z ≠ ω ^ ω ^ (upsilon (l + 1) + 1) →
      pi (upsilon μ) (upsilon l) (cdOff (cdExp z)) < ω ^ (upsilon (μ + 1) + 1))
    (hB : Bases (upsilon μ) (upsilon l)) (hn : upsilon (μ + 2) < Nm.Pv S η1)
    (hCw : upsilon (μ + ω ^ ω ^ (upsilon (μ + 1) + 1) + ω + 1) < nuC)
    (hside : ∀ Q : Ordinal.{0} → Ordinal.{0}, ∀ z ∈ Os, z ≠ ω ^ ω ^ (upsilon (l + 1) + 1) →
      ω ≤ Vy.vyMap Q z ∧ Vy.vyMap Q z < upsilon (μ + 2) ∧ upsilon (μ + Vy.vyMap Q z + ω + 1) < nuC) :
    ∃ f : Ordinal.{0} → Ordinal.{0},
      ω ^ 2 ∣ wcX (upsilon (μ + 1)) ∧ upsilon (μ + wcX (upsilon (μ + 1))) ≤ cdR S μ ∧
      Sl.SlOff f Os (wcX (upsilon (μ + 1))) ∧
      Vr.vrImg l μ f (Vr.vrEw (ω ^ ω ^ (upsilon (l + 1) + 1))) = cdR S (μ + ω ^ ω ^ (upsilon (μ + 1) + 1)) ∧
      ∀ z ∈ Os, z ≠ ω ^ ω ^ (upsilon (l + 1) + 1) →
        Vr.vrImg l μ f (.add (.ub (z + ω + 1) .base) (.lo (cdOff (cdExp z)))) ≤ cdR S (μ + f z) := by
  have hu1 : upsilon (μ + 1) < Om1 := by
    rw [wcUps1 (k := k + 1) hR hc hω, Ph.ph_Om1_eq]; exact psi_lt Low.InR_Om_one _
  obtain ⟨Q, hoff, hwit, hlo⟩ := wcQ_carry (S := S) hOs hg hP hB hR.1 hu1 hn hCw hside
  exact ⟨Vy.vyMap Q, wcX_dvd _, (wcSup hR hc hω hr).2.2, hoff, hwit, hlo⟩

#print axioms wcSupLo

end Googology.Trans.PoR.InaccPsi.R2.Wc
