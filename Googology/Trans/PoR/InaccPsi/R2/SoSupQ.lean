import Googology.Trans.PoR.InaccPsi.R2.SoCnf

/-!
# The supply for the base renaming below `a^a`: `υ_{μ+ρ_μ^{ρ_μ}} ≤ r(μ)`

`ρ = ρ_μ = υ_μ`.  The reading `x = Σ ρ^{E_i}·c_i < ρ^ρ` (`E_i, c_i < ρ`) has the code
`soQ Ω₁ ρ x = Σ Ω₁^{E_i}·c_i`: a member of every `Cl(a, b)` with `a > Ω_ω`, `b ≥ ρ`, below `Ω₁^ρ < θ_{k+1}`.
`So.soSup_gen` along this code map gives the supply.

* `soGoodQ` (`η + y` is good for `y < P(η)^{P(η)}`), `soPvPv_lt_Om1`;
* `soQMem` (`ω^e·soQ Ω₁ ρ x` is a member when `e` is), `soE_lim` (an `ε`-number is a limit);
* `soSupQ` (**`υ_{μ+ρ_μ^{ρ_μ}} ≤ Θ_μ(G') ≤ r(μ)` at every Range restart with code `G_{k+1} + 1`,
  unconditionally**).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.So

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- `η + y` is good for every `y < P(η)^{P(η)}`. -/
theorem soGoodQ {η y : Ordinal.{0}} (hg : Bt.Good S η) (hy : y < Nm.Pv S η ^ Nm.Pv S η) :
    Bt.Good S (η + y) := by
  refine Rz.rz_good_shift hg ?_
  by_cases hyP : y < Nm.Pv S η
  · exact hyP.trans_le (Nm.Pv_mono le_self_add)
  · have h1 : 1 ≤ y := Order.one_le_iff_ne_zero.2 fun h0 => by
      rw [h0] at hyP; exact hyP (Sl.slPv_E (S := S) η).pos
    have hE := Sl.slPv_E (S := S) (η + 1)
    exact (hy.trans (soE_opow_lt hE (Nm.Pv_lt_succ hg) (Nm.Pv_lt_succ hg))).trans_le
      (Nm.Pv_mono (add_le_add le_rfl h1))

/-- `P(η)^{P(η)} < Ω₁` for a good `η`. -/
theorem soPvPv_lt_Om1 (η : Ordinal.{0}) (hg : Bt.Good S η) : Nm.Pv S η ^ Nm.Pv S η < Om 1 := by
  have hE := Sl.slPv_E (S := S) (η + 1)
  exact (soE_opow_lt hE (Nm.Pv_lt_succ hg) (Nm.Pv_lt_succ hg)).trans (Nm.Pv_lt_Om1 S _)

/-- An `ε`-number is a limit. -/
theorem soE_lim {ρ : Ordinal.{0}} (hρ : InE ρ) : IsSuccLimit ρ := by
  have h := isSuccLimit_opow_left isSuccLimit_omega0 hρ.pos.ne'
  have h5 : ω ^ ρ = ρ := hρ
  rwa [h5] at h

/-- `ω^e·soQ Ω₁ ρ x ∈ Cl(a, b)` for a member `e`, `x < ρ^ρ`, `ρ ≤ b`. -/
theorem soQMem {a b ρ : Ordinal.{0}} (hρ1 : 1 < ρ) (hb : ρ ≤ b) :
    ∀ x, x < ρ ^ ρ → ∀ e, e ∈ S.CSet a b → ω ^ e * soQ (Om 1) ρ x ∈ S.CSet a b := by
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hx e he
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [soQ_zero, mul_zero]; exact CSet.zero_mem a b
  obtain ⟨E, c, d, rfl, hc0, hca, hde, hdg⟩ := soEx hρ1 hx0
  have hE : E < ρ := by
    have := (lt_opow_iff_log_lt hρ1 (soLead_ne hρ1 hc0)).1 hx
    rwa [(soLead hρ1 hc0 hca hde).1] at this
  have hO : ω ^ e * Om 1 ^ E = ω ^ (e + Om 1 * E) := by
    rw [opow_add, opow_mul, soOm1_opow]
  rw [soQ_dec (Om 1) hρ1 hca hde, mul_add, ← mul_assoc, hO]
  have hOE : Om 1 * E ∈ S.CSet a b := by
    have := Nm.mem_opow_mul (S := S) (CSet.Om_mem (CSet.one_mem a b)) (hE.trans_le hb)
    rwa [soOm1_opow] at this
  exact CSet.add_mem (Nm.mem_opow_mul (CSet.add_mem he hOE) (hca.trans_le hb))
    (IH d hdg (hdg.trans hx) e he)

/-- **The supply for the base renaming**: `υ_{μ+ρ_μ^{ρ_μ}} ≤ Θ_μ(G') ≤ r(μ)` at every Range restart `μ` with
code `G_{k+1} + 1`. -/
theorem soSupQ (k : ℕ) {μ : Ordinal.{0}} (hR : CdRange S μ) (hc : cdCode S μ = Ls.lsG S (k + 1) + 1) :
    upsilon (μ + upsilon μ ^ upsilon μ) ≤ cdTheta S μ (Ls.lsG S (k + 1)) ∧
      upsilon (μ + upsilon μ ^ upsilon μ) ≤ cdR S μ := by
  obtain ⟨hgμ, -, hpv⟩ := Ra.raName hR
  set ρ := upsilon μ with hρdef
  have hρE : InE ρ := by rw [← hpv]; exact Sl.slPv_E _
  have hρ1 : 1 < ρ := soOne_lt_E hρE
  have hρΩ : ρ < Om 1 := soRho_lt_Om1 hR
  have hlim : IsSuccLimit (ρ ^ ρ) := isSuccLimit_opow_left (soE_lim hρE) hρE.pos.ne'
  refine soSup_gen hR hc hlim (fun y hy => soGoodQ hgμ (by rw [hpv]; exact hy))
    (by rw [← hpv]; exact (soPvPv_lt_Om1 _ hgμ).le) (soQ (Om 1) ρ) ?_ ?_ ?_ ?_
  · intro x _
    exact soQ_add (Om 1) hρE hρ1 x
  · intro y x hyx hx
    rcases hyx.lt_or_eq with h | h
    · exact (soQ_strict hρ1 x y h ((soMX_lt hρ1 y (h.trans hx)).trans hρΩ)
        ((soMX_lt hρ1 x hx).trans hρΩ)).le
    · rw [h]
  · intro x hx a b ha hb
    have h := soQMem (S := S) hρ1 hb x hx _ (Ls.lsTh_mem ha 2)
    rw [Ls.lsTh_opow] at h
    exact CSet.add_mem (ConjT.OmW_mem S a b) h
  · intro x hx
    have hE : InE (Lc.lcTh S (k + 1)) := Low.opow_eq_self_of_SC (Ls.lsTh_SC (k + 1))
    have hO := Rp.rpOm1_lt_th (S := S) k
    exact (soQ_lt (r := Om 1) hρ1 x ρ hx ((soMX_lt hρ1 x hx).trans hρΩ)).trans
      (soE_opow_lt hE hO (hρΩ.trans hO))

end Googology.Trans.PoR.InaccPsi.R2.So
