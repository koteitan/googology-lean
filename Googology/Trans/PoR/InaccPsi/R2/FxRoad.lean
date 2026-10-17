import Googology.Trans.PoR.InaccPsi.R2.FxIso

/-!
# ENUM-REACH below `cpB1 = Λ_B⁺` except at the limits of fixed points, and the road

A restart index `λ` of the range is **left** (`Cp.CpOut2 λ`) when `cpB1 ≤ λ`, or `λ = υ_λ` is a fixed point of
`υ` that is a limit of fixed points (`¬ CpIso λ`).  Every other restart of the range is covered:

* `fxEnum_cov` (**ENUM-REACH below `cpB1` off the limits of fixed points**): at every `λ` of the range with
  `λ < cpB1` and not (`λ = υ_λ`, `¬ CpIso λ`): `Θ_λ(m_λ) = VzOrec(λ)`, UPPER, LOWER, the caps `CdCapV`,
  `CdCapAt` (`Cp.cpEnum_nonfix`, `Cp.cpCapV_nonfix` off the fixed points; `Fx.fxIso_exact`, `Fx.fxIso_capV` at
  the isolated ones);
* `fxTHfix`: `Cp.CpTHfix` (`Θ_F(m_F) = VzOrec(F)` at every fixed point `F < cpB1` of the range) follows from
  the same statement at the fixed points that are limits of fixed points;
* `fxUPPER`, `fxLOWER`, `fxCapV`, `fxCAP0`, `fxCAP1`: `CdUPPER`, `CdLOWER`, the cap of the values below `L(ω)`,
  `CdCAP0`, `CdCAP1 (L(ω))` from the same statements at the left restarts only;
* `fxLow` (`L(ω) ≤ ν_C`), `fxRoad`, `fxRoad_cap`, `fxRoad3`: the conclusions of `Cp.cpRoad`, `Cp.cpRoad_cap`,
  `Cp.cpRoad3` with their ENUM-REACH and cap hypotheses asked only at the left restarts.

No new axiom, no new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Fx

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Br Googology.Trans.PoR.InaccPsi.R2.Bt
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp

variable {S : InaccSeq.{0}}

/-- Every index is left, or below `cpB1` and not a fixed point, or an isolated fixed point below `cpB1`. -/
theorem fxOut2_or (l : Ordinal.{0}) :
    CpOut2 l ∨ (l < cpB1 ∧ l < upsilon l) ∨ (l < cpB1 ∧ upsilon l = l ∧ CpIso l) := by
  rcases cpOut_or l with (h | h) | h
  · exact Or.inl (Or.inl h)
  · rcases le_or_gt cpB1 l with hB | hB
    · exact Or.inl (Or.inl hB)
    · by_cases hiso : CpIso l
      · exact Or.inr (Or.inr ⟨hB, h, hiso⟩)
      · exact Or.inl (Or.inr ⟨h, hiso⟩)
  · exact Or.inr (Or.inl h)

/-- **ENUM-REACH below `cpB1` off the limits of fixed points.** -/
theorem fxEnum_cov {l η1 : Ordinal.{0}} (hl : IsRestartIdx l) (hww : ω * ω < l) (hlB : l < cpB1)
    (hn : upsilon l < Pv S η1) (hcov : ¬ (upsilon l = l ∧ ¬ CpIso l)) :
    cdTheta S l (cdCode S l) = VzOrec l ∧ CdUpper S l ∧ CdLower S l ∧ CdCapV S l ∧ CdCapAt S l := by
  rcases (upsilon_normal.strictMono.le_apply : l ≤ upsilon l).lt_or_eq with hfix | hfix
  · obtain ⟨hO, -, hθ, -, -, hU, hL⟩ := cpEnum_nonfix hl hww hfix hlB hn
    exact ⟨hθ.trans hO.symm, hU, hL, cpCapV_nonfix hl hww hfix hlB hn, cpCapAt_nonfix hl hww hfix hlB hn⟩
  · have hiso : CpIso l := by
      by_contra h
      exact hcov ⟨hfix.symm, h⟩
    obtain ⟨hθ, -, -, -, -, hU, hL⟩ := fxIso_exact hl hfix.symm hlB hiso hn
    exact ⟨hθ, hU, hL, fxIso_capV hl hfix.symm hlB hiso hn, fxIso_capAt hl hfix.symm hlB hiso hn⟩

/-- `fxEnum_cov` on the range. -/
theorem fxEnum_range {l : Ordinal.{0}} (hr : CdRange S l) (hlB : l < cpB1)
    (hcov : ¬ (upsilon l = l ∧ ¬ CpIso l)) :
    cdTheta S l (cdCode S l) = VzOrec l ∧ CdUpper S l ∧ CdLower S l ∧ CdCapV S l ∧ CdCapAt S l :=
  fxEnum_cov hr.1 (cp_ww_lt_B0.trans_le hr.2.1) hlB (cp_name_L hr.2.2.1) hcov

/-- **`Cp.CpTHfix` from the notation statement at the fixed points that are limits of fixed points.** -/
theorem fxTHfix (h : ∀ l, CdRange S l → l < cpB1 → upsilon l = l → ¬ CpIso l →
    cdTheta S l (cdCode S l) = VzOrec l) : CpTHfix S := fun l hr hlB hfix => by
  by_cases hiso : CpIso l
  · exact (fxEnum_range hr hlB fun h' => h'.2 hiso).1
  · exact h l hr hlB hfix hiso

/-- **UPPER on the range from UPPER at the left restarts.** -/
theorem fxUPPER (hU : ∀ l, CdRange S l → CpOut2 l → CdUpper S l) : CdUPPER S := fun l hr => by
  rcases fxOut2_or l with h | ⟨hlB, hfix⟩ | ⟨hlB, hfix, hiso⟩
  · exact hU l hr h
  · exact (cpUPPER_init hr hlB hfix).1
  · exact (fxEnum_range hr hlB fun h' => h'.2 hiso).2.1

/-- **LOWER on the range from LOWER at the left restarts.** -/
theorem fxLOWER (hL : ∀ l, CdRange S l → CpOut2 l → CdLower S l) : CdLOWER S := fun l hr => by
  rcases fxOut2_or l with h | ⟨hlB, hfix⟩ | ⟨hlB, hfix, hiso⟩
  · exact hL l hr h
  · exact (cpUPPER_init hr hlB hfix).2
  · exact (fxEnum_range hr hlB fun h' => h'.2 hiso).2.2.1

/-- **The cap of the values below `L(ω)` from the cap at the left restarts.** -/
theorem fxCapV (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → CpOut2 l → CdCapV S l) :
    ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → CdCapV S l := fun l hr hX => by
  rcases fxOut2_or l with h | ⟨hlB, hfix⟩ | ⟨hlB, hfix, hiso⟩
  · exact hV l hr hX h
  · exact cpCapV_nonfix hr.1 (cp_ww_lt_B0.trans_le hr.2.1) hfix hlB (cp_name_L hr.2.2.1)
  · exact (fxEnum_range hr hlB fun h' => h'.2 hiso).2.2.2.1

/-- **CAP-0 from CAP-0 at the left restarts.** -/
theorem fxCAP0 (h0 : ∀ l, IsRestartIdx l → cdB0 ≤ l → upsilon l < cdMstar S → CpOut2 l → CdCapAt S l) :
    CdCAP0 S := fun l hl hB hlev => by
  rcases fxOut2_or l with h | ⟨hlB, hfix⟩ | ⟨hlB, hfix, hiso⟩
  · exact h0 l hl hB hlev h
  · exact cpCapAt_nonfix hl (cp_ww_lt_B0.trans_le hB) hfix hlB hlev
  · exact fxIso_capAt hl hfix hlB hiso hlev

/-- **CAP-1 below `L(ω)` from CAP-1 at the left restarts.** -/
theorem fxCAP1 (h1 : ∀ l, IsRestartIdx l → cdB0 ≤ l → cdMstar S ≤ upsilon l → upsilon l < Nc.ncL S ω →
    cdCode S l < Nc.ncPp S → CpOut2 l → CdCapAt S l) : CdCAP1 S (Nc.ncL S ω) :=
  fun l hl hB hlev hX hc => by
    rcases fxOut2_or l with h | ⟨hlB, hfix⟩ | ⟨hlB, hfix, hiso⟩
    · exact h1 l hl hB hlev hX hc h
    · exact cpCapAt_nonfix hl (cp_ww_lt_B0.trans_le hB) hfix hlB (Lw.lw_L_eq S ω ▸ hX)
    · exact fxIso_capAt hl hfix hlB hiso (Lw.lw_L_eq S ω ▸ hX)

/-- **NU-LOW″ from the caps at the left restarts**: `L(ω) ≤ ν_C`. -/
theorem fxLow (h0 : ∀ l, IsRestartIdx l → cdB0 ≤ l → upsilon l < cdMstar S → CpOut2 l → CdCapAt S l)
    (h1 : ∀ l, IsRestartIdx l → cdB0 ≤ l → cdMstar S ≤ upsilon l → upsilon l < Nc.ncL S ω →
      cdCode S l < Nc.ncPp S → CpOut2 l → CdCapAt S l) : Nc.ncL S ω ≤ nuC :=
  cdLow (fxCAP0 h0) (fxCAP1 h1)

/-- **The road with ENUM-REACH and the cap of the values asked only at the left restarts.** -/
theorem fxRoad (hU : ∀ l, CdRange S l → CpOut2 l → CdUpper S l)
    (hL : ∀ l, CdRange S l → CpOut2 l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → CpOut2 l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  cdRoad (fxUPPER hU) (fxLOWER hL) (fxCapV hV) hC hEQ hrest hB2

/-- **The road with the caps asked only at the left restarts**: CAP-0, CAP-1 there, (CL), (TC), (EMB₂). -/
theorem fxRoad_cap (h0 : ∀ l, IsRestartIdx l → cdB0 ≤ l → upsilon l < cdMstar S → CpOut2 l → CdCapAt S l)
    (h1 : ∀ l, IsRestartIdx l → cdB0 ≤ l → cdMstar S ≤ upsilon l → upsilon l < Nc.ncL S ω →
      cdCode S l < Nc.ncPp S → CpOut2 l → CdCapAt S l) (hC : CdCL S) (hTC : CdTC S)
    (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  cdRoad_cap (fxCAP0 h0) (fxCAP1 h1) hC hTC hB2

/-- **The road with UPPER and LOWER asked only at `λ ≥ cpB1`, the notation statement only at the limits of
fixed points below `cpB1`**, the cap of the values at the left restarts, (CL), EQ, TCrest, (EMB₂). -/
theorem fxRoad3 (hU : CpUPPERhigh S) (hL : CpLOWERhigh S)
    (hT : ∀ l, CdRange S l → l < cpB1 → upsilon l = l → ¬ CpIso l →
      cdTheta S l (cdCode S l) = VzOrec l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → CpOut2 l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  cdRoad (cpUPPER3 hU (fxTHfix hT)) (cpLOWER3 hL (fxTHfix hT)) (fxCapV hV) hC hEQ hrest hB2

end Googology.Trans.PoR.InaccPsi.R2.Fx
