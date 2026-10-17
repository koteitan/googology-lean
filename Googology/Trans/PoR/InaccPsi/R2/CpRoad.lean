import Googology.Trans.PoR.InaccPsi.R2.CdNu
import Googology.Trans.PoR.InaccPsi.R2.CpFix

/-!
# The road to `ν_C = L(ω+1)` with ENUM-REACH proved below `cpB1` off the fixed points of `υ`

`R2.CpUp` proves UPPER, LOWER, the cap of the value and the cap (`CdCapAt`) at every restart `λ` of the range
with `λ < cpB1` and `λ < υ_λ`.  A restart index `λ` is **outside** (`CpOut λ`) if `cpB1 ≤ λ` or `υ_λ = λ`; every
restart index is outside or covered (`cpOut_or`).  The hypotheses of the road of `R2.CdNu` are needed only
outside:

* `CpUPPERout`, `CpLOWERout`, `CpCapVout`: UPPER, LOWER, the cap of the value at the outside restarts of the
  range (the last one below `L(ω)`); `CpCAP0out`, `CpCAP1out`: the caps at the outside restarts of levels 1
  and 2 (from `B₀`, level 2 below `L(ω)` with code `< P'`);
* `cpUPPER`, `cpLOWER`, `cpCapV`, `cpCAP0`, `cpCAP1`: these give `CdUPPER`, `CdLOWER`, the cap of the values
  below `L(ω)`, `CdCAP0`, `CdCAP1 (L(ω))`;
* `cpLow` (**NU-LOW″**): `CpCAP0out` and `CpCAP1out` give `L(ω) ≤ ν_C`;
* `cpRoad`, `cpRoad_cross`, `cpRoad_cap`: the conclusions of `cdRoad`, `cdRoad_cross`, `cdRoad_cap`
  (`ν_C = L(ω+1)`, `L(ω) ≤ ν_C`, `L(ω) <₂ L(ω+1)`, (P), (Q), `lh(L(ω)) = lh(L(n+1)) = L(ω+1)`) with the
  hypotheses UPPER, LOWER, the cap of the values, CAP-0 and CAP-1 asked only outside;
* `CpOut2`, `CpUPPERout2`, `CpCODEfix`, `cpUPPER2`, `cpRoad2` (**UPPER at the isolated fixed points from the
  code**, `R2.CpFix`): UPPER is asked only at `λ ≥ cpB1` and at the fixed points of `υ` that are limits of
  fixed points; at the isolated fixed points `F < cpB1` of the range it is replaced by the statement
  `F ≤ m_F` on the code (no `≤₁` in it);
* `CpUPPERhigh`, `CpLOWERhigh`, `CpTHfix`, `cpUPPER3`, `cpLOWER3`, `cpRoad3` (**below `cpB1` only the
  notation is left**): UPPER and LOWER are asked only at `λ ≥ cpB1`; at the fixed points `F < cpB1` of the
  range they are replaced by the equation `Θ_F(m_F) = VzOrec(F)` between the reading of the code and the offset
  (`cpExact_iff`).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Cp

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Cd

/-- `λ` is **outside** the covered part: `cpB1 ≤ λ` or `λ` is a fixed point of `υ`. -/
def CpOut (l : Ordinal.{0}) : Prop := cpB1 ≤ l ∨ upsilon l = l

/-- UPPER at the outside restarts of the range. -/
def CpUPPERout (S : InaccSeq.{0}) : Prop := ∀ l, CdRange S l → CpOut l → CdUpper S l

/-- LOWER at the outside restarts of the range. -/
def CpLOWERout (S : InaccSeq.{0}) : Prop := ∀ l, CdRange S l → CpOut l → CdLower S l

/-- The cap of the value at the outside restarts of the range below `L(ω)`. -/
def CpCapVout (S : InaccSeq.{0}) : Prop :=
  ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → CpOut l → CdCapV S l

/-- CAP-0 at the outside restarts. -/
def CpCAP0out (S : InaccSeq.{0}) : Prop :=
  ∀ l, IsRestartIdx l → cdB0 ≤ l → upsilon l < cdMstar S → CpOut l → CdCapAt S l

/-- CAP-1 below `X` at the outside restarts. -/
def CpCAP1out (S : InaccSeq.{0}) (X : Ordinal.{0}) : Prop :=
  ∀ l, IsRestartIdx l → cdB0 ≤ l → cdMstar S ≤ upsilon l → upsilon l < X →
    cdCode S l < Nc.ncPp S → CpOut l → CdCapAt S l

variable {S : InaccSeq.{0}}

/-- Every index is outside, or below `cpB1` and not a fixed point of `υ`. -/
theorem cpOut_or (l : Ordinal.{0}) : CpOut l ∨ (l < cpB1 ∧ l < upsilon l) := by
  rcases le_or_gt cpB1 l with h | h
  · exact Or.inl (Or.inl h)
  · rcases (upsilon_normal.strictMono.le_apply : l ≤ upsilon l).lt_or_eq with h' | h'
    · exact Or.inr ⟨h, h'⟩
    · exact Or.inl (Or.inr h'.symm)

theorem cp_name_L {l : Ordinal.{0}} (h : upsilon l < Nc.ncL S (ω + 1)) :
    upsilon l < Pv S (Om ω + Nc.ncPp S * (ω + 1)) := Lw.lw_L_eq S (ω + 1) ▸ h

/-- **UPPER on the range from UPPER outside.** -/
theorem cpUPPER (hU : CpUPPERout S) : CdUPPER S := fun l hr => by
  rcases cpOut_or l with h | ⟨hlB, hfix⟩
  · exact hU l hr h
  · exact (cpUPPER_init hr hlB hfix).1

/-- **LOWER on the range from LOWER outside.** -/
theorem cpLOWER (hL : CpLOWERout S) : CdLOWER S := fun l hr => by
  rcases cpOut_or l with h | ⟨hlB, hfix⟩
  · exact hL l hr h
  · exact (cpUPPER_init hr hlB hfix).2

/-- **The cap of the values below `L(ω)` from the cap outside.** -/
theorem cpCapV (hV : CpCapVout S) : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → CdCapV S l :=
  fun l hr hX => by
    rcases cpOut_or l with h | ⟨hlB, hfix⟩
    · exact hV l hr hX h
    · exact cpCapV_nonfix hr.1 (cp_ww_lt_B0.trans_le hr.2.1) hfix hlB (cp_name_L hr.2.2.1)

/-- **CAP-0 from CAP-0 outside.** -/
theorem cpCAP0 (h0 : CpCAP0out S) : CdCAP0 S := fun l hl hB hlev => by
  rcases cpOut_or l with h | ⟨hlB, hfix⟩
  · exact h0 l hl hB hlev h
  · exact cpCapAt_nonfix hl (cp_ww_lt_B0.trans_le hB) hfix hlB hlev

/-- **CAP-1 below `L(ω)` from CAP-1 outside.** -/
theorem cpCAP1 (h1 : CpCAP1out S (Nc.ncL S ω)) : CdCAP1 S (Nc.ncL S ω) :=
  fun l hl hB hlev hX hc => by
    rcases cpOut_or l with h | ⟨hlB, hfix⟩
    · exact h1 l hl hB hlev hX hc h
    · exact cpCapAt_nonfix hl (cp_ww_lt_B0.trans_le hB) hfix hlB (Lw.lw_L_eq S ω ▸ hX)

/-- **NU-LOW″ from the caps outside**: `L(ω) ≤ ν_C`. -/
theorem cpLow (h0 : CpCAP0out S) (h1 : CpCAP1out S (Nc.ncL S ω)) : Nc.ncL S ω ≤ nuC :=
  cdLow (cpCAP0 h0) (cpCAP1 h1)

/-- **The road with ENUM-REACH asked only outside.** -/
theorem cpRoad (hU : CpUPPERout S) (hL : CpLOWERout S) (hV : CpCapVout S) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  cdRoad (cpUPPER hU) (cpLOWER hL) (cpCapV hV) hC hEQ hrest hB2

/-- **The same with the crossing step `CdCROSS` in place of (CL).** -/
theorem cpRoad_cross (hU : CpUPPERout S) (hL : CpLOWERout S) (hV : CpCapVout S) (hx : CdCROSS S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  cdRoad_cross (cpUPPER hU) (cpLOWER hL) (cpCapV hV) hx hEQ hrest hB2

/-- **The road with the caps asked only outside**: CAP-0, CAP-1 outside, (CL), (TC), (EMB₂). -/
theorem cpRoad_cap (h0 : CpCAP0out S) (h1 : CpCAP1out S (Nc.ncL S ω)) (hC : CdCL S) (hTC : CdTC S)
    (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  cdRoad_cap (cpCAP0 h0) (cpCAP1 h1) hC hTC hB2

/-- `λ` is outside the covered part and not an isolated fixed point below `cpB1`. -/
def CpOut2 (l : Ordinal.{0}) : Prop := cpB1 ≤ l ∨ (upsilon l = l ∧ ¬ CpIso l)

/-- UPPER at the restarts of the range that are `≥ cpB1` or fixed points of `υ` that are limits of fixed
points. -/
def CpUPPERout2 (S : InaccSeq.{0}) : Prop := ∀ l, CdRange S l → CpOut2 l → CdUpper S l

/-- **The code at the isolated fixed points**: `F ≤ m_F` at every isolated fixed point `F < cpB1` of `υ` in the
range. -/
def CpCODEfix (S : InaccSeq.{0}) : Prop :=
  ∀ l, CdRange S l → l < cpB1 → upsilon l = l → CpIso l → l ≤ cdCode S l

/-- **UPPER on the range from UPPER at `λ ≥ cpB1` and at the non-isolated fixed points, and the code at the
isolated fixed points.** -/
theorem cpUPPER2 (hU : CpUPPERout2 S) (hc : CpCODEfix S) : CdUPPER S := fun l hr => by
  rcases cpOut_or l with (h | h) | ⟨hlB, hfix⟩
  · exact hU l hr (Or.inl h)
  · by_cases hiso : CpIso l
    · rcases le_or_gt cpB1 l with hB | hlB
      · exact hU l hr (Or.inl hB)
      · exact (cpFix_code hr.1 h hlB hiso (cp_name_L hr.2.2.1)).1 (hc l hr hlB h hiso)
    · exact hU l hr (Or.inr ⟨h, hiso⟩)
  · exact (cpUPPER_init hr hlB hfix).1

/-- **The road with UPPER asked only at `λ ≥ cpB1` and at the non-isolated fixed points**, the code at the
isolated fixed points, LOWER and the cap of the values outside, (CL), EQ, TCrest, (EMB₂). -/
theorem cpRoad2 (hU : CpUPPERout2 S) (hc : CpCODEfix S) (hL : CpLOWERout S) (hV : CpCapVout S)
    (hC : CdCL S) (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  cdRoad (cpUPPER2 hU hc) (cpLOWER hL) (cpCapV hV) hC hEQ hrest hB2

/-- UPPER at the restarts `λ ≥ cpB1` of the range. -/
def CpUPPERhigh (S : InaccSeq.{0}) : Prop := ∀ l, CdRange S l → cpB1 ≤ l → CdUpper S l

/-- LOWER at the restarts `λ ≥ cpB1` of the range. -/
def CpLOWERhigh (S : InaccSeq.{0}) : Prop := ∀ l, CdRange S l → cpB1 ≤ l → CdLower S l

/-- **The notation at the fixed points below `cpB1`**: `Θ_F(m_F) = VzOrec(F)` at every fixed point `F < cpB1`
of `υ` in the range. -/
def CpTHfix (S : InaccSeq.{0}) : Prop :=
  ∀ l, CdRange S l → l < cpB1 → upsilon l = l → cdTheta S l (cdCode S l) = VzOrec l

/-- **UPPER on the range from UPPER at `λ ≥ cpB1` and the notation at the fixed points below `cpB1`.** -/
theorem cpUPPER3 (hU : CpUPPERhigh S) (hT : CpTHfix S) : CdUPPER S := fun l hr => by
  rcases le_or_gt cpB1 l with hB | hlB
  · exact hU l hr hB
  · rcases cpOut_or l with (h | h) | ⟨-, hfix⟩
    · exact absurd h (not_le.2 hlB)
    · exact ((cpExact_iff hr.1 hlB).2 (hT l hr hlB h)).1
    · exact (cpUPPER_init hr hlB hfix).1

/-- **LOWER on the range from LOWER at `λ ≥ cpB1` and the notation at the fixed points below `cpB1`.** -/
theorem cpLOWER3 (hL : CpLOWERhigh S) (hT : CpTHfix S) : CdLOWER S := fun l hr => by
  rcases le_or_gt cpB1 l with hB | hlB
  · exact hL l hr hB
  · rcases cpOut_or l with (h | h) | ⟨-, hfix⟩
    · exact absurd h (not_le.2 hlB)
    · exact ((cpExact_iff hr.1 hlB).2 (hT l hr hlB h)).2
    · exact (cpUPPER_init hr hlB hfix).2

/-- **The road with UPPER and LOWER asked only at `λ ≥ cpB1`** and the notation `Θ_F(m_F) = VzOrec(F)` at
the fixed points below `cpB1`, the cap of the values outside, (CL), EQ, TCrest, (EMB₂). -/
theorem cpRoad3 (hU : CpUPPERhigh S) (hL : CpLOWERhigh S) (hT : CpTHfix S) (hV : CpCapVout S)
    (hC : CdCL S) (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  cdRoad (cpUPPER3 hU hT) (cpLOWER3 hL hT) (cpCapV hV) hC hEQ hrest hB2

end Googology.Trans.PoR.InaccPsi.R2.Cp
