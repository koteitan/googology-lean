import Googology.Trans.PoR.InaccPsi.R2.GdDiag

/-!
# Below the diagonal frontier: ENUM-REACH and CapV off the fixed points, and the road

For the diagonal layer `gdDSys` (top `Γ_{x+x}`, `R2.GdDiag`) the generic theorems of `R2.XtEnum` give, unconditionally:

* `gdD_nonfix` (`O_D(μ) = -1 + e(μ)` at every restart `ω² < μ < Λ⁺(gdDSys)` that is not a fixed point of `υ`);
* `gdD_init` (**ENUM-REACH: UPPER and LOWER at every range restart `λ < Λ⁺(gdDSys)` that is not a fixed point**),
  `gdD_capV` (**CapV there**);
* `gdD_fixLow` (**at the fixed points below `ι(Γ_{Ω₁+ε₀})`: `Θ_F(m_F) = O_D(F)`**, from `Gc.gcBT_fix` and
  `O_D = O_{gcB α}`), `gdD_enumLow`, `gdD_capVLow` (ENUM-REACH and CapV at every range restart below `ι(Γ_{Ω₁+ε₀})`,
  fixed points included, `Gc.gcEnum`, `Gc.gcCapV`);
* `gdD_road` (**THE ROAD past the diagonal**: UPPER and LOWER asked only at `λ ≥ Λ⁺(gdDSys)`, the notation
  `Θ_F(m_F) = O_D(F)` only at the fixed points `F ∈ [ι(Γ_{Ω₁+ε₀}), Λ⁺(gdDSys))`, CapV only at `λ ≥ Λ⁺(gdDSys)` and
  at those fixed points, (CL), EQ, TCrest, (EMB₂) ⟹ `ν_C = L(ω+1)`, `L(ω) ≤ ν_C`, `L(ω) <₂ L(ω+1)`, (P), (Q), reaches).

No new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Ly
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp Googology.Trans.PoR.InaccPsi.R2.Bt
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gc

variable {S : InaccSeq.{0}}

theorem gdD_nonfix : XtNonfix (xtOrec gdDSys) (xtB1 gdDSys) :=
  fun _ hμ hww hfix hμB => xtNonfix hμ hww hfix (hμB.trans gdD_B1_lt_Om1)

/-- **ENUM-REACH at every non-fixed range restart below `Λ⁺(gdDSys)`.** -/
theorem gdD_init {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtB1 gdDSys) (hfix : l < upsilon l) :
    CdUpper S l ∧ CdLower S l :=
  xtInit gdD_spec gdD_nonfix hr hl hfix

/-- **CapV at every non-fixed range restart below `Λ⁺(gdDSys)`.** -/
theorem gdD_capV {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtB1 gdDSys) (hfix : l < upsilon l) :
    CdCapV S l := by
  have hww := cp_ww_lt_B0.trans_le hr.2.1
  exact xtCapV_nonfix gdD_spec hr.1 hww hfix hl (cp_name_L hr.2.2.1) (gdD_nonfix l hr.1 hww hfix hl)

/-- **`Θ_F(m_F) = O_D(F)` at every fixed range restart `F < ι(Γ_{Ω₁+ε₀})`.** -/
theorem gdD_fixLow {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S gcV) (hfix : upsilon l = l) :
    cdTheta S l (cdCode S l) = xtOrec gdDSys l := by
  rw [← (gcFamSup (S := S)).1] at hl
  obtain ⟨k, hk⟩ := gcFam.famLt hl
  rw [gdD_eq_gc (gcSeq_one_add k) hr.1 hk]
  exact gcBT_fix S (gcSeq_one_add k) hr hk hfix

/-- **ENUM-REACH and CapV at every range restart below `ι(Γ_{Ω₁+ε₀})`, fixed points included.** -/
theorem gdD_enumLow {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S gcV) :
    (CdUpper S l ∧ CdLower S l) ∧ CdCapV S l :=
  ⟨gcEnum hr hl, gcCapV hr hl⟩

/-- **THE ROAD past the diagonal**: UPPER and LOWER asked only at `λ ≥ Λ⁺(gdDSys)`; the notation `Θ_F(m_F) = O_D(F)`
only at the fixed points `F ∈ [ι(Γ_{Ω₁+ε₀}), Λ⁺(gdDSys))`; CapV only at `λ ≥ Λ⁺(gdDSys)` and at those fixed points. -/
theorem gdD_road (hU : ∀ l, CdRange S l → xtB1 gdDSys ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → xtB1 gdDSys ≤ l → CdLower S l)
    (hT : ∀ l, CdRange S l → iota S gcV ≤ l → l < xtB1 gdDSys → upsilon l = l →
      cdTheta S l (cdCode S l) = xtOrec gdDSys l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → (xtB1 gdDSys ≤ l ∨ (upsilon l = l ∧ iota S gcV ≤ l)) →
      CdCapV S l)
    (hC : CdCL S) (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  refine xtRoad3 gdD_spec gdD_nonfix hU hL (fun l hr hlB hfix => ?_) (fun l hr hX hout => ?_) hC hEQ hrest hB2
  · rcases lt_or_ge l (iota S gcV) with h | h
    · exact gdD_fixLow hr h hfix
    · exact hT l hr h hlB hfix
  · rcases hout with h | h
    · exact hV l hr hX (Or.inl h)
    · rcases lt_or_ge l (iota S gcV) with h' | h'
      · exact gcCapV hr h'
      · exact hV l hr hX (Or.inr ⟨h, h'⟩)

end Googology.Trans.PoR.InaccPsi.R2.Gd
