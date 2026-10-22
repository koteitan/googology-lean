import Googology.Trans.PoR.InaccPsi.R2.GbW

/-!
# The ladder over the limit base `gbWB` (top `Γ_{x+ω}`): BLK^O, reaches, ENUM-REACH and the road

The generic ladder (`R2.LpTm` … `R2.LpFam`) over the base `gbWB` of `R2.GbW`: the stage systems `lpSys gbWB n` with
tops `gP gbWB 0 = ϑˣ(Ω₁·Ω₁ + ω)`, `gP gbWB (n+1) = ϑˣ(Ω₁·gP gbWB n)`, and `Λ^W = sup_n Λ⁺(lpSys gbWB n)`:

* `gb_O_low` (**`O_{lpSys gbWB n} = O_{gbUSys}` below `Λ⁺(gbUSys)`**), `gb_T_low` (**the notation hypothesis
  `Θ_F(m_F) = O_n(F)` at every fixed point of the range below `ι(Γ_{Ω₁+ω})`**, from `Ga.gaTowT_fix`);
* `gb_order` (**`ι(Γ_{Ω₁+ω}) < Λ⁺(gbUSys) < Λ⁺(lpSys gbWB 1) < Λ^W < Ω₁`**);
* `gbBlk` (**BLK^O below `υ_{Λ^W}`** with the exact reaches `lh(ρ_λ) = δ_λ + O_n(λ)`), `gbInit` (**ENUM-REACH at every
  non-fixed restart of the range below `Λ^W`**), `gbCapV` (CapV there), `gbEnum_low` / `gbCapV_low` (both with the
  fixed points below `ι(Γ_{Ω₁+ω})`);
* `gbRoad` (**the successor road**: UPPER/LOWER asked only at `λ ≥ Λ^W`, the notation hypothesis only at the fixed
  points in `[ι(Γ_{Ω₁+ω}), Λ^W)`, CapV only at the outer restarts `λ ≥ ι(Γ_{Ω₁+ω})`).

No new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gb

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Ly Googology.Trans.PoR.InaccPsi.R2.Lp
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp Googology.Trans.PoR.InaccPsi.R2.Bt

/-- **`O_{lpSys gbWB n} = O_{gbUSys}` below `Λ⁺(gbUSys)`.** -/
theorem gb_O_low (n : ℕ) {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlK : l < xtB1 gbUSys)
    (hln : l < lpLam gbWB n) : xtOrec (lpSys gbWB n) l = xtOrec gbUSys l := by
  have h1 : xtOrec (lpSys gbWB 1) l = xtOrec gbUSys l := lp_eq_K (B := gbWB) hl hlK
  rcases n with _ | n
  · rw [← h1]
    exact (Googology.Trans.PoR.InaccPsi.R2.Lp.lp_eq (B := gbWB) 0 hl hln).symm
  · rw [lp_eq_le gbWB (Nat.succ_le_succ (Nat.zero_le n)) hl (hlK.trans (lpB1_gt_K (B := gbWB) 0))]
    exact h1

variable {S : InaccSeq.{0}}

/-- **The notation hypothesis at every fixed point of the range below `ι(Γ_{Ω₁+ω})`**, for every stage. -/
theorem gb_T_low (n : ℕ) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S Ga.gaW)
    (hln : l < lpLam gbWB n) (hfix : upsilon l = l) :
    cdTheta S l (cdCode S l) = xtOrec (lpSys gbWB n) l := by
  have hlT : l < lpTowFam.famSup := by rw [(Ga.gaTowSup (S := S)).1]; exact hl
  obtain ⟨k, hk⟩ := lpTowFam.famLt hlT
  rw [gb_O_low n hr.1 (hlT.trans (gb_towSup_lt S).2) hln, gb_tow_eq k hr.1 hk]
  exact Ga.gaTowT_fix k hr hk hfix

/-- **The order of the new frontiers**: `ι(Γ_{Ω₁+ω}) < Λ⁺(gbUSys) < Λ⁺(lpSys gbWB 1) < Λ^W < Ω₁`. -/
theorem gb_order : iota S Ga.gaW < xtB1 gbUSys ∧ xtB1 gbUSys < xtB1 (lpSys gbWB 1) ∧
    xtB1 (lpSys gbWB 1) < (lpFam gbWB).famSup ∧ (lpFam gbWB).famSup < Om1 :=
  ⟨(gb_towSup_lt S).1, lpB1_gt_K (B := gbWB) 0, (lpFam gbWB).famBd_lt 1, (lpFam gbWB).famSup_lt_Om1⟩

omit S in
/-- **Theorem BLK^O below `υ_{Λ^W}`** in `R₂^C`, with the exact reaches `lh(ρ_λ) = δ_λ + O_n(λ)`. -/
theorem gbBlk :
    (∀ c d, c < d → d < upsilon (lpFam gbWB).famSup → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < (lpFam gbWB).famSup ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → ∀ k, l < lpLam gbWB k →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec (lpSys gbWB k) l)) ∧
    (∀ α < upsilon (lpFam gbWB).famSup, ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  lpFam_blk gbWB

/-- **ENUM-REACH at every non-fixed restart of the range below `Λ^W`.** -/
theorem gbInit {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < (lpFam gbWB).famSup) (hfix : l < upsilon l) :
    CdUpper S l ∧ CdLower S l :=
  lpFam_init gbWB hr hl hfix

/-- **CapV at every non-fixed restart of the range below `Λ^W`.** -/
theorem gbCapV {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < (lpFam gbWB).famSup) (hfix : l < upsilon l) :
    CdCapV S l :=
  lpFam_capV gbWB hr hl hfix

/-- **ENUM-REACH at every restart of the range below `Λ^W` that is non-fixed or below `ι(Γ_{Ω₁+ω})`.** -/
theorem gbEnum_low {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < (lpFam gbWB).famSup)
    (h : l < upsilon l ∨ l < iota S Ga.gaW) : CdUpper S l ∧ CdLower S l := by
  rcases h with h | h
  · exact gbInit hr hl h
  · exact Ga.gaTowEnum hr h

/-- **ENUM-REACH at every restart of the range below `Λ^W`, fixed points included**, given the notation hypothesis
only at the fixed points in `[ι(Γ_{Ω₁+ω}), Λ^W)`. -/
theorem gbEnum (hT : ∀ n l, CdRange S l → iota S Ga.gaW ≤ l → l < lpLam gbWB n → upsilon l = l →
      cdTheta S l (cdCode S l) = xtOrec (lpSys gbWB n) l)
    {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < (lpFam gbWB).famSup) : CdUpper S l ∧ CdLower S l :=
  lpFamEnum gbWB (fun n l hr hln hfix => by
    rcases lt_or_ge l (iota S Ga.gaW) with h | h
    · exact gb_T_low n hr h hln hfix
    · exact hT n l hr h hln hfix) hr hl

/-- **The successor road over the limit base**: UPPER and LOWER asked only at `λ ≥ Λ^W`, the notation hypothesis only
at the fixed points in `[ι(Γ_{Ω₁+ω}), Λ^W)`, CapV only at the outer restarts `λ ≥ ι(Γ_{Ω₁+ω})`, (CL), EQ, TCrest,
(EMB₂). -/
theorem gbRoad (hU : ∀ l, CdRange S l → (lpFam gbWB).famSup ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → (lpFam gbWB).famSup ≤ l → CdLower S l)
    (hT : ∀ n l, CdRange S l → iota S Ga.gaW ≤ l → l < lpLam gbWB n → upsilon l = l →
      cdTheta S l (cdCode S l) = xtOrec (lpSys gbWB n) l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut (lpFam gbWB).famSup l → iota S Ga.gaW ≤ l →
      CdCapV S l)
    (hC : CdCL S) (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  refine lpFamRoad3 gbWB hU hL (fun n l hr hln hfix => ?_) (fun l hr hlω hout => ?_) hC hEQ hrest hB2
  · rcases lt_or_ge l (iota S Ga.gaW) with h | h
    · exact gb_T_low n hr h hln hfix
    · exact hT n l hr h hln hfix
  · rcases lt_or_ge l (iota S Ga.gaW) with h | h
    · exact Ga.gaTowCapV hr h
    · exact hV l hr hlω hout h

end Googology.Trans.PoR.InaccPsi.R2.Gb
