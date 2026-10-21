import Googology.Trans.PoR.InaccPsi.R2.LkCap
import Googology.Trans.PoR.InaccPsi.R2.RlReal
import Googology.Trans.PoR.InaccPsi.R2.MwOm

/-!
# The roads `Rl.rlRoad_rz` and `Mw.mwRoad_w` with nothing asked below `Λ⁺(lvgSys n)`

`Rl.rlRoad_rz` and `Mw.mwRoad_w` ask UPPER, LOWER, CapV at the restarts `λ` of the range with `Λ_B⁺ ≤ λ` or
`λ = υ_λ` (`Rz.RzRest`), and `VzOrec(λ) ≤ c(λ)` at the other range restarts `λ < Λ_B⁺`.

* `lkOrec_cL` (**`VzOrec(λ) ≤ c(λ)` at every range restart `λ < Λ_B⁺` with `υ_λ ≠ λ`**, unconditional: UPPER there is
  `Ph.phEnum_cp`, and UPPER is `VzOrec(λ) ≤ c(λ)` there by `Rz.rzUpper_nonfix`);
* `lkU_rest`, `lkL_rest`, `lkV_rest`: the hypotheses at `Rz.RzRest` from the same hypotheses at `λ ≥ Λ⁺(lvgSys n)`
  (`lvgEnum`, `Lk.lkCapV_lvg` below);
* `lkRoad_rl` (**`Rl.rlRoad_rz` with UPPER, LOWER, CapV asked only at the range restarts `λ ≥ Λ⁺(lvgSys n)` and without
  `VzOrec ≤ c`**), `lkRoad_mw` (**the same for `Mw.mwRoad_w`**).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Lk

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Xt

variable {S : InaccSeq.{0}}

/-- **`VzOrec(λ) ≤ c(λ)` at every restart `λ < Λ_B⁺` of the range with `υ_λ ≠ λ`.** -/
theorem lkOrec_cL : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l := by
  intro l hr hl hfix
  exact (Rz.rzUpper_nonfix hr.1 hl hfix (Rz.rz_range_pv hr)).1.1 (Ph.phEnum_cp hr hl).1

/-- UPPER at `Rz.RzRest` from UPPER at `λ ≥ Λ⁺(lvgSys n)`. -/
theorem lkU_rest (n : ℕ) (hU : ∀ l, CdRange S l → xtB1 (lvgSys n) ≤ l → CdUpper S l) :
    ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l := by
  intro l hr _
  rcases lt_or_ge l (xtB1 (lvgSys n)) with h | h
  · exact (lvgEnum n hr h).1
  · exact hU l hr h

/-- LOWER at `Rz.RzRest` from LOWER at `λ ≥ Λ⁺(lvgSys n)`. -/
theorem lkL_rest (n : ℕ) (hL : ∀ l, CdRange S l → xtB1 (lvgSys n) ≤ l → CdLower S l) :
    ∀ l, CdRange S l → Rz.RzRest l → CdLower S l := by
  intro l hr _
  rcases lt_or_ge l (xtB1 (lvgSys n)) with h | h
  · exact (lvgEnum n hr h).2
  · exact hL l hr h

/-- CapV at `Rz.RzRest` below `L(ω)` from CapV at `λ ≥ Λ⁺(lvgSys n)` below `L(ω)`. -/
theorem lkV_rest (n : ℕ)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → xtB1 (lvgSys n) ≤ l → CdCapV S l) :
    ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l := by
  intro l hr hlω _
  rcases lt_or_ge l (xtB1 (lvgSys n)) with h | h
  · exact lkCapV_lvg n hr h
  · exact hV l hr hlω h

/-- **`Rl.rlRoad_rz` with UPPER, LOWER and CapV asked only at the range restarts `λ ≥ Λ⁺(lvgSys n)`, and without
`VzOrec ≤ c`.** -/
theorem lkRoad_rl (n : ℕ) (hU : ∀ l, CdRange S l → xtB1 (lvgSys n) ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → xtB1 (lvgSys n) ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → xtB1 (lvgSys n) ≤ l → CdCapV S l)
    (hEQ : Cx.CxEQtop S) (htop : Cx.CxTCtopOff S) (hups : Cx.CxUpsRestTop S)
    (h0 : Rl.RlRealCof S (Nc.ncL S 0) (Nc.ncL S 1))
    (hn : ∀ k : ℕ, Rl.RlRealCof S (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}))
      (Nc.ncL S ((k + 2 : ℕ) : Ordinal.{0})))
    (hP : Cv.CvNoPair (Nc.ncL S ω) (Nc.ncL S (ω + 1)))
    (hw : Rl.RlRealCof S (Nc.ncL S ω) (Nc.ncL S (ω + 1)))
    (hmove : Cx.CxStdMoveTop S) (hstd : Cx.CxStdPairTop S) :
    CdEQ S ∧ CdTC S ∧ CdEMB2 S ∧ Cx.CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  Rl.rlRoad_rz (lkU_rest n hU) lkOrec_cL (lkL_rest n hL) (lkV_rest n hV) hEQ htop hups h0 hn hP hw hmove hstd

/-- **`Mw.mwRoad_w` with UPPER, LOWER and CapV asked only at the range restarts `λ ≥ Λ⁺(lvgSys n)`, and without
`VzOrec ≤ c`.** -/
theorem lkRoad_mw (n : ℕ) (hU : ∀ l, CdRange S l → xtB1 (lvgSys n) ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → xtB1 (lvgSys n) ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → xtB1 (lvgSys n) ≤ l → CdCapV S l)
    (hN : Cx.CxNamed S) (hlh : Mw.MwLhTopW S) (htop : Nc.ncL S (ω + 1) ≤ nuC → Mw.MwEQtop S) :
    CdEQ S ∧ CdTC S ∧ CdEMB2 S ∧ Cx.CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  Mw.mwRoad_w (lkU_rest n hU) lkOrec_cL (lkL_rest n hL) (lkV_rest n hV) hN hlh htop

end Googology.Trans.PoR.InaccPsi.R2.Lk
