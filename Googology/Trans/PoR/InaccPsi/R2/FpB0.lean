import Googology.Trans.PoR.InaccPsi.R2.RmNamed
import Googology.Trans.PoR.InaccPsi.R2.PhFr

/-!
# `ρ_{B₀} < m*`, and the realizer road without it

`L(ξ) = Nc.ncL S ξ`, `m* = L(0)`, `B₀ = Cd.cdB0 = Λ_B + ω²` (`Λ_B = VzLam`), `ρ_λ = υ_λ`.

* `fpLamB_lt_M` (**`Λ_B ≤ ι(phB) < L(0)`**: `Ph.phFr_vz`, `Ph.phIota_lt_L0`), `fpB0_lt_M'` (`B₀ < L(0)`, `L(0)` is
  an `ε`-number), `fpB0_lt_M` (**`ρ_{B₀} < m*`**, since `υ` fixes `m*`, `Rm.rm_M_fix`);
* `fpCof_named` (**`RmCof` at `m*`, at every `L(n+1)` and at `L(ω)`**), `fpReal_named` (**`RlReal` at the three
  points for every target `t ≤ a·ω^ω`**): `Rm.rmNamed_cof_iff`, `Rm.rmNamed_real` without their hypothesis;
* `FpRealHi S a b` (the realizer maps for the targets above `a·ω^ω` only), `fpRealCof_iff` (**at the named points,
  `RlRealCof S a b ↔ FpRealHi S a b`**: the targets `t ≤ a·ω^ω` are covered by `Rm.rmReal_lin`);
* `fpNamed_of_real`, `fpRoad_front`, `fpRoad_rz` (**`Rl.rlNamed_of_real`, `Rl.rlRoad_front`, `Rl.rlRoad_rz` with
  the realizer hypotheses asked only for the targets above `a·ω^ω`**).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Fp

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Rl
  Googology.Trans.PoR.InaccPsi.R2.Rm Googology.Trans.PoR.InaccPsi.R2.Cv Googology.Trans.PoR.InaccPsi.R2.Cx

variable {S : InaccSeq.{0}}

/-! ## `ρ_{B₀} < m*` -/

/-- **`Λ_B < L(0)`**: `Λ_B ≤ ι(phB) < L(0)`. -/
theorem fpLamB_lt_M : VzLam < Nc.ncL S 0 :=
  (Ph.phFr_vz (S := S)).2.1.trans_lt (Ph.phIota_lt_L0 (S := S) (fun _ hZ => Ph.ph_cl_B hZ)).1

/-- **`B₀ = Λ_B + ω² < L(0)`**. -/
theorem fpB0_lt_M' : cdB0 < Nc.ncL S 0 := by
  have hE := rm_L_inE (S := S) 0
  have hw : ω < Nc.ncL S 0 := omega0_lt_inE hE
  exact rm_prin hE fpLamB_lt_M (mul_lt_inE hE hw hw)

/-- **`ρ_{B₀} < m*`.** -/
theorem fpB0_lt_M : upsilon cdB0 < Nc.ncL S 0 := by
  have h := upsilon_normal.strictMono (fpB0_lt_M' (S := S))
  rwa [rm_M_fix] at h

/-- **`RmCof` at `m*`, at every `L(n+1)` and at `L(ω)`.** -/
theorem fpCof_named :
    RmCof S (Nc.ncL S 0) ∧ (∀ n : ℕ, RmCof S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))) ∧
      RmCof S (Nc.ncL S ω) :=
  rmNamed_cof_iff.1 fpB0_lt_M

/-- **The realizer maps at `m*`, `L(n+1)`, `L(ω)` for every target `t ≤ a·ω^ω`.** -/
theorem fpReal_named :
    (∀ t, t ≤ Nc.ncL S 0 * ω ^ ω → RlReal S (Nc.ncL S 0) t) ∧
    (∀ n : ℕ, ∀ t, t ≤ Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) * ω ^ ω →
      RlReal S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) t) ∧
    (∀ t, t ≤ Nc.ncL S ω * ω ^ ω → RlReal S (Nc.ncL S ω) t) :=
  rmNamed_real fpB0_lt_M

/-! ## The realizer hypotheses above `a·ω^ω` -/

/-- **The realizer maps for the targets above `a·ω^ω` only.** -/
def FpRealHi (S : InaccSeq.{0}) (a b : Ordinal.{0}) : Prop :=
  ∀ y, a * ω ^ ω ≤ y → y < b → ∃ t, y < t ∧ t ≤ b ∧ RlReal S a t

/-- `a·ω^ω < b` for `a < b`, `b` an `ε`-number. -/
theorem fp_mul_lt {a b : Ordinal.{0}} (hb : InE b) (hab : a < b) : a * ω ^ ω < b := by
  have hw : ω ^ ω < b := by
    have h := (opow_lt_opow_iff_right one_lt_omega0).2 (omega0_lt_inE hb)
    rwa [show ω ^ b = b from hb] at h
  exact mul_lt_inE hb hab hw

/-- **`RlRealCof S a b ↔ FpRealHi S a b`** when `a ∈ E`, `RmCof S a` and `a·ω^ω ≤ b`. -/
theorem fpRealCof_iff {a b : Ordinal.{0}} (ha : InE a) (hc : RmCof S a) (hab : a * ω ^ ω ≤ b) :
    RlRealCof S a b ↔ FpRealHi S a b := by
  constructor
  · intro h y hy hyb
    exact h y ((le_mul_left a (opow_pos ω omega0_pos)).trans hy) hyb
  · intro h y hay hyb
    rcases lt_or_ge y (a * ω ^ ω) with h1 | h1
    · exact ⟨a * ω ^ ω, h1, hab, rmReal_lin ha hc le_rfl⟩
    · exact h y h1 hyb

theorem fpRealCof_M (h : FpRealHi S (Nc.ncL S 0) (Nc.ncL S 1)) : RlRealCof S (Nc.ncL S 0) (Nc.ncL S 1) :=
  (fpRealCof_iff (rm_L_inE 0) fpCof_named.1 (fp_mul_lt (rm_L_inE 1) rlM_lt_L1).le).2 h

theorem fpRealCof_n (n : ℕ)
    (h : FpRealHi S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))) :
    RlRealCof S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0})) :=
  (fpRealCof_iff (rm_L_inE _) (fpCof_named.2.1 n) (fp_mul_lt (rm_L_inE _) (Pp.ppL_lt_succ n)).le).2 h

theorem fpRealCof_w (h : FpRealHi S (Nc.ncL S ω) (Nc.ncL S (ω + 1))) :
    RlRealCof S (Nc.ncL S ω) (Nc.ncL S (ω + 1)) :=
  (fpRealCof_iff (rm_L_inE _) fpCof_named.2.2 (fp_mul_lt (rm_L_inE _) (Qq.qqL_lt_succ S)).le).2 h

/-! ## The realizer road with the hypotheses above `a·ω^ω` -/

/-- **`CxNamed` from the realizer maps above `a·ω^ω`** (`Rl.rlNamed_of_real`). -/
theorem fpNamed_of_real (hL : CdLOWER S) (hlow : Nc.ncL S ω ≤ nuC)
    (h0 : FpRealHi S (Nc.ncL S 0) (Nc.ncL S 1))
    (hn : ∀ n : ℕ, FpRealHi S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0})))
    (hP : CvNoPair (Nc.ncL S ω) (Nc.ncL S (ω + 1)))
    (hw : FpRealHi S (Nc.ncL S ω) (Nc.ncL S (ω + 1))) : CxNamed S :=
  rlNamed_of_real hL hlow (fpRealCof_M h0) (fun n => fpRealCof_n n (hn n)) hP (fpRealCof_w hw)

/-- **`Rl.rlRoad_front` with the realizer hypotheses above `a·ω^ω`.** -/
theorem fpRoad_front (hU : CdUPPER S) (hL : CdLOWER S)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → CdCapV S l)
    (hEQ : CxEQtop S) (htop : CxTCtopOff S) (hups : CxUpsRestTop S)
    (h0 : FpRealHi S (Nc.ncL S 0) (Nc.ncL S 1))
    (hn : ∀ n : ℕ, FpRealHi S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0})))
    (hP : CvNoPair (Nc.ncL S ω) (Nc.ncL S (ω + 1)))
    (hw : FpRealHi S (Nc.ncL S ω) (Nc.ncL S (ω + 1)))
    (hmove : CxStdMoveTop S) (hstd : CxStdPairTop S) :
    CdEQ S ∧ CdTC S ∧ CdEMB2 S ∧ CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  rlRoad_front hU hL hV hEQ htop hups (fpRealCof_M h0) (fun n => fpRealCof_n n (hn n)) hP (fpRealCof_w hw)
    hmove hstd

/-- **`Rl.rlRoad_rz` with the realizer hypotheses above `a·ω^ω`.** -/
theorem fpRoad_rz (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hEQ : CxEQtop S) (htop : CxTCtopOff S) (hups : CxUpsRestTop S)
    (h0 : FpRealHi S (Nc.ncL S 0) (Nc.ncL S 1))
    (hn : ∀ n : ℕ, FpRealHi S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0})))
    (hP : CvNoPair (Nc.ncL S ω) (Nc.ncL S (ω + 1)))
    (hw : FpRealHi S (Nc.ncL S ω) (Nc.ncL S (ω + 1)))
    (hmove : CxStdMoveTop S) (hstd : CxStdPairTop S) :
    CdEQ S ∧ CdTC S ∧ CdEMB2 S ∧ CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  rlRoad_rz hU hO hL hV hEQ htop hups (fpRealCof_M h0) (fun n => fpRealCof_n n (hn n)) hP (fpRealCof_w hw)
    hmove hstd

end Googology.Trans.PoR.InaccPsi.R2.Fp
