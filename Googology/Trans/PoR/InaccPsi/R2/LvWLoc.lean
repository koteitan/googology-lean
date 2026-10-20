import Googology.Trans.PoR.InaccPsi.R2.LvWRd

/-!
# The exact place of the first limit of frontiers of `lvwSys`

By `Fp.fpB1_eq` of `R2.FpLoc`: `lvw_loc` (**`Λ⁺(lvwSys) = ι(φ(Ω₁·ω, 0)·ω)`, `ρ_{Λ⁺(lvwSys)} = P(φ(Ω₁·ω, 0)·ω) <
L(0)`**).

No new axiom beyond `R2.CitedLu` and `R2.CitedLv`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Ph Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm Lu

variable {S : InaccSeq.{0}}

/-- `ϑˣ(Ω₁·(x + x)) < ϑˣ(Ω₁·(x·ω))`. -/
theorem lvw_lvTop_lt {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : lvTop x < lvwTop x := by
  have hL : lvwL x 1 0 = x + x := by unfold lvwL; rw [add_zero, Nat.cast_one, mul_add_one, mul_one]
  have h := (LvWT.lvw_T hx hx1 (LvWT.th 1 0 (LvWT.cst 0)) ⟨hx.pos, hx.pos⟩).2
  simp only [LvWT.val_th, LvWT.val_cst, add_zero, hL] at h
  exact h

/-- **`Λ⁺(lvwSys) = ι(φ(Ω₁·ω, 0)·ω)`, `ρ_{Λ⁺(lvwSys)} = P(φ(Ω₁·ω, 0)·ω) < L(0)`.** -/
theorem lvw_loc : xtB1 lvwSys = iota S (lvwTc * ω) ∧ upsilon (xtB1 lvwSys) = Pv S (lvwTc * ω) ∧
    Pv S (lvwTc * ω) < Nc.ncL S 0 := by
  have hw0 : Om (1 : Ordinal.{0}) * ω ≠ 0 :=
    (mul_pos (zero_lt_one.trans (gg_one_lt_of_SC ph_SC_Om1)) omega0_pos).ne'
  have e : ω ^ lvwTc = lvwTc := gg_veblen_eps hw0
  have h := Fp.fpB1_eq (S := S) lvw_T_lt_Gam lvwPoly (fun _ hy hy1 => (lvwTh_T hy hy1).symm)
    (fun _ hZ => lvw_cl_T hZ) lvw_Om1_le_T
    (fun _ hx hx1 => ((lv_eN_lt_luTop hx hx1).trans (lv_luTop_lt hx hx1)).trans (lvw_lvTop_lt hx hx1))
    lvwSys_topPkg
  rwa [e] at h

end Googology.Trans.PoR.InaccPsi.R2
