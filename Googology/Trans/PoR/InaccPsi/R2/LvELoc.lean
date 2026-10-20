import Googology.Trans.PoR.InaccPsi.R2.LvERd

/-!
# The exact place of the first limit of frontiers of `lveSys`

By `Fp.fpB1_eq` of `R2.FpLoc`: `lve_loc` (**`Λ⁺(lveSys) = ι(φ(ε_{Ω₁+1}, 0)·ω)`, `ρ_{Λ⁺(lveSys)} =
P(φ(ε_{Ω₁+1}, 0)·ω) < L(0)`**).

No new axiom beyond `R2.CitedLu` and `R2.CitedLv`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Ph Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm Lu

variable {S : InaccSeq.{0}}

/-- `ϑˣ(Ω₁·(x·ω)) < ϑˣ(Ω₁·ε_{x+1})`. -/
theorem lve_lvwTop_lt {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : lvwTop x < lveTop x := by
  have hL : LvET.val (.pw (.sm .bs (.cst 1))) x = x * ω := by
    simp only [LvET.val_pw, LvET.val_sm, LvET.val_bs, LvET.val_cst]
    rw [opow_add, opow_one, show ω ^ x = x from hx]
  have h := (LvET.lve_T hx hx1 (LvET.tl (.pw (.sm .bs (.cst 1))) (.cst 0))
    ⟨⟨trivial, trivial⟩, Or.inl trivial, ⟨trivial, lu_one_lt_E hx⟩, hx.pos⟩).2
  simp only [LvET.val_tl, LvET.val_cst, add_zero, hL] at h
  exact h

/-- **`Λ⁺(lveSys) = ι(φ(ε_{Ω₁+1}, 0)·ω)`, `ρ_{Λ⁺(lveSys)} = P(φ(ε_{Ω₁+1}, 0)·ω) < L(0)`.** -/
theorem lve_loc : xtB1 lveSys = iota S (lveTc * ω) ∧ upsilon (xtB1 lveSys) = Pv S (lveTc * ω) ∧
    Pv S (lveTc * ω) < Nc.ncL S 0 := by
  have hv0 : veblen 1 (Om (1 : Ordinal.{0}) + 1) ≠ 0 := veblen_pos.ne'
  have e : ω ^ lveTc = lveTc := gg_veblen_eps hv0
  have h := Fp.fpB1_eq (S := S) lve_T_lt_Gam lvePoly (fun _ hy hy1 => (lveTh_T hy hy1).symm)
    (fun _ hZ => lve_cl_T hZ) lve_Om1_le_T
    (fun _ hx hx1 => (((lv_eN_lt_luTop hx hx1).trans (lv_luTop_lt hx hx1)).trans (lvw_lvTop_lt hx hx1)).trans
      (lve_lvwTop_lt hx hx1))
    lveSys_topPkg
  rwa [e] at h

end Googology.Trans.PoR.InaccPsi.R2
