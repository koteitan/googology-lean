import Googology.Trans.PoR.InaccPsi.R2.LvRd
import Googology.Trans.PoR.InaccPsi.R2.FpLoc

/-!
# The exact place of the first limit of frontiers of `luSys` and `lvSys`

By `Fp.fpB1_eq` of `R2.FpLoc` (a system with top code `T`, `GgPoly X T`, `ε_{x+1} < top(x)` and an IMG package has
`Λ⁺(X) = ι(ω^T·ω)` and `ρ_{Λ⁺(X)} = P(ω^T·ω) < L(0)`):

* `lv_loc_luSys` (**`Λ⁺(luSys) = ι(φ(Ω₁, 1)·ω)`, `ρ_{Λ⁺(luSys)} = P(φ(Ω₁, 1)·ω) < L(0)`**);
* `lv_loc` (**`Λ⁺(lvSys) = ι(φ(Ω₁ + Ω₁, 0)·ω)`, `ρ_{Λ⁺(lvSys)} = P(φ(Ω₁ + Ω₁, 0)·ω) < L(0)`**), and with
  `lv_fr_order`: `L(0) = m* ≤ L(n+1) < L(ω) < L(ω+1)`.

No new axiom beyond `R2.CitedLu` and `R2.CitedLv`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Ph Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm Lu

variable {S : InaccSeq.{0}}

/-- `ε_{x+1} < ϑˣ(Ω₁·x)` for an `ε`-number `x < Ω₁`. -/
theorem lv_eN_lt_luTop {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : eN x < luTop x := by
  have h0T := lu_zero_T hx hx1
  obtain ⟨-, -, -, hxA, -, hAE, -, -⟩ := lu_th_facts hx hx1 le_rfl (lu_one_lt_E hx) h0T (Ordinal.omega_pos 1)
  exact (eN_le hxA hAE).trans_lt
    (lu_th_lt_top hx hx1 (lu_one_lt_E hx) h0T (Ordinal.omega_pos 1) (luTop_facts hx hx1).2.2.2.1.pos)

/-- `ϑˣ(Ω₁·x) < ϑˣ(Ω₁·(x + x))`. -/
theorem lv_luTop_lt {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : luTop x < lvTop x := by
  have h := (LvT.lv_T hx hx1 (LvT.th 0 (LvT.cst 0)) ⟨hx.pos, hx.pos⟩).2
  simpa only [LvT.val_th, LvT.val_cst, add_zero] using h

/-- **`Λ⁺(luSys) = ι(φ(Ω₁, 1)·ω)`, `ρ_{Λ⁺(luSys)} = P(φ(Ω₁, 1)·ω) < L(0)`.** -/
theorem lv_loc_luSys : xtB1 luSys = iota S (luTc * ω) ∧ upsilon (xtB1 luSys) = Pv S (luTc * ω) ∧
    Pv S (luTc * ω) < Nc.ncL S 0 := by
  have e : ω ^ luTc = luTc := gg_veblen_eps (zero_lt_one.trans (gg_one_lt_of_SC ph_SC_Om1)).ne'
  have h := Fp.fpB1_eq (S := S) lu_T_lt_Gam luPoly (fun _ hy hy1 => (luTh_T hy hy1).symm) (fun _ hZ => lu_cl_T hZ)
    lu_Om1_le_T (fun _ hx hx1 => lv_eN_lt_luTop hx hx1) luSys_topPkg
  rwa [e] at h

/-- **`Λ⁺(lvSys) = ι(φ(Ω₁ + Ω₁, 0)·ω)`, `ρ_{Λ⁺(lvSys)} = P(φ(Ω₁ + Ω₁, 0)·ω) < L(0)`.** -/
theorem lv_loc : xtB1 lvSys = iota S (lvTc * ω) ∧ upsilon (xtB1 lvSys) = Pv S (lvTc * ω) ∧
    Pv S (lvTc * ω) < Nc.ncL S 0 := by
  have hOO : Om 1 + Om 1 ≠ 0 :=
    (lt_of_lt_of_le (zero_lt_one.trans (gg_one_lt_of_SC ph_SC_Om1)) le_self_add).ne'
  have e : ω ^ lvTc = lvTc := gg_veblen_eps hOO
  have h := Fp.fpB1_eq (S := S) lv_T_lt_Gam lvPoly (fun _ hy hy1 => (lvTh_T hy hy1).symm) (fun _ hZ => lv_cl_T hZ)
    lv_Om1_le_T (fun _ hx hx1 => (lv_eN_lt_luTop hx hx1).trans (lv_luTop_lt hx hx1)) lvSys_topPkg
  rwa [e] at h

end Googology.Trans.PoR.InaccPsi.R2
