import Googology.Trans.PoR.InaccPsi.R2.LvETm

/-!
# The exact `R₁⁺`-reach of the top `ϑˣ(Ω₁·ε_{x+1})`

`LvE.luL_top` (`luL(a, ε_{x+1}) = a·ε_{x+1} + ε_{x+1}`), `LvE.lh_top` (**the reach of the top**:
`lh(ϑˣ(Ω₁·ε_{x+1})) = ϑˣ(Ω₁·ε_{x+1})·ε_{x+1} + ε_{x+1}`, from `Lv.lv_lh_gen`), `LvE.lve_lg_opow` (`logend(ω^a) = a`).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order

namespace LvE

/-- `logend(ω^a) = a`. -/
theorem lve_lg_opow (a : Ordinal.{0}) : lg (ω ^ a) = a := by
  have h0 : ω ^ a ≠ 0 := (opow_pos a omega0_pos).ne'
  refine le_antisymm ?_ (le_lg h0 (dvd_refl _))
  have h1 := le_of_dvd h0 (lg_dvd h0)
  exact (opow_le_opow_iff_right one_lt_omega0).1 h1

/-- `luL(a, ε_{x+1}) = a·ε_{x+1} + ε_{x+1}`. -/
theorem luL_top {x a : Ordinal.{0}} (hx : InE x) : Lu.luL a (eN x) = a * eN x + eN x := by
  have he : ω ^ eN x = eN x := eN_E x
  have hω : ω ≤ eN x := (Lu.lu_omega_lt_E hx).le.trans (lt_eN x).le
  have hlog : log ω (eN x) = eN x := by
    have h := log_opow one_lt_omega0 (eN x)
    rwa [he] at h
  unfold Lu.luL
  rw [if_neg (not_lt.2 hω), hlog, he, Lu.lu_lg_E (eN_E x), Ordinal.sub_self, mul_zero, add_zero]

/-- **The reach of the top**. -/
theorem lh_top {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    IsLh1 (lveTop x) (lveTop x * eN x + eN x) := by
  obtain ⟨heT, he1⟩ := lve_eN_T hx hx1
  have h := Lv.lv_lh_gen hx hx1 heT (lt_eN x).le he1 (mem_T_of_le hx hx1 zero_le) (Ordinal.omega_pos 1)
  rw [add_zero, Lu.lu_zeta_zero, add_zero, luL_top hx] at h
  exact h

end LvE

end Googology.Trans.PoR.InaccPsi.R2
