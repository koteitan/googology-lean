import Googology.Trans.PoR.InaccPsi.R2.UiCa
import Googology.Trans.PoR.InaccPsi.R2.UcH

/-!
# The hierarchy `H^s_γ` on `Ω_{s+1}` for the levels `γ < ε_{Ω_{s+1}+1}`, for every `s`

`W = Ω_{s+1}`, `L = Ω_s`, `E = uiE s`, `uiC s γ` the largest base-`W` component of `γ` (`R2.UiCmp`), `Uc.ucG d L μ`
the generic hierarchy of `R2.UcH` (the enumeration of the strongly critical `v > L` with `d μ < v` that are fixed
points of every `ucG d L j`, `j < μ`, with `d j < v`).

* `uiH s γ := ucG (uiC s) (Om s) γ` (**the levels one cardinal up from `L`**: values `> Ω_s`, all components of `γ`
  below the value); `uiH_SC`, `uiH_gt`, `uiH_C_lt`, `uiH_lt_iff`, `uiH_le_iff`, `uiH_le_self`, `uiH_normal`,
  `uiH_fix_lower`, `uiH_range`;
* `uiH_zero_range` (**`H^s_0` enumerates the strongly critical ordinals above `Ω_s`**), `uiH_zero_lt` (a successor
  `a + 1 > Ω_s` lies strictly below `H^s_0(a + 1)`).

At `s = 1` this is `Uc.ucH` (`R2.UiAgree`).  No new axiom.  New definition: `uiH`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ui

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Uc

variable {s : Ordinal.{0}}

/-- **`H^s_γ`**: the levels `γ < E` with the data `uiC s` (largest component) and the floor `Ω_s`. -/
noncomputable def uiH (s γ : Ordinal.{0}) : Ordinal.{0} → Ordinal.{0} := ucG (uiC s) (Om s) γ

theorem uiH_SC (γ o : Ordinal.{0}) : SC (uiH s γ o) := ucG_SC γ o

theorem uiH_gt (γ o : Ordinal.{0}) : Om s < uiH s γ o := ucG_L_lt γ o

theorem uiH_C_lt (γ o : Ordinal.{0}) : uiC s γ < uiH s γ o := ucG_d_lt γ o

theorem uiH_lt_iff (γ : Ordinal.{0}) {a b : Ordinal.{0}} : uiH s γ a < uiH s γ b ↔ a < b := ucG_lt_iff γ

theorem uiH_le_iff (γ : Ordinal.{0}) {a b : Ordinal.{0}} : uiH s γ a ≤ uiH s γ b ↔ a ≤ b := ucG_le_iff γ

theorem uiH_le_self (γ o : Ordinal.{0}) : o ≤ uiH s γ o := ucG_le_self γ o

theorem uiH_normal (γ : Ordinal.{0}) : Order.IsNormal (uiH s γ) := ucG_normal γ

theorem uiH_fix_lower {j γ v : Ordinal.{0}} (h : j < γ) (hv : v ∈ range (uiH s γ)) (hj : uiC s j < v) :
    uiH s j v = v := ucG_fix_lower h hv hj

theorem uiH_range {γ v : Ordinal.{0}} (hSC : SC v) (hL : Om s < v) (hγ : uiC s γ < v)
    (hfix : ∀ j < γ, uiC s j < v → uiH s j v = v) : ∃ e, uiH s γ e = v := ucG_range hSC hL hγ hfix

/-- **`H^s_0` enumerates the strongly critical ordinals above `Ω_s`.** -/
theorem uiH_zero_range {v : Ordinal.{0}} (hSC : SC v) (hL : Om s < v) : ∃ e, uiH s 0 e = v :=
  uiH_range hSC hL (by rw [uiC_small (ui_SC_W s).1]; exact hSC.1) fun j hj => absurd hj (not_lt.2 zero_le)

/-- A successor `a + 1` lies strictly below `H^s_0(a + 1)`. -/
theorem uiH_zero_lt (a : Ordinal.{0}) : a + 1 < uiH s 0 (a + 1) :=
  lt_of_le_of_ne (uiH_le_self 0 (a + 1)) fun e => SC.ne_add_one (uiH_SC (s := s) 0 (a + 1)) a e.symm

end Googology.Trans.PoR.InaccPsi.R2.Ui
