import Googology.Trans.PoR.InaccPsi.R2.ZgRef

/-!
# ZgDiv: DIVISION OF CODES BY AN `ε`-NUMBER CODE, AND THE DIGITS OF THE OFFSETS `B_Γ·d + r`

`Tl.tl_cl_div` (division by `Ω₁`) for every `ε`-number code `E` (`zgDivE`), so a code `B_Γ·d + r` (`d, r < B_Γ`) has
codes `d` and `r` as digits and both gates below `Z` (`zgDig`): the inversion needed by the cover of a reading system
for the offsets `B_Γ·d + r`.

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zg

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Tl
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Tf Googology.Trans.PoR.InaccPsi.R2.Yr Googology.Trans.PoR.InaccPsi.R2.Zb

/-- **The codes over a strongly critical `Z` are closed under `y ↦ y / E`** for an `ε`-number code `E`. -/
theorem zgDivE {Z E : Ordinal.{0}} (hZ : SC Z) (hE : ω ^ E = E) (hEC : TlCl Z E) :
    ∀ y, TlCl Z y → TlCl Z (y / E) := by
  have hE0 : E ≠ 0 := by
    intro h; rw [h, opow_zero] at hE; exact one_ne_zero hE
  intro y
  induction y using WellFoundedLT.induction with
  | ind y IH =>
  intro hy
  rcases eq_or_ne y 0 with rfl | hy0
  · rw [Ordinal.zero_div]; exact TlCl.zero hZ.1
  obtain ⟨hsub, hlog⟩ := tlDec hZ y hy
  set g := log ω y with hg
  obtain ⟨k, hk⟩ := lt_omega0.1 (div_opow_log_lt y one_lt_omega0)
  have hdec : ω ^ g * (y / ω ^ g) + y % ω ^ g = y := Ordinal.div_add_mod y _
  rw [hk] at hdec
  rcases lt_or_ge g E with hgO | hgO
  · have hy1 : y < E := by
      have h1 : y < ω ^ (g + 1) := lt_opow_succ_log_self one_lt_omega0 y
      refine h1.trans_le ?_
      rw [← hE]
      exact opow_le_opow_right omega0_pos (Order.add_one_le_of_lt hgO)
    rw [Ordinal.div_eq_zero_of_lt hy1]; exact TlCl.zero hZ.1
  · set g' := g - E with hg'
    have hge : E + g' = g := Ordinal.add_sub_cancel_of_le hgO
    have hg'C : TlCl Z g' := (tlDec hZ g hlog).1 _ hEC hgO
    have hwk : TlCl Z (ω ^ g * k) := TlCl.mul_nat hZ.1 (TlCl.opow hZ.1 hlog) k
    have hle : ω ^ g * k ≤ y := by
      conv_rhs => rw [← hdec]
      exact le_self_add
    have hr : TlCl Z (y % ω ^ g) := by
      have e : y - ω ^ g * k = y % ω ^ g := by
        nth_rewrite 1 [← hdec]; exact Ordinal.add_sub_cancel _ _
      rw [← e]; exact hsub _ hwk hle
    have hry : y % ω ^ g < y := Rj.rj_mod_lt hy0
    have e : y = E * (ω ^ g' * k) + y % ω ^ g := by
      conv_lhs => rw [← hdec]
      rw [← hge, opow_add, hE, mul_assoc]
    rw [e, Ordinal.mul_add_div _ hE0]
    exact TlCl.add (TlCl.mul_nat hZ.1 (TlCl.opow hZ.1 hg'C) k) (IH _ hry hr)

/-- **The digits of `B_Γ·d + r` are codes with gates below `Z`** (`d, r < B_Γ`, `Z ≤ Ω₁` strongly critical). -/
theorem zgDig {Z d r : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om1) (hd : d < tfBG) (hr : r < tfBG)
    (h : TlCl Z (tfBG * d + r)) : TlCl Z d ∧ TlCl Z r ∧ yrG d < Z ∧ yrG r < Z := by
  have hE : ω ^ tfBG = tfBG := Low.opow_eq_self_of_SC tfBG_SC
  have hBC : TlCl Z tfBG := zbBG_tl hZ.1
  have hdC : TlCl Z d := by
    have := zgDivE hZ hE hBC _ h
    rwa [(zgQM' d hr).1] at this
  have hBd : TlCl Z (tfBG * d) := by
    have := tl_cl_opow_mul hZ hBC d hdC
    rwa [hE] at this
  have hrC : TlCl Z r := by
    have := (tlDec hZ _ h).1 _ hBd le_self_add
    rwa [Ordinal.add_sub_cancel] at this
  exact ⟨hdC, hrC, zgGate hZ hZ1 hd hdC, zgGate hZ hZ1 hr hrC⟩

end Googology.Trans.PoR.InaccPsi.R2.Zg
