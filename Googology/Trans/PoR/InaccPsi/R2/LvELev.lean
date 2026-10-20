import Googology.Trans.PoR.InaccPsi.R2.LvESys

/-!
# The top `ϑᵗ(Ω₁·ε_{τ+1})` is the least element of `P_{ε_{τ+1}}` above `τ`

From the fixed-point levels of `R2.LvLev` (every level `β ∈ Tᵗ ∩ Ω₁`): `lve_top_P` (**`ϑᵗ(Ω₁·ε_{τ+1}) ∈ P_{ε_{τ+1}}`**),
`lve_top_least` (**`ϑᵗ(Ω₁·ε_{τ+1})` is the least element of `P_{ε_{τ+1}}` above `τ`**).

No new axiom beyond `R2.CitedLu` and `R2.CitedLv`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order Lu

section Base

variable {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1)
include hτ hτ1

/-- **`ϑᵗ(Ω₁·ε_{τ+1}) ∈ P_{ε_{τ+1}}`**. -/
theorem lve_top_P : LuP (eN τ) (lveTop τ) := by
  obtain ⟨-, -, haT, -, ha1, haE, -⟩ := lveTop_facts hτ hτ1
  obtain ⟨hwT, hw1⟩ := lve_eN_T hτ hτ1
  have hw0 : eN τ ≠ 0 := (eN_E τ).pos.ne'
  refine (mem_range_veblen hw0).2 (fun β hβ => ?_)
  rcases eq_or_ne β 0 with rfl | hβ0
  · rw [veblen_zero_apply]; exact haE
  have hβ1 : 1 ≤ β := one_le_iff_ne_zero.2 hβ0
  refine le_antisymm ?_ (right_le_veblen _ _)
  rw [(isNormal_veblen _).apply_of_isSuccLimit (ev_isSuccLimit_of_inE haE)]
  refine Ordinal.iSup_le (fun j => ?_)
  have hj1 : j.1 < Om1 := j.2.trans ha1
  have hjT : j.1 ∈ Tset τ := vz_T_down hτ hτ1 haT ha1 j.2.le
  have hβT := vz_T_down hτ hτ1 hwT hw1 hβ.le
  exact (lv_veblen_le_th hτ hτ1 hβ1 hβT (hβ.trans hw1) j.1 hjT hj1).trans
    (lve_lt_top hτ hτ1 hβT hβ hjT hj1 j.2).le

/-- **`ϑᵗ(Ω₁·ε_{τ+1})` is the least element of `P_{ε_{τ+1}}` above `τ`.** -/
theorem lve_top_least {u : Ordinal.{0}} (hPu : LuP (eN τ) u) (hτu : τ < u) : lveTop τ ≤ u := by
  by_contra hlt
  push Not at hlt
  obtain ⟨-, -, haT, -, ha1, -, -⟩ := lveTop_facts hτ hτ1
  obtain ⟨hwT, hw1⟩ := lve_eN_T hτ hτ1
  have hu1 : u < Om1 := hlt.trans ha1
  have huT : u ∈ Tset τ := vz_T_down hτ hτ1 haT ha1 hlt.le
  have huE : InE u := luP_E ((lu_one_lt_E hτ).le.trans (lt_eN τ).le) hPu
  obtain ⟨ξ, hξT, hξ2, hξu⟩ := vt_rep hτ hτ1 huT hτu.le hu1 (inE_indec huE)
  have hΩξ : Om1 ≤ ξ := (vt_E_iff hτ hτ1 hξT hξ2).1 ⟨by rw [hξu]; exact hτu, by rw [hξu]; exact huE⟩
  obtain ⟨hq1, hrT, hr1, hdec⟩ := lu_split hτ hτ1 hξT hξ2 hΩξ
  have hqw : ξ / Om1 < eN τ :=
    lve_quot_top hτ hτ1 hξT hξ2 (by rw [hξu]; exact hτu) (by rw [hξu]; exact huE) (by rw [hξu]; exact hlt)
  have hnP := lv_th_notP hτ hτ1 hq1 (vz_T_down hτ hτ1 hwT hw1 hqw.le) (hqw.trans hw1) hrT hr1
  rw [hdec, hξu] at hnP
  exact hnP (luP_mono (hq1.trans le_self_add) (add_one_le_of_lt hqw) hPu)

end Base

end Googology.Trans.PoR.InaccPsi.R2
