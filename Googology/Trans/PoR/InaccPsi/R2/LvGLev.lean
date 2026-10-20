import Googology.Trans.PoR.InaccPsi.R2.LvGSys

/-!
# The tops of the tower are the least elements of the fixed-point levels

From the fixed-point levels of `R2.LvLev`: `lvg_top_P` (**`gT (n+1) x ∈ P_{gT n x}`**), `lvg_top_least`
(**`gT (n+1) x` is the least element of `P_{gT n x}` above `x`**), `lvg_P_self` (an ordinal `β > x` with `β ∈ P_β` is
above every top `gT n x`).

No new axiom beyond `R2.CitedLu` and `R2.CitedLv`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order Lu

section Base

variable {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1)
include hτ hτ1

/-- **`gT (n+1) τ ∈ P_{gT n τ}`**. -/
theorem lvg_top_P (n : ℕ) : LuP (gT n τ) (gT (n + 1) τ) := by
  obtain ⟨haT, -, ha1, haE⟩ := gT_facts hτ hτ1 (n + 1)
  obtain ⟨hwT, -, hw1, hwE⟩ := gT_facts hτ hτ1 n
  have hw0 : gT n τ ≠ 0 := hwE.pos.ne'
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
    (lvg_lt_top hτ hτ1 hβT hβ hjT hj1 j.2).le

/-- **`gT (n+1) τ` is the least element of `P_{gT n τ}` above `τ`.** -/
theorem lvg_top_least (n : ℕ) {u : Ordinal.{0}} (hPu : LuP (gT n τ) u) (hτu : τ < u) : gT (n + 1) τ ≤ u := by
  by_contra hlt
  push Not at hlt
  obtain ⟨haT, -, ha1, -⟩ := gT_facts hτ hτ1 (n + 1)
  obtain ⟨hwT, hτw, hw1, -⟩ := gT_facts hτ hτ1 n
  have hu1 : u < Om1 := hlt.trans ha1
  have huT : u ∈ Tset τ := vz_T_down hτ hτ1 haT ha1 hlt.le
  have huE : InE u := luP_E ((lu_one_lt_E hτ).le.trans hτw.le) hPu
  obtain ⟨ξ, hξT, hξ2, hξu⟩ := vt_rep hτ hτ1 huT hτu.le hu1 (inE_indec huE)
  have hΩξ : Om1 ≤ ξ := (vt_E_iff hτ hτ1 hξT hξ2).1 ⟨by rw [hξu]; exact hτu, by rw [hξu]; exact huE⟩
  obtain ⟨hq1, hrT, hr1, hdec⟩ := lu_split hτ hτ1 hξT hξ2 hΩξ
  have hqw : ξ / Om1 < gT n τ :=
    lvg_quot hτ hτ1 n ξ hξT hξ2 (by rw [hξu]; exact hτu) (by rw [hξu]; exact huE) (by rw [hξu]; exact hlt)
  have hnP := lv_th_notP hτ hτ1 hq1 (vz_T_down hτ hτ1 hwT hw1 hqw.le) (hqw.trans hw1) hrT hr1
  rw [hdec, hξu] at hnP
  exact hnP (luP_mono (hq1.trans le_self_add) (add_one_le_of_lt hqw) hPu)

/-- An ordinal `β > τ` with `β ∈ P_β` is above every top `gT n τ`. -/
theorem lvg_P_self : ∀ n : ℕ, ∀ β, τ < β → LuP β β → gT n τ ≤ β
  | 0, β, hτβ, hP => eN_le hτβ (luP_E ((lu_one_lt_E hτ).le.trans hτβ.le) hP)
  | n + 1, β, hτβ, hP => by
      have hle := lvg_P_self n β hτβ hP
      have hw1 : 1 ≤ gT n τ := (lu_one_lt_E hτ).le.trans (gT_facts hτ hτ1 n).2.1.le
      exact lvg_top_least hτ hτ1 n (luP_mono hw1 hle hP) hτβ

end Base

end Googology.Trans.PoR.InaccPsi.R2
