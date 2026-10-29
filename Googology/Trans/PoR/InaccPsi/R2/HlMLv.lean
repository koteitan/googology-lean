import Googology.Trans.PoR.InaccPsi.R2.HlLow

/-!
# HlMLv: THE GATED LEVEL DATUM `Ω₁·M` READ AS `x·M`, FOR EVERY `1 ≤ M < Ω₁`

`Ω₁·M` (`M < Ω₁`) is read as `x·M`; Lemma EXACT `π_{σ,ρ}(ρ·M) = σ·M` is `Exact.pi_mul`, which needs `M < σ`.  At
`M ≥ ε₀` this fails at the bases `σ ≤ M` (at `M = ε₀` exactly at `σ = ε₀`, the first failing case of round 104), so
the datum is GATED: gate `hlGt M = 0` for `M < ε₀`, `= M` otherwise; at or below the gate the reading is `x`
(`hlRd`).  The code gate: a code `y ∈ [Ω₁·M, Ω₁²)` over a strongly critical `Z` has `M < Z` (`hl_mul_cl`, from
`Gw.gw_cl_coef`), so `hlGt M < Z`.  Hull membership: `Hk.hk_mul_mem` for `M < ε₀`, `hl_mul_mem` (`M < b`) otherwise.

* `hlGt`, `hlGt_le`, `hlGt_mono`, `hl_gt_E` (`hlGt M < σ ⇒ M < σ` at an `ε`-number `σ`), `hl_mul_mem`, `hl_mul_cl`;
* `hlRd`, `hlMLv M` (**THE GATED LEVEL DATUM `Ω₁·M`**, `1 ≤ M < Ω₁`), `hlMLv_L`, `hlMLv_l`, `hlMLv_g`.

What differs from `Hk.hkLv`: the range `M < Ω₁` in place of `M < ε₀`, the gate, the reading `x` at or below the gate,
the hull membership only at `0 < a`, `hlGt M < b`.  No new axiom.  New definitions: `hlGt`, `hlRd`, `hlMLv`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hl

open Googology.Trans.PoR.InaccPsi.R2.Hj Googology.Trans.PoR.InaccPsi.R2.Hk
open Googology.Trans.PoR.InaccPsi.R2.Hi Googology.Trans.PoR.InaccPsi.R2.Hg
open Googology.Trans.PoR.InaccPsi.R2.Hf Googology.Trans.PoR.InaccPsi.R2.Hd Googology.Trans.PoR.InaccPsi.R2.He
open Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Hb
open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

/-! ## The gate of a constant level -/

open Classical in
/-- **The gate of the level `Ω₁·M`**: `0` for `M < ε₀`, `M` otherwise. -/
noncomputable def hlGt (M : Ordinal.{0}) : Ordinal.{0} := if M < ε₀ then 0 else M

theorem hlGt_le (M : Ordinal.{0}) : hlGt M ≤ M := by
  unfold hlGt; split_ifs
  · exact zero_le
  · exact le_rfl

theorem hlGt_mono {M M' : Ordinal.{0}} (h : M ≤ M') : hlGt M ≤ hlGt M' := by
  unfold hlGt; split_ifs with h1 h2 h2
  · exact le_rfl
  · exact zero_le
  · exact absurd (h.trans_lt h2) h1
  · exact h

/-- **Above the gate of `M`, at an `ε`-number `σ`: `M < σ`.** -/
theorem hl_gt_E {M σ : Ordinal.{0}} (hσ : InE σ) (h : hlGt M < σ) : M < σ := by
  unfold hlGt at h; split_ifs at h with h1
  · exact h1.trans_le (gc_eps0_le hσ)
  · exact h

/-- **`Ω₁·M` lies in every hull `C(a, b)` with `M < b`.** -/
theorem hl_mul_mem (S : InaccSeq.{0}) (a b : Ordinal.{0}) :
    ∀ M : Ordinal.{0}, M < b → (Om1 : Ordinal.{0}) * M ∈ S.CSet a b := by
  intro M
  induction M using WellFoundedLT.induction with
  | ind M IH =>
  intro hM
  rcases eq_or_ne M 0 with rfl | h0
  · rw [mul_zero]; exact CSet.zero_mem _ _
  obtain ⟨hdr, hrd⟩ := hk_split h0
  have hw : (Om1 : Ordinal.{0}) * ω ^ log ω M ∈ S.CSet a b := by
    rw [hk_om_opow]
    exact CSet.phi_mem (CSet.zero_mem _ _) (CSet.add_mem (CSet.Om_mem (CSet.one_mem _ _))
      (CSet.of_lt ((log_le_self ω M).trans_lt hM)))
  rw [← hdr, mul_add]
  exact CSet.add_mem hw (IH _ hrd (hrd.trans hM))

/-- **The gate of `Ω₁·M` from a code**: a code `y ∈ [Ω₁·M, Ω₁²)` over a strongly critical `Z ≤ Ω₁` has
`M < Z` (`Gw.gw_cl_coef`). -/
theorem hl_mul_cl {Z y M : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om 1) (hy : GxCl Z {gcG 0} y)
    (hMy : (Om1 : Ordinal.{0}) * M ≤ y) (hy2 : y < Om 1 * Om 1) : M < Z := by
  have h := gw_cl_coef hZ hZ1 hy hy2
  rw [Br.Om1_eq] at hMy
  exact ((le_div gw_Om_pos.ne').2 hMy).trans_lt h

/-! ## The gated level datum -/

open Classical in
/-- **The reading of the level `Ω₁·M`**: `x·M` above the gate, `x` at or below it. -/
noncomputable def hlRd (M x : Ordinal.{0}) : Ordinal.{0} := if hlGt M < x then x * M else x

theorem hlRd_eq {M x : Ordinal.{0}} (h : hlGt M < x) : hlRd M x = x * M := by unfold hlRd; rw [if_pos h]

/-- **THE GATED LEVEL DATUM `Ω₁·M`, READ AS `x·M`** (above the gate `hlGt M`), for `1 ≤ M < Ω₁`. -/
noncomputable def hlMLv (M : Ordinal.{0}) (h1 : 1 ≤ M) (hM : M < Om1) : HlLv where
  L := Om1 * M
  l := hlRd M
  q := M
  g := hlGt M
  g_lt := (hlGt_le M).trans_lt hM
  q_lt := hM
  OL := le_mul_of_one_le_right' h1
  L_G := InE.mul_lt (Low.opow_eq_self_of_SC (gcG_SC 0)) (hg_Om1_lt_G 0) (hM.trans (hg_Om1_lt_G 0))
  L_eq := by rw [Br.Om1_eq]
  g_cl := fun _ _ hZ hZ1 hy hMy hy2 => (hlGt_le M).trans_lt (hl_mul_cl hZ hZ1 hy hMy hy2)
  L_mem := fun S a b _ hb => by
    by_cases he : M < ε₀
    · exact hk_mul_mem S a b M he
    · unfold hlGt at hb; rw [if_neg he] at hb; exact hl_mul_mem S a b M hb
  l_ge := fun x => by
    unfold hlRd; split_ifs
    · exact le_mul_of_one_le_right' h1
    · exact le_rfl
  l_lt := fun x hx hx1 => by
    unfold hlRd; split_ifs with h
    · exact InE.mul_lt (lgG_facts hx hx1).2.2.2.1 (lgG_facts hx hx1).2.1 ((hl_gt_E hx h).trans (lgG_facts hx hx1).2.1)
    · exact (lgG_facts hx hx1).2.1
  l_lt2 := fun x hx _ hg => by
    rw [hlRd_eq hg, ← mul_add_one]
    exact mul_lt_mul_of_pos_left ((ev_isSuccLimit_of_inE hx).add_one_lt (hl_gt_E hx hg)) hx.pos
  l_pi := fun σ ρ hB hg => by
    rw [hlRd_eq hg, hlRd_eq (hg.trans hB.2.2.1)]
    exact pi_mul hB M (hl_gt_E hB.1 hg)

theorem hlMLv_L (M : Ordinal.{0}) (h1 : 1 ≤ M) (hM : M < Om1) : (hlMLv M h1 hM).L = Om1 * M := rfl

theorem hlMLv_l (M : Ordinal.{0}) (h1 : 1 ≤ M) (hM : M < Om1) {x : Ordinal.{0}} (hx : hlGt M < x) :
    (hlMLv M h1 hM).l x = x * M := hlRd_eq hx

theorem hlMLv_g (M : Ordinal.{0}) (h1 : 1 ≤ M) (hM : M < Om1) : (hlMLv M h1 hM).g = hlGt M := rfl

end Googology.Trans.PoR.InaccPsi.R2.Hl
