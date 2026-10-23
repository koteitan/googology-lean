import Googology.Trans.PoR.InaccPsi.R2.GdLd
import Googology.Trans.PoR.InaccPsi.R2.GdTow
import Googology.Trans.PoR.InaccPsi.R2.GcTow

/-!
# THE GATED UNIFORMITY THEOREM: the top of `gdB α` reads the atom `Γ_{Ω₁+2+α}`, for every ordinal `α`

`R2.GcTow.gcB_codes` for the gated tower of `R2.GdTow`, with the codes over the base (`R2.GdAt`):

* `gdq_sup` (`ϑˣ(Ω₁·Ω₁ + η) = sup_n gdP B n x` above the gate), `gdLim_top` (**the gated limit top reads `cQs c`**),
  `gdLim_poly` (**the gated limit layer has terms for every code below `cQs c`**);
* `gdB_codes` (**THE GATED UNIFORMITY THEOREM**: for every ordinal `α`, `E_{gdB α}(y) = Θ_y(Γ_{Ω₁+2+α})` at every
  strongly critical `y > α`, and every code below `Γ_{Ω₁+2+α}` over a base `Z > α` is read by a term of `gdB α`;
  the base from `Gc.gcB_codes`, the successor by the gated ladder, the limit by the union).

No new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph Googology.Trans.PoR.InaccPsi.R2.Xt Lu
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Lp Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gc

theorem gdq_sup {B : GdB} {η : Ordinal.{0}} (H : GdqH B η) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
    (hg : B.g < x) : gq η x = ⨆ n, gdP B n x :=
  le_antisymm (le_of_forall_lt fun v hv => by
      obtain ⟨n, hn⟩ := gdq_lt_iff H hx hx1 hg v hv
      exact hn.trans_le (Ordinal.le_iSup (fun n => gdP B n x) n))
    (Ordinal.iSup_le fun n => (gdq_gP_lt H hx hx1 hg n).le)

section Lim

variable {B : GdB} {c : Ordinal.{0}} (hc : ∀ Z, SC Z → B.g < Z → GxCl Z (gdAt Z) c) (hcO : Om 1 ≤ c)
  (hKE : ∀ y, SC y → y < Om 1 → B.g < y → B.K.E y = gxTh y (gdAt y) c) {η : Ordinal.{0}} (H : GdqH B η)
include hc hKE H

/-- **The gated limit top reads the code `cQs c`**: `gq η y = Θ_y(cQs c)` above the gate. -/
theorem gdLim_top {y : Ordinal.{0}} (hy : SC y) (hy1 : y < Om 1) (hg : B.g < y) :
    gq η y = gxTh y (gdAt y) (cQs c) := by
  rw [gdq_sup H (gg_SC_eps hy) (lp_y1 hy1) hg, cQs, gcTh_iSup]
  exact iSup_congr fun n => gdTop_th hc hKE n y hy hy1 hg

include hcO in
/-- **The gated limit layer has terms for every code below `cQs c`.** -/
theorem gdLim_poly (hKP : GdPolyG B.K.sys c) : GdPolyG (gdqUSys B η H) (cQs c) := by
  intro Z d hg hd hdE
  obtain ⟨n, hn⟩ := cQs_lt hdE
  obtain ⟨s, hs⟩ := gdPoly hc hcO hKE hKP n Z d hg hd hn
  exact ⟨s, fun y hy hy1 hZy => ⟨(hs y hy hy1 hZy).1.1, (hs y hy hy1 hZy).2⟩⟩

end Lim

/-! ## The uniformity theorem -/

theorem gdB_zero : gdB 0 = GdB.ofLp (lpTB 1) 0 := by
  unfold gdB gdRec
  rw [Ordinal.limitRecOn_zero]; rfl

/-- **THE GATED UNIFORMITY THEOREM**: for every ordinal `α`, the top of `gdB α` reads `Γ_{Ω₁+2+α}` at every strongly
critical `y > α`, and `gdB α` has terms for every code below it over every base above `α`. -/
theorem gdB_codes (S : InaccSeq.{0}) : ∀ α : Ordinal.{0},
    (∀ y, SC y → y < Om 1 → α < y → (gdB α).K.E y = gxTh y (gdAt y) (gcG (1 + α))) ∧
    GdPolyG (gdB α).K.sys (gcG (1 + α)) := by
  intro α
  induction α using WellFoundedLT.induction with
  | ind α IH0 =>
  rcases zero_or_succ_or_isSuccLimit α with rfl | ⟨δ, rfl⟩ | hα
  · -- the start: `Gc.gcB_codes` at `0`
    have h1e : (1 : Ordinal.{0}) < ε₀ := by exact_mod_cast natCast_lt_epsilon 1 0
    have hG := gcB_codes S 0 (by rw [add_zero]; exact h1e)
    have e1 : gcG (1 + 0) ≤ gcV := gcG_le (by rw [add_zero]; exact h1e.le)
    rw [gcB_zero] at hG
    rw [gdB_zero]
    refine ⟨fun y hy hy1 _ => ?_, fun Z d _ hd hdE => ?_⟩
    · show (lpTB 1).K.E y = _
      rw [hG.1 y hy hy1, gdTh_eq_gcTh hy e1]
    · obtain ⟨s, hs⟩ := hG.2 Z d (gc_of_gdCl hd (hdE.trans_le e1)) hdE
      exact ⟨s, fun y hy hy1 hZy => ⟨(hs y hy hy1 hZy).1, by
        rw [show (GdB.ofLp (lpTB 1) 0).K.sys.val s y = (lpTB 1).K.sys.val s y from rfl, (hs y hy hy1 hZy).2,
          gdTh_eq_gcTh hy (hdE.trans_le e1).le]⟩⟩
  · rw [succ_eq_add_one] at IH0 ⊢
    obtain ⟨ihE, ihP⟩ := IH0 δ (lt_add_one δ)
    have hg0 : (gdB δ).g = δ := gdB_g δ
    have hc : ∀ Z, SC Z → (gdB δ).g < Z → GxCl Z (gdAt Z) (gcG (1 + δ)) := fun Z hZ hg => by
      rw [hg0] at hg
      exact GxCl.atom (gdG_atom (gd_one_add_lt' (gg_SC_eps hZ) hg))
    have hcO : Om 1 ≤ gcG (1 + δ) := (gcG_Om1_lt _).le
    have hKE : ∀ y, SC y → y < Om 1 → (gdB δ).g < y → (gdB δ).K.E y = gxTh y (gdAt y) (gcG (1 + δ)) :=
      fun y hy hy1 hg => ihE y hy hy1 (hg0 ▸ hg)
    have hQ : cQs (gcG (1 + δ)) = gcG (1 + (δ + 1)) := by rw [gc_cQs, add_assoc]
    have H := gdH_succ (gdRec δ)
    rw [gdB_succ δ]
    refine ⟨fun y hy hy1 hδy => ?_, fun Z d hg hd hdE => ?_⟩
    · show gq (1 + δ + 1) y = _
      rw [gdLim_top hc hKE H hy hy1 (by rw [hg0]; exact (lt_add_one δ).trans hδy), hQ]
    · have hP := gdLim_poly hc hcO hKE H ihP
      rw [hQ] at hP
      have hg' : (gdB δ).g < Z := by rw [hg0]; exact (lt_add_one δ).trans hg
      exact hP Z d hg' hd hdE
  · have IH : ∀ β < α, (∀ y, SC y → y < Om 1 → β < y → (gdB β).K.E y = gxTh y (gdAt y) (gcG (1 + β))) ∧
        GdPolyG (gdB β).K.sys (gcG (1 + β)) := IH0
    have hα' : 1 + α = α := one_add_of_omega0_le (omega0_le_of_isSuccLimit hα)
    rw [hα']
    rw [gdB_lim hα]
    refine ⟨fun y hy hy1 hαy => ?_, fun Z d hg hd hdE => ?_⟩
    · have hyE := gg_SC_eps hy
      have hy1' := lp_y1 hy1
      show gq α y = _
      refine le_antisymm (le_of_forall_lt fun v hv => ?_) ?_
      · obtain ⟨ν, hν, hvν⟩ := gc_lt_lim_iff hyE hy1' hα hαy v hv
        have h1 : gq ν y ≤ gq (1 + ν) y := gq_mono hyE hy1' ((gc_one_add_lt hα hν).trans hαy) le_add_self
        have h2 : gq (1 + ν) y = gxTh y (gdAt y) (gcG (1 + ν)) := by
          rw [← gdB_E hyE hy1' (hν.trans hαy)]; exact (IH ν hν).1 y hy hy1 (hν.trans hαy)
        calc v < gq ν y := hvν
          _ ≤ gq (1 + ν) y := h1
          _ = gxTh y (gdAt y) (gcG (1 + ν)) := h2
          _ ≤ gxTh y (gdAt y) (gcG α) := gxTh_mono (gcG_le (gc_one_add_lt hα hν).le)
      · rw [gcTh_limit hα]
        refine ciSup_le' fun β => ?_
        have h2 : gxTh y (gdAt y) (gcG (1 + β.1)) = gq (1 + β.1) y := by
          rw [← (IH β.1 β.2).1 y hy hy1 (β.2.trans hαy), gdB_E hyE hy1' (β.2.trans hαy)]
        calc gxTh y (gdAt y) (gcG β.1) ≤ gxTh y (gdAt y) (gcG (1 + β.1)) := gxTh_mono (gcG_le le_add_self)
          _ = gq (1 + β.1) y := h2
          _ ≤ gq α y := gq_mono hyE hy1' hαy (gc_one_add_lt hα β.2).le
    · obtain ⟨β, hβ, hdβ⟩ := gcG_lt_of_lt_limit hα hdE
      have hgβ : (gdB β).g < Z := by rw [gdB_g]; exact hβ.trans hg
      obtain ⟨s, hs⟩ := (IH β hβ).2 Z d hgβ hd (hdβ.trans_le (gcG_le le_add_self))
      exact ⟨⟨⟨β, hβ⟩, s⟩, fun y hy hy1 hZy => hs y hy hy1 hZy⟩

end Googology.Trans.PoR.InaccPsi.R2.Gd
