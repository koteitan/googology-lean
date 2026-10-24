import Googology.Trans.PoR.InaccPsi.R2.GfLd
import Googology.Trans.PoR.InaccPsi.R2.GeUnif

/-!
# THE UNIFORMITY THEOREM FOR EVERY CODE BELOW `ε_{Ω₁+1}`: the top of `gfB a` reads the atom `Γ_{Ω₁+2+a}`

`R2.GeUnif` for the layers `gfB a` of `R2.GfTow`, with the atoms `gfAt` of `R2.GfAt` (the generic `Ge.geq_sup`,
`Ge.gxTh_le_of` are reused):

* `gfLim_top` (**the term-offset limit top reads `cQs c`**), `gfLim_poly` (**its layer has terms for every code below
  `cQs c`**), `gtc_one_add`, `gfB_zero`, `GfPolyG.mono`;
* `gfB_codes` (**THE UNIFORMITY THEOREM**: for every code `a < ε_{Ω₁+1}`, `E_{gfB a}(y) = Θ_y(Γ_{Ω₁+1+(1+a)})` at
  every strongly critical `y` above `gtc a`, and every code below `Γ_{Ω₁+1+(1+a)}` over a base above `gtc a` is read
  by a term of `gfB a`; the base from `Gd.gdB_codes`, the successor by the term-offset ladder, the limit by the union:
  the codes below `Γ_{Ω₁+1+a}` lie below some atom `Γ_{Ω₁+1+b}`, `b < a`, `gtc b < y`, `R2.GfRd.gfCl_lt_G`).

No new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gf

open Googology.Trans.PoR.InaccPsi.R2.Ge
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph Googology.Trans.PoR.InaccPsi.R2.Xt Lu
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Lp Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Gd

section Lim

variable {B : GdB} {c : Ordinal.{0}} (hc : ∀ Z, SC Z → B.g < Z → GxCl Z (gfAt Z) c) (hcO : Om 1 ≤ c)
  (hKE : ∀ y, SC y → y < Om 1 → B.g < y → B.K.E y = gxTh y (gfAt y) c) {e : Ordinal.{0} → Ordinal.{0}}
  (H : GeqH B e)
include hc hKE H

/-- **The term-offset limit top reads the code `cQs c`**: `ϑʸ(Ω₁·Ω₁ + e(y)) = Θ_y(cQs c)` above the gate. -/
theorem gfLim_top {y : Ordinal.{0}} (hy : SC y) (hy1 : y < Om 1) (hg : B.g < y) :
    gq (e y) y = gxTh y (gfAt y) (cQs c) := by
  rw [geq_sup H (gg_SC_eps hy) (lp_y1 hy1) hg, cQs, gcTh_iSup]
  exact iSup_congr fun n => gfTop_th hc hKE n y hy hy1 hg

include hcO in
/-- **The term-offset limit layer has terms for every code below `cQs c`.** -/
theorem gfLim_poly (hKP : GfPolyG B.K.sys c) : GfPolyG (geqUSys B e H) (cQs c) := by
  intro Z d hg hd hdE
  obtain ⟨n, hn⟩ := cQs_lt hdE
  obtain ⟨s, hs⟩ := gfPoly hc hcO hKE hKP n Z d hg hd hn
  exact ⟨s, fun y hy hy1 hZy => ⟨(hs y hy hy1 hZy).1.1, (hs y hy hy1 hZy).2⟩⟩

end Lim

theorem gtc_one_add {b Z : Ordinal.{0}} (hb : b < gfE) (hZ : IsSuccLimit Z) (hg : gtc b < Z) :
    1 + b < gfE ∧ gtc (1 + b) < Z := by
  rcases le_or_gt ω b with h | h
  · rw [one_add_of_omega0_le h]; exact ⟨hb, hg⟩
  · have e : 1 + b = b + 1 := by
      obtain ⟨n, rfl⟩ := lt_omega0.1 h
      calc (1 : Ordinal.{0}) + n = ((1 + n : ℕ) : Ordinal.{0}) := by norm_cast
        _ = ((n + 1 : ℕ) : Ordinal.{0}) := by rw [Nat.add_comm]
        _ = n + 1 := by norm_cast
    rw [e]
    have hb1 : b + 1 < gfE := eW_indec.add_lt hb ((Lu.lu_one_lt_E Rj.rj_Om1_inE).trans Om1_lt_eW)
    exact ⟨hb1, (rdc_succ b hb 0).2.2.trans_lt (hZ.add_one_lt hg)⟩

theorem gfB_zero (ha : (0 : Ordinal.{0}) < gfE) : gfB 0 ha = GdB.ofLp (lpTB 1) 0 := by
  show (gfRec 0 ha).1 = _
  unfold gfRec
  rw [Ordinal.limitRecOn_zero]
  rfl

theorem GfPolyG.mono {g g' E : Ordinal.{0}} {X : GdSys g} (hP : GfPolyG X E) (h : g ≤ g') :
    GfPolyG (X.mono h) E := fun Z d hg hd hdE => hP Z d (h.trans_lt hg) hd hdE

/-- **THE UNIFORMITY THEOREM** for every code `a < ε_{Ω₁+1}`: the top of `gfB a` reads `Γ_{Ω₁+1+(1+a)}` at every
strongly critical `y` above `gtc a`, and `gfB a` has terms for every code below it over every base above `gtc a`. -/
theorem gfB_codes (S : InaccSeq.{0}) : ∀ a : Ordinal.{0}, ∀ ha : a < gfE,
    (∀ y, SC y → y < Om 1 → gtc a < y → (gfB a ha).K.E y = gxTh y (gfAt y) (gcG (1 + a))) ∧
    GfPolyG (gfB a ha).K.sys (gcG (1 + a)) := by
  intro a
  induction a using WellFoundedLT.induction with
  | ind a IH0 =>
  rcases zero_or_succ_or_isSuccLimit a with rfl | ⟨δ, rfl⟩ | hα
  · intro ha
    -- the start: `Gd.gdB_codes` at `0`
    obtain ⟨hG1, hG2⟩ := gdB_codes S 0
    rw [gdB_zero] at hG1 hG2
    have e1 : gcG (1 + 0) ≤ gdV := gcG_le (by rw [add_zero]; exact le_add_self)
    rw [gfB_zero]
    refine ⟨fun y hy hy1 _ => ?_, fun Z d hg hd hdE => ?_⟩
    · rw [hG1 y hy hy1 hy.1, gfTh_eq_gdTh hy hy1 e1]
    · obtain ⟨s, hs⟩ := hG2 Z d hg (gdCl_of_gfCl hd (hdE.trans_le e1)) hdE
      refine ⟨s, fun y hy hy1 hZy => ⟨(hs y hy hy1 hZy).1, ?_⟩⟩
      rw [(hs y hy hy1 hZy).2, gfTh_eq_gdTh hy hy1 ((hdE.trans_le e1).le)]
  · rw [succ_eq_add_one] at IH0 ⊢
    intro ha
    have hδ : δ < gfE := (lt_add_one δ).trans ha
    obtain ⟨ihE, ihP⟩ := IH0 δ (lt_add_one δ) hδ
    have hg0 : (gfB δ hδ).g = gtc δ := gfB_g hδ
    have hc : ∀ Z, SC Z → (gfB δ hδ).g < Z → GxCl Z (gfAt Z) (gcG (1 + δ)) := fun Z hZ hg => by
      rw [hg0] at hg
      obtain ⟨h1, h2⟩ := gtc_one_add hδ hZ.isSuccLimit hg
      exact GxCl.atom (gfG_atom h1 h2)
    have hcO : Om 1 ≤ gcG (1 + δ) := (gcG_Om1_lt _).le
    have hKE : ∀ y, SC y → y < Om 1 → (gfB δ hδ).g < y →
        (gfB δ hδ).K.E y = gxTh y (gfAt y) (gcG (1 + δ)) :=
      fun y hy hy1 hg => ihE y hy hy1 (hg0 ▸ hg)
    have hQ : cQs (gcG (1 + δ)) = gcG (1 + (δ + 1)) := by rw [gc_cQs, add_assoc]
    have H := gfH_succ (gfRec δ hδ) ha
    rw [gfB_succ δ ha]
    refine ⟨fun y hy hy1 hδy => ?_, fun Z d hg hd hdE => ?_⟩
    · show gq (1 + rdc δ y + 1) y = _
      have hgy : (gfB δ hδ).g < y := by rw [hg0]; exact (rdc_succ δ hδ 0).2.1.trans_lt hδy
      rw [gfLim_top (e := fun x => 1 + rdc δ x + 1) hc hKE H hy hy1 hgy, hQ]
    · have hP := (gfLim_poly hc hcO hKE H ihP).mono (gf_g_succ (gfRec δ hδ) ha)
      rw [hQ] at hP
      exact hP Z d hg hd hdE
  · intro ha
    have IH : ∀ b, ∀ hb : b < a, (∀ y, SC y → y < Om 1 → gtc b < y →
        (gfB b (hb.trans ha)).K.E y = gxTh y (gfAt y) (gcG (1 + b))) ∧
        GfPolyG (gfB b (hb.trans ha)).K.sys (gcG (1 + b)) := fun b hb => IH0 b hb (hb.trans ha)
    have hα' : 1 + a = a := one_add_of_omega0_le (omega0_le_of_isSuccLimit hα)
    rw [hα', gfB_lim hα ha]
    refine ⟨fun y hy hy1 hαy => ?_, ?_⟩
    · have hyE := gg_SC_eps hy
      have hy1' := lp_y1 hy1
      obtain ⟨_, _, _, -, -, -, -, -, hF⟩ := rdc_lim_facts hα ha
      obtain ⟨-, -, -, -, e5, e6⟩ := hF y hyE hαy
      show gq (1 + rdc a y) y = _
      have hlE := rdc_lt_eN hyE a hαy
      refine le_antisymm (le_of_forall_lt fun v hv => ?_) (gxTh_le_of fun d hd hdlt => ?_)
      · rw [e5] at hv
        obtain ⟨ν, hν, hvν⟩ := ge_lt_lim_iff hyE hy1' e6 hlE v hv
        obtain ⟨b, hb, hgb, hsb⟩ := rdc_surj hyE hy1'.le ha hαy hν
        have h1 : gq ν y ≤ gq (1 + ν) y := by
          rw [← hsb]; exact geq_mono hyE hy1' (gfO_lt (hb.trans ha) hyE hgb) le_add_self
        have h2 : gq (1 + ν) y = gxTh y (gfAt y) (gcG (1 + b)) := by
          rw [← hsb, ← gfB_E (hb.trans ha) hyE hy1' hgb]; exact (IH b hb).1 y hy hy1 hgb
        calc v < gq ν y := hvν
          _ ≤ gq (1 + ν) y := h1
          _ = gxTh y (gfAt y) (gcG (1 + b)) := h2
          _ ≤ gxTh y (gfAt y) (gcG a) := gxTh_mono (gcG_le (gc_one_add_lt hα hb).le)
      · obtain ⟨b, hb, hgb, hdb⟩ := gfCl_lt_G hy hy1.le hα ha.le hd hdlt
        have h2 : gxTh y (gfAt y) (gcG (1 + b)) = gq (1 + rdc b y) y := by
          rw [← (IH b hb).1 y hy hy1 hgb, gfB_E (hb.trans ha) hyE hy1' hgb]
        calc gxTh y (gfAt y) d < gxTh y (gfAt y) (gcG b) := gxTh_lt hd hdb
          _ ≤ gxTh y (gfAt y) (gcG (1 + b)) := gxTh_mono (gcG_le le_add_self)
          _ = gq (1 + rdc b y) y := h2
          _ < gq (1 + rdc a y) y := geq_lt hyE hy1' (gfO_lt ha hyE hαy)
              ((gfF_lt hα ha (b := ⟨b, hb⟩) hyE hαy hgb).trans_le
                le_add_self)
    · refine gfPoly_of_SC _ _ ((gfUSys a hα ha (gfF fun b hb => gfRec b (hb.trans ha))).cst 0)
        fun Z hZ hZ1 hgZ d hd hdE => ?_
      obtain ⟨b, hb, hgb, hdb⟩ := gfCl_lt_G hZ hZ1.le hα ha.le hd hdE
      have hgb' : (gfB b (hb.trans ha)).g < Z := by rw [gfB_g]; exact hgb
      obtain ⟨s, hs⟩ := (IH b hb).2 Z d hgb' hd (hdb.trans_le (gcG_le le_add_self))
      exact ⟨⟨⟨b, hb⟩, s⟩, fun y hy hy1 hZy => ⟨⟨hgb.trans_le hZy, (hs y hy hy1 hZy).1⟩, (hs y hy hy1 hZy).2⟩⟩

end Googology.Trans.PoR.InaccPsi.R2.Gf
