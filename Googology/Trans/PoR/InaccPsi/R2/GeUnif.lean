import Googology.Trans.PoR.InaccPsi.R2.GeLd

/-!
# THE UNIFORMITY THEOREM FOR EVERY CODE BELOW `Ω₁^ω`: the top of `geB a` reads the atom `Γ_{Ω₁+2+a}`

`R2.GdUnif.gdB_codes` for the layers `geB a` of `R2.GeTow`, with the atoms `geAt` of `R2.GeAt`:

* `geq_sup` (`ϑˣ(Ω₁·Ω₁ + e(x)) = sup_n gdP B n x` for a term offset), `geLim_top` (**the term-offset limit top reads
  `cQs c`**), `geLim_poly` (**its layer has terms for every code below `cQs c`**);
* `gxTh_le_of` (a reading is at most `v` when every code below is read below `v`), `gate_one_add`;
* `geB_codes` (**THE UNIFORMITY THEOREM**: for every code `a < Ω₁^ω`, `E_{geB a}(y) = Θ_y(Γ_{Ω₁+1+(1+a)})` at every
  strongly critical `y` above `gate a`, and every code below `Γ_{Ω₁+1+(1+a)}` over a base above `gate a` is read by a
  term of `geB a`; the base from `Gd.gdB_codes`, the successor by the term-offset ladder, the limit by the union:
  the codes below `Γ_{Ω₁+1+a}` lie below some atom `Γ_{Ω₁+1+b}`, `b < a`, `gate b < y`, `R2.GeRd.geCl_lt_G`).

No new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ge

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph Googology.Trans.PoR.InaccPsi.R2.Xt Lu
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Lp Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Gd

theorem geq_sup {B : GdB} {e : Ordinal.{0} → Ordinal.{0}} (H : GeqH B e) {x : Ordinal.{0}} (hx : InE x)
    (hx1 : x < Om1) (hg : B.g < x) : gq (e x) x = ⨆ n, gdP B n x :=
  le_antisymm (le_of_forall_lt fun v hv => by
      obtain ⟨n, hn⟩ := geq_lt_iff H hx hx1 hg v hv
      exact hn.trans_le (Ordinal.le_iSup (fun n => gdP B n x) n))
    (Ordinal.iSup_le fun n => (geq_gP_lt H hx hx1 hg n).le)

section Lim

variable {B : GdB} {c : Ordinal.{0}} (hc : ∀ Z, SC Z → B.g < Z → GxCl Z (geAt Z) c) (hcO : Om 1 ≤ c)
  (hKE : ∀ y, SC y → y < Om 1 → B.g < y → B.K.E y = gxTh y (geAt y) c) {e : Ordinal.{0} → Ordinal.{0}}
  (H : GeqH B e)
include hc hKE H

/-- **The term-offset limit top reads the code `cQs c`**: `ϑʸ(Ω₁·Ω₁ + e(y)) = Θ_y(cQs c)` above the gate. -/
theorem geLim_top {y : Ordinal.{0}} (hy : SC y) (hy1 : y < Om 1) (hg : B.g < y) :
    gq (e y) y = gxTh y (geAt y) (cQs c) := by
  rw [geq_sup H (gg_SC_eps hy) (lp_y1 hy1) hg, cQs, gcTh_iSup]
  exact iSup_congr fun n => geTop_th hc hKE n y hy hy1 hg

include hcO in
/-- **The term-offset limit layer has terms for every code below `cQs c`.** -/
theorem geLim_poly (hKP : GePolyG B.K.sys c) : GePolyG (geqUSys B e H) (cQs c) := by
  intro Z d hg hd hdE
  obtain ⟨n, hn⟩ := cQs_lt hdE
  obtain ⟨s, hs⟩ := gePoly hc hcO hKE hKP n Z d hg hd hn
  exact ⟨s, fun y hy hy1 hZy => ⟨(hs y hy hy1 hZy).1.1, (hs y hy hy1 hZy).2⟩⟩

end Lim

/-- **A reading is at most `v`** when every code below is read below `v`. -/
theorem gxTh_le_of {y m v : Ordinal.{0}} {At : Set Ordinal.{0}}
    (h : ∀ d, GxCl y At d → d < m → gxTh y At d < v) : gxTh y At m ≤ v := by
  classical
  unfold gxTh
  rw [Cd.cdOtp_eq]
  refine ciSup_le' fun d => ?_
  split_ifs with hd
  · exact Order.add_one_le_of_lt (h d.1 hd d.2)
  · exact zero_le

theorem gate_one_add {b Z : Ordinal.{0}} (hb : b < geW) (hZ : IsSuccLimit Z) (hg : gate b < Z) :
    1 + b < geW ∧ gate (1 + b) < Z := by
  rcases le_or_gt ω b with h | h
  · rw [one_add_of_omega0_le h]; exact ⟨hb, hg⟩
  · have e : 1 + b = b + 1 := by
      obtain ⟨n, rfl⟩ := lt_omega0.1 h
      calc (1 : Ordinal.{0}) + n = ((1 + n : ℕ) : Ordinal.{0}) := by norm_cast
        _ = ((n + 1 : ℕ) : Ordinal.{0}) := by rw [Nat.add_comm]
        _ = n + 1 := by norm_cast
    rw [e]
    have hb1 : b + 1 < geW := geW_indec.add_lt hb ((Lu.lu_one_lt_E Rj.rj_Om1_inE).trans Om1_lt_W)
    exact ⟨hb1, (sb_succ hb1 0).2.2.trans_lt (hZ.add_one_lt hg)⟩

theorem geB_zero (ha : (0 : Ordinal.{0}) < geW) : geB 0 ha = GdB.ofLp (lpTB 1) 0 := by
  show (geRec 0 ha).1 = _
  unfold geRec
  rw [Ordinal.limitRecOn_zero]
  rfl

theorem GePolyG.mono {g g' E : Ordinal.{0}} {X : GdSys g} (hP : GePolyG X E) (h : g ≤ g') :
    GePolyG (X.mono h) E := fun Z d hg hd hdE => hP Z d (h.trans_lt hg) hd hdE

/-- **THE UNIFORMITY THEOREM** for every code `a < Ω₁^ω`: the top of `geB a` reads `Γ_{Ω₁+1+(1+a)}` at every
strongly critical `y` above `gate a`, and `geB a` has terms for every code below it over every base above `gate a`. -/
theorem geB_codes (S : InaccSeq.{0}) : ∀ a : Ordinal.{0}, ∀ ha : a < geW,
    (∀ y, SC y → y < Om 1 → gate a < y → (geB a ha).K.E y = gxTh y (geAt y) (gcG (1 + a))) ∧
    GePolyG (geB a ha).K.sys (gcG (1 + a)) := by
  intro a
  induction a using WellFoundedLT.induction with
  | ind a IH0 =>
  rcases zero_or_succ_or_isSuccLimit a with rfl | ⟨δ, rfl⟩ | hα
  · intro ha
    -- the start: `Gd.gdB_codes` at `0`
    obtain ⟨hG1, hG2⟩ := gdB_codes S 0
    rw [gdB_zero] at hG1 hG2
    have e1 : gcG (1 + 0) ≤ gdV := gcG_le (by rw [add_zero]; exact le_add_self)
    rw [geB_zero]
    refine ⟨fun y hy hy1 _ => ?_, fun Z d hg hd hdE => ?_⟩
    · rw [hG1 y hy hy1 hy.1, geTh_eq_gdTh hy hy1 e1]
    · obtain ⟨s, hs⟩ := hG2 Z d hg (gdCl_of_geCl hd (hdE.trans_le e1)) hdE
      refine ⟨s, fun y hy hy1 hZy => ⟨(hs y hy hy1 hZy).1, ?_⟩⟩
      rw [(hs y hy hy1 hZy).2, geTh_eq_gdTh hy hy1 ((hdE.trans_le e1).le)]
  · rw [succ_eq_add_one] at IH0 ⊢
    intro ha
    have hδ : δ < geW := (lt_add_one δ).trans ha
    obtain ⟨ihE, ihP⟩ := IH0 δ (lt_add_one δ) hδ
    have hg0 : (geB δ hδ).g = gate δ := geB_g hδ
    have hc : ∀ Z, SC Z → (geB δ hδ).g < Z → GxCl Z (geAt Z) (gcG (1 + δ)) := fun Z hZ hg => by
      rw [hg0] at hg
      obtain ⟨h1, h2⟩ := gate_one_add hδ hZ.isSuccLimit hg
      exact GxCl.atom (geG_atom h1 h2)
    have hcO : Om 1 ≤ gcG (1 + δ) := (gcG_Om1_lt _).le
    have hKE : ∀ y, SC y → y < Om 1 → (geB δ hδ).g < y →
        (geB δ hδ).K.E y = gxTh y (geAt y) (gcG (1 + δ)) :=
      fun y hy hy1 hg => ihE y hy hy1 (hg0 ▸ hg)
    have hQ : cQs (gcG (1 + δ)) = gcG (1 + (δ + 1)) := by rw [gc_cQs, add_assoc]
    have H := geH_succ (geRec δ hδ) ha
    rw [geB_succ δ ha]
    refine ⟨fun y hy hy1 hδy => ?_, fun Z d hg hd hdE => ?_⟩
    · show gq (1 + sbc δ y + 1) y = _
      have hgy : (geB δ hδ).g < y := by rw [hg0]; exact (sb_succ ha 0).2.1.trans_lt hδy
      rw [geLim_top (e := fun x => 1 + sbc δ x + 1) hc hKE H hy hy1 hgy, hQ]
    · have hP := (geLim_poly hc hcO hKE H ihP).mono (ge_g_succ (geRec δ hδ) ha)
      rw [hQ] at hP
      exact hP Z d hg hd hdE
  · intro ha
    have IH : ∀ b, ∀ hb : b < a, (∀ y, SC y → y < Om 1 → gate b < y →
        (geB b (hb.trans ha)).K.E y = gxTh y (geAt y) (gcG (1 + b))) ∧
        GePolyG (geB b (hb.trans ha)).K.sys (gcG (1 + b)) := fun b hb => IH0 b hb (hb.trans ha)
    have hα' : 1 + a = a := one_add_of_omega0_le (omega0_le_of_isSuccLimit hα)
    rw [hα', geB_lim hα ha]
    refine ⟨fun y hy hy1 hαy => ?_, ?_⟩
    · have hyE := gg_SC_eps hy
      have hy1' := lp_y1 hy1
      obtain ⟨a', k, d, -, -, -, hF⟩ := sb_lim_facts hα ha
      obtain ⟨-, -, -, -, e5, e6⟩ := hF y hyE hαy
      show gq (1 + sbc a y) y = _
      have hlE := sb_lt_eN ha hyE hαy
      refine le_antisymm (le_of_forall_lt fun v hv => ?_) (gxTh_le_of fun d hd hdlt => ?_)
      · rw [e5] at hv
        obtain ⟨ν, hν, hvν⟩ := ge_lt_lim_iff hyE hy1' e6 hlE v hv
        obtain ⟨b, hb, hgb, hsb⟩ := sb_surj ha hyE hy1' hαy hν
        have h1 : gq ν y ≤ gq (1 + ν) y := by
          rw [← hsb]; exact geq_mono hyE hy1' (geO_lt (hb.trans ha) hyE hgb) le_add_self
        have h2 : gq (1 + ν) y = gxTh y (geAt y) (gcG (1 + b)) := by
          rw [← hsb, ← geB_E (hb.trans ha) hyE hy1' hgb]; exact (IH b hb).1 y hy hy1 hgb
        calc v < gq ν y := hvν
          _ ≤ gq (1 + ν) y := h1
          _ = gxTh y (geAt y) (gcG (1 + b)) := h2
          _ ≤ gxTh y (geAt y) (gcG a) := gxTh_mono (gcG_le (gc_one_add_lt hα hb).le)
      · obtain ⟨b, hb, hgb, hdb⟩ := geCl_lt_G hy hy1.le hα ha.le hd hdlt
        have h2 : gxTh y (geAt y) (gcG (1 + b)) = gq (1 + sbc b y) y := by
          rw [← (IH b hb).1 y hy hy1 hgb, geB_E (hb.trans ha) hyE hy1' hgb]
        calc gxTh y (geAt y) d < gxTh y (geAt y) (gcG b) := gxTh_lt hd hdb
          _ ≤ gxTh y (geAt y) (gcG (1 + b)) := gxTh_mono (gcG_le le_add_self)
          _ = gq (1 + sbc b y) y := h2
          _ < gq (1 + sbc a y) y := geq_lt hyE hy1' (geO_lt ha hyE hαy)
              ((geF_lt hα ha (b := ⟨b, hb⟩) hyE hαy hgb).trans_le
                le_add_self)
    · refine gePoly_of_SC _ _ ((geUSys a hα ha (geF fun b hb => geRec b (hb.trans ha))).cst 0)
        fun Z hZ hZ1 hgZ d hd hdE => ?_
      obtain ⟨b, hb, hgb, hdb⟩ := geCl_lt_G hZ hZ1.le hα ha.le hd hdE
      have hgb' : (geB b (hb.trans ha)).g < Z := by rw [geB_g]; exact hgb
      obtain ⟨s, hs⟩ := (IH b hb).2 Z d hgb' hd (hdb.trans_le (gcG_le le_add_self))
      exact ⟨⟨⟨b, hb⟩, s⟩, fun y hy hy1 hZy => ⟨⟨hgb.trans_le hZy, (hs y hy hy1 hZy).1⟩, (hs y hy hy1 hZy).2⟩⟩

end Googology.Trans.PoR.InaccPsi.R2.Ge
