import Googology.Trans.PoR.InaccPsi.R2.WqWit

/-!
# REFUTATION: the image clause of the restricted carry cannot hold for EVERY offset map with the map data

`a = L(k)`, `u₁ = υ_{a+1}`, `g = ω^{ω^{u₁+1}}`, `μ` a supply restart (Range, code `G₂+1`, below `L(ω)`, `WcRead0`,
`υ_μ < a`), `π = π_{υ_μ,υ_a}`, `m(z) = cdOff(cdExp z)`.

The map data asked of an offset map (`Sl.SlOff`, `f g = g'`, and the exponent clause `π(m z) ≤ m(f z)` only where
`m z < u₁` and `m z ∈ T^{a}[υ_μ]`) leave `f z` free at every offset `z` with `m z ≥ u₁`.  Take `z = ω^{u₁}`
(`m z = u₁`), `Os = {1, z, z+ω+1}` and the map `f x = x` (`x < ω²`), `f x = ω² + (x mod ω²)` (`x ≥ ω²`), so
`f z = ω²`, `m(f z) = 1`.  The decomposition `E = ub (z+ω+1) base + ub 1 base` of `r(a+z) = υ_{a+(z+ω+1)} + u₁` is
well formed, has offsets in `Os`, satisfies `Wf.WfR` (no leaves), and its image is `υ_{μ+(ω²+ω+1)} + υ_{μ+1}`, while
`r(μ+ω²) = υ_{μ+(ω²+ω+1)} + 1` (`Vr.vrEQ_code`).  So the image clause fails.

* `wqImgF_ref` (**for every supply restart `μ` below `L(k)` and every `β ≥ g` there are `Os ⊂ β`, `f`, `B` with the
  map data, `z ∈ Os` and a decomposition `E` with all the hypotheses of the image clause and
  `r(μ + f z) < img E`**; given `L(k+1) ≤ ν_C`).

The carry must therefore be asked for ONE suitable map (an `∃ f`), not for every map with the map data.

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Wq

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- **REFUTATION of the image clause for an arbitrary offset map with the map data.** -/
theorem wqImgF_ref (k : ℕ) (hν : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC) {μ : Ordinal.{0}}
    (hR : CdRange S μ) (hc : cdCode S μ = Ls.lsG S (0 + 1 + 1) + 1) (hω : upsilon μ < Nc.ncL S ω)
    (hr : Wc.WcRead0 S μ) (hμl : upsilon μ < upsilon (Nc.ncL S (k : Ordinal.{0}))) {β : Ordinal.{0}}
    (hgβ : ω ^ ω ^ (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1) + 1) ≤ β) :
    ∃ (Os : Finset Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}) (B z : Ordinal.{0}) (E : Vr.VrE),
      (∀ d ∈ Os, d < β) ∧ μ + B ≤ Nc.ncL S (k : Ordinal.{0}) ∧ ω ^ 2 ∣ B ∧ upsilon (μ + B) ≤ cdR S μ ∧
      Sl.SlOff f Os B ∧
      (ω ^ ω ^ (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1) + 1) ∈ Os →
        f (ω ^ ω ^ (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1) + 1)) = ω ^ ω ^ (upsilon (μ + 1) + 1)) ∧
      (∀ x ∈ Os, 0 < x → ω ^ 2 ∣ x → cdOff (cdExp x) < upsilon (Nc.ncL S (k : Ordinal.{0}) + 1) →
        cdOff (cdExp x) ∈ TB (upsilon (Nc.ncL S (k : Ordinal.{0}))) (upsilon μ) →
        pi (upsilon μ) (upsilon (Nc.ncL S (k : Ordinal.{0}))) (cdOff (cdExp x)) ≤ cdOff (cdExp (f x))) ∧
      z ∈ Os ∧ 0 < z ∧ ω ^ 2 ∣ z ∧ Vr.VrWF (Nc.ncL S (k : Ordinal.{0})) β E ∧
      Vr.vrVal (Nc.ncL S (k : Ordinal.{0})) E = cdR S (Nc.ncL S (k : Ordinal.{0}) + z) ∧
      Vr.VrOs (Nc.ncL S (k : Ordinal.{0})) Os E ∧ Wf.WfR (Nc.ncL S (k : Ordinal.{0})) μ E ∧
      cdR S (μ + f z) < Vr.vrImg (Nc.ncL S (k : Ordinal.{0})) μ f E := by
  classical
  have hm := upsilon_normal.strictMono
  obtain ⟨hl0, hu1E, hu2E, hu12, hu2L1, hL1E, hL1O, hbelow, hωL1⟩ := Vr.vr_facts (S := S) k
  set l := Nc.ncL S (k : Ordinal.{0}) with hldef
  have hlfix : upsilon l = l := Te.teUps_L k
  have hlL1 : l < Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) := Te.teL_lt_succ k
  have hlE : InE l := hlfix ▸ upsPt_inE (upsPt_upsilon hl0)
  have hlν : upsilon l < nuC := by rw [hlfix]; exact hlL1.trans_le hν
  set u1 := upsilon (l + 1) with hu1def
  have hu1ω : ω ≤ u1 := Vo.vo_omega_le hu1E (InE.pos hu1E)
  have hp : (0 : Ordinal.{0}) < ω ^ 2 := Vo.vo_e2 ▸ opow_pos (2 : Ordinal.{0}) omega0_pos
  have h1ω2 : (1 : Ordinal.{0}) < ω ^ 2 := one_lt_omega0.trans (le_self_add.trans_lt Vo.vo_om2)
  have hω1ω2 : ω + 1 < ω ^ 2 := (add_lt_add_right one_lt_two ω).trans Vo.vo_om2
  have hωω2 : ω ≤ ω ^ 2 := by rw [pow_two]; exact Ordinal.le_mul_left _ omega0_pos
  -- the offset `z = ω^{u₁}`
  set z := ω ^ u1 with hzdef
  have h2u1 : (2 : Ordinal.{0}) ≤ u1 := (natCast_lt_omega0 2).le.trans hu1ω
  have hzd : ω ^ 2 ∣ z := Vo.vo_e2 ▸ opow_dvd_opow ω h2u1
  have hz0 : 0 < z := opow_pos _ omega0_pos
  have hωz : ω ≤ z := Vr.vr_omega_le hz0.ne' hzd
  have hω2z : ω ^ 2 ≤ z := le_of_dvd hz0.ne' hzd
  have hzu : z < upsilon (l + 2) := hu2E.opow_lt hu12
  have hmz : cdOff (cdExp z) = u1 := by
    rw [hzdef, R2Skel.SkSX.skSX_cdExp_opow]; unfold cdOff; rw [if_neg (not_lt.2 hu1ω)]
  -- the witness offset `g` lies above `z + ω + 1`
  set g := ω ^ ω ^ (u1 + 1) with hgdef
  have hu1c : u1 < ω ^ (u1 + 1) := (lt_add_one u1).trans_le (right_le_opow _ one_lt_omega0)
  have hzg : z < g := (opow_lt_opow_iff_right one_lt_omega0).2 hu1c
  have hωg : ω < g := hωz.trans_lt hzg
  have hgP : IsPrincipal (· + ·) g := isPrincipal_add_omega0_opow _
  have hz1g : z + ω + 1 < g := hgP (hgP hzg hωg) (one_lt_omega0.trans hωg)
  have h1z : (1 : Ordinal.{0}) < z := h1ω2.trans_le hω2z
  have hzz1 : z < z + ω + 1 := by rw [add_assoc]; exact lt_add_of_pos_right z (lt_of_le_of_lt zero_le (lt_add_one ω))
  -- the offsets
  set Os : Finset Ordinal.{0} := {1, z, z + ω + 1} with hOsdef
  have hzO : z ∈ Os := by simp [hOsdef]
  have hOs : ∀ d ∈ Os, d = 1 ∨ d = z ∨ d = z + ω + 1 := by
    intro d hd; simpa [hOsdef] using hd
  -- the bound `B` of the map data (from `Wf.wfOffMap`)
  obtain ⟨f₀, B, hB1, hB2, hB3, hO₀, -, -, -, -⟩ :=
    Wf.wfOffMap (S := S) k hlfix.symm hR hc hω hr hμl hlν Os
  have hBbig : ω ^ 2 + (ω + 1) < B := by
    obtain ⟨hf0, hfd, -⟩ := Wk.wkOff_val hO₀ hzO hz0 hzd
    have hle : ω ^ 2 ≤ f₀ z := le_of_dvd hf0.ne' hfd
    have hres : f₀ (z + ω + 1) = f₀ z + (ω + 1) := by
      obtain ⟨q, hq⟩ := hzd
      rw [add_assoc, hq, hO₀.res q _ hω1ω2]
    have hbd := hO₀.bd (z + ω + 1) (by simp [hOsdef])
    rw [hres] at hbd
    exact (add_le_add_left hle _).trans_lt hbd
  -- the bad map
  set f : Ordinal.{0} → Ordinal.{0} := fun x => if x < ω ^ 2 then x else ω ^ 2 + x % ω ^ 2 with hfdef
  have hfs : ∀ r, r < ω ^ 2 → f r = r := fun r hr => by simp only [hfdef]; rw [if_pos hr]
  have hfq : ∀ q r, q ≠ 0 → r < ω ^ 2 → f (ω ^ 2 * q + r) = ω ^ 2 + r := by
    intro q r hq hr
    have hge : ω ^ 2 ≤ ω ^ 2 * q + r := by
      have : ω ^ 2 * 1 ≤ ω ^ 2 * q :=
        mul_le_mul_right (Order.one_le_iff_pos.2 (pos_iff_ne_zero.2 hq)) _
      rw [mul_one] at this; exact this.trans le_self_add
    simp only [hfdef]
    rw [if_neg (not_lt.2 hge), Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hr]
  obtain ⟨q₀, hq₀⟩ := hzd
  have hq₀0 : q₀ ≠ 0 := by rintro rfl; rw [mul_zero] at hq₀; exact hz0.ne' hq₀
  have hv0 : f 0 = 0 := hfs 0 hp
  have hv1 : f 1 = 1 := hfs 1 h1ω2
  have hvz : f z = ω ^ 2 := by
    have := hfq q₀ 0 hq₀0 hp; rw [add_zero, add_zero, ← hq₀] at this; exact this
  have hvz1 : f (z + ω + 1) = ω ^ 2 + (ω + 1) := by
    rw [add_assoc, hq₀]; exact hfq q₀ _ hq₀0 hω1ω2
  have hfO : Sl.SlOff f Os B := by
    refine ⟨hv0, fun q r hr => ?_, fun q => ?_, ?_, ?_⟩
    · by_cases hq : q = 0
      · rw [hq, mul_zero, zero_add, hfs r hr, hv0, zero_add]
      · have h0 := hfq q 0 hq hp
        rw [add_zero, add_zero] at h0
        rw [hfq q r hq hr, h0]
    · by_cases hq : q = 0
      · rw [hq, mul_zero, hv0]; exact dvd_zero _
      · have h0 := hfq q 0 hq hp
        rw [add_zero, add_zero] at h0
        rw [h0]
    · intro a ha b hb hab
      have ha' : a = 0 ∨ a = 1 ∨ a = z ∨ a = z + ω + 1 := by simpa [hOsdef] using ha
      have hb' : b = 0 ∨ b = 1 ∨ b = z ∨ b = z + ω + 1 := by simpa [hOsdef] using hb
      have hv2 : ω ^ 2 < ω ^ 2 + (ω + 1) := lt_add_of_pos_right _ (lt_of_le_of_lt zero_le (lt_add_one ω))
      have h01 : (0 : Ordinal.{0}) < 1 := zero_lt_one
      rcases ha' with rfl | rfl | rfl | rfl <;> rcases hb' with rfl | rfl | rfl | rfl <;>
        simp only [hv0, hv1, hvz, hvz1] <;> order
    · intro d hd
      have hB0 : ω ^ 2 < B := (lt_add_of_pos_right _ (lt_of_le_of_lt zero_le (lt_add_one ω))).trans hBbig
      rcases hOs d hd with rfl | rfl | rfl
      · rw [hv1]; exact h1ω2.trans hB0
      · rw [hvz]; exact hB0
      · rw [hvz1]; exact hBbig
  -- the decomposition
  have hzβ : z + ω + 1 < β := hz1g.trans_le hgβ
  have h1β : (1 : Ordinal.{0}) < β := (h1z.trans hzz1).trans hzβ
  set E : Vr.VrE := .add (.ub (z + ω + 1) .base) (.ub 1 .base) with hEdef
  have hh0 : 0 < z + ω + 1 := lt_of_le_of_lt zero_le (lt_add_one _)
  have hWF : Vr.VrWF l β E :=
    ⟨⟨hh0, hzβ, trivial, trivial, trivial, le_rfl, upsilon_normal.strictMono (lt_succ _)⟩,
      ⟨one_pos, h1β, trivial, trivial, trivial, le_rfl, upsilon_normal.strictMono (lt_succ _)⟩⟩
  have hzd' : ω ^ 2 ∣ z := ⟨q₀, hq₀⟩
  have hval : Vr.vrVal l E = cdR S (l + z) := by
    show upsilon (l + (z + ω + 1)) + upsilon (l + 1) = _
    rw [Vr.vrR_inner k hν hz0 hzd' hzu, Vo.voCode_add k hωz hzu, hmz]
  have hOsE : Vr.VrOs l Os E := ⟨⟨by simp [hOsdef], trivial⟩, ⟨by simp [hOsdef], trivial⟩⟩
  have hWR : Wf.WfR l μ E := ⟨fun p hp => by simp [Ub.UbT.lvs] at hp, fun p hp => by simp [Ub.UbT.lvs] at hp⟩
  -- the map data: witness clause (vacuous) and exponent clause
  have hgO : g ∉ Os := by
    intro hg
    rcases hOs g hg with h | h | h
    · exact absurd h (h1z.trans hzg).ne'
    · exact absurd h hzg.ne'
    · exact absurd h hz1g.ne'
  have hexp : ∀ x ∈ Os, 0 < x → ω ^ 2 ∣ x → cdOff (cdExp x) < upsilon (l + 1) →
      cdOff (cdExp x) ∈ TB (upsilon l) (upsilon μ) →
      pi (upsilon μ) (upsilon l) (cdOff (cdExp x)) ≤ cdOff (cdExp (f x)) := by
    intro x hx _ hxd hxl _
    exfalso
    rcases hOs x hx with rfl | rfl | rfl
    · exact absurd (le_of_dvd one_ne_zero hxd) (not_le.2 h1ω2)
    · rw [hmz] at hxl; exact lt_irrefl _ hxl
    · have h1 : ω ^ 2 ∣ ω + 1 := by
        rw [add_assoc] at hxd; exact (Ordinal.dvd_add_iff hzd').1 hxd
      exact absurd (le_of_dvd (lt_of_le_of_lt zero_le (lt_add_one ω)).ne' h1) (not_le.2 hω1ω2)
  -- the failure of the image clause (`Vr.vrEQ_code`)
  have hμl' : μ < l := by have := hm.lt_iff_lt.1 hμl; exact this
  have h2l : (2 : Ordinal.{0}) < l := (natCast_lt_omega0 2).trans_le (Vo.vo_omega_le hlE hl0)
  have hω2l : ω ^ 2 < l := Vo.vo_e2 ▸ hlE.opow_lt h2l
  have hωl : ω < l := (hωω2.trans_lt hω2l)
  have h1l : (1 : Ordinal.{0}) < l := one_lt_omega0.trans hωl
  have hμ2l : μ + 2 < l := hlE.add_lt hμl' h2l
  have hu2l : upsilon (μ + 2) < l := hlfix ▸ hm hμ2l
  have hn : upsilon (μ + 2) < Nm.Pv S (Om ω + Nc.ncPp S * (ω + 1)) := by
    rw [← Lw.lw_L_eq]
    exact hu2l.trans ((Te.teL_lt_omega (S := S) k).trans (Qq.qqL_lt_succ S))
  have hμ0 : 0 < μ := pos_iff_ne_zero.2 hR.1.1
  have hu2E' : InE (upsilon (μ + 2)) := upsPt_inE (upsPt_upsilon (hμ0.trans_le le_self_add))
  have hfu : f z < upsilon (μ + 2) := by
    rw [hvz, Vo.vo_e2]
    exact hu2E'.opow_lt ((natCast_lt_omega0 2).trans_le (Vo.vo_omega_le hu2E' (InE.pos hu2E')))
  have hC : upsilon (μ + f z + ω + 1) < nuC := by
    rw [hvz]
    have : μ + ω ^ 2 + ω + 1 < l := hlE.add_lt (hlE.add_lt (hlE.add_lt hμl' hω2l) hωl) h1l
    exact (hm this).trans hlν
  have hfd : ω ^ 2 ∣ f z := by rw [hvz]
  have hωf : ω ≤ f z := by rw [hvz]; exact hωω2
  have hE1 : Vr.vrImg l μ f (.ub 1 .base) = upsilon (μ + 1) := by
    show Ub.UbT.ev (upsilon (μ + f 1)) (Ub.UbT.map (Vr.vrLf l μ f) .base) = _
    simp only [Ub.UbT.map, Ub.UbT.ev, hv1]
  have hoff : cdOff (cdExp (f z)) = 1 := by
    rw [hvz, Vo.vo_e2, R2Skel.SkSX.skSX_cdExp_opow]
    unfold cdOff
    have h2ω : (2 : Ordinal.{0}) < ω := by exact_mod_cast natCast_lt_omega0 2
    rw [if_pos h2ω, show (2 : Ordinal.{0}) = 1 + 1 from one_add_one_eq_two.symm, Ordinal.add_sub_cancel]
  have hbad : ¬ Vr.vrImg l μ f E ≤ cdR S (μ + f z) := by
    intro hle
    have h := (Vr.vrEQ_code (S := S) (l := l) (.ub 1 .base) hfO hzd' hR.1 hn hfd hωf hfu hC).1 hle
    rw [hE1, hoff] at h
    have hu1' : InE (upsilon (μ + 1)) := upsPt_inE (upsPt_upsilon (hμ0.trans_le le_self_add))
    exact absurd (one_lt_omega0.trans_le (Vo.vo_omega_le hu1' (InE.pos hu1'))) (not_lt.2 h)
  refine ⟨Os, f, B, z, E, fun d hd => ?_, hB1, hB2, hB3, hfO, fun hg => absurd hg hgO, hexp, hzO, hz0, hzd',
    hWF, hval, hOsE, hWR, lt_of_not_ge hbad⟩
  rcases hOs d hd with rfl | rfl | rfl
  · exact h1β
  · exact hzz1.trans hzβ
  · exact hzβ

end Googology.Trans.PoR.InaccPsi.R2.Wq
