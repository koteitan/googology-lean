import Googology.Trans.PoR.InaccPsi.R2.ZhFix
import Googology.Trans.PoR.InaccPsi.R2.ZhCar
import Googology.Trans.PoR.InaccPsi.R2.WuWin
import Googology.Trans.PoR.InaccPsi.R2.WuSup

/-!
# The reach formula at every inner restart of a `υ`-fixed restart

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`Wu.wuR_X` gives `r(a + X) = υ_{a+(X+ω+1)} + X` only at `a = L(k)` and an `ε`-offset `X`.  Here the formula is proved
at every `υ`-fixed restart `μ` (an `ε`-number) and every offset `z` with `μ + z` not a `υ`-fixed point:
`r(μ + z) = υ_{μ+z+ω+1} + c(z)`, `c(z) = sup{k : ω^{1+k} ∣ z}` (`= -1 + e(z)`; `= z` at an `ε`-number `z`).
Every supply restart below `ν_C` is `υ`-fixed (`Zh.zhSup_fix`), so the formula holds at every supply restart.

* `zl_cL_add` (`c(μ + z) = c(z)` for an `ε`-number `μ`), `zl_lt_ups` (a restart that is no `ε`-number is not
  `υ`-fixed), `zl_notE_add` (`μ + z` is no `ε`-number when `0 < z < μ`, or `z` is no `ε`-number);
* `zlR_add` (**THE REACH FORMULA** at every inner restart of a `υ`-fixed restart);
* `zlMu_fix` (the supply restarts of the skeleton (Range, code `G₂+1`, below `L(ω)`, `Wc.WcRead0`) are `υ`-fixed below
  `ν_C`), `zlR_sup` (**the formula at every supply restart**);
* REFUTE-FIRST tests: `zlR_sup_one` (`z = ω²`: `r(μ+ω²) = υ_{μ+ω²+ω+1} + 1`), `zlR_sup_omega` (`z = ω^ω`:
  `r(μ+ω^ω) = υ_{μ+ω^ω+ω+1} + ω`), `zlR_sup_eps` (an `ε`-offset `X`: `r(μ+X) = υ_{μ+X+ω+1} + X`, the twin of
  `Wu.wuR_X`);
* `zl_short_lt` (a short reach `υ_{λ+g+ω+1} + c(g)` is below `υ_{λ+β}` once `g + ω² ≤ β`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zl

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- `c(μ + z) = c(z)` at an `ε`-number `μ`. -/
theorem zl_cL_add {μ z : Ordinal.{0}} (hE : InE μ) (hz : z ≠ 0) : cL (μ + z) = cL z := by
  unfold cL
  congr 1
  ext k
  simp only [Set.mem_setOf_eq]
  rcases le_or_gt (1 + k) μ with hk | hk
  · have hd : ω ^ (1 + k) ∣ μ := by
      have := opow_dvd_opow ω hk
      rwa [hE] at this
    exact Ordinal.dvd_add_iff hd
  · have hμ1 : μ + 1 ≤ 1 + k := Order.add_one_le_of_lt hk
    have hlt : μ < ω ^ (μ + 1) := by
      have := (opow_lt_opow_iff_right one_lt_omega0).2 (lt_add_one μ)
      rwa [hE] at this
    have habs : ∀ w, ω ^ (μ + 1) ≤ w → μ + w = w := fun w hw => Ordinal.add_of_omega0_opow_le hlt hw
    constructor
    · intro hd
      have hne : μ + z ≠ 0 := by
        intro h; exact hz (Ordinal.add_eq_zero_iff.1 h).2
      have h1 : ω ^ (μ + 1) ≤ μ + z :=
        (opow_le_opow_right omega0_pos hμ1).trans (le_of_dvd hne hd)
      have hz' : ω ^ (μ + 1) ≤ z := by
        by_contra hc
        push Not at hc
        have hP : IsPrincipal (· + ·) (ω ^ (μ + 1)) := isPrincipal_add_omega0_opow _
        exact absurd (hP hlt hc) (not_lt.2 h1)
      rwa [habs z hz'] at hd
    · intro hd
      have hz' : ω ^ (μ + 1) ≤ z :=
        (opow_le_opow_right omega0_pos hμ1).trans (le_of_dvd hz hd)
      rwa [habs z hz']

/-- A restart index that is no `ε`-number is not `υ`-fixed. -/
theorem zl_lt_ups {x : Ordinal.{0}} (hx0 : 0 < x) (hx : ¬ InE x) : x < upsilon x := by
  rcases eq_or_lt_of_le (upsilon_normal.strictMono.le_apply : x ≤ upsilon x) with h | h
  · exfalso; apply hx
    have := upsPt_inE (upsPt_upsilon hx0)
    rwa [← h] at this
  · exact h

/-- `μ + z` is no `ε`-number when `0 < z < μ` and `μ` is an `ε`-number. -/
theorem zl_notE_add {μ z : Ordinal.{0}} (hz0 : 0 < z) (hzμ : z < μ) : ¬ InE (μ + z) := by
  intro h
  have h1 : μ < μ + z := lt_add_of_pos_right μ hz0
  have h2 : z < μ + z := hzμ.trans h1
  exact lt_irrefl _ (h.add_lt h1 h2)

/-- **THE REACH FORMULA** at every inner restart of a `υ`-fixed restart `μ`: if `0 < z`, `ω² ∣ z`, `μ + z` is not a
`υ`-fixed point and `υ_{μ+z} < ν_C`, `υ_{μ+z} < P(η₁)`, then `r(μ + z) = υ_{μ+z+ω+1} + c(z)`. -/
theorem zlR_add {μ z η1 : Ordinal.{0}} (hμ : IsRestartIdx μ) (hE : InE μ) (hz0 : 0 < z) (hzd : ω ^ 2 ∣ z)
    (hfix : ¬ InE (μ + z)) (hν : upsilon (μ + z) < nuC) (hn : upsilon (μ + z) < Nm.Pv S η1) :
    cdR S (μ + z) = cdDelta (μ + z) + cL z := by
  have hpos : 0 < μ + z := hz0.trans_le le_add_self
  have hl : IsRestartIdx (μ + z) := ⟨hpos.ne', dvd_add hμ.2 hzd⟩
  have hww : ω * ω < μ + z := Zh.zh_ww_lt hμ (lt_add_of_pos_right μ hz0)
  rw [Zh.zhR_nonfix hl hww (zl_lt_ups hpos hfix) hν hn, zl_cL_add hE hz0.ne']

/-- **THE REACH FORMULA, `υ`-form**: as `zlR_add` with "`μ + z` not `υ`-fixed" (`μ + z < υ_{μ+z}`) in place of
"`μ + z` no `ε`-number" (so `ε`-offsets `X < υ_{μ+X}` are included, as in `Wu.wuR_X`). -/
theorem zlR_addU {μ z η1 : Ordinal.{0}} (hμ : IsRestartIdx μ) (hE : InE μ) (hz0 : 0 < z) (hzd : ω ^ 2 ∣ z)
    (hfix : μ + z < upsilon (μ + z)) (hν : upsilon (μ + z) < nuC) (hn : upsilon (μ + z) < Nm.Pv S η1) :
    cdR S (μ + z) = cdDelta (μ + z) + cL z := by
  have hpos : 0 < μ + z := hz0.trans_le le_add_self
  have hl : IsRestartIdx (μ + z) := ⟨hpos.ne', dvd_add hμ.2 hzd⟩
  have hww : ω * ω < μ + z := Zh.zh_ww_lt hμ (lt_add_of_pos_right μ hz0)
  rw [Zh.zhR_nonfix hl hww hfix hν hn, zl_cL_add hE hz0.ne']

/-- Not `υ`-fixed means below its `υ`. -/
theorem zl_lt_of_ne {x : Ordinal.{0}} (h : ¬ upsilon x = x) : x < upsilon x :=
  lt_of_le_of_ne upsilon_normal.strictMono.le_apply (Ne.symm h)

/-- `ω² ≤ φ(1, u+1)`. -/
theorem zl_w2_le_wuX (u : Ordinal.{0}) : ω ^ 2 ≤ Wu.wuX u := by
  have hE := Wu.wuX_E u
  have h2 : (2 : Ordinal.{0}) < Wu.wuX u :=
    (natCast_lt_omega0 2).trans_le (Vo.vo_omega_le hE (InE.pos hE))
  rw [Vo.vo_e2]; exact (hE.opow_lt h2).le

/-- **The supply restarts of the skeleton are `υ`-fixed below `ν_C`** (Range, code `G₂ + 1`, below `L(ω)`,
`Wc.WcRead0`). -/
theorem zlMu_fix {μ : Ordinal.{0}} (hR : CdRange S μ) (hc : cdCode S μ = Ls.lsG S (0 + 1 + 1) + 1)
    (hω : upsilon μ < Nc.ncL S ω) (hr : Wc.WcRead0 S μ) (hν : upsilon μ < nuC) : upsilon μ = μ := by
  have hlong : upsilon (μ + ω ^ 2) ≤ cdR S μ :=
    Wu.wuSup_lt (k := 0) hR hc hω hr (zl_w2_le_wuX _)
  have hww : ω * ω < μ := lt_of_lt_of_le Cp.cp_ww_lt_B0 hR.2.1
  exact Zh.zhSup_fix hR.1 hww hν (Wc.wcX_pv hR hc hω) hlong

/-- **The reach formula at every supply restart**: `μ` as in `zlMu_fix`, `0 < z`, `ω² ∣ z`, `μ + z` not
`υ`-fixed, `υ_{μ+z} < ν_C` give `r(μ + z) = υ_{μ+z+ω+1} + c(z)`. -/
theorem zlR_sup {μ z : Ordinal.{0}} (hR : CdRange S μ) (hc : cdCode S μ = Ls.lsG S (0 + 1 + 1) + 1)
    (hω : upsilon μ < Nc.ncL S ω) (hr : Wc.WcRead0 S μ) (hz0 : 0 < z) (hzd : ω ^ 2 ∣ z)
    (hfix : ¬ InE (μ + z)) (hν : upsilon (μ + z) < nuC) (hzL : upsilon (μ + z) < Nc.ncL S (ω + 1)) :
    cdR S (μ + z) = cdDelta (μ + z) + cL z := by
  have hμν : upsilon μ < nuC :=
    (upsilon_normal.strictMono (lt_add_of_pos_right μ hz0)).trans hν
  have hfixμ := zlMu_fix hR hc hω hr hμν
  have hE : InE μ := by
    have := upsPt_inE (upsPt_upsilon (pos_iff_ne_zero.2 hR.1.1)); rwa [hfixμ] at this
  refine zlR_add hR.1 hE hz0 hzd hfix hν (η1 := Om ω + Nc.ncPp S * (ω + 1)) ?_
  rw [← Lw.lw_L_eq]; exact hzL

/-- REFUTE-FIRST test `g = 1` (the offset `ω²`, code `1`): `r(μ + ω²) = υ_{μ+ω²+ω+1} + 1` at every supply restart. -/
theorem zlR_sup_one {μ : Ordinal.{0}} (hR : CdRange S μ) (hc : cdCode S μ = Ls.lsG S (0 + 1 + 1) + 1)
    (hω : upsilon μ < Nc.ncL S ω) (hr : Wc.WcRead0 S μ) (hν : upsilon (μ + ω ^ 2) < nuC)
    (hzL : upsilon (μ + ω ^ 2) < Nc.ncL S (ω + 1)) :
    cdR S (μ + ω ^ 2) = cdDelta (μ + ω ^ 2) + 1 := by
  have h2 : (0 : Ordinal.{0}) < ω ^ 2 := by rw [Vo.vo_e2]; exact opow_pos _ omega0_pos
  have hμν : upsilon μ < nuC := (upsilon_normal.strictMono (lt_add_of_pos_right μ h2)).trans hν
  have hfixμ := zlMu_fix hR hc hω hr hμν
  have hμ0 : 0 < μ := pos_iff_ne_zero.2 hR.1.1
  have hE : InE μ := by have := upsPt_inE (upsPt_upsilon hμ0); rwa [hfixμ] at this
  have hlt : ω ^ 2 < μ := by
    rw [Vo.vo_e2]; exact hE.opow_lt ((natCast_lt_omega0 2).trans_le (Vo.vo_omega_le hE hμ0))
  rw [zlR_sup hR hc hω hr h2 dvd_rfl (zl_notE_add h2 hlt) hν hzL, Vo.vo_e2, cL_opow le_rfl]
  norm_num

/-- REFUTE-FIRST test `g = ω` (the offset `ω^ω`, code `ω`): `r(μ + ω^ω) = υ_{μ+ω^ω+ω+1} + ω`. -/
theorem zlR_sup_omega {μ : Ordinal.{0}} (hR : CdRange S μ) (hc : cdCode S μ = Ls.lsG S (0 + 1 + 1) + 1)
    (hω : upsilon μ < Nc.ncL S ω) (hr : Wc.WcRead0 S μ) (hν : upsilon (μ + ω ^ ω) < nuC)
    (hzL : upsilon (μ + ω ^ ω) < Nc.ncL S (ω + 1)) :
    cdR S (μ + ω ^ ω) = cdDelta (μ + ω ^ ω) + ω := by
  have h2 : (0 : Ordinal.{0}) < ω ^ ω := opow_pos _ omega0_pos
  have hμν : upsilon μ < nuC := (upsilon_normal.strictMono (lt_add_of_pos_right μ h2)).trans hν
  have hfixμ := zlMu_fix hR hc hω hr hμν
  have hμ0 : 0 < μ := pos_iff_ne_zero.2 hR.1.1
  have hE : InE μ := by have := upsPt_inE (upsPt_upsilon hμ0); rwa [hfixμ] at this
  have hlt : ω ^ ω < μ := hE.opow_lt (Vo.vo_omega_le hE hμ0 |>.lt_of_ne (fun h => by
    have : InE ω := h ▸ hE
    exact absurd this (by
      unfold InE; intro h'
      have := (opow_lt_opow_iff_right one_lt_omega0).2 (one_lt_omega0)
      rw [h', opow_one] at this; exact lt_irrefl _ this)))
  have hd : ω ^ 2 ∣ ω ^ ω := by
    rw [Vo.vo_e2]; exact opow_dvd_opow ω (natCast_lt_omega0 2).le
  rw [zlR_sup hR hc hω hr h2 hd (zl_notE_add h2 hlt) hν hzL, cL_opow (natCast_lt_omega0 2).le]
  rw [Ordinal.sub_eq_of_add_eq (one_add_omega0)]

/-- REFUTE-FIRST test, the twin of `Wu.wuR_X`: an `ε`-offset `X < μ` gives `r(μ + X) = υ_{μ+X+ω+1} + X`. -/
theorem zlR_sup_eps {μ X : Ordinal.{0}} (hR : CdRange S μ) (hc : cdCode S μ = Ls.lsG S (0 + 1 + 1) + 1)
    (hω : upsilon μ < Nc.ncL S ω) (hr : Wc.WcRead0 S μ) (hXE : InE X) (hXμ : X < μ)
    (hν : upsilon (μ + X) < nuC) (hzL : upsilon (μ + X) < Nc.ncL S (ω + 1)) :
    cdR S (μ + X) = cdDelta (μ + X) + X := by
  have hX0 := InE.pos hXE
  have hd : ω ^ 2 ∣ X := by
    have h := Vo.vo_e2 ▸ opow_dvd_opow ω
      ((natCast_lt_omega0 2).trans_le (Vo.vo_omega_le hXE hX0)).le
    rwa [hXE] at h
  rw [zlR_sup hR hc hω hr hX0 hd (zl_notE_add hX0 hXμ) hν hzL]
  congr 1
  have h := Zh.zh_cL_eq (l := X) ⟨hX0.ne', hd⟩
  rw [h, Te.te_cdExp_E hXE]
  unfold cdOff; rw [if_neg (not_lt.2 (Vo.vo_omega_le hXE hX0))]

/-- **A short reach is below `υ_{λ+β}`** once `g + ω² ≤ β`. -/
theorem zl_short_lt {l g β : Ordinal.{0}} (hl : IsRestartIdx (l + g)) (hβ : g + ω ^ 2 ≤ β) :
    cdDelta (l + g) + cL (l + g) < upsilon (l + β) := by
  have hm := upsilon_normal.strictMono
  have hE : InE (upsilon (l + g + (ω + 2))) :=
    upsPt_inE (upsPt_upsilon (omega0_pos.trans_le (le_self_add.trans le_add_self)))
  have hδ : cdDelta (l + g) < upsilon (l + g + (ω + 2)) := by
    unfold cdDelta; refine hm ?_; rw [add_assoc (l + g)]
    exact (add_lt_add_iff_left _).2 ((add_lt_add_iff_left ω).2 one_lt_two)
  have hc : cL (l + g) < upsilon (l + g + (ω + 2)) :=
    (cL_le_ups hl).trans_lt (hm (lt_add_of_pos_right _ (omega0_pos.trans_le le_self_add)))
  refine (hE.add_lt hδ hc).trans_le (hm.monotone ?_)
  have hw : ω + 2 ≤ ω ^ 2 := by
    rw [Vo.vo_e2]
    have h1 : ω < ω ^ (2 : Ordinal.{0}) := by
      have := (opow_lt_opow_iff_right one_lt_omega0).2 (show (1 : Ordinal.{0}) < 2 from one_lt_two)
      rwa [opow_one] at this
    have h2 : (2 : Ordinal.{0}) < ω ^ (2 : Ordinal.{0}) := (natCast_lt_omega0 2).trans h1
    exact (isPrincipal_add_omega0_opow 2 h1 h2).le
  rw [add_assoc]
  exact (add_le_add_iff_left l).2 ((add_le_add_right hw g).trans hβ)

end Googology.Trans.PoR.InaccPsi.R2.Zl
