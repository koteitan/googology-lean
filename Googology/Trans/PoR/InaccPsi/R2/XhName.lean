import Googology.Trans.PoR.InaccPsi.R2.WjSplit
import Googology.Trans.PoR.InaccPsi.R2.WxTop
import Googology.Trans.PoR.InaccPsi.R2.RzLow
import Googology.Trans.PoR.InaccPsi.R2.RzSpec
import Googology.Trans.PoR.InaccPsi.R2.LsName

/-!
# Xh: the names of region (B) of the frontier, the offsets, the caps, and a lower bound of `ν_C`

Region (B) of the split `Wj.wjSplit` consists of (B-lo), (B-hi), the windows `W_k` and the top window `W_ω`.

* `xhExp_add` (**the last exponent of `a + ζ` is that of `ζ`** when `ω^E ∣ a`, `0 < ζ < ω^E`);
* `xhBlo_iff` (**(B-lo) on names**: a range restart is in (B-lo) iff its name `η` has `η < Ω₂` and
  `Γ(B)·ω ≤ η` for every `B < Γ(1)`);
* `xhBhi_iff` (**(B-hi) on names**: iff `Ω₂ ≤ η < Ω_ω` and `e(η) < Ω₂`), `xhBhi_off` (**every (B-hi) name is
  `Ω₂·q + ζ`, `1 ≤ q`, `0 < ζ < Ω₂`, with `e(η) = e(ζ)` and code `-1 + e(ζ)`**), `xhBhi_nonempty`;
* `xhWin_off` (**every name in `(b_ξ, b_{ξ+1})` is `b_ξ + ζ`, `0 < ζ < P′`, with `e(η) = e(ζ)` and code
  `-1 + e(ζ)`**; `ξ = k` the windows, `ξ = ω` the top window), `xhWin_cap` (**the cap `P(η + ω^{e(η)})` is at most
  `L(ξ+1)`**), `xhWin_capV` (CapV there gives `r(λ) < L(ξ+1)`);
* `xhNu_ge` (**if LOWER holds at every range restart below `U` and `υ_U ≤ L(0)`, then `υ_U ≤ ν_C`**),
  `xhNu_A2` (**`υ(ι(Γ(B)·ω)) ≤ ν_C` for every `B < φ(G, 1)`, unconditional**), `xhLower_ne_nu` (a piece where LOWER
  holds does not contain `ν_C`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Xh

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2

variable {S : InaccSeq.{0}}

/-! ## The last exponent of a sum -/

theorem xhExp_le {η : Ordinal.{0}} (hη : η ≠ 0) : Cd.cdExp η ≤ η :=
  (right_le_opow _ one_lt_omega0).trans (Ordinal.le_of_dvd hη (Cd.cdExp_dvd hη))

/-- **`e(a + ζ) = e(ζ)`** when `ω^E ∣ a` and `0 < ζ < ω^E`. -/
theorem xhExp_add {a ζ E : Ordinal.{0}} (hd : ω ^ E ∣ a) (h0 : ζ ≠ 0) (hζ : ζ < ω ^ E) :
    Cd.cdExp (a + ζ) = Cd.cdExp ζ := by
  have hζe : Cd.cdExp ζ < E := by
    by_contra h
    push Not at h
    have h1 : ω ^ E ∣ ζ := (opow_dvd_opow ω h).trans (Cd.cdExp_dvd h0)
    exact absurd (Ordinal.le_of_dvd h0 h1) (not_le.2 hζ)
  have hs0 : a + ζ ≠ 0 := fun h => h0 (Ordinal.add_eq_zero_iff.1 h).2
  have hda : ω ^ Cd.cdExp ζ ∣ a := (opow_dvd_opow ω hζe.le).trans hd
  apply le_antisymm
  · by_contra h
    push Not at h
    have h1 : ω ^ (Cd.cdExp ζ + 1) ∣ a + ζ :=
      (opow_dvd_opow ω (Order.add_one_le_of_lt h)).trans (Cd.cdExp_dvd hs0)
    have h2 : ω ^ (Cd.cdExp ζ + 1) ∣ a := (opow_dvd_opow ω (Order.add_one_le_of_lt hζe)).trans hd
    exact Cd.cdExp_not_dvd h0 ((Ordinal.dvd_add_iff h2).1 h1)
  · exact Cd.cdExp_max hs0 ((Ordinal.dvd_add_iff hda).2 (Cd.cdExp_dvd h0))

/-! ## (B-lo) and (B-hi) on names -/

theorem xhOm2_lim {η : Ordinal.{0}} (hη : η < Om (1 + 1)) : η + 1 < Om (1 + 1) := by
  have hE := Wj.wjOm2_inE
  have hw : ω < Om (1 + 1 : Ordinal.{0}) := omega0_lt_inE hE
  exact (inE_indec hE).add_lt hη (one_lt_omega0.trans hw)

/-- **(B-lo) on names.** -/
theorem xhBlo_iff {l : Ordinal.{0}} (hr : Cd.CdRange S l) :
    (Wj.WjNotA S l ∧ upsilon l < Nc.ncL S 0 ∧ Cd.cdExp (Cd.cdEta S l) < Om (1 + 1) ∧
      l < Bt.iota S (Om (1 + 1))) ↔
    (Cd.cdEta S l < Om (1 + 1) ∧ ∀ B, B < Gc.gcG 1 → Gc.gcG B * ω ≤ Cd.cdEta S l) := by
  obtain ⟨hl, -, hlt, -⟩ := hr
  obtain ⟨hg, hι, hpv⟩ := Wj.wjEta_spec (S := S) hl.1 hlt
  constructor
  · rintro ⟨hN, -, -, hlι⟩
    refine ⟨?_, fun B hB => ?_⟩
    · by_contra h
      push Not at h
      have := Bt.iota_mono (S := S) _ _ h
      rw [hι] at this
      exact absurd hlι (not_lt.2 this)
    · by_contra h
      push Not at h
      have := Cd.cd_iota_lt_of_good hg h
      rw [hι] at this
      exact absurd (hN B hB) (not_le.2 this)
  · rintro ⟨hη, hB⟩
    have hη0 : Cd.cdEta S l ≠ 0 := by
      intro h
      have h1 := hB 0 (Gc.gcG_SC 1).1
      rw [h] at h1
      exact absurd h1 (not_le.2 (mul_pos (Gc.gcG_SC 0).1 omega0_pos))
    refine ⟨fun B hB' => ?_, ?_, (xhExp_le hη0).trans_lt hη, ?_⟩
    · rw [← hι]; exact Bt.iota_mono (S := S) _ _ (hB B hB')
    · rw [← hpv]; exact (Nm.Pv_mono (S := S) hη.le).trans_lt (Ga.ga_Pv_lt_L0 S le_rfl)
    · rw [← hι]; exact Cd.cd_iota_lt_of_good hg hη

/-- **(B-hi) on names.** -/
theorem xhBhi_iff {l : Ordinal.{0}} (hr : Cd.CdRange S l) :
    (Wj.WjNotA S l ∧ upsilon l < Nc.ncL S 0 ∧ Cd.cdExp (Cd.cdEta S l) < Om (1 + 1) ∧
      Bt.iota S (Om (1 + 1)) ≤ l) ↔
    (Om (1 + 1) ≤ Cd.cdEta S l ∧ Cd.cdEta S l < Om ω ∧ Cd.cdExp (Cd.cdEta S l) < Om (1 + 1)) := by
  obtain ⟨hl, -, hlt, -⟩ := hr
  obtain ⟨hg, hι, -⟩ := Wj.wjEta_spec (S := S) hl.1 hlt
  have hb0 : Wj.wjBase S 0 = Om ω := by simp [Wj.wjBase]
  constructor
  · rintro ⟨-, h0, he, hlι⟩
    refine ⟨?_, hb0 ▸ (Wj.wjLt_L_iff hl.1 hlt 0).1 h0, he⟩
    by_contra h
    push Not at h
    have := Cd.cd_iota_lt_of_good hg h
    rw [hι] at this
    exact absurd hlι (not_le.2 this)
  · rintro ⟨h2, hw, he⟩
    have hlι : Bt.iota S (Om (1 + 1)) ≤ l := by rw [← hι]; exact Bt.iota_mono (S := S) _ _ h2
    exact ⟨fun B hB => (Wj.wjFrA_le_Om2 hB).trans hlι,
      (Wj.wjLt_L_iff hl.1 hlt 0).2 (hb0 ▸ hw), he, hlι⟩

/-- **Every (B-hi) name is `Ω₂·q + ζ`** with `1 ≤ q`, `0 < ζ < Ω₂`, `e(η) = e(ζ)`, code `-1 + e(ζ)`. -/
theorem xhBhi_off {l : Ordinal.{0}} (h2 : Om (1 + 1) ≤ Cd.cdEta S l)
    (he : Cd.cdExp (Cd.cdEta S l) < Om (1 + 1)) :
    ∃ q ζ, Cd.cdEta S l = Om (1 + 1) * q + ζ ∧ 1 ≤ q ∧ ζ ≠ 0 ∧ ζ < Om (1 + 1) ∧
      Cd.cdExp (Cd.cdEta S l) = Cd.cdExp ζ ∧ Cd.cdCode S l = Cd.cdOff (Cd.cdExp ζ) := by
  set η := Cd.cdEta S l with hηdef
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := (Om_pos (by simp)).ne'
  have hη0 : η ≠ 0 := fun h => by rw [h] at h2; exact hW0 (nonpos_iff_eq_zero.1 h2)
  refine ⟨η / Om (1 + 1), η % Om (1 + 1), (Ordinal.div_add_mod η _).symm, ?_, ?_,
    Ordinal.mod_lt η hW0, ?_, ?_⟩
  · rw [Order.one_le_iff_ne_zero]
    intro hq
    have e := Ordinal.div_add_mod η (Om (1 + 1))
    rw [hq, mul_zero, zero_add] at e
    have := Ordinal.mod_lt η hW0
    rw [e] at this
    exact absurd h2 (not_le.2 this)
  · intro hz
    have hd : Om (1 + 1 : Ordinal.{0}) ∣ η := Ordinal.dvd_iff_mod_eq_zero.2 hz
    rw [← Wj.wjOm2_inE] at hd
    exact absurd (Cd.cdExp_max hη0 hd) (not_le.2 he)
  · have e := Ordinal.div_add_mod η (Om (1 + 1))
    have hz : η % Om (1 + 1) ≠ 0 := by
      intro hz
      have hd : Om (1 + 1 : Ordinal.{0}) ∣ η := Ordinal.dvd_iff_mod_eq_zero.2 hz
      rw [← Wj.wjOm2_inE] at hd
      exact absurd (Cd.cdExp_max hη0 hd) (not_le.2 he)
    have hd : ω ^ Om (1 + 1 : Ordinal.{0}) ∣ Om (1 + 1) * (η / Om (1 + 1)) := by
      rw [Wj.wjOm2_inE]; exact dvd_mul_right _ _
    have hlt : η % Om (1 + 1) < ω ^ Om (1 + 1 : Ordinal.{0}) := by
      rw [Wj.wjOm2_inE]; exact Ordinal.mod_lt η hW0
    conv_lhs => rw [← e]
    exact xhExp_add hd hz hlt
  · show Cd.cdCodeOf S η = _
    rw [Cd.cdCodeOf_of_lt he]
    congr 1
    have e := Ordinal.div_add_mod η (Om (1 + 1))
    have hz : η % Om (1 + 1) ≠ 0 := by
      intro hz
      have hd : Om (1 + 1 : Ordinal.{0}) ∣ η := Ordinal.dvd_iff_mod_eq_zero.2 hz
      rw [← Wj.wjOm2_inE] at hd
      exact absurd (Cd.cdExp_max hη0 hd) (not_le.2 he)
    have hd : ω ^ Om (1 + 1 : Ordinal.{0}) ∣ Om (1 + 1) * (η / Om (1 + 1)) := by
      rw [Wj.wjOm2_inE]; exact dvd_mul_right _ _
    have hlt : η % Om (1 + 1) < ω ^ Om (1 + 1 : Ordinal.{0}) := by
      rw [Wj.wjOm2_inE]; exact Ordinal.mod_lt η hW0
    conv_lhs => rw [← e]
    exact xhExp_add hd hz hlt

/-! ## The windows: base + offset, and the cap -/

theorem xhPp_opow : ω ^ Nc.ncPp S = Nc.ncPp S := Low.opow_eq_self_of_SC (Nc.ncPp_SC S)

theorem xhPp_dvd_base (ξ : Ordinal.{0}) : ω ^ Nc.ncPp S ∣ Wj.wjBase S ξ := by
  have hWE : ω ^ Om ω = Om ω := Low.opow_eq_self_of_SC (SC_Om omega0_ne_zero)
  have h12 : (1 + 1 : Ordinal.{0}) ≤ ω := by
    rw [one_add_one_eq_two]; exact (natCast_lt_omega0 2).le
  have hPW : Nc.ncPp S ≤ Om ω := Wj.wjPp_lt_Om2.le.trans (Om_le_Om.2 h12)
  have h1 : ω ^ Nc.ncPp S ∣ Om ω := by
    have := opow_dvd_opow ω hPW
    rwa [hWE] at this
  have h2 : ω ^ Nc.ncPp S ∣ Nc.ncPp S * ξ := by rw [xhPp_opow]; exact dvd_mul_right _ _
  exact (Ordinal.dvd_add_iff h1).2 h2

theorem xhBase_succ (ξ : Ordinal.{0}) : Wj.wjBase S (ξ + 1) = Wj.wjBase S ξ + Nc.ncPp S := by
  simp only [Wj.wjBase, mul_add_one, add_assoc]

/-- **A name between two window bases**: `η = b_ξ + ζ`, `0 < ζ < P′`, `e(η) = e(ζ)`, code `-1 + e(ζ)`. -/
theorem xhWin_off {ξ l : Ordinal.{0}} (hr : Cd.CdRange S l) (h1 : Nc.ncL S ξ < upsilon l)
    (h2 : upsilon l < Nc.ncL S (ξ + 1)) :
    ∃ ζ, Cd.cdEta S l = Wj.wjBase S ξ + ζ ∧ ζ ≠ 0 ∧ ζ < Nc.ncPp S ∧
      Cd.cdExp (Cd.cdEta S l) = Cd.cdExp ζ ∧ Cd.cdCode S l = Cd.cdOff (Cd.cdExp ζ) := by
  obtain ⟨hl, -, hlt, -⟩ := hr
  obtain ⟨-, -, hpv⟩ := Wj.wjEta_spec (S := S) hl.1 hlt
  have hge : Wj.wjBase S ξ ≤ Cd.cdEta S l := (Wj.wjLe_L_iff hl.1 hlt ξ).1 h1.le
  have hlt' : Cd.cdEta S l < Wj.wjBase S ξ + Nc.ncPp S := by
    rw [← xhBase_succ]; exact (Wj.wjLt_L_iff hl.1 hlt _).1 h2
  set ζ := Cd.cdEta S l - Wj.wjBase S ξ with hζ
  have e : Wj.wjBase S ξ + ζ = Cd.cdEta S l := Ordinal.add_sub_cancel_of_le hge
  have hζ0 : ζ ≠ 0 := by
    intro h
    rw [h, add_zero] at e
    rw [← e, ← Wj.wjL_eq] at hpv
    exact absurd hpv (ne_of_lt h1)
  have hζP : ζ < Nc.ncPp S := by
    have : Wj.wjBase S ξ + ζ < Wj.wjBase S ξ + Nc.ncPp S := by rw [e]; exact hlt'
    exact (add_lt_add_iff_left _).1 this
  have hexp : Cd.cdExp (Cd.cdEta S l) = Cd.cdExp ζ := by
    rw [← e]; exact xhExp_add (xhPp_dvd_base ξ) hζ0 (by rw [xhPp_opow]; exact hζP)
  have hc : Cd.cdCode S l = Cd.cdOff (Cd.cdExp ζ) := by
    show Cd.cdCodeOf S (Cd.cdEta S l) = _
    have hlt2 : Cd.cdExp (Cd.cdEta S l) < Om (1 + 1) :=
      hexp ▸ (xhExp_le hζ0).trans_lt (hζP.trans Wj.wjPp_lt_Om2)
    rw [Cd.cdCodeOf_of_lt hlt2, hexp]
  exact ⟨ζ, e.symm, hζ0, hζP, hexp, hc⟩

/-- **The cap of a window restart is at most `L(ξ+1)`.** -/
theorem xhWin_cap {ξ l : Ordinal.{0}} (hr : Cd.CdRange S l) (h1 : Nc.ncL S ξ < upsilon l)
    (h2 : upsilon l < Nc.ncL S (ξ + 1)) : Cd.cdCapB S l ≤ Nc.ncL S (ξ + 1) := by
  obtain ⟨hl, -, hlt, -⟩ := hr
  obtain ⟨-, -, hpv⟩ := Wj.wjEta_spec (S := S) hl.1 hlt
  have hge : Wj.wjBase S ξ ≤ Cd.cdEta S l := (Wj.wjLe_L_iff hl.1 hlt ξ).1 h1.le
  have hne : Wj.wjBase S ξ ≠ Cd.cdEta S l := by
    intro e; rw [← e, ← Wj.wjL_eq] at hpv; exact absurd hpv (ne_of_lt h1)
  have hlt' : Cd.cdEta S l < Wj.wjBase S ξ + ω ^ Nc.ncPp S := by
    rw [xhPp_opow, ← xhBase_succ]; exact (Wj.wjLt_L_iff hl.1 hlt _).1 h2
  have hw := (Cd.cdWin (xhPp_dvd_base ξ) (lt_of_le_of_ne hge hne) hlt').2
  rw [xhPp_opow, ← xhBase_succ] at hw
  unfold Cd.cdCapB
  rw [Wj.wjL_eq]
  exact Nm.Pv_mono hw.le

/-- **CapV at a window restart gives `r(λ) < L(ξ+1)`.** -/
theorem xhWin_capV {ξ l : Ordinal.{0}} (hr : Cd.CdRange S l) (h1 : Nc.ncL S ξ < upsilon l)
    (h2 : upsilon l < Nc.ncL S (ξ + 1)) (hV : Cd.CdCapV S l) : Cd.cdR S l < Nc.ncL S (ξ + 1) :=
  hV.trans_le (xhWin_cap hr h1 h2)

/-! ## `ν_C` and LOWER -/

/-- A restart where LOWER holds is not `ν_C`. -/
theorem xhLower_ne_nu (P : Ordinal.{0} → Prop) (h : ∀ l, Cd.CdRange S l → P l → Cd.CdLower S l) :
    ∀ l, Cd.CdRange S l → P l → upsilon l ≠ nuC :=
  fun l hr hp e => Sh.shNotLower (S := S) e (h l hr hp)

/-- `υ_{B₀} < ν_C`. -/
theorem xhB0_lt_nu : upsilon Cd.cdB0 < nuC := Rz.rz_lt_nuC Rz.rzB0_lt

/-- **The lower bound of `ν_C` from LOWER below `U`.** -/
theorem xhNu_ge {U : Ordinal.{0}} (hU : upsilon U ≤ Nc.ncL S 0)
    (hL : ∀ l, Cd.CdRange S l → l < U → Cd.CdLower S l) : upsilon U ≤ nuC := by
  by_contra h
  push Not at h
  obtain ⟨ξ, hξ, e⟩ := nuC_restart
  have hξU : ξ < U := upsilon_normal.strictMono.lt_iff_lt.1 (e ▸ h)
  rcases lt_or_ge ξ Cd.cdB0 with hB | hB
  · have := upsilon_normal.strictMono hB
    rw [← e] at this
    exact absurd xhB0_lt_nu (not_lt.2 this.le)
  · have hξ0 : upsilon ξ < Nc.ncL S 0 := (e ▸ h).trans_le hU
    have hr : Cd.CdRange S ξ := by
      refine Wj.wjRange_iff.2 ⟨hξ, hB, hξ0.trans_le (Pp.ppL_mono zero_le), fun k hk => ?_, fun hk => ?_⟩
      · exact absurd (hk ▸ hξ0) (not_lt.2 (Pp.ppL_mono zero_le))
      · exact absurd (hk ▸ hξ0) (not_lt.2 (Pp.ppL_mono zero_le))
    exact Sh.shNotLower (S := S) e.symm (hL ξ hr hξU)

/-- **`υ(ι(Γ(B)·ω)) ≤ ν_C` for every `B < φ(G, 1)`** (from the closed region (A2)). -/
theorem xhNu_A2 (S : InaccSeq.{0}) {B : Ordinal.{0}} (hB : B < veblen (Gc.gcG 0) 1) :
    upsilon (Bt.iota S (Gc.gcG B * ω)) ≤ nuC := by
  have hB1 : B < Gc.gcG 1 :=
    hB.trans (Wj.wjVeb_lt_G1 Wj.wjG_lt_G1 (lt_of_le_of_lt le_add_self Wj.wjG1_lt))
  refine xhNu_ge (S := S) ?_ fun l hr hl => (Wx.wxA2_enum S hr ⟨B, hB, hl⟩).2
  rw [← Fx.fx_Pv_eq]
  exact (Ga.ga_Pv_lt_L0 S (R2Skel.SkFX.skfxG_lt_Om2 hB1).le).le

/-! ## Non-vacuity of (B-hi) -/

/-- **(B-hi) contains range restarts** (the code-`G′+1` restarts of `Ls.lsNames_M` above `P(Ω₂)`). -/
theorem xhBhi_nonempty (S : InaccSeq.{0}) : ∃ l, Cd.CdRange S l ∧ Wj.WjNotA S l ∧
    upsilon l < Nc.ncL S 0 ∧ Cd.cdExp (Cd.cdEta S l) < Om (1 + 1) ∧ Bt.iota S (Om (1 + 1)) ≤ l := by
  obtain ⟨μ, hr, hγ, hμ, hc⟩ := Ls.lsNames_M (S := S) 0 (Nm.Pv S (Om (1 + 1))) (Ga.ga_Pv_lt_L0 S le_rfl)
  have hι : Bt.iota S (Om (1 + 1)) ≤ μ := by
    rw [Fx.fx_Pv_eq] at hγ
    exact (upsilon_normal.strictMono.lt_iff_lt.1 hγ).le
  have he : Cd.cdExp (Cd.cdEta S μ) < Om (1 + 1) := by
    by_contra h
    push Not at h
    have hpi := (Wj.wjC_props hr h).2.2.2
    rw [hc] at hpi
    have hSC : SC (Cd.cdPi S (Cd.cdEta S μ)) := SC_psi (InR_Om_succ 1) _
    have hlt : Ls.lsG S (0 + 1) < Cd.cdPi S (Cd.cdEta S μ) := by
      rw [← hpi]; exact Order.lt_add_one_iff.2 le_rfl
    exact absurd (hSC.add_one_lt hlt) (by rw [hpi]; exact lt_irrefl _)
  exact ⟨μ, hr, fun B hB => (Wj.wjFrA_le_Om2 hB).trans hι, hμ, he, hι⟩

end Googology.Trans.PoR.InaccPsi.R2.Xh
