import Googology.Trans.PoR.InaccPsi.R2.CdDef
import Googology.Trans.PoR.InaccPsi.R2.PpIdx
import Googology.Trans.PoR.InaccPsi.R2.CpRel

/-!
# The names and the codes of the restarts that are not fixed points of `υ`

`P(η) = ψ_{Ω₁}(Ω_ω + θ·η)` (`Nm.Pv`), `ι` the index of Theorem GEN (`υ_{ι(η)} = P(η)`), `η_λ = cdEta S λ` the
name of a restart index (the good `η` with `ι(η) = λ`), `m_λ = cdCode S λ` its code (`-1 + e(η_λ)` for a
last exponent `e(η_λ) < Ω₂`).

* `cpGood_add`, `cpIota_add`: if `η` is good and `z < P(η)`, then `η + z` is good and `ι(η + z) = ι(η) + z`
  (every `y ≤ z` lies in the hull, `Nm.good_add`, `Pp.ppIota_add`);
* `cpEta_add` (**the name above a restart**): for a restart index `λ₀` with a name (`ρ_{λ₀} < P(η₁)` for some
  `η₁`) and `z < ρ_{λ₀}`: `η_{λ₀+z} = η_{λ₀} + z`;
* `cpCode_add` (**the code above a restart**): then, for `z ≠ 0`, `m_{λ₀+z} = -1 + e(z)` (`cpExp_add`);
* `cpDecomp`: **every restart index `λ` with `ω² < λ < υ_λ` is `λ₀ + z`** with `λ₀` a restart index,
  `0 < z < ρ_{λ₀}` and `ω² ∣ z` (if `λ/ω²` is a successor, `z = ω²`; if it is a limit, `υ` is continuous at
  `λ`, so `λ < υ_x` for some `x < λ`);
* `cpCode_exp` (**the code of a restart that is not a fixed point of `υ`**): for a restart index `λ` with
  `ω² < λ < υ_λ` and a name, `m_λ = -1 + e(λ)`, and `η_λ = η_{λ₀} + z` for the decomposition of `cpDecomp`.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Cp

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- `η + z` is good when `η` is good and `z < P(η)`. -/
theorem cpGood_add {η z : Ordinal.{0}} (hg : Bt.Good S η) (hz : z < Pv S η) : Bt.Good S (η + z) :=
  good_add hg (CSet.of_lt (hz.trans_le (Pv_mono le_self_add)))

/-- `ι(η + z) = ι(η) + z` when `η` is good and `z < P(η)`. -/
theorem cpIota_add {η z : Ordinal.{0}} (hg : Bt.Good S η) (hz : z < Pv S η) :
    iota S (η + z) = iota S η + z :=
  Pp.ppIota_add η z (fun _ hy => cpGood_add hg (hy.trans hz))

/-- **The name above a restart**: `η_{λ₀+z} = η_{λ₀} + z` for `z < ρ_{λ₀}`. -/
theorem cpEta_add {l0 η1 z : Ordinal.{0}} (hl0 : l0 ≠ 0) (hn : upsilon l0 < Pv S η1)
    (hz : z < upsilon l0) :
    cdEta S (l0 + z) = cdEta S l0 + z ∧ Bt.Good S (cdEta S l0 + z) ∧
      Pv S (cdEta S l0) = upsilon l0 := by
  obtain ⟨hg, hι, -, hpv⟩ := cdEta_pv_spec (S := S) hl0 hn
  have hz' : z < Pv S (cdEta S l0) := hpv ▸ hz
  have hg' := cpGood_add hg hz'
  refine ⟨cdEta_unique hg' ?_, hg', hpv⟩
  rw [cpIota_add hg hz', hι]

theorem cpExp_le {η : Ordinal.{0}} (hη : η ≠ 0) : cdExp η ≤ η :=
  csSup_le (cdExp_nonempty η) fun _ he => (right_le_opow _ one_lt_omega0).trans (le_of_dvd hη he)

/-- **The code above a restart**: `m_{λ₀+z} = -1 + e(z)` for `0 < z < ρ_{λ₀}`. -/
theorem cpCode_add {l0 η1 z : Ordinal.{0}} (hl0 : l0 ≠ 0) (hn : upsilon l0 < Pv S η1)
    (hz : z < upsilon l0) (hz0 : z ≠ 0) : cdCode S (l0 + z) = cdOff (cdExp z) := by
  unfold cdCode
  rw [(cpEta_add hl0 hn hz).1]
  have he : cdExp (cdEta S l0 + z) = cdExp z := cpExp_add _ hz0
  have hz2 : cdExp z < Om (1 + 1) := by
    have h1 : z < Om 1 := hz.trans (hn.trans (Pv_lt_Om1 S η1))
    have h12 : (1 : Ordinal.{0}) < 1 + 1 := lt_add_one 1
    exact ((cpExp_le hz0).trans_lt h1).trans (Om_lt_Om.2 h12)
  rw [cdCodeOf_of_lt (by rw [he]; exact hz2), he]

/-- **Every restart index `λ` with `ω² < λ < υ_λ` is `λ₀ + z`** with `λ₀` a restart index, `0 < z < ρ_{λ₀}`,
`ω² ∣ z`. -/
theorem cpDecomp {l : Ordinal.{0}} (hl : IsRestartIdx l) (hww : ω * ω < l) (hfix : l < upsilon l) :
    ∃ l0 z, IsRestartIdx l0 ∧ 0 < z ∧ z < upsilon l0 ∧ ω * ω ∣ z ∧ l = l0 + z := by
  have hpos : (0 : Ordinal.{0}) < ω * ω := mul_pos omega0_pos omega0_pos
  obtain ⟨q, hq⟩ := (ri_iff.1 hl).2
  rcases zero_or_succ_or_isSuccLimit q with h0 | ⟨q', hq'⟩ | hlim
  · rw [h0, mul_zero] at hq; exact absurd hq hl.1
  · rw [← hq', succ_eq_add_one, mul_add_one] at hq
    have hq'0 : q' ≠ 0 := by
      rintro rfl
      rw [mul_zero, zero_add] at hq
      exact absurd hq (ne_of_gt hww)
    have hl0 : IsRestartIdx (ω * ω * q') :=
      ri_iff.2 ⟨(mul_pos hpos (pos_iff_ne_zero.2 hq'0)).ne', dvd_mul_right _ _⟩
    refine ⟨ω * ω * q', ω * ω, hl0, hpos, ?_, dvd_refl _, hq⟩
    have hE : InE (upsilon (ω * ω * q')) := ups_inE hl0
    have hρ1 : 1 ≤ upsilon (ω * ω * q') := Order.one_le_iff_pos.2 (upsPt_upsilon (pos_iff_ne_zero.2 hl0.1)).1
    have hω : ω ≤ upsilon (ω * ω * q') := by
      calc ω = ω ^ (1 : Ordinal.{0}) := (opow_one ω).symm
        _ ≤ ω ^ upsilon (ω * ω * q') := opow_le_opow_right omega0_pos hρ1
        _ = upsilon (ω * ω * q') := hE
    have h2 : (2 : Ordinal.{0}) < upsilon (ω * ω * q') :=
      lt_of_lt_of_le (by exact_mod_cast natCast_lt_omega0 2) hω
    calc ω * ω = ω ^ (2 : Ordinal.{0}) := cp_ww_eq.symm
      _ < ω ^ upsilon (ω * ω * q') := (opow_lt_opow_iff_right one_lt_omega0).2 h2
      _ = upsilon (ω * ω * q') := hE
  · have hlim' : IsSuccLimit l := hq ▸ isSuccLimit_mul_right hpos hlim
    obtain ⟨_, ⟨x, hx, rfl⟩, hxl⟩ := (lt_isLUB_iff (upsilon_limit hlim')).1 hfix
    have hx' : x < ω * ω * q := hq ▸ hx
    obtain ⟨c, hc, hxc⟩ := (lt_mul_iff_of_isSuccLimit hlim).1 hx'
    have hc0 : c ≠ 0 := by
      rintro rfl; rw [mul_zero] at hxc; exact absurd hxc (not_lt.2 zero_le)
    have hl0 : IsRestartIdx (ω * ω * c) :=
      ri_iff.2 ⟨(mul_pos hpos (pos_iff_ne_zero.2 hc0)).ne', dvd_mul_right _ _⟩
    have hcl : ω * ω * c < l := hq ▸ (mul_lt_mul_iff_right₀ hpos).2 hc
    obtain ⟨z, hz⟩ := exists_add_of_le hcl.le
    have hz0 : 0 < z := by
      rcases eq_or_ne z 0 with rfl | h
      · rw [add_zero] at hz; exact absurd hz (ne_of_gt hcl)
      · exact pos_iff_ne_zero.2 h
    refine ⟨ω * ω * c, z, hl0, hz0, ?_, (dvd_add_iff (dvd_mul_right (ω * ω) c)).1 (hz ▸ (ri_iff.1 hl).2), hz⟩
    calc z ≤ ω * ω * c + z := le_add_self
      _ = l := hz.symm
      _ < upsilon x := hxl
      _ ≤ upsilon (ω * ω * c) := upsilon_normal.strictMono.monotone hxc.le

/-- **The code of a restart that is not a fixed point of `υ`**: `m_λ = -1 + e(λ)` for a restart index `λ` with
`ω² < λ < υ_λ` and `ρ_λ < P(η₁)` for some `η₁`. -/
theorem cpCode_exp {l η1 : Ordinal.{0}} (hl : IsRestartIdx l) (hww : ω * ω < l) (hfix : l < upsilon l)
    (hn : upsilon l < Pv S η1) : cdCode S l = cdOff (cdExp l) := by
  obtain ⟨l0, z, hl0, hz0, hzρ, -, rfl⟩ := cpDecomp hl hww hfix
  have hn0 : upsilon l0 < Pv S η1 :=
    (upsilon_normal.strictMono (lt_add_of_pos_right l0 hz0)).trans hn
  rw [cpCode_add hl0.1 hn0 hzρ hz0.ne', cpExp_add _ hz0.ne']

end Googology.Trans.PoR.InaccPsi.R2.Cp
