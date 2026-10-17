import Googology.Trans.PoR.InaccPsi.R2.CdLow
import Googology.Trans.PoR.InaccPsi.R2.LhGen
import Googology.Trans.PoR.InaccPsi.R2.CpFront
import Googology.Trans.PoR.InaccPsi.R2.CpName

/-!
# UPPER and LOWER of ENUM-REACH below `cpB1`

`r(λ) = k_λ(Θ_λ(m_λ))` (`cdR`), `δ_λ = υ_{λ+ω+1}`, UPPER = `CdUpper` (not `ρ_λ ≤₁ r(λ) + 1`), LOWER = `CdLower`
(`ρ_λ ≤₁ r(λ)`), `cpB1` the first limit of frontiers (`R2.CpFront`, `B₀ < cpB1`).

* `cpClosed`, `cpk_eq` (**`k_λ(x) = δ_λ + x` for `x < δ_λ`**, `λ < cpB1`): every `a ∈ (ρ_λ, δ_λ]` has its
  `≤₁`-successors at most `δ_λ` (`RstK.capδ`), and every `a ∈ (δ_λ, δ_λ + x]` is decomposable, not a `υ`-point,
  so its `≤₁` is that of `R₁⁺` (BLK^O, `cpBlk`) and `lh(a) = a` (`lhDecomp`);
* `cpUpper_iff`, `cpLower_iff`, `cpExact_iff` (**ENUM-REACH below `cpB1` as an equation of offsets**): for a
  restart index `λ < cpB1`, UPPER at `λ` iff `VzOrec(λ) ≤ Θ_λ(m_λ)`, LOWER iff `Θ_λ(m_λ) ≤ VzOrec(λ)`, both iff
  `Θ_λ(m_λ) = VzOrec(λ)`;
* `cpEnum_nonfix` (**ENUM-REACH, both halves, at every restart below `cpB1` that is not a fixed point of
  `υ`**): for a restart index `λ` with `ω² < λ < υ_λ`, `λ < cpB1` and a name (`ρ_λ < P(η₁)`):
  `VzOrec(λ) = m_λ = Θ_λ(m_λ) = -1 + e(λ)`, `r(λ) = δ_λ + (-1 + e(λ)) = lh(ρ_λ)`, UPPER and LOWER at `λ`;
* `cpRange_nonfix`: such a `λ` with `B₀ ≤ λ` and `ρ_λ < L(ω+1)` is in the range of ENUM-REACH;
  `cpUPPER_init` (**the initial part**): UPPER and LOWER at every `λ` of the range with `λ < cpB1` and
  `λ < υ_λ`;
* `cpCapV_nonfix` (**the cap of the value**): there `r(λ) < υ_{λ+ω+2} ≤ P(η_λ + ω^{e(η_λ)})`;
  `cpCapAt_nonfix`: hence `ρ_λ` is not self-crossing (`CdCapAt`).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Cp

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

theorem cpB1_lt_add {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlB : l < cpB1) :
    l + ω + 1 + 1 < cpB1 := by
  have h1 : l + ω * ω ≤ cpB1 := next_mult (ri_iff.1 hl).2 cpB1_mult hlB
  refine lt_of_lt_of_le ?_ h1
  rw [add_assoc, add_assoc]
  refine (add_lt_add_iff_left l).2 ?_
  have h2 : (1 + 1 : Ordinal.{0}) < ω := by
    rw [one_add_one_eq_two]; exact_mod_cast natCast_lt_omega0 2
  have h3 : ω + (1 + 1) < ω + ω := (add_lt_add_iff_left ω).2 h2
  calc ω + (1 + 1) < ω + ω := h3
    _ = ω * 2 := (Ordinal.mul_two ω).symm
    _ < ω * ω := mul_lt_mul_of_pos_left (by exact_mod_cast natCast_lt_omega0 2) omega0_pos

/-- `δ_λ + x < υ_{λ+ω+2}` for `x < δ_λ`. -/
theorem cp_delta_add_lt {l x : Ordinal.{0}} (hx : x < cdDelta l) :
    cdDelta l + x < upsilon (l + ω + 1 + 1) := by
  have hU : UpsPt (upsilon (l + ω + 1 + 1)) :=
    upsPt_upsilon (lt_of_le_of_lt zero_le (lt_add_one _))
  have hp := (indec_iff.1 (indec_of_upsPt hU)).2
  have hδ : cdDelta l < upsilon (l + ω + 1 + 1) := upsilon_normal.strictMono (lt_add_one _)
  exact hp hδ (hx.trans hδ)

/-- **`δ_λ + x` is closed relative to `λ`** for `x < δ_λ`, `λ < cpB1`. -/
theorem cpClosed {l x : Ordinal.{0}} (hl : IsRestartIdx l) (hlB : l < cpB1) (hx : x < cdDelta l) :
    cdClosed l (cdDelta l + x) := by
  have R := (cpRst hl hlB).1
  refine ⟨le_self_add, fun a hρa hax g hg => ?_⟩
  rcases le_or_gt a (cdDelta l) with haδ | hδa
  · exact (not_lt.1 fun h => R.capδ a hρa haδ g h hg).trans le_self_add
  · have hnI : ¬ Indec a := decomp_mid hx hδa hax
    have hnU : ¬ UpsPt a := fun h => hnI (indec_of_upsPt h)
    have hacp : a < upsilon cpB1 :=
      (hax.trans_lt (cp_delta_add_lt hx)).trans (upsilon_normal.strictMono (cpB1_lt_add hl hlB))
    have hR := (cpBlk.2.2 a hacp hnU g).1 hg
    exact ((Lh.lhDecomp hnI).2 g hR).trans hax

/-- **`k_λ(x) = δ_λ + x` for `x < δ_λ`**, `λ < cpB1`. -/
theorem cpk_eq {l x : Ordinal.{0}} (hl : IsRestartIdx l) (hlB : l < cpB1) (hx : x < cdDelta l) :
    cdk l x = cdDelta l + x :=
  cdk_interval (fun _ hy => Or.inl (cpClosed hl hlB (hy.trans_lt hx))) x le_rfl

theorem cpVz_lt_delta {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlB : l < cpB1) :
    VzOrec l < cdDelta l := vzOrec_lt_δ hl (hlB.trans cpB1_lt_Om1)

/-- **UPPER below `cpB1`**: UPPER at `λ` iff `VzOrec(λ) ≤ Θ_λ(m_λ)`. -/
theorem cpUpper_iff {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlB : l < cpB1) :
    CdUpper S l ↔ VzOrec l ≤ cdTheta S l (cdCode S l) := by
  rw [cdUpper_iff_ge (cpReach hl hlB)]
  have e : upsilon (l + ω + 1) + VzOrec l = cdk l (VzOrec l) := (cpk_eq hl hlB (cpVz_lt_delta hl hlB)).symm
  rw [e]
  exact (cdk_strictMono l).le_iff_le

/-- **LOWER below `cpB1`**: LOWER at `λ` iff `Θ_λ(m_λ) ≤ VzOrec(λ)`. -/
theorem cpLower_iff {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlB : l < cpB1) :
    CdLower S l ↔ cdTheta S l (cdCode S l) ≤ VzOrec l := by
  rw [cdLower_iff_le (cpReach hl hlB)]
  have e : upsilon (l + ω + 1) + VzOrec l = cdk l (VzOrec l) := (cpk_eq hl hlB (cpVz_lt_delta hl hlB)).symm
  rw [e]
  exact (cdk_strictMono l).le_iff_le

/-- **ENUM-REACH below `cpB1`**: both halves at `λ` iff `Θ_λ(m_λ) = VzOrec(λ)`. -/
theorem cpExact_iff {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlB : l < cpB1) :
    (CdUpper S l ∧ CdLower S l) ↔ cdTheta S l (cdCode S l) = VzOrec l := by
  rw [cpUpper_iff hl hlB, cpLower_iff hl hlB]
  exact ⟨fun h => le_antisymm h.2 h.1, fun h => ⟨h.ge, h.le⟩⟩

/-- **ENUM-REACH, both halves, at every restart below `cpB1` that is not a fixed point of `υ`.** -/
theorem cpEnum_nonfix {l η1 : Ordinal.{0}} (hl : IsRestartIdx l) (hww : ω * ω < l)
    (hfix : l < upsilon l) (hlB : l < cpB1) (hn : upsilon l < Pv S η1) :
    VzOrec l = cdOff (cdExp l) ∧ cdCode S l = cdOff (cdExp l) ∧
      cdTheta S l (cdCode S l) = cdOff (cdExp l) ∧
      cdR S l = cdDelta l + cdOff (cdExp l) ∧ IsReach R2C (upsilon l) (cdR S l) ∧
      CdUpper S l ∧ CdLower S l := by
  obtain ⟨l0, z, hl0, hz0, hzρ, hzd, hlz⟩ := cpDecomp hl hww hfix
  have hl01 : l0 < Om1 :=
    (lt_of_lt_of_le (lt_add_of_pos_right l0 hz0) hlz.ge).trans (hlB.trans cpB1_lt_Om1)
  have hO : VzOrec l = cdOff (cdExp l) := by
    rw [hlz, cpVz_rel hl0 hl01 z hz0 hzρ hzd, cpExp_add _ hz0.ne']
  have hm : cdCode S l = cdOff (cdExp l) := cpCode_exp hl hww hfix hn
  have hml : cdOff (cdExp l) ≤ l := (cdOff_le _).trans (cpExp_le hl.1)
  have hθ : cdTheta S l (cdCode S l) = cdOff (cdExp l) := by
    rw [hm]; exact cdTheta_small S (hml.trans upsilon_normal.strictMono.le_apply)
  have hmδ : cdOff (cdExp l) < cdDelta l :=
    (hml.trans upsilon_normal.strictMono.le_apply).trans_lt (cdRho_lt_delta l)
  have hR : cdR S l = cdDelta l + cdOff (cdExp l) := by
    show cdk l (cdTheta S l (cdCode S l)) = _
    rw [hθ]; exact cpk_eq hl hlB hmδ
  have hex : CdUpper S l ∧ CdLower S l := (cpExact_iff hl hlB).2 (hθ.trans hO.symm)
  exact ⟨hO, hm, hθ, hR, cdExact_iff.1 hex, hex.1, hex.2⟩

theorem cp_ww_lt_B0 : ω * ω < cdB0 := by
  have hpos : (0 : Ordinal.{0}) < ω * ω := mul_pos omega0_pos omega0_pos
  have h1 : ω * ω ≤ VzLam := le_of_dvd vzLam_ri.1 (ri_iff.1 vzLam_ri).2
  calc ω * ω < ω * ω + ω * ω := lt_add_of_pos_right _ hpos
    _ ≤ VzLam + ω * ω := add_le_add h1 le_rfl

/-- **A restart `λ ≥ B₀` that is not a fixed point of `υ`, with `ρ_λ < L(ω+1)`, is in the range of
ENUM-REACH** (its code `-1 + e(λ)` is countable, so below `P'`). -/
theorem cpRange_nonfix {l : Ordinal.{0}} (hl : IsRestartIdx l) (hB : cdB0 ≤ l) (hfix : l < upsilon l)
    (hX : upsilon l < Nc.ncL S (ω + 1)) : CdRange S l := by
  have hn : upsilon l < Pv S (Om ω + Nc.ncPp S * (ω + 1)) := Lw.lw_L_eq S (ω + 1) ▸ hX
  refine ⟨hl, hB, hX, ?_⟩
  rw [cpCode_exp hl (cp_ww_lt_B0.trans_le hB) hfix hn]
  have h1 : cdOff (cdExp l) < Om 1 :=
    ((cdOff_le _).trans (cpExp_le hl.1)).trans_lt
      ((hfix.trans hn).trans (Pv_lt_Om1 S _))
  exact h1.trans (Lw.lw_Om1_lt_Pp S)

/-- **The initial part of ENUM-REACH**: UPPER and LOWER at every restart `λ` of the range with `λ < cpB1`
that is not a fixed point of `υ`. -/
theorem cpUPPER_init {l : Ordinal.{0}} (hr : CdRange S l) (hlB : l < cpB1) (hfix : l < upsilon l) :
    CdUpper S l ∧ CdLower S l := by
  have hn : upsilon l < Pv S (Om ω + Nc.ncPp S * (ω + 1)) := Lw.lw_L_eq S (ω + 1) ▸ hr.2.2.1
  obtain ⟨-, -, -, -, -, hU, hL⟩ :=
    cpEnum_nonfix hr.1 (cp_ww_lt_B0.trans_le hr.2.1) hfix hlB hn
  exact ⟨hU, hL⟩

/-- **The cap of the value** at a restart below `cpB1` that is not a fixed point of `υ`. -/
theorem cpCapV_nonfix {l η1 : Ordinal.{0}} (hl : IsRestartIdx l) (hww : ω * ω < l)
    (hfix : l < upsilon l) (hlB : l < cpB1) (hn : upsilon l < Pv S η1) : CdCapV S l := by
  obtain ⟨-, -, -, hR, -, -, -⟩ := cpEnum_nonfix hl hww hfix hlB hn
  obtain ⟨l0, z, hl0, hz0, hzρ, -, rfl⟩ := cpDecomp hl hww hfix
  have hn0 : upsilon l0 < Pv S η1 :=
    (upsilon_normal.strictMono (lt_add_of_pos_right l0 hz0)).trans hn
  obtain ⟨heta, hg, -⟩ := cpEta_add (S := S) hl0.1 hn0 hzρ
  obtain ⟨hg', hι', -, hpv'⟩ := cdEta_pv_spec (S := S) hl.1 hn
  have hml : cdOff (cdExp (l0 + z)) ≤ l0 + z := (cdOff_le _).trans (cpExp_le hl.1)
  have hmδ : cdOff (cdExp (l0 + z)) < cdDelta (l0 + z) :=
    (hml.trans upsilon_normal.strictMono.le_apply).trans_lt (cdRho_lt_delta _)
  -- `P(η_λ + (ω + 2)) = υ_{λ+ω+2}`
  have hw2 : (ω + 1 + 1 : Ordinal.{0}) < Pv S (cdEta S (l0 + z)) := by
    rw [hpv']
    have hU := upsPt_upsilon (pos_iff_ne_zero.2 hl.1)
    have hp := (indec_iff.1 (indec_of_upsPt hU)).2
    have hω : ω < upsilon (l0 + z) :=
      lt_of_le_of_lt (le_mul_left _ omega0_pos) (hww.trans hfix)
    have h1 : (1 : Ordinal.{0}) < upsilon (l0 + z) := one_lt_omega0.trans hω
    exact hp (hp hω h1) h1
  have hP : Pv S (cdEta S (l0 + z) + (ω + 1 + 1)) = upsilon (l0 + z + ω + 1 + 1) := by
    calc Pv S (cdEta S (l0 + z) + (ω + 1 + 1))
        = upsilon (iota S (cdEta S (l0 + z) + (ω + 1 + 1))) := (ups_iota S _).symm
      _ = upsilon (l0 + z + ω + 1 + 1) := by rw [cpIota_add hg' hw2, hι']; simp only [add_assoc]
  have hexp : cdExp (cdEta S (l0 + z)) = cdExp (l0 + z) := by
    rw [heta, cpExp_add _ hz0.ne', cpExp_add _ hz0.ne']
  have he2 : 2 ≤ cdExp (l0 + z) := cp_two_le_exp hl.1 (ri_iff.1 hl).2
  have hle : ω + 1 + 1 ≤ ω ^ cdExp (cdEta S (l0 + z)) := by
    rw [hexp]
    refine le_trans ?_ (opow_le_opow_right omega0_pos he2)
    rw [cp_ww_eq]
    refine le_of_lt ?_
    have h2 : (1 + 1 : Ordinal.{0}) < ω := by
      rw [one_add_one_eq_two]; exact_mod_cast natCast_lt_omega0 2
    calc ω + 1 + 1 = ω + (1 + 1) := add_assoc _ _ _
      _ < ω + ω := (add_lt_add_iff_left ω).2 h2
      _ = ω * 2 := (Ordinal.mul_two ω).symm
      _ < ω * ω := mul_lt_mul_of_pos_left (by exact_mod_cast natCast_lt_omega0 2) omega0_pos
  unfold CdCapV cdCapB
  rw [hR]
  calc cdDelta (l0 + z) + cdOff (cdExp (l0 + z)) < upsilon (l0 + z + ω + 1 + 1) := cp_delta_add_lt hmδ
    _ = Pv S (cdEta S (l0 + z) + (ω + 1 + 1)) := hP.symm
    _ ≤ Pv S (cdEta S (l0 + z) + ω ^ cdExp (cdEta S (l0 + z))) := Pv_mono (add_le_add le_rfl hle)

/-- **`ρ_λ` is not self-crossing** at a restart below `cpB1` that is not a fixed point of `υ`. -/
theorem cpCapAt_nonfix {l η1 : Ordinal.{0}} (hl : IsRestartIdx l) (hww : ω * ω < l)
    (hfix : l < upsilon l) (hlB : l < cpB1) (hn : upsilon l < Pv S η1) : CdCapAt S l :=
  cdCapAt_of_upper (cpEnum_nonfix hl hww hfix hlB hn).2.2.2.2.2.1 (cpCapV_nonfix hl hww hfix hlB hn)

end Googology.Trans.PoR.InaccPsi.R2.Cp
